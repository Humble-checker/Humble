theory Modest_MDP_II_Maxred_Impl
  imports "Modest_MDP_II_Reach_Impl" "../Intf/Modest_MDP_II_Maxred"
begin

text \<open>LLVM code refinement for the MAX-reduction interval iteration over the Modest data structure.
  The mode-neutral operations (accessors, avoid/target tests, \<open>init_lb/ub\<close>, \<open>get_trans_val\<close>) and their
  \<open>sepref\<close> synthesis are inherited from \<open>Modest_MDP_II_Reach_Impl\<close> (shared with the
  min side). Only the \<open>Sup\<close>-mode Bellman backup is added here: the folds start from
  \<open>op_0_lb_nn\<close>/\<open>op_0_ub_nn\<close> and combine with \<open>op_max_lb\<close>/\<open>op_max_ub\<close> (the min
  side uses \<open>op_1_*\<close>/\<open>op_min_*\<close>). The Intf-level abstract Sup interval-iteration layer lives in
  \<open>Modest_MDP_II_Maxred\<close> (imported).\<close>





  section \<open>Sup-mode extracted operations\<close>

  locale interval_iteration_sup_env_defs = interval_iteration_env_defs
  begin

    sublocale reachability_opt_mode_defs Sup sup "(\<ge>)" 1 0 .
    interpretation modest_mdp_ii_sup_def .

    definition "mop_state_vals_gs_sup = mop_state_vals_gs"

    definition "get_state_val_lb_impl = (\<lambda> MDP xs u. do {
      let xmin = op_0_lb_nn;
      (_,xmin) \<leftarrow> WHILET (\<lambda>(t, xmin). t < St_nth_uid MDP u) (\<lambda> (t, xmin). do{
        xmin \<leftarrow> do{

          ASSERT (t < length (tTr MDP) - Suc 0);
          val \<leftarrow> get_trans_val_lb_impl MDP xs t;
          RETURN (op_max_lb val xmin)

        };
        ASSERT (t < length (tTr MDP));
        RETURN (t + 1,xmin)
      }) (St_nth_lid MDP u,xmin);
      RETURN xmin
    })"
    sepref_register get_state_val_lb_impl

    definition "get_state_val_ub_impl = (\<lambda> MDP xs u. do {
      let xmin = op_0_ub_nn;
      (_,xmin) \<leftarrow> WHILET (\<lambda>(t, xmin). t < St_nth_uid MDP u) (\<lambda> (t, xmin). do{
        xmin \<leftarrow> do{

          ASSERT (t < length (tTr MDP) - Suc 0);
          val \<leftarrow> get_trans_val_ub_impl MDP xs t;
          RETURN (op_max_ub val xmin)

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


    subsection \<open>Extraction proofs (Sup-specific)\<close>

    lemma get_state_val_opt_lb_impl_refine:
      assumes INV: "modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta"
      assumes UB: "u < N"
      assumes NXS: "N_len xs"
      shows "get_state_val_lb_impl (St,Tr,Br,Pr,Av,Ta) xs u
        \<le> modest_mdp_ii_sup_def.get_state_val_opt St Tr Br Pr xs u"
    proof -

      from INV interpret modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta .
      have II: "modest_mdp_input_invar N St Tr Br Pr Av Ta" using INV by (simp add: modest_mdp_ii_invar_sup_def)

      define f where "f \<equiv> (\<lambda> MDP xs u. do {
        let xmin = 0;
        xmin \<leftarrow> WHILE_intv (tSt MDP) u (\<lambda> t xmin. do{

          ASSERT (t < length (tTr MDP) - Suc 0);
          val \<leftarrow> get_trans_val_lb_impl MDP xs t;
          RETURN (sup val xmin)

        }) xmin;
        RETURN xmin
      })"

      have "get_state_val_lb_impl (St,Tr,Br,Pr,Av,Ta) xs u
        \<le> f (St,Tr,Br,Pr,Av,Ta) xs u"
        unfolding f_def get_state_val_lb_impl_def WHILE_intv_def St_nth_uid_alt St_nth_lid_alt
        apply (clarsimp simp: Real.sup_real_def op_max_lb_def op_0_lb_nn_def)
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
        \<le> modest_mdp_ii_sup_def.get_state_val_opt St Tr Br Pr xs u"
        unfolding f_def modest_mdp_ii_sup_def.get_state_val_opt_def
        apply (clarsimp simp flip: FOREACH_intv_def)
        apply (refine_vcg WHILE_intv_refine[where ?R=Id, simplified] while.ibind_mono)
        by (auto simp: sorted_St UB[unfolded N_DEF] intro!: get_trans_val_lb_impl_refine[OF II] NXS)

      finally show ?thesis .
    qed

    lemma get_state_val_opt_ub_impl_refine:
      assumes INV: "modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta"
      assumes UB: "u < N"
      assumes NXS: "N_len xs"
      shows "get_state_val_ub_impl (St,Tr,Br,Pr,Av,Ta) xs u
        \<le> modest_mdp_ii_sup_def.get_state_val_opt St Tr Br Pr xs u"
    proof -

      from INV interpret modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta .
      have II: "modest_mdp_input_invar N St Tr Br Pr Av Ta" using INV by (simp add: modest_mdp_ii_invar_sup_def)

      define f where "f \<equiv> (\<lambda> MDP xs u. do {
        let xmin = 0;
        xmin \<leftarrow> WHILE_intv (tSt MDP) u (\<lambda> t xmin. do{

          ASSERT (t < length (tTr MDP) - Suc 0);
          val \<leftarrow> get_trans_val_ub_impl MDP xs t;
          RETURN (sup val xmin)

        }) xmin;
        RETURN xmin
      })"

      have "get_state_val_ub_impl (St,Tr,Br,Pr,Av,Ta) xs u
        \<le> f (St,Tr,Br,Pr,Av,Ta) xs u"
        unfolding f_def get_state_val_ub_impl_def WHILE_intv_def St_nth_uid_alt St_nth_lid_alt
        apply (clarsimp simp: Real.sup_real_def op_max_ub_def op_0_ub_nn_def)
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
        \<le> modest_mdp_ii_sup_def.get_state_val_opt St Tr Br Pr xs u"
        unfolding f_def modest_mdp_ii_sup_def.get_state_val_opt_def
        apply (clarsimp simp flip: FOREACH_intv_def)
        apply (refine_vcg WHILE_intv_refine[where ?R=Id, simplified] while.ibind_mono)
        by (auto simp: sorted_St UB[unfolded N_DEF] intro!: get_trans_val_ub_impl_refine[OF II] NXS)

      finally show ?thesis .
    qed

    lemma updated_state_val_gs_impl_refine:
      assumes INV: "modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta"
      shows "updated_state_val_gs_impl (St,Tr,Br,Pr,Av,Ta) xs ys \<le>
      modest_mdp_ii_sup_def.updated_state_val_gs N St Tr Br Pr Av Ta xs ys"
    proof -

      from INV interpret modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta .

      have B: "(rev [0..<N], rev [0..<N]) \<in> \<langle>Id\<rangle>list_rel"
        by auto

      show ?thesis
        unfolding updated_state_val_gs_impl_def modest_mdp_ii_sup_def.updated_state_val_gs_def IT_nfoldli_eq
        apply (clarsimp simp: b_assn_open_block_fun_def)

        apply(rule nfoldli_refine[where ?R=Id, simplified])
        apply(vc_solve solve: B)
        apply(refine_vcg)
        apply(vc_solve simp: isT_alt isA_alt )
        apply(refine_vcg bind_mono(1) order_trans[OF get_state_val_opt_lb_impl_refine] order_trans[OF get_state_val_opt_ub_impl_refine])
        by(auto simp: INV)

    qed

  end


  section \<open>Assertions\<close>

  definition "Modest_mdp_sup_assn N = hr_comp (modest_init_mdp_env_defs.Modest_mdp_assn_aux N) (modest_mdp_sup_rel N)"


  section \<open>Correctness (data refinement)\<close>

  context interval_iteration_sup_env_defs
  begin

    lemma init_ub_impl_refine:
      assumes REL: "(DS, M) \<in> modest_mdp_sup_rel N"
      shows "init_ub_impl DS \<le> \<Down> (\<langle>node_rel' N, Id\<rangle>list_fun_rel N) (mop_init_ub M)"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast

      from REL have INV: "modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta" and [simp]: "M = modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr"
        unfolding DDEF modest_mdp_sup_rel_def modest_mdp_input_invar_def by(auto simp: in_br_conv)

      from INV interpret modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta .

      show ?thesis
        apply(rule order_trans[OF init_ub_impl_alt])
        apply (simp add: DDEF)
        apply(rule init_ub_refine)
        done
    qed

    lemma init_lb_impl_refine:
      assumes REL: "(DS, M) \<in> modest_mdp_sup_rel N"
      shows "init_lb_impl DS \<le> \<Down> (\<langle>node_rel' N, Id\<rangle>list_fun_rel N) (mop_init_lb M)"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast

      from REL have INV: "modest_mdp_input_invar N St Tr Br Pr Av Ta" and [simp]: "M = modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr"
        unfolding DDEF modest_mdp_sup_rel_def modest_mdp_ii_invar_sup_def by(auto simp: in_br_conv)

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
      assumes REL: "(DS, \<M>) \<in> modest_mdp_sup_rel N"
      assumes XREL: "(xs, x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes UREL: "(ui, u) \<in> node_rel' N"
      shows "get_state_val_lb_impl DS xs ui
       \<le> RETURN (op_state_val \<M> x u)"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast

      from REL have INV: "modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta"
        unfolding DDEF modest_mdp_sup_rel_def
        by(auto simp: in_br_conv)

      from INV interpret modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta .

      from REL have [simp]: "to_mdpc \<M> = M\<^sub>0_\<alpha>" "avoids \<M> = Av" "targets \<M> = Ta" "\<M> = \<M>_\<alpha>"
        unfolding DDEF modest_mdp_sup_rel_def
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
      assumes REL: "(DS, \<M>) \<in> modest_mdp_sup_rel N"
      assumes XREL: "(xs, x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes UREL: "(ui, u) \<in> node_rel' N"
      shows "get_state_val_ub_impl DS xs ui
       \<le> RETURN (op_state_val \<M> x u)"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast

      from REL have INV: "modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta"
        unfolding DDEF modest_mdp_input_def.\<M>_\<alpha>_def modest_mdp_sup_rel_def
        by(auto simp: in_br_conv)

      from INV interpret modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta .

      from REL have [simp]: "to_mdpc \<M> = M\<^sub>0_\<alpha>" "avoids \<M> = Av" "targets \<M> = Ta" "\<M> = \<M>_\<alpha>"
        unfolding DDEF modest_mdp_sup_rel_def
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
      assumes REL: "(DS, \<M>) \<in> modest_mdp_sup_rel N"
      assumes XREL: "(xs, x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes YREL: "(ys, y) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes XU: "(\<And>v. v \<in> states (to_mdpc \<M>) \<Longrightarrow> x v \<le> 1)"
      assumes XL: "(\<And>v. v \<in> states (to_mdpc \<M>) \<Longrightarrow> y v \<le> 1)"
      shows "updated_state_val_gs_impl DS xs ys \<le>
      \<Down> (\<langle>node_rel' N, Id\<rangle>list_fun_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) (mop_state_vals_gs \<M> x y)"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast

      from REL have INV: "modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta"
        unfolding DDEF modest_mdp_input_def.\<M>_\<alpha>_def modest_mdp_sup_rel_def
        by(auto simp: in_br_conv)

      from INV interpret modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta .

      from REL have [simp]: "to_mdpc \<M> = M\<^sub>0_\<alpha>" "avoids \<M> = Av" "targets \<M> = Ta" "\<M> = \<M>_\<alpha>"
        unfolding DDEF modest_mdp_sup_rel_def
        by(auto simp: in_br_conv)

      show ?thesis
        by(auto simp: DDEF intro!: XL XU order_trans[OF updated_state_val_gs_impl_refine[OF INV] updated_state_val_max_gs_refine[OF _ _ XREL YREL]])
    qed

    interpretation modest_mdp_ii_sup_def .

    definition "get_state_val_pre = (\<lambda> ((\<M>,x),u). \<not>op_is_avoid \<M> u \<and> \<not> op_is_target \<M> u \<and> (\<forall>v \<in> states (to_mdpc \<M>). x v \<le> 1) \<and> (\<forall>v \<in> states (to_mdpc \<M>). 0 \<le> x v))"

    definition "upd_state_val_pre = (\<lambda> ((\<M>,x),y). (\<forall>v \<in> states (to_mdpc \<M>). x v \<le> 1) \<and> (\<forall>v \<in> states (to_mdpc \<M>). y v \<le> 1))"

    lemma isA_correct:  "(isA, op_is_avoid) \<in> modest_mdp_sup_rel N \<rightarrow> node_rel' N \<rightarrow> bool_rel"
      apply(refine_vcg)
      by(auto simp: isA_alt modest_mdp_input_invar.is_avoid_state_alt modest_mdp_ii_invar_sup_def modest_mdp_sup_rel_def in_br_conv)

    lemma isT_correct: "(isT, op_is_target) \<in> modest_mdp_sup_rel N \<rightarrow> node_rel' N \<rightarrow> bool_rel"
      apply(refine_vcg)
      by(auto simp: isT_alt modest_mdp_input_invar.is_target_state_alt modest_mdp_ii_invar_sup_def modest_mdp_sup_rel_def in_br_conv)

    lemma init_ub_impl_correct: "(init_ub_impl, mop_init_ub) \<in> modest_mdp_sup_rel N \<rightarrow> \<langle>\<langle>node_rel' N, Id\<rangle>list_fun_rel N\<rangle>nres_rel"
      apply(refine_vcg) by (auto dest!: init_ub_impl_refine)

    lemma init_lb_impl_correct: "(init_lb_impl, mop_init_lb) \<in> modest_mdp_sup_rel N \<rightarrow> \<langle>\<langle>node_rel' N, Id\<rangle>list_fun_rel N\<rangle>nres_rel"
      apply(refine_vcg) by (auto dest!: init_lb_impl_refine)

    lemma get_state_val_lb_impl_correct:  "(uncurry2 get_state_val_lb_impl, uncurry2 (RETURN ooo op_state_val)) \<in> [get_state_val_pre]\<^sub>f
      ((modest_mdp_sup_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) \<times>\<^sub>r node_rel' N) \<rightarrow> \<langle>Id\<rangle>nres_rel"
      apply(rule frefI)
      apply(refine_vcg)
      by(auto simp: get_state_val_pre_def intro!: get_state_val_lb_impl_refine_aux)

    lemma get_state_val_ub_impl_correct: "(uncurry2 get_state_val_ub_impl, uncurry2 (RETURN ooo op_state_val)) \<in> [get_state_val_pre]\<^sub>f
      ((modest_mdp_sup_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) \<times>\<^sub>r node_rel' N) \<rightarrow> \<langle>Id\<rangle>nres_rel"
      apply(rule frefI)
      apply(refine_vcg)
      by(auto simp: get_state_val_pre_def intro!: get_state_val_ub_impl_refine_aux)

    lemma updated_state_val_gs_impl_correct: "(uncurry2 updated_state_val_gs_impl, uncurry2 (mop_state_vals_gs)) \<in> [upd_state_val_pre]\<^sub>f
      ((modest_mdp_sup_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) \<rightarrow> \<langle>\<langle>node_rel' N, Id\<rangle>list_fun_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N\<rangle>nres_rel"
      apply(rule frefI)
      apply(refine_vcg)
      by(auto simp: upd_state_val_pre_def intro!: updated_state_val_gs_impl_refine_aux)

  end


  section \<open>LLVM synthesis (Sup-specific)\<close>

  locale interval_iteration_sup_env = interval_iteration_env + interval_iteration_sup_env_defs
  begin

    sepref_definition get_state_val_opt_lb_ll is "uncurry2 get_state_val_lb_impl" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a lb_reach_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nn_real_lb_assn"
      unfolding get_state_val_lb_impl_def St_nth_uid_alt[symmetric] PR_CONST_def
      unfolding St_nth_lid_alt[symmetric]
      apply (annot_snat_const "TYPE(size_T)")
      supply[elim] = Suc_N_leq_max less_trans_Suc[OF _ Modest_mdp_assn_boundsD(1), rotated]
      apply sepref
      done
    concrete_definition(in -) get_state_val_opt_lb_sup_ll' [llvm_code] is interval_iteration_sup_env.get_state_val_opt_lb_ll_def
    lemmas get_state_val_opt_lb_ll_hnr[sepref_fr_rules] = get_state_val_opt_lb_ll.refine[unfolded get_state_val_opt_lb_sup_ll'.refine[OF interval_iteration_sup_env_axioms]]

    sepref_definition get_state_val_opt_ub_ll is "uncurry2 get_state_val_ub_impl" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a ub_reach_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nn_real_ub_assn"
      unfolding get_state_val_ub_impl_def St_nth_uid_alt[symmetric] PR_CONST_def
      unfolding St_nth_lid_alt[symmetric]
      apply (annot_snat_const "TYPE(size_T)")
      supply[elim] = Suc_N_leq_max less_trans_Suc[OF _ Modest_mdp_assn_boundsD(1), rotated]
      apply sepref
      done
    concrete_definition(in -) get_state_val_opt_ub_sup_ll' [llvm_code] is interval_iteration_sup_env.get_state_val_opt_ub_ll_def
    lemmas get_state_val_opt_ub_ll_hnr[sepref_fr_rules] = get_state_val_opt_ub_ll.refine[unfolded get_state_val_opt_ub_sup_ll'.refine[OF interval_iteration_sup_env_axioms]]

    sepref_definition updated_state_val_gs_impl_ll is "uncurry2 updated_state_val_gs_impl" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a lb_reach_assn\<^sup>d *\<^sub>a ub_reach_assn\<^sup>d \<rightarrow>\<^sub>a (lb_reach_assn \<times>\<^sub>a ub_reach_assn)"
      unfolding updated_state_val_gs_impl_def nfoldli_rev_upt_by_while
      apply (annot_snat_const "TYPE(size_T)")
      supply[elim] = Suc_N_leq_max
      supply[simp] = modest_mdp_input_def.N_len_def
      apply sepref
      done
    concrete_definition(in -) updated_state_val_gs_impl_sup_ll' [llvm_code] is interval_iteration_sup_env.updated_state_val_gs_impl_ll_def
    lemmas updated_state_val_gs_impl_ll_hnr = updated_state_val_gs_impl_ll.refine[unfolded updated_state_val_gs_impl_sup_ll'.refine[OF interval_iteration_sup_env_axioms]]

  end


  context interval_iteration_sup_env
  begin

    context
      notes [fcomp_norm_unfold] = f_triple_aux Modest_mdp_sup_assn_def[symmetric]
        output_ub_assn_alt[symmetric] output_lb_assn_alt[symmetric]
    begin

      lemmas mop_init_lb_hnr[sepref_fr_rules] = init_lb_ll_hnr[FCOMP init_lb_impl_correct]
      lemmas mop_init_ub_hnr[sepref_fr_rules] = init_ub_ll_hnr[FCOMP init_ub_impl_correct]

      lemmas mop_state_vals_gs_hnr[sepref_fr_rules] = updated_state_val_gs_impl_ll_hnr[FCOMP updated_state_val_gs_impl_correct, folded mop_state_vals_gs_sup_def]

      lemmas op_is_avoid_hnr[sepref_fr_rules] = isA_ll_hnr[FCOMP isA_correct]
      lemmas op_is_target_hnr[sepref_fr_rules] = isT_ll_hnr[FCOMP isT_correct]

    end

  end

end
