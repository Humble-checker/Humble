theory Modest_MDP_II_Reach_Impl
  imports "../../mec/MaxEndComponent_Code" "../Intf/Modest_MDP_II_Reach"
          "../../fpii/Interval_Iteration_Tool" "Nat_Interval_Impl" "II_Modest_Base.More_Functions"
begin

text \<open>Mode-neutral LLVM code layer shared by the min (\<open>Inf\<close>) and max (\<open>Sup\<close>) interval-iteration
  implementations. It holds every operation that does not depend on the optimisation mode — the
  structural accessors (\<open>St_nth\<close>/\<open>Tr_nth\<close>/\<dots>), the avoid/target tests, the value initialisation
  (\<open>init_lb/ub\<close>), and the per-transition value fold (\<open>get_trans_val\<close>) — together with their \<open>sepref\<close>
  synthesis, so the corresponding LLVM constants are emitted exactly ONCE. The mode-specific Bellman
  backup (\<open>get_state_val\<close>: \<open>op_min\<close>/\<open>1\<close> vs \<open>op_max\<close>/\<open>0\<close>) and the sweep that calls it
  (\<open>updated_state_val_gs\<close>) live in the per-mode Impls, which extend \<open>interval_iteration_env\<close>.\<close>

  section \<open>Boilerplate\<close>

  hide_const (open) Formal_Power_Series.fps_compose

  lemma f_triple_aux: "(\<lambda>((a, b), ba). f ((a, b), ba)) = f" by fast

  type_synonym modest_mdpi =
    "size_t ptr \<times> size_t ptr \<times> size_t ptr \<times> (double \<times> double) ptr \<times> bitseti \<times> bitseti"
  type_synonym modest_ii_res = "modest_mdpi \<times> double ptr \<times> double ptr \<times> size_t"


  section \<open>Mode-neutral extracted operations\<close>

  locale interval_iteration_env_defs =
    fixes N :: nat
    fixes \<epsilon> :: real
  begin

    sublocale modest_init_mdp_env_defs N .

    abbreviation "tSt \<equiv> (\<lambda> (St,Tr,Br,Pr,Av,Ta). St)"
    abbreviation "tTr \<equiv> (\<lambda> (St,Tr,Br,Pr,Av,Ta). Tr)"
    abbreviation "tBr \<equiv> (\<lambda> (St,Tr,Br,Pr,Av,Ta). Br)"
    abbreviation "tPr \<equiv> (\<lambda> (St,Tr,Br,Pr,Av,Ta). Pr)"
    abbreviation "tAv \<equiv> (\<lambda> (St,Tr,Br,Pr,Av,Ta). Av)"
    abbreviation "tTa \<equiv> (\<lambda> (St,Tr,Br,Pr,Av,Ta). Ta)"

    abbreviation "lb_reach_assn \<equiv> IICF_Array.array_assn nn_real_lb_assn"
    abbreviation "ub_reach_assn \<equiv> IICF_Array.array_assn nn_real_ub_assn"

    definition isA :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool" where "isA = (\<lambda> (St,Tr,Br,Pr,Av,Ta) u. b_assn_open_block_fun u (\<lambda>u. op_set_member u Av))"
    definition isT :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool" where "isT = (\<lambda> (St,Tr,Br,Pr,Av,Ta) u. b_assn_open_block_fun u (\<lambda>u. op_set_member u Ta))"

    definition St_nth_lid :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat" where "St_nth_lid = (\<lambda> (St,Tr,Br,Pr,Av,Ta) u. b_assn_open_block_fun2 u St (\<lambda> u St. (St ! u)))"
    definition St_nth_uid :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat" where "St_nth_uid = (\<lambda> (St,Tr,Br,Pr,Av,Ta) u. b_assn_open_block_fun2 u St (\<lambda> u St. (St ! (Suc u))))"

    definition Tr_nth :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat" where "Tr_nth = (\<lambda> (St,Tr,Br,Pr,Av,Ta) t. b_assn_open_block_fun Tr (\<lambda> Tr. (Tr ! t)))"
    definition Br_nth :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat" where "Br_nth = (\<lambda> (St,Tr,Br,Pr,Av,Ta) b. b_assn_open_block_fun Br (\<lambda> Br. (Br ! b)))"
    definition Pr_nth :: "modest_mdp \<Rightarrow> nat \<Rightarrow> real" where "Pr_nth = (\<lambda> (St,Tr,Br,Pr,Av,Ta) b. b_assn_open_block_fun Pr (\<lambda> Pr. (Pr ! b)))"

    lemma isA_alt: "isA MDP u = modest_mdp_input_def.is_avoid_state (tAv MDP) u"
      unfolding isA_def modest_mdp_input_def.is_avoid_state_def b_assn_open_block_fun_def
      by auto

    lemma isT_alt: "isT MDP u = modest_mdp_input_def.is_target_state (tTa MDP) u"
      unfolding isT_def modest_mdp_input_def.is_target_state_def b_assn_open_block_fun_def
      by auto

    lemma
      shows St_nth_lid_alt: "St_nth_lid MDP u = (tSt MDP) ! u"
      and St_nth_uid_alt: "St_nth_uid MDP u = (tSt MDP) ! (Suc u)"
      and Tr_nth_alt: "Tr_nth MDP t = (tTr MDP) ! t"
      and Br_nth_alt: "Br_nth MDP b = (tBr MDP) ! b"
      and Pr_nth_alt: "Pr_nth MDP b = (tPr MDP) ! b"
      unfolding St_nth_lid_def St_nth_uid_def Tr_nth_def Br_nth_def Pr_nth_def b_assn_open_block_fun_def b_assn_open_block_fun2_def
      by(cases MDP; fastforce)+

    lemma St_nth_lid_boundsI: "tSt MDP ! b < x \<Longrightarrow> St_nth_lid MDP b < x"
      and St_nth_uid_boundsI: "tSt MDP ! (Suc b) < x \<Longrightarrow> St_nth_uid MDP b < x"
      and Tr_nth_boundsI: "tTr MDP ! b < x \<Longrightarrow> Tr_nth MDP b < x"
      and Br_nth_boundsI: "tBr MDP ! b < x \<Longrightarrow> Br_nth MDP b < x"
      unfolding St_nth_lid_def St_nth_uid_def Tr_nth_def Br_nth_def b_assn_open_block_fun_def b_assn_open_block_fun2_def
      by(cases MDP; auto) +


    definition init_lb_impl :: "modest_mdp \<Rightarrow> real list nres" where "init_lb_impl = (\<lambda> MDP. do{
      let N' = b_assn_open_block_fun N (\<lambda> N. N);
      let xs = replicate N' (op_0_lb_nn);
      nfoldli [0..<N'] (\<lambda> x. True) (\<lambda> u xs. do{
        ASSERT (u < N \<and> modest_mdp_input_def.N_len N xs);
        let u' = op_bound_val (\<lambda>i. i < N) u;
        if isT MDP u' then
          RETURN (xs[u':=op_1_lb_nn])
        else
          RETURN xs
      }) xs
    })"
    sepref_register init_lb_impl

    definition init_ub_impl :: "modest_mdp \<Rightarrow> real list nres" where "init_ub_impl = (\<lambda> MDP. do{
      let N' = b_assn_open_block_fun N (\<lambda> N. N);
      let xs = replicate N' (op_0_ub_nn);
      nfoldli [0..<N'] (\<lambda> x. True) (\<lambda> u xs. do{
        ASSERT (u < N \<and> modest_mdp_input_def.N_len N xs);
        let u' = op_bound_val (\<lambda>i. i < N) u;
        if isA MDP u then
          RETURN xs
        else
          RETURN (xs[u:=op_1_ub_nn])
      }) xs
    })"
    sepref_register init_ub_impl

    definition get_trans_val_lb_impl :: "modest_mdp \<Rightarrow> real list \<Rightarrow> nat \<Rightarrow> real nres" where
      "get_trans_val_lb_impl = (\<lambda> MDP xs t. do{
      let val = op_0_lb_nn;
        (_,val) \<leftarrow> WHILET (\<lambda>(b, val). b < Tr_nth MDP (Suc t)) (\<lambda> (b, val). do{
          val \<leftarrow> do{
            ASSERT(Br_nth MDP b < length xs \<and> b < length (tBr MDP) \<and> b < length (tPr MDP));
            RETURN (op_fma_lb (xs ! (Br_nth MDP b)) (Pr_nth MDP b) val)
          };
        ASSERT (b < length (tBr MDP) \<and> b < length (tPr MDP));
        RETURN (b + 1,val)
      }) (Tr_nth MDP t,val);
      RETURN val
    })"
    sepref_register get_trans_val_lb_impl

    definition get_trans_val_ub_impl :: "modest_mdp \<Rightarrow> real list \<Rightarrow> nat \<Rightarrow> real nres" where
      "get_trans_val_ub_impl = (\<lambda> MDP xs t. do{
      let val = op_0_ub_nn;
        (_,val) \<leftarrow> WHILET (\<lambda>(b, val). b < Tr_nth MDP (Suc t)) (\<lambda> (b, val). do{
          val \<leftarrow> do{
            ASSERT(Br_nth MDP b < length xs \<and> b < length (tBr MDP) \<and> b < length (tPr MDP));
            RETURN (op_fma_ub (xs ! (Br_nth MDP b)) (Pr_nth MDP b) val)
          };
        ASSERT (b < length (tBr MDP) \<and> b < length (tPr MDP));
        RETURN (b + 1,val)
      }) (Tr_nth MDP t,val);
      RETURN val
    })"
    sepref_register get_trans_val_ub_impl


    subsection \<open>Mode-neutral extraction proofs\<close>

    lemma init_lb_impl_alt: "init_lb_impl MDP \<le> (modest_mdp_input_def.init_lb N (tTa MDP))"
      unfolding init_lb_impl_def modest_mdp_input_def.init_lb_def op_0_lb_nn_def op_1_lb_nn_def b_assn_open_block_fun_def Let_def isT_def
      apply(rule LFO_refine[where ?R=Id, simplified])
      using upt_list_set_rel by auto

    lemma init_ub_impl_alt: "init_ub_impl MDP \<le> (modest_mdp_input_def.init_ub N (tAv MDP))"
      unfolding init_ub_impl_def modest_mdp_input_def.init_ub_def op_0_ub_nn_def op_1_ub_nn_def b_assn_open_block_fun_def Let_def isA_def
      apply(rule LFO_refine[where ?R=Id, simplified])
      using upt_list_set_rel by auto

    lemma get_trans_val_lb_impl_refine:
      assumes INV: "modest_mdp_input_invar N St Tr Br Pr Av Ta"
      assumes TB: "t < length Tr - Suc 0"
      assumes NXS: "modest_mdp_input_def.N_len N xs"
      shows "get_trans_val_lb_impl (St,Tr,Br,Pr,Av,Ta) xs t
      \<le> modest_mdp_input_def.get_trans_val Tr Br Pr xs t"
    proof -
      from INV interpret modest_mdp_input_invar N St Tr Br Pr Av Ta .

      define f where "f \<equiv>  (\<lambda> MDP xs t. do{
        let val = op_0_lb_nn;
        val \<leftarrow> WHILE_intv (tTr MDP) t (\<lambda> b val. do{
          ASSERT(b < length (tBr MDP) \<and> b < length (tPr MDP));
          RETURN (op_fma_lb (xs ! (Br_nth MDP b)) (Pr_nth MDP b) val)
        }) val;
        RETURN val
      })"

      have "f (St,Tr,Br,Pr,Av,Ta) xs t
      \<le> modest_mdp_input_def.get_trans_val Tr Br Pr xs t"
        unfolding f_def modest_mdp_input_def.get_trans_val_def op_fma_lb_def op_0_lb_nn_def Br_nth_def Pr_nth_def
        by(auto simp flip: FOREACH_intv_def simp: sorted_Tr TB b_assn_open_block_fun_def intro!: Refine_Basic.bind_mono(1) WHILE_intv_refine[where ?R=Id, simplified])
      moreover have "get_trans_val_lb_impl (St,Tr,Br,Pr,Av,Ta) xs t
        \<le> f (St,Tr,Br,Pr,Av,Ta) xs t"
        unfolding f_def get_trans_val_lb_impl_def WHILE_intv_def Tr_nth_alt
        apply clarsimp
        apply(refine_vcg Refine_Basic.bind_mono(1) while.WHILE_mono_prover_rule(3))
        subgoal
          by (auto simp: refine_pw_simps pw_le_iff Br_nth_alt simp flip: NXS[unfolded N_len_def] intro: Br_in_bound)
        subgoal
          using TB sorted_Tr uid_sorted_intvs
          by(auto simp: refine_pw_simps pw_le_iff intro: Br_in_boundD)
        subgoal
          by auto
        subgoal
          by blast
        done

      ultimately show ?thesis
        by simp
    qed

    lemma get_trans_val_ub_impl_refine:
      assumes INV: "modest_mdp_input_invar N St Tr Br Pr Av Ta"
      assumes TB: "t < length Tr - Suc 0"
      assumes NXS: "modest_mdp_input_def.N_len N xs"
      shows "get_trans_val_ub_impl (St,Tr,Br,Pr,Av,Ta) xs t
      \<le> modest_mdp_input_def.get_trans_val Tr Br Pr xs t"
    proof -
      from INV interpret modest_mdp_input_invar N St Tr Br Pr Av Ta .

      define f where "f \<equiv>  (\<lambda> MDP xs t. do{
        let val = op_0_ub_nn;
        val \<leftarrow> WHILE_intv (tTr MDP) t (\<lambda> b val. do{
          ASSERT(b < length (tBr MDP) \<and> b < length (tPr MDP));
          RETURN (op_fma_ub (xs ! (Br_nth MDP b)) (Pr_nth MDP b) val)
        }) val;
        RETURN val
      })"

      have "f (St,Tr,Br,Pr,Av,Ta) xs t
      \<le> modest_mdp_input_def.get_trans_val Tr Br Pr xs t"
        unfolding f_def modest_mdp_input_def.get_trans_val_def op_fma_ub_def op_0_ub_nn_def Br_nth_def Pr_nth_def
        by(auto simp flip: FOREACH_intv_def simp: sorted_Tr TB b_assn_open_block_fun_def intro!: Refine_Basic.bind_mono(1) WHILE_intv_refine[where ?R=Id, simplified])
      moreover have "get_trans_val_ub_impl (St,Tr,Br,Pr,Av,Ta) xs t
        \<le> f (St,Tr,Br,Pr,Av,Ta) xs t"
        unfolding f_def get_trans_val_ub_impl_def WHILE_intv_def Tr_nth_alt
        apply clarsimp
        apply(refine_vcg Refine_Basic.bind_mono(1) while.WHILE_mono_prover_rule(3))
        subgoal
          by (auto simp: refine_pw_simps pw_le_iff Br_nth_alt simp flip: NXS[unfolded N_len_def] intro: Br_in_bound)
        subgoal
          using TB sorted_Tr uid_sorted_intvs
          by(auto simp: refine_pw_simps pw_le_iff intro: Br_in_boundD)
        subgoal
          by auto
        subgoal
          by blast
        done

      ultimately show ?thesis
        by simp
    qed

  end


  section \<open>Mode-neutral output assertions\<close>

  definition "output_ub_assn N = hr_comp raw_array_assn (\<langle>node_rel' N, nn_real_ub_double_rel\<rangle>list_fun_rel N)"

  definition "output_lb_assn N = hr_comp raw_array_assn (\<langle>node_rel' N, nn_real_lb_double_rel\<rangle>list_fun_rel N)"

  abbreviation "u_iter_assn DS N \<equiv> pure (snat_rel O (u_iter_rel DS N))"

  lemma output_ub_assn_alt: "output_ub_assn N = hr_comp (IICF_Array.array_assn nn_real_ub_assn) (\<langle>node_rel' N, Id\<rangle>list_fun_rel N)"
    unfolding IICF_Array.array_assn_def output_ub_assn_def
    by(auto simp: list_rel_comp_list_fun_rel hr_comp_assoc list_rel_comp_b_rel_eq)

  lemma output_lb_assn_alt: "output_lb_assn N = hr_comp (IICF_Array.array_assn nn_real_lb_assn) (\<langle>node_rel' N, Id\<rangle>list_fun_rel N)"
    unfolding IICF_Array.array_assn_def output_lb_assn_def
    by(auto simp: list_rel_comp_list_fun_rel hr_comp_assoc list_rel_comp_b_rel_eq)


  section \<open>Mode-neutral LLVM synthesis\<close>

  locale interval_iteration_env = interval_iteration_env_defs +
    fixes ni \<epsilon>i
    assumes n_impl: "(ni,N) \<in> b_rel size_rel (\<lambda>i. 2 * i < max_size_t)"
    assumes \<epsilon>_impl: "(\<epsilon>i,\<epsilon>) \<in> nn_real_lb_double_rel"
  begin

    lemmas [sepref_import_param] = n_impl \<epsilon>_impl

    sepref_register N \<epsilon>

    lemma N_upper: "N < max_size_t"
      using n_impl
      using in_snat_rel_boundsD by fastforce

    lemma Suc_N_leq_max: "x < N \<Longrightarrow> Suc x < max_size_t"
      using n_impl
      by auto

    lemma Modest_mdp_assn_boundsD[sepref_bounds_dest]:
      assumes "rdomp Modest_mdp_assn_aux (St,Tr,Br,Pr,Av,Ta)"
      shows "length Tr < max_size_t" and "length Br < max_size_t" and "length Pr < max_size_t"
      and "length Tr - Suc 0 < max_size_t"
      using assms unfolding Modest_mdp_assn_aux_def
      apply auto
      done

    sepref_definition St_nth_lid_ll is "uncurry (RETURN \<circ>\<circ> St_nth_lid)" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding St_nth_lid_def Modest_mdp_assn_aux_def
      apply sepref
      done
    concrete_definition(in -) St_nth_lid_ll' [llvm_code] is interval_iteration_env.St_nth_lid_ll_def
    lemmas St_nth_lid_ll_hnr [sepref_fr_rules] = St_nth_lid_ll.refine[unfolded St_nth_lid_ll'.refine[OF interval_iteration_env_axioms]]

    sepref_definition St_nth_uid_ll is "uncurry (RETURN \<circ>\<circ> St_nth_uid)" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding St_nth_uid_def Modest_mdp_assn_aux_def
      supply[elim] = Suc_N_leq_max
      apply sepref
      done
    concrete_definition(in -) St_nth_uid_ll' [llvm_code] is interval_iteration_env.St_nth_uid_ll_def
    lemmas St_nth_uid_ll_hnr [sepref_fr_rules] = St_nth_uid_ll.refine[unfolded St_nth_uid_ll'.refine[OF interval_iteration_env_axioms]]

    sepref_definition Tr_nth_ll is "uncurry (RETURN \<circ>\<circ> Tr_nth)" :: "[\<lambda> ((St,Tr,Br,Pr,Av,Ta),t). t < length Tr]\<^sub>a Modest_mdp_assn_aux\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> size_assn"
      unfolding Tr_nth_def Modest_mdp_assn_aux_def
      by sepref
    concrete_definition(in -) Tr_nth_ll' [llvm_code] is interval_iteration_env.Tr_nth_ll_def
    lemmas Tr_nth_ll_hnr [sepref_fr_rules] = Tr_nth_ll.refine[unfolded Tr_nth_ll'.refine[OF interval_iteration_env_axioms]]

    sepref_definition Br_nth_ll is "uncurry (RETURN \<circ>\<circ> Br_nth)" :: "[\<lambda> ((St,Tr,Br,Pr,Av,Ta),b). b < length Br]\<^sub>a Modest_mdp_assn_aux\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> node_assn"
      unfolding Br_nth_def Modest_mdp_assn_aux_def
      by sepref
    concrete_definition(in -) Br_nth_ll' [llvm_code] is interval_iteration_env.Br_nth_ll_def
    lemmas Br_nth_ll_hnr [sepref_fr_rules] = Br_nth_ll.refine[unfolded Br_nth_ll'.refine[OF interval_iteration_env_axioms]]

    sepref_definition Pr_nth_ll is "uncurry (RETURN \<circ>\<circ> Pr_nth)" :: "[\<lambda> ((St,Tr,Br,Pr,Av,Ta),b). b < length Pr]\<^sub>a Modest_mdp_assn_aux\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> pfin_real_intv_assn"
      unfolding Pr_nth_def Modest_mdp_assn_aux_def
      by sepref
    concrete_definition(in -) Pr_nth_ll' [llvm_code] is interval_iteration_env.Pr_nth_ll_def
    lemmas Pr_nth_ll_hnr [sepref_fr_rules] = Pr_nth_ll.refine[unfolded Pr_nth_ll'.refine[OF interval_iteration_env_axioms]]

    sepref_definition get_trans_val_ub_ll is "uncurry2 get_trans_val_ub_impl" :: "[\<lambda> (((St,Tr,Br,Pr,Av,Ta),xs),t). t < length Tr - Suc 0]\<^sub>a Modest_mdp_assn_aux\<^sup>k *\<^sub>a ub_reach_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> nn_real_ub_assn"
      unfolding get_trans_val_ub_impl_def
      apply (annot_snat_const "TYPE(size_T)")
      supply[intro!] = Br_nth_boundsI
      supply[elim] = less_trans_Suc[OF _ Modest_mdp_assn_boundsD(3), rotated]
      apply sepref
      done
    concrete_definition(in -) get_trans_val_ub_ll' [llvm_code] is interval_iteration_env.get_trans_val_ub_ll_def
    lemmas get_trans_val_ub_ll_hnr [sepref_fr_rules] = get_trans_val_ub_ll.refine[unfolded get_trans_val_ub_ll'.refine[OF interval_iteration_env_axioms]]

    sepref_definition get_trans_val_lb_ll is "uncurry2 get_trans_val_lb_impl" :: "[\<lambda> (((St,Tr,Br,Pr,Av,Ta),xs),t). t < length Tr - Suc 0]\<^sub>a Modest_mdp_assn_aux\<^sup>k *\<^sub>a lb_reach_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> nn_real_lb_assn"
      unfolding get_trans_val_lb_impl_def
      apply (annot_snat_const "TYPE(size_T)")
      supply[intro!] = Br_nth_boundsI
      supply[elim] = less_trans_Suc[OF _ Modest_mdp_assn_boundsD(3), rotated]
      apply sepref
      done
    concrete_definition(in -) get_trans_val_lb_ll' [llvm_code] is interval_iteration_env.get_trans_val_lb_ll_def
    lemmas get_trans_val_lb_ll_hnr [sepref_fr_rules] = get_trans_val_lb_ll.refine[unfolded get_trans_val_lb_ll'.refine[OF interval_iteration_env_axioms]]

    sepref_definition isA_ll is "uncurry (RETURN oo isA)" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding isA_def Modest_mdp_assn_aux_def
      by sepref
    concrete_definition(in -) isA_ll' [llvm_code] is interval_iteration_env.isA_ll_def
    lemmas isA_ll_hnr [sepref_fr_rules] = isA_ll.refine[unfolded isA_ll'.refine[OF interval_iteration_env_axioms]]

    sepref_definition isT_ll is "uncurry (RETURN oo isT)" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding isT_def Modest_mdp_assn_aux_def
      by sepref
    concrete_definition(in -) isT_ll' [llvm_code] is interval_iteration_env.isT_ll_def
    lemmas isT_ll_hnr [sepref_fr_rules] = isT_ll.refine[unfolded isT_ll'.refine[OF interval_iteration_env_axioms]]

    sepref_definition init_lb_ll is "init_lb_impl" :: "Modest_mdp_assn_aux\<^sup>k \<rightarrow>\<^sub>a lb_reach_assn"
      unfolding init_lb_impl_def nfoldli_upt_by_while
      apply(rewrite array_fold_custom_replicate)
      apply (annot_snat_const "TYPE(size_T)")
      supply [simp] = modest_mdp_input_def.N_len_def
      apply sepref
      done
    concrete_definition(in -) init_lb_ll' [llvm_code] is interval_iteration_env.init_lb_ll_def
    lemmas init_lb_ll_hnr = init_lb_ll.refine[unfolded init_lb_ll'.refine[OF interval_iteration_env_axioms]]

    sepref_definition init_ub_ll is "init_ub_impl" :: "Modest_mdp_assn_aux\<^sup>k \<rightarrow>\<^sub>a ub_reach_assn"
      unfolding init_ub_impl_def nfoldli_upt_by_while
      apply(rewrite array_fold_custom_replicate)
      apply (annot_snat_const "TYPE(size_T)")
      supply [simp] = modest_mdp_input_def.N_len_def
      apply sepref
      done
    concrete_definition(in -) init_ub_ll' [llvm_code] is interval_iteration_env.init_ub_ll_def
    lemmas init_ub_ll_hnr = init_ub_ll.refine[unfolded init_ub_ll'.refine[OF interval_iteration_env_axioms]]

  end

end
