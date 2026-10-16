theory Interval_Iteration_Tool_GS_Minred_Code
  imports "../ds/Impl/Modest_MDP_II_Minred_Impl" "II_Modest_Base.Bind_Const" "Interval_Iteration_Min_Code"
begin                   

  (*WARNING: Without this, the parsing of separation logic formulae becomes really slow*)
  no_notation Finite_Cartesian_Product.matrix_matrix_mult (infixl "**" 70)

  lemma leq_lt_eq_Suc: "b < a \<Longrightarrow> a \<le> Suc b \<Longrightarrow> a = Suc b"
    by linarith

  lemma nfoldli_rev_upt_by_while_aux:
    "h\<le>h' \<Longrightarrow> nfoldli (rev [l..<h]) c f \<sigma> =
    doN { (_,\<sigma>)\<leftarrow>WHILET (\<lambda>(i,\<sigma>). i>l \<and> c \<sigma>) (\<lambda>(i,\<sigma>). doN { ASSERT(i>l); let i'=i-1; \<sigma> \<leftarrow> f i' \<sigma>; RETURN (i',\<sigma>) }) (h,\<sigma>); RETURN \<sigma> }
    "
  proof (induction "rev [l..<h]" arbitrary: h h' \<sigma>)
    case Nil thus ?case
      apply (simp add: Nil_eq_upt_conv)
      apply (subst WHILET_unfold)
      by fastforce
  next
    case (Cons hh xs)
    
    from Cons.hyps(2)[symmetric] have [simp]: "l<h" and [simp]: "hh=h-1" "rev [l..<h] = (h-1)#(rev [l..<h-1])" "xs=rev [l..<h-1]"
      by (auto simp: upt_eq_lel_conv Nil_eq_upt_conv rev_swap dest: leq_lt_eq_Suc) 

    from Cons.prems have A: "h - Suc 0 \<le> h'"
      by linarith

    note IH = Cons.hyps(1)[of "h - Suc 0" h', simplified, OF A, abs_def]  

    from Cons.hyps(2)[symmetric] show ?case
      apply (subst WHILET_unfold)
      apply (auto simp add: IH Let_def A)
      done
  qed

  lemma nfoldli_rev_upt_by_while:
    "nfoldli (rev [l..<h]) c f \<sigma> =
    doN { (_,\<sigma>)\<leftarrow>WHILET (\<lambda>(i,\<sigma>). i>l \<and> c \<sigma>) (\<lambda>(i,\<sigma>). doN { ASSERT(i>l); let i'=i-1; \<sigma> \<leftarrow> f i' \<sigma>; RETURN (i',\<sigma>) }) (h,\<sigma>); RETURN \<sigma> }
    "
    using nfoldli_rev_upt_by_while_aux[of h h l c f \<sigma>, simplified] by auto

  lemma hfref_ref:
    assumes FREF: "(fi,f) \<in> [P]\<^sub>a [C]\<^sub>c RR \<rightarrow>\<^sub>d S [CP]\<^sub>c"
    assumes REF: "(\<And>c. P c \<Longrightarrow> f c \<le> f' c)"
    shows "(fi,f') \<in> [P]\<^sub>a [C]\<^sub>c RR \<rightarrow>\<^sub>d S [CP]\<^sub>c"
    using FREF unfolding hfref_def
    apply clarsimp
    subgoal for c a
      apply(frule REF)
      by (auto elim!: le_funE[where ?x=a] hn_refine_ref) 
    done


  section \<open>Interval Iteration Gauss-Seidel\<close>

  subsection \<open>Implementation\<close>

  definition next_iter :: "(nat mdptc \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> bool nres)" where "next_iter M x y = SPEC(\<lambda>_. True)"

  context interval_iteration_inf_env_defs
  begin
  
    definition "mop_interval_iteration_gs_impl = (\<lambda>\<M> L. do{
      x \<leftarrow> mop_init_lb \<M>;
      y \<leftarrow> mop_init_ub \<M>;
      (x,y,i,flag) \<leftarrow> WHILET (\<lambda> (x,y,i,flag). i < L \<and> flag) (\<lambda> (x,y,i,flag). do {
        ASSERT (\<forall>u \<in> states (to_mdpc \<M>). (x u \<ge> 0 \<and> y u \<ge> 0 \<and> x u \<le> 1 \<and> y u \<le> 1));
        (x,y) \<leftarrow> mop_state_vals_gs_inf \<M> x y;
        ASSERT (\<forall>u \<in> states (to_mdpc \<M>). x u \<le> y u);
        flag \<leftarrow> next_iter \<M> x y;
        ASSERT(Suc i \<le> L);
        RETURN (x,y,Suc i,flag)
      }) (x,y,0,True);
      RETURN (x,y,i)
    })"
    sepref_register mop_interval_iteration_gs_impl

    definition "mop_min_red_impl' = (\<lambda> \<M>\<^sub>0. do{
      ASSERT(compute_mecs_pre \<M>\<^sub>0);
      D \<leftarrow> op_compute_mecs \<M>\<^sub>0;
      \<M> \<leftarrow> nfoldli [0..<N] (\<lambda>_.True) (\<lambda>u \<M>. do{
        ASSERT (u < N \<and> states (to_mdpc \<M>) = states (to_mdpc \<M>\<^sub>0));
        if op_is_avoid \<M> u then
          RETURN \<M>
        else if op_is_target \<M> u then
          RETURN \<M>
        else if \<not>op_is_trivial \<M> D u then do{
          ASSERT(make_avd_sink_pre (\<M>,u));
          RETURN (op_make_avd_sink \<M> u)
        }
        else
          RETURN \<M>
      }) \<M>\<^sub>0;
      RETURN \<M>
    })"
    sepref_register mop_min_red_impl'

    definition "tool_pmin_impl \<M> L = do{
      \<M> \<leftarrow> mop_min_red_impl' \<M>;
      R \<leftarrow> mop_interval_iteration_gs_impl \<M> L;
      RETURN (\<M>,R)
    }"

  end


  subsection \<open>Rewriting for Sepref\<close>

  context modest_mdp_ii_inf_def
  begin

    definition "next_iter_impl' \<epsilon> MDP xs ys = do{
      ASSERT((\<forall>u < N. xs ! u \<le> ys ! u) \<and> N > 0 \<and> length xs = N \<and> length ys = N);
      mop_leq_cmplt_nn \<epsilon> (op_sub_ub (ys ! 0) (xs ! 0))
    }"

  end

  context modest_mdp_ii_invar_inf
  begin               

    lemma next_iter'_refine:
      assumes XSX: "(xs,x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes YSY: "(ys,y) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes XY: "\<forall>u \<in> states M\<^sub>0_\<alpha>. x u \<le> y u"
      shows "next_iter_impl' \<epsilon> (St, Tr, Br, Pr, Av, Ta) xs ys \<le> next_iter \<M>_\<alpha> x y"
    proof -

      have AUX: "u < N \<Longrightarrow> x u \<le> y u" for u
        using XY AT
        by(auto simp: states_M\<^sub>0_\<alpha>) 

      from XSX YSY have [simp]: "length xs = N" "length ys = N"
        using list_fun_relD1 by blast+

      show ?thesis
        using N0 XSX YSY
        unfolding next_iter_impl'_def next_iter_def mop_leq_cmplt_nn_def
        apply refine_vcg
        by (auto simp: br_id_list_fun_rel dest!: list_fun_relD2 intro: AUX) 
    qed

  end


  context interval_iteration_inf_env
  begin


    definition next_iter_impl :: "modest_mdp \<Rightarrow> real list \<Rightarrow> real list \<Rightarrow> bool nres" where "next_iter_impl MDP xs ys = do{
      ASSERT((\<forall>u < N. xs ! u \<le> ys ! u) \<and> N > 0 \<and> length xs = N \<and> length ys = N);
      mop_leq_cmplt_nn \<epsilon> (op_sub_ub (ys ! 0) (xs ! 0))
    }"
    sepref_register next_iter_impl

    lemma next_iter_impl_alt: "next_iter_impl MDP xs ys = modest_mdp_ii_inf_def.next_iter_impl' N \<epsilon> MDP xs ys"
      unfolding next_iter_impl_def modest_mdp_ii_inf_def.next_iter_impl'_def
      by presburger

    lemma next_iter_refine:
      assumes REL: "(DS, \<M>) \<in> modest_mdp_inf_rel N"
      assumes XSX: "(xs,x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes YSY: "(ys,y) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes XY: "\<forall>u \<in> states (to_mdpc \<M>). x u \<le> y u"
      shows "next_iter_impl DS xs ys \<le> next_iter \<M> x y"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast

      from REL have INV: "modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta"
        unfolding modest_mdp_inf_rel_def by(auto simp: DDEF in_br_conv)

      from INV interpret modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta .

      from REL have [simp]: "to_mdpc \<M> = M\<^sub>0_\<alpha>" "avoids \<M> = Av" "targets \<M> = Ta" "\<M> = \<M>_\<alpha>"
        unfolding DDEF modest_mdp_inf_rel_def 
        by(auto simp: in_br_conv)


      show ?thesis
        unfolding next_iter_impl_alt
        using assms by(auto simp: DDEF states_M\<^sub>0_\<alpha> intro!: next_iter'_refine ) 
    qed


    definition "next_iter_pre = (\<lambda> ((\<M>,x),y). \<forall>u \<in> states (to_mdpc \<M>). x u \<le> y u)"

    lemma next_iter_correct: "(uncurry2 next_iter_impl, uncurry2 next_iter) \<in> [next_iter_pre]\<^sub>f 
      (modest_mdp_inf_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
      unfolding next_iter_pre_def
      apply(rule frefI)
      apply(refine_vcg)
      by(auto intro!: next_iter_refine)


    sepref_definition next_iter_impl_ll is "uncurry2 (next_iter_impl)" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a lb_reach_assn\<^sup>k *\<^sub>a ub_reach_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding next_iter_impl_def
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
    concrete_definition(in -) next_iter_impl_ll' [llvm_code] is interval_iteration_inf_env.next_iter_impl_ll_def

    context 
      notes [fcomp_norm_unfold] = f_triple_aux Modest_mdp_inf_assn_def[symmetric] 
        output_ub_assn_alt[symmetric] output_lb_assn_alt[symmetric]
    begin
      lemmas next_iter_impl_ll_hnr' = next_iter_impl_ll.refine[FCOMP next_iter_correct]
      lemmas next_iter_impl_ll_hnr [sepref_fr_rules] = next_iter_impl_ll_hnr'[unfolded next_iter_impl_ll'.refine[OF interval_iteration_inf_env_axioms]]
    end

    sepref_definition mop_interval_iteration_gs_ll is "uncurry (mop_interval_iteration_gs_impl)" :: "(Modest_mdp_inf_assn N)\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn)"
      unfolding mop_interval_iteration_gs_impl_def PR_CONST_def
      supply[iff del] = length_greater_0_conv
      supply[simp] = upd_state_val_pre_def next_iter_pre_def
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
    concrete_definition(in -) mop_interval_iteration_gs_ll' [llvm_code] is interval_iteration_inf_env.mop_interval_iteration_gs_ll_def
    lemmas mop_interval_iteration_gs_hnr_raw[sepref_fr_rules] = mop_interval_iteration_gs_ll.refine[unfolded mop_interval_iteration_gs_ll'.refine[OF interval_iteration_inf_env_axioms]]

    interpretation modest_init_mdp_env N ni
      apply(unfold_locales)
      using n_impl by auto
    interpretation disj_set_list_tuple_env N N ni ni
      apply(unfold_locales)
      using n_impl by auto

    lemma is_trivial_pre_aux: "RETURN xa \<le> op_compute_mecs \<M>' \<Longrightarrow> states (to_mdpc \<M>') = states (to_mdpc \<M>) \<Longrightarrow> \<not> op_is_avoid \<M> a1' \<Longrightarrow> \<not> op_is_target \<M> a1'
      \<Longrightarrow> is_trivial_pre ((\<M>, xa), a1')"
      unfolding op_compute_mecs_def op_is_avoid_def op_is_target_def is_trivial_pre_def mec_algo_defs.compute_MEC_spec_def
      by auto


    sepref_definition mop_min_red_impl_ll is "PR_CONST mop_min_red_impl'" :: "(Modest_mdp_inf_assn N)\<^sup>d \<rightarrow>\<^sub>a Modest_mdp_inf_assn N"
      unfolding PR_CONST_def mop_min_red_impl'_def nfoldli_upt_by_while Suc_eq_plus1[symmetric]
      apply (annot_snat_const "TYPE(size_T)")
      supply [elim] = N_Suc_max_size_t is_trivial_pre_aux
      apply sepref
      done
    concrete_definition(in -) mop_min_red_impl_ll' [llvm_code] is interval_iteration_inf_env.mop_min_red_impl_ll_def
    lemmas mop_min_red_impl_hnr_raw[sepref_fr_rules] = mop_min_red_impl_ll.refine[unfolded mop_min_red_impl_ll'.refine[OF interval_iteration_inf_env_axioms]]

    sepref_definition tool_pmin_impl_ll is "uncurry tool_pmin_impl" ::  "(Modest_mdp_inf_assn N)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a Modest_mdp_inf_assn N \<times>\<^sub>a (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn)"
      unfolding tool_pmin_impl_def
      apply sepref
      done
    concrete_definition(in -) tool_pmin_impl_ll' [llvm_code] is interval_iteration_inf_env.tool_pmin_impl_ll_def
    lemmas tool_pmin_impl_hnr_raw = tool_pmin_impl_ll.refine[unfolded tool_pmin_impl_ll'.refine[OF interval_iteration_inf_env_axioms]]


  end

  subsection \<open>II-code For Min Reachability\<close>


  locale interval_iteration_inf_code = MDPC_Reach_Avoid_Inf \<M> for \<M>::"nat mdptc" +
    fixes N::nat and ni::"64 Word.word" and \<epsilon>::real and \<epsilon>i::double
    assumes n_impl: "(ni,N) \<in> b_rel size_rel (\<lambda>i. 2 * i < max_size_t)"
    assumes \<epsilon>_impl: "(\<epsilon>i,\<epsilon>) \<in> nn_real_lb_double_rel"
    assumes states_M: "states (to_mdpc \<M>) = {0..<N}"
  begin

    sublocale interval_iteration_inf_env
      where N=N
      and ni=ni
      apply(unfold_locales)
      subgoal using n_impl .
      subgoal using \<epsilon>_impl .
      done



    lemma interval_iteration_min_red_impl_inf_correct:
      shows "mop_interval_iteration_gs_impl min_red L \<le> mop_interval_iteration min_red L"
    proof -

      have LOC: "MDPC_Reach_Avoid_Inf min_red"
        unfolding MDPC_Reach_Avoid_Inf_def
        using MDPC_Reach_Avoid_min_red .

      have "mop_interval_iteration_gs_impl min_red L = MDPC_Reach_Avoid_opt.mop_interval_iteration_gs min_red Inf L"
        unfolding MDPC_Reach_Avoid_opt.mop_interval_iteration_gs_def[OF MDPC_Reach_Avoid_Inf.MDPC_Reach_Avoid_opt_inf[OF LOC]]
        unfolding mop_interval_iteration_gs_impl_def MDPC_Reach_Avoid_opt.mop_interval_iteration_gs_def 
          mop_state_vals_gs_inf_def next_iter_def
        by blast
      also note MDPC_Reach_Avoid_Inf.mop_interval_iteration_gs_correct[OF LOC]
      also have "MDPC_Reach_Avoid_Inf.interval_iteration_nspec min_red = mop_interval_iteration min_red L"
        unfolding mop_interval_iteration_def by presburger
      finally show ?thesis .
    qed


    lemma interval_iteration_impl_inf_correct:
      shows "mop_interval_iteration_gs_impl \<M> L \<le> mop_interval_iteration \<M> L"
    proof -
      have "mop_interval_iteration_gs_impl \<M> L = mop_interval_iteration_gs L"
        unfolding mop_interval_iteration_gs_impl_def mop_interval_iteration_gs_def mop_state_vals_gs_inf_def next_iter_def
        by blast
      also note mop_interval_iteration_gs_correct
      also have "interval_iteration_nspec = mop_interval_iteration \<M> L"
        unfolding mop_interval_iteration_def by presburger
      finally show ?thesis .
    qed


    sublocale collapse_min_env
      apply unfold_locales .


    lemma mop_min_red_impl_correct:
      shows "mop_min_red_impl' \<M> \<le> RETURN (op_min_red \<M>)"
    proof -
      have "mop_min_red_impl' \<M> \<le> mop_min_red_impl"
        unfolding mop_min_red_impl'_def mop_min_red_impl_def 
        apply simp
        apply(refine_vcg )
        subgoal
          unfolding compute_mecs_pre_def 
          using states_M by force
        apply(rule Refine_Basic.bind_mono(1))
        apply blast
        apply(rule LFO_refine[where ?R=Id, simplified])
        apply(unfold states_M; rule list_to_set_b_relI[of "(\<lambda>i. i < N)" "[0..<N]" "{0..<N}"])
        apply(auto simp: compute_mecs_pre_def simp flip: Ball_set)[3]        
        subgoal for D u ui \<M>1 \<M>2
          unfolding ASSERT_over_prod
          apply(refine_vcg) 
          apply auto[]
          apply force 
          by (auto simp: make_avd_sink_pre_def make_avd_sink_pre_def op_is_avoid_def op_is_target_def )
          
        subgoal by (auto simp: make_avd_sink_pre_def make_avd_sink_pre_def op_is_avoid_def op_is_target_def )
        done
      also note mop_min_red_impl_correct
      finally show ?thesis .

    qed


    lemma tool_pmin_impl_correct: "tool_pmin_impl \<M> L \<le> ii_tool_nspec \<M>"
    proof -

      have AUX1: "Refine_Basic.RETURN \<M>' \<le> mop_min_red_impl' \<M> \<Longrightarrow> \<M>' = min_red" for \<M>'
        using mop_min_red_impl_correct 
        apply(cases \<M>')
        by(auto simp: pw_le_iff sep_algebra_simps op_min_red_def) 

      have AUX2: "mop_interval_iteration \<M> L = mop_interval_iteration min_red L"
        unfolding mop_interval_iteration_def interval_iteration_defs.interval_iteration_spec_def
        by (auto simp: n_real_eq_min)

      show ?thesis
        apply(rule order_trans[OF _ ii_tool_pmin_correct[of L]])
        unfolding ii_tool_pmin_def tool_pmin_impl_def prod_nres_def
        apply (refine_vcg bind_mono)
        unfolding SPEC_eq_is_RETURN
        by (auto simp: states_M AUX2 interval_iteration_min_red_impl_inf_correct dest!: AUX1 intro!: mop_min_red_impl_correct)                                   
    qed


    lemma interval_iteration_inf_hnr: "hn_refine 
      (Modest_mdp_inf_assn N \<M> \<M>i \<and>* snat_assn L Li)
      (tool_pmin_impl_ll' ni \<epsilon>i \<M>i Li)
      (hn_invalid (Modest_mdp_inf_assn N) \<M> \<M>i \<and>* snat_assn L Li)
      (Modest_mdp_inf_assn N \<times>\<^sub>a output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn) 
      (\<lambda>_. True)
      (ii_tool_nspec \<M>)"
    proof -

      note R = tool_pmin_impl_hnr_raw[to_hnr, simplified]


      show ?thesis
        apply(rule hn_refine_ref)
        apply(rule tool_pmin_impl_correct[of L])
        apply(rule hn_refine_cons[OF _ R])
        unfolding hn_ctxt_def apply blast+
        done

    qed

  end

  abbreviation "n_real' \<equiv> MDPC_Reach_Avoid.n_real"

  \<comment> \<open>Main correctness theorem\<close>
  theorem interval_iteration_inf_ll_htriple[vcg_rules]: "llvm_htriple
    (size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i ** Modest_mdp_inf_assn N \<M> \<M>i ** snat_assn L Li
       ** \<up>(2 * N < max_size_t))

    (tool_pmin_impl_ll' ni \<epsilon>i \<M>i Li)

    (\<lambda> resi. EXS \<M>' x y i. size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i ** hn_invalid (Modest_mdp_inf_assn N) \<M> \<M>i ** snat_assn L Li 
      ** \<up>(2 * N < max_size_t)
      ** ((Modest_mdp_inf_assn N) \<times>\<^sub>a output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn) (\<M>',x,y,i) resi
      ** \<up>(\<M>' = Min_red \<M>)
      ** \<up>(\<forall>u\<in>states (to_mdpc \<M>). x u \<le> n_real' \<M> u \<and> n_real' \<M> u \<le> y u)
      )"
    proof (rule htriple_pure_preI; goal_cases)
      have AUX: "(DS, \<M>) \<in> modest_mdp_inf_rel N \<Longrightarrow> states (to_mdpc \<M>) = {0..<N}" for DS \<M>
        unfolding modest_mdp_inf_rel_def modest_mdp_input_def.\<M>_\<alpha>_def modest_mdp_input_def.M\<^sub>0_\<alpha>_def
        apply (auto simp: in_br_conv to_mdpc.abs_eq states.abs_eq split: if_splits)
        done

      have AUX2: "(DS, \<M>) \<in> modest_mdp_inf_rel N \<Longrightarrow> MDPC_Reach_Avoid \<M>" for DS \<M>
        unfolding modest_mdp_inf_rel_def
        by(auto simp: in_br_conv modest_mdp_ii_invar_inf_def 
          dest: modest_mdp_input_invar.MDPC_Reach_Avoid_\<M>_\<alpha>)


      case 1
      then interpret MDPC_Reach_Avoid_Inf \<M>
        by (auto simp: Modest_mdp_inf_assn_def pure_part_hr_comp_eq MDPC_Reach_Avoid_Inf_def AUX2 dest!: pure_part_split_conj)

      from 1 have "(ni,N) \<in> size_rel" "(\<epsilon>i, \<epsilon>) \<in> nn_real_lb_double_rel"  "2 * N < max_snat 64"
        "states (to_mdpc \<M>) = {0..<N}"
        by (auto simp: Modest_mdp_inf_assn_def pure_part_hr_comp_eq MDPC_Reach_Avoid_Inf_def AUX AUX2 dest!: pure_part_split_conj)

      then interpret interval_iteration_inf_code
        apply(unfold_locales)
        subgoal 
          by (simp add: closed_M )
        subgoal 
          by (simp add: actions_finite')
        subgoal by blast
        done


      note [vcg_rules] = interval_iteration_inf_hnr[THEN hn_refineD, unfolded interval_iteration_spec_def]


      show ?thesis 
        apply vcg
        apply(subst nofail_prod_nres) apply simp apply simp
        apply vcg'
        by(auto simp: prod_nres_def refine_pw_simps pw_le_iff)

    qed


  definition Modest_tool_pmin_impl_ll :: "size_t \<Rightarrow> size_t \<Rightarrow> double \<Rightarrow> modest_mdpi ptr \<Rightarrow> modest_ii_res ptr \<Rightarrow> unit llM"
  where [llvm_code, llvm_inline]: "Modest_tool_pmin_impl_ll Li ni \<epsilon>i Eip resp \<equiv> doM {
    Ei \<leftarrow> ll_load Eip;
    res \<leftarrow> tool_pmin_impl_ll' ni \<epsilon>i Ei Li;
    ll_store res resp
  }"

  context
    fixes A_sz A_lb A_lbf A_ubf A_MDP
    defines "A_sz \<equiv> size_assn"
    defines "A_lb \<equiv> nn_real_lb_assn"
    defines "A_lbf \<equiv> output_lb_assn"
    defines "A_ubf \<equiv> output_ub_assn"
    defines "A_MDP \<equiv> Modest_mdp_inf_assn"
    
    notes A_defs = A_sz_def A_lb_def A_lbf_def A_ubf_def A_MDP_def
  begin

    interpretation llvm_prim_setup . \<comment> \<open>For ll_load/ll_store\<close>
  
    \<comment> \<open>For completeless, the full Hoare triple including importing pointers.\<close>
    corollary Modest_interval_iteration_inf_ll_htriple: "llvm_htriple
      ( snat_assn L Li ** size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i 
        ** \<upharpoonleft>ll_pto \<M>i Mip ** Modest_mdp_inf_assn N \<M> \<M>i ** \<upharpoonleft>ll_pto xx resip
        ** \<up>(2 * N < max_size_t))
  
      (Modest_tool_pmin_impl_ll Li ni \<epsilon>i Mip resip)
  
      (\<lambda> _. EXS \<M>' x y i resi. \<upharpoonleft>ll_pto resi resip
        ** size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i ** hn_invalid (Modest_mdp_inf_assn N) \<M> \<M>i ** snat_assn L Li 
        ** \<up>(2 * N < max_size_t)
        ** ((Modest_mdp_inf_assn N) \<times>\<^sub>a output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn) (\<M>',x,y,i) resi
        ** \<upharpoonleft>ll_pto \<M>i Mip
        ** \<up>(\<M>' = Min_red \<M>)
        ** \<up>(\<forall>u\<in>states (to_mdpc \<M>). x u \<le> n_real' \<M> u \<and> n_real' \<M> u \<le> y u)
        )"
      unfolding Modest_tool_pmin_impl_ll_def
      apply vcg
      done

      
    theorem Modest_tool_pmin_impl_ll_htriple: "llvm_htriple
      ( A_sz L Li ** A_sz N Ni ** A_lb \<epsilon> \<epsilon>i 
        ** \<upharpoonleft>ll_pto \<M>i Mip ** A_MDP N \<M> \<M>i ** \<upharpoonleft>ll_pto xx resip
        ** \<up>(2 * N < max_size_t))
  
      (Modest_tool_pmin_impl_ll Li Ni \<epsilon>i Mip resip)
  
      (\<lambda> _. EXS \<M>' x y i resi. \<upharpoonleft>ll_pto resi resip
        ** ((A_MDP N) \<times>\<^sub>a A_lbf N \<times>\<^sub>a A_ubf N \<times>\<^sub>a A_sz) (\<M>',x,y,i) resi
        ** \<upharpoonleft>ll_pto \<M>i Mip
        ** \<up>(\<M>' = Min_red \<M>)
        ** \<up>(\<forall>u\<in>states (to_mdpc \<M>). n_real' \<M> u \<in> {x u .. y u})
        )"
      unfolding Modest_tool_pmin_impl_ll_def A_defs
      apply vcg
      \<comment> \<open>Purge leftover pure assertions\<close>
      unfolding pure_def hn_ctxt_def invalid_assn_def
      by fri
      
      
  end


  lemmas [llvm_code] = disj_set_list_tuple_defs.tuple_list_id_am_lookup_def 
    disj_set_list_tuple_defs.tuple_list_id_am_update_def
    scc_map_defs.node_state_am_lookup_def
    scc_map_defs.node_state_am_update_def
    scc_map_defs.node_state_am_empty_def
    disj_set_list_tuple_defs.tuple_list_id_am_empty_def


  lemmas [llvm_inline] = disj_set_list_tuple_defs.to_LIST1_impl_def
    disj_set_list_tuple_defs.to_LIST2_impl_def
    scc_map_defs.is_DONE_impl_def
    scc_map_defs.is_STACK_v_impl_def
    disj_set_list_tuple_defs.in_LIST1_impl_def
    disj_set_list_tuple_defs.in_LIST2_impl_def

  export_llvm Modest_tool_pmin_impl_ll
    is "void compute_II(modest_size_t, modest_size_t, modest_dec_t, modest_mdp_t *, modest_ii_res_t *)"  
  defines \<open>
    typedef double modest_dec_t;
    typedef int64_t modest_size_t;
    typedef modest_size_t node_t;

    typedef struct {
      modest_dec_t lb;
      modest_dec_t ub;
    } modest_interval_t;

    typedef struct {
      node_t *states;
      struct {
        node_t *transitions;
        struct {
          node_t *branches;
          struct {
            modest_interval_t *probabilities;
            struct {
              modest_size_t *avoid;
              modest_size_t *target;
            };
          };
        };
      };
    } modest_mdp_t;

    typedef struct {
      modest_mdp_t mdp;
      struct{
        modest_dec_t *lbs;
        struct{
          modest_dec_t *ubs;
          modest_size_t iterations;
        };
      };
    } modest_ii_res_t;
  \<close>
    file "modest_pmin_gs.ll"

end