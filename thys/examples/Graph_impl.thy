theory Graph_impl
  imports Main Graph "../ds/Stack_Set" "II_Modest_Base.More_B_Assn"
begin

  type_synonym node_T = size_T
  type_synonym node_t = size_t



  type_synonym list_graph = "nat list list"
  
  definition list_graph_\<alpha> :: "list_graph \<Rightarrow> nat rel" where "list_graph_\<alpha> xss = {(i,j). i < length xss \<and> j \<in> set (xss ! i)}"
    
  definition list_graph_invar :: "nat \<Rightarrow> list_graph \<Rightarrow> bool" where "list_graph_invar N xss = ((\<forall>xs \<in> set xss. set xs \<subseteq> {0..<N}) \<and> (length xss = N))"

  definition "list_graph_rel N = br list_graph_\<alpha> (list_graph_invar N)"

  definition "list_graph_succ xss v = mop_list_get xss v"

  definition "list_graph_add_edge xss u v = RETURN (xss[u:=xss ! u @ [v]])"

  lemma list_graph_succ_refine: "(list_graph_succ, mop_graph_succ) \<in> list_graph_rel N \<rightarrow> node_rel' N \<rightarrow> \<langle>\<langle>node_rel' N\<rangle> list_rel\<rangle> nres_rel"
    unfolding list_graph_succ_def mop_graph_succ_def list_graph_rel_def list_set_rel_def
    apply(refine_vcg RETURN_SPEC_refine)
    apply (auto simp: in_br_conv list_graph_invar_def list_graph_\<alpha>_def set_rel_def)
    subgoal for xss i (* TODO: Clean up this mess *)
      apply (rule exI[where x="xss!i"])
      apply (auto simp: b_rel_list_rel list_all_iff)
      apply (auto simp: in_set_conv_nth Ball_def subset_code) 
      done
    done

  (*TODO: Needs some work for refinement to LLVM*)
  lemma list_graph_add_edge_refine: "(list_graph_add_edge, mop_graph_add_edge) \<in> list_graph_rel N \<rightarrow> node_rel' N  \<rightarrow> node_rel' N \<rightarrow> \<langle>list_graph_rel N\<rangle> nres_rel"
    unfolding list_graph_add_edge_def mop_graph_add_edge_def list_graph_rel_def
    apply(refine_vcg)
    using  nth_mem atLeastLessThan_iff
    by (fastforce simp: in_br_conv list_graph_invar_def list_graph_\<alpha>_def nth_list_update 
      split: if_splits elim!: in_set_upd_cases)

  definition "list_graph_assn_aux = stack_assn' TYPE(size_T) (stack_assn' TYPE(size_T) (snat_assn' TYPE(node_T)))"

  sepref_def list_graph_succ_ll is "uncurry list_graph_succ" :: "(list_graph_assn_aux)\<^sup>k *\<^sub>a (snat_assn' TYPE(node_T))\<^sup>k \<rightarrow>\<^sub>a stack_assn' TYPE(size_T) (snat_assn' TYPE(node_T))"
    unfolding list_graph_succ_def list_graph_assn_aux_def
    supply [sepref_fr_rules] = stack_nth_copy_hnr
    apply sepref
    done


  definition "list_graph_assn N = (hr_comp list_graph_assn_aux (list_graph_rel N))"

  
  lemma list_assn_shift_bound: "\<upharpoonleft>(list_assn (mk_assn (b_assn A P))) = hr_comp (\<upharpoonleft>(list_assn (mk_assn A))) (\<langle>b_rel Id P\<rangle>list_rel)"
    apply (rule ext)
    apply (rule ext)
    subgoal for xs ys 
      apply(cases "length xs  = length ys")
      subgoal apply(induction rule: list_induct2)
        apply (auto simp: sep_algebra_simps hr_comp_def list_assn_one_side_conv) 
        done
      apply (auto simp: hr_comp_def fun_eq_iff)
      by (metis list_assn_neq_len(2) list_rel_pres_length pred_lift_extract_simps(2) sep_conj_commuteI)
    done


  lemma bounded_list_rel_eq: "(xs, ys) \<in> \<langle>b_rel A P\<rangle>list_rel \<longleftrightarrow>(xs, ys) \<in> \<langle>A\<rangle>list_rel \<and> (\<forall> y \<in> set ys. P y)"
    apply(induction xs arbitrary: ys)
    apply auto[]
    apply clarsimp
    subgoal for x xs ys 
      apply(cases ys) 
      by auto
    done

  lemma bounded_set_rel_eq: "(xs, ys) \<in> \<langle>b_rel A P\<rangle>set_rel \<longleftrightarrow> (xs, ys) \<in> \<langle>A\<rangle>set_rel \<and> (\<forall> y \<in> ys. P y)"
    apply (auto simp: set_rel_def)
    done

  lemma br_distinct_set_to_list: "br set distinct O \<langle>b_rel Id P\<rangle>set_rel = \<langle>b_rel Id P\<rangle>list_rel O br set distinct"
    apply (auto simp: in_br_conv bounded_list_rel_eq bounded_set_rel_eq)
    done

  lemma stack_set_node_assn_shift_bound: "hr_comp (stack_set_assn snat_assn) (\<langle>node_rel' N\<rangle>set_rel) = stack_set_assn (node_assn' N)"
    apply (simp add: stack_set_assn_def stack_set_rel_def stack_assn_def stack_assn_raw_alt list_assn_shift_bound list_assn_pure)
    apply (simp add: hr_comp_pure flip: hr_comp_to_assn_comp)
    apply (simp add: hr_comp_assoc br_distinct_set_to_list O_assoc flip: list_rel_compp)
    apply (simp add: list_rel_compp O_assoc)
    done

  lemma stack_node_assn_shift_bound: "hr_comp (stack_assn snat_assn) (\<langle>node_rel' N\<rangle>list_rel) = stack_assn (node_assn' N)"
    apply (simp add: stack_assn_def stack_assn_raw_alt list_assn_shift_bound list_assn_pure)
    apply (simp add: hr_comp_pure flip: hr_comp_to_assn_comp)
    apply (simp add: hr_comp_assoc br_distinct_set_to_list O_assoc flip: list_rel_compp)
    done

  context 
    notes [fcomp_norm_unfold] = list_graph_assn_def[symmetric] stack_node_assn_shift_bound
  begin

    lemmas mop_graph_succ_hnr[sepref_fr_rules] = list_graph_succ_ll.refine[FCOMP list_graph_succ_refine]
  
  end


  definition "succ_list_spec N E = SPEC (\<lambda> xs. \<forall>i < N. E `` {i} \<noteq> {} \<longrightarrow> (\<exists> j. j \<in> set xs \<and> (i,j) \<in> E))"

  definition succ_list :: "nat \<Rightarrow> nat rel \<Rightarrow> nat list nres" where "succ_list N E = do{
    let xs = [];
    FOREACH {0..<N} (\<lambda> u xs. do{
      x \<leftarrow> mop_graph_succ E u;
      if x = [] then
        RETURN xs
      else do {
        ASSERT(length xs < N);
        RETURN (xs @ [x ! 0])
      }
    }) xs
  }"

  lemma "succ_list N E \<le> succ_list_spec N E"
  proof -

    have AUX: "x \<in> it \<Longrightarrow> it \<subseteq> {..<N} \<Longrightarrow> card ({..<N} - it) < N" for x it
      apply(subst card_Diff_subset_Int)
      apply blast
      by (force simp: card_gt_0_iff intro!: diff_less) 

    show ?thesis
      unfolding succ_list_def succ_list_spec_def Let_def mop_graph_succ_def
      apply(refine_vcg FOREACH_rule[where ?I="(\<lambda> ns xs. (\<forall>i \<in> ({0..<N}) - ns. E `` {i} \<noteq> {} \<longrightarrow> (\<exists> j. j \<in> set xs \<and> (i,j) \<in> E)) \<and> length xs \<le> card ({0..<N} - ns))"])
      apply (vc_solve)
      by (auto simp: atLeast0LessThan it_step_insert_iff intro: order.strict_trans1[OF _ AUX])

  qed

  definition succ_list' :: "nat \<Rightarrow> nat rel \<Rightarrow> nat list nres" where "succ_list' N E = do{
    let xs = op_stack_empty TYPE(64);
    (_,xs) \<leftarrow> WHILET (\<lambda> (u,xs). u < N) (\<lambda> (u,xs). do{
      ASSERT(u < N);
      mop_bound_val (\<lambda> u. u < N) u; 
      x \<leftarrow> mop_graph_succ E u;
      if x = [] then
        RETURN (u+1,xs)
      else do{
        ASSERT(length xs < N);
        RETURN (u+1,xs @ [x ! 0])
      }
    }) (0,xs);
    RETURN xs
  }"

  lemma "succ_list' N E \<le> succ_list N E"
    unfolding succ_list'_def succ_list_def Let_def
    apply(rule order_trans[OF _ LFO_refine[where ?R=Id and ?A=Id and ?fi=f and ?f=f and ?s0i="[]" and ?li="[0..<N]" for f, simplified]])
    apply (clarsimp simp: nfoldli_upt_by_while)
    apply(refine_vcg WHILET_refine[where ?R=Id, simplified] bind_refine[where ?R=Id and ?R'=Id, simplified])
    by (auto simp: upt_list_set_rel)


  lemma "succ_list' N E \<le> succ_list_spec N E"
    unfolding succ_list'_def succ_list_spec_def Let_def mop_graph_succ_def
    apply(refine_vcg WHILET_rule[where ?I="(\<lambda> (u,xs). (\<forall>i < u. E `` {i} \<noteq> {} \<longrightarrow> (\<exists> j. j \<in> set xs \<and> (i,j) \<in> E)) \<and> length xs \<le> u)" and ?R ="measure (\<lambda>(l',_). N-l')"])
    apply (vc_solve)
    apply(auto 0 3 simp: pw_le_iff refine_pw_simps le_eq_less_or_eq less_Suc_eq_le)
    done


  sepref_definition succ_list_ll is "uncurry succ_list'" :: "[\<lambda> (n,E). n = N]\<^sub>a (snat_assn' TYPE(node_T))\<^sup>k *\<^sub>a (list_graph_assn N)\<^sup>k \<rightarrow> stack_assn' TYPE(size_T) (node_assn' N)"
    unfolding succ_list'_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done


  (*TODO: The following is broken and I want to know how to fix it.*)

  lemma sep_union_entails: "(\<Union>*i \<in> X. A1 (f i) (g i)) h \<Longrightarrow> finite X \<Longrightarrow> (\<And> a c. A1 a c \<turnstile> A2 a c) \<Longrightarrow> (\<Union>*i \<in> X. A2 (f i) (g i)) h"
    apply(rotate_tac)
    apply(induction X arbitrary: h rule: finite_induct)
    apply simp
    apply (clarsimp simp: sep_algebra_simps sep_conj_def entails_def)
    subgoal for x F x1 x2
      apply(rule exI[where ?x=x1])
      apply(rule exI[where ?x=x2])
      by auto
    done


  lemma stack_assn_entails: "(\<And>a' c'. A1 a' c' \<turnstile> A2 a' c') \<Longrightarrow> stack_assn A1 a c \<turnstile> stack_assn A2 a c"
    unfolding stack_assn_def stack_assn_raw_def list_assn_def
    apply(clarsimp simp: entails_def) 
    subgoal for s x
      apply(rule exI[where ?x=x]) 
      apply(clarsimp simp: sep_algebra_simps sep_conj_def)
      subgoal for x1 x2
        apply(rule exI[where ?x=x1])
        apply(rule exI[where ?x=x2])  
        by (auto simp: sep_algebra_simps sep_conj_def entails_def elim!: sep_union_entails) 
      done
    done
  
  lemma stack_assn_entails': "(\<And>a' c'. hn_ctxt A1 a' c' \<turnstile> hn_ctxt A2 a' c') \<Longrightarrow> hn_ctxt (stack_assn A1) a c \<turnstile> hn_ctxt (stack_assn A2) a c"
    unfolding hn_ctxt_def
    using stack_assn_entails
    by blast


end