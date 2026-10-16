theory Stack_Set
  imports Stack "II_Modest_Base.More_List_Rel"
begin

  context 
    notes [simp] = IS_LEFT_UNIQUE_def (* Argh, the set parametricity lemmas use single_valued (K\<inverse>) here. *)
  begin
  
    sepref_decl_op set_select: "(\<lambda>s. SPEC (\<lambda>(x,s'). x \<in> s \<and> s' = s - {x}))" 
      :: "[\<lambda>s. s\<noteq>{}]\<^sub>f \<langle>K\<rangle>set_rel \<rightarrow> K \<times>\<^sub>r \<langle>K\<rangle>set_rel" where "IS_LEFT_UNIQUE K" "IS_RIGHT_UNIQUE K"  
      subgoal 
        apply rule
        apply (rule nres_relI)
        apply (rule RES_refine)
        apply clarsimp
      proof goal_cases
        case (1 x y a)
        then obtain aa where A: "aa \<in> y" "(a, aa) \<in> K" by (auto simp: set_rel_def)
        with 1 have B: "(x - {a}, y - {aa}) \<in> \<langle>K\<rangle>set_rel"
          by parametricity
        from A B show ?case by blast
      qed  
      subgoal by auto 
      done
  
  end

  definition "stack_set_rel = br set distinct"

  lemma stack_set_rel_alt: "stack_set_rel = \<langle>Id\<rangle>list_set_rel"
    unfolding stack_set_rel_def list_set_rel_def by simp

  lemma "([],{}) \<in> stack_set_rel"
    by(auto simp: in_br_conv stack_set_rel_def)

  lemma list_set_is_empty_refine: "(mop_list_is_empty, mop_set_is_empty) \<in> stack_set_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
    by(auto simp: in_br_conv stack_set_rel_def intro!: nres_relI)

  lemma list_set_pop_refine: "(mop_list_pop_last, mop_set_select) \<in> stack_set_rel \<rightarrow> \<langle>Id \<times>\<^sub>r stack_set_rel\<rangle>nres_rel"
    apply (auto simp add: in_br_conv refine_pw_simps pw_nres_rel_iff neq_Nil_conv_rev stack_set_rel_def)
    done

  definition "stack_set_assn A = hr_comp (stack_assn A) (stack_set_rel)"
  abbreviation "stack_set_assn' TYPE('l::len2) \<equiv> stack_set_assn :: _ \<Rightarrow> _ \<Rightarrow> (_,'l) array_list \<Rightarrow> _"


  lemma stack_set_copy[sepref_gen_algo_rules]: "GEN_ALGO cp (is_copy A) \<Longrightarrow> 4 < LENGTH('l::len2) \<Longrightarrow> GEN_ALGO (stack_copy_ll' cp) (is_copy (stack_set_assn' TYPE('l::len2) A))"
    unfolding stack_set_assn_def 
    unfolding GEN_ALGO_def
    apply (rule is_copy_hr_comp)
    apply (rule stack_assn_copy[unfolded GEN_ALGO_def])
    .

  lemma stack_set_node_assn_shift_bound: "hr_comp (stack_set_assn (pure R)) (\<langle>b_rel Id f\<rangle>set_rel) = stack_set_assn (b_assn (pure R) f)"
    apply (simp add: stack_set_assn_def stack_assn_def stack_assn_raw_alt list_assn_shift_bound list_assn_pure stack_set_rel_def)
    apply (simp add: hr_comp_pure flip: hr_comp_to_assn_comp)
    apply (simp add: hr_comp_assoc br_distinct_set_to_list O_assoc flip: list_rel_compp)
    apply (simp add: list_rel_compp O_assoc) 
    done
  
  lemma stack_node_assn_shift_bound: "hr_comp (stack_assn (pure R)) (\<langle>b_rel Id f\<rangle>list_rel) = stack_assn (b_assn (pure R) f)"
    apply (simp add: stack_assn_def stack_assn_raw_alt list_assn_shift_bound list_assn_pure)
    apply (simp add: hr_comp_pure flip: hr_comp_to_assn_comp)
    apply (simp add: hr_comp_assoc br_distinct_set_to_list O_assoc flip: list_rel_compp)
    done
  
  lemma stack_set_node_assn_snat_shift_bound: "hr_comp (stack_set_assn snat_assn) (\<langle>node_rel' N\<rangle>set_rel) = stack_set_assn (node_assn' N)"
    using stack_set_node_assn_shift_bound
    by blast
  
  lemma stack_node_assn_snat_shift_bound: "hr_comp (stack_assn snat_assn) (\<langle>node_rel' N\<rangle>list_rel) = stack_assn (node_assn' N)"
    using stack_node_assn_shift_bound
    by blast
  
  lemmas [sepref_import_param] = list_set_is_empty_refine list_set_pop_refine
  
  context 
    notes[fcomp_norm_simps] = stack_set_assn_def[symmetric] set_rel_id_simp
  begin
    private lemmas mop_set_select_id_fref = mop_set_select.fref[where K=Id, unfolded IS_LEFT_UNIQUE_def,simplified]

    sepref_decl_impl (ismop) stack_pop_hnr[FCOMP list_set_pop_refine] uses mop_set_select_id_fref . 
    sepref_decl_impl (ismop) stack_is_empty.refine[FCOMP list_set_is_empty_refine] uses mop_set_is_empty.fref[where A=Id] .
  end
  
  lemma stack_set_assn_free[sepref_frame_free_rules]:
    assumes A: "MK_FREE A free_elem"
    shows "MK_FREE (stack_set_assn A) (stack_free free_elem)"
    unfolding stack_set_assn_def
    using assms
    by (intro sepref_frame_free_rules)
 

end

