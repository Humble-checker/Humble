theory "Filter_List"
  imports "II_Modest_Base.Base_MEC" 
begin

  (*TODO generalize to built-in filter function with arbitrary filter and data type*)
  (*TODO generalize to arbitrary word size*)

  type_synonym 'a filter_list = "'a list \<times> 'a list"
  type_synonym 'a filter_listc = "'a list \<times> nat list"
  type_synonym 'ai filter_listi = "'ai ptr \<times> size_t ptr" 

  locale create_filter_env =
    fixes P :: "'a \<Rightarrow> bool"

  definition(in create_filter_env) op_create_filter :: "'a list \<Rightarrow> nat \<Rightarrow> 'a filter_list" where 
    "op_create_filter xs ub = (xs, filter P (take ub xs))"

  definition op_filter_nth :: "'a filter_list \<Rightarrow> nat \<Rightarrow> 'a" where 
    "op_filter_nth fxs i = (snd fxs) ! i"

  definition op_nfilter_nth :: "'a filter_list \<Rightarrow> nat \<Rightarrow> 'a" where 
    "op_nfilter_nth fxs i = (fst fxs) ! i"



  definition(in create_filter_env) "create_filter_list xs ub = do{
    (_,ids) \<leftarrow> WHILEIT (\<lambda> (i,ids). map ((!) xs) ids = filter P (take i xs) \<and> i \<le> ub \<and> (\<forall> j \<in> set ids. j < i) \<and> length ids \<le> i) (\<lambda> (i,fxs). i < ub) (\<lambda> (i,ids). do{
      ASSERT(Suc i \<le> ub);
      if P (xs ! i) then do{ ASSERT(Suc (length ids) \<le> ub); RETURN (i+1,op_list_append ids i)} else RETURN (i+1,ids)
    }) (0,op_list_empty);
    RETURN (xs,ids)
  }"
  sepref_register(in create_filter_env) create_filter_list


  definition "fa_filter_nth = (\<lambda> (xs,is) i. do {
    let j = is ! i;
    ASSERT (j < length xs);
    RETURN (xs ! j)
  })"

  definition "fa_nfilter_nth = (\<lambda> (xs,is) i. xs ! i)"

  locale filter_list_invar_defs = 
    fixes FA :: "'a filter_listc"
  begin

    definition "xs = (\<lambda> (xs,ids). xs) FA"
    definition "ids = (\<lambda> (xs,ids). ids) FA"

    definition \<alpha> :: "'a filter_list" where "\<alpha> = (xs, map ((!) xs) ids)"

  end

  lemma FA_simps[simp]: 
    "filter_list_invar_defs.xs (xs,ids) = xs"
    "filter_list_invar_defs.ids (xs,ids) = ids"
    unfolding filter_list_invar_defs.xs_def filter_list_invar_defs.ids_def
    by auto
                                          
  locale filter_list_invar = filter_list_invar_defs FA for FA +
    assumes BOUNDS: "i < length ids \<Longrightarrow> ids ! i < length xs"
  begin

    lemma fa_filter_nth_eq1: "(xs', fas) = \<alpha> \<Longrightarrow> i < length fas \<Longrightarrow> fa_filter_nth FA i \<le> RETURN (op_filter_nth \<alpha> i)"
      unfolding fa_filter_nth_def op_filter_nth_def \<alpha>_def
      apply(refine_vcg)
      using BOUNDS
      apply (auto)
      done

    lemma fa_filter_nth_eq2: "(xs', fas) = \<alpha> \<Longrightarrow> i < length fas \<Longrightarrow> RETURN (op_filter_nth \<alpha> i) \<le> fa_filter_nth FA i"
      unfolding fa_filter_nth_def op_filter_nth_def \<alpha>_def
      apply(refine_vcg)
      using BOUNDS
      apply (auto)
      done

    lemma fa_filter_nth_eq: "(xs', fas) = \<alpha> \<Longrightarrow> i < length fas \<Longrightarrow> fa_filter_nth FA i = RETURN (op_filter_nth \<alpha> i)"    
      using fa_filter_nth_eq1 fa_filter_nth_eq2 by fastforce

    lemma fa_nfilter_nth_eq: "(xs', fas) = \<alpha> \<Longrightarrow> fa_nfilter_nth FA i = op_nfilter_nth \<alpha> i"
      unfolding fa_nfilter_nth_def op_nfilter_nth_def \<alpha>_def
      apply(cases FA)
      apply auto
      done

  end

  definition "filter_list_rel = br filter_list_invar_defs.\<alpha> filter_list_invar"

  lemma(in create_filter_env) create_filter_list_refine:
    assumes UBV: "ub \<le> length xs"
    shows "create_filter_list xs ub
       \<le> \<Down> filter_list_rel (RETURN (op_create_filter xs ub))"
  proof -
    have INV: "\<forall>j\<in>set ids. j < ub \<Longrightarrow> filter_list_invar (xs, ids)" for ids
      apply(unfold_locales)
      using UBV nth_mem by fastforce

    have LE: "create_filter_list xs ub \<le> SPEC (\<lambda> r. (r, (xs, filter P (take ub xs))) \<in> filter_list_rel)"
      unfolding create_filter_list_def
      apply(refine_vcg WHILEIT_rule[where ?R="measure (\<lambda> (i,ids). ub - i)"])
      subgoal by simp 
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by fastforce
      subgoal by fastforce
      subgoal for s i ids i' ids'  
        apply clarsimp 
        apply(subst take_Suc_conv_app_nth) 
        using UBV apply linarith 
        by simp
      subgoal
        by force
      subgoal by fastforce
      subgoal by force
      subgoal by force
      subgoal for s i ids i' ids'
        apply clarsimp  
        apply(subst take_Suc_conv_app_nth)
        using UBV apply linarith 
        by simp
      subgoal by force
      subgoal by force
      subgoal by force
      subgoal by force
      subgoal for s i ids
        by(auto simp: filter_list_rel_def in_br_conv filter_list_invar_defs.\<alpha>_def INV) 
      done

    show ?thesis
      unfolding op_create_filter_def
      by(refine_vcg LE[THEN order_trans])

  qed

  lemma(in create_filter_env) create_filter_list_correct: "(uncurry create_filter_list, uncurry (RETURN oo op_create_filter)) 
      \<in> [\<lambda> (xs, ub). ub \<le> length xs]\<^sub>f Id \<times>\<^sub>r nat_rel \<rightarrow> \<langle>filter_list_rel\<rangle>nres_rel"
    apply(rule frefI)
    by (auto simp: in_nres_rel_iff intro: create_filter_list_refine)

  lemma fa_filter_nth_correct: "(uncurry fa_filter_nth, uncurry (RETURN oo op_filter_nth)) \<in> [\<lambda> ((xs,ids),i). i < length ids]\<^sub>f filter_list_rel \<times>\<^sub>r nat_rel \<rightarrow> Id"
    apply(rule frefI)
    apply (auto simp: filter_list_rel_def in_br_conv intro!: filter_list_invar.fa_filter_nth_eq)
    done

  lemma fa_nfilter_nth_correct: "(fa_nfilter_nth, op_nfilter_nth) \<in> filter_list_rel \<rightarrow> nat_rel \<rightarrow> Id"
    apply (auto simp: filter_list_rel_def in_br_conv intro!: filter_list_invar.fa_nfilter_nth_eq) 
    done

  definition "filter_list_assn_raw L A = (L A) \<times>\<^sub>a (al_assn' TYPE(size_T) size_assn)"

  locale filter_list_constr_env_defs = create_filter_env P for P +
    fixes A :: "'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn" \<comment> \<open>Assertion for the elements\<close>
    and L :: "('a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'li::llvm_rep \<Rightarrow> assn"
    and Pi :: "'ai \<Rightarrow> 1 Word.word llM"
    and Li :: "'li \<Rightarrow> size_t \<Rightarrow> 'ai llM"
  begin

  end

  locale filter_list_constr_env = 
    filter_list_constr_env_defs P A L Pi Li for P and A :: "'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn" 
    and L :: "('a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'li::llvm_rep \<Rightarrow> assn" and Pi and Li +
    assumes pure_A[constraint_simps]: "is_pure A" (*TODO adding this to constraint_simps should not be necessary, right?*)
    assumes P_ref[sepref_fr_rules]: "(Pi, RETURN o P) \<in> A\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    assumes nth_ref[sepref_fr_rules]: "(uncurry Li, uncurry (RETURN oo op_list_get)) \<in> [\<lambda> (xs,i). i < length xs]\<^sub>a (L A)\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> A"
  begin
    sepref_register P

    lemma mk_free_A[sepref_frame_free_rules]: "MK_FREE A (\<lambda>_. return\<^sub>M ())"
      apply(rule mk_free_is_pure) using pure_A .

    sepref_def create_filter_list_ll is "(uncurry (PR_CONST create_filter_list))" :: "[\<lambda> (xs,ub). ub < length xs]\<^sub>a (L A)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> filter_list_assn_raw L A"
      unfolding filter_list_assn_raw_def create_filter_list_def PR_CONST_def
      apply (annot_snat_const "TYPE(size_T)")
      apply (rewrite al_fold_custom_empty[where 'l=size_T])
      apply sepref
      done


    sepref_def fa_filter_nth_ll is "uncurry (fa_filter_nth)" :: "[\<lambda> ((xs,ids),i). i < length ids]\<^sub>a (filter_list_assn_raw L A)\<^sup>k *\<^sub>a (size_assn)\<^sup>k \<rightarrow> A"
      unfolding fa_filter_nth_def filter_list_assn_raw_def
      apply sepref
      done


    sepref_def fa_nfilter_nth_ll is "uncurry (RETURN oo fa_nfilter_nth)" :: "[\<lambda> ((xs,ids),i). i < length xs]\<^sub>a (filter_list_assn_raw L A)\<^sup>k *\<^sub>a (size_assn)\<^sup>k \<rightarrow> A"
      unfolding fa_nfilter_nth_def filter_list_assn_raw_def
      apply sepref
      done

  end
end