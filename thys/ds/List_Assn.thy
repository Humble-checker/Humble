theory List_Assn
  imports "II_Modest_Base.Base_MEC"
begin

  lemma dr_assn_eq_iff: "a=b \<longleftrightarrow> \<upharpoonleft>a = \<upharpoonleft>b"
    unfolding dr_assn_prefix_def
    by (metis Rep_dr_assn_inject)

  subsection \<open>List Assertion\<close>

  definition "list_assn A \<equiv> mk_assn (\<lambda>xs xsi. \<up>(length xs = length xsi) ** (\<Union>*i\<in>{0..<length xs}. \<upharpoonleft>A (xs!i) (xsi!i)))"

  lemma pure_part_list_assn [vcg_prep_ext_rules]: "pure_part (\<upharpoonleft>(list_assn A) xs ys) \<Longrightarrow> length ys = length xs"
    unfolding list_assn_def 
    by (auto simp: pure_part_def sep_algebra_simps)

  text \<open>Inductive characterization\<close>
  lemma list_assn_ee_simp:
    "\<upharpoonleft>(list_assn A) [] [] = \<box>"
    unfolding list_assn_def
    by (auto simp: sep_algebra_simps)
  
  lemma list_assn_nm_simp:
    "\<upharpoonleft>(list_assn A) [] (xi#xsi) = sep_false"
    "\<upharpoonleft>(list_assn A) (x#xs) [] = sep_false"
    unfolding list_assn_def
    by (auto simp: sep_algebra_simps)



  lemma list_assn_cc_simp:
    shows "\<upharpoonleft>(list_assn A) (x#xs) (xi#xsi) = (\<upharpoonleft>A x xi ** \<upharpoonleft>(list_assn A) xs xsi)"
  proof -
    have intv_conv1: "{0..<Suc n} = insert 0 (Suc`{0..<n})" for n by auto
    have 1: "(\<Union>*i\<in>{0..<Suc n}. A i) = (A 0 ** (\<Union>*i\<in>{0..<n}. A (Suc i)))" for A :: "nat \<Rightarrow> ll_assn" and n
      by (simp del: image_Suc_atLeastLessThan add: intv_conv1 sep_set_img_map)
  
    show ?thesis
      unfolding list_assn_def
      by (auto simp: sep_algebra_simps entails_lift_extract_simps entails_eq_iff 1)
      
  qed
  
 
  lemmas list_assn_simps[simp] = list_assn_ee_simp list_assn_nm_simp list_assn_cc_simp
                   
  lemma list_assn_empty1_conv[simp]: "\<upharpoonleft>(list_assn A) [] ys = \<up>(ys=[])"
    by (cases ys) (auto simp: sep_algebra_simps)

  lemma list_assn_empty2_conv[simp]: "\<upharpoonleft>(list_assn A) xs [] = \<up>(xs=[])"
    by (cases xs) (auto simp: sep_algebra_simps)
    
    
  lemma list_assn_cons1_conv: "\<upharpoonleft>(list_assn A) (x#xs) yys = (EXS y ys. \<up>(yys=y#ys) ** \<upharpoonleft>A x y ** \<upharpoonleft>(list_assn A) xs ys)"
    apply (cases yys)
    by (auto simp: entails_eq_iff sep_algebra_simps pred_lift_extract_simps)
  
  lemma list_assn_cons2_conv: "\<upharpoonleft>(list_assn A) xxs (y#ys) = (EXS x xs. \<up>(xxs=x#xs) ** \<upharpoonleft>A x y ** \<upharpoonleft>(list_assn A) xs ys)"
    apply (cases xxs)
    by (auto simp: entails_eq_iff sep_algebra_simps pred_lift_extract_simps)
  
  lemma list_assn_append1_conv: "\<upharpoonleft>(list_assn A) (xs\<^sub>1@xs\<^sub>2) yys = (EXS ys\<^sub>1 ys\<^sub>2. \<up>(yys=ys\<^sub>1@ys\<^sub>2) ** \<upharpoonleft>(list_assn A) xs\<^sub>1 ys\<^sub>1 ** \<upharpoonleft>(list_assn A) xs\<^sub>2 ys\<^sub>2)"
    apply (induction xs\<^sub>1 arbitrary: yys)
    by (auto simp: sep_algebra_simps list_assn_cons1_conv)
  
  lemma list_assn_append2_conv: "\<upharpoonleft>(list_assn A) xxs (ys\<^sub>1@ys\<^sub>2) = (EXS xs\<^sub>1 xs\<^sub>2. \<up>(xxs=xs\<^sub>1@xs\<^sub>2) ** \<upharpoonleft>(list_assn A) xs\<^sub>1 ys\<^sub>1 ** \<upharpoonleft>(list_assn A) xs\<^sub>2 ys\<^sub>2)"
    apply (induction ys\<^sub>1 arbitrary: xxs)
    by (auto simp: sep_algebra_simps list_assn_cons2_conv)

  lemma list_assn_take1_conv: "\<upharpoonleft>(list_assn A) xxs yys = (EXS ys\<^sub>1 ys\<^sub>2. \<up>(yys=ys\<^sub>1@ys\<^sub>2) ** \<upharpoonleft>(list_assn A) (take n xxs) ys\<^sub>1 ** \<upharpoonleft>(list_assn A) (drop n xxs) ys\<^sub>2)"
    apply(subgoal_tac "\<upharpoonleft>(list_assn A) xxs yys = \<upharpoonleft>(list_assn A) ((take n xxs)@(drop n xxs)) yys")
    using list_assn_append1_conv[of A "(take n xxs)" "(drop n xxs)" yys] apply argo
    by force

  lemma list_assn_take2_conv: "\<upharpoonleft>(list_assn A) xxs yys = (EXS xs\<^sub>1 xs\<^sub>2. \<up>(xxs=xs\<^sub>1@xs\<^sub>2) ** \<upharpoonleft>(list_assn A) xs\<^sub>1 (take n yys) ** \<upharpoonleft>(list_assn A) xs\<^sub>2 (drop n yys))"
    apply(subgoal_tac "\<upharpoonleft>(list_assn A) xxs yys = \<upharpoonleft>(list_assn A) xxs ((take n yys)@(drop n yys))")
    using list_assn_append2_conv[of A xxs "(take n yys)" "(drop n yys)"] apply argo
    by force    

  lemmas list_assn_one_side_conv = 
    list_assn_cons1_conv list_assn_cons2_conv
    list_assn_append1_conv list_assn_append2_conv


  lemma list_assn_neq_len[simp]: 
    "length xs \<noteq> length xsi \<Longrightarrow> \<upharpoonleft>(list_assn A) xs xsi = sep_false"  
    "length xsi \<noteq> length xs \<Longrightarrow> \<upharpoonleft>(list_assn A) xs xsi = sep_false"  
    by (auto simp: list_assn_def)
    
  lemma list_assn_append[simp]: "length xs\<^sub>1 = length ys\<^sub>1 
    \<Longrightarrow> \<upharpoonleft>(list_assn A) (xs\<^sub>1@xs\<^sub>2) (ys\<^sub>1@ys\<^sub>2) = (\<upharpoonleft>(list_assn A) xs\<^sub>1 ys\<^sub>1 ** \<upharpoonleft>(list_assn A) xs\<^sub>2 ys\<^sub>2)"  
    apply (induction rule: list_induct2)
    by (auto simp: sep_algebra_simps)

  lemma entails_exE: assumes "(EXS x. P x) \<turnstile> Q" obtains x where "P x \<turnstile> Q"
    using assms unfolding entails_def   
    by blast 

  lemma entails_exE2: assumes "\<And> x. P x \<turnstile> Q" shows "(EXS x. P x) \<turnstile> Q"
    using assms unfolding entails_def   
    by blast 

  lemma list_assn_nth_conv1: "n < length xs \<Longrightarrow> \<upharpoonleft>(list_assn A) xs ys = (EXS ys1 y ys2. \<upharpoonleft>(list_assn A) (take n xs) ys1 ** \<upharpoonleft>A (xs ! n) y ** \<upharpoonleft>(list_assn A) (drop (Suc n) xs) ys2 ** \<up>(ys = ys1 @ y # ys2))"
    apply (subst id_take_nth_drop, assumption)
    apply (simp add: list_assn_one_side_conv sep_algebra_simps nth_append)
    done

  lemma list_assn_nth_conv2: "n < length xs \<Longrightarrow>(EXS ys1 y ys2. \<upharpoonleft>(list_assn A) (take n xs) ys1 ** \<upharpoonleft>A (xs ! n) y ** \<upharpoonleft>(list_assn A) (drop (Suc n) xs) ys2 ** \<up>(ys = ys1 @ y # ys2)) = (EXS ys1 y ys2. \<upharpoonleft>(list_assn A) (take n xs) ys1 ** \<upharpoonleft>A (xs ! n) y ** \<upharpoonleft>(list_assn A) (drop (Suc n) xs) ys2 ** \<up>(ys = ys1 @ y # ys2 \<and> ys ! n = y))"
    apply (rule entails_eqI)
    apply (intro entails_exE2)
    apply fri_keep
    apply (intro entails_exE2)
    apply fri_keep
    done



  lemma list_assn_nth_conv: "n < length xs \<Longrightarrow> \<upharpoonleft>(list_assn A) xs ys = (EXS ys1 y ys2. \<upharpoonleft>(list_assn A) (take n xs) ys1 ** \<upharpoonleft>A (xs ! n) y ** \<upharpoonleft>(list_assn A) (drop (Suc n) xs) ys2 ** \<up>(ys = ys1 @ y # ys2 \<and> ys ! n = y))"
    apply (auto simp: list_assn_nth_conv1 list_assn_nth_conv2)
    done


  lemma list_assn_pure_part[vcg_prep_ext_rules]: 
    "pure_part (\<upharpoonleft>(list_assn A) xs ys) \<Longrightarrow> length xs = length ys" (* TODO: Extraction should also go to elements! *)  
    unfolding list_assn_def
    apply (vcg_prepare_external)
    by (auto)

  lemma list_assn_pure: "list_assn (mk_assn (pure R )) = (mk_assn (pure (\<langle>R\<rangle>list_rel)))"
    apply(clarsimp simp add: dr_assn_eq_iff)
    apply(rule ext)
    apply(rule ext)
    proof(goal_cases)
      case (1 xs ys)
      then show ?case 
      proof(induction xs arbitrary: ys)
        case Nil
        then show ?case 
          apply(cases ys) unfolding pure_def
          by auto
      next
        case (Cons a xs)
        then show ?case unfolding pure_def 
          apply(cases ys) 
          by(auto simp: sep_algebra_simps)
      qed
      
    qed 

  lemma list_assn_id: "list_assn (mk_assn id_assn) = (mk_assn id_assn)"
    by(simp add: list_assn_pure)


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

end