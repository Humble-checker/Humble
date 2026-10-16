theory Stack
  imports "II_Modest_Base.Base_MEC" "List_Assn"
begin

  (* TODO move: base_MEC and later sepref*)
  section \<open>General theory\<close>

  lemma pure_P_exs:
    assumes "\<And>x. pure_part (P x) \<Longrightarrow> x = c" 
      shows "(EXS x. P x) = P c"
    using assms unfolding pure_part_def by auto

  lemma id_assn_refl: "id_assn a a = \<box>"
    apply (simp add: pure_def sep_algebra_simps)
    done

  lemma make_assn_uph1[simp]: "mk_assn \<upharpoonleft>A = A"
    apply(auto simp: fun_eq_iff dr_assn_eq_iff)
    done

  lemma make_assn_uph2[simp]: "\<upharpoonleft>(mk_assn A) = A"
    apply(auto simp: fun_eq_iff dr_assn_eq_iff)
    done

  lemma rdomp_pure_part: "rdomp A x = (\<exists>y. pure_part (A x y))"
    unfolding rdomp_def pure_part_def
    by blast
  
  lemma pure_part_ex_iff: "pure_part (EXS x. P x) = (\<exists>x. pure_part (P x))" by (auto simp: pure_part_def)
  

  subsection \<open>assn_comp\<close>
  (*TODO move assn_comp to sepref*)
  definition "assn_comp A B a c \<equiv> EXS b. A a b ** B b c"
  
  lemma assn_comp_def_rev: "assn_comp A B a c \<equiv> EXS b. B b c ** A a b"
    unfolding assn_comp_def by (auto simp add: sep_algebra_simps fun_eq_iff sep_conj_c)
  
  
  lemma assn_comp_id[simp]: 
    "assn_comp id_assn B = B"
    "assn_comp A id_assn = A"
    unfolding assn_comp_def 
    by (auto simp: fun_eq_iff sep_algebra_simps pure_def)
  
  lemma assn_comp_assoc[simp]: "assn_comp (assn_comp A B) C = assn_comp A (assn_comp B C)"  
    unfolding assn_comp_def 
    by (auto simp: fun_eq_iff sep_algebra_simps)
    
  lemma hr_comp_to_assn_comp: "hr_comp A B = assn_comp (pure B) A"
    unfolding assn_comp_def hr_comp_def pure_def 
    by (auto simp: fun_eq_iff sep_algebra_simps)
    
  lemma assn_comp_summarize_pure: 
    "assn_comp (pure A) (pure B) = pure (B O A)"  
    "assn_comp (pure A) (assn_comp (pure B) C) = assn_comp (pure (B O A)) C"
    unfolding assn_comp_def pure_def 
    by (auto simp: fun_eq_iff sep_algebra_simps)

  lemma rdomp_assn_comp_split: "rdomp (assn_comp A\<^sub>2 A\<^sub>1) x \<Longrightarrow> \<exists> y. rdomp A\<^sub>1 y \<and> pure_part (A\<^sub>2 x y)"
    unfolding assn_comp_def rdomp_def pure_part_def
    apply(auto simp: sep_conj_def)
    done


  section \<open>Stack assn\<close>

  sepref_decl_op list_pop: "(\<lambda>l. (hd l, tl l))" :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A \<times>\<^sub>r \<langle>A\<rangle>list_rel" by auto



  definition "stack_assn_raw A \<equiv> mk_assn (\<lambda>s si. EXS xs. \<upharpoonleft>arl_assn xs si ** \<upharpoonleft>(list_assn A) s xs)"

  lemma stack_assn_raw_alt: "stack_assn_raw A = mk_assn (assn_comp (\<upharpoonleft>(list_assn A)) (\<upharpoonleft>arl_assn))"
    unfolding stack_assn_raw_def assn_comp_def 
    apply(fo_rule fun_cong arg_cong, intro ext) 
    apply(auto simp: sep_conj_commute)
    done

  

  lemma stack_assn_raw_id_arl: "stack_assn_raw (mk_assn id_assn) = arl_assn"
    unfolding stack_assn_raw_def list_assn_id 
    apply (auto simp: pure_def sep_algebra_simps)
    done

  type_synonym ('e,'l) stack = "('e,'l) array_list"
  

  definition "stack_assn A \<equiv> \<upharpoonleft>(stack_assn_raw (mk_assn A))"
  abbreviation "stack_assn' TYPE('l::len2) \<equiv> stack_assn :: _ \<Rightarrow> _ \<Rightarrow> (_,'l) array_list \<Rightarrow> _"


  definition "stack_nth_copy cp s i = 
    doM { 
      x \<leftarrow> arl_nth s i;
      y \<leftarrow> cp x;
      Mreturn y
    }"

  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "stack_assn A" for A]
  
  lemma rdomp_arl_length: "rdomp \<upharpoonleft>(arl_assn :: (_ list, 'l::len2 word \<times> 'l word \<times> _ ptr) dr_assn) xs \<Longrightarrow> length xs < max_snat LENGTH('l) "
    unfolding arl_assn_def arl_assn'_def rdomp_pure_part 
    apply (auto simp: pure_part_ex_iff dest!: vcg_prep_ext_rules )
    done
  
  lemma [sepref_bounds_dest]: "rdomp (stack_assn' TYPE('l::len2) A) xs \<Longrightarrow> length xs < max_snat LENGTH('l)"
    unfolding stack_assn_def stack_assn_raw_alt
    apply simp
    apply(drule rdomp_assn_comp_split)
    apply clarsimp
    by (metis list_assn_pure_part rdomp_arl_length)






  lemma stack_assn_id_arl:"stack_assn id_assn = \<upharpoonleft>arl_assn"
    unfolding stack_assn_def
    by(simp add: stack_assn_raw_id_arl)



  lemma stack_empty_rule[vcg_rules]: "llvm_htriple (\<up>(LENGTH('l)>4)) arl_new_raw (\<lambda>xsi. \<upharpoonleft>(stack_assn_raw A) [] (xsi::(_,'l::len2) array_list))"
    unfolding stack_assn_raw_def
    by vcg

  lemma stack_len_rule[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>(stack_assn_raw A) xs xsi) 
    (arl_len xsi) 
    (\<lambda>ni. EXS n. \<upharpoonleft>(stack_assn_raw A) xs xsi ** \<upharpoonleft>snat.assn n ni ** \<up>(n=length xs))"
    unfolding stack_assn_raw_def

    by vcg

  lemma stack_nth_rule[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>(stack_assn_raw (mk_assn id_assn)) xs xsi ** \<upharpoonleft>snat.assn n ni ** \<up>(n < length xs)) 
    (arl_nth xsi ni)
    (\<lambda> ei. \<upharpoonleft>(stack_assn_raw (mk_assn id_assn)) xs xsi ** \<upharpoonleft>snat.assn n ni ** \<upharpoonleft>(mk_assn id_assn) (xs ! n) ei)"
    unfolding stack_assn_raw_def
    supply [simp] = pure_def
    unfolding list_assn_id
    apply vcg
    done


  lemma stack_nth_copy_rule[vcg_rules]: 
    assumes [vcg_rules]: "\<And> x xi. llvm_htriple (\<upharpoonleft>A x xi) (cp xi) (\<lambda> yi. \<upharpoonleft>A x xi ** \<upharpoonleft>A x yi)"
      shows "llvm_htriple
    (\<upharpoonleft>(stack_assn_raw A) xs xsi ** \<upharpoonleft>snat.assn n ni ** \<up>(n < length xs)) 
    (stack_nth_copy cp xsi ni)
    (\<lambda> ei. \<upharpoonleft>(stack_assn_raw A) xs xsi ** \<upharpoonleft>snat.assn n ni ** \<upharpoonleft>A (xs ! n) ei)"
    unfolding stack_assn_raw_def stack_nth_copy_def
    supply [simp] = pure_def
    unfolding list_assn_id 
    apply vcg
    apply (subst (asm) list_assn_nth_conv, assumption)
    apply (subst list_assn_nth_conv, assumption)
    apply fri_extract
    apply vcg
    done


  lemma stack_top_rule[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>(stack_assn_raw (mk_assn id_assn)) xs xsi ** \<up>(xs\<noteq>[])) 
    (arl_last xsi) 
    (\<lambda> ei. \<upharpoonleft>(stack_assn_raw (mk_assn id_assn)) xs xsi ** \<up>(xs\<noteq>[]) ** \<upharpoonleft>(mk_assn id_assn) (last xs) ei)"
    unfolding stack_assn_raw_def
    supply [simp] = list_assn_one_side_conv pure_def
    apply (cases xs rule: rev_cases)
    apply vcg
    done


  lemma stack_pop_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(stack_assn_raw A) xs xsi ** \<up>(xs\<noteq>[])) 
    (arl_pop_back xsi) 
    (\<lambda>(ei,xsi). \<upharpoonleft>(stack_assn_raw A) (butlast xs) xsi ** \<upharpoonleft>A (last xs) ei)"
    unfolding stack_assn_raw_def
    supply [simp] = list_assn_one_side_conv
    apply (cases xs rule: rev_cases)
    apply vcg
    done
  
  lemma stack_push_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(stack_assn_raw A) xs xsi ** \<upharpoonleft>A x xi ** \<up>(length xs + 1 < max_snat LENGTH('l))) 
    (arl_push_back xsi xi) 
    (\<lambda>xsi. \<upharpoonleft>(stack_assn_raw A) (xs@[x]) xsi)"
    for xsi :: "(_,'l::len2) array_list"
    unfolding stack_assn_raw_def
    supply [simp] = list_assn_one_side_conv
    by vcg

  definition [simp]: "op_stack_empty TYPE('l::len2) \<equiv> op_list_empty"     
  sepref_register "op_stack_empty TYPE('l::len2)"

  lemma stack_len_hnr: "(arl_len, mop_list_length) \<in> (stack_assn A)\<^sup>k \<rightarrow>\<^sub>a snat_assn"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    unfolding stack_assn_def
    by vcg

  lemma stack_nth_hnr: "(uncurry arl_nth, uncurry mop_list_get) \<in> (stack_assn id_assn)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
    unfolding stack_assn_id_arl
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    supply [simp] = refine_pw_simps
    apply sepref_to_hoare
    apply vcg
    done


  definition "is_copy A cp = (\<forall>x xi. llvm_htriple (A x xi) (cp xi) (\<lambda> yi. A x xi ** A x yi))"

  lemma pure_assn_copy[sepref_gen_algo_rules]: "Sepref_Constraints.CONSTRAINT is_pure A \<Longrightarrow> GEN_ALGO Mreturn (is_copy A)"
    apply (clarsimp simp: GEN_ALGO_def is_copy_def is_pure_conv pure_def)
    apply vcg
    done


  lemma is_copy_hr_comp: assumes "is_copy A cp" shows "is_copy (hr_comp A B) cp"
    unfolding is_copy_def hr_comp_def
    supply [vcg_rules] = assms[unfolded is_copy_def, rule_format]
    apply vcg
    done


  lemma stack_nth_copy_hnr: 
    assumes "GEN_ALGO cp (is_copy A)" 
      shows "(uncurry (stack_nth_copy cp), uncurry mop_list_get) \<in> (stack_assn A)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a A"
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    unfolding stack_assn_def
    supply [simp] = refine_pw_simps
    supply [vcg_rules] = assms[unfolded GEN_ALGO_def is_copy_def, rule_format]
    apply vcg
    done


  lemma stack_top_hnr: "(arl_last, mop_list_last) \<in> (stack_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a id_assn"
    apply sepref_to_hoare
    unfolding stack_assn_def
    supply [simp] = pure_def
    apply vcg'
    done

  lemma stack_pop_hnr: "(arl_pop_back, mop_list_pop_last) \<in> (stack_assn A)\<^sup>d \<rightarrow>\<^sub>a A \<times>\<^sub>a stack_assn A"
    apply sepref_to_hoare
    unfolding stack_assn_def
    apply vcg'
    by (simp add: refine_pw_simps)
    
    
  definition [simp, llvm_inline]: "stack_push \<equiv> arl_push_back"  
  
  lemma stack_push_hnr: "(uncurry stack_push, uncurry mop_list_append) 
    \<in> [\<lambda>(xs,x). length xs + 1 < max_snat LENGTH('l)]\<^sub>a (stack_assn' TYPE('l::len2) A)\<^sup>d *\<^sub>a A\<^sup>d \<rightarrow> stack_assn A"
    apply sepref_to_hoare
    unfolding stack_assn_def
    apply vcg'
    done
                  
  lemma singleton_list_append: "[v] = op_list_append [] v"
    by simp                      

  lemma stack_fold_custom_empty:
    "[] = op_stack_empty TYPE('l::len2)"
    "op_list_empty = op_stack_empty TYPE('l::len2)"
    "mop_list_empty = RETURN (op_stack_empty TYPE('l::len2))"
    by auto
      
  lemma stack_empty_hnr[sepref_fr_rules]: "(uncurry0 arl_new_raw, uncurry0 (RETURN (PR_CONST (op_stack_empty TYPE('l))))) 
    \<in> [\<lambda>_. 4 < LENGTH('l::len2)]\<^sub>a unit_assn\<^sup>k \<rightarrow> stack_assn' TYPE('l) A"
    apply sepref_to_hoare
    unfolding stack_assn_def
    by vcg


  lemma stack_assn_pure [fcomp_norm_simps]: "hr_comp (stack_assn id_assn) (\<langle>A\<rangle>list_rel) = stack_assn (pure A)"
    unfolding stack_assn_def stack_assn_raw_def 
    apply (simp add: list_assn_id)
    apply (clarsimp simp add: fun_eq_iff hr_comp_def)
    apply (fo_rule arg_cong)
    apply (rule ext)
    apply (subst pure_P_exs)
    apply (elim pure_part_split_conj[elim_format] conjE)
    apply simp
    apply(auto simp: sep_algebra_simps list_assn_pure id_assn_refl)
    apply (auto simp add: pure_def sep_algebra_simps)
    done    
    
  context
    notes [fcomp_norm_simps] = list_rel_id_simp
    fixes l_dummy :: "'l::len2 itself" 
      and L
    defines [simp]: "L \<equiv> (LENGTH ('l))"
  begin  


  sepref_decl_impl (ismop) stack_top_hnr .
  sepref_decl_impl (ismop) stack_pop_hnr uses mop_list_pop_last.fref[where A=Id] .  
  sepref_decl_impl (ismop) stack_push_hnr[where 'l='l,folded L_def] uses mop_list_append.fref[where A=Id] by simp
  sepref_decl_impl (ismop) stack_len_hnr uses mop_list_length.fref[where A=Id] .
  sepref_decl_impl (ismop) stack_nth_hnr .
  
  lemma mop_list_is_empty_by_len: "mop_list_is_empty xs = RETURN (length xs = 0)" by simp
  
  sepref_definition stack_is_empty [llvm_inline] is "mop_list_is_empty" 
    :: "(stack_assn' TYPE('l::len2) A)\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding mop_list_is_empty_by_len
    apply (annot_snat_const "TYPE('l)")
    by sepref
    
  sepref_decl_impl (ismop) stack_is_empty.refine uses mop_list_is_empty.fref[where A=Id] .


  (* TODO: Several improvements possible: 
      - Make this an operation of Stack
      - Combine this with the find_seg_impl program
  *)
  definition "stack_pop_to_n n xs = do {
    ASSERT(n \<le> length xs);
    xs'\<leftarrow>WHILET
      (\<lambda>xs. length xs > n) 
      (\<lambda>xs. do { (ei,xs') \<leftarrow> mop_list_pop_last xs; RETURN xs'})
      (xs);
    RETURN xs'
  }"


  lemma prefix_eq_length: "prefix xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> xs = ys"
    unfolding prefix_def
    by fastforce

  lemma prefix_butlast: "length xs < length ys \<Longrightarrow> prefix xs ys \<Longrightarrow> prefix xs (butlast ys)"
    apply(induction xs rule: rev_induct) 
    apply simp
    apply(cases ys rule: rev_cases)
    apply auto
    done

  lemma stack_pop_to_n_aux:
    assumes "n \<le> length xs"
    shows "stack_pop_to_n n xs 
    \<le> SPEC (\<lambda>r. r = take n xs)"
      unfolding stack_pop_to_n_def
      apply (refine_rcg 
      WHILET_rule[where I="\<lambda>xs'. prefix (take n xs) xs' \<and> length xs' \<le> length xs" 
                    and R="measure (\<lambda>xs'. length xs')" 
      ]
      refine_vcg)
      apply (auto simp: assms take_is_prefix prefix_butlast)[8]
      apply (metis le_def sublist_equal_part take_all_iff bounded_take_length[OF assms])
      done

  lemma stack_pop_to_n_aux': "stack_pop_to_n n xs \<le> mop_list_take n xs"
      apply simp
      unfolding stack_pop_to_n_def
      apply (refine_rcg 
      WHILET_rule[where I="\<lambda>xs'. prefix (take n xs) xs' \<and> length xs' \<le> length xs" 
                    and R="measure (\<lambda>xs'. length xs')" 
      ]
      refine_vcg)
      apply (auto simp: take_is_prefix prefix_butlast)
      apply (metis le_def sublist_equal_part take_all_iff bounded_take_length)
      done

  lemma stack_pop_to_n_refine: "(stack_pop_to_n, mop_list_take) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    using stack_pop_to_n_aux' 
    apply (auto simp: pw_nres_rel_iff refine_pw_simps pw_le_iff) 
    by blast+



  context fixes free_elem and A :: "'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn" assumes A[sepref_frame_free_rules]: "MK_FREE A free_elem" begin
    sepref_definition stack_pop_to_n_impl is "uncurry stack_pop_to_n" :: "(snat_assn' TYPE('l))\<^sup>k *\<^sub>a (stack_assn' TYPE('l) A)\<^sup>d \<rightarrow>\<^sub>a stack_assn' TYPE('l) A"
      unfolding stack_pop_to_n_def
      apply sepref
      done
  end



  concrete_definition stack_pop_to_n_ll[llvm_inline, llvm_code] is stack_pop_to_n_impl_def
  context fixes free_elem and A :: "'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn" assumes free_A[sepref_frame_free_rules]: "MK_FREE A free_elem" begin
  
    lemmas stack_pop_to_n_ll_refine = stack_pop_to_n_impl.refine[FCOMP stack_pop_to_n_refine, OF free_A, unfolded stack_pop_to_n_ll.refine[OF free_A]]
    sepref_decl_impl (ismop) stack_pop_to_n_ll_refine uses mop_list_take.fref[where A = Id] .
  end
  end
  

  definition "stack_copy xs =
    nfoldli xs (\<lambda> _. True) (\<lambda> x ys. do {ASSERT(length ys < length xs); mop_list_append ys x}) op_list_empty
  "

  lemma stack_copy_alt_def :"stack_copy xs = nfoldli [0..<length xs] (\<lambda>_. True) (\<lambda> i ys. 
    do {
      y \<leftarrow> mop_list_get xs i;
      ASSERT(length ys < length xs);
      mop_list_append ys y
    }) op_list_empty
    "
    unfolding stack_copy_def
    apply(rewrite in "\<hole> = _" nfoldli_by_idx)
    apply auto
    done

  lemma stack_copy_correct: "stack_copy xs \<le> RETURN xs"
    unfolding stack_copy_def
    apply(refine_vcg nfoldli_rule[where I = "(\<lambda> xs _ xs'. xs' = xs)"])
    apply auto
    done

  lemma stack_copy_refine: "(stack_copy, RETURN) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding stack_copy_def
    apply(refine_vcg nfoldli_rule[where I = "(\<lambda> xs _ xs'. xs' = xs)"])
    apply auto
    done


  context fixes A :: "'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn" and cp assumes [sepref_gen_algo_rules]: "GEN_ALGO cp (is_copy A)"
    begin
   
    sepref_definition stack_copy_ll is "stack_copy" :: "[\<lambda>_. 4 < LENGTH('l::len2)]\<^sub>a (stack_assn' TYPE('l::len2) A)\<^sup>k \<rightarrow> stack_assn' TYPE('l) A"
      unfolding stack_copy_alt_def 
      unfolding nfoldli_upt_by_while 
      unfolding stack_fold_custom_empty[where 'l = 'l]
      apply(annot_snat_const "TYPE('l)")
      supply [sepref_fr_rules] = stack_nth_copy_hnr
      supply [safe_constraint_rules] = CN_FALSEI[of is_pure "A"]
      apply sepref
      done
    
  end
  
  concrete_definition (in -) stack_copy_ll' [llvm_code] is stack_copy_ll_def 


  lemma stack_assn_copy[sepref_gen_algo_rules]: assumes A: "GEN_ALGO cp (is_copy A)" shows "4 < LENGTH('l) \<Longrightarrow> GEN_ALGO (stack_copy_ll' cp) (is_copy (stack_assn' TYPE('l::len2) A))"
    unfolding stack_copy_ll'.refine[symmetric, OF A]
    unfolding is_copy_def GEN_ALGO_def
    apply clarify
    supply R=stack_copy_ll.refine[OF A, FCOMP stack_copy_refine, to_hnr, THEN hn_refineD, simplified, unfolded hn_ctxt_def]
    supply [vcg_rules] = R
    apply vcg
    done


  context
    includes monad_syntax_M
  begin
      
    definition [llvm_code]: "stack_free free_elem xsi \<equiv> doM {
      xsi \<leftarrow> llc_while 
        (\<lambda>xsi. doM { n\<leftarrow>arl_len xsi; ll_icmp_ne n (signed_nat 0) }) 
        (\<lambda>xsi. doM {
          (p,xsi) \<leftarrow> arl_pop_back xsi;
          free_elem p;
          return xsi
        }) 
        xsi;
      
      arl_free xsi
    }"
                                                                                
    lemma free_empty_stack_rule: "llvm_htriple (\<upharpoonleft>(stack_assn_raw A) [] xsi) (arl_free xsi) (\<lambda>_. \<box>)"
      unfolding stack_assn_raw_def
      apply vcg
      done
    
    lemma stack_assn_free[sepref_frame_free_rules]:
      assumes A: "MK_FREE A free_elem"
      shows "MK_FREE (stack_assn A) (stack_free free_elem)"
      apply rule
      
      supply [vcg_rules] = MK_FREED[OF A] free_empty_stack_rule
      unfolding stack_free_def 
      apply vcg_monadify
      
      apply (rewrite annotate_llc_while[where 
            I="\<lambda>xsi t. EXS xs. stack_assn A xs xsi ** \<up>(t=length xs)" 
        and R="measure id" ])
      unfolding stack_assn_def
      apply vcg
      done
  
  end  
  
  
  
  
  
  definition "test xs \<equiv> doN {
    \<^cancel>\<open>ASSERT (length xs > 2);\<close>
    (x\<^sub>1,xs) \<leftarrow> mop_list_pop_last xs;
    (x\<^sub>2,xs) \<leftarrow> mop_list_pop_last xs;
    RETURN ((x\<^sub>1,x\<^sub>2),xs)
  }"
    
  sepref_def test_impl is test :: 
    "(stack_assn' TYPE(64) (unat_assn' TYPE(32)))\<^sup>d 
      \<rightarrow>\<^sub>a (unat_assn' TYPE(32)\<times>\<^sub>aunat_assn' TYPE(32))\<times>\<^sub>astack_assn' TYPE(64) (unat_assn' TYPE(32))"
    unfolding test_def
    by sepref
    
  export_llvm test_impl file "test.ll"
  
    
  definition "test2 x \<equiv> doN {
    let xs = [];
    let xs = xs@[x];
    (x,xs) \<leftarrow> mop_list_pop_last xs;
    RETURN x
  }"

  
  
  
  sepref_def test2_impl is test2 :: "(unat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE(32)"  
    unfolding test2_def
    apply (rewrite stack_fold_custom_empty[where 'l=64])
    apply sepref
    done
    
    
  lemmas [llvm_inline] = swap_args2_def 
    
  
  export_llvm test2_impl is "uint32_t test2 (uint32_t)" file "test2.ll"
  
end  
