theory Array_Nat_Partition
  imports "II_Modest_Base.More_B_Assn" "II_Modest_Base.More_snat" "II_Modest_Base.Bind_Const" 
begin


section \<open>Snat Array Map\<close>

type_synonym 'v dsm = "'v \<Rightarrow> nat option"

type_synonym anpar = "nat set list"

type_synonym anparc = "nat \<times> nat dsm"
type_synonym anparc' = "nat \<times> ((nat, nat) i_map)"

type_synonym anpari = "64 Word.word \<times> 64 Word.word ptr"

locale disj_set_list_defs =
  fixes N::nat \<comment> \<open>The largest natural number the sets can contain\<close>
begin

  abbreviation "elem_assn \<equiv> b_assn size_assn (\<lambda> i. i < N)"

  definition disj_set_id_none :: "nat option" where "disj_set_id_none = None"

  lemmas [sepref_fr_rules] = snat.hn_None[folded disj_set_id_none_def]
  sepref_register disj_set_id_none 


  definition "disj_empty_def = snat.am2_empty"


  definition disj_set_id_am_assn :: "_ \<Rightarrow> 64 Word.word ptr \<Rightarrow> _" where "disj_set_id_am_assn = snat.am_assn N"

  definition disj_set_list_assn_raw :: "anparc \<Rightarrow> anpari \<Rightarrow> assn" where  "disj_set_list_assn_raw = size_assn \<times>\<^sub>a disj_set_id_am_assn"

end

section \<open>Abstract Disjoint Set List\<close>

subsection \<open>Abstract Operations\<close>

definition op_anpar_empty :: "nat \<Rightarrow> anpar" where "op_anpar_empty N = []"

definition op_anpar_count :: "anpar \<Rightarrow> nat" where "op_anpar_count XS = length XS"

definition op_anpar_expand :: "anpar \<Rightarrow> nat \<Rightarrow> anpar" where "op_anpar_expand XS m = XS @ (replicate m {})"

definition op_anpar_mem_any :: "anpar \<Rightarrow> nat \<Rightarrow> bool" where "op_anpar_mem_any XS v = (\<exists> i < length XS. v \<in> XS ! i)"

definition op_anpar_mem_of :: "anpar \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "op_anpar_mem_of XS v i = (if i < length XS then v \<in> XS ! i else False)"

definition op_eq_set_mem :: "anpar \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "op_eq_set_mem XS v w = (\<exists> i < length XS. v \<in> XS ! i \<and> w \<in> XS ! i)"

definition op_anpar_move :: "anpar \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> anpar" where "op_anpar_move XS v i = (map (\<lambda> X. X - {v}) XS)[i:=insert v (XS ! i)]"

definition op_anpar_remove :: "anpar \<Rightarrow> nat \<Rightarrow> anpar" where "op_anpar_remove XS v = map (\<lambda> X. X - {v}) XS"


section \<open>Concrete Disjoint Set List\<close>



subsection \<open>Abstraction relation\<close>

definition disj_set_list_\<alpha> :: "anparc \<Rightarrow> anpar" where "disj_set_list_\<alpha> = (\<lambda> (n,M). map (\<lambda> i. {v. M v = Some i}) [0..<n])"

definition disj_set_list_invar :: "anparc \<Rightarrow> bool" where "disj_set_list_invar = (\<lambda> (n,M). (\<forall> v. case M v of Some i \<Rightarrow> i < n | None \<Rightarrow> True))"

definition "disj_set_list_rel = br disj_set_list_\<alpha> disj_set_list_invar"


lemma disj_set_list_invar_geq_n_empty: "disj_set_list_invar (n, M) \<Longrightarrow> i \<ge> n \<Longrightarrow> {v. M v = Some i} = {}" 
  by(auto simp: disj_set_list_invar_def le_def split: option.splits)

lemma disj_set_list_invarD: "disj_set_list_invar (n, M) \<Longrightarrow> M v = Some i \<Longrightarrow> i < n"
  unfolding disj_set_list_invar_def
  by(auto split: option.splits)

lemma disj_set_list_rel_n_eq_len: "((n, M), XS) \<in> disj_set_list_rel \<Longrightarrow> n = length XS"
  unfolding disj_set_list_rel_def
  by(auto simp: in_br_conv disj_set_list_\<alpha>_def)

lemma disj_set_list_rel_n_eq_len_leq: "((n, M), XS) \<in> disj_set_list_rel \<Longrightarrow> n + b < c \<longleftrightarrow> length XS + b < c"
  unfolding disj_set_list_rel_def
  by(auto simp: in_br_conv disj_set_list_\<alpha>_def)


lemma disj_set_list_rel_ex_mem: "((n, M), XS) \<in> disj_set_list_rel \<Longrightarrow> (\<exists>i<length XS. b \<in> XS ! i) = (\<exists>y. M b = Some y)" 
  unfolding disj_set_list_rel_def
  by(fastforce simp: in_br_conv disj_set_list_\<alpha>_def dest!: disj_set_list_invarD) 


subsection \<open>Concrete Operations\<close>


definition disj_set_list_empty :: "nat \<Rightarrow> anparc" where "disj_set_list_empty N = (let M = op_am_custom_empty N in (0,M))"
sepref_register disj_set_list_empty :: "nat \<Rightarrow> anparc'"

definition disj_set_count :: "anparc \<Rightarrow> nat" where "disj_set_count = (\<lambda> (n,M). n)"
sepref_register disj_set_count :: "anparc' \<Rightarrow> nat"

definition expand_capacity :: "anparc \<Rightarrow> nat \<Rightarrow> anparc" where "expand_capacity = (\<lambda> (n,M) m. (n + m, M))"
sepref_register expand_capacity :: "anparc' \<Rightarrow> nat \<Rightarrow> anparc'"

definition is_member_any :: "anparc \<Rightarrow> nat \<Rightarrow> bool" where "is_member_any = (\<lambda> (n,M) v. \<not>is_None (op_map_lookup v M))"
sepref_register is_member_any :: "anparc' \<Rightarrow> nat \<Rightarrow> bool"

definition is_member_of :: "anparc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "is_member_of = (\<lambda> (n,M) v i. let vo = op_map_lookup v M in i = the vo)"
sepref_register is_member_of :: "anparc' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"

definition eq_set_member :: "anparc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "eq_set_member = (\<lambda> (n,M) v w. the (op_map_lookup v M) = the (op_map_lookup w M))"
sepref_register eq_set_member :: "anparc' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"

definition move_elem :: "anparc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> anparc" where "move_elem = (\<lambda> (n,M) v i. (n,M(v\<mapsto>i)))"
sepref_register move_elem :: "anparc' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> anparc'"

definition remove_elem :: "anparc \<Rightarrow> nat \<Rightarrow> anparc" where "remove_elem = (\<lambda> (n,M) v. (n,M(v:=None)))"
sepref_register remove_elem :: "anparc' \<Rightarrow> nat \<Rightarrow> anparc'"

subsection \<open>Correctness of abstraction\<close>

subsubsection \<open>Abstraction correctness\<close>

lemma disj_set_list_empty_\<alpha>: "disj_set_list_\<alpha> (disj_set_list_empty N) = op_anpar_empty N"
  by(auto simp: disj_set_list_\<alpha>_def op_anpar_empty_def disj_set_list_empty_def)

lemma disj_set_count_\<alpha>: "disj_set_count (n, M) = op_anpar_count (disj_set_list_\<alpha> (n, M))"
  unfolding disj_set_list_\<alpha>_def disj_set_count_def op_anpar_count_def
  by auto

lemma expand_capacity_\<alpha>: "disj_set_list_invar (n, M) \<Longrightarrow> disj_set_list_\<alpha> (expand_capacity (n, M) m) = op_anpar_expand (disj_set_list_\<alpha> (n, M)) m"
  unfolding expand_capacity_def op_anpar_expand_def
  apply(clarsimp simp: disj_set_list_\<alpha>_def split: option.splits) 
  apply(subst upt_add_eq_append)
  subgoal
    by simp
  subgoal
    apply(simp only: map_append)
    apply clarsimp
    apply(induction m)
    subgoal
      by simp
    subgoal for m
      unfolding replicate_Suc_conv_snoc
      apply clarsimp
      apply(drule disj_set_list_invar_geq_n_empty[where ?i = "n + m"])
      by auto
    done
  done

lemma is_member_any_\<alpha>: "disj_set_list_invar (n, M) \<Longrightarrow> is_member_any (n, M) = op_anpar_mem_any (disj_set_list_\<alpha> (n, M))"
  unfolding op_anpar_mem_any_def disj_set_list_\<alpha>_def is_member_any_def
  apply clarsimp
  apply (rule ext)
  by (force dest: disj_set_list_invarD)

lemma is_member_of_\<alpha>: "disj_set_list_invar (n, M) \<Longrightarrow> i < length (disj_set_list_\<alpha> (n, M)) \<Longrightarrow> v \<in> disj_set_list_\<alpha> (n, M) ! i \<Longrightarrow>  is_member_of (n, M) v = op_anpar_mem_of (disj_set_list_\<alpha> (n, M)) v"
  unfolding is_member_of_def op_anpar_mem_of_def disj_set_list_\<alpha>_def Let_def 
  apply clarsimp
  apply(rule ext)+
  by fast

lemma eq_set_member_\<alpha>:  "disj_set_list_invar (n, M) \<Longrightarrow> i < length (disj_set_list_\<alpha> (n, M)) \<Longrightarrow> v \<in> disj_set_list_\<alpha> (n, M) ! i \<Longrightarrow>
    j < length (disj_set_list_\<alpha> (n, M)) \<Longrightarrow> w \<in> disj_set_list_\<alpha> (n, M) ! j \<Longrightarrow> eq_set_member (n, M) v w \<longleftrightarrow> op_eq_set_mem (disj_set_list_\<alpha> (n, M)) v w"
  unfolding eq_set_member_def op_eq_set_mem_def disj_set_list_\<alpha>_def
  by auto

lemma move_elem_\<alpha>: "disj_set_list_invar (n, M) \<Longrightarrow> disj_set_list_\<alpha> (move_elem (n, M) v i) = op_anpar_move (disj_set_list_\<alpha> (n, M)) v i"
  unfolding disj_set_list_\<alpha>_def op_anpar_move_def move_elem_def
  apply (clarsimp split: option.splits)
  apply(rule nth_equalityI)
  subgoal
    by simp
  subgoal for j
    apply clarsimp
    apply(cases "i = j")
    subgoal
      by auto
    subgoal
      by auto
    done
  done

lemma remove_elem_\<alpha>: "disj_set_list_invar (n, M) \<Longrightarrow> disj_set_list_\<alpha> (remove_elem (n, M) v) = op_anpar_remove (disj_set_list_\<alpha> (n, M)) v"
  unfolding op_anpar_remove_def disj_set_list_\<alpha>_def remove_elem_def
  by fastforce

subsubsection \<open>Invariant preservation\<close>

lemma disj_set_list_empty_invar: "disj_set_list_invar (disj_set_list_empty N)"
  by(auto simp: disj_set_list_invar_def disj_set_list_empty_def)

lemma expand_capacity_invar: "disj_set_list_invar (n, M) \<Longrightarrow> disj_set_list_invar (expand_capacity (n, M) m)"
  unfolding disj_set_list_invar_def expand_capacity_def
  by (fastforce split: option.splits) 

lemma move_elem_invar: "disj_set_list_invar (n, M) \<Longrightarrow> i < length (disj_set_list_\<alpha> (n, M)) \<Longrightarrow> disj_set_list_invar (move_elem (n, M) v i)"
  unfolding disj_set_list_invar_def move_elem_def disj_set_list_\<alpha>_def
  by(auto split: option.split)

lemma remove_elem_invar: "disj_set_list_invar (n, M) \<Longrightarrow> disj_set_list_invar (remove_elem (n, M) v)"
  unfolding remove_elem_def disj_set_list_invar_def
  by (auto split: option.splits)



subsubsection \<open>Refinement correcness\<close>

lemma disj_set_list_empty_correct: "(disj_set_list_empty, op_anpar_empty) \<in> nat_rel \<rightarrow> disj_set_list_rel"
  by(auto simp: disj_set_list_rel_def in_br_conv disj_set_list_empty_\<alpha> disj_set_list_empty_invar)

lemma disj_set_count_correct: "(disj_set_count, op_anpar_count) \<in> disj_set_list_rel \<rightarrow> nat_rel"
  unfolding disj_set_list_rel_def
  by(auto simp: in_br_conv disj_set_count_\<alpha>)

lemma expand_capacity_correct: "(expand_capacity, op_anpar_expand) \<in> disj_set_list_rel \<rightarrow> nat_rel \<rightarrow> disj_set_list_rel"
  unfolding disj_set_list_rel_def
  by(auto simp: in_br_conv expand_capacity_\<alpha> expand_capacity_invar) 

lemma is_member_any_correct: "(is_member_any, op_anpar_mem_any) \<in> disj_set_list_rel \<rightarrow> nat_rel \<rightarrow> bool_rel"
  unfolding disj_set_list_rel_def
  by(auto simp: in_br_conv is_member_any_\<alpha>)

lemma is_member_of_correct: "(uncurry2 is_member_of, uncurry2 op_anpar_mem_of) \<in> [\<lambda> ((XS,v),i). \<exists> i < length XS. v \<in> XS ! i]\<^sub>f ((disj_set_list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel) \<rightarrow> bool_rel"
  unfolding disj_set_list_rel_def
  by(auto intro!: frefI simp: in_br_conv is_member_of_\<alpha>)

lemma eq_set_member_correct: "(uncurry2 eq_set_member, uncurry2 op_eq_set_mem) \<in> [\<lambda> ((XS,v),w). (\<exists> i < length XS. v \<in> XS ! i) \<and> (\<exists> j < length XS. w \<in> XS ! j)]\<^sub>f ((disj_set_list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel) \<rightarrow> bool_rel"
  unfolding disj_set_list_rel_def
  by(auto intro!: frefI simp: in_br_conv eq_set_member_\<alpha>)

lemma move_elem_correct: "(uncurry2 move_elem, uncurry2 op_anpar_move) \<in> [\<lambda> ((XS,v),i). i < length XS]\<^sub>f ((disj_set_list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel) \<rightarrow> disj_set_list_rel"
  unfolding disj_set_list_rel_def
  by(auto intro!: frefI simp: in_br_conv move_elem_\<alpha> move_elem_invar)

lemma remove_elem_correct: "(remove_elem, op_anpar_remove) \<in> disj_set_list_rel \<rightarrow> nat_rel \<rightarrow> disj_set_list_rel"
  unfolding disj_set_list_rel_def
  by(auto simp: in_br_conv remove_elem_\<alpha> remove_elem_invar)

section \<open>Sepref Translations\<close>

context disj_set_list_defs
begin
                                                                        
  sepref_definition(in -) disj_set_list_empty_ll is "(RETURN o disj_set_list_empty)" :: "size_assn\<^sup>k \<rightarrow>\<^sub>a\<^sub>d disj_set_list_defs.disj_set_list_assn_raw"
    unfolding disj_set_list_defs.disj_set_list_assn_raw_def disj_set_list_defs.disj_set_id_am_assn_def disj_set_list_empty_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done

  sepref_definition disj_set_count_ll is "RETURN o disj_set_count" :: "disj_set_list_assn_raw\<^sup>k \<rightarrow>\<^sub>a size_assn"
    unfolding disj_set_list_assn_raw_def disj_set_id_am_assn_def disj_set_count_def
    apply sepref
    done

  sepref_definition expand_capacity_ll is "uncurry (RETURN oo expand_capacity)" :: "[\<lambda> ((n,M),m). n + m < max_size_t]\<^sub>a disj_set_list_assn_raw\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> disj_set_list_assn_raw"
    unfolding disj_set_list_assn_raw_def disj_set_id_am_assn_def expand_capacity_def
    apply sepref
    done

  sepref_definition is_member_any_ll is "(uncurry (RETURN oo is_member_any))" :: "disj_set_list_assn_raw\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding disj_set_list_assn_raw_def disj_set_id_am_assn_def is_member_any_def
    apply sepref
    done

  sepref_definition is_member_of_ll is "(uncurry2 (RETURN ooo is_member_of))" :: "[\<lambda> (((n,M),v),i). M v \<noteq> None]\<^sub>a disj_set_list_assn_raw\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> bool1_assn"
    unfolding disj_set_list_assn_raw_def disj_set_id_am_assn_def is_member_of_def
    apply sepref
    done
            
  sepref_definition eq_set_member_ll is "(uncurry2 (RETURN ooo eq_set_member))" :: "[\<lambda> (((n,M),v),w). M v \<noteq> None \<and> M w \<noteq> None]\<^sub>a disj_set_list_assn_raw\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow> bool1_assn"
    unfolding disj_set_list_assn_raw_def disj_set_id_am_assn_def eq_set_member_def
    apply sepref
    done

  sepref_definition move_elem_ll is "(uncurry2 (RETURN ooo move_elem))" :: "disj_set_list_assn_raw\<^sup>d *\<^sub>a elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a disj_set_list_assn_raw"
    unfolding disj_set_list_assn_raw_def disj_set_id_am_assn_def move_elem_def
    apply sepref
    done

  sepref_definition remove_elem_ll is "(uncurry (RETURN oo remove_elem))" :: "disj_set_list_assn_raw\<^sup>d *\<^sub>a elem_assn\<^sup>k \<rightarrow>\<^sub>a disj_set_list_assn_raw"
    unfolding disj_set_list_assn_raw_def disj_set_id_am_assn_def remove_elem_def
    apply sepref
    done

  concrete_definition(in -) disj_set_list_empty_ll' is disj_set_list_empty_ll_def
  concrete_definition(in -) disj_set_count_ll' is disj_set_list_defs.disj_set_count_ll_def
  concrete_definition(in -) expand_capacity_ll' is disj_set_list_defs.expand_capacity_ll_def
  concrete_definition(in -) is_member_any_ll' is disj_set_list_defs.is_member_any_ll_def
  concrete_definition(in -) is_member_of_ll' is disj_set_list_defs.is_member_of_ll_def
  concrete_definition(in -) eq_set_member_ll' is disj_set_list_defs.eq_set_member_ll_def
  concrete_definition(in -) move_elem_ll' is disj_set_list_defs.move_elem_ll_def
  concrete_definition(in -) remove_elem_ll' is disj_set_list_defs.remove_elem_ll_def

end


section \<open>Operation Composition\<close>

definition disj_set_list_assn :: "nat \<Rightarrow> anpar \<Rightarrow> anpari \<Rightarrow> assn" where "disj_set_list_assn N = hr_comp (disj_set_list_defs.disj_set_list_assn_raw N) disj_set_list_rel"


context 
  notes [fcomp_norm_unfold] = disj_set_list_assn_def[symmetric] hrr_comp_id_conv
  notes [simp] = disj_set_list_rel_ex_mem disj_set_list_rel_n_eq_len_leq
begin

  lemmas mop_disj_set_list_empty_hnr[sepref_fr_rules] = disj_set_list_empty_ll.refine[unfolded disj_set_list_empty_ll'.refine, FCOMP disj_set_list_empty_correct]
  lemmas mop_anpar_count_hnr[sepref_fr_rules] = disj_set_list_defs.disj_set_count_ll.refine[unfolded disj_set_count_ll'.refine, FCOMP disj_set_count_correct]
  lemmas mop_anpar_expand_hnr[sepref_fr_rules] = disj_set_list_defs.expand_capacity_ll.refine[unfolded expand_capacity_ll'.refine, FCOMP expand_capacity_correct]
  lemmas mop_anpar_mem_any_hnr[sepref_fr_rules] = disj_set_list_defs.is_member_any_ll.refine[unfolded is_member_any_ll'.refine, FCOMP is_member_any_correct]
  lemmas mop_anpar_mem_of_hnr[sepref_fr_rules] = disj_set_list_defs.is_member_of_ll.refine[unfolded is_member_of_ll'.refine, FCOMP is_member_of_correct]
  lemmas mop_eq_set_mem_hnr[sepref_fr_rules] = disj_set_list_defs.eq_set_member_ll.refine[unfolded eq_set_member_ll'.refine, FCOMP eq_set_member_correct]
  lemmas mop_anpar_move_hnr[sepref_fr_rules] = disj_set_list_defs.move_elem_ll.refine[unfolded move_elem_ll'.refine, FCOMP move_elem_correct]
  lemmas mop_anpar_remove_hnr[sepref_fr_rules] = disj_set_list_defs.remove_elem_ll.refine[unfolded remove_elem_ll'.refine, FCOMP remove_elem_correct]

end


end