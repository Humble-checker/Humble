theory BitSet
  imports "II_Modest_Base.Bitwise_Ext" "II_Modest_Base.More_snat"
begin

  text \<open>
    This theory file implements a bitset which is abstractly represented by a set of natural numbers
    and implemented as a bit-packed array of boolean values.
  \<close>
  
  section \<open>General Lemmas\<close>
  
  
  lemma eq_nat_mod_div: "i mod n = x mod n \<Longrightarrow> i div n = x div n \<Longrightarrow> (x::nat) = i" 
    by (metis div_mod_decomp)
  
  lemma ndvd_pred_lmod: "0 < (m::nat) \<Longrightarrow> \<not>m dvd n \<Longrightarrow> (n - 1) mod m = (n mod m) - 1" 
    by (smt (verit) Suc_diff_1 Suc_to_right dvd_0_right mod_Suc mod_eq_0_iff_dvd not_gr_zero)
  
  lemma dvd_pred_lmod: "(n::nat) > 0 \<Longrightarrow> m > 0 \<Longrightarrow> m dvd n \<Longrightarrow> (n - 1) mod m = m - 1"
    by (metis Suc_diff_1 mod_Suc mod_eq_0_iff_dvd nat.simps(3) old.nat.simps(1))
  
  lemma ndvd_pred_ldiv: "0 < (m::nat) \<Longrightarrow> \<not>m dvd n \<Longrightarrow> (n - 1) div m = n div m" 
    proof -
      assume A1: "0 < m"
      and  A2: "\<not>m dvd n"
      then have B1:"n > 0" and B2:"m > 1" 
        apply(fold mod_greater_zero_iff_not_dvd)
        by (metis gr0I mod_less less_one mod_by_1 nat_neq_iff)+
      hence "m * ((n - 1) div m) + (n - 1) mod m + 1 = m * (n div m) + n mod m"
        by force
      moreover have "((n - 1) mod m) + 1 = n mod m"
        using ndvd_pred_lmod[OF _ A2] A2 B2
        apply(fold mod_greater_zero_iff_not_dvd)
        by auto
      ultimately have "m * ((n - 1) div m) = m * (n div m)" 
        by linarith
      then show ?thesis 
        by fastforce
    qed
  
  lemma dvd_pred_ldiv: 
    assumes MN0: "0 < (m::nat)"
    and NN0: "0 < n" 
    and NDM: "m dvd n" 
    shows "(n - 1) div m = n div m - 1"
    proof -
      from MN0 NN0 NDM have "m * (n div m) = m * ((n - 1) div m) + (n - 1) mod m + 1"
        by simp
      also have "... = m * ((n - 1) div m) + (m - 1) + 1"
        using dvd_pred_lmod[OF NN0 MN0 NDM] 
        by argo
      also have "... = m * ((n - 1) div m) + m"
        using MN0
        by auto
      also have "... = m * ((n - 1) div m + 1)"
        by algebra
      finally have "n div m = (n - 1) div m + 1"
        using MN0 mult_left_cancel by blast
      thus ?thesis by auto
    qed
      
  
  lemma distrib_div_add: "((a::nat) mod c + b mod c < c) \<Longrightarrow> a div c + b div c = (a + b) div c"
    proof -
      assume ASM: "a mod c + b mod c < c"
      hence DIS: "(a + b) mod c = a mod c + b mod c" 
        by (metis mod_add_eq nat_mod_eq)
  
      have CN0:"c > 0" using ASM by linarith
  
      have A1: "a + b = c * ((a + b) div c) + (a + b) mod c" by presburger
      have "a + b = c * (a div c) + c * (b div c) + a mod c + b mod c" by simp
      also have "... = c * ((a div c) + (b div c)) + a mod c + b mod c" by algebra
      finally have "c * ((a + b) div c) + (a + b) mod c = c * ((a div c) + (b div c)) + a mod c + b mod c" using A1 by argo
      thus ?thesis using DIS CN0 by force
    qed
  
  
  section \<open>Rounded up division\<close>
  
  text \<open>
    Standard division in Isabelle rounds down. We need to round up to determine the size of our 
    array storing the bitset.
  \<close>
  
  definition div_round_up :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
    "div_round_up n m = (if m dvd n then n div m else n div m + 1)"
 
 (*TODO, actually this one seems more efficient*)
  definition div_round_up2 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "div_round_up2 n m = (n + m - 1) div m"
  
  definition div_up :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
    "div_up n m = (if n = 0 then 0 else ((n - 1) div m + 1))"
  
  lemma div_round_up_eq_div_round_up2: "m > 0 \<Longrightarrow> div_round_up n m = div_round_up2 n m"
    proof -
      assume MN0: "m > 0"
      {
        fix n m::nat
        assume MN0: "m > 0"
        assume DVD: "m dvd n"
        hence "n > 0 \<Longrightarrow> ((n + m) - 1) div m = (n + m) div m - 1" 
          using dvd_pred_ldiv[OF _ _ DVD[folded dvd_add_triv_right_iff[of m n]]] MN0
          by blast
        also have "... = n div m + m div m - 1"
          by (simp add: DVD)
        finally have "n > 0 \<Longrightarrow> n div m = ((n + m) - 1) div m" 
          using MN0
          by force
        hence "n div m = (n + m - 1) div m" 
          apply(cases "n = 0") 
          apply presburger
          apply auto
          done
      } note AUX1 = this
  
      {      
        fix n m::nat
        assume MN0: "m > 0"
        assume NDVD: "\<not>m dvd n"
        have "(n + m - 1) div m = n div m + 1" 
          using ndvd_pred_ldiv[OF MN0 NDVD[folded dvd_add_triv_right_iff[of m n]]]
          by (simp add: MN0)
      } note AUX2 = this
  
      from AUX1[OF MN0, of n] AUX2[OF MN0, of n] show ?thesis
        by(auto simp: div_round_up_def div_round_up2_def)
    qed
  
  
  lemma div_round_up2_eq_div_up: "m > 0 \<Longrightarrow> div_round_up2 n m = div_up n m"
    proof(cases "n = 0")
      case True
      moreover assume "m > 0"
      ultimately show ?thesis 
        unfolding div_round_up2_def div_up_def 
        by simp
    next
      case False
      assume A2: "m > 0"
  
      have "(n - 1) div m + 1 = (n - 1) div m + m div m"
        by (simp add: A2)
      also have "... = ((n - 1) + m) div m" 
        apply(rule distrib_div_add)
        by (auto simp: A2)
      also have "... = (n + m - 1) div m"
        using False by fastforce
      finally show ?thesis
        unfolding div_round_up2_def div_up_def
        by simp
    qed
  
  
  lemma "m > 0 \<Longrightarrow> div_round_up n m = div_up n m"
    using div_round_up_eq_div_round_up2 div_round_up2_eq_div_up
    by simp
              
       
  lemma round_up_ge: "m > 0 \<Longrightarrow> n \<le> m * div_up n m"
    unfolding div_up_def
    apply(simp split: if_split)
    apply(fold minus_mod_eq_mult_div[of "n - Suc 0" m])
    apply(cases "m dvd n")  
    using dvd_pred_lmod apply auto[]
    using ndvd_pred_lmod apply simp
    apply(fold mod_greater_zero_iff_not_dvd)
    apply simp 
    using pos_mod_bound 
    by (meson le_add_diff mod_le_divisor)
  
  
  lemma round_up_le: "m > 0 \<Longrightarrow> m * div_up n m < n + m"
    unfolding div_up_def
    apply(simp split: if_split)
    apply(fold minus_mod_eq_mult_div[of "n - Suc 0" m])
    apply(cases "m dvd n")
    using dvd_pred_lmod apply auto[]
    using ndvd_pred_lmod by simp
  
  lemma div_up_minus_1_leq_div: "div_up n m - Suc 0 \<le> n div m"
    by (auto simp: div_up_def div_le_mono)
  
  lemma div_leq_div_up: "n div m \<le> div_up n m"
    apply (clarsimp simp: div_up_def )
    by (metis One_nat_def Suc_pred bot_nat_0.not_eq_extremum divide_nat_def dvd_pred_ldiv less_imp_le_nat nat_in_between_eq(1) ndvd_pred_ldiv)
  
  lemma div_up_mod: "a mod b > 0 \<Longrightarrow> b > 0 \<Longrightarrow> div_up a b - 1 = (a div b)"
    unfolding div_up_def
    using mod_greater_zero_iff_not_dvd ndvd_pred_ldiv by force
  
  lemma div_up_nmod: "a mod b = 0 \<Longrightarrow> b > 0 \<Longrightarrow> div_up a b = (a div b)"
    unfolding div_up_def
    using dvd_pred_ldiv by fastforce
  
  lemma div_up_mult_mod: "a mod b > 0 \<Longrightarrow> b * div_up a b - b = b * (a div b)"
    using div_up_mod
    by (metis bot_nat_0.not_eq_extremum factor_minus mult_0)
  
  lemma div_up_mult_nmod: "a mod b = 0 \<Longrightarrow> b * div_up a b = b * (a div b)"
    using div_up_nmod by auto
  
  lemma div_up_to_mod_if_mod: "a mod b > 0 \<Longrightarrow> b * div_up a b - b = a - (a mod b)"
    apply(subst div_up_mult_mod)
    apply assumption
    by (metis minus_mod_eq_mult_div)
  
  lemma div_up_to_mod_if_nmod: "a mod b = 0 \<Longrightarrow> b * div_up a b = a - (a mod b)"
    apply(subst div_up_mult_nmod)
    apply assumption
    by force
  
  subsection \<open>Concrete Operation\<close>
  
  sepref_decl_op div_round_up: "div_up" :: "[\<lambda> (n, m). m > 0]\<^sub>f nat_rel \<times>\<^sub>r nat_rel \<rightarrow> nat_rel" .
  
  definition "div_round_up_impl n m = 
      do{
        ASSERT(m > 0);
        if n = 0 then
          RETURN 0
        else
          do {
            ASSERT((n - 1) div m + 1 \<le> n);
            RETURN((n - 1) div m + 1)
          }
      }"
  
  
  subsection \<open>Refinement\<close>
  
  lemma div_round_up2_refine: "(div_round_up_impl, mop_div_round_up) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
    unfolding div_round_up_impl_def mop_div_round_up_def op_div_round_up_def div_up_def
    apply (clarsimp simp: )
    subgoal for n m
      apply(cases "0 < m")
      subgoal
        apply(auto simp: refine_pw_simps pw_nres_rel_iff Let_def) 
        apply (metis Suc_le_mono Suc_pred div_le_dividend)
        by (metis Suc_le_mono Suc_pred div_le_dividend)
      subgoal
        by(auto simp: refine_pw_simps pw_nres_rel_iff Let_def)
      done
    done
  
  
  subsection \<open>Refinement to LLVM\<close>
    
  sepref_def div_round_up_ll is "uncurry div_round_up_impl" :: "(snat_assn' TYPE('a::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('a))\<^sup>k \<rightarrow>\<^sub>a (snat_assn' TYPE('a))"
    unfolding div_round_up_impl_def
    apply (annot_snat_const "TYPE('a)")
    apply sepref
    done
  
  sepref_decl_impl(ismop) div_round_up_ll.refine[FCOMP div_round_up2_refine] .
  
  
  
  section \<open>Bitset\<close>
  
  abbreviation "wsmask \<equiv> mask::(nat\<Rightarrow>size_t)"
  
  subsection \<open>Abstract Operations\<close>
  
  definition "op_set_empty_custom N = {}"
  
  definition "op_set_upt_n_custom N = {0..<N}"
  
  subsection \<open>Concrete Operations\<close>
  
  type_synonym bitset = "size_t list"
  
  definition bitset_get :: "nat \<Rightarrow> bitset \<Rightarrow> bool" where "bitset_get i bi \<equiv> (bi ! (i div len_size_T) !! (i mod len_size_T))"
  
  definition bitset_empty :: "nat \<Rightarrow> bitset" where "bitset_empty n = replicate (op_div_round_up n len_size_T) 0"
  
  definition bitset_upt_n :: "nat \<Rightarrow> bitset" where "bitset_upt_n n = (let N = op_div_round_up n len_size_T in (op_array_custom_replicate N (NOT 0))[N-1:=wsmask ((len_size_T * N) - n)])"
  
  definition "bitset_insert i bs = (let j = i div len_size_T; k = i mod len_size_T in bs[j:=op_set_bit (bs ! j) k])"
  
  definition "bitset_delete i bs = (let j = i div len_size_T; k = i mod len_size_T in bs[j:=op_unset_bit (bs ! j) k])"
  
  subsection \<open>Refinement Relation\<close>
  
  definition bitset_\<alpha> :: "bitset \<Rightarrow> nat set" where "bitset_\<alpha> bs = Collect (\<lambda> i. bitset_get i bs \<and> i < len_size_T * length bs)"
  
  definition bitset_invar :: "nat \<Rightarrow> bitset \<Rightarrow> bool" where "bitset_invar n bs = (n \<le> LENGTH(size_T) * length bs)"
  
  definition "bitset_rel n = br bitset_\<alpha> (bitset_invar n)"
  
  
  subsection \<open>Operation Abstraction\<close>
  
  
  lemma bitset_empty_\<alpha>[simp]: "bitset_\<alpha> (bitset_empty n) = {}"
    unfolding bitset_\<alpha>_def bitset_empty_def bitset_get_def
    apply auto
    done
  
  lemma bitset_get_\<alpha>[simp]: "i < LENGTH(size_T) * length bs \<Longrightarrow> bitset_get i bs \<longleftrightarrow> i \<in> bitset_\<alpha> bs"
    unfolding bitset_\<alpha>_def 
    apply simp
    done
  
  lemma bitset_insert_\<alpha>[simp]: "i < LENGTH(size_T) * length bs \<Longrightarrow> bitset_\<alpha> (bitset_insert i bs) = insert i (bitset_\<alpha> bs)"
    unfolding bitset_insert_def bitset_\<alpha>_def op_set_bit_def bitset_get_def Let_def 
    apply (auto simp: nth_list_update' bit_set_bit_word_iff mult.commute td_gal_lt intro: eq_nat_mod_div)
    done
    
  lemma bitset_delete_\<alpha>[simp]: "bitset_\<alpha> (bitset_delete i bs) = bitset_\<alpha> bs - {i}"
    unfolding bitset_delete_def bitset_\<alpha>_def op_unset_bit_def bitset_get_def Let_def 
    apply (auto simp: nth_list_update' bit_set_bit_word_iff mult.commute td_gal_lt intro: eq_nat_mod_div)
    done
  
  lemma bitset_invar_n_bound: "bitset_invar n bs \<Longrightarrow> n \<le> length bs * 64"
    unfolding bitset_invar_def
    by fastforce
  
  
  subsection \<open>Invariant Preservation\<close>
  
  lemma bitset_empty_invar[simp]: "bitset_invar n (bitset_empty n)"
    unfolding bitset_invar_def bitset_empty_def
    apply (auto simp: round_up_ge)
    done
  
  lemma bitset_upt_n_invar[simp]: "bitset_invar n (bitset_upt_n n)"
    unfolding bitset_invar_def bitset_upt_n_def
    apply (auto simp: Let_def round_up_ge)
    done

  lemma bitset_insert_invar [simp]: "bitset_invar n bs \<Longrightarrow> bitset_invar n (bitset_insert i bs)"
    unfolding bitset_invar_def bitset_insert_def op_set_bit_def Let_def
    by simp
  
  lemma bitset_delete_invar [simp]: "bitset_invar n bs \<Longrightarrow> bitset_invar n (bitset_delete i bs)"
    unfolding bitset_invar_def bitset_delete_def op_set_bit_def Let_def
    by simp 
  
  
  lemma bitset_rel_n_bound: "(bs, b) \<in> bitset_rel n \<Longrightarrow> n \<le> length bs * 64"
    unfolding bitset_rel_def
    by(auto simp: in_br_conv bitset_invar_n_bound)
  
  lemma bitset_rel_n_bound_aux: "a < n \<Longrightarrow> (bs, b) \<in> bitset_rel n \<Longrightarrow> a < length bs * 64"
    by (auto dest: bitset_rel_n_bound)
  
  
  subsection \<open>Operation Refinement\<close>
 
  
  lemma bitset_invar_i_bound: "i < n \<Longrightarrow> bitset_invar n bs \<Longrightarrow> i < len_size_T * length bs "
    unfolding bitset_invar_def
    by simp
  
  lemma bitset_get_refine: "(bitset_get, op_set_member) \<in> (nbn_rel n) \<rightarrow> bitset_rel n \<rightarrow> bool_rel"
    apply (auto simp: bitset_rel_def in_br_conv bitset_invar_i_bound)
    done
  
  lemma bitset_insert_refine: "(bitset_insert, op_set_insert) \<in> (nbn_rel n) \<rightarrow> bitset_rel n \<rightarrow> bitset_rel n"
    apply(auto simp: bitset_rel_def in_br_conv bitset_invar_i_bound) 
    done
  
  lemma bitset_delete_refine: "(bitset_delete, op_set_delete) \<in> (nbn_rel n) \<rightarrow> bitset_rel n \<rightarrow> bitset_rel n"
    apply(auto simp: bitset_rel_def in_br_conv) 
    done
  
  lemma bitset_upt_n_ll_aux1: "x > 0 \<Longrightarrow> Suc 0 \<le> div_up x 64"
    by (metis less_Suc0 linorder_not_le mult_zero_right round_up_ge zero_less_numeral)
  
  subsection \<open>Bitset Assertion\<close>
  
  type_synonym bitseti = "size_t ptr"
  
  definition 
    bitset_assn_raw :: "bitset \<Rightarrow> bitseti \<Rightarrow> llvm_amemory \<Rightarrow> bool" where
    "bitset_assn_raw = IICF_Array.array_slice_assn (id_assn::size_t \<Rightarrow> _)" 
  
  definition "bitset_assn n = hr_comp bitset_assn_raw (bitset_rel n)"
  
  
  subsection \<open>Refinement to LLVM\<close>
  
  sepref_def bitset_get_ll is "uncurry (RETURN oo bitset_get)" :: "[\<lambda>(i,l). i<length l * len_size_T]\<^sub>a size_assn\<^sup>k *\<^sub>a bitset_assn_raw\<^sup>k \<rightarrow> bool1_assn"
    unfolding bitset_get_def bitset_assn_raw_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done
  
  
  sepref_def bitset_insert_ll is "uncurry (RETURN oo bitset_insert)" :: "[\<lambda>(i,l). i<length l * len_size_T]\<^sub>a size_assn\<^sup>k *\<^sub>a bitset_assn_raw\<^sup>d \<rightarrow> bitset_assn_raw"
    unfolding bitset_insert_def bitset_assn_raw_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done
  
  sepref_def bitset_delete_ll is "uncurry (RETURN oo bitset_delete)" :: "[\<lambda>(i,l). i<length l * len_size_T]\<^sub>a size_assn\<^sup>k *\<^sub>a bitset_assn_raw\<^sup>d \<rightarrow> bitset_assn_raw"
    unfolding bitset_delete_def bitset_assn_raw_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done
  
  
  subsection \<open>Refinement Composition\<close>
  
  lemma P_hfref_to_dep_hfref: "(\<And>n. (f,g) \<in> [(\<lambda> i. i = n)]\<^sub>a RR \<rightarrow> (T n)) \<Longrightarrow> (f,g) \<in> RR \<rightarrow>\<^sub>a\<^sub>d T"
    apply (auto simp: hfref_def)
    done
  
  context 
    notes [fcomp_norm_unfold] = bitset_assn_def[symmetric]
    notes [simp] = bitset_rel_n_bound_aux
  begin
  
    lemmas mop_bitset_get_hnr[sepref_fr_rules] = bitset_get_ll.refine[FCOMP bitset_get_refine]
    lemmas mop_bitset_insert_hnr[sepref_fr_rules] = bitset_insert_ll.refine[FCOMP bitset_insert_refine]
    lemmas mop_bitset_delete_hnr[sepref_fr_rules] = bitset_delete_ll.refine[FCOMP bitset_delete_refine]

  end


  section \<open>Owned Bitsets\<close>

  text \<open>\<^const>\<open>bitset_assn\<close> above is built on \<^const>\<open>IICF_Array.array_slice_assn\<close>: a \<^emph>\<open>view\<close> of
    caller-owned memory. That is exactly right for the input MDP's target / avoid sets, which Modest
    passes in and the generated code must neither allocate nor release. But it also means such a
    bitset can be neither created nor destroyed: \<open>array_slice_assn\<close> has no \<open>narray_new_init\<close>, and
    (soundly) no \<open>MK_FREE\<close> rule --- one cannot deallocate part of somebody else's array.

    Algorithms that need \<^emph>\<open>scratch\<close> or \<^emph>\<open>freshly built\<close> bitsets need the owned variant defined here,
    backed by a full \<^const>\<open>IICF_Array.array_assn\<close>, which has both \<open>narray_new_init\<close> and
    \<open>array_mk_free\<close>. Both variants refine the same \<^const>\<open>bitset_rel\<close>, so the abstract operations and
    all their correctness lemmas above are shared --- only the assertion (and hence the ownership
    discipline of the emitted code) differs.\<close>

  definition bitset_own_assn_raw :: "bitset \<Rightarrow> bitseti \<Rightarrow> llvm_amemory \<Rightarrow> bool" where
    "bitset_own_assn_raw = IICF_Array.array_assn (id_assn::size_t \<Rightarrow> _)"

  definition "bitset_own_assn n = hr_comp bitset_own_assn_raw (bitset_rel n)"

  text \<open>The point of the exercise: an owned bitset is freeable. \<open>MK_FREE_hrcompI\<close> peels the
    \<^const>\<open>hr_comp\<close> and \<open>array_mk_free\<close> discharges the array, both already in
    \<open>sepref_frame_free_rules\<close>.\<close>
  schematic_goal bitset_own_mk_free[sepref_frame_free_rules]: "MK_FREE (bitset_own_assn n) ?f"
    unfolding bitset_own_assn_def bitset_own_assn_raw_def
    by (rule sepref_frame_free_rules)+

  subsection \<open>Refinement to LLVM\<close>

  sepref_def bitset_own_get_ll is "uncurry (RETURN oo bitset_get)"
    :: "[\<lambda>(i,l). i<length l * len_size_T]\<^sub>a size_assn\<^sup>k *\<^sub>a bitset_own_assn_raw\<^sup>k \<rightarrow> bool1_assn"
    unfolding bitset_get_def bitset_own_assn_raw_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done

  sepref_def bitset_own_insert_ll is "uncurry (RETURN oo bitset_insert)"
    :: "[\<lambda>(i,l). i<length l * len_size_T]\<^sub>a size_assn\<^sup>k *\<^sub>a bitset_own_assn_raw\<^sup>d \<rightarrow> bitset_own_assn_raw"
    unfolding bitset_insert_def bitset_own_assn_raw_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done

  sepref_def bitset_own_delete_ll is "uncurry (RETURN oo bitset_delete)"
    :: "[\<lambda>(i,l). i<length l * len_size_T]\<^sub>a size_assn\<^sup>k *\<^sub>a bitset_own_assn_raw\<^sup>d \<rightarrow> bitset_own_assn_raw"
    unfolding bitset_delete_def bitset_own_assn_raw_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done

  text \<open>The other half of the point: an owned bitset can be \<^emph>\<open>created\<close>. \<^const>\<open>bitset_empty\<close> is already
    proven to abstract to \<^term>\<open>{}\<close> (@{thm [source] bitset_empty_\<alpha>}) and to satisfy the invariant
    (@{thm [source] bitset_empty_invar}); all that was missing is a monadic form whose word count is
    computed by the registered \<^const>\<open>mop_div_round_up\<close>, so that \<open>sepref\<close> can allocate the array.

    This is what lets a caller stop supplying pre-zeroed scratch bitsets: an operation that
    initialises its own bitsets is \<^emph>\<open>total\<close>, whereas one taking them as arguments can only be correct
    under an \<open>= {}\<close> precondition that nothing outside the proof enforces.\<close>
  definition bitset_empty_impl :: "nat \<Rightarrow> bitset nres" where
    "bitset_empty_impl n = do {
       k \<leftarrow> mop_div_round_up n len_size_T;
       RETURN (replicate k 0) }"

  text \<open>An \<^emph>\<open>equation\<close>, not just \<open>\<le>\<close>: the only \<^const>\<open>ASSERT\<close> is \<open>len_size_T > 0\<close>, which holds
    outright, so the \<open>FCOMP\<close> at the use site can rewrite the concrete side to a plain \<^const>\<open>RETURN\<close>
    (the \<open>mk_pfin_one_pair_alt\<close> pattern).\<close>
  lemma bitset_empty_impl_alt: "bitset_empty_impl n = RETURN (bitset_empty n)"
    unfolding bitset_empty_impl_def bitset_empty_def mop_div_round_up_def op_div_round_up_def
    by simp

  lemma bitset_empty_rel: "(bitset_empty n, {}) \<in> bitset_rel n"
    unfolding bitset_rel_def by (auto simp: in_br_conv)

  sepref_def bitset_empty_ll is "bitset_empty_impl"
    :: "size_assn\<^sup>k \<rightarrow>\<^sub>a bitset_own_assn_raw"
    unfolding bitset_empty_impl_def bitset_own_assn_raw_def
    apply (rewrite array_fold_custom_replicate)
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done

  subsection \<open>Refinement Composition\<close>

  context
    notes [fcomp_norm_unfold] = bitset_own_assn_def[symmetric]
    notes [simp] = bitset_rel_n_bound_aux
  begin

    lemmas mop_bitset_own_get_hnr[sepref_fr_rules] =
      bitset_own_get_ll.refine[FCOMP bitset_get_refine]
    lemmas mop_bitset_own_insert_hnr[sepref_fr_rules] =
      bitset_own_insert_ll.refine[FCOMP bitset_insert_refine]
    lemmas mop_bitset_own_delete_hnr[sepref_fr_rules] =
      bitset_own_delete_ll.refine[FCOMP bitset_delete_refine]

  end


end