theory SharedNat
  imports "II_Modest_Base.Nat_Interval" "II_Modest_Base.Bitwise_Ext" "II_Modest_Base.More_snat"
begin
  
  text \<open>
    This theory contains a definition for a tuple that is packed into one single word on the 
    implementation layer. E.g. the tuple (5,26), which in bits would be (101, 11010) can be packed
    into one 8-bit word (10111010).
  
    NOTE: The current implementation fixes the first entry to 20 bits and the second entry to 44 bits
      catered to the Modest data structures. We are planning to generalize this. 
  \<close>
  
  section \<open>SharedNat basic definitions\<close>
  
  
  definition make_tuple :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where "make_tuple nl nr = (nl,nr)"
  
  abbreviation "shared_left \<equiv> cnt" 
  
  abbreviation "shared_right \<equiv> lid"
  
  abbreviation "shared_sum \<equiv> uid"
  
  lemma make_tuple_eq1[simp]: "make_tuple nl nr = (nl1, nr1) \<longleftrightarrow> nl = nl1 \<and> nr = nr1"
    unfolding make_tuple_def
    by blast
  
  lemma make_tuple_eq2[simp]: "(nl1, nr1) = make_tuple nl nr \<longleftrightarrow> nl = nl1 \<and> nr = nr1"
    unfolding make_tuple_def
    by blast
  
  lemma shared_left_make_tuple[simp]: "shared_left (make_tuple nl nr) = nl"
    unfolding cnt_def make_tuple_def by simp
  
  lemma shared_right_make_tuple[simp]: "shared_right (make_tuple nl nr) = nr"
    unfolding lid_def make_tuple_def by simp
  
  subsection \<open>Constant definitions\<close>
  
  definition "right_size = (44::nat)"
  definition "left_size = len_size_T - right_size"
  
  lemma size_bounds: "right_size < len_size_T" "left_size < len_size_T"
    unfolding right_size_def left_size_def by auto
  
  lemma left_right_add: "left_size + right_size = len_size_T"
    unfolding left_size_def right_size_def
    by simp
  
  definition "max_left = 2 ^ left_size"
  definition "max_right = 2 ^ right_size"
  
  lemma max_left_alt: "max_left = max_unat left_size"
    unfolding max_left_def max_unat_def by simp
  
  lemma max_right_alt: "max_right = max_unat right_size"
    unfolding max_right_def max_unat_def by simp
  
  lemma max_left_gt_0[simp]: "max_left > (0::nat)"
    unfolding max_left_def
    by simp
  
  lemma max_right_gt_0[simp]: "max_right > (0::nat)"
    unfolding max_right_def
    by simp
    
  
  lemma max_left_right_unat: "max_left * max_right = max_unat len_size_T"
    unfolding max_left_def max_right_def max_unat_def
    apply(fold monoid_mult_class.power_add)
    unfolding left_right_add
    by presburger
  
  lemma max_left_plus_right_lt_max_snat: "max_left + max_right < max_snat len_size_T"
    unfolding max_left_def max_right_def left_size_def right_size_def max_snat_def
    by simp
  
  
  section \<open>SharedNat operations\<close>
  
  type_synonym shared_nat = "size_t"
  
  definition shared_zero :: "shared_nat" where "shared_zero = 0"
  definition make_shared :: "size_t \<Rightarrow> size_t \<Rightarrow> shared_nat" where "make_shared nl nr = (nl << right_size) OR nr"
  
  definition get_shared_left :: "shared_nat \<Rightarrow> size_t" where "get_shared_left sn = (sn >> right_size)"
  definition get_shared_right :: "shared_nat \<Rightarrow> size_t" where "get_shared_right sn = take_bit right_size sn"
  
  definition get_shared_sum :: "shared_nat \<Rightarrow> size_t" where "get_shared_sum sn = (sn >> right_size) + take_bit right_size sn"
  
  
  lemma get_shared_sum_alt_def: "get_shared_sum sn = get_shared_left sn + get_shared_right sn"
    unfolding get_shared_sum_def get_shared_left_def get_shared_right_def
    by simp
  
  lemmas [llvm_inline] = make_shared_def
  
  
  subsection \<open>SharedNat unimplemented operations\<close>
  
  text \<open>We have not refined these to LLVM yet\<close>
  
  definition add_intervals :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where 
    "add_intervals = (\<lambda> (l1,r1) (l2,r2). (l1 + l2, r1 + r2))"
  
  lemma "add_intervals (l1,r1) (l2,r2) = (l1 + l2, r1 + r2)"
    unfolding add_intervals_def by(auto split: prod.split)
  
  lemma shared_left_add: "shared_left (add_intervals sn1 sn2) = shared_left sn1 + shared_left sn2"
    unfolding cnt_def add_intervals_def by(auto split: prod.split)
  
  lemma shared_right_add: "shared_right (add_intervals sn1 sn2) = shared_right sn1 + shared_right sn2"
    unfolding lid_def add_intervals_def by(auto split: prod.split)
  
  lemma "shared_sum (add_intervals sn1 sn2) = shared_sum sn1 + shared_sum sn2"
    unfolding uid_def add_intervals_def by(auto split: prod.split)
  
  abbreviation "increment_left sn \<equiv> add_intervals sn (make_tuple 1 0)"
  
  abbreviation "increment_right sn \<equiv> add_intervals sn (make_tuple 0 1)"
  
  lemma shared_left_inc_left: "shared_left (increment_left sn) = Suc (shared_left sn)"
    unfolding add_intervals_def by(auto split: prod.split)
  
  lemma shared_right_inc_left: "shared_right (increment_left sn) = shared_right sn"
    unfolding add_intervals_def by(auto split: prod.split)
  
  lemma shared_sum_inc_left: "shared_sum (increment_left sn) = Suc (shared_sum sn)"
    unfolding add_intervals_def by(auto split: prod.split)
  
  
  lemma shared_left_inc_right: "shared_left (increment_right sn) = shared_left sn"
    unfolding add_intervals_def by(auto split: prod.split)
  
  lemma shared_right_inc_right: "shared_right (increment_right sn) = Suc (shared_right sn)"
    unfolding add_intervals_def by(auto split: prod.split)
  
  lemma shared_sum_inc_right: "shared_sum (increment_right sn) = Suc (shared_sum sn)"
    unfolding add_intervals_def by(auto split: prod.split)
  
  
  
  
  
  section \<open>Refinement Relation\<close>
  
  subsection \<open>Abstraction Function\<close>
  
  definition "shared_nat_\<alpha> sn = (unat sn div max_right, unat sn mod max_right)"
  
  
  lemma shared_zero_\<alpha>[simp]: "shared_nat_\<alpha> shared_zero = (0,0)"
    unfolding shared_nat_\<alpha>_def shared_zero_def get_shared_left_def get_shared_right_def
    by simp
  
  
  lemma make_shared_\<alpha>[simp]: "snat_invar nl \<Longrightarrow> snat_invar nr \<Longrightarrow> snat nl < max_left \<Longrightarrow> snat nr < max_right \<Longrightarrow> 
      shared_nat_\<alpha> (make_shared nl nr) = (snat nl, snat nr)"
    unfolding shared_nat_\<alpha>_def make_shared_def get_shared_left_def get_shared_right_def max_left_def max_right_def
    apply (clarsimp simp: shiftr_over_or_dist simp flip: shiftr_div_2n')
    apply(subst shiftl_shiftr_id)
    apply (auto simp: right_size_def left_size_def)[2]
    apply (subst(asm) snat_numeral[where 'a = size_T, symmetric])
    apply (simp add: max_snat_def)
    apply (subst(asm) snat_less_refine; (simp add: snat_invar_def; erule less_trans[of nl]; simp)|(simp add: snat_invar_def))
    apply(rewrite mod_word_2p_unat[of right_size "((nl << right_size) || nr)", simplified, OF size_bounds(1)])
    apply (auto simp add: shiftr_le_0 word_ao_dist snat_eq_unat_aux2 mod_2p_is_mask) 
    by (metis take_bit_eq_mask take_bit_nat_eq_self unsigned_take_bit_eq)
  
  
  lemma get_left_\<alpha>[simp]: "unat (get_shared_left sn) = shared_left (shared_nat_\<alpha> sn)"
    unfolding shared_nat_\<alpha>_def get_shared_left_def max_right_def
    apply (clarsimp simp add: shiftr_div_2n_w[symmetric] div_word_2p_unat[of right_size sn, simplified, OF size_bounds(1)]
      intro!: snat_eq_unat_aux2)
    done
  
  
  lemma get_right_\<alpha>[simp]: "unat (get_shared_right sn) = shared_right (shared_nat_\<alpha> sn) "
    unfolding shared_nat_\<alpha>_def get_shared_right_def max_right_def
    apply(clarsimp simp: mod_word_2p_unat[of right_size sn, simplified, OF size_bounds(1)]) 
    apply(rewrite word_eqI_folds(3))
    apply simp
    done
  
  
  lemma shared_sum_unat_bounds: "unat (get_shared_left sn) + unat (get_shared_right sn) < 2 ^ (64 - right_size) + 2 ^ right_size"
  proof -
    have "unat sn div 2 ^ right_size \<le> 2 ^ (64 - right_size)"
      apply(rewrite power_minus_is_div[OF less_imp_le_nat, OF size_bounds(1)])
      apply(rule div_le_mono)
      using unat_lt_max_unat[of sn] 
      unfolding max_unat_def by simp 
    moreover have "unat sn mod 2 ^ right_size < 2 ^ right_size" 
      by force
    ultimately have "unat sn div 2 ^ right_size + unat sn mod 2 ^ right_size < 2 ^ (64 - right_size) + 2 ^ right_size" 
      by linarith
    then show ?thesis 
      by (auto simp: shared_nat_\<alpha>_def max_right_def)
  qed
  
  
  corollary shared_sum_unat_in_max_snat: "unat (get_shared_left sn) + unat (get_shared_right sn) < max_snat len_size_T"
    using shared_sum_unat_bounds[of sn] 
    unfolding right_size_def max_snat_def 
    by simp
  
  
  lemma unat_shared_sum_bounds: "unat ((get_shared_left sn) + (get_shared_right sn)) < 2 ^ (64 - right_size) + 2 ^ right_size"
    apply(subst unat_add_lem')
    using shared_sum_unat_in_max_snat[unfolded max_snat_def, of sn]
    apply fastforce 
    using shared_sum_unat_bounds[of sn] .
  
  corollary unat_shared_sum_in_max_snat_aux: "unat ((get_shared_left sn) + (get_shared_right sn)) < max_snat len_size_T"
    using unat_shared_sum_bounds[of sn] 
    unfolding right_size_def max_snat_def
    by simp
  
  corollary unat_shared_sum_in_max_snat: "unat ((get_shared_sum sn)) < max_snat len_size_T"
    unfolding get_shared_sum_alt_def
    using unat_shared_sum_in_max_snat_aux[of sn] .
  
  lemma snat_invar_get_shared_left: "snat_invar (get_shared_left sn)"
    unfolding get_shared_left_def right_size_def 
    by (simp add: n_gt_0_snat_invar_rshiftn)
  
  lemma snat_invar_get_shared_right: "snat_invar (get_shared_right sn)"
    unfolding get_shared_right_def right_size_def 
    apply(rule snat_invar_take_bit)
    by force
  
  lemma snat_invar_get_shared_sum: "snat_invar (get_shared_sum sn)"
    apply(auto simp: snat_invar_unat_bound unat_shared_sum_in_max_snat)
    done
    
  
  lemma shared_sum_\<alpha>[simp]: "unat (get_shared_sum sn) = shared_sum (shared_nat_\<alpha> sn)"
    unfolding shared_nat_\<alpha>_def get_shared_sum_def
    apply(auto simp: shiftr_div_2n'[symmetric] unat_take_bit_2p[symmetric] max_right_def)
    apply(subst unat_add_lem'[symmetric]) 
    using shared_sum_unat_in_max_snat[of sn] 
    unfolding max_snat_def get_shared_left_def get_shared_right_def
    apply auto
    done
  
  
  subsection \<open>Invariant definition\<close>
  
  text \<open>Note, our invariant holds for all implementations, which we prove later.\<close>
  
  definition shared_nat_invar :: "shared_nat \<Rightarrow> bool" where "shared_nat_invar sn = ((get_shared_left sn < 2 ^ left_size) \<and> (get_shared_right sn < 2 ^ right_size))"
  
  
  lemma get_shared_right_ub: "get_shared_right sn < 2 ^ right_size"
    proof -
      have "sn && 2 ^ right_size - 1 \<le> 2 ^ right_size - 1" 
        using Word.word_and_le1 by blast
      also have "... < 2 ^ right_size" 
        unfolding right_size_def by force
      finally show ?thesis
        apply (auto simp: get_shared_right_def mask_eq take_bit_eq_mask) 
        done
    qed
  
  
  lemma get_shared_right_lb: "sint (get_shared_right sn) \<ge> 0"
    apply(simp add: get_shared_right_def take_bit_eq_mod sint_eq_uint_2pl)
    apply(subgoal_tac "(sn mod 2 ^ right_size) < 2 ^ (LENGTH(64) - 1)" )
    apply(drule sint_eq_uint_2pl)
    apply simp
    apply(rule less_trans[of "sn mod 2 ^ right_size" "2 ^ right_size" "2 ^ (LENGTH(64) - 1)"])
    apply(rule word_mod_less_divisor)
    apply (auto simp add: right_size_def)
    done
  
  
  
  lemma nmsb_get_shared_right: "\<not>msb (get_shared_right sn)"
    unfolding word_msb_sint
    using get_shared_right_lb[of sn] 
    by fastforce
  
  
  lemma get_shared_right_snat_ub: "snat (get_shared_right sn) < 2 ^ right_size" 
    unfolding snat_eq_unat_aux2[unfolded snat_invar_def, OF nmsb_get_shared_right]
    unfolding get_shared_right_def 
    using unat_take_bit_lt_2p by blast
  
  
  lemma get_shared_left_ub: "(get_shared_left sn < 2 ^ left_size)"
    proof -
      have "unat (sn >> right_size) < 2 ^ left_size" 
        using word_shiftr_lt[of sn right_size] 
        by (auto simp: right_size_def left_size_def)
      hence "unat (sn >> right_size) < unat ((2::64 word) ^ left_size)"
        using unat_p2[where 'a = 64, simplified, OF size_bounds(2)] 
        by presburger
      thus ?thesis 
        by(simp add: word_less_nat_alt get_shared_left_def)
    qed
  
  
  lemma get_shared_left_lb: "sint (get_shared_left sn) \<ge> 0"
    apply(simp add: get_shared_left_def right_size_def) 
    apply(rule ccontr)
    apply (clarsimp simp: not_le simp flip: word_msb_sint)
    done
    
  
  lemma shared_nat_invar_true[simp]: "shared_nat_invar sn"
    apply (auto simp: get_shared_right_ub get_shared_left_ub get_shared_right_lb get_shared_left_lb shared_nat_invar_def)
    done
  
  
  subsection \<open>Refinement Relation and Assertion\<close>
  
  definition "shared_nat_rel = br shared_nat_\<alpha> shared_nat_invar"
  definition "shared_nat_assn_aux = word_assn"
  abbreviation "shared_nat_assn \<equiv> pure shared_nat_rel"
  
  
  section \<open>Refinement of Operations\<close>
  
  lemma shared_zero_refine: "(uncurry0 shared_zero, uncurry0 (0, 0)) \<in> unit_rel \<rightarrow> shared_nat_rel"
    unfolding shared_nat_rel_def
    apply (auto simp: in_br_conv)
    done
  
                   
  lemma make_shared_refine: "(uncurry make_shared, uncurry make_tuple) \<in> [\<lambda>(nl,nr). nl < max_left \<and> nr < max_right]\<^sub>f (size_rel \<times>\<^sub>r size_rel) \<rightarrow> shared_nat_rel"
    unfolding make_tuple_def shared_nat_rel_def
    apply (auto intro!: frefI simp: in_br_conv snat_rel_def snat.rel_def)
    done
  
  
  lemma get_left_refine: "(get_shared_left, shared_left) \<in> shared_nat_rel \<rightarrow> snat_rel"
    unfolding shared_nat_rel_def shared_nat_\<alpha>_def max_right_def
    apply(clarsimp simp: in_br_conv shiftr_div_2n'[symmetric])
    apply(subst snat_eq_unat_aux2[symmetric])
    apply(auto simp: get_shared_left_def right_size_def intro!: n_gt_0_snat_invar_rshiftn snat_invar_id_snat_rel)
    done
  
  
  lemma get_right_refine: "(get_shared_right, shared_right) \<in> shared_nat_rel \<rightarrow> snat_rel"
    unfolding shared_nat_rel_def shared_nat_\<alpha>_def max_right_def
    apply(clarsimp simp: in_br_conv unat_take_bit_2p[symmetric])
    apply(subst snat_eq_unat_aux2[symmetric])
    apply(auto simp: get_shared_right_def right_size_def intro!: snat_invar_take_bit snat_invar_id_snat_rel)
    done
  
  
  lemma get_shared_sum_refine: "(get_shared_sum, shared_sum) \<in> shared_nat_rel \<rightarrow> snat_rel"
    unfolding shared_nat_rel_def shared_nat_\<alpha>_def get_shared_sum_def max_right_def
    apply(clarsimp simp: in_br_conv shiftr_div_2n'[symmetric] unat_take_bit_2p[symmetric])
    apply(subst unat_add_lem'[symmetric])
    apply(rule less_trans[OF shared_sum_unat_in_max_snat[unfolded get_shared_left_def get_shared_right_def max_snat_def], of "2 ^ LENGTH(64)"])
    apply(auto intro!: snat_invar_unat_snat_rel snat_invar_get_shared_sum[unfolded get_shared_sum_alt_def get_shared_left_def get_shared_right_def])  
    done
    
  
  section \<open>Refinement to LLVM\<close>
  
  sepref_def shared_zero_ll is "uncurry0 (RETURN (PR_CONST shared_zero))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a shared_nat_assn_aux"
    unfolding shared_zero_def shared_nat_assn_aux_def PR_CONST_def
    apply sepref
    done
  
  
  sepref_def make_shared_ll is "uncurry (RETURN oo make_shared)" :: "id_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a shared_nat_assn_aux"
    unfolding make_shared_def right_size_def shared_nat_assn_aux_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done
  
  
  sepref_def shared_left_ll is "RETURN o get_shared_left" :: "shared_nat_assn_aux\<^sup>k \<rightarrow>\<^sub>a id_assn"
    unfolding get_shared_left_def shared_nat_assn_aux_def right_size_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done
  
  
  sepref_def shared_right_ll is "RETURN o get_shared_right" :: "shared_nat_assn_aux\<^sup>k \<rightarrow>\<^sub>a id_assn"
    unfolding get_shared_right_def shared_nat_assn_aux_def right_size_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done
  
  sepref_def shared_sum_ll is "RETURN o get_shared_sum" :: "shared_nat_assn_aux\<^sup>k \<rightarrow>\<^sub>a id_assn"
    unfolding get_shared_sum_alt_def right_size_def
    apply sepref
    done
  
  
  lemma shared_nat_assn_alt: "hr_comp shared_nat_assn_aux shared_nat_rel = shared_nat_assn"
    unfolding shared_nat_assn_aux_def
    apply auto
    done
  
  
  
  section \<open>Composition of Refinements\<close>
  
  context 
    notes[fcomp_norm_unfold] = shared_nat_assn_alt
  begin
  
    lemmas [sepref_fr_rules] = shared_left_ll.refine[FCOMP get_left_refine]
    lemmas [sepref_fr_rules] = shared_right_ll.refine[FCOMP get_right_refine]
    lemmas [sepref_fr_rules] = make_shared_ll.refine[FCOMP make_shared_refine]
    lemmas [sepref_fr_rules] = shared_sum_ll.refine[FCOMP get_shared_sum_refine]
  
  end
  
  lemma div_less_mono_nat: "(A::nat) < B \<Longrightarrow> B mod n = 0 \<Longrightarrow> A div n < B div n"
    using less_mult_imp_div_less by force
  
  lemma rdomp_shared_left_upper:
    assumes "rdomp shared_nat_assn x"
    shows "shared_left x < max_left"
  proof -
    {
      fix ni::size_t
      note unat_unat_rel[of ni]
      hence "unat ni < max_unat len_size_T"
        by(auto dest!: in_unat_rel_boundsD)
      moreover have "max_unat len_size_T mod max_right = 0"
        unfolding max_unat_def right_size_def max_right_def by simp
      ultimately have "unat ni div max_right < max_unat len_size_T div max_right"
        using div_less_mono_nat by presburger
      moreover have "max_unat len_size_T div max_right = max_left"
        using max_left_right_unat
        by (metis calculation div_by_0 less_nat_zero_code nonzero_mult_div_cancel_right)
      ultimately have "unat ni div max_right < max_left" by argo
    }
    then show ?thesis
      using assms
      unfolding shared_nat_rel_def shared_nat_\<alpha>_def
      by(auto simp: in_br_conv max_unat_def)
  qed
  
  lemma rdomp_shared_right_upper:
    assumes "rdomp shared_nat_assn x"
    shows "shared_right x < max_right"
    using assms
    unfolding shared_nat_rel_def
    by (auto simp: in_br_conv shared_nat_\<alpha>_def max_unat_def intro!: pos_mod_bound)
  
  
  lemma nat_add_less_mono_rev: "(a::nat) < c \<Longrightarrow> b < d \<Longrightarrow> b + a < c + d"
    using add_less_mono by linarith
  
  lemma rdomp_shared_sum_upper: "rdomp shared_nat_assn x \<Longrightarrow> shared_sum x < max_right + max_left"
    apply(frule rdomp_shared_left_upper)
    apply(drule rdomp_shared_right_upper)
    by(auto simp: uid_as_cnt_plus_lid intro: nat_add_less_mono_rev)
    
  corollary shared_nat_snat_boundD: "rdomp shared_nat_assn x \<Longrightarrow> shared_sum x < max_snat len_size_T"
    apply(drule rdomp_shared_sum_upper)
    using max_left_plus_right_lt_max_snat 
    by simp
  
  lemma shared_nat_rel_snat_boundD: "(ni,n) \<in> shared_nat_rel \<Longrightarrow> shared_sum n < max_snat len_size_T"
    by (auto simp: Range.intros shared_nat_snat_boundD)


end





