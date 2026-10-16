theory More_snat
  imports Base_MEC
begin


section \<open>snat lemmas\<close>

lemma m1_notin_snat_rel: "(-1,x)\<notin>snat_rel' TYPE(size_T)"
  by (auto simp: snat_rel_def snat.rel_def snat_invar_def in_br_conv)

lemma in_snat_rel_snat: "(ii,i)\<in>snat_rel \<Longrightarrow> snat ii = i"
  by (auto dest!: in_snat_rel_int simp: snat_def)

lemma in_snat_rel_leq: "(a, j + i) \<in> snat_rel \<Longrightarrow> j \<le> snat a" 
  by (auto dest!: in_snat_rel_snat )

lemma snat_rel_abs_eq1: "(xi, x1) \<in> snat_rel \<Longrightarrow> (xi, x2) \<in> snat_rel \<Longrightarrow> x1 = x2"
  using in_snat_rel_snat by blast

lemma snat_rel_abs_eq2: "(xi, x2) \<in> snat_rel \<Longrightarrow> (xi, x1) \<in> snat_rel \<Longrightarrow> x1 = x2"
  using in_snat_rel_snat by blast

lemma snat_rel_con_eq1: "(xi1, x) \<in> snat_rel \<Longrightarrow> (xi2, x) \<in> snat_rel \<Longrightarrow> xi1 = xi2"
  by(auto simp: snat_rel_def snat.rel_def in_br_conv snat_eq_unat_aux2 word_eq_unatI)

lemma snat_rel_con_eq2: "(xi2, x) \<in> snat_rel \<Longrightarrow> (xi1, x) \<in> snat_rel \<Longrightarrow> xi1 = xi2"
  by(auto simp: snat_rel_def snat.rel_def in_br_conv snat_eq_unat_aux2 word_eq_unatI)

lemma snat_rel_eq_iff: "(xi1, x1) \<in> snat_rel \<Longrightarrow> (xi2, x2) \<in> snat_rel \<Longrightarrow> xi1 = xi2 \<longleftrightarrow> x1 = x2"
  by(auto intro: snat_rel_con_eq1 snat_rel_abs_eq1)


subsection \<open>Adaptations from @thm\<open>snat_bin_ops\<close>\<open>snat_cmp_ops\<close>\<close>

lemmas snat_simps = snat_invar_alt max_snat_def snat_eq_unat unat_word_ariths

lemma plus_snat_refine: "a + b < max_snat LENGTH('a::len2) \<Longrightarrow> (ai, a) \<in> snat_rel \<Longrightarrow> (bi, b) \<in> snat_rel \<Longrightarrow> (ai + bi, a + b) \<in> snat_rel" for ai bi ::"'a::len2 word"
  unfolding snat_rel_def snat.rel_def 
  apply (auto simp: in_br_conv snat_simps)
  done

lemma minus_snat_refine: "a \<ge> b \<Longrightarrow> (ai, a) \<in> snat_rel \<Longrightarrow> (bi, b) \<in> snat_rel \<Longrightarrow> (ai - bi, a - b) \<in> snat_rel"
  unfolding snat_rel_def snat.rel_def 
  apply (auto simp: in_br_conv snat_simps unat_sub_if')
  done

lemma lt_snat_refine: "(ai, a) \<in> snat_rel \<Longrightarrow> (bi, b) \<in> snat_rel \<Longrightarrow> a < b \<longleftrightarrow> ai < bi"
  unfolding snat_rel_def snat.rel_def 
  apply(auto simp: in_br_conv snat_simps word_less_nat_alt)
  done

lemma le_snat_refine: "(ai, a) \<in> snat_rel \<Longrightarrow> (bi, b) \<in> snat_rel \<Longrightarrow> a \<le> b \<longleftrightarrow> ai \<le> bi"
  unfolding snat_rel_def snat.rel_def 
  apply(auto simp: in_br_conv snat_simps word_le_nat_alt)
  done




(*TODO: Everything from here on needs to be sorted*)
section \<open>snat lemmas\<close>

lemma snat_less_refine: "snat_invar a \<Longrightarrow> snat_invar b \<Longrightarrow> snat a < snat b \<longleftrightarrow> a < b"
  apply(auto simp: snat_def snat_invar_def)
  apply (meson word_sless_alt word_sless_msb_less)
  apply (metis linorder_le_less_linear order_le_imp_less_or_eq signed_eq_0_iff word_gt_0 word_gt_a_gt_0 word_msb_sint)
  by (simp add: sint_eq_uint word_less_def)


lemma snat_mask_id: "snat_invar x \<Longrightarrow> snat x < 2 ^ n \<Longrightarrow> x && mask n = x"
  apply(simp add: snat_def snat_invar_def and_mask_mod_2p)
  apply (simp add: sint_eq_uint)
  done


lemma snat_take_bit_id: "snat_invar x \<Longrightarrow> snat x < 2 ^ n \<Longrightarrow> take_bit n x = x" 
  apply(simp add: snat_def snat_invar_def take_bit_word_eq_self_iff)
  apply(cases "LENGTH('a) \<le> n")
  apply (auto simp: sint_eq_uint uint_power_lower word_less_def) 
  done

lemma rshift_suc_n_alt: "(w >> Suc n) = (w >> n) >> 1" for w::"'a::len word"
  apply(simp add: shiftr_shiftr)
  done 
  

lemma nmsb_rshiftn: "\<not>msb (w >> Suc n)"  for w::"'a::len2 word"
  apply(rewrite rshift_suc_n_alt)
  by auto


corollary snat_invar_rshift_Sucn: "snat_invar (w >> Suc n)"
  unfolding snat_invar_def
  using nmsb_rshiftn .

corollary n_gt_0_snat_invar_rshiftn: "n > 0 \<Longrightarrow> snat_invar (w >> n)"
  unfolding snat_invar_def
  using nmsb_rshiftn 
  using gr0_implies_Suc by blast


lemma nmsb_take_bit: "n < LENGTH('a::len2) \<Longrightarrow> \<not>msb (take_bit n (w::'a word))"
  apply(rule ccontr)
  apply (auto simp: word_msb_sint signed_take_bit_eq) 
  done

corollary snat_invar_take_bit: "n < LENGTH('a::len2) \<Longrightarrow> snat_invar (take_bit n (w::'a word))"
  unfolding snat_invar_def
  using nmsb_take_bit .

lemma take_bit_lshift_is_0: "take_bit n (a << n) = 0" for a::"'a::len word"
  apply (auto simp: take_bit_eq_mask)
  done

lemma snat_invar_id_snat_rel: "snat_invar ii \<Longrightarrow> (ii, snat ii) \<in> snat_rel"
  apply(auto simp: snat_rel_def snat.rel_def in_br_conv snat_invar_def)
  done

lemma snat_invar_unat_snat_rel: "snat_invar ii \<Longrightarrow> (ii, unat ii) \<in> snat_rel"
  apply(auto simp: snat_eq_unat_aux2[symmetric] snat_invar_id_snat_rel)
  done

lemma p_sint_id_snat_rel: "sint ii \<ge> 0 \<Longrightarrow> (ii, snat ii) \<in> snat_rel"
  apply(auto simp: snat_rel_def snat.rel_def in_br_conv snat_invar_def word_msb_sint)
  done

lemma snat_invar_unat_bound:"snat_invar w \<longleftrightarrow> unat w < max_snat LENGTH('a)" for w::"'a::len2 word"
  apply auto
  apply (metis snat_eq_unat_aux2 snat_lt_max_snat)
  apply (rule ccontr)
  unfolding snat_invar_def
  apply (auto simp: msb_unat_big max_snat_def)
  done

section \<open>unat lemmas\<close>

lemma mod_word_2p_unat: "n < LENGTH ('a::len) \<Longrightarrow> (unat (w::'a word)) mod (2 ^ n) = unat (w mod 2 ^ n)"
  by (simp add: unat_mod_distrib)

lemma div_word_2p_unat: "n < LENGTH ('a::len) \<Longrightarrow> (unat (w::'a word)) div (2 ^ n) = unat (w div 2 ^ n)"
  by (simp add: unat_div_distrib)

lemma unat_take_bit_2p: "unat (take_bit n w) = unat w mod 2 ^ n"
  by (metis take_bit_eq_mod unsigned_take_bit_eq)

lemma unat_and_mask_lt_2p: "unat (w && mask n) < 2 ^ n" 
  by (metis take_bit_eq_mask take_bit_nat_less_exp unsigned_take_bit_eq)

lemma unat_take_bit_lt_2p: "unat (take_bit n a) < 2 ^ n"
  by(auto simp: take_bit_eq_mask unat_and_mask_lt_2p)
  
lemma unat_unat_rel: "(ii, unat ii) \<in> unat_rel"
  by(auto simp: unat_rel_def unat.rel_def in_br_conv)


end
