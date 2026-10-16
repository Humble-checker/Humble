theory Bitwise_Ext
  imports Base_MEC
begin

section \<open>Mask\<close>

lemma word_mask_less_length_no_msb: "n < LENGTH('a::len) \<Longrightarrow> \<not>(msb::'a word \<Rightarrow> bool) (mask n)"
  by (metis (no_types, lifting) min.absorb4 signed_take_bit_eq take_bit_minus_one_eq_mask take_bit_take_bit uint_lt_0 uint_sint word_msb_sint)

definition mask_impl :: "nat \<Rightarrow> ('a::len2) word" where "mask_impl n = (1 << n) - 1"

lemma mask_refine: "(mask_impl, mask) \<in> nat_rel \<rightarrow> word_rel"
  unfolding mask_impl_def
  apply(auto simp: mask_eq)
  done

sepref_def mask_ll is "RETURN o (mask_impl :: nat \<Rightarrow> ('a::len2) word)" :: "[\<lambda> n. n < LENGTH('a)]\<^sub>a (snat_assn' TYPE('a::len2))\<^sup>k \<rightarrow> id_assn"
  unfolding mask_impl_def
  apply sepref
  done

lemmas [sepref_fr_rules] = mask_ll.refine[FCOMP mask_refine]

section \<open>Take Bit\<close>

definition take_bit_impl :: "nat \<Rightarrow> ('a::len2) word \<Rightarrow> 'a word" where "take_bit_impl n a = a AND ((1 << n) - 1)"

lemma take_bit_refine: "(take_bit_impl, take_bit) \<in> nat_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  unfolding take_bit_impl_def
  apply(auto simp: fun_eq_iff take_bit_eq_mask mask_eq)
  done

sepref_def take_bit_ll is "uncurry (RETURN oo (take_bit_impl :: nat \<Rightarrow> 'a::len2 word \<Rightarrow> 'a::len2 word))" :: "[\<lambda> (n,_). n < LENGTH('a::len2)]\<^sub>a (snat_assn' TYPE('a))\<^sup>k *\<^sub>a id_assn\<^sup>d \<rightarrow> id_assn"
  unfolding take_bit_impl_def
  apply sepref
  done


lemmas [sepref_fr_rules] = take_bit_ll.refine[FCOMP take_bit_refine]


section \<open>Get Bit\<close>


definition get_bit_impl :: "size_t \<Rightarrow> nat \<Rightarrow> bool nres" where "get_bit_impl w i = 
  do { 
    let v = 1 << i; 
    let v = w AND v; 
    RETURN (v \<noteq> 0) 
  }"

lemma get_bit_impl_refine: "get_bit_impl w i \<le> RETURN (w !! i)"
  unfolding get_bit_impl_def
  apply refine_vcg 
  using and_eq_0_is_nth by auto


sepref_def get_bit_ll is "uncurry get_bit_impl" :: "[\<lambda> (_, i). i < len_size_T]\<^sub>a id_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding get_bit_impl_def 
  apply sepref
  done


lemma get_bit_impl_rel_refine: "(uncurry get_bit_impl, uncurry (RETURN oo (!!))) \<in> word_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using get_bit_impl_refine
  apply (auto intro: nres_relI)
  done

lemmas [sepref_fr_rules] = get_bit_ll.refine[FCOMP get_bit_impl_rel_refine]



section \<open>Set Bit\<close>

definition "op_set_bit w i = set_bit w i True"

definition set_bit_impl :: "size_t \<Rightarrow> nat \<Rightarrow> size_t" where 
  "set_bit_impl w i = w OR (1 << i)"

lemma set_bit_impl_refine: "set_bit_impl w i = op_set_bit w i"
  unfolding set_bit_impl_def op_set_bit_def
  by (auto simp add: set_bit_eq set_bit_eq_or unset_bit_eq_and_not)


sepref_def set_bit_ll is "uncurry (RETURN oo set_bit_impl)" :: "[\<lambda> (_, i). i < len_size_T]\<^sub>a id_assn\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> id_assn"
  unfolding set_bit_impl_def 
  apply sepref
  done

lemma set_bit_impl_rel_refine: "(set_bit_impl, op_set_bit) \<in> word_rel \<rightarrow> nat_rel \<rightarrow> word_rel"
  using set_bit_impl_refine
  apply (auto)
  done

lemmas [sepref_fr_rules] = set_bit_ll.refine[FCOMP set_bit_impl_rel_refine]


section \<open>Unset Bit\<close>

definition "op_unset_bit w i = set_bit w i False"

definition unset_bit_impl :: "size_t \<Rightarrow> nat \<Rightarrow> size_t" where 
  "unset_bit_impl w i = w AND (NOT (1 << i))"

lemma unset_bit_impl_refine: "unset_bit_impl w i = op_unset_bit w i"
  unfolding unset_bit_impl_def op_unset_bit_def
  by (auto simp add: set_bit_eq set_bit_eq_or unset_bit_eq_and_not)


sepref_def unset_bit_ll is "uncurry (RETURN oo unset_bit_impl)" :: "[\<lambda> (_, i). i < len_size_T]\<^sub>a id_assn\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> id_assn"
  unfolding unset_bit_impl_def 
  apply sepref
  done

lemma unset_bit_impl_rel_refine: "(unset_bit_impl, op_unset_bit) \<in> word_rel \<rightarrow> nat_rel \<rightarrow> word_rel"
  unfolding unset_bit_impl_refine
  apply (auto )
  done

lemmas [sepref_fr_rules] = unset_bit_ll.refine[FCOMP unset_bit_impl_rel_refine]

end