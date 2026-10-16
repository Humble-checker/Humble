theory Base_MEC
  imports "HOL-Library.Omega_Words_Fun"
          "Markov_Models.Markov_Models" 
          "Isabelle_LLVM.IICF_Array_Map" 
          "Isabelle_LLVM.Refine_Monadic_Add" "./VC_Solve"
          "Isabelle_LLVM.IICF_Set"
          "Isabelle_LLVM.LLVM_DS_Array_List"
          "Isabelle_LLVM.IICF_List"
          "Isabelle_LLVM.IICF_Array_List"
          "Isabelle_LLVM.Float_Setup"
begin

hide_const (open) NEMonad.RETURN
hide_const (open) Sigma_Algebra.measure


type_synonym size_T = "64"
type_synonym size_t = "size_T word"
abbreviation(input) "len_size_T \<equiv> (64::nat)"
abbreviation "size_rel \<equiv> snat_rel' TYPE(size_T)"
abbreviation "size_assn \<equiv> snat_assn' TYPE(size_T)"
abbreviation "size_option_assn \<equiv> snat_option_assn' TYPE(size_T)"
abbreviation "max_size_t \<equiv> max_snat len_size_T"
type_synonym sizeopt = "nat option"

abbreviation "small_array_slice_assn A \<equiv> b_assn (IICF_Array.array_slice_assn A) (\<lambda>xs. length xs < max_snat len_size_T)"



type_synonym node_T = size_T
type_synonym node_t = size_t

abbreviation "node_rel' N \<equiv> b_rel nat_rel (\<lambda>x. x<N)"
abbreviation "node_assn' N \<equiv> b_assn (snat_assn' TYPE(node_T)) (\<lambda>x. x<N)"


lemma len_size_T_alt: "len_size_T = LENGTH(size_T) "
  by simp


(* GENERAL LEMMAS *)

lemma hr_comp_entails: "\<forall> vi. A\<^sub>1 vi v \<turnstile> A\<^sub>2 vi v \<Longrightarrow> R\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow> hr_comp A\<^sub>1 R\<^sub>1 vi v \<turnstile> hr_comp A\<^sub>2 R\<^sub>2 vi v"
  unfolding hr_comp_def by(auto simp: entails_def sep_algebra_simps)

lemma bounded_take_length: "n \<le> length xs \<Longrightarrow> length (take n xs) = n"
  by simp

lemma neq_Nil_conv_rev: "(xs \<noteq> []) = (\<exists>y ys. xs = ys @ [y])"
  apply(cases xs rule: rev_cases)
  by auto

end
