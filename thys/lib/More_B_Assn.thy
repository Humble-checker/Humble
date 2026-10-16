theory More_B_Assn
  imports Base_MEC
begin

no_notation
  vec_nth (infixl "$" 90)

section \<open>Bounded value assertions\<close>

  definition op_bound_val:: "('a\<Rightarrow>bool) \<Rightarrow> 'a \<Rightarrow> 'a" where "op_bound_val P x = x"
  
  definition mop_bound_val :: "('a\<Rightarrow>bool) \<Rightarrow> 'a \<Rightarrow> 'a nres" where "mop_bound_val P x = do{ ASSERT (P x); RETURN x }"

  lemmas [simp] = op_bound_val_def mop_bound_val_def
  
  context 
    fixes P :: "'a \<Rightarrow> bool"
  begin
    sepref_register "op_bound_val P" 
    sepref_register "mop_bound_val P" 
  end
  
  lemma op_bound_val_refine[sepref_fr_rules]: "(Mreturn,RETURN o PR_CONST (op_bound_val P)) \<in> [\<lambda>x. P x]\<^sub>a A\<^sup>d \<rightarrow> b_assn A P"
    apply sepref_to_hoare
    unfolding op_bound_val_def
    apply vcg
    done
  
  lemma mop_bound_val_refine[sepref_fr_rules]: "(Mreturn,PR_CONST (mop_bound_val P)) \<in> A\<^sup>d \<rightarrow>\<^sub>a b_assn A P"
    apply sepref_to_hoare
    unfolding mop_bound_val_def
    supply [simp] = refine_pw_simps 
    apply vcg
    done

  lemma hr_comp_bounded_rel_assn[simp,fcomp_norm_unfold]: "hr_comp (b_assn A P) (b_rel Id P) = b_assn A P"
    unfolding hr_comp_def b_assn_def
    apply(rule ext)+
    by (auto simp: sep_algebra_simps)

  lemma hr_comp_br_assn[simp,fcomp_norm_unfold]: "hr_comp (b_assn A P) (br \<alpha> I) = hr_comp A (br \<alpha> (\<lambda>x. I x \<and> P x))"
    unfolding hr_comp_def b_assn_def
    apply(rule ext)+
    by(auto simp: sep_algebra_simps in_br_conv)


section \<open>Auxiliary b_assn functions\<close>

  lemma "b_assn A P a c \<turnstile> \<up>P a \<and>* A a c"
    by simp

  definition "open_b_assn x = RETURN x"

  lemma "hn_refine (b_assn A P a c) (Mreturn c) \<box> A (\<lambda> r. r = c) (open_b_assn a)"
    apply(sepref_to_hoare)
    unfolding open_b_assn_def
    apply vcg
    done

  lemma b_rel_br_eq [simp]: "(b_rel Id P) O br \<alpha> P = br \<alpha> P" 
    unfolding b_rel_def by (auto simp: in_br_conv) 

  lemma entails_b_rel_br: "P \<turnstile> Q \<Longrightarrow> (b_rel Id Q) O br \<alpha> P = br \<alpha> P"
    unfolding b_rel_def entails_def by (auto simp: in_br_conv) 


section \<open>Bounded Assn Open Block Nres\<close>

  subsection \<open>Arity 1\<close>

  definition b_assn_open_block :: "'a \<Rightarrow> ('a \<Rightarrow> 'b nres) \<Rightarrow> 'b nres" where "b_assn_open_block x f = f x"

  lemma hn_b_assn_open_block[sepref_comb_rules]:
    assumes "\<Gamma> \<turnstile> hn_ctxt (b_assn A B) x xi \<and>* \<Gamma>\<^sub>1"
    assumes "B x \<Longrightarrow> hn_refine (hn_ctxt A x xi \<and>* \<Gamma>\<^sub>1) fi \<Gamma>\<^sub>2 R CP (f x)"
    assumes "\<Gamma>\<^sub>2 \<turnstile> hn_ctxt A x xi \<and>* \<Gamma>\<^sub>3"
    shows "hn_refine (\<Gamma>) (fi) (hn_ctxt (b_assn A B) x xi \<and>* \<Gamma>\<^sub>3) R CP (b_assn_open_block$x$(\<lambda>\<^sub>2 x. f x))"
    apply(rule hn_refine_cons_pre[OF assms(1)])
    apply(cases "B x")     
    unfolding hn_ctxt_def
    subgoal 
      apply (simp add: sep_algebra_simps b_assn_open_block_def)
      apply(rule hn_refine_cons[OF _ assms(2)])
      apply(simp add: hn_ctxt_def)
      apply(simp)
      using assms(3)[unfolded hn_ctxt_def] apply simp
      apply simp
      done
    subgoal by simp
    done

  lemma b_assn_open_block_mono[refine_mono]: 
    "\<lbrakk>\<And>a. f a \<le> f' a\<rbrakk> \<Longrightarrow> b_assn_open_block x f \<le> b_assn_open_block x f'"
    unfolding b_assn_open_block_def
    by refine_mono

  lemma b_assn_open_block_arity[sepref_monadify_arity]: "b_assn_open_block \<equiv> \<lambda>\<^sub>2x f. SP b_assn_open_block$x$(\<lambda>\<^sub>2a. f$a)"
    by simp

  lemma b_assn_open_block_comb[sepref_monadify_comb]:  
    "b_assn_open_block$x$f = Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. SP b_assn_open_block$x$f)"
    by simp

  lemma b_assn_open_block_mono_flat[refine_mono]: 
    "\<lbrakk>\<And>a. flat_ge (f a) (f' a)\<rbrakk> \<Longrightarrow> flat_ge (b_assn_open_block x f) (b_assn_open_block x f')"
    unfolding b_assn_open_block_def
    by refine_mono

  lemma WITH_SPLIT_rule[refine_vcg]:
      assumes "f x \<le> SPEC P"
      shows "b_assn_open_block x f \<le> SPEC P"  
      using assms(1) unfolding b_assn_open_block_def
      by simp

  lemma WITH_split_refine[refine]:
      assumes "f' x' \<le>\<Down>R (f x)"
      shows "b_assn_open_block x' f' \<le>\<Down>R (b_assn_open_block x f)"
      unfolding b_assn_open_block_def
      using assms
      by auto

  subsection \<open>Arity 2\<close>

  definition b_assn_open_block_arity2 :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c nres) \<Rightarrow> 'c nres" where "b_assn_open_block_arity2 x y f = f x y"

  lemma hn_b_assn_open_block_arity2[sepref_comb_rules]:
    assumes "\<Gamma> \<turnstile> hn_ctxt (b_assn A1 B1) x xi \<and>* hn_ctxt (b_assn A2 B2) y yi \<and>* \<Gamma>\<^sub>1"
    assumes "B1 x \<Longrightarrow> B2 y \<Longrightarrow> hn_refine (hn_ctxt A1 x xi \<and>* hn_ctxt A2 y yi \<and>* \<Gamma>\<^sub>1) fi \<Gamma>\<^sub>2 R CP (f x y)"
    assumes "\<Gamma>\<^sub>2 \<turnstile> hn_ctxt A1 x xi \<and>* hn_ctxt A2 y yi \<and>* \<Gamma>\<^sub>3"
    shows "hn_refine (\<Gamma>) (fi) (hn_ctxt (b_assn A1 B1) x xi \<and>* hn_ctxt (b_assn A2 B2) y yi \<and>* \<Gamma>\<^sub>3) R CP (b_assn_open_block_arity2$x$y$(\<lambda>\<^sub>2 x y. f x y))"
    apply(rule hn_refine_cons_pre[OF assms(1)])
    apply(cases "B1 x \<and> B2 y")     
    unfolding hn_ctxt_def
    subgoal 
      apply (simp add: sep_algebra_simps b_assn_open_block_arity2_def)
      apply(rule hn_refine_cons[OF _ assms(2)])
      apply(simp add: hn_ctxt_def) 
      apply simp
      apply simp
      using assms(3)[unfolded hn_ctxt_def] apply simp
      apply simp
      done
    subgoal 
      by force
    done

  lemma b_assn_open_block2_mono[refine_mono]: 
    "\<lbrakk>\<And>a b. f a b \<le> f' a b\<rbrakk> \<Longrightarrow> b_assn_open_block_arity2 x y f \<le> b_assn_open_block_arity2 x y f'"
    unfolding b_assn_open_block_arity2_def
    by refine_mono

  lemma b_assn_open_block2_arity[sepref_monadify_arity]: "b_assn_open_block_arity2 \<equiv> \<lambda>\<^sub>2x y f. SP b_assn_open_block_arity2$x$y$(\<lambda>\<^sub>2a b. f$a$b)"
    by simp

  lemma b_assn_open_block2_comb[sepref_monadify_comb]:  
    "b_assn_open_block_arity2$x$y$f = Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. Refine_Basic.bind$(EVAL$y)$(\<lambda>\<^sub>2y. SP b_assn_open_block_arity2$x$y$f))"
    by simp

  lemma b_assn_open_block2_mono_flat[refine_mono]: 
    "\<lbrakk>\<And>a b. flat_ge (f a b) (f' a b)\<rbrakk> \<Longrightarrow> flat_ge (b_assn_open_block_arity2 x y f) (b_assn_open_block_arity2 x y f')"
    unfolding b_assn_open_block_arity2_def
    by refine_mono

  lemma WITH_SPLIT2_rule[refine_vcg]:
      assumes "f x y \<le> SPEC P"
      shows "b_assn_open_block_arity2 x y f \<le> SPEC P"  
      using assms(1) unfolding b_assn_open_block_arity2_def
      by simp

  lemma WITH_split2_refine[refine]:
      assumes "f' x' y' \<le>\<Down>R (f x y)"
      shows "b_assn_open_block_arity2 x' y' f' \<le>\<Down>R (b_assn_open_block_arity2 x y f)"
      unfolding b_assn_open_block_arity2_def
      using assms
      by auto


subsection \<open>Bounded Assn Open Block Fun\<close>

  subsubsection \<open>Arity 1\<close>

  definition b_assn_open_block_fun :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" where "b_assn_open_block_fun x f = f x"

  lemma hn_b_assn_open_block_fun[sepref_comb_rules]:
    assumes "\<Gamma> \<turnstile> hn_ctxt (b_assn A B) x xi \<and>* \<Gamma>\<^sub>1"
    assumes "B x \<Longrightarrow> hn_refine (hn_ctxt A x xi \<and>* \<Gamma>\<^sub>1) fi \<Gamma>\<^sub>2 R CP (RETURN$(f x))"
    assumes "\<Gamma>\<^sub>2 \<turnstile> hn_ctxt A x xi \<and>* \<Gamma>\<^sub>3"
    shows "hn_refine (\<Gamma>) (fi) (hn_ctxt (b_assn A B) x xi \<and>* \<Gamma>\<^sub>3) R CP ((b_assn_open_block_fun$x$(\<lambda>\<^sub>2 x. RETURN $ (f x))))"
    apply(rule hn_refine_cons_pre[OF assms(1)])
    apply(cases "B x")     
    unfolding hn_ctxt_def
    subgoal 
      apply (simp add: sep_algebra_simps b_assn_open_block_fun_def)
      apply(rule hn_refine_cons[OF _ assms(2)[unfolded APP_def]])
      apply(simp add: hn_ctxt_def)
      apply(simp)
      using assms(3)[unfolded hn_ctxt_def] apply simp
      apply simp
      done
    subgoal by simp
    done

  lemma b_assn_open_block_fun_mono[refine_mono]: 
    "\<lbrakk>\<And>a. f a = f' a\<rbrakk> \<Longrightarrow> RETURN (b_assn_open_block_fun x f) \<le> RETURN (b_assn_open_block_fun x f')"
    unfolding b_assn_open_block_fun_def nres_order_simps(20)
    by refine_mono

  lemma b_assn_open_block_fun_arity[sepref_monadify_arity]: "b_assn_open_block_fun \<equiv> \<lambda>\<^sub>2x f. SP b_assn_open_block_fun$x$(\<lambda>\<^sub>2a. f$a)"
    by simp

  lemma b_assn_open_block_fun_comb[sepref_monadify_comb]:  
    "EVAL$(b_assn_open_block_fun$x$(\<lambda>\<^sub>2 x. f x)) = Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. b_assn_open_block$x$(\<lambda>\<^sub>2 y. EVAL $ (f y)))"
    by (simp add: b_assn_open_block_fun_def b_assn_open_block_def)

  lemma b_assn_open_block_fun_mono_flat[refine_mono]: 
    "\<lbrakk>\<And>a. flat_ge (f a) (f' a)\<rbrakk> \<Longrightarrow> flat_ge (b_assn_open_block_fun x f) (b_assn_open_block_fun x f')"
    unfolding b_assn_open_block_fun_def
    by refine_mono

  lemma WITH_SPLIT_fun_rule[refine_vcg]:
      assumes "P (f x)"
      shows "RETURN (b_assn_open_block_fun x f) \<le> SPEC P"  
      using assms(1) unfolding b_assn_open_block_fun_def
      by simp

  lemma WITH_split_fun_refine[refine]:
      assumes "(f' x', f x) \<in> R"
      shows "RETURN (b_assn_open_block_fun x' f') \<le>\<Down>R (RETURN (b_assn_open_block_fun x f))"
      unfolding b_assn_open_block_fun_def
      using assms
      by auto

  subsubsection \<open>Arity 2\<close>

  definition b_assn_open_block_fun2 :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'c" where "b_assn_open_block_fun2 x y f = f x y"

  lemma hn_b_assn_open_block_fun2[sepref_comb_rules]:
    assumes "\<Gamma> \<turnstile> hn_ctxt (b_assn A1 B1) x xi \<and>* hn_ctxt (b_assn A2 B2) y yi \<and>* \<Gamma>\<^sub>1"
    assumes "B1 x \<Longrightarrow> B2 y \<Longrightarrow> hn_refine (hn_ctxt A1 x xi \<and>* hn_ctxt A2 y yi \<and>* \<Gamma>\<^sub>1) fi \<Gamma>\<^sub>2 R CP (RETURN$(f x y))"
    assumes "\<Gamma>\<^sub>2 \<turnstile> hn_ctxt A1 x xi \<and>* hn_ctxt A2 y yi \<and>* \<Gamma>\<^sub>3"
    shows "hn_refine (\<Gamma>) (fi) (hn_ctxt (b_assn A1 B1) x xi \<and>* hn_ctxt (b_assn A2 B2) y yi \<and>* \<Gamma>\<^sub>3) R CP ((b_assn_open_block_fun2$x$y$(\<lambda>\<^sub>2 x y. RETURN $ (f x y))))"
    apply(rule hn_refine_cons_pre[OF assms(1)])
    apply(cases "B1 x \<and> B2 y")     
    unfolding hn_ctxt_def
    subgoal 
      apply (simp add: sep_algebra_simps b_assn_open_block_fun2_def)
      apply(rule hn_refine_cons[OF _ assms(2)[unfolded APP_def]])
      apply(simp add: hn_ctxt_def)
      apply(simp)
      apply simp
      using assms(3)[unfolded hn_ctxt_def] apply simp
      apply simp
      done
    subgoal 
      by auto
    done

  lemma b_assn_open_block_fun2_mono[refine_mono]: 
    "\<lbrakk>\<And>a b. f a b = f' a b\<rbrakk> \<Longrightarrow> RETURN (b_assn_open_block_fun2 x y f) \<le> RETURN (b_assn_open_block_fun2 x y f')"
    unfolding b_assn_open_block_fun2_def nres_order_simps(20)
    by refine_mono

  lemma b_assn_open_block_fun2_arity[sepref_monadify_arity]: "b_assn_open_block_fun2 \<equiv> \<lambda>\<^sub>2 x y f. SP b_assn_open_block_fun2$x$y$(\<lambda>\<^sub>2a b. f$a$b)"
    by simp

  lemma b_assn_open_block_fun2_comb[sepref_monadify_comb]:  
    "EVAL$(b_assn_open_block_fun2$x$y$(\<lambda>\<^sub>2 x y. f x y)) = Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. Refine_Basic.bind$(EVAL$y)$(\<lambda>\<^sub>2y. b_assn_open_block_arity2$x$y$(\<lambda>\<^sub>2 x y. EVAL $ (f x y))))"
    by (simp add: b_assn_open_block_fun2_def b_assn_open_block_arity2_def)

  lemma b_assn_open_block_fun2_mono_flat[refine_mono]: 
    "\<lbrakk>\<And>a b. flat_ge (f a b) (f' a b)\<rbrakk> \<Longrightarrow> flat_ge (b_assn_open_block_fun2 x y f) (b_assn_open_block_fun2 x y f')"
    unfolding b_assn_open_block_fun2_def
    by refine_mono

  lemma WITH_SPLIT_fun2_rule[refine_vcg]:
      assumes "P (f x y)"
      shows "RETURN (b_assn_open_block_fun2 x y f) \<le> SPEC P"  
      using assms(1) unfolding b_assn_open_block_fun2_def
      by simp

  lemma WITH_split_fun2_refine[refine]:
      assumes "(f' x' y', f x y) \<in> R"
      shows "RETURN (b_assn_open_block_fun2 x' y' f') \<le>\<Down>R (RETURN (b_assn_open_block_fun2 x y f))"
      unfolding b_assn_open_block_fun2_def
      using assms
      by auto

end