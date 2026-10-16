theory Bind_Const
  imports Base_MEC
begin

subsection \<open>BCONST lemmas\<close>

(* TODO: Move to central library *)
definition BCONST :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" where "BCONST c m \<equiv> m"

lemma annot_BCONST: "m = BCONST c m" by (simp add: BCONST_def)

definition bind_const :: "'a \<Rightarrow> 'a nres \<Rightarrow> ('a \<Rightarrow> 'b nres) \<Rightarrow> 'b nres" 
  where "bind_const c \<equiv> Refine_Basic.bind"

lemma bind_BCONST_pat[def_pat_rules]: "Refine_Basic.bind$(BCONST$c$m)$f \<equiv> UNPROTECT (bind_const c)$m$f"
  unfolding BCONST_def bind_const_def by auto
    
lemma Let_BCONST_pat[def_pat_rules]: "Let$(BCONST$c$cc)$f \<equiv> UNPROTECT (bind_const c)$(RETURN$cc)$f"
  unfolding BCONST_def bind_const_def by auto

lemma id_op_bind_const[id_rules]: 
  "PR_CONST (bind_const c) ::\<^sub>i TYPE('a nres \<Rightarrow> ('a \<Rightarrow> 'b nres) \<Rightarrow> 'b nres)"
  by simp

  

lemma hn_bind_const[sepref_comb_rules]:
  assumes PRE: "vassn_tag \<Gamma> \<Longrightarrow> m \<le> RETURN c"
  assumes D1: "hn_refine \<Gamma> m' \<Gamma>1 Rh CP\<^sub>1 m"
  assumes D2: 
    "\<And>x'. bind_ref_tag c m \<Longrightarrow> CP_assm (CP\<^sub>1 x') \<Longrightarrow>
      hn_refine (hn_ctxt Rh c x' ** \<Gamma>1) (f' x') (\<Gamma>2 x') R (CP\<^sub>2 x') (f c)"
  assumes IMP: "\<And>x'. \<Gamma>2 x' \<turnstile> hn_ctxt Rx c x' ** \<Gamma>'"
  assumes "MK_FREE Rx fr"
  shows "hn_refine \<Gamma> (doM {x\<leftarrow>m'; r\<leftarrow>f' x; fr x; Mreturn r}) \<Gamma>' R (CP_SEQ CP\<^sub>1 CP\<^sub>2) (PR_CONST (bind_const c)$m$(\<lambda>\<^sub>2x. f x))"
proof (rule hn_refine_vassn_tagI)
  assume "vassn_tag \<Gamma>"
  then have X: "m = RETURN c \<and> x=c" if "RETURN x \<le> m" for x
    using PRE that dual_order.trans by fastforce
  
  show ?thesis  
    unfolding APP_def PROTECT2_def bind_const_def PR_CONST_def CP_SEQ_def
    apply (rule hnr_bind[where ?\<Gamma>2.0="\<lambda>x x'. \<up>(x=c) ** G x'" for G])
    apply fact
    apply (drule X) apply (clarsimp simp: sep_algebra_simps) apply (rule D2)
    unfolding bind_ref_tag_def CP_assm_def apply simp apply simp
    apply (clarsimp simp: entails_lift_extract_simps sep_algebra_simps) apply fact
    by fact
    
qed

end