theory More_Functions
  imports Base_MEC
begin

  definition "popWhile P xs \<equiv> 
    WHILET (\<lambda> (wo,succs). wo = None \<and> succs\<noteq>[]) 
    (\<lambda> (wo,succs). do {
      let (w,succs) = op_list_pop_last succs; 
      let wo = (if P w then None else Some w);
      RETURN (wo, succs)
    }) (None, xs)"

  lemma popWhile_correct: "popWhile P xs\<^sub>0 \<le> SPEC (\<lambda> (wo, xs). case wo of 
    None \<Rightarrow> xs = [] \<and> (\<forall> x \<in> set xs\<^sub>0. P x)
  | Some v \<Rightarrow> \<not>P v \<and> (\<exists> xs\<^sub>1. xs\<^sub>0 = xs @ v # xs\<^sub>1 \<and> (\<forall> x \<in> set xs\<^sub>1. P x)))"
    unfolding popWhile_def
    apply(refine_vcg WHILET_rule[where 
      ?I ="(\<lambda> (wo, xs). case wo of 
        None \<Rightarrow> \<exists> xs\<^sub>1. xs\<^sub>0 = xs @ xs\<^sub>1 \<and> (\<forall> x \<in> set xs\<^sub>1. P x)
      | Some v \<Rightarrow> \<not>P v \<and> (\<exists> xs\<^sub>1. xs\<^sub>0 = xs @ v # xs\<^sub>1 \<and> (\<forall> x \<in> set xs\<^sub>1. P x)))" and 
      ?R="measure (\<lambda> (_,xs). length xs)"])
    apply simp
    
    apply simp

    apply (auto)[]
    subgoal for xs xs\<^sub>1
      apply(rule exI[where ?x="last xs # xs\<^sub>1"])
      apply simp
      done
    subgoal for xs xs\<^sub>1
      apply(rule exI[where ?x="xs\<^sub>1"])
      apply simp
      done

    apply simp
    apply (simp split: option.splits)
    done

  lemma leq_lt_eq_Suc: "b < a \<Longrightarrow> a \<le> Suc b \<Longrightarrow> a = Suc b"
    by linarith

  lemma nfoldli_rev_upt_by_while_aux:
    "h\<le>h' \<Longrightarrow> nfoldli (rev [l..<h]) c f \<sigma> =
    doN { (_,\<sigma>)\<leftarrow>WHILET (\<lambda>(i,\<sigma>). i>l \<and> c \<sigma>) (\<lambda>(i,\<sigma>). doN { ASSERT(i>l); let i'=i-1; \<sigma> \<leftarrow> f i' \<sigma>; RETURN (i',\<sigma>) }) (h,\<sigma>); RETURN \<sigma> }
    "
  proof (induction "rev [l..<h]" arbitrary: h h' \<sigma>)
    case Nil thus ?case
      apply (simp add: Nil_eq_upt_conv)
      apply (subst WHILET_unfold)
      by fastforce
  next
    case (Cons hh xs)
    
    from Cons.hyps(2)[symmetric] have [simp]: "l<h" and [simp]: "hh=h-1" "rev [l..<h] = (h-1)#(rev [l..<h-1])" "xs=rev [l..<h-1]"
      by (auto simp: upt_eq_lel_conv Nil_eq_upt_conv rev_swap dest: leq_lt_eq_Suc) 

    from Cons.prems have A: "h - Suc 0 \<le> h'"
      by linarith

    note IH = Cons.hyps(1)[of "h - Suc 0" h',simplified, OF A, abs_def]  

    from Cons.hyps(2)[symmetric] show ?case
      apply (subst WHILET_unfold)
      apply (auto simp add: IH Let_def A)
      done
  qed

  lemma nfoldli_rev_upt_by_while:
    "nfoldli (rev [l..<h]) c f \<sigma> =
    doN { (_,\<sigma>)\<leftarrow>WHILET (\<lambda>(i,\<sigma>). i>l \<and> c \<sigma>) (\<lambda>(i,\<sigma>). doN { ASSERT(i>l); let i'=i-1; \<sigma> \<leftarrow> f i' \<sigma>; RETURN (i',\<sigma>) }) (h,\<sigma>); RETURN \<sigma> }
    "
    using nfoldli_rev_upt_by_while_aux[of h h l c f \<sigma>, simplified] by auto

end