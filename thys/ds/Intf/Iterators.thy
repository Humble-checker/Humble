theory Iterators
  imports "II_Modest_Base.More_List_Rel"
begin


lemma remdups_snoc: "remdups (xs @ [a]) = remdups (removeAll a xs) @ [a]"
  apply(induction xs)
  by auto

lemma rev_removeAll: "rev (removeAll a xs) = removeAll a (rev xs)"
  apply(induction xs)
  by auto

lemma unique_SPEC:
  assumes "P x"
  assumes "(\<And> x'. P x' \<Longrightarrow> x = x')"
  shows "SPEC P = RETURN x"
  by(auto simp: pw_eq_iff refine_pw_simps assms)



definition [to_relAPP]: "lset_rel R \<equiv> \<langle>R\<rangle>list_rel O br set (\<lambda>_. True)"

lemma lset_rel_finite[simp]: "(xs,x) \<in> \<langle>R\<rangle>lset_rel \<Longrightarrow> finite x"
  unfolding lset_rel_def by(auto simp: in_br_conv)


lemma set_lset_rel[simp,intro!]: "(xs, set xs) \<in> \<langle>Id\<rangle>lset_rel"
  unfolding lset_rel_def
  by(auto simp: in_br_conv)


lemma lset_relI: "\<exists> x'. (x,x') \<in> \<langle>R\<rangle>list_rel \<and> y = set x' \<Longrightarrow> (x,y) \<in> \<langle>R\<rangle>lset_rel"
  unfolding lset_rel_def by (auto simp: in_br_conv)


fun duplicates :: "'a list \<Rightarrow> 'a set" where
  "duplicates [] = {}"
| "duplicates (x#xs) = (if x \<in> set xs then insert x (duplicates xs) else duplicates xs)"

lemma duplicates_remdups[simp]: "duplicates (remdups xs) = {}"
  apply(induction xs)
  by auto

lemma duplicates_count_list: "x \<in> duplicates xs \<longleftrightarrow> count_list xs x > 1"
  apply(induction xs)
  by (simp_all add: count_list_0_iff zero_less_iff_neq_zero)

lemma duplicates_rev[simp]: "duplicates (rev xs) = duplicates xs"
  apply(rule set_eqI)
  by (simp add: duplicates_count_list)


definition "remdups_rel = br remdups (\<lambda>_. True)"

lemma remdups_rel_distinct: "(xs,xs') \<in> remdups_rel \<Longrightarrow> distinct xs'"
  unfolding remdups_rel_def by(auto simp: in_br_conv)

lemma remdups_rel_set_eq: "(xs, xs') \<in> remdups_rel \<Longrightarrow> set xs = set xs'"
  unfolding remdups_rel_def by(auto simp: in_br_conv)

lemma remdups_rel_snoc_removeAll:  "(xs, xs' @ [a]) \<in> remdups_rel \<Longrightarrow> (removeAll a xs, xs') \<in> remdups_rel"
  apply(induction xs arbitrary: xs' rule: rev_induct)
  unfolding remdups_rel_def
  by(auto simp: in_br_conv remdups_snoc) 

lemma remdups_rel_Cons_removeAll:  "(xs, a # xs') \<in> remdups_rel \<Longrightarrow> (removeAll a xs, xs') \<in> remdups_rel"
  apply(induction xs arbitrary: xs')
  unfolding remdups_rel_def
  by(auto simp: in_br_conv)

lemma remdups_rel_snoc_last: "(xs, xs' @ [a]) \<in> remdups_rel \<Longrightarrow> last xs = a"
  unfolding remdups_rel_def
  apply(clarsimp simp: in_br_conv   snoc_eq_iff_butlast)  
  by (metis remdups_snoc snoc_eq_iff_butlast)



definition "revdups_rel = br (rev o remdups o rev) (\<lambda>_. True)"
                                
lemma revdups_rel_distinct: "(xs,xs') \<in> revdups_rel \<Longrightarrow> distinct xs'"
  unfolding revdups_rel_def by(auto simp: in_br_conv)

lemma revdups_rel_set_eq: "(xs, xs') \<in> revdups_rel \<Longrightarrow> set xs = set xs'"
  unfolding revdups_rel_def by(auto simp: in_br_conv)

lemma revdups_rel_snoc_removeAll:  "(xs, xs' @ [a]) \<in> revdups_rel \<Longrightarrow> (removeAll a xs, xs') \<in> revdups_rel"
  apply(induction xs arbitrary: xs' rule: rev_induct)
  unfolding revdups_rel_def
  by(auto simp: in_br_conv remdups_snoc) 

lemma revdups_rel_Cons_removeAll:  "(xs, a # xs') \<in> revdups_rel \<Longrightarrow> (removeAll a xs, xs') \<in> revdups_rel"
  apply(induction xs arbitrary: xs')
  unfolding revdups_rel_def
  by(auto simp: in_br_conv remdups_snoc rev_removeAll)

lemma revdups_rel_snoc_hd: "(xs, a # xs') \<in> revdups_rel \<Longrightarrow> hd xs = a"
  unfolding revdups_rel_def
  apply(induction xs)
  by(auto simp: in_br_conv snoc_eq_iff_butlast remdups_snoc)  



lemma br_comp_altR: "R O br \<alpha> I = {(a,c) | a b c. (a,b) \<in> R \<and> I b \<and> \<alpha> b = c}"
  unfolding br_def by auto


lemma Ex_subset_list_rel: "(xs, xs') \<in> \<langle>A\<rangle>list_rel \<Longrightarrow> set ys \<subseteq> set xs \<Longrightarrow> \<exists>ys'. (ys, ys') \<in> \<langle>A\<rangle>list_rel"
  unfolding list_rel_def 
  apply(induction ys)
  apply simp
  apply clarsimp
  by (metis in_set_conv_nth list.rel_intros(2) list_all2_nthD)


(*TODO: GENERALIZE*)
lemma Id_lset_rel_alt: "\<langle>Id\<rangle>lset_rel = revdups_rel O \<langle>Id\<rangle>list_set_rel" 
  apply(safe)
  subgoal
    unfolding lset_rel_def revdups_rel_def list_set_rel_def
    by (simp add: in_br_conv list.rel_eq relcomp.simps)
  subgoal
    unfolding lset_rel_def revdups_rel_def list_set_rel_def
    apply(rule relcompI)
    apply simp
    by (simp add: in_br_conv)[]
  done



lemma LIST_FOREACH_unfold: "LIST_FOREACH \<Phi> (RETURN tsl) c f \<sigma> \<le> (if \<Phi> (set tsl) \<sigma> then (if c \<sigma> then (case tsl of [] \<Rightarrow> RETURN \<sigma> | x # xs \<Rightarrow> f x \<sigma> \<bind> (\<lambda> \<sigma>. LIST_FOREACH \<Phi> (RETURN xs) c f \<sigma>)) else RETURN \<sigma>) else Refine_Basic.FAIL)"
  unfolding LIST_FOREACH_def
  apply(cases tsl)
  subgoal apply clarsimp 
    apply(subst WHILEIT_unfold)
    by(auto simp: FOREACH_cond_def)
  subgoal 
    apply(subst WHILEIT_unfold)
    by (auto simp: FOREACH_body_def FOREACH_cond_def Cons_eq_append_conv intro!: bind_mono WHILEIT_weaken ) 
  done


lemma LIST_FOREACH'_unfold: "LIST_FOREACH' (RETURN tsl) c f \<sigma> = (if c \<sigma> then (case tsl of [] \<Rightarrow> RETURN \<sigma> | x # xs \<Rightarrow> f x \<sigma> \<bind> (\<lambda> \<sigma>. LIST_FOREACH' (RETURN xs) c f \<sigma>)) else RETURN \<sigma>)"
  unfolding LIST_FOREACH'_def by(auto split: list.splits)


lemma nfoldli_fsimps: (*TODO: add to simp set? May clash with nfoldli_simps?*)
  "nfoldli [] c f = RETURN"
  "nfoldli (x#ls) c f = (\<lambda>s. 
    (if c s then do { s\<leftarrow>f x s; nfoldli ls c f s} else RETURN s))"
  apply(rule ext)
  apply (subst nfoldli.simps, auto)+
  done

lemma nfoldli_unfold: "nfoldli xs c f \<sigma> = (if c \<sigma> then (case xs of [] \<Rightarrow> RETURN \<sigma> | x # xs \<Rightarrow> f x \<sigma> \<bind> nfoldli xs c f) else RETURN \<sigma>)"
  by(auto split: list.splits)

lemma nfoldli_rev_unfold: "nfoldli xs c f \<sigma> = (if xs = [] then RETURN \<sigma> else nfoldli (butlast xs) c f \<sigma> \<bind> (\<lambda>\<sigma>. (if c \<sigma> then f (last xs) \<sigma> else RETURN \<sigma>)))"
  apply(induction xs arbitrary: \<sigma> rule: rev_induct)
  by (auto simp: nfoldli_fsimps intro!: bind_cong) 

lemma nfoldli_deriv_set1: 
  assumes SI: "S s0 \<subseteq> set xs"
  assumes SNS: "(\<And> i s. i \<notin> S s \<Longrightarrow> f i s \<le> SPEC (\<lambda> s'. i \<in> S s' \<and> S s \<subseteq> S s' \<and> S s' \<subseteq> set xs))"
  assumes SES: "(\<And> i s. i \<in> S s \<Longrightarrow> f i s \<le> RETURN s)"
  assumes CS: "(\<And>s. \<not>c s \<Longrightarrow> S s = set xs)"
  shows "nfoldli xs c f s0 \<le> SPEC (\<lambda>s. S s = set xs)"
  apply(refine_vcg nfoldli_rule[where ?I="(\<lambda> xsd xs' s. S s0 \<subseteq> S s \<and> set xsd \<subseteq> S s \<and> S s \<subseteq> set xs)"])
  subgoal by simp
  subgoal using SI by presburger
  subgoal for x xsd xs' s
    apply(cases "x \<in> S s")
    subgoal by(refine_vcg order_trans[OF SES]; auto)
    subgoal by(refine_vcg order_trans[OF SNS]; auto)
    done
  subgoal using CS by auto
  subgoal by blast
  done

lemma nfoldli_deriv_set2: 
  assumes ST: "s0 \<in> T"
  assumes STX: "(\<And> s. s \<in> T \<Longrightarrow> S s \<subseteq> set xs)"
  assumes SNS: "(\<And> i s. i \<notin> S s \<Longrightarrow> s \<in> T \<Longrightarrow> f i s \<le> SPEC (\<lambda> s'. i \<in> S s' \<and> S s \<subseteq> S s' \<and> s' \<in> T))"
  assumes SES: "(\<And> i s. i \<in> S s \<Longrightarrow> s \<in> T \<Longrightarrow> f i s \<le> RETURN s)"
  assumes CS: "(\<And>s. s \<in> T \<Longrightarrow> \<not>c s \<Longrightarrow> S s = set xs)"
  shows "nfoldli xs c f s0 \<le> SPEC (\<lambda>s. s \<in> T \<and> S s = set xs)"
  apply(refine_vcg nfoldli_rule[where ?I="(\<lambda> xsd xs' s. S s0 \<subseteq> S s \<and> set xsd \<subseteq> S s \<and> s \<in> T)"])
  subgoal by simp
  subgoal using ST by presburger
  subgoal for x xsd xs' s
    apply(cases "x \<in> S s")
    subgoal by(refine_vcg order_trans[OF SES]; auto)
    subgoal by(refine_vcg order_trans[OF SNS]; auto)
    done
  subgoal using CS by auto
  subgoal using CS by auto
  subgoal by presburger
  subgoal using STX by fast
  done



lemma nfoldli_removeAll_refine: 
  assumes SNS: "(\<And> i s. i \<notin> S s \<Longrightarrow> f i s \<le> SPEC (\<lambda> s'. S s \<subseteq> S s'))" 
  assumes SES: "(\<And> i s. i \<in> S s \<Longrightarrow> f i s \<le> RETURN s)"
  assumes ASS: "a \<in> S s"
  shows "nfoldli xs c f s \<le> nfoldli (removeAll a xs) c f s"
using ASS
proof(induction xs arbitrary: s)
  case Nil
  then show ?case  by simp
next
  case (Cons b xs)
  then show ?case
  proof(cases "b = a")
    case True

    with SES have "f a s \<le> RETURN s"
      using Cons.prems by presburger

    then show ?thesis
      using True Cons.IH[OF Cons(2)] apply clarsimp 
      apply(rule specify_left; unfold ireturn_eq) 
      apply assumption 
      by blast 
  next
    case False

    have "RETURN x \<le> f b s \<Longrightarrow> a \<in> S x" for x
      apply(cases "b \<in> S s")
      using SES lfp.leq_trans Cons(2) apply fastforce
      using gfp.leq_trans Cons(2) by (fastforce dest: SNS)
    then show ?thesis
      using False by (auto intro!: bind_mono Cons.IH)
  qed
qed


lemma nfoldli_revdups_refine:
  assumes RREL:"(xs,xs') \<in> revdups_rel"
  assumes SNS: "(\<And> i s. i \<notin> S s \<Longrightarrow> f i s \<le> SPEC (\<lambda> s'. i \<in> S s' \<and> S s \<subseteq> S s'))"
  assumes SES: "(\<And> i s. i \<in> S s \<Longrightarrow> f i s \<le> RETURN s)"
  shows "nfoldli xs c f s0 \<le> nfoldli xs' c f s0"
using RREL
proof(induction xs' arbitrary: xs s0)
  case Nil
  then show ?case 
    by(auto dest: revdups_rel_set_eq)
next
  case (Cons a xs')

  from Cons.prems(1) have "(removeAll a xs, xs') \<in> revdups_rel" 
    using revdups_rel_Cons_removeAll by fast
  with Cons.IH have IH: "nfoldli (removeAll a xs) c f s' \<le> nfoldli xs' c f s'" for s'
    by fast

  obtain ys where XSD: "xs = a # ys"
    using revdups_rel_snoc_hd Cons.prems  revdups_rel_set_eq
    by (metis empty_iff list.collapse list.set(1) list.set_intros(1))
  hence "(removeAll a ys, xs') \<in> revdups_rel"
    using revdups_rel_Cons_removeAll[OF Cons.prems] by force

  have REF': "(\<And> s' a s. RETURN s \<le> f a s' \<Longrightarrow> a \<in> S s)"
    by (smt (verit, del_insts) SNS SES SPEC_eq_is_RETURN(1) inres_SPEC inres_def)

  have "nfoldli (a # ys) c f s0 \<le> nfoldli (a # (removeAll a ys)) c f s0"
    apply(clarsimp)
    apply(rule bind_mono)
    apply blast
    apply(rule nfoldli_removeAll_refine)
    apply(rule order_trans[OF SNS]) 
    apply blast 
    apply force 
    apply(rule SES; assumption)
    apply(erule REF')
    done


  also have "nfoldli (a # (removeAll a ys)) = nfoldli (a # (removeAll a xs))"
    using XSD by force


  also have "nfoldli (a # (removeAll a xs)) c f s0 \<le> nfoldli (a # xs') c f s0"
    by (auto intro!: bind_mono IH)


  finally show ?case using XSD by presburger

qed



lemma LLFO_refine_Id:
  assumes LREL: "(li,l)\<in>\<langle>Id\<rangle>lset_rel" (*TODO: We need Id here because we did not manage to prove a more general version of Id_lset_rel_alt (And at the moment I am not even sure if it holds anymore)*)
  assumes REFI: "(s0i,s0)\<in>R"
  assumes REF: "\<And>x xi s si. \<lbrakk>(xi,x)\<in>Id; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  assumes SNS: "(\<And> i s. i \<notin> S s \<Longrightarrow> fi i s \<le> SPEC (\<lambda> s'. i \<in> S s' \<and> S s \<subseteq> S s'))"
  assumes SES: "(\<And> i s. i \<in> S s \<Longrightarrow> fi i s \<le> RETURN s)"
  shows "nfoldli li (\<lambda>_. True) fi s0i \<le> \<Down>R (FOREACH l f s0)"
proof -

  from LREL obtain l' where A: "(li,l') \<in> revdups_rel" and B: "(l',l) \<in> \<langle>Id\<rangle>list_set_rel"
    unfolding Id_lset_rel_alt by blast

  show ?thesis
    apply(rule order_trans[OF nfoldli_revdups_refine LFO_refine])
    apply(rule A)
    apply(erule SNS)
    apply(erule SES)
    apply(rule B)
    apply(erule REF; assumption)
    apply(rule REFI)
    done

qed

lemma eq_conc_fun_le: "M \<le> M' \<Longrightarrow> \<Down>R M \<le> \<Down>R M'"
  by (auto simp: pw_le_iff refine_pw_simps)

lemma LLFO_refine: (*TODO: I am not happy with what I did here, sure this works but set S is now suddenly defined over f rather than fi, which might actually correspond better with what I am trying to achieve?*)
  assumes LREL: "(li,l)\<in>\<langle>A\<rangle>lset_rel" 
  assumes REFI: "(s0i,s0)\<in>R"
  assumes REF: "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  assumes SNS: "(\<And> i s. i \<notin> S s \<Longrightarrow> f i s \<le> SPEC (\<lambda> s'. i \<in> S s' \<and> S s \<subseteq> S s'))"
  assumes SES: "(\<And> i s. i \<in> S s \<Longrightarrow> f i s \<le> RETURN s)"
  shows "nfoldli li (\<lambda>_. True) fi s0i \<le> \<Down>R (FOREACH l f s0)"
proof -

  have "\<langle>A\<rangle>lset_rel = \<langle>A\<rangle>list_rel O \<langle>Id\<rangle>lset_rel"
    unfolding lset_rel_def by auto

  with LREL obtain l' where A: "(li,l') \<in> \<langle>A\<rangle>list_rel" and B: "(l',l) \<in> \<langle>Id\<rangle>lset_rel"
    by blast

  show ?thesis
    apply(rule order_trans[OF nfoldli_refine[where ?R=R, simplified]] )
    using A apply assumption
    using REFI apply assumption
    apply force
    apply simp
    apply(rule REF; simp_all)
    apply(rule eq_conc_fun_le)
    apply(rule LLFO_refine_Id[where ?R=Id, simplified])
    using B apply assumption
    apply(rule refl)
    apply blast
    apply(erule SNS)
    apply(erule SES)
    done
qed




type_synonym 'i iterator = "'i list"


definition iinit :: "'i list \<Rightarrow> 'c \<Rightarrow> 'i iterator" where "iinit i c = i"
definition itest :: "'c \<Rightarrow> 'i iterator \<Rightarrow> bool" where "itest = (\<lambda> c i. i \<noteq> [])"
definition inext :: "'c \<Rightarrow> 'i iterator \<Rightarrow> 'i \<times> 'i iterator" where "inext = (\<lambda> c i. (hd i, tl i))"

definition IT_nfoldli :: "'i list \<Rightarrow> 'c \<Rightarrow> ('i \<Rightarrow> 'a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres" where 
  "IT_nfoldli i c f \<sigma> \<equiv> nfoldli i (\<lambda>_. True) f \<sigma>"

definition IT_WHILE :: "'i list \<Rightarrow> 'c \<Rightarrow> ('i \<Rightarrow> 'a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres" where "IT_WHILE i c f \<sigma> = do{
  let i = iinit i c;
  (it,\<sigma>) \<leftarrow> WHILET (\<lambda> (it,\<sigma>). itest c it) (\<lambda> (it,\<sigma>). do{
    let (i,it) = inext c it;
    \<sigma> \<leftarrow> f i \<sigma>;
    RETURN (it,\<sigma>)
  }) (i,\<sigma>);
  RETURN \<sigma>
}"

definition IT_WHILE_impl :: "('i list \<Rightarrow> 'c \<Rightarrow> 'j nres) \<Rightarrow> ('c \<Rightarrow> 'j \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'j \<Rightarrow> ('i \<times> 'j) nres) \<Rightarrow> 'i list \<Rightarrow> 'c \<Rightarrow> ('i \<Rightarrow> 'a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres" where
  "IT_WHILE_impl iin its ixt i c f \<sigma> = do{
  i \<leftarrow> iin i c;
  (it,\<sigma>) \<leftarrow> WHILET (\<lambda> (it,\<sigma>). its c it) (\<lambda> (it,\<sigma>). do{
    (i,it) \<leftarrow> ixt c it;
    \<sigma> \<leftarrow> f i \<sigma>;
    RETURN (it,\<sigma>)
  }) (i,\<sigma>);
  RETURN \<sigma>
}"

lemma rel_to_rel_Id: "(a,b) \<in> R \<Longrightarrow> ((a,c),(b,c)) \<in> (R \<times>\<^sub>r Id)"
  by simp

lemma IT_WHILE_impl_refine: 
  assumes IIN: "iin is c \<le> \<Down> Ri (RETURN (iinit is c))"
  assumes ITS: "\<And> i ii. (ii,i) \<in> Ri \<Longrightarrow> its c ii \<longleftrightarrow> itest c i"
  assumes INX: "\<And> i ii. (ii,i) \<in> Ri \<Longrightarrow> itest c i \<Longrightarrow> inx c ii \<le> \<Down>(Id \<times>\<^sub>r Ri) (RETURN (inext c i))"
  assumes REF: "\<And> i s. fi i s \<le> f i s"
  shows "IT_WHILE_impl iin its inx is c fi \<sigma> \<le> IT_WHILE is c f \<sigma>"
  unfolding IT_WHILE_impl_def IT_WHILE_def let_to_bind_conv
  apply(rule bind_refine[where ?R=Id, simplified])
  apply(rule IIN)
  apply(rule bind_refine[where ?R=Id, simplified])
  apply(refine_vcg WHILET_refine)
  apply(erule rel_to_rel_Id)
  apply(auto simp: ITS)[] 
  apply(auto simp: conc_fun_RETURN intro!: order_trans[OF INX])[] 
  apply(auto intro!: refine_IdI)[]
  apply(auto intro!: REF refine_IdI)[]
  apply simp
  apply auto
  done

lemma itest_simps [simp]: "\<not>itest c []" "itest c (x#xs)"
  unfolding itest_def
  by blast+

lemma inext_cons[simp]: "inext c (x#xs) = (x,xs)"
  unfolding inext_def by simp

lemma IT_nfoldli_eq: "IT_nfoldli i c f \<sigma> = IT_WHILE i c f \<sigma>"
proof -
  have "IT_WHILE i c f \<sigma> = IT_nfoldli i c f \<sigma>"
    unfolding IT_WHILE_def IT_nfoldli_def iinit_def
    apply clarsimp
    apply(induction i arbitrary: \<sigma>)
    subgoal
      apply(subst WHILET_unfold)
      by fastforce
    subgoal
      apply(subst WHILET_unfold)
      by (auto) 
    done
  thus ?thesis by presburger
qed
    
end

