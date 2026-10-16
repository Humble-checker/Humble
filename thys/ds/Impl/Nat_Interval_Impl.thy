theory Nat_Interval_Impl
  imports "II_Modest_Base.Nat_Interval" 
begin

  lemma upt_list_set_rel_Id: "(li,l) \<in> Id \<Longrightarrow> (hi,h) \<in> Id \<Longrightarrow> ([li..<hi], {l..<h}) \<in> \<langle>nat_rel\<rangle>list_set_rel"
    using upt_list_set_rel by auto

  lemmas LFO_refine_while_by_upt = upt_list_set_rel_Id[THEN LFO_refine[where ?l = "{l..<h}" and ?li = "[li..<hi]" and ?A=Id for l h li hi, unfolded nfoldli_upt_by_while conj.comm_neutral]]

  lemmas LFOc_refine_while_by_upt = upt_list_set_rel_Id[THEN LFOc_refine[where ?l = "{l..<h}" and ?li = "[li..<hi]" and ?A=Id for l h li hi, unfolded nfoldli_upt_by_while conj.comm_neutral]]


  definition "FOREACH_intv xs i = FOREACH (sn_intv (sorted_intvs xs ! i))"

  definition "WHILE_intv xs i f \<sigma> = do {
    (_,\<sigma>) \<leftarrow> WHILET (\<lambda>(j, \<sigma>). j < xs ! (Suc i)) (\<lambda> (j, \<sigma>). do{ 
      \<sigma> \<leftarrow> f j \<sigma>;
      ASSERT (j < xs ! (Suc i));
      RETURN (j + 1,\<sigma>)
    }) (xs ! i,\<sigma>);
    RETURN \<sigma>
  }"

  (*TODO: these can be generalized: list_rel instead Id for xs*)
  lemma WHILE_intv_refine:
    assumes SORT: "sorted xs"
    assumes IB: "i < length xs - Suc 0"
    assumes IID: "(ii,i) \<in> Id"
    assumes XSID: "(xsi,xs) \<in> Id"
    assumes FREF: "\<And>x xi s si. \<lbrakk>(xi,x)\<in>Id; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
    assumes SR: "(\<sigma>i,\<sigma>)\<in>R"
    shows "WHILE_intv xsi ii fi \<sigma>i \<le> \<Down> R (FOREACH_intv xs i f \<sigma>)"
    unfolding WHILE_intv_def FOREACH_intv_def sn_intv_sorted_intvs[OF SORT IB]
    apply(rule LFO_refine_while_by_upt)
    using IID XSID FREF SR by auto


  definition "FOREACHc_intv xs i = FOREACHc (sn_intv (sorted_intvs xs ! i))"

  definition "WHILEc_intv xs i c f \<sigma> = do {
    (_,\<sigma>) \<leftarrow> WHILET (\<lambda>(j, \<sigma>). j < xs ! (Suc i) \<and> c \<sigma>) (\<lambda> (j, \<sigma>). do{ 
      \<sigma> \<leftarrow> f j \<sigma>;
      ASSERT (j < xs ! (Suc i));
      RETURN (j + 1,\<sigma>)
    }) (xs ! i,\<sigma>);
    RETURN \<sigma>
  }"

  
 
  lemma WHILEc_intv_refine:
    assumes SORT: "sorted xs"
    assumes IB: "i < length xs - Suc 0"
    assumes IID: "(ii,i) \<in> Id"
    assumes XSID: "(xsi,xs) \<in> Id"
    assumes CR: "(\<And>s si. (si, s) \<in> R \<Longrightarrow> ci si = c s)"
    assumes FREF: "\<And>x xi s si. \<lbrakk>(xi,x)\<in>Id; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
    assumes SR: "(\<sigma>i,\<sigma>)\<in>R"
    shows "WHILEc_intv xsi ii ci fi \<sigma>i \<le> \<Down> R (FOREACHc_intv xs i c f \<sigma>)"
    unfolding WHILEc_intv_def FOREACHc_intv_def sn_intv_sorted_intvs[OF SORT IB]
    apply(rule LFOc_refine_while_by_upt)
    using IID XSID FREF SR CR by auto


end