theory MDP_MEC
  imports Main "../ds/SCC_map" "../II/MDP_Components" "../II/MDP_Util"
begin

hide_const (open) R r measure MDP_Components.is_scc

text \<open>
  This file contains basic definitions surrounding the MDP structure. We lay the foundations
  for the definition of MECs in the folder MaxEndComponent.thy.
\<close>

section  \<open>Auxiliary General Lemmas\<close>

lemma (in Finite_MDP) set_pmf_closed': \<open>D \<in> actions M s \<Longrightarrow> t \<in> set_pmf D \<Longrightarrow> t \<in> states M\<close>
  using closed_mdpcD[OF closed_M] by auto

lemmas states_map_mdpc[simp]

lemma rtrancl_eq_trancl_cases: "(a,b) \<in> R\<^sup>* \<Longrightarrow> (a = b \<Longrightarrow> P) \<Longrightarrow> ((a,b) \<in> R\<^sup>+ \<Longrightarrow> P) \<Longrightarrow> P"
  by (meson rtranclD)

lemma rtrancl_Restr_cases: "R \<subseteq> A \<times> A \<Longrightarrow> (a,b) \<in> R\<^sup>* \<Longrightarrow> (a = b \<Longrightarrow> (a,b) \<notin> Restr (R\<^sup>*) A \<Longrightarrow> P) \<Longrightarrow> ((a,b) \<in> Restr (R\<^sup>*) A \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis Int_iff rtranclD subsetD trancl_subset_Sigma)

lemma finite_property_set: assumes "finite {x. P x}" and "\<forall>x\<in>A. P x" shows "finite A"
  by (metis assms(1) assms(2) mem_Collect_eq rev_finite_subset subsetI)

lemma ex_transitive_transition: "(p, q) \<in> r\<^sup>* \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q - P \<Longrightarrow> r \<subseteq> Q \<times> Q \<Longrightarrow> (\<exists> p2 \<in> P. (\<exists> q2 \<in> Q - P. (p2,q2) \<in> r))"
  apply(induction rule: rtrancl.induct)
   apply fast
  by blast

lemma ex_transitive_transition': "(p, q) \<in> r\<^sup>* \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> p \<in> Q - P \<Longrightarrow> q \<in> P \<Longrightarrow> r \<subseteq> Q \<times> Q \<Longrightarrow> (\<exists> p2 \<in> Q - P. (\<exists> q2 \<in> P. (p2,q2) \<in> r))"
  apply(induction rule: rtrancl.induct)
   apply fast
  by blast
  
lemma trancl_through_pred: "(u,v) \<in> r\<^sup>+ \<Longrightarrow> \<exists>w \<in> r\<inverse> `` {v}. (u,w) \<in> r\<^sup>*"
  apply(induction rule: trancl_induct)
   apply blast
  by (metis Image_singleton_iff converse.intros trancl_into_rtrancl)

lemma distinct_elems_not_singleton: "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<not>is_singleton X"
  unfolding is_singleton_def by blast 

lemma mem_nsingleton_get_distinct_mem:
  assumes "u \<in> X" and "\<not>is_singleton X" 
  obtains v where "u \<noteq> v" and "v \<in> X"
  by (metis assms empty_iff is_singletonI')

lemma pairwise_disjnt_alt: "(pairwise disjnt C) = (\<forall> x X Y. X \<in> C \<longrightarrow> Y \<in> C \<longrightarrow> x \<in> X \<longrightarrow> x \<in> Y \<longrightarrow> X = Y)"
  unfolding pairwise_def disjnt_def by blast

lemma pairwise_disjntI: "(\<And> x X Y. X \<in> C \<Longrightarrow> Y \<in> C \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> Y \<Longrightarrow> X = Y) \<Longrightarrow> pairwise disjnt C"
  using pairwise_disjnt_alt by blast

lemma pairwise_disjntD: "pairwise disjnt C \<Longrightarrow> (\<And> x X Y. X \<in> C \<Longrightarrow> Y \<in> C \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> Y \<Longrightarrow> X = Y)"
  using pairwise_disjnt_alt by meson

lemma pairwise_disjnt_Un: "pairwise disjnt C\<^sub>1 \<Longrightarrow> pairwise disjnt C\<^sub>2 \<Longrightarrow> (\<And> X Y. X \<in> C\<^sub>1 \<Longrightarrow> Y \<in> C\<^sub>2 \<Longrightarrow> disjnt X Y) \<Longrightarrow> pairwise disjnt (C\<^sub>1 \<union> C\<^sub>2)"
  unfolding pairwise_def
  by (metis Un_iff disjnt_sym)

lemma disj_finite_set_of_subsets_card_bound: 
  assumes DISJ: "pairwise disjnt C"
  assumes CS: "(\<And>X. X \<in> C \<Longrightarrow> X \<subseteq> S)"
  assumes FIN: "finite S"
  assumes NE: "{} \<notin> C"
  shows "card C \<le> card S"
proof -

  define f where "f \<equiv> (\<lambda> X. SOME x::'a. x \<in> X)"

  have A: "X \<in> C \<Longrightarrow> (SOME xa. xa \<in> X) \<in> X" for X
    using NE some_in_eq by blast

  have inj_f: "inj_on f  C" 
    unfolding f_def
    apply(rule inj_onI)
    apply(rule pairwise_disjntD[OF DISJ])
    apply(auto intro: A) 
    done
  
  have f_sub: "f ` C \<subseteq> S" 
    apply (clarsimp simp: f_def)
    apply(frule A) 
    apply(drule CS)
    by blast

  show ?thesis
    apply(rule card_inj_on_le)
    apply(rule inj_f)
    apply(rule f_sub)
    apply(rule FIN)
    done
qed
 
lemma trancl_wf: "wf (r\<^sup>+) \<Longrightarrow> wf r"
  apply(erule wf_subset)
  by auto

lemma wf_trancl_wf: "wf (r\<^sup>+) = wf r"
  using wf_trancl trancl_wf by blast

definition dep_lex_prod :: "('a \<times>'a) set \<Rightarrow> ('a \<Rightarrow> ('b \<times> 'b) set) \<Rightarrow> (('a \<times> 'b) \<times> ('a \<times> 'b)) set"
    (infixr "<*dlex*>" 80)
    where "ra <*dlex*> frb = {((a, b), (a', b')). (a, a') \<in> ra \<or> a = a' \<and> (b, b') \<in> frb a}"

lemma in_dep_lex_prod[simp]: "((a, b), (a', b')) \<in> r <*dlex*> s \<longleftrightarrow> (a, a') \<in> r \<or> a = a' \<and> (b, b') \<in> s a"
  by (auto simp:dep_lex_prod_def)

lemma wf_dep_lex_prod:
  assumes WFA: "wf ra" 
  and WFB: "(\<And>x. wf (rb x))" 
  shows "wf (ra <*dlex*> rb)"
proof (rule wfI)
  fix z :: "'a \<times> 'b" and P
  assume * [rule_format]: "\<forall>u. (\<forall>v. (v, u) \<in> ra <*dlex*> rb \<longrightarrow> P v) \<longrightarrow> P u"
  obtain x y where zeq: "z = (x,y)"
    by fastforce
  have "P(x,y)" using \<open>wf ra\<close>
  proof (induction x arbitrary: y rule: wf_induct_rule)
    case (less x)
    note lessx = less
    show ?case using \<open>wf (rb x)\<close> less
    proof (induction y rule: wf_induct_rule)
      case (less y)
      show ?case 
        by(force intro: * less.IH lessx)
    qed
  qed
  then show "P z"
    by (simp add: zeq)
  qed auto

lemma prod_rel_sub_rel: "R1 \<times>\<^sub>r R2 \<subseteq> (Domain R1 \<times> Domain R2) \<times> (Range R1 \<times> Range R2)"
  unfolding prod_rel_def
  by fast


lemma wf_UNIV_prod_rel_left: assumes WF: "wf R\<^sub>1" shows "wf (R\<^sub>1 \<times>\<^sub>r UNIV)"
proof(unfold wf_eq_minimal2, intro allI impI, elim conjE)
  fix A
  assume AS: "A \<subseteq> Field (R\<^sub>1 \<times>\<^sub>r UNIV)" and "A \<noteq> {}"
  then obtain B where BDEF: "B = fst ` A" and BS: "B \<subseteq> Field R\<^sub>1" and "B \<noteq> {}" unfolding Field_def
    by force
  then obtain b where "b \<in> B" and "\<forall>b'\<in>B. (b', b) \<notin> R\<^sub>1" using WF[unfolded wf_eq_minimal2]
    by meson
  moreover then obtain c where BCA: "(b,c) \<in> A" using BDEF
    by force
  ultimately have "\<forall> (b',c') \<in> A. ((b',c'), (b,c)) \<notin> (R\<^sub>1 \<times>\<^sub>r UNIV)" unfolding prod_rel_def
    using AS BS 
    using BDEF by force
  then show "\<exists>a\<in>A. \<forall>a'\<in>A. (a', a) \<notin> R\<^sub>1 \<times>\<^sub>r UNIV"
    apply -
    apply(rule bexI[where ?x="(b,c)"])
    by (auto simp: BCA)
qed

lemma wf_UNIV_prod_rel_right: assumes WF: "wf R\<^sub>2" shows "wf (UNIV \<times>\<^sub>r R\<^sub>2)"
proof(unfold wf_eq_minimal2, intro allI impI, elim conjE)
  fix A
  assume AS: "A \<subseteq> Field (UNIV \<times>\<^sub>r R\<^sub>2)" and "A \<noteq> {}"
  then obtain B where BDEF: "B = snd ` A" and BS: "B \<subseteq> Field R\<^sub>2" and "B \<noteq> {}" unfolding Field_def
    by force
  then obtain b where "b \<in> B" and "\<forall>b'\<in>B. (b', b) \<notin> R\<^sub>2" using WF[unfolded wf_eq_minimal2]
    by meson
  moreover then obtain c where CBA: "(c,b) \<in> A" using BDEF
    by force
  ultimately have "\<forall> (c',b') \<in> A. ((c',b'), (c,b)) \<notin> (UNIV \<times>\<^sub>r R\<^sub>2)" unfolding prod_rel_def
    using AS BS 
    using BDEF by force
  then show "\<exists>a\<in>A. \<forall>a'\<in>A. (a', a) \<notin> UNIV \<times>\<^sub>r R\<^sub>2"
    apply -
    apply(rule bexI[where ?x="(c,b)"])
    by (auto simp: CBA)
qed

lemma wf_prod_rel_left: "wf R\<^sub>1 \<Longrightarrow> wf (R\<^sub>1 \<times>\<^sub>r R\<^sub>2)"
  apply(rule wf_subset[of "R\<^sub>1 \<times>\<^sub>r UNIV"])
  apply(erule wf_UNIV_prod_rel_left)
  by force

lemma wf_prod_rel_right: "wf R\<^sub>2 \<Longrightarrow> wf (R\<^sub>1 \<times>\<^sub>r R\<^sub>2)"
  apply(rule wf_subset[of "UNIV \<times>\<^sub>r R\<^sub>2"])
  apply(erule wf_UNIV_prod_rel_right)
  by force

definition finite_ne_psubset :: "('a set \<times> 'a set) set"
  where "finite_ne_psubset = {(A, B). A \<subset> B \<and> finite B \<and> A \<noteq> {}}"

lemma finite_ne_psubset_sub: "finite_ne_psubset \<subseteq> finite_psubset"
  unfolding finite_ne_psubset_def finite_psubset_def 
  by fastforce

lemma union_trancl_subset_trancl_union: "(\<Union>i \<in> A. (f i)\<^sup>*) \<subseteq> (\<Union> i \<in> A. f i)\<^sup>*" 
  apply clarsimp 
  subgoal for u v i
    apply(rotate_tac) 
    apply(induction rule: rtrancl.induct)
    subgoal by simp
    subgoal for u v w
      apply(subgoal_tac "(v,w) \<in> \<Union> (f ` A)") 
      subgoal
        by (meson rtrancl.simps)
      subgoal 
        by blast
      done
    done
  done


lemma dir_image_mem[simp, intro]: "(a,b) \<in> r \<Longrightarrow> (f a, f b) \<in> dir_image r f"
  unfolding dir_image_def by auto

lemma dir_image_wf:
  assumes WF: "wf (dir_image r f)" 
  shows "wf r" 
proof(unfold wf_eq_minimal2, intro allI impI, elim conjE)
  fix A
  assume "A \<subseteq> Field r" and "A \<noteq> {}"
  then obtain B where BDEF: "B = f ` A" and "B \<noteq> {}" and "B \<subseteq> Field (dir_image r f)"
    by (auto simp: dir_image_Field)
  then obtain b where "b \<in> B" and "\<forall>b'\<in>B. (b', b) \<notin> (dir_image r f)" using WF[unfolded wf_eq_minimal2]
    by metis
  then show "\<exists>a\<in>A. \<forall>a'\<in>A. (a', a) \<notin> r" 
    by (auto simp: BDEF) 
qed

section "Markov Decision Processes"

text \<open>
  The MDP structure is defined as a list of lists. The outer list represents the transitions while
  the inner list represents the branches.
  We chose this representation for straightforward compatibility with the SCC algorithm.

  NOTE: The SCC algorithm can be refined to abstractly use an MDP structure as a set of sets,
    but since the current representation is abstract enough for our purposes we have marked it
    as a future improvement.
\<close>


type_synonym 'a mdp_K = "'a \<Rightarrow> 'a set set"


locale mdp_def = 
  fixes S :: "'v set" and K :: "'v mdp_K" 
begin
  
  definition "Et_\<alpha> = {(u,v) | u v. u \<in> S \<and> (\<exists>a \<in> K u. v \<in> a)}"

  lemma Et_\<alpha>_mem: "(u,v) \<in> Et_\<alpha> \<longleftrightarrow> u \<in> S \<and> (\<exists>a \<in> (K u). v \<in> a)"
    unfolding Et_\<alpha>_def by blast
  
  lemma Et_\<alpha>_mem': "u \<in> S \<Longrightarrow> (u,v) \<in> Et_\<alpha> \<longleftrightarrow> v \<in> \<Union>(K u)"
    unfolding Et_\<alpha>_def by blast
  
  lemma Et_\<alpha>_image_eq: "u \<in> S \<Longrightarrow> Et_\<alpha> `` {u} = \<Union>(K u)"
    unfolding Et_\<alpha>_def by blast

  lemma Et_\<alpha>I: "u \<in> S \<Longrightarrow> v \<in> a \<Longrightarrow> a \<in> K u \<Longrightarrow> (u,v) \<in> Et_\<alpha>"
    unfolding Et_\<alpha>_def by blast

  definition "scc_set u = {scc. is_scc Et_\<alpha> scc \<and> scc \<subseteq> Et_\<alpha> `` {u}}"

  lemma scc_in_S: 
    assumes US: "u \<in> S" 
    and USCC:  "u \<in> scc" 
    and SCC: "is_scc Et_\<alpha> scc" 
    shows "scc \<subseteq> S"
  proof(rule ccontr)
    assume "\<not> scc \<subseteq> S"
    then obtain v where "v \<in> scc" and VNS:"v \<notin> S"
      by fast
    with SCC USCC have "(v,u) \<in> Et_\<alpha>\<^sup>*"
      by (simp add: is_scc_connected)
    then obtain w where "(v,w) \<in> Et_\<alpha>" 
      by (metis VNS US converse_rtranclE)
    thus False by(auto simp: Et_\<alpha>_mem VNS)
  qed

end

lemma subset_Et_\<alpha>: "S' \<subseteq> S \<Longrightarrow> mdp_def.Et_\<alpha> S' K \<subseteq> mdp_def.Et_\<alpha> S K"
  unfolding mdp_def.Et_\<alpha>_def by fast


text \<open>
  A closed MDP S K is an MDP such that all transitions that start in S also end in S.
\<close>

definition "closed_mdp S' K' \<equiv> \<forall>u \<in> S'. \<forall> a \<in> K' u. a \<subseteq> S'"


lemma closed_mdpI: "(\<And>u a v. u \<in> S' \<Longrightarrow> a \<in> K' u \<Longrightarrow> v \<in> a \<Longrightarrow> v \<in> S') \<Longrightarrow> closed_mdp S' K'"
  unfolding closed_mdp_def
  by blast

lemma closed_mdpD: "closed_mdp S' K' \<Longrightarrow> u \<in> S' \<Longrightarrow> a \<in> K' u \<Longrightarrow> v \<in> a \<Longrightarrow> v \<in> S'"
  unfolding closed_mdp_def  by blast

lemma empty_closed_mdp[simp]: "closed_mdp {} K'"
  unfolding closed_mdp_def by simp

lemma closed_mdp_insert_trans: "closed_mdp S' K' \<Longrightarrow> a \<subseteq> S' \<Longrightarrow> closed_mdp S' (K'(u := insert a (K' u)))"
  unfolding closed_mdp_def by auto

lemma closed_mdp_restr_edges: "closed_mdp S' K' \<Longrightarrow> mdp_def.Et_\<alpha> S' K' \<subseteq> S' \<times> S'"
  unfolding closed_mdp_def mdp_def.Et_\<alpha>_def  by blast

  lemma closedfin_finite_actions:
    assumes CL: "closed_mdp S' K'"
    assumes FIN:  "finite S'"
    assumes US: "u \<in> S'"
    assumes AKU: "a \<in> K' u"
    shows "finite a"
  proof -

    have "a \<subseteq> S'" using closed_mdpD[OF CL US AKU] 
      by blast

    thus ?thesis
      by (simp add: finite_subset[OF _ FIN])

  qed

  lemma closedfin_finite_K:
    assumes CL: "closed_mdp S' K'"
    assumes FIN:  "finite S'"
    assumes US: "u \<in> S'"
    shows "finite (K' u)"
  proof -

    have "K' u \<subseteq> Pow S'"
      using closed_mdpD[OF CL US] by blast

    moreover from FIN have "finite (Pow S')"
      by blast

    ultimately show ?thesis
      by (simp add: finite_subset)

  qed

definition "strongly_connected S' K' \<equiv> (S' \<times> S') \<subseteq> (mdp_def.Et_\<alpha> S' K')\<^sup>*"

locale mdp = mdp_def S K for S and K :: "'v mdp_K" +  
  (*assumes non_empty_branch[simp, intro!]: "u \<in> S \<Longrightarrow> {} \<notin> K u"*)
  assumes finite[simp, intro!]: "finite S"
  assumes K_closed_under_S[simp]: "closed_mdp S K"
begin  

  lemma closed_mdp_succ: "u \<in> S \<Longrightarrow> a \<in> K u \<Longrightarrow> v \<in> a \<Longrightarrow> v \<in> S"
    using K_closed_under_S unfolding closed_mdp_def 
    by blast

  lemma edge_connects_states:
    assumes UVE: "(u,v) \<in> Et_\<alpha>" 
    shows "u \<in> S" and "v \<in> S"
  using UVE unfolding Et_\<alpha>_def
  using closed_mdp_succ 
  by blast+

  lemma Et_\<alpha>_subset_states: "Et_\<alpha> \<subseteq> S \<times> S"
    using edge_connects_states 
    by auto

  lemma Et_\<alpha>_subset_states': "Et_\<alpha>\<^sup>* \<subseteq> (S \<times> S)\<^sup>="
    by (metis Et_\<alpha>_subset_states mem_Sigma_iff rtrancl_mono trans_def trans_rtrancl_eq_reflcl)

  lemma finite_edges: "finite Et_\<alpha>"
    using Et_\<alpha>_subset_states
    by (simp add: finite_subset)

  lemmas finite_actions = closedfin_finite_actions[OF K_closed_under_S finite]

  lemmas finite_K = closedfin_finite_K[OF K_closed_under_S finite]

  lemma finite_reach: "u \<in> S \<Longrightarrow> finite (Et_\<alpha>\<^sup>* `` {u})"
    by (simp add: finite_edges)

  lemma reach_in_S: "u \<in> S \<Longrightarrow> Et_\<alpha>\<^sup>* `` {u} \<subseteq> S"
    by (metis Image_singleton_iff edge_connects_states(2) rtrancl.cases subsetI)

end


section \<open>Sub MDPs\<close>

text \<open>A sub MDP preserves the MDP structure of a part of another MDP. I.e. states and transitions
  may be omitted, but if a transition is available in a sub MDP, then exactly all of its branches
  must be available as well.
  We give several similar transitions:
  \<open>eq_mdp\<close> The two MDPs have the same MDP structure (up to (de)duplication of the transitions)
  \<open>not_eq_mdp\<close> The two MDPs either have a different state space or different transitions
  \<open>sub_mdp_of\<close> The structure of the LHS MDP is also a part of the RHS MDP
  \<open>psub_mdp_of\<close> The proper sub MDP
\<close>


definition eq_mdp :: "'a set \<Rightarrow> 'a mdp_K \<Rightarrow> 'a set \<Rightarrow> 'a mdp_K \<Rightarrow> bool" where 
  "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<equiv> S\<^sub>1 = S\<^sub>2 \<and> (\<forall> u \<in> S\<^sub>1 \<inter> S\<^sub>2. K\<^sub>1 u = K\<^sub>2 u)"

definition not_eq_mdp :: "'a set \<Rightarrow> 'a mdp_K \<Rightarrow> 'a set \<Rightarrow> 'a mdp_K \<Rightarrow> bool" where 
  "not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<equiv> S\<^sub>1 \<noteq> S\<^sub>2 \<or> (\<exists> u \<in> S\<^sub>1 \<union> S\<^sub>2. K\<^sub>1 u \<noteq> K\<^sub>2 u)"

lemma eq_mdp_equiv: 
  "eq_mdp S K S K"
  "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<longleftrightarrow> eq_mdp S\<^sub>2 K\<^sub>2 S\<^sub>1 K\<^sub>1"
  "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2  \<Longrightarrow> eq_mdp S\<^sub>2 K\<^sub>2 S\<^sub>3 K\<^sub>3 \<Longrightarrow> eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>3 K\<^sub>3"
  "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2  \<Longrightarrow> eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>3 K\<^sub>3 \<Longrightarrow> eq_mdp S\<^sub>2 K\<^sub>2 S\<^sub>3 K\<^sub>3"
  "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>3 K\<^sub>3  \<Longrightarrow> eq_mdp S\<^sub>2 K\<^sub>2 S\<^sub>3 K\<^sub>3 \<Longrightarrow> eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding eq_mdp_def by auto

lemma not_eq_mdp_inequiv: 
  "not_eq_mdp S K S K \<Longrightarrow> False"
  "not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<longleftrightarrow> not_eq_mdp S\<^sub>2 K\<^sub>2 S\<^sub>1 K\<^sub>1"
  unfolding not_eq_mdp_def by metis+

lemma not_eq_mdpI1: "S\<^sub>1 \<noteq> S\<^sub>2 \<Longrightarrow> not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding not_eq_mdp_def by blast

lemma not_eq_mdpI2: "u \<in> S\<^sub>1 \<Longrightarrow> K\<^sub>1 u \<noteq> K\<^sub>2 u \<Longrightarrow> not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding not_eq_mdp_def by blast

lemma eq_mdpD: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> S\<^sub>1 = S\<^sub>2 \<and> (\<forall> u \<in> S\<^sub>1 \<inter> S\<^sub>2. K\<^sub>1 u = K\<^sub>2 u)"
  unfolding eq_mdp_def by blast

lemma eq_mdpD': "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> (u \<in> S\<^sub>1 \<and> a \<in> K\<^sub>1 u \<longleftrightarrow> u \<in> S\<^sub>2 \<and> a \<in> K\<^sub>2 u)"
  unfolding eq_mdp_def by auto

lemma eq_mdpI: "S\<^sub>1 = S\<^sub>2 \<Longrightarrow> (\<forall>u \<in> S\<^sub>1. K\<^sub>1 u = K\<^sub>2 u) \<Longrightarrow> eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding eq_mdp_def by blast

lemma eq_mdpE: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> (S\<^sub>1 = S\<^sub>2 \<Longrightarrow> (\<forall>u \<in> S\<^sub>2. K\<^sub>1 u = K\<^sub>2 u) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding eq_mdp_def by blast

lemma eq_mdpD1: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> S\<^sub>1 = S\<^sub>2"
  unfolding eq_mdp_def by blast

lemma eq_mdpD2: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> (\<forall> u \<in> S\<^sub>1 \<inter> S\<^sub>2. K\<^sub>1 u = K\<^sub>2 u)"
  unfolding eq_mdp_def by blast

lemma eq_eq_mdp[simp]: "S\<^sub>1 = S\<^sub>2 \<Longrightarrow> K\<^sub>1 = K\<^sub>2 \<Longrightarrow> eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding eq_mdp_def by blast

lemma eq_mdp_alt: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<longleftrightarrow> S\<^sub>1 = S\<^sub>2 \<and> (\<forall>u \<in> S\<^sub>1. (\<forall>a. a \<in> K\<^sub>1 u \<longleftrightarrow> a \<in> K\<^sub>2 u))"
  unfolding eq_mdp_def by auto 

lemma not_not_eq_mdp[simp]: "(\<not>not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2) = eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding not_eq_mdp_def eq_mdp_def by blast

lemma not_eq_mdp[simp]: "(\<not>eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2) = not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding not_eq_mdp_def eq_mdp_def by blast

lemma eq_not_eq_mdp_contr [simp, elim!]: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> False"
  unfolding eq_mdp_def not_eq_mdp_def by blast

lemma eq_mdp_cases [case_names eq neq]: "(eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> P) \<Longrightarrow> (not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding eq_mdp_def not_eq_mdp_def by blast

lemma eq_mdp_closed_mdp: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> closed_mdp S\<^sub>1 K\<^sub>1 \<Longrightarrow> closed_mdp S\<^sub>2 K\<^sub>2"
  unfolding eq_mdp_def closed_mdp_def by auto

lemma eq_mdp_Et_\<alpha>_eq: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> mdp_def.Et_\<alpha> S\<^sub>1 K\<^sub>1 = mdp_def.Et_\<alpha> S\<^sub>2 K\<^sub>2"
  unfolding eq_mdp_def mdp_def.Et_\<alpha>_def by blast

definition sub_mdp_of :: "'a set \<Rightarrow> 'a mdp_K \<Rightarrow> 'a set \<Rightarrow> 'a mdp_K \<Rightarrow> bool" where 
  "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<equiv> S\<^sub>1 \<subseteq> S\<^sub>2 \<and> (\<forall>u \<in> S\<^sub>1. K\<^sub>1 u \<subseteq> K\<^sub>2 u)"


lemma sub_mdp_of_order:
  "sub_mdp_of S K S K"
  "sub_mdp_of S K S' K' \<Longrightarrow> sub_mdp_of S' K' S K \<Longrightarrow> eq_mdp S K S' K'"
  "sub_mdp_of S K S' K' \<Longrightarrow> sub_mdp_of S' K' S'' K'' \<Longrightarrow> sub_mdp_of S K S'' K''"
  unfolding sub_mdp_of_def eq_mdp_def
  apply(cases S K S' K' rule: eq_mdp_cases) (* TODO, Just a reminder *)
  apply blast+
  done

lemmas [simp] = sub_mdp_of_order(1)

lemma empty_sub_mdp_of: "sub_mdp_of {} K' S K"
  unfolding sub_mdp_of_def
  by blast

lemma sub_mdp_ofI: "S \<subseteq> S' \<Longrightarrow> (\<forall>x\<in>S. K x \<subseteq> K' x) \<Longrightarrow> sub_mdp_of S K S' K'"
  unfolding sub_mdp_of_def by presburger

lemma sub_mdp_ofD: "sub_mdp_of S K S' K' \<Longrightarrow> S \<subseteq> S' \<and> (\<forall>x\<in>S. K x \<subseteq> K' x)" 
  unfolding sub_mdp_of_def by presburger

lemma sub_mdp_ofD1: "sub_mdp_of S K S' K' \<Longrightarrow> S \<subseteq> S'" 
  unfolding sub_mdp_of_def by presburger

lemma sub_mdp_ofD2: "sub_mdp_of S K S' K' \<Longrightarrow> (\<forall>x\<in>S. K x \<subseteq> K' x)" 
  unfolding sub_mdp_of_def by presburger

lemma eq_mdp_impl_sub_mdp: "eq_mdp S K S' K' \<Longrightarrow> sub_mdp_of S K S' K'"
  unfolding eq_mdp_def sub_mdp_of_def
  by fast

lemma sub_mdp_simp1[simp,intro]: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> sub_mdp_of S\<^sub>3 K\<^sub>3 S\<^sub>1 K\<^sub>1 \<Longrightarrow> sub_mdp_of S\<^sub>3 K\<^sub>3 S\<^sub>2 K\<^sub>2"
  unfolding eq_mdp_def sub_mdp_of_def 
  by fast

lemma sub_mdp_simp2[simp,intro]: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>3 K\<^sub>3 \<Longrightarrow> sub_mdp_of S\<^sub>2 K\<^sub>2 S\<^sub>3 K\<^sub>3"
  unfolding eq_mdp_def sub_mdp_of_def 
  by fast

lemma sub_mdp_simp3: "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>3 K\<^sub>3 \<Longrightarrow> sub_mdp_of S\<^sub>3 K\<^sub>3 S\<^sub>2 K\<^sub>2"
  unfolding sub_mdp_of_def eq_mdp_def by blast

lemma sub_mdp_simp4: "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> eq_mdp S\<^sub>2 K\<^sub>2 S\<^sub>3 K\<^sub>3 \<Longrightarrow> sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>3 K\<^sub>3"
  unfolding sub_mdp_of_def eq_mdp_def by blast

lemma sub_mdp_of_insert_transition: "sub_mdp_of S' K' S K \<Longrightarrow> a \<in> K u \<Longrightarrow> sub_mdp_of S' (K'(u := insert a (K' u))) S K"
  unfolding sub_mdp_of_def  by auto

lemma sub_mdp_of_self_insert_transition: "sub_mdp_of S' K' S' (K'(u := insert a (K' u)))"
  unfolding sub_mdp_of_def 
  by fastforce

lemma sub_mdp_of_sub_Et_\<alpha>: "sub_mdp_of S' K' S K \<Longrightarrow> mdp_def.Et_\<alpha> S' K' \<subseteq> mdp_def.Et_\<alpha> S K"
  unfolding sub_mdp_of_def mdp_def.Et_\<alpha>_def by auto

lemma sub_mdp_sub_scc:
  assumes SUB: "sub_mdp_of S' K' S K"
  and SCC': "is_scc (mdp_def.Et_\<alpha> S' K') scc'"
  obtains scc where "scc' \<subseteq> scc" and "is_scc (mdp_def.Et_\<alpha> S K) scc"
proof -
  have A: "scc'\<times>scc' \<subseteq> (mdp_def.Et_\<alpha> S K)\<^sup>*" 
    using subset_trans[OF scc_strongly_connected[OF SCC'] sub_mdp_of_sub_Et_\<alpha>[OF SUB, THEN rtrancl_mono]] .
  from SCC' obtain u where U1: "u \<in> scc'" 
    by fastforce
  then obtain scc where SCC: "is_scc (mdp_def.Et_\<alpha> S K) scc" and U2: "u \<in> scc"
    by (meson is_scc_ex)
  moreover have "scc' \<subseteq> scc" using sc_sub_scc[OF U2 U1 A SCC] .
  ultimately show ?thesis using that by blast
qed

definition psub_mdp_of :: "'a set \<Rightarrow> 'a mdp_K \<Rightarrow> 'a set \<Rightarrow> 'a mdp_K \<Rightarrow> bool" where 
  "psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<equiv> sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<and> not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"

lemma psub_mdp_ofI: "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding psub_mdp_of_def by presburger

lemma psub_mdp_ofD: "psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<and> not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding psub_mdp_of_def by presburger

lemma psub_mdp_of_state_cases: "psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> (\<And>u. u \<in> S\<^sub>2 \<Longrightarrow> u \<notin> S\<^sub>1 \<Longrightarrow> P) \<Longrightarrow> (\<And>u a. u \<in> S\<^sub>1 \<Longrightarrow> a \<in> K\<^sub>2 u \<Longrightarrow> a \<notin> K\<^sub>1 u \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding psub_mdp_of_def sub_mdp_of_def not_eq_mdp_def by blast

lemma sub_mdp_of_strict_order: 
  "\<not>psub_mdp_of S K S K"
  "psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> \<not>psub_mdp_of S\<^sub>2 K\<^sub>2 S\<^sub>1 K\<^sub>1"
  "psub_mdp_of S K S' K' \<Longrightarrow> psub_mdp_of S' K' S'' K'' \<Longrightarrow> psub_mdp_of S K S'' K''"
  unfolding psub_mdp_of_def not_eq_mdp_def sub_mdp_of_def
  by blast+

lemma psub_mdp_of_alt: "psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 
    = (sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<and> ((S\<^sub>1 \<subset> S\<^sub>2) \<or> (S\<^sub>1 = S\<^sub>2 \<and> (\<exists>u \<in> S\<^sub>2. K\<^sub>1 u \<subset> K\<^sub>2 u))))"
  unfolding psub_mdp_of_def sub_mdp_of_def not_eq_mdp_def by auto

lemma sub_mdp_not_psub_eq:"sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> \<not>psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding sub_mdp_of_def psub_mdp_of_def
  by simp

lemma psub_mdp_simp1[simp,intro]: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> psub_mdp_of S\<^sub>3 K\<^sub>3 S\<^sub>1 K\<^sub>1 \<Longrightarrow> psub_mdp_of S\<^sub>3 K\<^sub>3 S\<^sub>2 K\<^sub>2"
  unfolding eq_mdp_def psub_mdp_of_def sub_mdp_of_def not_eq_mdp_def
  by blast

lemma psub_mdp_simp2[simp,intro]: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>3 K\<^sub>3 \<Longrightarrow> psub_mdp_of S\<^sub>2 K\<^sub>2 S\<^sub>3 K\<^sub>3"
  unfolding eq_mdp_def psub_mdp_of_def sub_mdp_of_def not_eq_mdp_def
  by blast

lemma psub_mdp_of_subD: "psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding psub_mdp_of_def by simp

lemma psub_mdp_of_neqD: "psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> not_eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding psub_mdp_of_def by simp

lemma psub_mdp_of_non_empty: "psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> S\<^sub>2 \<noteq> {}"
  unfolding psub_mdp_of_def sub_mdp_of_def not_eq_mdp_def 
  by blast

lemma psub_states_psub_mdp_of: "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> S\<^sub>1 \<subset> S\<^sub>2 \<Longrightarrow> psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding  psub_mdp_of_def by (auto simp: eq_mdp_def)

lemma 
  assumes S12: "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  and SA2: "sub_mdp_of S\<^sub>a K\<^sub>a S\<^sub>2 K\<^sub>2"
  and NSA1: "\<not>sub_mdp_of S\<^sub>a K\<^sub>a S\<^sub>1 K\<^sub>1"
  shows "psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
proof(rule ccontr)
  assume "\<not> psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  with S12 have "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2" 
    unfolding psub_mdp_of_def by fastforce
  with SA2 have "sub_mdp_of S\<^sub>a K\<^sub>a S\<^sub>1 K\<^sub>1" 
    using sub_mdp_simp1 eq_mdp_equiv(2) by blast
  with NSA1 show False by presburger
qed


subsection \<open>Well-founded relation over MDPs\<close>

text \<open>
  For termination, we prove that the remaining MDP is a proper sub MDP of the MDP of the previous
  iteration. This is captured by a well-founded relation

  NOTE: We are aware that this is over-engineered because it is guaranteed that every iteration
    removes at least one state. So we could have used \<open>finite_psubset\<close> over the set of states to
    prove termination as well.
\<close>

definition "psub_mdp_of_rel = {((S\<^sub>1,K\<^sub>1),(S\<^sub>2,K\<^sub>2)) | S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2. closed_mdp S\<^sub>2 K\<^sub>2 \<and> finite S\<^sub>2 \<and> psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2}"

lemma psub_mdp_of_rel_mem: "((S\<^sub>1,K\<^sub>1),(S\<^sub>2,K\<^sub>2)) \<in> psub_mdp_of_rel \<longleftrightarrow> closed_mdp S\<^sub>2 K\<^sub>2 \<and> finite S\<^sub>2 \<and> psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  unfolding psub_mdp_of_rel_def by auto

lemma Id_not_in_psub_mdp_of_rel[simp]: "(m,m) \<notin> psub_mdp_of_rel"
  unfolding psub_mdp_of_rel_def
  by(auto simp: sub_mdp_of_strict_order(1))

definition "sub_transitions_rel S' = {(K\<^sub>1,K\<^sub>2)| K\<^sub>1 K\<^sub>2. closed_mdp S' K\<^sub>2 \<and> finite S' \<and> S' \<noteq> {} \<and> (\<forall>x \<in> S'. K\<^sub>1 x \<subseteq> K\<^sub>2 x) \<and> (\<exists>x \<in> S'. K\<^sub>1 x \<subset> K\<^sub>2 x)}"

definition "num_trans S' K' = (\<Sum>u \<in> S'. (card (K' u)))"


lemma sub_transitions_rel_num_trans: "sub_transitions_rel S' \<subseteq> measure (num_trans S')"
proof safe
  fix K\<^sub>1 K\<^sub>2
  assume "(K\<^sub>1,K\<^sub>2) \<in> sub_transitions_rel S'"
  hence FINS: "finite S'" and CL: "closed_mdp S' K\<^sub>2" and NEMP: "S' \<noteq> {}" and ALS: "\<forall>x\<in>S'. K\<^sub>1 x \<subseteq> K\<^sub>2 x" and EXS: "\<exists>x\<in>S'. K\<^sub>1 x \<subset> K\<^sub>2 x" 
    unfolding sub_transitions_rel_def by auto
  
  have "(\<Sum>u\<in>S'. card (K\<^sub>1 u)) < (\<Sum>u\<in>S'. card (K\<^sub>2 u))"
  proof -

    obtain u where UMEM: "u \<in> S'" and PS: "(K\<^sub>1 u) \<subset> (K\<^sub>2 u)"
      using EXS by blast

    show ?thesis 
      apply(rule sum_strict_mono_ex1)
      subgoal using FINS .
      subgoal using ALS 
        by (auto intro!: card_mono closedfin_finite_K[OF CL FINS])
      subgoal apply(rule bexI[where ?x=u])
        apply(rule psubset_card_mono)
        using PS by (auto simp: UMEM intro!: card_mono closedfin_finite_K[OF CL FINS])
      done
  qed

  thus "(K\<^sub>1,K\<^sub>2) \<in> measure (num_trans S')"
    by(simp add: num_trans_def)
qed


lemma wf_finite_sub_transitions_rel: "wf (sub_transitions_rel S')" 
  apply(cases" S' = {}")
  subgoal 
    unfolding sub_transitions_rel_def by simp
  subgoal
    apply(cases "finite S'")
    subgoal
      apply(rule wf_subset[where ?r="measure (num_trans S')"])
      apply simp
      using sub_transitions_rel_num_trans by blast
    subgoal
      unfolding sub_transitions_rel_def by simp
    done
  done



lemma wf_psubset_dlex_sub_trans: "wf (finite_psubset <*dlex*> sub_transitions_rel)"
  apply(rule wf_dep_lex_prod)
  apply simp
  using wf_finite_sub_transitions_rel 
  by blast
    

lemma psub_mdp_of_rel_sub_dlex: "psub_mdp_of_rel \<subseteq> finite_psubset <*dlex*> sub_transitions_rel"
  unfolding psub_mdp_of_rel_def psub_mdp_of_def sub_mdp_of_def not_eq_mdp_def finite_psubset_def sub_transitions_rel_def 
  apply clarsimp
  by blast

lemma wf_psub_mdp_of_rel[simp]: "wf psub_mdp_of_rel"
  apply(rule wf_subset)
  using wf_psubset_dlex_sub_trans apply assumption
  using psub_mdp_of_rel_sub_dlex .

context mdp_def
begin

  text \<open>
    As a tool for our BSCC lemmas, we define \<open>make_sub_mdp\<close> which constructs a sub MDP consisting
    of the provided states. Note that transitions may leave the provided state space.
  \<close>

  definition "make_sub_mdp S' = (\<lambda> u. if u \<in> S' then K u else {})"

  lemma make_sub_mdp_S[simp]: "u \<in> S \<Longrightarrow> make_sub_mdp S u = K u"
    unfolding make_sub_mdp_def 
    by(clarsimp simp: closed_mdp_def)

  lemma disj_make_sub_mdp_states: "S' \<inter> S = {} \<Longrightarrow> u \<in> S \<Longrightarrow> make_sub_mdp S' u = {}"
    unfolding make_sub_mdp_def
    by auto

  lemma disj_make_sub_mdp_edges: "S' \<inter> S = {} \<Longrightarrow> mdp_def.Et_\<alpha> S (make_sub_mdp S') = {}"
    unfolding mdp_def.Et_\<alpha>_def make_sub_mdp_def
    by (simp add:  disjoint_iff)

  lemma disj_make_disj_mdp_edges: "S' \<inter> S = {} \<Longrightarrow> mdp_def.Et_\<alpha> S' (make_sub_mdp S') \<inter> Et_\<alpha> = {}"
    unfolding mdp_def.Et_\<alpha>_def make_sub_mdp_def
    by auto

  lemma make_sub_mdp_cases: "(make_sub_mdp S' u = K u \<Longrightarrow> P) \<Longrightarrow> (make_sub_mdp S' u = {} \<Longrightarrow> P) \<Longrightarrow> P"
    unfolding make_sub_mdp_def 
    by presburger

  lemma closed_mdp_eq_make_sub_mdp: "closed_mdp S' K \<Longrightarrow> eq_mdp S' K S' (make_sub_mdp S')"
    unfolding eq_mdp_def make_sub_mdp_def  by auto

  definition "sub_mdp S' K' \<equiv> sub_mdp_of S' K' S K"

  lemma self_sub_mdp [simp,intro!]: "sub_mdp S K"
    unfolding sub_mdp_def
    using sub_mdp_of_order(1)
    by blast
    
  lemma sub_mdp_sub_mdp_of [intro]:"sub_mdp S' K' \<Longrightarrow> sub_mdp_of S' K' S K"
    unfolding sub_mdp_def by assumption

  lemma make_sub_mdp_sub_mdp[simp]: "S' \<subseteq> S \<Longrightarrow> sub_mdp S' (make_sub_mdp S')"
    unfolding sub_mdp_def sub_mdp_of_def make_sub_mdp_def 
    by simp

  lemma sub_mdp_empty [simp,intro!]: "sub_mdp {} K"
    unfolding sub_mdp_def sub_mdp_of_def by blast

  lemma sub_mdp_eq_mdp: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> sub_mdp S\<^sub>1 K\<^sub>1 \<Longrightarrow> sub_mdp S\<^sub>2 K\<^sub>2"
    unfolding sub_mdp_def 
    by blast

  lemma sub_mdp_subset_S: "sub_mdp S' K' \<Longrightarrow> S' \<subseteq> S"
    unfolding sub_mdp_def sub_mdp_of_def 
    by blast

  lemma sub_mdp_subset_K: "sub_mdp S' K' \<Longrightarrow> (\<forall>x \<in> S'. K' x \<subseteq> K x)"
    unfolding sub_mdp_def sub_mdp_of_def 
    by blast

  lemma sub_mdp_subset_SK: "sub_mdp S' K' \<Longrightarrow> S' \<subseteq> S \<and> (\<forall>x \<in> S'. K' x \<subseteq> K x)"
    unfolding sub_mdp_def sub_mdp_of_def 
    by blast

  lemma sub_mdp_actions_in_sup: "sub_mdp S' K' \<Longrightarrow> u \<in> S' \<Longrightarrow> a \<in> K' u \<Longrightarrow> a \<in> K u"
    unfolding sub_mdp_def sub_mdp_of_def
    by fast

  lemma sub_mdp_sub_Et_\<alpha>: "sub_mdp S' K' \<Longrightarrow> mdp_def.Et_\<alpha> S' K' \<subseteq> Et_\<alpha>"
    unfolding sub_mdp_def sub_mdp_of_def mdp_def.Et_\<alpha>_def by auto

  lemma sub_mdp_order:
    "sub_mdp S K"
    "sub_mdp S' K' \<Longrightarrow> sub_mdp_of S'' K'' S' K' \<Longrightarrow> sub_mdp S'' K''"
    unfolding sub_mdp_def
    using sub_mdp_of_order by auto

  lemma make_sub_mdp_K[simp]: "u \<in> S' \<Longrightarrow> make_sub_mdp S' u = K u"
    unfolding make_sub_mdp_def by simp

  lemma make_sub_mdp_empty[simp]: "u \<notin> S' \<Longrightarrow> make_sub_mdp S' u = {}"
    unfolding make_sub_mdp_def by simp
end

lemma sub_mdp_of_make_sub_mdp: "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> sub_mdp_of S\<^sub>1 (mdp_def.make_sub_mdp K\<^sub>1 S\<^sub>1) S\<^sub>2 (mdp_def.make_sub_mdp K\<^sub>2 S\<^sub>2)"
  unfolding sub_mdp_of_def mdp_def.make_sub_mdp_def  apply clarsimp by blast

context mdp
begin



  lemma sub_mdp_finite: "sub_mdp S' K' \<Longrightarrow> finite S'"
    by (meson finite_subset local.finite sub_mdp_subset_S)


end


section \<open>Union MDP\<close>

text \<open>
  A union MDP of a set of MDPs is the union of all states and for each of those states the
  union of all transitions (up to (de)duplications).\<close>

definition union_mdp_states where "union_mdp_states M = (\<Union>(S,K) \<in> M. S)"
definition union_mdp_K_set where "union_mdp_K_set M = {K. \<forall> u \<in> union_mdp_states M. K u = (\<Union>K' \<in> {K'| S' K'. (S',K') \<in> M \<and> u \<in> S'}. K' u)}"


lemma(in mdp_def) ex_union_sub_mdp_K_set:
  assumes SUB: "\<forall>(S,K) \<in> M. sub_mdp S K"
  shows "union_mdp_K_set M \<noteq> {}"
proof -

  define K\<^sub>c where "K\<^sub>c = (\<lambda> u. \<Union>K' \<in> {K'| S' K'. (S',K') \<in> M \<and> u \<in> S'}. K' u)"
  hence "K\<^sub>c u \<subseteq> K u" for u
    using assms sub_mdp_actions_in_sup by fastforce

  hence "K\<^sub>c \<in> union_mdp_K_set M"
    unfolding union_mdp_K_set_def
    using K\<^sub>c_def by blast

  thus ?thesis by blast
qed


lemma K_set_union_mdp_K_set: "K \<in> union_mdp_K_set M \<Longrightarrow> u \<in> union_mdp_states M \<Longrightarrow> K u = (\<Union>K' \<in> {K'| S' K'. (S',K') \<in> M \<and> u \<in> S'}. K' u)"
  unfolding union_mdp_K_set_def
  by auto 

lemma mem_sub_mdp_of_union: "K\<^sub>m \<in> union_mdp_K_set M \<Longrightarrow> (S',K') \<in> M \<Longrightarrow> sub_mdp_of S' K' (union_mdp_states M) K\<^sub>m"
  unfolding sub_mdp_of_def union_mdp_K_set_def union_mdp_states_def by auto

lemma union_mdp_ex_sub:
  assumes KM: "K\<^sub>m \<in> union_mdp_K_set M"
  assumes UM: "u \<in> union_mdp_states M"
  assumes AKU: "a \<in> K\<^sub>m u"
  obtains S' K' where "(S',K') \<in> M" and "a \<in> K' u" and "u \<in> S'" and "sub_mdp_of S' K' (union_mdp_states M) K\<^sub>m"
proof -
  obtain S' K' where A: "(S',K') \<in> M" and B: "a \<in> K' u" and C: "u \<in> S'"
    using KM UM AKU unfolding union_mdp_K_set_def by blast
  hence "sub_mdp_of S' K' (union_mdp_states M) K\<^sub>m"
    using mem_sub_mdp_of_union[OF KM] by blast
  thus ?thesis using that A B C by blast
qed

lemma union_mdp_branches_eq:
  shows "K\<^sub>m \<in> union_mdp_K_set M \<Longrightarrow> u \<in> union_mdp_states M \<Longrightarrow> a \<in> K\<^sub>m u \<longleftrightarrow> (\<exists> S' K'. (S',K') \<in> M \<and> a \<in> K' u \<and> u \<in> S' \<and> sub_mdp_of S' K' (union_mdp_states M) K\<^sub>m)"
  apply safe
  subgoal
    using union_mdp_ex_sub by meson
  subgoal
    using sub_mdp_ofD2 by blast
  done

lemma union_closed:
  assumes CL: "\<forall>(S,K) \<in> M. closed_mdp S K"
  assumes KM: "K\<^sub>m \<in> union_mdp_K_set M"
  shows
    "closed_mdp (union_mdp_states M) K\<^sub>m"
unfolding closed_mdp_def union_mdp_states_def
proof(safe)
  fix u S' K' v a
  assume SKM: "(S',K') \<in> M" and US': "u \<in> S'" and VA: "v \<in> a" and AMEM: "a \<in> (K\<^sub>m u)"
  hence "u \<in> union_mdp_states M"
    using KM mem_sub_mdp_of_union sub_mdp_ofD1 by blast
  with AMEM US' obtain S'' K'' where MM: "(S'',K'') \<in> M" and "u \<in> S''" and AKU: "a \<in> K'' u" 
    unfolding union_mdp_K_set_def 
    using mem_sub_mdp_of_union[OF KM SKM] union_mdp_ex_sub[OF KM] by metis
  with CL VA AKU have "v \<in> S''" unfolding closed_mdp_def by blast
  with MM show "v \<in> (\<Union>(S, K)\<in>M. S)"
    by blast
qed



lemma union_mdp:
  assumes MDP: "\<forall>(S,K) \<in> M. mdp S K" 
      and KM: "K\<^sub>m \<in> union_mdp_K_set M"
      and FIN: "finite M"
      and NE: "M \<noteq> {}"
  shows
    "mdp (union_mdp_states M) K\<^sub>m"
proof (unfold_locales)
  show "finite (union_mdp_states M)"
    unfolding union_mdp_states_def 
    apply(rule finite_UN_I)
    using FIN 
    apply simp
    by (metis MDP case_prod_conv mdp.finite surj_pair)
next
  from MDP have "\<forall>(S, K)\<in>  M. closed_mdp S K" unfolding mdp_def by blast
  thus "closed_mdp (union_mdp_states M) K\<^sub>m"
    using union_closed KM unfolding union_mdp_states_def by blast
qed

lemma union_mdp_edges [simp]:
  assumes KM: "K\<^sub>m \<in> union_mdp_K_set M"
  shows "mdp_def.Et_\<alpha> (union_mdp_states M) K\<^sub>m = (\<Union>(S,K)\<in> M. mdp_def.Et_\<alpha> S K)"
proof safe
  fix u v
  assume "(u,v) \<in> mdp_def.Et_\<alpha> (union_mdp_states M) K\<^sub>m"
  then obtain S' K' where "(S',K') \<in> M" and "(u,v) \<in> mdp_def.Et_\<alpha> S' K'" 
    unfolding mdp_def.Et_\<alpha>_def using KM union_mdp_branches_eq by fast
  thus "(u,v) \<in> (\<Union>(S', K')\<in> M. mdp_def.Et_\<alpha> S' K')" by blast
next
  fix u v S' K'
  assume "(S',K') \<in> M" and A: "(u,v) \<in> mdp_def.Et_\<alpha> S' K'"
  hence "sub_mdp_of S' K' (union_mdp_states M) K\<^sub>m" 
    using mem_sub_mdp_of_union[OF KM] by presburger
  with A show "(u,v) \<in> mdp_def.Et_\<alpha> (union_mdp_states M) K\<^sub>m"
    using sub_mdp_of_sub_Et_\<alpha> by blast
qed

lemma union_sc:
  assumes SC: "\<forall>(S,K) \<in> M. S \<times> S \<subseteq> (mdp_def.Et_\<alpha> S K)\<^sup>*"
  assumes OV: "\<forall>(S,K) \<in> M. v \<in> S"
  assumes KM: "K\<^sub>m \<in> union_mdp_K_set M"
  shows "(union_mdp_states M) \<times> (union_mdp_states M) \<subseteq> (mdp_def.Et_\<alpha> (union_mdp_states M) K\<^sub>m)\<^sup>*"
proof safe
  fix u w 
  assume "u \<in> union_mdp_states M" and "w \<in> union_mdp_states M"
  then obtain S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 where M1: "(S\<^sub>1, K\<^sub>1) \<in> M" "u \<in> S\<^sub>1" and M2: "(S\<^sub>2, K\<^sub>2) \<in> M" "w \<in> S\<^sub>2"
    unfolding union_mdp_states_def by blast
  from M1 SC OV have "(u,v) \<in> (mdp_def.Et_\<alpha> S\<^sub>1 K\<^sub>1)\<^sup>*" by fast
  hence A: "(u,v) \<in> (\<Union>(S, K)\<in> M. mdp_def.Et_\<alpha> S K)\<^sup>*" 
    using union_trancl_subset_trancl_union M1(1)
    by force

  from M2 SC OV have "(v,w) \<in> (mdp_def.Et_\<alpha> S\<^sub>2 K\<^sub>2)\<^sup>*" by fast
  hence B: "(v,w) \<in> (\<Union>(S, K)\<in> M. mdp_def.Et_\<alpha> S K)\<^sup>*" 
    using union_trancl_subset_trancl_union M2(1)
    by force
  
  from A B KM show "(u,w) \<in> (mdp_def.Et_\<alpha> (union_mdp_states M) K\<^sub>m)\<^sup>*"
    by force
qed

lemma union_sub_mdp_of:
  assumes SUB:"\<forall>(S',K') \<in> M. sub_mdp_of S' K' S K"
  assumes KM: "K\<^sub>m \<in> union_mdp_K_set M"
  shows "sub_mdp_of (union_mdp_states M) K\<^sub>m S K"
proof(rule sub_mdp_ofI; safe)
  fix u
  assume "u \<in> union_mdp_states M"
  thus "u \<in> S"
    unfolding union_mdp_states_def using SUB sub_mdp_ofD1
    by fast
next
  fix u a
  assume "u \<in> union_mdp_states M" and A:"a \<in> K\<^sub>m u"
  then obtain S' K' where "(S', K') \<in> M" "a \<in> K' u"  "u \<in> S'" "sub_mdp_of S' K' (union_mdp_states M) K\<^sub>m"
    using union_mdp_ex_sub[OF KM] by blast
  thus "a \<in> K u"
    using SUB sub_mdp_ofD by fastforce
qed

  


lemma union_mdp_states_singleton: "union_mdp_states {(S',K')} = S'"
  unfolding union_mdp_states_def by force

lemma union_mdp_K_set_singleton: "u \<in> S' \<Longrightarrow> K\<^sub>m \<in> union_mdp_K_set {(S',K')} \<Longrightarrow> K\<^sub>m u = K' u"
  unfolding union_mdp_K_set_def union_mdp_states_def by simp

lemma eq_mdp_union_singleton: "K\<^sub>m \<in> union_mdp_K_set {(S',K')} \<Longrightarrow> eq_mdp S' K' (union_mdp_states {(S',K')}) K\<^sub>m"
  unfolding eq_mdp_def union_mdp_K_set_def union_mdp_states_def by simp

subsection \<open>Custom Definitions for the SCC algorithm\<close>

definition "ordered l S K = (\<forall>i j. i < j \<longrightarrow> j < length l \<longrightarrow> l!i \<times> l!j \<inter> (mdp_def.Et_\<alpha> S K)\<^sup>* = {})"

lemma ordered_empty: "ordered [] S K"
  unfolding ordered_def by auto

lemma ordered_single: "ordered [x] S K"
  unfolding ordered_def by auto

lemma ordered_consD1: "ordered (x # xs) S K \<Longrightarrow> ordered xs S K"
  unfolding ordered_def
  by (metis add.right_neutral add_Suc_right less_Suc_eq_le list.size(4) not_less_eq nth_Cons_Suc)

lemma ordered_consD2: "ordered (x # xs) S K \<Longrightarrow> (\<forall>y \<in> set xs. x \<times> y \<inter> (mdp_def.Et_\<alpha> S K)\<^sup>* = {})"
  unfolding ordered_def
  apply clarsimp 
  by (metis Suc_less_eq diff_Suc_Suc diff_zero in_set_conv_nth nth_Cons_0 zero_less_Suc)




lemma ordered_distinct: "{} \<notin> set l \<Longrightarrow> ordered l S K \<Longrightarrow> distinct l"
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  {
    fix u
    assume O: "ordered (a # l) S K"
    and "a \<in> set l"
    and UA: "u \<in> a"

    then obtain i where ADEF: "a = l!i" and IB: "i < length l"
      by (metis in_set_conv_nth)
    
    have "0 < Suc i" by simp
    moreover from IB have "Suc i < Suc (length l)" by blast
    ultimately have CC: "a \<times> l!i \<inter> (mdp_def.Et_\<alpha> S K)\<^sup>* = {}"
      using O unfolding ordered_def by fastforce
    moreover from UA ADEF have "(u,u) \<in> a \<times> l!i \<inter> (mdp_def.Et_\<alpha> S K)\<^sup>*" by blast
    ultimately have False by fast
  } note AUX = this

  from Cons.prems Cons.IH show ?case 
    by (auto intro: AUX dest: ordered_consD1) 
qed


subsection \<open>Scc List\<close>

definition "scc_list C S K \<equiv> distinct C \<and> set C = {scc. is_scc (mdp_def.Et_\<alpha> S K) scc \<and> scc \<subseteq> S}"

lemma scc_list_scc_to_state: "scc_list C S K \<Longrightarrow> x \<in> \<Union> (set C) \<Longrightarrow> x \<in> S"
  unfolding scc_list_def
  by blast

lemma scc_list_state_to_scc: "scc_list C S K \<Longrightarrow> x \<in> S \<Longrightarrow> x \<in> \<Union> (set C)"
  unfolding scc_list_def
  by (metis (no_types, lifting) CollectI Union_iff is_scc_ex mdp_def.scc_in_S)

lemma scc_list_states_eq: "scc_list C S K \<Longrightarrow> S = \<Union> (set C)"
  using scc_list_scc_to_state scc_list_state_to_scc by fast

lemma scc_list_states_index: "scc_list C S K \<Longrightarrow> u \<in> S \<Longrightarrow> \<exists> i < length C. u \<in> C ! i"
  by(auto dest!: scc_list_state_to_scc simp: in_set_conv_nth) 

lemma ordered_list_distinct: "scc_list C S K \<Longrightarrow> distinct C"
  unfolding scc_list_def by simp

lemma scc_listD2: "scc_list C S K \<Longrightarrow> set C = {scc. is_scc (mdp_def.Et_\<alpha> S K) scc \<and> scc \<subseteq> S}"
  unfolding scc_list_def by blast

lemma scc_listD: "scc_list C S K \<Longrightarrow> ordered C S K \<Longrightarrow> 
    set C = {scc. is_scc (mdp_def.Et_\<alpha> S K) scc \<and> scc \<subseteq> S}"
  unfolding scc_list_def by blast

lemma scc_listI: "distinct C \<Longrightarrow> set C = {scc. is_scc (mdp_def.Et_\<alpha> S K) scc \<and> scc \<subseteq> S} \<Longrightarrow> scc_list C S K"
  unfolding scc_list_def by blast

lemma scc_list_mem: "scc_list C S K \<Longrightarrow> x \<in> set C \<longleftrightarrow> is_scc (mdp_def.Et_\<alpha> S K) x \<and> x \<subseteq> S"
  unfolding scc_list_def by blast

lemma scc_list_index: "scc_list C S K \<Longrightarrow> i < length C \<Longrightarrow> is_scc (mdp_def.Et_\<alpha> S K) (C ! i) \<and> C ! i \<subseteq> S"
  apply(drule scc_list_mem)
  apply(drule nth_mem)
  by blast

lemma scc_list_unique_index: "scc_list C S K \<Longrightarrow> i < length C \<Longrightarrow> j < length C \<Longrightarrow> u \<in> C ! i \<Longrightarrow> u \<in> C ! j \<Longrightarrow> i = j"
  apply(frule scc_list_index[of _ _ _ i])
  apply assumption
  apply(frule scc_list_index[of _ _ _ j])
  apply assumption
  by (meson is_scc_unique nth_eq_iff_index_eq ordered_list_distinct)

lemma scc_list_non_empty_mem: "scc_list C S K \<Longrightarrow> X \<in> set C \<Longrightarrow> X \<noteq> {}"
  using scc_list_mem scc_non_empty' by blast

lemma filter_perm_index: "distinct ys \<Longrightarrow> set ys \<subseteq> set xs \<Longrightarrow> i < length ys \<Longrightarrow> \<exists>j. j < length xs \<and> ys ! i = xs ! j"
  apply(induction xs arbitrary: ys rule: rev_induct)
  apply simp
  by (metis in_set_conv_nth subsetD)

lemma scc_list_mec_unique_index: 
  assumes SCC: "scc_list C S K"
  and DV: "distinct V"
  and SETV: "set V \<subseteq> set C"
  and IV: "i < length V"
  and JV: "j < length V"
  and UVI: "u \<in> V ! i"
  and UVJ: "u \<in> V ! j"
  shows "i = j"
  using filter_perm_index[OF DV SETV IV] filter_perm_index[OF DV SETV JV] scc_list_unique_index[OF SCC] UVI UVJ
  by (metis DV IV JV nth_eq_iff_index_eq)


lemma scc_list_unique_C: "scc_list C S K \<Longrightarrow> X \<in> set C \<Longrightarrow> Y \<in> set C \<Longrightarrow> u \<in> X \<Longrightarrow> u \<in> Y \<Longrightarrow> X = Y"
  by (meson is_scc_unique scc_list_mem)

lemma scc_list_unique_V: "scc_list C S K \<Longrightarrow> X \<in> set C \<Longrightarrow> Y \<in> set C \<Longrightarrow> u \<in> X \<Longrightarrow> u \<in> Y \<Longrightarrow> X = Y"
  by (meson is_scc_unique scc_list_mem)

lemma u_in_C_not_in_V:
  assumes SCC: "scc_list C S K"
  and VDEF: "set V = {S' \<in> set C. closed_mdp S' K}"
  and XC: "X \<in> set C"
  and UX: "u \<in> X"
  and XNV: "X \<notin> set V"
  shows "u \<notin> \<Union>(set V)"
proof(rule notI)
  assume CC: "u \<in> \<Union> (set V)"
  then obtain k where UVK: "u \<in> V ! k" and KV: "k < length V"
    using nth_index by fastforce
  then obtain i where EQ: "C ! i = V ! k" and IC: "i < length C"
    by (metis (no_types, lifting) VDEF in_set_conv_nth mem_Collect_eq)
  hence UCI: "u \<in> C ! i" 
    using UVK by blast

  obtain j where "X = C ! j" and JC: "j < length C" and UCJ: "u \<in> C ! j"
    by (metis XC in_set_conv_nth UX)

  hence "i \<noteq> j"
    using XNV EQ KV by fastforce
  thus False using scc_list_unique_index[OF SCC IC JC UCI UCJ]
    by blast
qed


lemma sub_mdp_scc_list_subset:
  assumes O1: "scc_list C\<^sub>1 S\<^sub>1 K\<^sub>1"
  and O2: "scc_list C\<^sub>2 S\<^sub>2 K\<^sub>2"
  and SUB: "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  and IL: "X\<^sub>1 \<in> set C\<^sub>1"
  obtains X\<^sub>2 where "X\<^sub>2 \<in> set C\<^sub>2" and "X\<^sub>1 \<subseteq> X\<^sub>2"
proof -                 

  from IL obtain i where "i < length C\<^sub>1" and X1DEF: "X\<^sub>1 = C\<^sub>1 ! i"
    by (metis in_set_conv_nth)

  with O1 obtain u where UC1: "u \<in> C\<^sub>1 ! i" and "is_scc (mdp_def.Et_\<alpha> S\<^sub>1 K\<^sub>1) (C\<^sub>1 ! i)" and A: "(C\<^sub>1 ! i) \<subseteq> S\<^sub>1" 
    unfolding scc_list_def
    using nth_mem by fastforce
  with SUB obtain scc where B: "(C\<^sub>1 ! i) \<subseteq> scc" and SCC2: "is_scc (mdp_def.Et_\<alpha> S\<^sub>2 K\<^sub>2) scc"
    by (blast intro: sub_mdp_sub_scc)
  moreover have "scc \<subseteq> S\<^sub>2"
    apply(rule mdp_def.scc_in_S)
    using SUB[THEN sub_mdp_ofD1] A UC1 apply blast

    using calculation UC1  apply blast

    using SCC2 by blast
  ultimately have "scc \<in> set C\<^sub>2" 
    using O2 unfolding scc_list_def by blast
  thus ?thesis using that B X1DEF
    by blast
qed

lemma sub_mdp_scc_list_subset_index:
  assumes O1: "scc_list C\<^sub>1 S\<^sub>1 K\<^sub>1"
  and O2: "scc_list C\<^sub>2 S\<^sub>2 K\<^sub>2"
  and SUB: "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
  and IL: "i < length C\<^sub>1"
  obtains j where "j < length C\<^sub>2" and "C\<^sub>1 ! i \<subseteq> C\<^sub>2 ! j"
  using assms sub_mdp_scc_list_subset 
  by (metis in_set_conv_nth)

lemma scc_list_length_C_bound: 
  assumes SCC: "scc_list C S K"
  assumes FIN: "finite (S::'a set)"
  shows "length C \<le> card S"
proof -

  have "card (set C) \<le> card S"
    apply(rule disj_finite_set_of_subsets_card_bound)
    apply (meson SCC scc_list_unique_V pairwise_disjntI)
    using SCC scc_list_mem apply blast
    apply (simp add: FIN)
    using SCC scc_list_non_empty_mem apply blast
    done

  thus ?thesis
    by (metis SCC distinct_card ordered_list_distinct)
qed


definition "K_actions M = (\<lambda> u. set_pmf ` (actions M u))"

lemma K_actions_mem: "a \<in> K_actions M u \<longleftrightarrow> a \<in> set_pmf ` (actions M u)"
  unfolding K_actions_def by(rule refl)

lemma en_Et_\<alpha>: "en M = mdp_def.Et_\<alpha> (states M) (K_actions M)"
  apply safe
  subgoal for u v 
    unfolding mdp_def.Et_\<alpha>_def en_def
    by (force simp: K_actions_mem empty_iff intro!: in_states) 
  subgoal
    unfolding mdp_def.Et_\<alpha>_def en_def 
    by (force simp: K_actions_mem)
  done


lemma le_imp_sub_mdp_of: "\<phi> \<le> \<psi> \<Longrightarrow> sub_mdp_of (states \<phi>) (K_actions \<phi>) (states \<psi>) (K_actions \<psi>)"
  unfolding sub_mdp_of_def le_mdpc_iff by (fastforce simp: K_actions_mem)


definition max_le_mdpc :: "'v mdpc \<Rightarrow> 'v mdpc \<Rightarrow> bool" (infixr "\<le>\<^sub>M" 80) where
  "max_le_mdpc M\<^sub>1 M\<^sub>2 \<equiv> M\<^sub>1 \<le> M\<^sub>2 \<and> (\<forall>u \<in> states M\<^sub>1. \<forall>a \<in> actions M\<^sub>1 u. \<forall>a' \<in> actions M\<^sub>2 u. set_pmf a' = set_pmf a \<longrightarrow> a' \<in> actions M\<^sub>1 u)"

lemma max_le_mdpc_le: "M\<^sub>1 \<le>\<^sub>M M\<^sub>2 \<Longrightarrow> M\<^sub>1 \<le> M\<^sub>2"
  unfolding max_le_mdpc_def by blast

lemma max_le_mdpcI: "M\<^sub>1 \<le> M\<^sub>2 \<Longrightarrow> (\<And> u a a'. u \<in> states M\<^sub>1 \<Longrightarrow> a \<in> actions M\<^sub>1 u \<Longrightarrow> a' \<in> actions M\<^sub>2 u \<Longrightarrow> set_pmf a' = set_pmf a \<Longrightarrow> a' \<in> actions M\<^sub>1 u) \<Longrightarrow> M\<^sub>1 \<le>\<^sub>M M\<^sub>2"
  unfolding max_le_mdpc_def by blast

lemma max_le_mdpcE: "M\<^sub>1 \<le>\<^sub>M M\<^sub>2 \<Longrightarrow> (M\<^sub>1 \<le> M\<^sub>2 \<Longrightarrow> P) \<Longrightarrow> (\<And> u a a'. u \<in> states M\<^sub>1 \<Longrightarrow> a \<in> actions M\<^sub>1 u \<Longrightarrow> a' \<in> actions M\<^sub>2 u \<Longrightarrow> set_pmf a' = set_pmf a \<Longrightarrow> a' \<in> actions M\<^sub>1 u \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding max_le_mdpc_def by blast

lemma max_le_mdpc_trans: "M\<^sub>1 \<le>\<^sub>M M\<^sub>2 \<Longrightarrow> M\<^sub>2 \<le>\<^sub>M M\<^sub>3 \<Longrightarrow> M\<^sub>1 \<le>\<^sub>M M\<^sub>3"
  unfolding max_le_mdpc_def 
  apply clarsimp
  by (meson le_mdpc_iff subset_eq)
  
lemma max_le_mdpc_antisym: "M\<^sub>1 \<le>\<^sub>M M\<^sub>2 \<Longrightarrow> M\<^sub>2 \<le>\<^sub>M M\<^sub>1 \<Longrightarrow> M\<^sub>1 = M\<^sub>2"
  by(auto dest!: max_le_mdpc_le)

lemma le_trans_infer_max_le: "M\<^sub>1 \<le> M\<^sub>2 \<Longrightarrow> M\<^sub>2 \<le> M\<^sub>3 \<Longrightarrow> M\<^sub>1 \<le>\<^sub>M M\<^sub>3 \<Longrightarrow> M\<^sub>1 \<le>\<^sub>M M\<^sub>2"
  unfolding max_le_mdpc_def 
  apply clarsimp 
  by (meson le_mdpc_iff subset_iff)


lemma mec_max_le: "mec M \<phi> \<Longrightarrow> \<phi> \<le>\<^sub>M M"
proof(rule max_le_mdpcI)
  show "mec M \<phi> \<Longrightarrow> \<phi> \<le> M"
    using mec_le .
next
  fix u a a'
  assume MEC: "mec M \<phi>" 
  and US: "u \<in> states \<phi>" 
  and AAP: "a \<in> actions \<phi> u" 
  and A'AM: "a' \<in> actions M u" 
  and EQS: "set_pmf a' = set_pmf a"

  define \<phi>' where "\<phi>' = Abs_mdpc (\<lambda>v. if v \<in> states \<phi> then Some (if u = v then insert a' (actions \<phi> v) else actions \<phi> v) else None)"

  have SDEF: "states \<phi>' = states \<phi>"
    unfolding \<phi>'_def apply transfer by (auto split: if_splits)
  
  have KDEF: "actions \<phi>' v = (if v \<in> states \<phi> \<and> u = v then insert a' (actions \<phi> v) else actions \<phi> v)" for v
    unfolding \<phi>'_def apply transfer by auto

  have EN: "en \<phi>' = en \<phi>"
    unfolding en_def using AAP EQS by (auto simp: KDEF)

  have "states \<phi> \<subseteq> states M"
    by (simp add: MEC mec_le states_mono)

  have "ec \<phi>'"
    unfolding ec_def
    apply -
    apply(rule conjI)
    subgoal unfolding sc_def
      using mec_ec[OF MEC] 
      unfolding ec_def sc_def EN SDEF by argo
    subgoal
      using mec_ec[OF MEC] 
      unfolding ec_def closed_mdpc_def EN SDEF by blast
    done

  moreover have "\<phi> \<le> \<phi>'"
    apply(rule le_mdpcI)
    subgoal using SDEF by blast
    subgoal for u using KDEF by force
    done

  moreover have "\<phi>' \<le> M"
    apply(rule le_mdpcI)
    apply (simp add: SDEF \<open>states \<phi> \<subseteq> states M\<close>)
    by (metis A'AM KDEF MEC insert_subset le_mdpc_iff mec_le)

  ultimately have "\<phi> = \<phi>'" 
    using MEC unfolding mec_def by presburger

  moreover have "a' \<in> actions \<phi>' u"
    using US KDEF[of u] by auto

  ultimately show "a' \<in> actions \<phi> u"
    by presburger
qed

lemma max_le_eq_mdp_eq: "\<phi> \<le>\<^sub>M \<psi> \<Longrightarrow> eq_mdp (states \<phi>) (K_actions \<phi>) (states \<psi>) (K_actions \<psi>) \<Longrightarrow> \<phi> = \<psi>"
  apply(rule mdpc_eqI)
  subgoal
    using eq_mdpD1 by blast
  subgoal for u
    apply(rule equalityI; safe)
    subgoal
      apply(drule max_le_mdpc_le)
      unfolding eq_mdp_def le_mdpc_iff by fast
    subgoal for a
      unfolding eq_mdp_def le_mdpc_iff max_le_mdpc_def K_actions_def
      by fast
    done
  done



definition sub_struc_of :: "'s mdpc \<Rightarrow> 's set \<Rightarrow> 's mdp_K \<Rightarrow> bool" where 
  "sub_struc_of M S K \<equiv> S \<subseteq> states M \<and> (\<forall>s \<in> S. K s \<subseteq> K_actions M s)"

lemma sub_struc_ofI: "S \<subseteq> states M \<Longrightarrow> (\<And>a s. s \<in> S \<Longrightarrow> K s \<subseteq> K_actions M s) \<Longrightarrow> sub_struc_of M S K"
  unfolding sub_struc_of_def by presburger

lemma sub_struc_ofD: "sub_struc_of M S K \<Longrightarrow> S \<subseteq> states M \<and> (\<forall>s \<in> S. K s \<subseteq> K_actions M s)"
  unfolding sub_struc_of_def by blast

lemma sub_struc_ofD1: "sub_struc_of M S K \<Longrightarrow> S \<subseteq> states M"
  unfolding sub_struc_of_def by blast

lemma sub_struc_ofD2: "sub_struc_of M S K \<Longrightarrow> (\<forall>s \<in> S. K s \<subseteq> K_actions M s)"
  unfolding sub_struc_of_def by blast

lemma sub_struc_ofE: "sub_struc_of M S K \<Longrightarrow> (S \<subseteq> states M \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> K s \<subseteq> K_actions M s) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding sub_struc_of_def by presburger

lemma sub_struc_sub_mdp_of: "sub_struc_of M S K \<Longrightarrow> sub_mdp_of S' K' S K \<Longrightarrow> sub_struc_of M S' K'"
  unfolding sub_struc_of_def sub_mdp_of_def by blast

lemma le_sub_struc_of: "M \<le> M' \<Longrightarrow> sub_struc_of M S K \<Longrightarrow> sub_struc_of M' S K"
  unfolding le_mdpc_iff
  apply(rule sub_struc_ofI)
  subgoal by (auto elim!: sub_struc_ofE)
  subgoal apply(erule sub_struc_ofE) 
    apply (clarsimp simp: K_actions_def)
    by (meson image_eqI image_mono subsetD)
  done 

lemma sub_struc_of_eq_sub_mdp_of: "sub_struc_of M S K \<longleftrightarrow> sub_mdp_of S K (states M) (K_actions M)"
  unfolding sub_struc_of_def sub_mdp_of_def K_actions_def
  by(rule refl)

lemma sub_struc_of_sub_Et_\<alpha>: "sub_struc_of M S K \<Longrightarrow> mdp_def.Et_\<alpha> S K \<subseteq> en M"
  unfolding sub_struc_of_def mdp_def.Et_\<alpha>_def en_Et_\<alpha>
  by fastforce

lemma sub_struc_of_actions_in_sup: "sub_struc_of M S K \<Longrightarrow> u \<in> S \<Longrightarrow> a \<in> K u \<Longrightarrow> a \<in> K_actions M u"
  unfolding sub_struc_of_def 
  apply clarsimp by force

lemma mdpc_from_sub_struc:
  assumes SUB: "sub_struc_of M S K"
  obtains M' where "M' \<le>\<^sub>M M" and "S = states M'" and "\<forall>u \<in> S. K u = K_actions M' u" 
  proof

    define M' where "M' \<equiv> Abs_mdpc (\<lambda>u. if u \<in> S then Some {p. p \<in> actions M u \<and> set_pmf p \<in> K u} else None)"

    show SDEF: "S = states M'"
      unfolding M'_def
      apply transfer 
      by (auto split: if_splits)

    have KDEF: "K u = K_actions M' u" if "u \<in> S" for u
      using that sub_struc_ofD2[OF SUB] unfolding M'_def K_actions_def 
      apply(transfer)
      by (fastforce split: if_splits option.splits)

    thus "\<forall>u \<in> S. K u = K_actions M' u"
      by blast

    have ASUB: "actions M' u \<subseteq> actions M u" for u
      unfolding M'_def 
      using sub_struc_ofD1[OF SUB]
      apply transfer by simp
      
    have ADEF: "p \<in> actions M' u = (p \<in> actions M u \<and> set_pmf p \<in> K u)" if "u \<in> S" for p u
      unfolding M'_def using that
      apply transfer by (auto split: option.splits)

    show "M' \<le>\<^sub>M M"
      apply(rule max_le_mdpcI)
      subgoal
        apply(rule le_mdpcI)
        subgoal 
          using sub_struc_ofD1[OF SUB] SDEF by blast
        subgoal for u
          using ASUB[of u] sub_struc_ofD[OF SUB] 
          by(auto simp: SDEF)
        done
      subgoal for u a a'
        using ADEF[of u , unfolded SDEF]
        by auto
      done

  qed


section \<open>Operations\<close>

definition "culled_self_loops M S K \<equiv> sub_struc_of M S K \<and> S = states M \<and> (\<forall>u \<in> states M. actions M u \<noteq> {return_pmf u} \<longrightarrow> K u = K_actions M u)"

lemma culled_self_loopsI: "sub_struc_of M S K \<Longrightarrow> S = states M \<Longrightarrow> (\<And>u. u \<in> states M \<Longrightarrow> actions M u \<noteq> {return_pmf u} \<Longrightarrow> K u = K_actions M u) \<Longrightarrow> culled_self_loops M S K"
  unfolding culled_self_loops_def by blast

lemma culled_self_loopsD: "culled_self_loops M S K \<Longrightarrow> sub_struc_of M S K \<and> S = states M \<and> (\<forall>u \<in> states M. actions M u \<noteq> {return_pmf u} \<longrightarrow> K u = K_actions M u)"
  unfolding culled_self_loops_def by blast


text \<open>
  These operations form all of the interactions with the MDP structure by the MEC algorithm:
  \<open>culled_edges\<close> Given a list of SCCs \<open>C\<close> and a "sublist" of MECs \<open>V\<close> and a kernel \<open>K\<close>, it returns
    \<open>True\<close> iff removing edges between different SCCs that are not MECs results in a kernel \<open>K'\<close>.
  
\<close>

definition "culled_edges C V K K' \<equiv> (let S' = \<Union>(set C) - \<Union>(set V) in \<forall>u \<in> S'. K' u = {a \<in> K u. \<exists>X' \<in> set C - set V. u \<in> X' \<and> (\<forall>v \<in> a. v \<in> X')})"

lemma "culled_edges C V K K' = (\<forall>u \<in> \<Union>(set C) - \<Union>(set V). K' u = {a \<in> K u. \<exists>X' \<in> set C - set V. u \<in> X' \<and> (\<forall>v \<in> a. v \<in> X')})"
  unfolding culled_edges_def by presburger

lemma culled_edgesI: "
  (\<And> u. u \<in> \<Union>(set C) - \<Union>(set V) \<Longrightarrow> K' u = {a \<in> K u. \<exists>X' \<in> set C - set V. u \<in> X' \<and> (\<forall>v \<in> a. v \<in> X')})
  \<Longrightarrow> culled_edges C V K K'"
  unfolding culled_edges_def
  by auto

lemma culled_edgesD: "culled_edges C V K K' \<Longrightarrow> u \<in> \<Union>(set C) - \<Union>(set V)
  \<Longrightarrow> K' u = {a \<in> K u. \<exists>X' \<in> set C - set V. u \<in> X' \<and> (\<forall>v \<in> a. v \<in> X')}"
  unfolding culled_edges_def
  by meson

lemma culled_edges_sub_mdp: "S = \<Union> (set C) \<Longrightarrow> S' = \<Union> (set C) - \<Union> (set V) \<Longrightarrow> culled_edges C V K K' \<Longrightarrow> sub_mdp_of S' K' S K"
  apply(rule sub_mdp_ofI)
  subgoal by blast
  subgoal
    apply clarsimp
    subgoal for u X a
      apply(drule culled_edgesD)
      by blast+
    done
  done

lemma culled_edges_K_subset: "culled_edges C V K K' \<Longrightarrow> u \<in> \<Union> (set C) - \<Union> (set V) \<Longrightarrow> a \<subseteq> T' \<Longrightarrow> a \<in> K' u \<Longrightarrow> a \<in> K u"
  unfolding culled_edges_def Let_def by blast

lemma culled_edges_K_supset: "culled_edges C V K K' \<Longrightarrow> u \<in> \<Union> (set C) - \<Union> (set V) \<Longrightarrow> u \<in> X' \<Longrightarrow> (\<forall>v \<in> a. v \<in> X') \<Longrightarrow> X' \<in> set C \<Longrightarrow> X' \<notin> set V \<Longrightarrow> a \<in> K u \<Longrightarrow> a \<in> K' u"
  unfolding culled_edges_def Let_def by blast

lemma culled_edges_K_eq: "culled_edges C V K K' \<Longrightarrow> u \<in> \<Union> (set C) - \<Union> (set V) \<Longrightarrow> u \<in> X' \<Longrightarrow> (\<forall>v \<in> a. v \<in> X') \<Longrightarrow> X' \<in> set C \<Longrightarrow> X' \<notin> set V \<Longrightarrow> a \<in> K u \<longleftrightarrow> a \<in> K' u"
  unfolding culled_edges_def Let_def by blast


definition "get_mec_pre = (\<lambda> (M,D,_,_). \<Union> (set D) = states M \<and> {} \<notin> set D)"



type_synonym 'v mec_abs_state = "'v mdpc \<times> 'v set list \<times> 'v set \<times> 'v mdp_K \<times> 'v set"
type_synonym 'v mec_abs_state_ext = "'v mdpc \<times> 'v set list \<times> 'v set list \<times> 'v set \<times> 'v mdp_K \<times> 'v set"


locale Finite_MDP_defs = fixes M::"'v mdpc"
begin

  sublocale mdp_def "(states M)" "(K_actions M)" .

  definition "mec_decomp = {states M' | M'. mec M M'}"

  lemma states_in_decomp: "u \<in> states M \<Longrightarrow> \<exists>X \<in> mec_decomp. u \<in> X"
    unfolding mec_decomp_def by auto

  lemma unique_in_mec_decomp:  "u \<in> X \<Longrightarrow> u \<in> Y \<Longrightarrow> X \<in> mec_decomp \<Longrightarrow> Y \<in> mec_decomp \<Longrightarrow> X = Y"
    unfolding mec_decomp_def by (auto dest!: the_mec_eqI)

end

context Finite_MDP
begin

  sublocale Finite_MDP_defs M .

  sublocale mdp "(states M)" "K_actions M"
    apply(unfold_locales)
    subgoal by (simp add: S_finite)
    subgoal
      by (auto simp: closed_mdpcD[OF closed_M] K_actions_mem intro!: closed_mdpI)
    done

end

text \<open>
  \<open>op_init_mdp\<close> adds a list of MECs to the MDP. For implementation purposes, we treat it as the 
  same data structure.
\<close>

\<comment> \<open>Initializes the loop state of the main loop of the MEC algorithm.\<close>
definition mop_init_mdp :: "'v mdpc \<Rightarrow> 'v mec_abs_state nres" where 
  "mop_init_mdp M\<^sub>0 = SPEC (\<lambda>(M,D,S,K,Z). M = M\<^sub>0 \<and> D = [] \<and> S = states M\<^sub>0 \<and> K = K_actions M\<^sub>0)"

\<comment> \<open>Checks whether there are still states in the loop state.\<close>
definition "op_states_non_empty = (\<lambda> (M,D,S,K,Z). S \<noteq> {})"

\<comment> \<open>Checks for a given state whether it is a state in the loop state.\<close>
definition "op_deleted_state = (\<lambda> (M,D,S,K,Z) u. u \<notin> S)"

\<comment> \<open>Increases the MEC counter.\<close>
definition op_expand_capacity where
  "op_expand_capacity = (\<lambda> (M,D,S,K,Z) n. (M,D @ replicate n {},S,K,Z))" (* Graph Operation *)

\<comment> \<open>Returns the number of MECs.\<close>
definition "op_get_mec_num = (\<lambda> (M,D,S,K,Z). length D)"

\<comment> \<open>Checks whether all successors of state \<open>u\<close> are part of the same SCC as \<open>u\<close>.\<close>
definition "op_all_succ_eq_map \<equiv> (\<lambda> (M,D,S,K,Z) (C,V) u. \<forall> a \<in> (K u). \<exists> i < length C. u \<in> C ! i \<and> a \<subseteq> C ! i)" 

text \<open>
  \<open>mop_track_sccs\<close> supplements our data structure to avoid tricky bookkeeping
  of the activated transitions (that may behave non-monotonically.

  NOTE: We have found a solution that does not involve adding extra data but have not implemented
    that into this artifact yet.
\<close>

definition mop_track_sccs :: "'v mec_abs_state \<Rightarrow> 'v set list \<times> 'v set list \<Rightarrow> 'v mec_abs_state_ext nres" where 
  "mop_track_sccs = (\<lambda> (M,D,S,K,Z) (C,V). SPEC(\<lambda>(M',L',D',S',K',Z'). length C \<le> length L' \<and> \<Union>(set L') \<subseteq> S \<and> M' = M \<and> D' = D \<and> S' = S \<and> K' = K \<and> Z'=Z))"

text \<open>These next three operations are exclusively meant for the supplemented data structure.\<close>

\<comment> \<open>Same as \<open>op_deleted_state\<close>.\<close>
definition "op_deleted_stateL = (\<lambda> (M,L,D,S,K) u. u \<notin> S)"

\<comment> \<open>Mark a state as part of a MEC with the specified ID.\<close>
definition mop_add_state_to_mec:: "'v mec_abs_state_ext \<Rightarrow> 'v set list \<times> 'v set list \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'v mec_abs_state_ext nres" where 
  "mop_add_state_to_mec = (\<lambda> (M,L,D,S,_,Z) (C,V) u i. SPEC(\<lambda> (M',L',D',S',_,Z'). M' = M \<and> L' = (map (\<lambda>X. X - {u}) L) \<and> D'=(map (\<lambda>X. X - {u}) D)[i:=(insert u (D ! i))] \<and> S' = S - {u} \<and> Z'=Z))" (* Graph states operation *)

\<comment> \<open>Mark a state as unfinished, i.e. it is in an SCC that needs further culling.\<close>
definition mop_add_state_unfinished :: "'v mec_abs_state_ext \<Rightarrow> 'v set list \<times> 'v set list \<Rightarrow> 'v \<Rightarrow> 'v mec_abs_state_ext nres" where 
  "mop_add_state_unfinished = (\<lambda> (M,L,D,S,_,Z) (C,V) u. SPEC(\<lambda> (M',L',D',S',_,Z'). M' = M \<and> (\<exists>i. i < length C \<and> u \<in> C ! i \<and> L' = (map (\<lambda>X. X - {u}) L)[i := (insert u (L ! i))]) \<and> D'=(map (\<lambda>X. X - {u}) D) \<and> S' = S \<and> Z'=Z))" (* Graph states operation *)

text \<open>Once the graph culling has finished, the supplemented data is removed.\<close>

definition mop_untrack_sccs :: "'v mec_abs_state_ext \<Rightarrow> 'v set list \<times> 'v set list \<Rightarrow> 'v mec_abs_state nres" where
  "mop_untrack_sccs = (\<lambda> (M,L,D,S,_,Z) (C,V). SPEC (\<lambda> (M',D',S',K',Z'). M'=M \<and> D'=D \<and> S'=S \<and> culled_edges C V (K_actions M) K' \<and> Z'=Z))"

\<comment> \<open>Get the index of the MEC that the specified state is a part of (if applicable).\<close>
definition mop_get_state_mec_id :: "'v set list \<times> 'v set list \<Rightarrow> 'v \<Rightarrow> nat option nres" where
  "mop_get_state_mec_id = (\<lambda> (C,V) u. SELECT (\<lambda> i. i < length V \<and> u \<in> V ! i))" (* MEC/SCC map operation*)

\<comment> \<open>Extract the MECs and return the input data structure (which remains unchanged over the coarse of the algorithm).\<close>
definition "op_get_mecs = (\<lambda> (M,D,_,_,_). (D,M))"


lemma op_all_succ_eq_map_succ: "\<forall> u i j. i < length C \<longrightarrow> j < length C \<longrightarrow> u \<in> C ! i \<longrightarrow> u \<in> C ! j \<longrightarrow> i = j 
    \<Longrightarrow> i < length C \<Longrightarrow> u \<in> C ! i \<Longrightarrow> a \<in> K u \<Longrightarrow> op_all_succ_eq_map (M,D,S,K,Z) (C,V) u \<Longrightarrow> a \<subseteq> C ! i"
  unfolding op_all_succ_eq_map_def by fast

section \<open>High-level MEC operations\<close>

definition "compute_sccs = (\<lambda> (_,_,S,K,Z). SPEC (\<lambda>r. scc_list r S K))"
 
definition "identify_mecs C = (\<lambda> (M,D,S,K,Z). do{ SPEC(\<lambda>(C',V'). C'=C \<and> distinct V' \<and> set V' = {S' \<in> set C. closed_mdp S' K})})"

definition "cull_graph = (\<lambda> (C,V) (M,D,S,K,Z). SPEC (\<lambda> (M',D',S',K',Z'). M'=M \<and> D' = D@V \<and> S' = S-\<Union>(set V) \<and> culled_edges C V K K' \<and> Z'=Z))"


end

