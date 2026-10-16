theory MaxEndComponent
  imports "../ds/Filter_Index_List" "MDP_MEC"
begin

  section \<open>General Lemmas\<close>
  
  lemma map_substract_eq_replicate_empty_set: "\<forall> x \<in> set xs. x \<subseteq> X \<Longrightarrow> map (\<lambda>x. x - X) xs = replicate (length xs) {}"
    by(induction xs) auto
  
  lemma disj_sub_sub_set: "A \<inter> C = {} \<Longrightarrow> A - B = (A - (B - C))"
    by blast
  
  lemma append_right_upd: "(xs @ ys)[length xs + i:=x] = xs @ (ys[i:=x])"
    apply(induction xs)
    apply auto
    done
  
  lemma insert_Un_list_upd: "i < length X \<Longrightarrow> \<Union> (set (X[i:=insert u (X ! i)])) = insert u (\<Union>(set X))"
    apply(induction X arbitrary: i rule: rev_induct)
    subgoal by simp
    subgoal for x xs i
      apply(cases "i = length xs")
      apply auto[]
      by (simp add: list_update_append1)
    done
  
  lemma ASSERT_over_prod: "(case s' of (a,b) \<Rightarrow> do{ASSERT (P a b); f a b}) = do{ASSERT (case s' of (a,b) \<Rightarrow> P a b); case s' of (a,b) \<Rightarrow> f a b}"
    apply(cases s')
    by auto
  
  
  section \<open>Maximal End Components\<close>
  
  context mdp_def
  begin
  
  
    subsubsection \<open>Setup\<close>
  
    lemma union_sub_mdp:
    assumes SUB:"\<forall>(S',K') \<in> M. sub_mdp S' K'"
    assumes KM: "K\<^sub>m \<in> union_mdp_K_set M"
    shows "sub_mdp (union_mdp_states M) K\<^sub>m"
    using assms
    unfolding sub_mdp_def
    by(rule union_sub_mdp_of)
  
  
  
    definition "is_ec S' K' \<equiv> S' \<noteq> {} \<and> sub_mdp S' K' \<and> closed_mdp S' K' \<and> (S' \<times> S') \<subseteq> (mdp_def.Et_\<alpha> S' K')\<^sup>*"
  
    lemma(in -) eq_mdp_sc: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> (S\<^sub>1 \<times> S\<^sub>1) \<subseteq> (mdp_def.Et_\<alpha> S\<^sub>1 K\<^sub>1)\<^sup>* \<Longrightarrow> (S\<^sub>2 \<times> S\<^sub>2) \<subseteq> (mdp_def.Et_\<alpha> S\<^sub>2 K\<^sub>2)\<^sup>*"
      apply(frule eq_mdp_Et_\<alpha>_eq)
      apply(frule eq_mdpD1)
      by auto
  
    lemma eq_mdp_ec: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> is_ec S\<^sub>1 K\<^sub>1 \<Longrightarrow> is_ec S\<^sub>2 K\<^sub>2"
      unfolding is_ec_def by(auto simp: sub_mdp_eq_mdp eq_mdp_closed_mdp eq_mdp_sc intro!: not_eq_mdpI1) 
  
    lemma union_ec:
      assumes EC: "\<forall>(S',K') \<in> M. is_ec S' K'"
      and OV: "\<forall>(S',K') \<in> M. v \<in> S'"
      assumes KM: "K\<^sub>m \<in> union_mdp_K_set M"
      and NE: "M \<noteq> {}"
      shows "is_ec (union_mdp_states M) K\<^sub>m"
    proof-
      have "sub_mdp (union_mdp_states M) K\<^sub>m"
        apply(rule union_sub_mdp)
        using EC KM unfolding is_ec_def by fast+
  
      moreover have "closed_mdp (union_mdp_states M) K\<^sub>m"
        apply(rule union_closed)
        using EC KM unfolding is_ec_def by fast+
  
      moreover have "(union_mdp_states M) \<times> (union_mdp_states M) \<subseteq> (mdp_def.Et_\<alpha> (union_mdp_states M) K\<^sub>m)\<^sup>*"
        apply(rule union_sc)
        using EC KM OV unfolding is_ec_def by fast+
  
      moreover have "union_mdp_states M \<noteq> {}"
        using EC NE  unfolding union_mdp_states_def is_ec_def by fast
        
      ultimately show ?thesis unfolding is_ec_def by blast
    qed
  
    lemma(in -) is_ec_sub_mdp: "mdp_def.is_ec S\<^sub>1 K\<^sub>1 S' K' \<Longrightarrow> sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> mdp_def.is_ec S\<^sub>2 K\<^sub>2 S' K'"
      unfolding mdp_def.is_ec_def mdp_def.sub_mdp_def  by (auto elim!: sub_mdp_of_order(3) dest: sub_mdp_ofD ) 
  
    lemma is_ec_of_sub_mdp: "mdp_def.is_ec S' K' S'' K'' \<Longrightarrow> sub_mdp S' K' \<Longrightarrow> is_ec S'' K''"
      unfolding mdp_def.is_ec_def mdp_def.sub_mdp_def by (auto elim!: sub_mdp_of_order(3) dest: sub_mdp_ofD) 
  
  
    lemma(in -) is_ec_sup_mdp: "mdp_def.is_ec S\<^sub>1 K\<^sub>1 S' K' \<Longrightarrow> sub_mdp_of S\<^sub>2 K\<^sub>2 S\<^sub>1 K\<^sub>1 \<Longrightarrow> S\<^sub>2 \<noteq> {} \<Longrightarrow> (S\<^sub>1 - S\<^sub>2) \<inter> S' = {} \<Longrightarrow> \<forall>u \<in> S'. K' u \<subseteq> K\<^sub>2 u \<Longrightarrow> mdp_def.is_ec S\<^sub>2 K\<^sub>2 S' K'"
      unfolding mdp_def.is_ec_def mdp_def.sub_mdp_def
      apply clarsimp
      unfolding sub_mdp_of_def
      by blast
  
    lemma(in -) is_ec_sup_mdp': "mdp_def.is_ec S\<^sub>1 K\<^sub>1 S' K' \<Longrightarrow> sub_mdp_of S\<^sub>2 K\<^sub>2 S\<^sub>1 K\<^sub>1 \<Longrightarrow> S\<^sub>2 \<noteq> {} \<Longrightarrow> (S\<^sub>1 - S\<^sub>2) \<inter> S' = {} \<Longrightarrow> \<forall>u \<in> S'. K\<^sub>1 u = K\<^sub>2 u \<Longrightarrow> mdp_def.is_ec S\<^sub>2 K\<^sub>2 S' K'"
      unfolding mdp_def.is_ec_def mdp_def.sub_mdp_def
      apply clarsimp
      unfolding sub_mdp_of_def
      by blast
  
    lemma ec_sub_mdp: "is_ec S' K' \<Longrightarrow> sub_mdp S' K'"
      unfolding is_ec_def
      by simp
  
    lemma ec_closed_mdp: "mdp_def.is_ec S K S' K' \<Longrightarrow> closed_mdp S' K'"
      unfolding is_ec_def by blast
  
    lemma ec_strongly_connected: "is_ec S' K' \<Longrightarrow> S' \<times> S' \<subseteq> (mdp_def.Et_\<alpha> S' K')\<^sup>*" 
      unfolding is_ec_def by argo
  
    lemma(in -) ec_sub_mdp_of: "mdp_def.is_ec S K S' K' \<Longrightarrow> sub_mdp_of S' K' S K"
      apply(drule mdp_def.ec_sub_mdp)
      unfolding mdp_def.sub_mdp_def by assumption
  
    lemma ec_strongly_connected_ext: "is_ec S' K' \<Longrightarrow> S' \<times> S' \<subseteq> (mdp_def.Et_\<alpha> S K)\<^sup>*"
      apply(frule ec_sub_mdp_of)
      apply(drule sub_mdp_of_sub_Et_\<alpha>[THEN rtrancl_mono])
      apply(drule ec_strongly_connected) 
      by auto
  
    lemma singleton_is_ec: "u \<in> S \<Longrightarrow> is_ec {u} (\<lambda>_. {})"
      unfolding is_ec_def
      by (auto simp: sub_mdp_def sub_mdp_of_def closed_mdp_def) 
  
    lemma ex_ec_over_state: "u \<in> S \<Longrightarrow> \<exists> S' K'. is_ec S' K' \<and> u \<in> S'"
      apply(rule exI[where ?x="{u}"])
      apply(rule exI[where ?x="(\<lambda>_.{})"])
      by (simp add: singleton_is_ec)
  
    lemmas(in -) ec_sub_mdp_ofD1 = ec_sub_mdp_of[THEN sub_mdp_ofD1]
  
    lemmas(in -) ec_sub_mdp_ofD2 = ec_sub_mdp_of[THEN sub_mdp_ofD2]
  
    definition "is_mec S' K' \<equiv> is_ec S' K' \<and> 
      (\<nexists>S'' K''. is_ec S'' K'' \<and> psub_mdp_of S' K' S'' K'')"
  
    lemma eq_mdp_mec:  "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> is_mec S\<^sub>1 K\<^sub>1 \<Longrightarrow> is_mec S\<^sub>2 K\<^sub>2"
      unfolding is_mec_def
      apply(rule conjI)
      subgoal by(auto simp: eq_mdp_ec) 
      subgoal using eq_mdp_equiv(2) by blast
      done
  
    lemma mec_is_ec: "is_mec S' K' \<Longrightarrow> is_ec S' K'"
      unfolding is_mec_def by blast
  
    lemma mec_sub_mdp: "is_mec S' K' \<Longrightarrow> sub_mdp S' K'"
      apply(rule ec_sub_mdp)
      apply(erule mec_is_ec)
      done
  
    lemma(in -) mec_sub_mdp_of: "mdp_def.is_mec S K S' K' \<Longrightarrow> sub_mdp_of S' K' S K"
      apply(drule mdp_def.mec_sub_mdp)
      unfolding mdp_def.sub_mdp_def by assumption
  
    lemmas(in -) mec_sub_mdp_ofD1 = mec_sub_mdp_of[THEN sub_mdp_ofD1]
  
    lemmas(in -) mec_sub_mdp_ofD2 = mec_sub_mdp_of[THEN sub_mdp_ofD2]
  
    lemma mec_closed_mdp: "is_mec S' K' \<Longrightarrow> closed_mdp S' K'"
      apply(rule ec_closed_mdp)
      apply(erule mec_is_ec)
      done
  
    lemma mec_strongly_connected: "is_mec S' K' \<Longrightarrow> S' \<times> S' \<subseteq> (mdp_def.Et_\<alpha> S' K')\<^sup>*" 
      apply(drule mec_is_ec) using ec_strongly_connected .
  
    lemma mec_strongly_connected_ext: "is_mec S' K' \<Longrightarrow> S' \<times> S' \<subseteq> (mdp_def.Et_\<alpha> S K)\<^sup>*"
      apply(drule mec_is_ec) using ec_strongly_connected_ext .
  
    lemma mec_maximal: "is_mec S' K' \<Longrightarrow> \<nexists> S''  K''. is_ec S'' K'' \<and> psub_mdp_of S' K' S'' K''"
      unfolding is_mec_def by blast
  
    lemma sup_ec_not_mec: "is_ec S'' K'' \<Longrightarrow> psub_mdp_of S' K' S'' K'' \<Longrightarrow> \<not>is_mec S'  K'"
      unfolding is_mec_def by blast
  
    definition "mec_set_struc = {S' |S' K'. is_mec S' K' }"
  
    lemma mec_set_struc_mem: "S' \<in> mec_set_struc \<longleftrightarrow> (\<exists>K'. is_mec S' K')"
      unfolding mec_set_struc_def by simp
  
    definition "ec_set_over u = {(S',K'). u \<in> S' \<and> is_ec S' K'}"
  
    lemma ec_set_over_mem[simp]: "(S',K') \<in> ec_set_over u \<longleftrightarrow> u \<in> S' \<and> is_ec S' K'"
      unfolding ec_set_over_def
      by fast 
  
    lemma is_in_ec_set_over: "is_ec S' K' \<Longrightarrow> u \<in> S' \<Longrightarrow> (S',K') \<in> ec_set_over u"
      unfolding ec_set_over_def
      by fast
  
    lemma ec_set_over_ne: "u \<in> S \<Longrightarrow> ec_set_over u \<noteq> {}"
      unfolding ec_set_over_def
      using ex_ec_over_state by fastforce
                                                
    lemma union_ec_over_is_ec: "u \<in> S \<Longrightarrow> K\<^sub>m \<in> union_mdp_K_set (ec_set_over u) \<Longrightarrow> is_ec (union_mdp_states (ec_set_over u)) K\<^sub>m"
      apply(rule union_ec)
      apply(auto simp: ec_set_over_def ec_set_over_ne )[3]
      apply(erule ec_set_over_ne)
      done
  
    lemma ec_sub_mdp_of_union_ec_over: "K\<^sub>m \<in> union_mdp_K_set (ec_set_over u) \<Longrightarrow> u \<in> S' \<Longrightarrow> is_ec S' K' \<Longrightarrow> sub_mdp_of S' K' (union_mdp_states (ec_set_over u)) K\<^sub>m"
      by (simp add: mem_sub_mdp_of_union)
  
  
    lemma(in -) is_mec_sup_mdp: "mdp_def.is_mec S\<^sub>1 K\<^sub>1 S' K' \<Longrightarrow> sub_mdp_of S\<^sub>2 K\<^sub>2 S\<^sub>1 K\<^sub>1 \<Longrightarrow> S\<^sub>2 \<noteq> {} \<Longrightarrow> (S\<^sub>1 - S\<^sub>2) \<inter> S' = {} \<Longrightarrow> \<forall>u \<in> S'. K' u \<subseteq> K\<^sub>2 u \<Longrightarrow> mdp_def.is_mec S\<^sub>2 K\<^sub>2 S' K'"
      unfolding mdp_def.is_mec_def
      apply clarsimp 
      by (meson is_ec_sub_mdp is_ec_sup_mdp)
  
    subsubsection \<open>Sanity Checks\<close>
  
    lemma ex_policy_in_ec: 
      assumes EC: "is_ec S' K'" 
      and US: "u \<in> S'" 
      and SIN: "\<not>is_singleton S'" 
      shows "\<exists> a \<in> K u. \<forall> v \<in> a. v \<in> S'"
    proof -
      obtain w where "u \<noteq> w" and "w \<in> S'"
        using mem_nsingleton_get_distinct_mem[OF US SIN] .
      with EC have "(u,w) \<in> (mdp_def.Et_\<alpha> S' K')\<^sup>+" unfolding is_ec_def
        by (meson SigmaI US rtrancl_eq_trancl_cases subset_eq)
      then obtain v where "(u,v) \<in> mdp_def.Et_\<alpha> S' K'"
        by (meson tranclD)
      then obtain a where AMEM: "a \<in> K' u" unfolding mdp_def.Et_\<alpha>_def by force
      moreover from EC have "closed_mdp S' K'" unfolding is_ec_def by simp 
      ultimately have A: "a \<subseteq> S'" unfolding closed_mdp_def using US by blast
      moreover have B: "a \<in> K u" using EC US AMEM 
        unfolding is_ec_def sub_mdp_def sub_mdp_of_def by blast
      show ?thesis
        apply(rule bexI[where ?x="a"])
        subgoal using A by blast
        subgoal using B by blast
        done
    qed
  
  
    lemma all_policies_in_ec: "is_ec S' K' \<Longrightarrow> u \<in> S' \<Longrightarrow> \<forall> a \<in> K' u. \<forall> v \<in> a. v \<in> S'"
      unfolding is_ec_def closed_mdp_def 
      apply clarsimp
      by blast
  
    lemma sc_with_persistent_policy_is_ec:
          "S' \<noteq> {}
      \<Longrightarrow> sub_mdp S' K'
      \<Longrightarrow> (S'\<times>S') \<subseteq> (mdp_def.Et_\<alpha> S' K')\<^sup>* 
      \<Longrightarrow> \<forall> u \<in> S'. \<forall> a \<in> K' u. \<forall> v \<in> a. v \<in> S' 
      \<Longrightarrow> is_ec S' K'"
      unfolding is_ec_def closed_mdp_def
      by clarsimp
  
  
    lemma empty_is_not_ec: "\<not>is_ec {} K'"
      unfolding is_ec_def by presburger
  
    lemma mdp_mec_non_empty: "\<not>is_mec {} K'"
      unfolding is_mec_def using empty_is_not_ec by fast
  
  
    lemma mdp_mec_is_non_empty: "is_mec S' K' \<Longrightarrow> S' \<noteq> {}" 
      using mdp_mec_non_empty 
      by blast
  
  
    subsubsection \<open>Existence of a MEC for each state\<close>
  
    lemma u_in_ec_set_over: "u \<in> S \<Longrightarrow> u \<in> (union_mdp_states (ec_set_over u))"
      unfolding ec_set_over_def union_mdp_states_def
      apply(drule ex_ec_over_state)
      by blast
  
    lemma union_ec_over_is_mec: 
      assumes US: "u \<in> S"
      assumes KM: "K\<^sub>m \<in> union_mdp_K_set (ec_set_over u)"
      shows "is_mec (union_mdp_states (ec_set_over u)) K\<^sub>m"
    proof(rule ccontr)
      assume "\<not> is_mec (union_mdp_states (ec_set_over u)) K\<^sub>m"
      then obtain S' K' where NEQ: "not_eq_mdp (union_mdp_states (ec_set_over u)) K\<^sub>m S' K'" 
        and EC: "is_ec S' K'" and SUB: "sub_mdp_of (union_mdp_states (ec_set_over u)) K\<^sub>m S' K'" 
        unfolding is_mec_def psub_mdp_of_def using union_ec_over_is_ec[OF US KM] by fast
      from SUB have "u \<in> S'" using u_in_ec_set_over[OF US] unfolding sub_mdp_of_def ec_set_over_def
        by blast
      hence "sub_mdp_of S' K' (union_mdp_states (ec_set_over u)) K\<^sub>m"
        apply(rule ec_sub_mdp_of_union_ec_over[OF KM])
        using EC .
      with SUB have "eq_mdp (union_mdp_states (ec_set_over u)) K\<^sub>m S' K' " 
        using sub_mdp_of_order(2) by blast
      thus False using NEQ by auto
    qed
  
    lemma ex_union_ec_set:
      assumes US: "u \<in> S"
      assumes FIN: "finite S"
      shows "union_mdp_K_set (ec_set_over u) \<noteq> {}"
    proof -
      have "union_mdp_states (ec_set_over u) \<subseteq> S"
        unfolding union_mdp_states_def ec_set_over_def  
        by (auto dest: ec_sub_mdp sub_mdp_subset_S)
  
      hence "finite (union_mdp_states (ec_set_over u))"
        unfolding union_mdp_states_def ec_set_over_def
        by (simp add: FIN finite_subset)
      moreover have "\<forall>(S,K) \<in> (ec_set_over u). sub_mdp S K"
        using ec_sub_mdp by force
  
      ultimately obtain K\<^sub>m where "K\<^sub>m \<in> union_mdp_K_set (ec_set_over u)"
        using ex_union_sub_mdp_K_set by blast
      thus ?thesis by blast
    qed
  
    corollary ex_mec_over_S: "finite S \<Longrightarrow> u \<in> S \<Longrightarrow> \<exists>S' K'. is_mec S' K' \<and> u \<in> S'"
    proof -
      assume FIN: "finite S" and US: "u \<in> S"
  
      then obtain K\<^sub>m where "K\<^sub>m \<in> union_mdp_K_set (ec_set_over u)"
        using ex_union_ec_set by blast
  
      thus ?thesis 
        apply -
        apply(drule union_ec_over_is_mec[OF US]) 
        apply(rule exI[where ?x="(union_mdp_states (ec_set_over u))"])
        apply(rule exI[where ?x="K\<^sub>m"])
        using u_in_ec_set_over[OF US] by auto
    qed
  
  
    subsubsection \<open>Uniqueness of MECs per state\<close>
  
    lemma unique_mec_per_state:
      assumes MEC1: "is_mec S\<^sub>1 K\<^sub>1" 
      and MEC2: "is_mec S\<^sub>2 K\<^sub>2" 
      and OV: "S\<^sub>1 \<inter> S\<^sub>2 \<noteq> {}"
      shows "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
    proof -
      define S\<^sub>m where "S\<^sub>m \<equiv> (union_mdp_states {(S\<^sub>1, K\<^sub>1), (S\<^sub>2, K\<^sub>2)})"
  
      then obtain K\<^sub>m where KM: "K\<^sub>m \<in> union_mdp_K_set {(S\<^sub>1, K\<^sub>1), (S\<^sub>2, K\<^sub>2)}"
        using ex_union_sub_mdp_K_set
        by (metis MEC1 MEC2 all_not_in_conv insert_iff mdp_def.mec_sub_mdp old.prod.case)
  
      from OV obtain u where "u \<in> S\<^sub>1" and "u \<in> S\<^sub>2" 
        by blast
      moreover note mec_is_ec[OF MEC1] mec_is_ec[OF MEC2]
      ultimately have ECM: "is_ec S\<^sub>m K\<^sub>m"
        apply(unfold S\<^sub>m_def)
        by(auto simp: KM intro: union_ec)
  
      have "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>m K\<^sub>m" 
        apply(unfold S\<^sub>m_def)
        by(auto simp: KM intro: mem_sub_mdp_of_union)
      hence EQ1: "eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>m K\<^sub>m" 
        using MEC1 ECM sub_mdp_not_psub_eq unfolding is_mec_def 
        by (auto dest!: spec[where ?x=S\<^sub>m] spec[where ?x=K\<^sub>m])
  
      have "sub_mdp_of S\<^sub>2 K\<^sub>2 S\<^sub>m K\<^sub>m" 
        apply(unfold S\<^sub>m_def)
        by(auto simp: KM intro: mem_sub_mdp_of_union)
      hence EQ2: "eq_mdp S\<^sub>m K\<^sub>m S\<^sub>2 K\<^sub>2" 
        apply(rewrite eq_mdp_equiv(2))
        using MEC2 ECM sub_mdp_not_psub_eq unfolding is_mec_def 
        by (auto dest!: spec[where ?x=S\<^sub>m] spec[where ?x=K\<^sub>m])
  
      show ?thesis using eq_mdp_equiv(3)[OF EQ1 EQ2] .
    qed
  
    subsubsection \<open>Existence of a unique MEC\<close>
  
    theorem ex_unique_mec:
      assumes US: "u \<in> S" 
      assumes FIN: "finite S" 
      obtains S\<^sub>1 K\<^sub>1 
      where "u \<in> S\<^sub>1" 
        and "is_mec S\<^sub>1 K\<^sub>1" 
        and "\<forall> S\<^sub>2 K\<^sub>2. u \<in> S\<^sub>2 \<longrightarrow> is_mec S\<^sub>2 K\<^sub>2 \<longrightarrow> eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
    proof -
      from US obtain S\<^sub>1 K\<^sub>1 where "is_mec S\<^sub>1 K\<^sub>1" and "u \<in> S\<^sub>1"
        using ex_mec_over_S FIN by blast
      moreover then have "\<forall> S\<^sub>2 K\<^sub>2. u \<in> S\<^sub>2 \<longrightarrow> is_mec S\<^sub>2 K\<^sub>2 \<longrightarrow> eq_mdp S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2" 
        by(auto intro!: unique_mec_per_state)
      ultimately show ?thesis using that 
        by presburger
    qed
  
    subsubsection \<open>Other MEC lemmas\<close>
  
    lemma mec_non_empty: assumes "S \<noteq> {}" shows "\<not>is_mec {} K'"
      using is_mec_def empty_is_not_ec by blast
  
    lemma mec_is_non_empty: "S \<noteq> {} \<Longrightarrow> is_mec S' K' \<Longrightarrow> S' \<noteq> {}" 
      using mec_non_empty 
      by blast
  
    lemma sub_mdp_insert_transition: "sub_mdp S' K' \<Longrightarrow> a \<in> K u \<Longrightarrow> sub_mdp S' (K'(u := insert a (K' u)))"
      unfolding sub_mdp_def using sub_mdp_of_insert_transition .
                                             
    lemma(in -) sub_mdp_of_sub_mdp:  "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2 \<Longrightarrow> mdp_def.sub_mdp S\<^sub>2 K\<^sub>2 S\<^sub>1 K\<^sub>1"
      unfolding mdp_def.sub_mdp_def by assumption
  
    lemma is_ec_insert_transition: "is_ec S' K' \<Longrightarrow> a \<in> K u \<Longrightarrow> a \<subseteq> S' \<Longrightarrow> is_ec S' (K'(u := insert a (K' u)))"
      unfolding is_ec_def
      apply clarsimp 
      apply(rule conjI)
      apply(erule sub_mdp_insert_transition)
      apply assumption
      apply(rule conjI)
      apply(erule closed_mdp_insert_trans)
      apply assumption
      apply clarsimp
      apply(rule mdp_def.sub_mdp_sub_Et_\<alpha>[THEN rtrancl_mono, THEN in_mono, THEN mp])
      apply(rule sub_mdp_of_sub_mdp)
      apply(rule sub_mdp_of_self_insert_transition)
      by blast
  
    lemma union_ec_set_eq_mec: 
      assumes US': "u \<in> S'" 
      assumes MEC: "is_mec S' K'" 
      assumes KM: "K\<^sub>m \<in> union_mdp_K_set (ec_set_over u)"
      shows "eq_mdp S' K' (union_mdp_states (ec_set_over u)) K\<^sub>m"
    proof -
      have US: "u \<in> S"
        using MEC US' mec_sub_mdp_ofD1 by blast 
      
  
      have "u \<in> union_mdp_states (ec_set_over u)"
        by (simp add: u_in_ec_set_over US)
      with US' have "S' \<inter> (union_mdp_states (ec_set_over u)) \<noteq> {}" by blast
      moreover have "is_mec (union_mdp_states (ec_set_over u)) K\<^sub>m" 
        using union_ec_over_is_mec[OF US KM] .
      ultimately show ?thesis using unique_mec_per_state[OF MEC]
        by presburger
    qed
  
    lemma ec_subset_of_mec: 
      assumes EC: "is_ec S\<^sub>1 K\<^sub>1" 
      and MEC: "is_mec S\<^sub>2 K\<^sub>2" 
      and U1: "u \<in> S\<^sub>1" 
      and U2: "u \<in> S\<^sub>2" 
      and FIN: "finite S"
      shows "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
    proof-
    
      have "u \<in> S"
        using EC U1 ec_sub_mdp_ofD1 by blast
  
      then obtain K\<^sub>m where KM: "K\<^sub>m \<in> union_mdp_K_set (ec_set_over u)" 
        using ex_union_ec_set FIN by blast
  
      note EQ1 = union_ec_set_eq_mec[OF U2 MEC KM, folded eq_mdp_equiv(2)]
    
      note SUB1 = ec_sub_mdp_of_union_ec_over[OF KM U1 EC]
    
      from SUB1 EQ1 show ?thesis 
        using eq_mdp_equiv(2) by blast
    
    qed
  
  end
  
  lemma mec_of_sub_mdp_is_sub: 
    assumes MEC1: "mdp_def.is_mec S\<^sub>1 K\<^sub>1 S\<^sub>a K\<^sub>a"
    and MEC2: "mdp_def.is_mec S\<^sub>2 K\<^sub>2 S\<^sub>b K\<^sub>b"
    and SUB: "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
    and UA: "u \<in> S\<^sub>a"
    and UB: "u \<in> S\<^sub>b"
    and FIN: "finite S\<^sub>2"
    shows "sub_mdp_of S\<^sub>a K\<^sub>a S\<^sub>b K\<^sub>b"
  proof -
    have A: "mdp_def.is_ec S\<^sub>2 K\<^sub>2 S\<^sub>a K\<^sub>a"
      using MEC1 SUB is_ec_sub_mdp mdp_def.is_mec_def by blast
    show ?thesis using mdp_def.ec_subset_of_mec[OF A MEC2 UA UB FIN] .
  qed
  
  lemma is_mec_of_sub_mdp: 
    assumes MECS: "mdp_def.is_mec S\<^sub>1 K\<^sub>1 S' K'"
    and NE: "S\<^sub>1 \<noteq> {}"
    and SUB: "sub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
    and KB: "\<forall> u \<in> S\<^sub>2 - S'. (\<forall> S'' K''. mdp_def.is_mec S\<^sub>2 K\<^sub>2 S'' K'' \<longrightarrow> u \<in> S'' \<longrightarrow> S' \<inter> S'' = {})"
    and KN: "\<forall> u \<in> S'. (\<forall> a \<in> (K\<^sub>2 u). a \<subseteq> S' \<longrightarrow> a \<in> (K\<^sub>1 u))"
    and FIN: "finite S\<^sub>2"
    shows "mdp_def.is_mec S\<^sub>2 K\<^sub>2 S' K'"
  proof(rule ccontr)
    assume "\<not> mdp_def.is_mec S\<^sub>2 K\<^sub>2 S' K'"
    moreover from mdp_def.mec_is_ec[OF MECS] SUB have EC': "mdp_def.is_ec S\<^sub>2 K\<^sub>2 S' K'"
      by(simp add: is_ec_sub_mdp)
    ultimately obtain S\<^sub>a K\<^sub>a where ECA: "mdp_def.is_ec S\<^sub>2 K\<^sub>2 S\<^sub>a K\<^sub>a" and PSUBA: "psub_mdp_of S' K' S\<^sub>a K\<^sub>a" 
      unfolding mdp_def.is_mec_def by fast
    hence SUBA: "sub_mdp_of S' K' S\<^sub>a K\<^sub>a" and "not_eq_mdp S' K' S\<^sub>a K\<^sub>a" 
      unfolding psub_mdp_of_def by blast+
    then consider (ssub) "S' \<subset> S\<^sub>a" | (ksub) "S' = S\<^sub>a \<and> (\<exists> u \<in> S'. K' u \<subset> K\<^sub>a u)"
      unfolding sub_mdp_of_def not_eq_mdp_def by auto
    then show False
    proof(cases)
      case ssub
      then obtain u where UMEM: "u \<in> S\<^sub>a - S'" and UMEM': "u \<in> S\<^sub>2 - S'"
        using ec_sub_mdp_ofD1[OF ECA]
        by blast
      then obtain S\<^sub>b K\<^sub>b where MECB: "mdp_def.is_mec S\<^sub>2 K\<^sub>2 S\<^sub>b K\<^sub>b" and USB: "u \<in> S\<^sub>b"
        by (meson DiffE mdp_def.ex_unique_mec FIN)
      with KB ECA UMEM' have "S' \<inter> S\<^sub>b = {}" by blast
      moreover have "sub_mdp_of S' K' S\<^sub>b K\<^sub>b"
        using mdp_def.ec_subset_of_mec[OF ECA MECB] UMEM USB SUBA sub_mdp_of_order FIN by blast
      moreover obtain v where "v \<in> S'" using mdp_def.mec_is_non_empty[OF NE MECS] by blast
      ultimately show ?thesis by(auto dest: sub_mdp_ofD1)
    next
      case ksub
      hence SEQ: "S' = S\<^sub>a" and KSUB: "(\<exists>u\<in>S'. K' u \<subset> K\<^sub>a u)" by auto
      moreover then obtain u a where UMEM': "u \<in> S'" and UMEM: "u \<in> S\<^sub>a" and AMEM: "a \<in> K\<^sub>a u" and ANMEM: "a \<notin> K' u"
        by blast
      moreover have "u \<in> S\<^sub>2" using UMEM ec_sub_mdp_ofD1[OF ECA] 
        by blast
      moreover have AS: "a \<subseteq> S\<^sub>a"
        by (meson ECA UMEM AMEM mdp_def.all_policies_in_ec subset_iff)
      moreover have "a \<in> K\<^sub>2 u"
        using ec_sub_mdp_ofD2[OF ECA] UMEM AMEM by blast
      ultimately have AK1: "a \<in> K\<^sub>1 u" using KN
        by fastforce
  
      with ANMEM have PSUBI: "psub_mdp_of S' K' S' (K'(u := insert a (K' u)))"
         unfolding psub_mdp_of_def sub_mdp_of_def not_eq_mdp_def by (auto simp: UMEM') 
      moreover have "mdp_def.is_ec S\<^sub>1 K\<^sub>1 S' (K'(u := insert a (K' u)))"
        apply(rule mdp_def.is_ec_insert_transition)
        subgoal by (simp add: \<open>mdp_def.is_ec S\<^sub>1 K\<^sub>1 S' K'\<close>)
        subgoal using AK1 by simp
        subgoal using AS by (simp add: SEQ)
        done
      ultimately show ?thesis using MECS unfolding mdp_def.is_mec_def
        by blast
    qed
  qed
  
  lemma ec_of_sub_mdp: 
    "mdp_def.is_ec S\<^sub>1 K\<^sub>1 S\<^sub>a K\<^sub>a \<Longrightarrow> sub_mdp_of S\<^sub>2 K\<^sub>2 S\<^sub>1 K\<^sub>1 \<Longrightarrow> sub_mdp_of S\<^sub>a K\<^sub>a S\<^sub>2 K\<^sub>2 \<Longrightarrow> mdp_def.is_ec S\<^sub>2 K\<^sub>2 S\<^sub>a K\<^sub>a"
    unfolding mdp_def.is_ec_def mdp_def.sub_mdp_def by auto
  
  lemma mec_of_sub_mdp:
    assumes MEC: "mdp_def.is_mec S\<^sub>1 K\<^sub>1 S\<^sub>a K\<^sub>a"
    and SUB1: "sub_mdp_of S\<^sub>2 K\<^sub>2 S\<^sub>1 K\<^sub>1"
    and SUB2: "sub_mdp_of S\<^sub>a K\<^sub>a S\<^sub>2 K\<^sub>2"
    shows"mdp_def.is_mec S\<^sub>2 K\<^sub>2 S\<^sub>a K\<^sub>a"
  proof -
    note EC = ec_of_sub_mdp[OF mdp_def.mec_is_ec[OF MEC] SUB1 SUB2]
    moreover have "\<nexists>S'' K''. mdp_def.is_ec S\<^sub>2 K\<^sub>2 S'' K'' \<and> psub_mdp_of S\<^sub>a K\<^sub>a S'' K''"
    proof(rule notI)
      assume "\<exists>S'' K''. mdp_def.is_ec S\<^sub>2 K\<^sub>2 S'' K'' \<and> psub_mdp_of S\<^sub>a K\<^sub>a S'' K''"
      then obtain S'' K'' where "mdp_def.is_ec S\<^sub>2 K\<^sub>2 S'' K''" and PSUB: "psub_mdp_of S\<^sub>a K\<^sub>a S'' K''"
        by blast
      hence "mdp_def.is_ec S\<^sub>1 K\<^sub>1 S'' K''" 
        using SUB1 is_ec_sub_mdp by blast
      hence "\<not>mdp_def.is_mec S\<^sub>1 K\<^sub>1 S\<^sub>a K\<^sub>a"
        using PSUB mdp_def.sup_ec_not_mec by blast
      with MEC show False by blast
    qed
    ultimately show ?thesis 
      unfolding mdp_def.is_mec_def by presburger
  qed
  
  
  context mdp
  begin
  
    lemma closed_mdp_sub_mdp_is_mdp: "closed_mdp S' K' \<Longrightarrow> sub_mdp S' K' \<Longrightarrow> S' \<noteq> {} \<Longrightarrow> mdp S' K'"
      apply(frule sub_mdp_finite)
      apply(frule sub_mdp_subset_S)
      unfolding mdp_def 
      by (auto simp: closed_mdp_def in_mono)
  
    lemma ec_is_mdp: "is_ec S' K' \<Longrightarrow> S' \<noteq> {} \<Longrightarrow> mdp S' K'"
      apply(rule ec_closed_mdp[THEN closed_mdp_sub_mdp_is_mdp], assumption)
      apply(erule ec_sub_mdp)
      apply assumption
      done
  
    lemma mec_is_mdp: "is_mec S' K' \<Longrightarrow> mdp S' K'"
      apply(frule mec_is_ec)
      apply(drule mdp_mec_is_non_empty)
      using ec_is_mdp by simp
  end
  
  
  context Finite_MDP
  begin
  
  
    lemma le_imp_sub_mdp: "\<phi> \<le> M \<Longrightarrow> sub_mdp (states \<phi>) (K_actions \<phi>)"
      unfolding sub_mdp_def sub_mdp_of_def le_mdpc_iff by (fastforce simp: K_actions_mem)
  
    lemma closed_mdpc_eq_closed_mdp:"closed_mdpc \<phi> \<longleftrightarrow> closed_mdp (states \<phi>) (K_actions \<phi>)"
      unfolding closed_mdp_def by (force simp: closed_mdpcD closed_mdpc_def mdp_def.Et_\<alpha>_mem K_actions_mem
        dest: en_states subst[OF en_Et_\<alpha>, where P="(\<lambda>x. (\<in>) _ x)"])
  
    lemma sc_struc: "sc \<phi> \<longleftrightarrow> states \<phi> \<times> states \<phi> \<subseteq> (mdp_def.Et_\<alpha> (states \<phi>) (K_actions \<phi>))\<^sup>*"
      unfolding sc_def by (auto simp: en_Et_\<alpha>)
  
    lemma ec_eq_is_ec: "sub_mdp (states \<phi>) (K_actions \<phi>) \<Longrightarrow> \<phi> \<noteq> \<bottom> \<Longrightarrow> ec \<phi> \<longleftrightarrow> is_ec (states \<phi>) (K_actions \<phi>)"
      unfolding ec_def is_ec_def by (auto simp: closed_mdpc_eq_closed_mdp eq_bot_iff_states sc_struc)
  
    (*TODO: potentially, we do not even need the K_actions since we are only interested in the states of the mecs*)
    lemma mec_eq_is_mec: "\<phi> \<le>\<^sub>M M \<Longrightarrow> mec M \<phi> \<longleftrightarrow> is_mec (states \<phi>) (K_actions \<phi>)"
    proof(rule iffI)
      assume A: "mec M \<phi>"
  
      hence EC: "is_ec (states \<phi>) (K_actions \<phi>)"
        unfolding mec_def apply clarsimp
        apply(subst(asm) ec_eq_is_ec)
        subgoal by(erule le_imp_sub_mdp)
        subgoal
          using M_neq_bot A mec_bot_imp_bot by blast
        subgoal
          by assumption
        done
  
      {
        fix S' K'
        assume ECP: "is_ec (states \<phi>) (K_actions \<phi>)" 
        and EC: "is_ec S' K'" 
        and PSUB: "psub_mdp_of (states \<phi>) (K_actions \<phi>) S' K'"
  
        have "sub_struc_of M S' K'"
          using EC ec_sub_mdp sub_struc_of_eq_sub_mdp_of by blast
        then obtain M' where LE: "M' \<le>\<^sub>M M" and SDEF: "S' = states M'" and KDEF: "\<forall>u\<in>S'. K' u = K_actions M' u"
          using mdpc_from_sub_struc[of M S' K'] by blast
        hence MAX: "(\<And> u a p. u \<in> S' \<Longrightarrow> a \<in> K' u \<Longrightarrow> p \<in> actions M u \<Longrightarrow> a = set_pmf p \<Longrightarrow> p \<in> actions M' u)"
          unfolding max_le_mdpc_def by (fastforce simp: K_actions_mem)
  
        {
          fix u a
          assume US: "u \<in> states \<phi>" and AA: "a \<in> actions \<phi> u"
          hence "set_pmf a \<in> K_actions \<phi> u"
            by (auto simp: K_actions_mem)
          with PSUB have MEM: "set_pmf a \<in> K_actions M' u" 
            by (metis KDEF Set.basic_monos(7) US psub_mdp_of_subD sub_mdp_of_def)
          have "a \<in> actions M' u"
            apply(rule MAX[of _ "set_pmf a"])
            subgoal using SDEF MEM by (auto simp: K_actions_mem intro!: in_states)
            subgoal using KDEF MEM \<open>u \<in> S'\<close> by blast
            subgoal by (meson A AA in_mono le_mdpc_iff mec_le)
            subgoal by (rule refl)
            done
  
        } note AUX = this
  
  
        have LE':"\<phi> \<le> M'"
          apply(rule le_mdpcI)
          subgoal by (metis PSUB SDEF psub_mdp_of_subD sub_mdp_of_def)
          subgoal for u
            using AUX by blast
          done
  
        have EC': "ec M'" 
          by (metis EC KDEF SDEF ec_bot ec_eq_is_ec eq_mdpI mdp_def.ec_sub_mdp mdp_def.eq_mdp_ec)
  
        have False
          apply(cases rule: psub_mdp_of_state_cases[OF PSUB])
          subgoal 
            using A LE LE' EC' SDEF unfolding mec_def max_le_mdpc_def by fast
          subgoal
            using A LE LE' EC' SDEF KDEF unfolding mec_def max_le_mdpc_def by fast
          done
      }
      
      with EC show "is_mec (states \<phi>) (K_actions \<phi>)"
        unfolding is_mec_def by blast
    next
      assume A: "is_mec (states \<phi>) (K_actions \<phi>)"
      and LE: "\<phi> \<le>\<^sub>M M"
  
      from A have EC: "ec \<phi>"
        apply(subst ec_eq_is_ec)
        apply(erule mec_sub_mdp)
        apply(simp add: eq_bot_iff_states mdp_mec_is_non_empty)
        apply(erule mec_is_ec)
        done
  
      have B\<phi>: "\<phi> \<noteq> \<bottom>"
        using A mdp_mec_is_non_empty states_bot by blast
  
      {
        fix \<psi>
        assume A1: "\<psi> \<le> M" and A2: "ec \<psi>" and A3: "\<phi> \<le> \<psi>"
        moreover have S1: "sub_mdp_of (states \<psi>) (K_actions \<psi>) (states M) (K_actions M)"
          and "\<psi> \<noteq> \<bottom>" 
          and S2: "sub_mdp_of (states \<phi>) (K_actions \<phi>) (states \<psi>) (K_actions \<psi>) "
          using calculation by(auto simp: B\<phi> dest: le_imp_sub_mdp_of le_bot)
        ultimately have EC: "is_ec (states \<psi>) (K_actions \<psi>)"
          by(auto simp: ec_eq_is_ec[unfolded sub_mdp_def])
  
        have "\<phi> = \<psi>"
          apply(rule max_le_eq_mdp_eq)
          subgoal
            apply(rule le_trans_infer_max_le)
            using A3 apply blast
            using A1 apply blast
            using LE apply blast
            done
          subgoal
            using A unfolding is_mec_def 
            using EC S2 sub_mdp_not_psub_eq by blast
          done
      }
  
      thus "mec M \<phi>"
        unfolding mec_def
        by(auto simp: EC max_le_mdpc_le[OF LE])
    qed
  
  
    lemma mec_set_struc_alt: "mec_set_struc = mec_decomp"
      unfolding mec_set_struc_def mec_decomp_def 
      apply safe
      subgoal for _ S K 
        apply(frule mec_sub_mdp)
        unfolding sub_mdp_def sub_struc_of_eq_sub_mdp_of[symmetric] mec_eq_is_mec
        apply(erule mdpc_from_sub_struc) 
        subgoal for M'
          apply(rule exI[where x=M'])
          apply(rule conjI)
          by (auto elim: eq_mdpI [THEN eq_mdp_mec, rotated 2] simp: mec_eq_is_mec)
        done
      subgoal
        apply(frule mec_max_le)
        by(auto simp: mec_eq_is_mec) 
      done
  
  
  end
  
  
  
  subsection \<open>SCC and BSCC\<close>
  
  text \<open>
    Bottom SCCs (BSCCs) play a crucial role in our formalization, because in every iteration
    the BSCCs are also MECs. When we identify a MEC we remove it, creating new BSCCs in the next
    iteration which are therefore also MECs. Since every graph has at least one BSCC, we also
    guarantee termination using this argument.
  \<close>
  
  lemma closed_scc_bscc: "is_scc (mdp_def.Et_\<alpha> S' K') S' \<Longrightarrow> closed_mdp S' K' \<Longrightarrow> is_bottom_scc (mdp_def.Et_\<alpha> S' K') S'"
    unfolding is_bottom_scc_def closed_mdp_def mdp_def.Et_\<alpha>_def sub_mdp_of_def
    by fast
  
  lemma closed_scc_sub_bscc: "is_scc (mdp_def.Et_\<alpha> S' K') S'' \<Longrightarrow> S' \<subseteq> S'' \<Longrightarrow> closed_mdp S' K' \<Longrightarrow> is_bottom_scc (mdp_def.Et_\<alpha> S' K') S''"
    unfolding is_bottom_scc_def closed_mdp_def mdp_def.Et_\<alpha>_def sub_mdp_of_def
    by blast
  
  lemma closed_scc_sup_bscc: "is_scc (mdp_def.Et_\<alpha> S' K') S'' \<Longrightarrow> S'' \<subseteq> S' \<Longrightarrow> closed_mdp S'' K' \<Longrightarrow> is_bottom_scc (mdp_def.Et_\<alpha> S' K') S''"
    unfolding is_bottom_scc_def closed_mdp_def mdp_def.Et_\<alpha>_def sub_mdp_of_def
    by fast
  
  context mdp_def
  begin
  
    lemma bscc_closed: "sub_mdp S' K' \<Longrightarrow> is_bottom_scc Et_\<alpha> S' \<Longrightarrow> closed_mdp S' K'"
      unfolding closed_mdp_def is_bottom_scc_def
      apply clarsimp
      apply(frule sub_mdp_actions_in_sup)
      apply assumption+
      subgoal for u a v
        apply(frule mdp_def.Et_\<alpha>I[of _ _ v a])
        apply assumption+
        apply(drule sub_mdp_sub_Et_\<alpha>[THEN set_mp])
        apply assumption 
        by blast
      done
  
    lemma bscc_edges_restr:
      fixes S'
      defines "K' \<equiv> (make_sub_mdp S')"
      assumes BSCC: "is_bottom_scc Et_\<alpha> S'" 
      and SSUB: "S' \<subseteq> S"
      shows "Restr Et_\<alpha> S' = mdp_def.Et_\<alpha> S' K'"
    proof -
      from SSUB have SUB: "sub_mdp S' K'" unfolding K'_def by simp
  
      {
        fix u v
        assume A: "(u, v) \<in> mdp_def.Et_\<alpha> S' K'"
        hence "u \<in> S'" unfolding mdp_def.Et_\<alpha>_def K'_def by force
        moreover have "v \<in> S'" 
          using A bscc_not_leavingD[OF BSCC _ calculation] in_mono[OF sub_mdp_sub_Et_\<alpha>[OF SUB]] 
          by presburger
        ultimately have "u \<in> S'" and "v \<in> S'" by auto
      } note AUX1 = this[unfolded K'_def]
  
      {
        fix u v
        assume A: "(u,v) \<in> Et_\<alpha>" 
        and U: "u \<in> S'" 
        and C: "(u, v) \<notin> mdp_def.Et_\<alpha> S' K'"
        have False
          by (metis A C K'_def U mdp_def.Et_\<alpha>_mem mdp_def.make_sub_mdp_K)
      } 
  
      hence AUX2: "(u, v) \<in> Et_\<alpha> \<Longrightarrow> u \<in> S' \<Longrightarrow> v \<in> S' \<Longrightarrow> (u, v) \<in> mdp_def.Et_\<alpha> S' (make_sub_mdp S')" for u v
        unfolding K'_def by presburger
  
      show ?thesis
        by (auto simp: sub_mdp_sub_Et_\<alpha>[OF SUB, THEN in_mono] K'_def dest: AUX1 AUX2) 
    qed
  
  
    lemma bscc_sc:
      fixes S'
      defines "K' \<equiv> (make_sub_mdp S')"
      assumes BSCC: "is_bottom_scc Et_\<alpha> S'" 
      and SSUB: "S' \<subseteq> S"
      shows "S' \<times> S' \<subseteq> (mdp_def.Et_\<alpha> S' K')\<^sup>*"
    proof safe
      fix u v
      assume UK: "u \<in> S'" and VK: "v \<in> S'"
      with BSCC have "(u,v) \<in> Et_\<alpha>\<^sup>*" unfolding is_bottom_scc_def
        by (meson is_scc_connected)
      then show "(u,v) \<in> (mdp_def.Et_\<alpha> S' K')\<^sup>*" using UK VK 
      proof(induction rule: rtrancl.induct)
        case (rtrancl_refl u)
        then show ?case by blast
      next
        case (rtrancl_into_rtrancl u v w)
        moreover from rtrancl_into_rtrancl.hyps(1) rtrancl_into_rtrancl.prems(1) have VMEM: "v \<in> S'"
          apply(induction rule: rtrancl_induct)
          using BSCC by(auto simp: is_bottom_scc_def)
        ultimately have "(v,w) \<in> Restr Et_\<alpha> S'" by blast
        hence "(v,w) \<in> mdp_def.Et_\<alpha> S' K'" 
          unfolding bscc_edges_restr[OF BSCC SSUB] K'_def .
        then show ?case using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems VMEM by force
      qed
    qed
  
    lemma bscc_is_ec: 
      fixes S'
      defines "K' \<equiv> (make_sub_mdp S')"
      assumes BSCC: "is_bottom_scc Et_\<alpha> S'" 
      and SSUB: "S' \<subseteq> S" 
      shows "is_ec S' K'" 
    proof -
      have SUB: "sub_mdp S' K'" 
        using make_sub_mdp_sub_mdp[OF SSUB] K'_def 
        by argo
      moreover have CL: "closed_mdp S' K'" 
        using bscc_closed[OF SUB BSCC] .
      moreover have SC: "S' \<times> S' \<subseteq> (mdp_def.Et_\<alpha> S' K')\<^sup>*" 
        using bscc_sc[OF BSCC SSUB] unfolding K'_def by simp
      moreover have "S' \<noteq> {}"
        using BSCC bssc_non_empty' by blast
      ultimately show ?thesis unfolding is_ec_def by simp
    qed
  
    lemma ec_in_scc:
      assumes SCC: "is_scc Et_\<alpha> scc" 
      and EC: "is_ec S' K'" 
      and OV: "scc \<inter> S' \<noteq> {}" 
      shows "S' \<subseteq> scc"
    proof safe
      fix u
      assume US': "u \<in> S'" 
      from OV obtain v where VS': "v \<in> S'" and VSCC: "v \<in> scc" by blast
      with US' EC have "(u,v) \<in> (mdp_def.Et_\<alpha> S' K')\<^sup>*" and "(v,u) \<in> (mdp_def.Et_\<alpha> S' K')\<^sup>*" 
        unfolding is_ec_def by blast+
      moreover have "(mdp_def.Et_\<alpha> S' K')\<^sup>* \<subseteq> Et_\<alpha>\<^sup>*" 
        by(rule rtrancl_mono; rule sub_mdp_sub_Et_\<alpha>; rule ec_sub_mdp; rule EC)
      ultimately have "(u,v) \<in> Et_\<alpha>\<^sup>*" and "(v,u) \<in> Et_\<alpha>\<^sup>*" by blast+
      thus "u \<in> scc"
        by(auto intro: is_scc_closed[OF SCC VSCC])
    qed
  
  
    lemma scc_of_ec:
      assumes EC: "is_ec S' K'"
      and NE: "S' \<noteq> {}"
      obtains S\<^sub>c where "is_scc Et_\<alpha> S\<^sub>c" and "S' \<subseteq> S\<^sub>c"  
    proof -
      from NE obtain v where VS: "v \<in> S'" using mec_non_empty
        by fastforce
      then obtain S\<^sub>c where SCC: "is_scc Et_\<alpha> S\<^sub>c" and VSC: "v \<in> S\<^sub>c" 
        by (meson is_scc_ex1)
      moreover have "S' \<subseteq> S\<^sub>c" using ec_in_scc[OF SCC EC] VS VSC
        by blast
      ultimately show ?thesis 
        by (simp add: that)
    qed
  
  
    lemma scc_of_mec: 
      assumes MEC: "is_mec S' K'"
      and NE: "S \<noteq> {}"
      obtains S\<^sub>c where "is_scc Et_\<alpha> S\<^sub>c" and "S' \<subseteq> S\<^sub>c"
    proof -
      from NE MEC have "S' \<noteq> {}" 
        by (metis mdp_def.mec_non_empty)
      thus ?thesis using that scc_of_ec[OF mec_is_ec[OF MEC]] by blast 
    qed
  
  end
  
  context mdp
  begin

    lemmas ex_bscc_mdp_E = finite_reach[THEN ex_bscc]
  
    lemma ex_bscc_mdp: 
      assumes NE: "S \<noteq> {}" 
      shows "\<exists>V'\<subseteq>S. is_bottom_scc Et_\<alpha> V'"
      proof(cases "Et_\<alpha> = {}")
        case True
        moreover from NE obtain v where VS: "v \<in> S"
          by fastforce
        ultimately have SCC: "is_scc Et_\<alpha> {v}" unfolding Graph.is_scc_def
          by fastforce
        show ?thesis apply(rule exI[where ?x="{v}"])
          using VS SCC by (auto simp: is_bottom_scc_def True)
      next
        case False
        from NE obtain v where VS: "v \<in> S"
          by fastforce
        show ?thesis using ex_bscc_mdp_E[OF VS] reach_in_S[OF VS] by blast
      qed
(*  
    lemma ec_sc:
      assumes "is_ec S' K'" 
      shows "(mdp_def.Et_\<alpha> S' K')\<^sup>* = (S' \<times> S')\<^sup>="
    proof(cases "S' = {}")
      case True
      then show ?thesis by(auto simp: mdp_def.Et_\<alpha>_def)
    next
      case False
  
      from assms have SUB: "sub_mdp S' K'" and CL: "closed_mdp S' K'" and SC: "(S'\<times>S') \<subseteq> (mdp_def.Et_\<alpha> S' K')\<^sup>*"
        unfolding is_ec_def by auto
      from assms False have MDP: "mdp S' K'"
        using ec_is_mdp by blast
  
      show ?thesis
      proof safe
        fix u v
        assume "(u,v) \<in> (mdp_def.Et_\<alpha> S' K')\<^sup>*" and "u \<noteq> v"
        thus "u \<in> S'" unfolding mdp_def.Et_\<alpha>_def
          apply(induction rule: converse_rtrancl_induct)
          apply force 
          by blast
      next
        fix u v
        assume A: "(u,v) \<in> (mdp_def.Et_\<alpha> S' K')\<^sup>*" and "u \<noteq> v"
        thus "v \<in> S'"
          apply(induction rule: rtrancl_induct) apply simp
          apply(drule mdp.edge_connects_states(2)[OF MDP]; assumption)
          done 
      next
        fix u v
        assume A: "u \<in> S'" "v \<in> S'"
        hence "(u,v) \<in> (mdp_def.Et_\<alpha> S' K')\<^sup>*" using SC by fast
        thus "(u,v) \<in> (mdp_def.Et_\<alpha> S' K')\<^sup>*" apply -
          apply(erule rtrancl_eq_trancl_cases)
          by auto
      qed 
    qed
*)
    lemma subset_non_empty: "A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {}" by auto
  
    lemma bscc_is_mec:     
      fixes S''
      defines "K'' \<equiv> (make_sub_mdp S'')"
      assumes BSCC: "is_bottom_scc Et_\<alpha> S''" 
      and SSUB: "S'' \<subseteq> S" 
      shows "is_mec S'' K''" 
    proof(rule ccontr)
      assume "\<not> is_mec S'' K''"
      with bscc_is_ec[OF BSCC SSUB] obtain S' K' where NEQ: "(S'' \<noteq> S' \<or> (\<exists>u\<in>S''. K' u \<noteq> K'' u))" and EC': "is_ec S' K'" and SUB': "sub_mdp_of S'' K'' S' K'" 
        unfolding is_mec_def K''_def psub_mdp_of_def not_eq_mdp_def
        by (metis Un_iff)
      then have SS': "S'' \<subseteq> S'" unfolding sub_mdp_of_def by auto
      then consider (sub) "S'' \<subset> S'" | (eq) "S'' = S'" by blast
      thus False
      proof cases
        case sub
        moreover from BSCC have SNEMP: "S'' \<noteq> {}" unfolding is_bottom_scc_def
          by fastforce
        ultimately obtain u v where UMEM: "u \<in> S''" and VMEM: "v \<in> S' - S''" by blast
        hence UVE': "(u, v) \<in> (mdp_def.Et_\<alpha> S' K')\<^sup>*" using EC' sub unfolding is_ec_def by blast
        hence UVE: "(u, v) \<in> Et_\<alpha>\<^sup>*" using sub_mdp_sub_Et_\<alpha>[OF ec_sub_mdp[OF EC'], THEN rtrancl_mono] set_mp 
          by blast
        moreover have "mdp_def.Et_\<alpha> S' K' \<subseteq> S' \<times> S'"  
          by (simp add: EC' ec_is_mdp mdp.Et_\<alpha>_subset_states subset_non_empty[OF SS' SNEMP])
        ultimately obtain u2 v2 where "u2 \<in> S''" and "v2 \<in> S' - S''" and "(u2, v2) \<in> mdp_def.Et_\<alpha> S' K'" 
          using ex_transitive_transition[OF UVE' SS' UMEM VMEM] by blast
        then show ?thesis  
          by (meson BSCC DiffD2 EC' bscc_not_leavingD ec_sub_mdp in_mono sub_mdp_sub_Et_\<alpha>)
      next
        case eq
        with NEQ obtain u a where "a \<in> K' u" and "a \<notin> K'' u" and US: "u \<in> S''"
          by (metis SUB' sub_mdp_of_def subsetI subset_antisym)
        hence "K'' u = {}" 
          using EC' K''_def ec_sub_mdp eq sub_mdp_subset_K 
          by (metis make_sub_mdp_def sub_mdp_actions_in_sup)
        hence "u \<notin> S''" unfolding K''_def make_sub_mdp_def 
          by (metis EC' \<open>a \<in> K' u\<close> emptyE eq mdp_def.ec_sub_mdp set_empty2 sub_mdp_actions_in_sup)
        then show ?thesis using US
          by simp
      qed
    qed
  
  
    
  end
  
  
  section \<open>Abstract Algorithm\<close>
  
  
  subsection \<open>Specification\<close>
  
  locale mec_algo_defs = Finite_MDP_defs M\<^sub>0 for M\<^sub>0
  begin
  
    text \<open>
      The algorithm calculates a list containing all MECs while not changing the
      input statespace.
    \<close>
                                                  
    definition "compute_MEC_spec \<equiv> SPEC (\<lambda>D. set D = mec_decomp \<and> distinct D)"
  
  end
  
  locale mec_algo = Finite_MDP M\<^sub>0 + mec_algo_defs M\<^sub>0 for M\<^sub>0
  
  
  
  subsection \<open>Invariant\<close>
  
  
  text \<open>
    Our algorithm iteratively identfies MECs and removes them.
  
    Terminology: The input MDP consists of a set of input states \<open>(states M\<^sub>0)\<close> and an input kernel \<open>K\<^sub>0\<close>.
    The loop state is a list of MECs \<open>M\<close>, and the part of the input MDP over which we have not 
    identified any MECs yet. We refer to that part as the "current" MDP with the current states \<open>S\<close>
    and the current kernel \<open>K\<close>.\<close>
  
  locale compute_MEC_invar_def =
    fixes M\<^sub>0::"'v mdpc" and MDSKZ::"'v mec_abs_state"
  begin
  
    definition "M = (\<lambda> (M,D,S,K,Z). M) MDSKZ" \<comment>\<open>Original MDP\<close>
    definition "D = (\<lambda> (M,D,S,K,Z). D) MDSKZ" \<comment>\<open>Set of discovered MECs\<close>
    definition "S = (\<lambda> (M,D,S,K,Z). S) MDSKZ" \<comment>\<open>Set of states in MDP\<close>
    definition "K = (\<lambda> (M,D,S,K,Z). K) MDSKZ" \<comment>\<open>Kernel: Set edges of MDP\<close>
    definition "Z = (\<lambda> (M,D,S,K,Z). Z) MDSKZ" \<comment>\<open>Kernel: Set edges of MDP\<close>
  
  end
  
  lemma abs_sel_simps [simp]:
    "compute_MEC_invar_def.M (M,D,S,K,Z) = M"
    "compute_MEC_invar_def.D (M,D,S,K,Z) = D"
    "compute_MEC_invar_def.S (M,D,S,K,Z) = S"
    "compute_MEC_invar_def.K (M,D,S,K,Z) = K"
    "compute_MEC_invar_def.Z (M,D,S,K,Z) = Z"
    unfolding compute_MEC_invar_def.S_def compute_MEC_invar_def.K_def compute_MEC_invar_def.M_def 
      compute_MEC_invar_def.D_def compute_MEC_invar_def.Z_def
    by auto
  
  text \<open>
    The invariant of the MEC algorithm is defined as a locale. The loop state in the main loop consists
    of: \<open>M\<close> The original MDP, \<open>D\<close> The list of MECs, \<open>S\<close> the states of the current MDP over which we 
    have not identified a MEC yet and \<open>K\<close> the kernel of that MDP\<close>
  
  locale compute_MEC_invar = compute_MEC_invar_def M\<^sub>0 MDSKZ + Finite_MDP M\<^sub>0 for M\<^sub>0::"'v mdpc" and MDSKZ::"'v mec_abs_state" +
    assumes S_D_disj: "S \<inter> \<Union>(set D) = {}" \<comment> \<open>S and D are disjoint\<close>
    and S_D_S0: "states M\<^sub>0 = \<Union>(set D) \<union> S" \<comment> \<open>S and D together form the input statespace\<close>
    and pairwise_disjnt_D: "pairwise disjnt (set D)" \<comment> \<open>D is pairwise disjoint\<close>
    and distinct_D: "distinct D" \<comment> \<open>D is distinct\<close>
  
    assumes mec_done_or_in_SK: "is_mec S' K' \<Longrightarrow> S' \<in> set D \<or> sub_mdp_of S' K' S K" \<comment> \<open>Each MEC is either identified or still in the current MDP\<close>
    and D_of_mecs: "S' \<in> set D \<Longrightarrow> \<exists>K'. is_mec S' K'" \<comment> \<open>Identified MECs are MECs in the input graph\<close>
    and preserve_mec: "S \<noteq> {} \<Longrightarrow> mdp_def.is_mec S K S' K' \<Longrightarrow> is_mec S' K'" \<comment> \<open>A MEC in the current MDP is a MEC in the input MDP.\<close>
    
    assumes is_mdp: "mdp S K" \<comment> \<open>The current MDP satisfies the \<open>mdp\<close> locale\<close>
    and is_sub_mdp: "sub_struc_of M\<^sub>0 S K" \<comment> \<open>The current MDP is a sub MDP of the input MDP\<close>
    and M0: "M = M\<^sub>0"
  
    assumes pres_max_K: "scc_list C S K \<Longrightarrow> a \<in> K_actions M\<^sub>0 u \<Longrightarrow> S' \<in> set C \<Longrightarrow> u \<in> S' \<Longrightarrow> \<forall>v\<in>a. v \<in> S' \<Longrightarrow> a \<in> K u"
      \<comment> \<open>If an edge of the input kernel remains within an SCC, it is also in the current kernel\<close>
  begin
  
    lemma emp_not_in_D: "{} \<notin> set D"
      apply(rule notI)
      apply(drule D_of_mecs)
      using mdp_mec_non_empty by auto
  
    lemma S_D_pairwise_disj: "X \<in> set D \<Longrightarrow> S \<inter> X = {}"
      using S_D_disj by fast
  
    lemma mem_D_nonempty: "X \<in> set D \<Longrightarrow> X \<noteq> {}"
      using emp_not_in_D by fast
  
    lemma subset_states: "S \<subseteq> states M\<^sub>0"
      using is_sub_mdp unfolding  sub_struc_of_def by simp
  
    lemma subset_transitions: "\<forall>u\<in>S. K u \<subseteq> K_actions M\<^sub>0 u"
      using is_sub_mdp unfolding sub_struc_of_def K_actions_def by argo
  
    lemma finite_S[simp]: "finite S"
      apply(cases "S = {}")
      apply simp
      using mdp.finite[OF is_mdp] .
  
    lemma closed_mdp': "closed_mdp S K"
      apply(cases "S = {}")
      apply simp
      using mdp.K_closed_under_S[OF is_mdp] .
  
    lemma scc_list_length_C_bound_S0: 
      assumes SCC: "scc_list C S K"
      shows "length C \<le> card (states M\<^sub>0)"
      using scc_list_length_C_bound[OF SCC finite_S] card_mono[OF finite subset_states]
      by fastforce
  
    lemma D_sub_S0: "\<Union>(set D) \<subseteq> (states M\<^sub>0)" 
      by (meson D_of_mecs Union_least mec_sub_mdp sub_mdp_subset_S)
  
    lemma S_D_size_bound: "card S + length D \<le> card (states M\<^sub>0)"
    proof -
  
      have DSM: "disjnt ((\<lambda>x. {x}) ` S) (set D)"
        unfolding disjnt_def
        using S_D_pairwise_disj by blast
  
      have "card ((\<lambda>x. {x}) ` S) = card S"
        apply(rule card_image)
        by auto
      moreover have "card (set D) = length D" 
        using distinct_D distinct_card by blast
        
  
      ultimately have "card (((\<lambda>x. {x}) ` S) \<union> set D) = card S + length D"
        apply(subst card_Un_disjnt)
        by (auto simp: DSM)
      moreover have "card (((\<lambda>x. {x}) ` S) \<union> set D) \<le> card (states M\<^sub>0)"
        apply(rule disj_finite_set_of_subsets_card_bound)
        subgoal apply(rule pairwise_disjnt_Un)
          subgoal by (simp add: pairwise_imageI)
          subgoal using pairwise_disjnt_D .
          subgoal using S_D_pairwise_disj disjnt_iff by blast
          done
        subgoal
          by (metis D_of_mecs Sup_le_iff UN_singleton UnE mec_sub_mdp_ofD1 subset_states)
        subgoal by blast
        subgoal
          using emp_not_in_D by blast
        done
      ultimately show ?thesis by presburger
  
    qed
  
    lemma length_V_bound: "scc_list C S K \<Longrightarrow> set V = {S' \<in> set C. closed_mdp S' K} \<Longrightarrow> distinct V \<Longrightarrow> length V \<le> card S"
      by (metis (no_types, lifting) List.finite_set card_length card_mono distinct_card dual_order.trans finite_S mem_Collect_eq scc_list_length_C_bound subset_code(1))
  
    corollary length_V_D_bound: "scc_list C S K \<Longrightarrow> D' = D \<Longrightarrow> set V = {S' \<in> set C. closed_mdp S' K} \<Longrightarrow> distinct V \<Longrightarrow> length D' + length V \<le> card (states M\<^sub>0)"
      using S_D_size_bound dual_order.trans length_V_bound by fastforce
  
    lemma mecs_states_M\<^sub>0: "S = {} \<Longrightarrow> \<Union>(set D) = (states M\<^sub>0)"
      using S_D_S0 by blast
  end
  
  subsection \<open>Abstract Algorithm Operations\<close>
  
  text \<open>The abstract algorithm consists of three operations: 1) Compute the SCC decomposition
    (\<open>compute_sccs\<close>), identify the SCCs that are MECs (\<open>identify_mecs\<close>) and remove the MECs from
    the MDP as well as transitions in the remaining kernel that leave their SCC (\<open>cull_graph\<close>).\<close>
  
  
  lemma (in mdp_def) bscc_in_identify_mecs: 
    assumes BSCC: "is_bottom_scc (mdp_def.Et_\<alpha> S K) S'"
    and SUB: "S' \<subseteq> S"
    and SCCL: "scc_list C S K"
    and VSET: "set V = {S' \<in> set C. closed_mdp S' K}"
    shows "S' \<in> set V" 
  proof -
    from SUB have "sub_mdp S' K" unfolding sub_mdp_def sub_mdp_of_def by simp
    hence "closed_mdp S' K" apply - apply(erule bscc_closed) using BSCC .
    thus ?thesis unfolding VSET using scc_list_mem[OF SCCL]
      by (fastforce simp: SUB BSCC intro!: bscc_is_sccD)
  qed
  
  lemma cull_graph_preserve_unfinished_mec_aux1: 
    assumes SP: "S' = S-\<Union>(set V)"
    and KP: "culled_edges C V K K'"
    and SCCL: "scc_list C S K"
    and MDP: "mdp S K"
    and MECA: "mdp_def.is_mec S' K' S\<^sub>a K\<^sub>a"
    and UMEM: "u \<in> S"
    and UNMEM': "u \<in> S'"
    and UNSA: "u \<notin> S\<^sub>a"
    and MEC'': "mdp_def.is_mec S K S'' K''"
    and UMEM'': "u \<in> S''"
    and VSET: "set V = {S' \<in> set C. closed_mdp S' K}"
    shows "S\<^sub>a \<inter> S'' = {}" 
  proof(rule ccontr)
  
    assume "S\<^sub>a \<inter> S'' \<noteq> {}"
    then obtain v where VSA: "v \<in> S\<^sub>a" and VS2: "v \<in> S''"
      by blast
  
    from MDP interpret mdp S K .
  
    have SDEF: "S = \<Union> (set C)"
      using SCCL scc_list_states_eq by blast
    hence SP': "S' = \<Union> (set C) - \<Union> (set V)" 
      using SP by presburger
  
    note SUB = culled_edges_sub_mdp[OF SDEF SP' KP]
  
    from SP UMEM UNMEM' have "u \<notin> \<Union>(set V)"
      by fast
    moreover obtain scc where SCC: "is_scc Et_\<alpha> scc" and SCCS: "scc \<subseteq> S" and USCC: "u \<in> scc"
      by (meson UMEM is_scc_ex scc_in_S)
    ultimately have A: "scc \<notin> set V"
      by blast
    with SP have SCCS: "scc \<subseteq> S'" unfolding cull_graph_def apply clarsimp
      by (metis (mono_tags, lifting) SCC SCCS scc_list_mem[OF SCCL] VSET in_mono is_scc_ex1 mem_Collect_eq)
      
    
  
    have SCA: "S\<^sub>a \<times> S\<^sub>a \<subseteq> Et_\<alpha>\<^sup>*" 
      using mdp_def.mec_strongly_connected_ext[OF MECA] sub_mdp_of_sub_Et_\<alpha>[OF SUB, THEN rtrancl_mono] SCCL
      by blast
    have SSCC: "S'' \<subseteq> scc" 
      by (metis IntI MEC'' SCC UMEM'' USCC ec_in_scc empty_iff mec_is_ec)
    with VS2 have "S\<^sub>a \<subseteq> scc" 
      using sc_sub_scc[OF _ VSA SCA SCC] by blast
    
    note SUB2 = mec_of_sub_mdp_is_sub[OF MECA MEC'' SUB VSA VS2]
    hence "psub_mdp_of S\<^sub>a K\<^sub>a S'' K''" using UNSA UMEM'' 
      unfolding psub_mdp_of_def not_eq_mdp_def by blast
  
    hence "\<not>mdp_def.is_ec S' K' S'' K''" using MECA unfolding mdp_def.is_mec_def
      by blast
    hence "\<not>mdp_def.sub_mdp S' K' S'' K''" 
      unfolding mdp_def.is_ec_def 
      using mec_closed_mdp[OF MEC''] mec_strongly_connected[OF MEC''] VS2 by blast
    moreover have SS': "S'' \<subseteq> S'"
      using \<open>S'' \<subseteq> scc\<close> \<open>scc \<subseteq> S'\<close> by blast
    ultimately obtain u a' where US'': "u \<in> S''" and AKU2: "a' \<in> K'' u" and AKU1: "a' \<notin> K' u" 
      unfolding mdp_def.sub_mdp_def sub_mdp_of_def by blast
    hence AKU: "a' \<in> K u" 
      using MEC'' mec_sub_mdp sub_mdp_actions_in_sup by blast
    
  
    have "a' \<in> K' u"     
      apply(rule culled_edges_K_supset[where ?X'=scc])
      using KP apply blast 
      using SDEF SP US'' SS' apply blast
      using SSCC US'' apply blast
      apply (meson AKU2 MEC'' SSCC US'' closed_mdpD mdp_def.mec_closed_mdp subsetD)
      using SCC SCCL scc_list_mem UMEM USCC scc_in_S apply blast
      using A apply linarith
      using AKU by blast 
  
    with AKU1 show False
      by blast
  qed
  
  lemma cull_graph_preserve_unfinished_mec_aux2: 
    assumes SP: "S' = S-\<Union>(set V)"
    and SCCL: "scc_list C S K"
    and MDP: "mdp S K"
    and MECA: "mdp_def.is_mec S' K' S\<^sub>a K\<^sub>a"
    and UMEM: "u \<in> S"
    and UNMEM': "u \<notin> S'"
    and MEC'': "mdp_def.is_mec S K S'' K''"
    and UMEM'': "u \<in> S''"
    and VSET: "set V = {S' \<in> set C. closed_mdp S' K}"
    shows "S\<^sub>a \<inter> S'' = {}"
  proof -
    from MDP interpret mdp S K .
  
    from SP UMEM UNMEM' have "u \<in> \<Union>(set V)"
      unfolding cull_graph_def by fast
    then obtain scc where SCC: "is_scc Et_\<alpha> scc" and SCCS: "scc \<subseteq> S" and CL: "closed_mdp scc K" and USCC: "u \<in> scc"
      unfolding identify_mecs_def using scc_list_mem[OF SCCL] VSET by auto
    hence "scc \<subseteq> \<Union>(set V)"
      unfolding identify_mecs_def using scc_list_mem[OF SCCL] VSET by blast
    with SP have "S' \<inter> scc = {}"
      unfolding cull_graph_def by auto
    hence DISJ: "S\<^sub>a \<inter> scc = {}"
      using mec_sub_mdp_ofD1[OF MECA] by fast
    
    have "is_bottom_scc Et_\<alpha> scc" 
      using closed_scc_sup_bscc[OF SCC SCCS CL] .
    hence "is_mec scc (make_sub_mdp scc)" 
      using bscc_is_mec[OF _ SCCS] by fast
    hence "eq_mdp scc (make_sub_mdp scc) S'' K''" 
      apply(rule unique_mec_per_state[OF _ MEC''])
      using USCC UMEM'' by fast
    with DISJ show ?thesis 
      using eq_mdpD1 by blast
  qed
  
  lemma cull_graph_preserve_unfinished_mec: 
    assumes SP: "S' = S-\<Union>(set V)"
    and KP: "culled_edges C V K K'"
    and SCCL: "scc_list C S K"
    and MDP: "mdp S K"
    and MECA: "mdp_def.is_mec S' K' S\<^sub>a K\<^sub>a"
    and UMEM: "u \<in> S"
    and UNMEM': "u \<notin> S\<^sub>a"
    and MEC'': "mdp_def.is_mec S K S'' K''"
    and UMEM'': "u \<in> S''"
    and VSET: "set V = {S' \<in> set C. closed_mdp S' K}"
    shows "S\<^sub>a \<inter> S'' = {}"
    apply(cases "u \<in> S'")
    subgoal using cull_graph_preserve_unfinished_mec_aux1[OF SP KP SCCL MDP MECA UMEM _ UNMEM' MEC'' UMEM''  VSET] .
    subgoal using cull_graph_preserve_unfinished_mec_aux2[OF SP SCCL MDP MECA UMEM _ MEC'' UMEM'' VSET] .
    done
  
  lemma(in mdp) cull_graph_scc:
    assumes SP: "S' = S-\<Union>(set V)"
    and KP: "culled_edges C V K K'"
    and SCCL: "scc_list C S K"
    and SCC: "is_scc (mdp_def.Et_\<alpha> S' K') scc'"
    and VSET: "set V = {S' \<in> set C. closed_mdp S' K}"
    obtains scc where "scc' \<subseteq> scc" and "is_scc (mdp_def.Et_\<alpha> S K) scc"
  proof -
  
    have SDEF: "S = \<Union> (set C)"
      using SCCL scc_list_states_eq by blast
    hence SP': "S' = \<Union> (set C) - \<Union> (set V)" 
      using SP by presburger
  
    note SUB = culled_edges_sub_mdp[OF SDEF SP' KP]
  
    from that show ?thesis using sub_mdp_sub_scc[OF SUB SCC] by blast
  
  qed
  
  
  lemma (in mdp) cull_graph_preserve_mec_transitions: 
    assumes SP: "S' = S-\<Union>(set V)"
    and KP: "culled_edges C V K K'"
    and SCCL: "scc_list C S K"
    and NE: "S' \<noteq> {}"
    and MECA: "mdp_def.is_mec S' K' S\<^sub>a K\<^sub>a"
    and USA: "u \<in> S\<^sub>a"
    and AKU: "a \<in> K u"
    and ASA: "a \<subseteq> S\<^sub>a"
    and VSET: "set V = {S' \<in> set C. closed_mdp S' K}"
    shows "a \<in> K' u"
  proof -
  
    obtain scc' where SCC: "is_scc (mdp_def.Et_\<alpha> S' K') scc'" and SUBA: "S\<^sub>a \<subseteq> scc'" and USCC: "u \<in> scc'"
      using mdp_def.scc_of_mec[OF MECA NE] USA using in_mono by metis
    moreover have B: "scc' \<subseteq> S'" using mdp_def.scc_in_S[OF _ USCC SCC] mec_sub_mdp_ofD1[OF MECA] USA by blast
    ultimately have "scc' \<notin> set V"
      using SP unfolding cull_graph_def apply clarsimp by blast
  
    have SDEF: "S = \<Union> (set C)"
      using SCCL scc_list_states_eq by blast
    hence SP': "S' = \<Union> (set C) - \<Union> (set V)" 
      using SP by presburger
  
    note SUB = culled_edges_sub_mdp[OF SDEF SP' KP]
  
    obtain scc where A: "scc' \<subseteq> scc" and SCC2: "is_scc Et_\<alpha> scc" and USCC2: "u \<in> scc"
      using USCC in_mono[THEN mp, OF _ USCC]
      by (meson SCC SUB sub_mdp_sub_scc)
    moreover have SCCSS: "scc \<subseteq> S" 
      using mdp_def.scc_in_S[OF _ USCC2 SCC2] USA subset_trans[OF mec_sub_mdp_ofD1[OF MECA] sub_mdp_ofD1[OF SUB]] 
      by blast
    ultimately have SNM: "scc \<notin> set V"
      using SP unfolding cull_graph_def apply clarsimp
      using USCC B by blast
  
    show ?thesis 
      using SP KP AKU unfolding cull_graph_def 
      apply -
      apply(erule culled_edges_K_supset[where ?X'=scc])
      using B SDEF USCC apply blast
      using SCCSS USCC2 apply blast
      using A ASA SUBA apply blast
      using SCC2 SCCL SCCSS scc_list_mem apply blast
      using SNM apply blast
      by blast
  qed
  
  
  lemma(in mdp) cull_graph_unidentified_sub_mdp:
    assumes SP: "S' = S-\<Union>(set V)"
    and KP: "culled_edges C V K K'"
    and SCCL: "scc_list C S K"
    and NE: "S \<noteq> {}"
    and MEC: "is_mec S\<^sub>a K\<^sub>a"
    and ID: "S\<^sub>a \<notin> set V"
    and VSET: "set V = {S' \<in> set C. closed_mdp S' K}"
    shows "sub_mdp_of S\<^sub>a K\<^sub>a S' K'"
  proof -
    note SUB = mec_sub_mdp_of[OF MEC]
  
    from MEC NE obtain scc where SCC: "is_scc Et_\<alpha> scc" and SAS: "S\<^sub>a \<subseteq> scc"
      using mdp_def.scc_of_mec by blast
    hence SUBSCC: "sub_mdp_of S\<^sub>a K\<^sub>a scc K" 
      using SUB by(auto intro: sub_mdp_ofI dest: sub_mdp_ofD2)
  
  
    from SCC have SCCS: "scc \<subseteq> S" 
      by (metis Int_absorb2 Int_iff MEC SAS SCC SUB mdp_mec_non_empty scc_in_S set_notEmptyE sub_mdp_of_def)
  
    from ID consider (scc) "\<not> is_scc Et_\<alpha> S\<^sub>a" | (cl) "is_scc Et_\<alpha> S\<^sub>a \<and> \<not> closed_mdp S\<^sub>a K" 
      by(auto simp: VSET sub_mdp_ofD1[OF SUB] scc_list_mem[OF SCCL])
    hence SID: "scc \<notin> set V"
    proof(cases)
      case scc
      with SCC SAS have "S\<^sub>a \<subset> scc" 
        by blast
      hence "not_eq_mdp S\<^sub>a K\<^sub>a scc K"
        by(auto intro!: not_eq_mdpI1)
      hence PSCC: "psub_mdp_of S\<^sub>a K\<^sub>a scc K"
        using SUBSCC
        by(auto intro: psub_mdp_ofI)
      show ?thesis 
      proof(rule notI)
        assume "scc \<in> set V"
        then have A: "closed_mdp scc K" by(auto simp: VSET)
        hence "is_bottom_scc Et_\<alpha> scc" using closed_scc_sup_bscc[OF SCC SCCS] by blast
        hence "is_ec scc (make_sub_mdp scc)" using bscc_is_ec SCCS by blast
        hence "is_ec scc K" using closed_mdp_eq_make_sub_mdp[OF A] eq_mdp_ec eq_mdp_equiv(2) by blast
        with PSCC have "\<not>is_mec S\<^sub>a K\<^sub>a" using sup_ec_not_mec by blast
        thus False using MEC by blast
      qed
    next
      case cl
      then show ?thesis using VSET ID SCC closed_mdpI is_scc_unique subsetD[OF SAS]
        by metis
    qed
    with SP SCCS have "scc \<subseteq> S'" 
      unfolding cull_graph_def 
      apply clarsimp 
      apply (rule conjI)
      subgoal by blast
      subgoal for u using SCC 
        by (auto simp: scc_list_mem[OF SCCL] VSET dest: is_scc_unique)  
      done
    with SAS have "S\<^sub>a \<subseteq> S'" by blast
    moreover from SP KP have "\<forall>u \<in> S\<^sub>a. K\<^sub>a u \<subseteq> K' u" 
      unfolding cull_graph_def 
      apply clarsimp
      apply(erule culled_edges_K_supset[where ?X'=scc])
      using SCCL calculation scc_list_states_eq apply blast
      apply (meson MEC SAS SCCS all_policies_in_ec mdp_def.mec_is_ec subset_iff)
      apply (meson MEC SAS closed_mdpD mec_closed_mdp subsetD)
      using SCC SCCL SCCS scc_list_mem apply blast
      using SID apply blast
      using MEC mec_sub_mdp_ofD2 by blast
  
    ultimately show ?thesis 
      by(auto intro: sub_mdp_ofI)
  qed
  
  lemma(in mdp) cull_graph_closed_mdp:
    assumes SP: "S' = S-\<Union>(set V)"
    and KP: "culled_edges C V K K'"
    and SCCL: "scc_list C S K"
    and VSET: "set V = {S' \<in> set C. closed_mdp S' K}"
    shows "closed_mdp S' K'"
  proof(rule closed_mdpI)
  
    have SDEF: "S = \<Union> (set C)" 
      using SCCL scc_list_states_eq by blast
    have SP': "S' = \<Union> (set C) - \<Union> (set V)"
      using SP SDEF by blast
  
    fix u a v
    assume "u \<in> S'" and "a \<in> K' u" and VA: "v \<in> a"
  
  
    with KP SCCL obtain scc where SCC: "is_scc Et_\<alpha> scc" and SCCS: "scc \<subseteq> S" and A: "scc \<notin> set V" and "u \<in> scc" and "(\<forall>v\<in> a. v \<in> scc)" 
      unfolding cull_graph_def  
      by (force dest!: culled_edgesD simp: scc_list_mem SDEF SP') 
    with VA have VSCC: "v \<in> scc" by blast
    have "scc \<inter> \<Union>(set V) = {}"
    proof(rule ccontr)
      assume "scc \<inter> \<Union> (set V) \<noteq> {}"
      then obtain w where W1: "w \<in> scc" and "w \<in> \<Union> (set V)" 
        by blast
      then obtain scc' where B: "scc' \<in> (set V)" and W2:"w \<in> scc' " 
        by blast
      hence "is_scc Et_\<alpha> scc'" and "scc' \<subseteq> S" 
        using VSET scc_list_mem[OF SCCL] by blast+
      with SCC have "scc' = scc" using W1 W2 is_scc_unique by meson
      thus False using A B by blast
    qed
    with SP A SCCS have "scc \<subseteq> S'" unfolding cull_graph_def by fast
    with VSCC show "v \<in> S'" by blast
  qed
  
  
  lemma(in compute_MEC_invar) cull_graph_orig: 
    assumes SCC: "scc_list C S K"
    shows "culled_edges C V K K' \<longleftrightarrow> culled_edges C V (K_actions M\<^sub>0) K'"
    unfolding culled_edges_def Let_def
    apply(rule iffI)
    subgoal
      apply(rule ballI)
      apply (clarsimp simp only: scc_list_mem[OF SCC] )
      apply(rule equalityI)
      subgoal for u X 
        apply safe
        subgoal 
          apply(rule sub_struc_of_actions_in_sup[OF is_sub_mdp])
          apply(rule scc_list_scc_to_state)
          apply(rule SCC)
          by blast+
        by blast
      subgoal for u X
        using pres_max_K[OF SCC] 
        by auto
      done
    subgoal
      apply (clarsimp simp: scc_list_mem[OF SCC] )
      apply(rule equalityI)
      subgoal for u X
        using pres_max_K[OF SCC]
        by auto
      subgoal 
        using is_sub_mdp sub_struc_of_actions_in_sup[OF is_sub_mdp] 
        apply clarsimp
        by blast
      done
    done
  
  
  subsection \<open>Abstract Algorithm Definition\<close>
  
  
  context mec_algo
  begin
  
    definition "compute_MEC \<equiv> do {
    
      MDSKZ \<leftarrow> mop_init_mdp M\<^sub>0;
    
      (M,D,S,K,Z) \<leftarrow> WHILEIT (compute_MEC_invar M\<^sub>0) op_states_non_empty
      (\<lambda>(M,D,S,K,Z). do {
        
        \<comment>\<open>Compute the SCCs and remove any transitions that have branches leaving an SCC\<close>
        C \<leftarrow> compute_sccs (M,D,S,K,Z);
  
        ASSERT(scc_list C S K \<and> length C \<le> card (states M\<^sub>0));
        
        \<comment>\<open>Identify the SCCs that are MECs\<close>
        (C',V) \<leftarrow> identify_mecs C (M,D,S,K,Z);
  
        ASSERT(C'=C \<and> distinct V \<and> set V = {S' \<in> set C. closed_mdp S' K} \<and> length D + length V \<le> card (states M\<^sub>0));
  
        \<comment>\<open>Remove the MECs from the graph and cull edges\<close>
        MDSKZ \<leftarrow> cull_graph (C',V) (M,D,S,K,Z);
  
        RETURN MDSKZ
      }) MDSKZ; 
      
      ASSERT(get_mec_pre (M,D,S,K,Z) \<and> M = M\<^sub>0);
      let (D,M) = op_get_mecs (M,D,S,K,Z);
      RETURN D
    }"
  
  
  end
  
  subsection \<open>Correctness of the Abstract Algorithm\<close>
  
  text \<open>
    Our invariant states that identified MECs (in M) are MECs of the input MDP. For the reverse,
    we have that MECs of the input MDP are either in M or in the current MDP. In other words, our
    culling provably never culls any state or transition belonging to an unidentified MEC.
    Once the current MDP is empty, this means that \<open>M\<close> contains exactly the MECs of the input MDP 
    when the current MDP is empty.
  \<close>
  
  context mec_algo
  begin
  
    lemma initial_invar: "compute_MEC_invar M\<^sub>0 (M\<^sub>0,[],(states M\<^sub>0),K_actions M\<^sub>0,Z\<^sub>X)"
      apply(unfold_locales)
      by (auto simp: set_pmf_not_empty[symmetric] sub_struc_of_eq_sub_mdp_of
        dest: mec_sub_mdp)
  
    lemma identify_mecs_is_mec: 
      assumes INV: "compute_MEC_invar M\<^sub>0 (M,D,S,K,Z)"
      assumes NEMP: "S \<noteq> {}"
      assumes SMEM: "S' \<in> set V"
      assumes SCCL: "scc_list C S K"
      assumes VSET: "set V = {S' \<in> set C. closed_mdp S' K}"
      shows "is_mec S' (mdp_def.make_sub_mdp K S')"
    proof -
  
      from INV interpret compute_MEC_invar M\<^sub>0 "(M,D,S,K,Z)" .
  
      from SMEM have "is_bottom_scc (mdp_def.Et_\<alpha> S K) S'" and "S' \<subseteq> S"
        by(auto simp: scc_list_mem[OF SCCL] VSET intro!: closed_scc_sup_bscc) 
      hence "mdp_def.is_mec S K S' (mdp_def.make_sub_mdp K S')" 
        using mdp.bscc_is_mec[OF is_mdp[simplified]] by force
      thus "is_mec S' (mdp_def.make_sub_mdp K S')" 
        using preserve_mec NEMP
        by force
    qed
  
  
    lemma cull_graph_invar:
      assumes INV: "compute_MEC_invar M\<^sub>0 (M,D,S,K,Z)"
      and NEMP: "S \<noteq> {}"
      and SCCL: "scc_list C S K"
      and DISTV: "distinct V"
      and VSET: "set V = {S' \<in> set C. closed_mdp S' K}"
      and MP: "M'=M"
      and DP: "D'=D@V"
      and SP: "S' = S-\<Union>(set V)"
      and KP: "culled_edges C V K K'"
      shows "compute_MEC_invar M\<^sub>0 (M',D',S',K',Z')"
    proof -
  
      from INV interpret compute_MEC_invar M\<^sub>0 "(M,D,S,K,Z)" .
  
  
      note MDP = is_mdp[simplified]
  
      have SDEF: "S = \<Union> (set C)"
        using SCCL scc_list_states_eq by blast
      hence SP': "S' = \<Union> (set C) - \<Union> (set V)" 
        using SP by presburger
    
      note SUB = culled_edges_sub_mdp[OF SDEF SP' KP]
  
      hence AUX2: "sub_struc_of M S' K'"  
        using is_sub_mdp M0 sub_struc_sub_mdp_of by fastforce
  
      have "is_mec S\<^sub>a K\<^sub>a \<Longrightarrow> S\<^sub>a \<notin> set D \<Longrightarrow> \<not> S\<^sub>a \<in> set V \<Longrightarrow> 
        mdp_def.is_mec S K S\<^sub>a K\<^sub>a \<Longrightarrow> sub_mdp_of S\<^sub>a K\<^sub>a S' K'" for S\<^sub>a K\<^sub>a 
        apply(rule mdp.cull_graph_unidentified_sub_mdp[OF MDP SP KP SCCL])
        using NEMP apply blast
        apply assumption+
        using VSET .
      hence AUX3: "is_mec S\<^sub>a K\<^sub>a \<Longrightarrow> S\<^sub>a \<notin> set D \<Longrightarrow> \<not> sub_mdp_of S\<^sub>a K\<^sub>a S' K' \<Longrightarrow> S\<^sub>a \<in> set V" for S\<^sub>a K\<^sub>a 
        apply-
        apply(frule mec_done_or_in_SK)
        apply clarsimp
        apply(frule mec_of_sub_mdp)
        apply(rule sub_struc_of_eq_sub_mdp_of[THEN iffD1])
        using is_sub_mdp[unfolded sub_mdp_def] apply simp
        apply assumption
        by blast
  
      have "S' \<noteq> {} \<Longrightarrow> mdp_def.is_mec S' K' S\<^sub>a K\<^sub>a \<Longrightarrow> mdp_def.is_mec S K S\<^sub>a K\<^sub>a" for S\<^sub>a K\<^sub>a
        apply(rule is_mec_of_sub_mdp)
        apply assumption
        subgoal by assumption
        subgoal using SUB .
        subgoal using cull_graph_preserve_unfinished_mec[OF SP KP SCCL is_mdp[simplified]] VSET by blast
        subgoal using mdp.cull_graph_preserve_mec_transitions[OF is_mdp[simplified] SP KP SCCL] VSET by blast
        subgoal using finite_S by auto
        done
      hence AUX4: "S' \<noteq> {} \<Longrightarrow> mdp_def.is_mec S' K' S\<^sub>a K\<^sub>a \<Longrightarrow> is_mec S\<^sub>a K\<^sub>a" for S\<^sub>a K\<^sub>a
        using preserve_mec[simplified] SUB unfolding sub_mdp_of_def
        by blast
  
      have PD: "pairwise disjnt (set V)" 
        by (metis (no_types, lifting) CollectD SCCL VSET scc_list_unique_V pairwise_disjntI)
  
      from SP have SS: "S' \<subseteq> S" by blast
  
      {
        fix C' a u S''
        assume O2: "scc_list C' S' K'"
        and AK0U: "a \<in> K_actions M\<^sub>0 u"
        and SMEM: "S'' \<in> set C'"
        and US'': "u \<in> S''"
        and AS'': "\<forall>v\<in> a. v \<in> S''"
  
        obtain S\<^sub>c where SCIC:"S\<^sub>c \<in> set C" and "S'' \<subseteq> S\<^sub>c"
          using sub_mdp_scc_list_subset[OF O2 SCCL SUB SMEM] by blast
        with AS'' US'' have USC: "u \<in> S\<^sub>c" and ASC: "\<forall>v\<in> a. v \<in> S\<^sub>c" by blast+
        hence AKU: "a \<in> K u" using pres_max_K[simplified, OF SCCL AK0U[simplified] SCIC]
          by blast
  
        have "S\<^sub>c \<notin> set V"
        proof(rule notI)
          assume "S\<^sub>c \<in> set V"
          hence "S' \<inter> S\<^sub>c = {}"
            unfolding SP cull_graph_def
            by blast
          moreover have "u \<in> S'"
            using O2 SMEM US'' scc_list_mem by blast
          ultimately show False using USC by blast
        qed
  
  
        with AKU KP have "a \<in> K' u" 
          apply -
          apply(erule culled_edges_K_supset[where ?X'=S\<^sub>c])
          apply (metis O2 SMEM SP' US'' UnionI scc_list_states_eq)
          apply (meson SCCL SCIC USC in_mono scc_list_mem)
          using ASC apply blast
          apply (simp add: SCIC)
          apply blast
          .
            
      } note AUX5 = this
  
  
      show ?thesis
        unfolding cull_graph_def
        apply(unfold_locales)
        subgoal using S_D_disj DP SP by auto
        subgoal using S_D_S0 by (auto simp: SDEF VSET SP DP) 
        subgoal using pairwise_disjnt_D DP apply clarsimp
          apply(rule pairwise_disjnt_Un)
          apply assumption
          using PD apply assumption
          using SDEF S_D_disj VSET abs_sel_simps(2) disjnt_iff by fastforce
        subgoal
          using DP distinct_D DISTV SDEF S_D_pairwise_disj VSET mem_D_nonempty by fastforce
        subgoal for S\<^sub>a K\<^sub>a       
          apply (clarsimp simp: DP) 
          using AUX3 by blast
        subgoal for S' using D_of_mecs[of S'] identify_mecs_is_mec[OF INV NEMP _ SCCL, of S'] VSET DP by force
        subgoal for S'' K'' by (auto elim!: AUX4 simp flip: cull_graph_def SP)
        subgoal  
          using finite_S SP
          by force
        subgoal using mdp.cull_graph_closed_mdp[OF MDP SP KP SCCL] unfolding SP VSET by auto
        subgoal by(auto simp flip: M0 simp: AUX2)
        subgoal by (auto simp flip: M0 MP)
        subgoal 
          by (simp add: AUX2 AUX5 sub_mdp_of_sub_mdp flip: M0 MP) 
        done
    qed
  
    lemma invar_correct: assumes INV: "compute_MEC_invar M\<^sub>0 (M,D,{},K,Z)" shows "set D = mec_set_struc"
    proof safe
    
      from INV interpret compute_MEC_invar M\<^sub>0 "(M,D,{},K,Z)" .
  
      fix S'
      assume "S' \<in> set D"
      thus "S' \<in> mec_set_struc"
        unfolding mec_set_struc_mem using D_of_mecs 
        by auto
    next
  
      from INV interpret compute_MEC_invar M\<^sub>0 "(M,D,{},K,Z)" .
  
      fix S'
      assume "S' \<in> mec_set_struc"
      then obtain K' where MEC: "is_mec S' K'" 
        unfolding mec_set_struc_mem by presburger
  
      from MEC have "S' \<noteq> {}"
        using mdp_mec_non_empty by blast
      then have "\<not>sub_mdp_of S' K' {} K"
        unfolding sub_mdp_of_def by blast
      thus "S' \<in> set D"
        using mec_done_or_in_SK[OF MEC]
        by force
    qed
  
  end
  
  
  subsection \<open>Termination\<close>
  
  text \<open>
    The termination argument is as follows: In the current MDP, each BSCC is a MEC of the input
    MDP which we identify in the current iteration. Each graph has at least one BSCC with at least 
    one state, which gets removed in the current iteration. Since the state space is finite, we
    necessarily terminate.\<close>
  
  
  context mec_algo
  begin 
  
    definition "union_psub_mdp_of_rel = {((M\<^sub>1,D\<^sub>1,S\<^sub>1,K\<^sub>1,Z\<^sub>1), (M\<^sub>2,D\<^sub>2,S\<^sub>2,K\<^sub>2,Z\<^sub>2)) | M\<^sub>1 D\<^sub>1 S\<^sub>1 K\<^sub>1 Z\<^sub>1 M\<^sub>2 D\<^sub>2 S\<^sub>2 K\<^sub>2 Z\<^sub>2. ((S\<^sub>1, K\<^sub>1), (S\<^sub>2, K\<^sub>2)) \<in> psub_mdp_of_rel}"
  
    definition "assoc R = {((a,b,c),d,e,f) | a b c d e f. (((a,b),c),(d,e),f) \<in> R}" \<comment> \<open>Workaround\<close>
    lemma compat_assoc1: "compat (assoc R) R (\<lambda> (a,b,c). ((a,b),c))"
      unfolding compat_def assoc_def by fast
    lemma compat_assoc2: "compat R (assoc R) (\<lambda> ((a,b),c). (a,b,c))"
      unfolding compat_def assoc_def by fast
  
    lemma wf_assoc: "wf (assoc R) \<longleftrightarrow> wf R"
      using compat_wf[OF compat_assoc1] compat_wf[OF compat_assoc2] by blast
  
    lemma union_psub_mdp_of_rel_alt: "union_psub_mdp_of_rel = UNIV \<times>\<^sub>r UNIV \<times>\<^sub>r assoc (psub_mdp_of_rel \<times>\<^sub>r UNIV)" 
      unfolding union_psub_mdp_of_rel_def assoc_def
      by force
  
    lemma wf_union_psub_mdp_of_rel [simp]: "wf union_psub_mdp_of_rel"
      unfolding union_psub_mdp_of_rel_alt
      apply(rule wf_UNIV_prod_rel_right)
      apply(rule wf_UNIV_prod_rel_right)
      unfolding wf_assoc
      apply(rule wf_UNIV_prod_rel_left)
      by simp
  
    lemma union_psub_mdp_of_rel_mem: "((M\<^sub>1,D\<^sub>1,S\<^sub>1,K\<^sub>1,Z\<^sub>1), (M\<^sub>2,D\<^sub>2,S\<^sub>2,K\<^sub>2,Z\<^sub>2)) \<in> union_psub_mdp_of_rel \<longleftrightarrow> closed_mdp S\<^sub>2 K\<^sub>2 \<and> finite S\<^sub>2 \<and> psub_mdp_of S\<^sub>1 K\<^sub>1 S\<^sub>2 K\<^sub>2"
      apply(fold psub_mdp_of_rel_mem)
      unfolding union_psub_mdp_of_rel_def 
      by blast
  
    lemma cull_graph_termination:
      assumes INV: "compute_MEC_invar M\<^sub>0 (M,D,S,K,Z)"
      and SCCL: "scc_list C S K"
      and NEMP: "S \<noteq> {}"
      and VSET: "set V = {S' \<in> set C. closed_mdp S' K}"
      and MP: "M'=M"
      and DP: "D'=D@V"
      and SP: "S' = S-\<Union>(set V)"
      and KP: "culled_edges C V K K'"
      shows "((M',D',S',K',Z'),M,D,S,K,Z)
         \<in> union_psub_mdp_of_rel"
    proof -
      from INV interpret compute_MEC_invar M\<^sub>0 "(M,D,S,K,Z)" .
  
      have SDEF: "S = \<Union> (set C)"
        using SCCL scc_list_states_eq by blast
      hence SP': "S' = \<Union> (set C) - \<Union> (set V)" 
        using SP by presburger
    
      note SUBM = culled_edges_sub_mdp[OF SDEF SP' KP]
  
      obtain S\<^sub>b where "is_bottom_scc (mdp_def.Et_\<alpha> S K) S\<^sub>b" and SUB: "S\<^sub>b \<subseteq> S" and NE: "S\<^sub>b \<noteq> {}"
        using mdp.ex_bscc_mdp[OF is_mdp[simplified]] bssc_non_empty' NEMP by blast
      hence "S\<^sub>b \<in> set V"
        using mdp_def.bscc_in_identify_mecs[OF _ _ SCCL VSET] by presburger
      hence "S' \<subset> S"
        using NE SP SUB by auto
      with SUB NE have "psub_mdp_of S' K' S K"
        by(auto intro!: psub_states_psub_mdp_of simp: SUBM) 
      moreover have "finite S" using finite_S 
        by force
      moreover have "closed_mdp S K"
        using closed_mdp' by auto
      ultimately show ?thesis
        by(auto simp: union_psub_mdp_of_rel_mem)
    qed
    
  end
  
  
  subsection \<open>Refinement Proof\<close>
  
  context mec_algo
  begin 
  
    lemmas invar_preserve = initial_invar identify_mecs_is_mec cull_graph_invar invar_correct 
                                
    theorem compute_MEC_refine: "compute_MEC \<le> compute_MEC_spec"
      unfolding compute_MEC_def compute_MEC_spec_def compute_sccs_def identify_mecs_def cull_graph_def 
        mop_init_mdp_def op_states_non_empty_def op_get_mecs_def get_mec_pre_def[symmetric] mec_set_struc_alt[symmetric]
      supply [cong] = refl[of "mdp_def.mec_set_struc _ _"]
      apply(refine_vcg WHILEIT_rule[where ?R = "union_psub_mdp_of_rel"])
      apply(vc_solve solve: invar_preserve ordered_list_distinct cull_graph_termination compute_MEC_invar.scc_list_length_C_bound_S0 compute_MEC_invar.length_V_D_bound  )
      subgoal 
        apply(frule compute_MEC_invar.mecs_states_M\<^sub>0)
        apply simp
        apply(frule compute_MEC_invar.M0)
        apply(frule compute_MEC_invar.emp_not_in_D)
        unfolding get_mec_pre_def by auto
      subgoal
        by(auto dest: compute_MEC_invar.M0)
      subgoal
        using compute_MEC_invar.distinct_D by fastforce
      done
  end
  
  
  
  section \<open>Concrete Algorithm\<close>
  
  text \<open>
    The concrete algorithm implements the three steps of the abstract algorithm as loops, defining
    the behaviour in a procedural way. Note that this refinement does not use any data refinement.
    For this work, we have leveraged the data refinement completely to the data structures.
  \<close>
  
  subsection \<open>Algorithm Operations\<close>
  
  definition "is_state_in_scc v C \<equiv> \<exists> i < length C. v \<in> C ! i" (*SCC map operation*)
  
  definition "get_scc_val u C = SPEC (\<lambda> i. i < length C \<and> u \<in> C ! i)" (*SCC map operation*)
  
  subsection \<open>Invariants\<close>
  
  text \<open>
    For the implementation of \<open>identify_mecs\<close> as a loop, we define another invariant.
    The set \<open>fs\<close> stores all SCCs for which we haven't proven that they are not MECs yet.
    This implementation initially assumes all SCCs are MECs (and thus adds them to \<open>fs\<close>).
    It iterates over all states and if a state has an edge leaving the SCC of that state, the 
    SCC is removed as a MEC.
  \<close>
  
  locale identify_mecs_fine_loop1_invar_defs =
    fixes C :: "'v set list"
    and it :: "'v set"
    and FS  :: "'v set list \<times> 'v set set"
  begin
  
    definition "xs = (\<lambda>(xs,fas). xs) FS"
    definition "fs = (\<lambda>(xs,fas). fas) FS"
  
  end
  
  lemma mec_FS_simps[simp]:
    "identify_mecs_fine_loop1_invar_defs.xs (xs,fs) = xs"
    "identify_mecs_fine_loop1_invar_defs.fs (xs,fs) = fs"
    unfolding identify_mecs_fine_loop1_invar_defs.xs_def identify_mecs_fine_loop1_invar_defs.fs_def
    by auto
  
  locale identify_mecs_fine_loop1_invar = compute_MEC_invar M\<^sub>0 + identify_mecs_fine_loop1_invar_defs C it FS 
    for M\<^sub>0::"'v mdpc" and C :: "'v set list" and it and FS +
    assumes sccs: "scc_list C S K" \<comment> \<open>C contains the SCCs of the current MDP\<close>
    assumes closed_Vi: "(\<forall>i < length C. C!i \<in> fs \<longleftrightarrow> (\<forall>u \<in> C ! i \<inter> ((states M\<^sub>0) - it). (\<forall> a \<in> K u. a \<subseteq> C ! i)))"
      \<comment> \<open>If an SCC is in fs, then all states that we have iterated over only have transitions that remain within the SCC\<close>
    assumes xs_eq: "xs=C" \<comment> \<open>xs contains the original SCCs which we store for implementation purposes\<close>
    assumes fs_ss: "fs \<subseteq> set C" \<comment> \<open>fs only contains SCCs.\<close>
  begin
  
    lemma(in compute_MEC_invar) op_create_filter_setD: "op_create_filter_set C = (C', V') \<Longrightarrow> C' = C \<and> V' = set C"
      unfolding op_create_filter_set_def 
      by blast
  
    lemma(in compute_MEC_invar) op_create_filter_setE: "op_create_filter_set C = (C', V') \<Longrightarrow> P C (set C) \<Longrightarrow> P C' V'"
      unfolding op_create_filter_set_def by blast
  
  
    lemma(in compute_MEC_invar) identify_mecs_fine_loop1_invar_initial:
      "scc_list C S K \<Longrightarrow> identify_mecs_fine_loop1_invar MDSKZ M\<^sub>0 C (states M\<^sub>0) (C,set C)"
      unfolding op_create_filter_set_def
      apply(unfold_locales)
      subgoal 
        by assumption
      subgoal 
        apply(drule scc_listD2)
        by force
      subgoal by auto
      subgoal by simp
      done
  
    text \<open>
      Each case distinction is captured in a lemma names \<open>caseX\<close> and assertions are proven in a
      lemma named \<open>assertX\<close>
    \<close>
  
    lemma case1:
      assumes ITS0: "it \<subseteq> (states M\<^sub>0)"
      and EQ0: "FS\<^sub>0 = (xs, fs)"
      and EQ: "FS' = (xs, fs - {xs!i})"
      and NEM: "\<not> op_all_succ_eq_map (M,D,S,K,Z) FS\<^sub>0 u"
      and UIT: "u \<in> it"
      and ILEN: "i < length xs"
      and UCI: "u \<in> xs ! i "
      shows "identify_mecs_fine_loop1_invar MDSKZ M\<^sub>0 C (it - {u}) FS'"
    proof -
  
      have A: "(states M\<^sub>0) - (it - {u}) = insert u ((states M\<^sub>0) - it)"
        using ITS0 UIT
        by fast
  
      show ?thesis
        apply unfold_locales
        subgoal using sccs .
        subgoal
          apply clarsimp
          subgoal for j
            apply(cases "j = i")
            subgoal
              using NEM
              apply (clarsimp simp: A op_all_succ_eq_map_def EQ xs_eq) 
              using EQ0 UCI xs_eq by auto
            subgoal
              apply (clarsimp simp: A EQ )
              apply(subgoal_tac "u \<notin> C ! j")
              subgoal
                using closed_Vi 
                using UCI by auto 
              subgoal
                using scc_list_unique_index[OF sccs] ILEN UCI xs_eq
                by blast
              done
            done
          done
          subgoal using EQ xs_eq by force
          subgoal using EQ fs_ss by auto
        done
    qed
  
    lemma case2:
      assumes UIT: "u \<in> it"
      and ITS0: "it \<subseteq> (states M\<^sub>0)"
      and EQ0: "FS\<^sub>0 = (xs,fs)"
      and EM: "op_all_succ_eq_map (M,D,S,K,Z) FS\<^sub>0 u"
      shows "identify_mecs_fine_loop1_invar MDSKZ M\<^sub>0 C (it - {u}) FS"
    proof -
  
      have A: "(states M\<^sub>0) - (it - {u}) = insert u ((states M\<^sub>0) - it)"
        using ITS0 UIT
        by fast
  
      have B: "\<forall> u i j. i < length C \<longrightarrow> j < length C \<longrightarrow> u \<in> C ! i \<longrightarrow> u \<in> C ! j \<longrightarrow> i = j"
        using scc_list_unique_index[OF sccs] by simp
  
      {
        fix i v a w
        assume ILEN: "i < length C"
        and VCI: "v \<in> C ! i" 
        and VU[simp]: "v = u"
        and AKV: "a \<in> K v" 
        and WA: "w \<in> a"
  
        have "a \<subseteq> C ! i" 
          using op_all_succ_eq_map_succ[OF B ILEN VCI] AKV EM EQ0 xs_eq
          by fastforce
  
        with WA have "w \<in> C ! i"
          by fast
      } note AUX1 = this
  
      {
        fix i v a w
        assume "i < length C" 
        and "C ! i \<in> fs" 
        and "v \<in> C ! i" 
        and "v \<in> (states M\<^sub>0)"
        and "v \<notin> it"
        and "a \<in> K v" 
        and "w \<in> a"
        hence "w \<in> C ! i" 
          using closed_Vi by blast
      } note AUX2 = this
  
  
      show ?thesis
        apply unfold_locales
        subgoal using sccs .
        subgoal apply (clarsimp simp: A) 
          apply(rule iffI)
          subgoal for i
            by (blast intro: AUX1 AUX2)
          subgoal for i
            using closed_Vi by auto
          done
        subgoal using xs_eq by force
        subgoal using fs_ss by auto
        done
    qed
  
    lemma case3:
      assumes UNS: "u \<notin> S"
      shows "identify_mecs_fine_loop1_invar MDSKZ M\<^sub>0 C (it - {u}) FS"
    proof -
  
      show ?thesis
        apply(unfold_locales)
        subgoal using sccs .
        subgoal
          apply clarsimp
          apply(rule iffI)
          subgoal for i
            apply clarsimp
            subgoal for u a v
              using UNS closed_Vi sccs scc_list_index by fast
            done
          subgoal for i
            using closed_Vi by fast
          done
        subgoal using xs_eq by force
        subgoal using fs_ss by auto
        done
            
    qed
  
    lemma assert1: "xs'=xs \<Longrightarrow> S' = S \<Longrightarrow> K' = K \<Longrightarrow> scc_list xs' S' K'"
      using sccs xs_eq by auto
  
    lemma assert2: "S' = S \<Longrightarrow> xs'=xs \<Longrightarrow> u \<in> S' \<Longrightarrow> \<exists>i<length xs'. u \<in> xs' ! i"
      using sccs scc_list_states_index xs_eq by fast
  
    lemma final:
      assumes NE[simp]: "it = {}"
      and EQ: "FS = (xs',fs')"
      and K[simp]: "K'=K"
      shows "fs' = {S' \<in> set C. closed_mdp S' K'}"
    proof -
  
      have [simp]: "xs'=xs" "fs'=fs"
        using EQ by auto
  
  
      {
        fix x
        assume A: "x \<in> fs"
        with fs_ss have XS: "x \<in> set C" by auto
        then obtain i where IL: "i<length C" and XD: "x = C ! i" 
          by (metis in_set_conv_nth)
        hence "\<forall>u\<in>C ! i \<inter> (states M\<^sub>0). \<forall>a\<in>K u. a \<subseteq> C ! i" using closed_Vi A by auto
        moreover have "C ! i \<subseteq> (states M\<^sub>0)" 
          using XD XS sccs scc_list_mem subset_states by fastforce
        ultimately have "closed_mdp x K" unfolding closed_mdp_def
          using XD IL by blast
      } note AUX1=this
  
      {
        fix x
        assume "x \<in> set C" and CL: "closed_mdp x K"
        then obtain i where IL: "i<length C" and XD: "x = C ! i" 
          by (metis in_set_conv_nth)
        hence "C ! i \<subseteq> (states M\<^sub>0)" 
          using sccs scc_list_mem subset_states by fastforce
        hence "\<forall>u\<in>C ! i \<inter> (states M\<^sub>0). \<forall>a\<in>K u. a \<subseteq> C ! i" using closed_Vi 
          using XD CL
          by (metis closed_mdpD inf_absorb1 subset_iff)
        hence "x \<in> fs" 
          using IL NE XD closed_Vi by blast
      } note AUX2=this
  
      show ?thesis
        using fs_ss by (auto simp: AUX1 AUX2) 
    qed
  
  end
  
  
  definition set_to_list:: "'a list \<times> 'a set \<Rightarrow> ('a list \<times> 'a list) nres" where 
    "set_to_list = (\<lambda> (xs,fs). SPEC (\<lambda> (xs',fas). xs' = xs \<and> fs = set fas \<and> distinct xs' \<and> distinct fas))"
  
  text \<open>
    Similarly, we implement \<open>cull_graph\<close> by iterating over states and removing them if
    they are in an identified MEC or removing any transitions leaving the SCC otherwise.
    To track the removed edges on an abstract level, we also track the SCCs that are not MECs
    in a separate list \<open>L\<^sub>2\<close>
    Note that, apart from the variant for the outer loop \<open>(M,D,S,K,Z)\<close>, there is now also a loop state for
    the inner loop \<open>(L\<^sub>2,M\<^sub>2,S\<^sub>2,K\<^sub>2)\<close>.
  \<close>
  
  locale cull_graph_fine_loop_invar_def = compute_MEC_invar_def M\<^sub>0 MDSKZ\<^sub>1 for M\<^sub>0::"'v mdpc" and MDSKZ\<^sub>1 +
    fixes C::"'v set list" 
    and V::"'v set list" 
    and it::"'v set"
    and MLDSKZ\<^sub>2::"'v mec_abs_state_ext"
  begin
  
  
    definition "M\<^sub>2 = (\<lambda> (M,L,D,S,K,Z). M) MLDSKZ\<^sub>2" \<comment>\<open>Original MDP\<close>
    definition "L\<^sub>2 = (\<lambda> (M,L,D,S,K,Z). L) MLDSKZ\<^sub>2" \<comment>\<open>Set of updated states\<close>
    definition "D\<^sub>2 = (\<lambda> (M,L,D,S,K,Z). D) MLDSKZ\<^sub>2" \<comment>\<open>Set of discovered MECs\<close>
    definition "S\<^sub>2 = (\<lambda> (M,L,D,S,K,Z). S) MLDSKZ\<^sub>2" \<comment>\<open>Set of states in MDP\<close>
    definition "K\<^sub>2 = (\<lambda> (M,L,D,S,K,Z). K) MLDSKZ\<^sub>2" \<comment>\<open>MDP Kernel\<close>
    definition "Z\<^sub>2 = (\<lambda> (M,L,D,S,K,Z). Z) MLDSKZ\<^sub>2" \<comment>\<open>Workaround: Contains the sates that lose their self-loop in the SCC computation\<close>
  
  
    definition "Cv = map (\<lambda> x. if x \<in> set V then {} else x) C"
  
    lemma length_Cv: "length Cv = length C"
      unfolding Cv_def by simp
  
    lemma Cv_in_S_aux: "scc_list C S K \<Longrightarrow> \<Union>(set Cv) \<subseteq> S"
      unfolding Cv_def
      using scc_list_states_eq by fastforce
  
    lemma mem_C_if_mem_Cv: "i < length C \<Longrightarrow> u \<in> Cv ! i \<Longrightarrow> u \<in> C ! i"
      unfolding Cv_def by (auto split: if_splits)
  
    lemma mem_Cv_if_mem_C: "i < length C \<Longrightarrow> u \<in> C ! i \<Longrightarrow> \<forall>j<length V. u \<notin> V ! j \<Longrightarrow> u \<in> Cv ! i"
      unfolding Cv_def by (auto simp: in_set_conv_nth) 
  
  end
  
  lemma abs_sel_simps1 [simp]:
    "cull_graph_fine_loop_invar_def.M\<^sub>2 (M,L,D,S,K,Z) = M"
    "cull_graph_fine_loop_invar_def.L\<^sub>2 (M,L,D,S,K,Z) = L"
    "cull_graph_fine_loop_invar_def.D\<^sub>2 (M,L,D,S,K,Z) = D"
    "cull_graph_fine_loop_invar_def.S\<^sub>2 (M,L,D,S,K,Z) = S"
    "cull_graph_fine_loop_invar_def.K\<^sub>2 (M,L,D,S,K,Z) = K"
    "cull_graph_fine_loop_invar_def.Z\<^sub>2 (M,L,D,S,K,Z) = Z"
    unfolding cull_graph_fine_loop_invar_def.S\<^sub>2_def cull_graph_fine_loop_invar_def.M\<^sub>2_def 
      cull_graph_fine_loop_invar_def.K\<^sub>2_def cull_graph_fine_loop_invar_def.L\<^sub>2_def
        cull_graph_fine_loop_invar_def.D\<^sub>2_def cull_graph_fine_loop_invar_def.Z\<^sub>2_def
    by auto
  
  
                                                
  locale cull_graph_fine_loop_invar_pre = compute_MEC_invar M\<^sub>0 MDSKZ\<^sub>1
    + cull_graph_fine_loop_invar_def M\<^sub>0 MDSKZ\<^sub>1 C V it MLDSKZ\<^sub>2 for M\<^sub>0::"'v mdpc" and MDSKZ\<^sub>1 C V it MLDSKZ\<^sub>2
  begin
  
    lemma MDSKZ1_def: "(M,D,S,K,Z) = MDSKZ\<^sub>1"
      by (metis abs_sel_simps prod_cases3)
  
    lemma MDSKZ2_simps: 
      assumes "MLDSKZ\<^sub>2 = (x1, x2, x3, x4, x5, x6)"
      shows "x1 = M\<^sub>2"
      and "x2 = L\<^sub>2"
      and "x3 = D\<^sub>2"
      and "x4 = S\<^sub>2"
      and "x5 = K\<^sub>2"
      and "x6 = Z\<^sub>2"
      by (simp_all add: assms)
  end
  
  
  definition "mop_untrack_sccs_pre_cull \<equiv> (\<lambda> ((M,L,D,S,K),(C,V)). \<exists> S\<^sub>1 K\<^sub>1. 
    S\<^sub>1 = \<Union> (set C) 
  \<and> scc_list C S\<^sub>1 K\<^sub>1 
  \<and> set V = {S' \<in> set C. closed_mdp S' K\<^sub>1} 
  \<and> sub_struc_of M S\<^sub>1 K\<^sub>1
  \<and> \<Union>(set C) - \<Union>(set V) \<subseteq> S 
  \<and> (\<forall>i < length L. length C \<le> i \<longrightarrow> L ! i = {}) 
  \<and> (\<forall>i < length C. if C ! i \<in> set V then L ! i = {} else L ! i = C ! i)
  )"
  
  lemma mop_untrack_sccs_pre_cullI: "S\<^sub>1 = \<Union> (set C) 
   \<Longrightarrow> scc_list C S\<^sub>1 K\<^sub>1 
   \<Longrightarrow> set V = {S' \<in> set C. closed_mdp S' K\<^sub>1} 
   \<Longrightarrow> sub_struc_of M S\<^sub>1 K\<^sub>1
   \<Longrightarrow> \<Union>(set C) - \<Union>(set V) \<subseteq> S 
   \<Longrightarrow> (\<forall>i < length L. length C \<le> i \<longrightarrow> L ! i = {}) 
   \<Longrightarrow> (\<forall>i < length C. if C ! i \<in> set V then L ! i = {} else L ! i = C ! i)
   \<Longrightarrow> mop_untrack_sccs_pre_cull ((M,L,D,S,K),(C,V))"
    unfolding mop_untrack_sccs_pre_cull_def
    by blast
  
  
  
  locale cull_graph_fine_loop_invar = cull_graph_fine_loop_invar_pre +
    assumes L_prog: "j < length C \<Longrightarrow> map (\<lambda> x. x - it) L\<^sub>2 ! j = map (\<lambda> x. x - it) Cv ! j" \<comment> \<open>\<open>L\<^sub>2\<close> contains the SCCs that are not MECs over iterated states\<close>
    assumes L_prog2: "j < length L\<^sub>2 \<Longrightarrow> length C \<le> j \<Longrightarrow> L\<^sub>2 ! j - it = {}" \<comment> \<open>\<open>L\<^sub>2\<close> only contains iterated states\<close>
    assumes L_len: "length C \<le> length L\<^sub>2" \<comment> \<open>The SCCs fit into \<open>L\<^sub>2\<close>\<close>
    assumes L_sub: "\<Union>(set L\<^sub>2) \<subseteq> S" \<comment> \<open>\<open>L\<^sub>2\<close> consists of states\<close>
    assumes D_prog: "D\<^sub>2 = D @ (map (\<lambda> x. x - it) V)" \<comment> \<open>The iterated states in MECs are added to \<open>M\<^sub>2\<close>\<close>
    assumes S_prog: "S\<^sub>2 = S - (\<Union> (set V) - it)" \<comment> \<open>The iterated states in MECs are removed from \<open>S\<^sub>2\<close>\<close>
    assumes SD2_disj: "S\<^sub>2 \<inter> \<Union>(set D\<^sub>2) = {}" \<comment> \<open>The updated states and MECs are disjoint\<close>
  
    assumes Scc_list: "scc_list C S K" \<comment> \<open>\<open>C\<close> is a list of SCCs\<close>
    assumes V_def_set: "set V = {S' \<in> set C. closed_mdp S' K}" \<comment> \<open>\<open>V\<close> is a list containing the SCCs that are MECs\<close>
    assumes V_distinct: "distinct V" \<comment> \<open>\<open>V\<close> is distinct\<close>
    assumes MC[simp]: "M\<^sub>2 = M"
    assumes ZC[simp]: "Z\<^sub>2 = Z"
  begin
  
    lemma length_D2: "length D\<^sub>2 = length D + length V"
      using D_prog by simp
  
    lemma L2_Cv_eq_mem: "j < length C \<Longrightarrow> x \<notin> it \<Longrightarrow> x \<in> L\<^sub>2 ! j \<longleftrightarrow> x \<in> Cv ! j"
      apply(frule L_prog) using L_len length_Cv by auto
  
    lemma set_C_int_V_def: "set C \<inter> set V = set V"
      using V_def_set by blast
  
    lemma S\<^sub>2_mem_to_S: "u \<in> S\<^sub>2 \<Longrightarrow> u \<in> S"
      by (simp add: S_prog)
  
    lemma Cv_in_S: "\<Union>(set Cv) \<subseteq> S"
      using Cv_in_S_aux Scc_list by presburger
  
    lemma set_Cv_alt: "\<Union>(set Cv) = \<Union>(set C) - \<Union>(set V)"
    proof(safe)
      fix u X
      assume "u \<in> X" "X \<in> set Cv"
      thus "u \<in> \<Union>(set C)"
        unfolding Cv_def by auto 
    next 
      fix u X Y
      assume "u \<in> X" "X \<in> set Cv" "u \<in> Y" "Y \<in> set V "
      thus False
        unfolding Cv_def by (auto simp: set_C_int_V_def V_def_set 
          dest: scc_list_unique_C[OF Scc_list])
    next
      fix u X
      assume "u \<notin> \<Union> (set V)" "u \<in> X" "X \<in> set C"
      thus "u \<in> \<Union> (set Cv)"
        unfolding Cv_def by auto
    qed
  
  
    lemma V_nth_in_C: "X \<in> set V \<Longrightarrow> \<exists> i. i < length C \<and> X = C ! i \<and> closed_mdp X K"
      using V_def_set nth_the_index the_index_bounded by fastforce
  
    lemma neq_V_C_nth: "\<forall>i<length V. V ! i \<noteq> C ! j \<Longrightarrow> j < length C \<Longrightarrow> u \<in> C ! j \<Longrightarrow> u \<notin> \<Union>(set V)"
      apply clarsimp
      apply (frule V_nth_in_C)
      using scc_list_unique_index[OF Scc_list]
      apply (fastforce simp: in_set_conv_nth)
      done
  
  
    lemma(in cull_graph_fine_loop_invar_pre) pre_initial: 
      assumes SCC: "scc_list C S K"
      assumes VDEF: "set V = {S' \<in> set C. closed_mdp S' K}"
      assumes VDIS: "distinct V"
      assumes LL: "length C \<le> length L"
      assumes LS: "\<Union>(set L) \<subseteq> S"
      shows "cull_graph_fine_loop_invar M\<^sub>0 MDSKZ\<^sub>1 C V (states M\<^sub>0) (M, L, D @ replicate (length V) {}, S, K, Z)"
      apply(unfold_locales)
      subgoal using subset_states map_substract_eq_replicate_empty_set
        apply clarsimp
        apply(subst map_substract_eq_replicate_empty_set)
        using LS apply blast
        apply(subst map_substract_eq_replicate_empty_set)
        using Cv_in_S_aux[OF SCC]
        apply blast
        using LL length_Cv by auto
      subgoal for j apply clarsimp
        by (meson LS UnionI in_mono nth_mem subset_states)
      subgoal using LL by auto
      subgoal using LS by simp
      subgoal using subset_states VDEF
        by (auto simp: scc_list_mem[OF SCC] intro!: map_substract_eq_replicate_empty_set[symmetric])
      subgoal using subset_states by auto
      subgoal using S_D_disj by auto
      subgoal using SCC by blast
      subgoal using VDEF by blast
      subgoal using VDIS by blast
      subgoal by simp
      subgoal by simp
      done
  
    lemma case1:
      assumes SCC: "scc_list C S K"  
      and UIT: "u \<in> it"
      and US2: "u \<notin> S\<^sub>2"
      and VDEF: "set V = {S' \<in> set C. closed_mdp S' K}"
      and VDIS: "distinct V"
      and MP: "M'=M\<^sub>2"
      and LP: "L'=L\<^sub>2"
      and DP: "D'=D\<^sub>2"
      and SP: "S'=S\<^sub>2"
      and ZP: "Z'=Z\<^sub>2"
      shows "cull_graph_fine_loop_invar M\<^sub>0 MDSKZ\<^sub>1 C V (it - {u}) (M',L',D',S',K',Z')"
    proof -
  
      have "S\<^sub>2 \<subseteq> S"
        by (simp add: S_prog)
  
      have AUX: "\<forall>S \<in> set V. u \<notin> S"
      proof 
        fix Sa
        assume "Sa \<in> set V"
        hence "Sa \<subseteq> S"
          using VDEF scc_list_mem[OF SCC] by blast
        moreover have "u \<notin> S"
          using US2 UIT unfolding S_prog by blast
        ultimately show "u \<notin> Sa" by blast
      qed 
  
      have US: "u \<notin> S"
        using S_prog UIT US2 by auto
  
      have "u \<notin> \<Union>(set Cv)"
        using Cv_in_S US by blast
      hence DM: "map (\<lambda>x. x - (it - {u})) Cv = map (\<lambda>x. x - it) Cv"
        by auto
  
      have "u \<notin> \<Union>(set L\<^sub>2)"
        using L_sub US by blast
      hence LM: "map (\<lambda>x. x - (it - {u})) L\<^sub>2 = map (\<lambda>x. x - it) L\<^sub>2"
        by auto
  
  
      have AUX2: "j < length C \<Longrightarrow> map (\<lambda>x. x - (it - {u})) L\<^sub>2 ! j = map (\<lambda>x. x - (it - {u})) Cv ! j" for j
        by (simp add: LM DM L_prog)
  
  
      show ?thesis
        apply(unfold_locales)
        subgoal
          using Cv_in_S S_prog LP US by (auto simp: AUX2)
        subgoal for j 
          using LP L_prog2 \<open>u \<notin> \<Union> (set L\<^sub>2)\<close> by auto
        subgoal
          using LP L_len by auto
        subgoal
          by (auto simp: LP L_sub)
        subgoal
          apply(clarsimp simp: D_prog VDEF DP LP)
          apply(rule disj_sub_sub_set)
          using AUX MDSKZ1_def 
          by (metis Int_empty_right SCC US disjoint_insert(1) scc_list_mem subset_eq)
        subgoal
          by(auto simp: AUX S_prog VDEF SP)
        subgoal
          by (simp add: DP SD2_disj SP)
        subgoal
          by (simp add: Scc_list)
        subgoal
          by (simp add: V_def_set)
        subgoal 
          by (simp add: V_distinct)
        subgoal 
          by (simp add: MP)
        subgoal 
          by (simp add: ZP)
        done
    qed
  
    lemma case2: 
      assumes UIT: "u \<in> it"
      and IL: "i < length V"
      and UID: "u \<in> V ! i"
      and MP: "M'=M"
      and LP: "L'=(map (\<lambda>X. X - {u}) L\<^sub>2)"
      and DP: "D'=(map (\<lambda>X. X - {u}) D\<^sub>2)[((length D) + i):=(insert u (D\<^sub>2 ! ((length D) + i)))]"
      and SP: "S'=S\<^sub>2 - {u}"
      and ZP: "Z'=Z\<^sub>2"
      and US2: "u \<in> S\<^sub>2"
      shows "cull_graph_fine_loop_invar M\<^sub>0 MDSKZ\<^sub>1 C V (it - {u}) (M',L',D',S',K',Z')"
    proof -
  
      have MDSKZ2_alt: "MLDSKZ\<^sub>2 = (M\<^sub>2,L\<^sub>2,D\<^sub>2,S\<^sub>2,K\<^sub>2,Z\<^sub>2)"
        by (metis MDSKZ2_simps prod.exhaust)
  
      have get_mec_num_MDSKZ_alt: "(op_get_mec_num MDSKZ\<^sub>1) = length D"
        unfolding op_get_mec_num_def 
        apply(rewrite MDSKZ1_def[symmetric])
        by simp
  
      from US2 have "u \<notin> \<Union>(set D\<^sub>2)"
        using SD2_disj by blast
      hence "D\<^sub>2 = (map (\<lambda>X. X - {u}) D\<^sub>2)"
        by (simp add: map_idI)
      hence DP': "D'=D\<^sub>2[((length D) + i):=(insert u (D\<^sub>2 ! ((length D) + i)))]"
        using DP by presburger
  
      {
        fix j
        assume JL:"j < length V" and UJD: "u \<in> V ! j"
  
        have "k < length V \<Longrightarrow> (is_scc (mdp_def.Et_\<alpha> S K) (V ! k) \<and> V ! k \<subseteq> S)" for k 
          using V_def_set nth_mem scc_list_mem[OF Scc_list, of "V ! k"] by auto
        hence "is_scc (mdp_def.Et_\<alpha> S K) (V ! i)" and "is_scc (mdp_def.Et_\<alpha> S K) (V ! j)"
          using IL JL by auto
        with UID UJD have "V ! i = V ! j"
          by (simp add: is_scc_unique)
        with V_distinct have "i = j" 
          by (simp add: IL JL nth_eq_iff_index_eq)
      } note A = this
  
      have AUX2: "\<Union> (set (D\<^sub>2[(length D) + i := insert u (D\<^sub>2 ! ((length D) + i))])) = insert u (\<Union> (set D\<^sub>2))"
        apply(rule insert_Un_list_upd)
        by (simp add: IL D_prog)
  
      have "u \<in> \<Union>(set C)" 
        using  S_prog US2 scc_list_states_eq[OF Scc_list] by blast
      with UID have UND: "u \<notin> \<Union>(set Cv)"
        unfolding Cv_def apply (clarsimp simp: in_set_conv_nth )
        using IL by (auto dest: neq_V_C_nth)
  
      have R: "(\<lambda>x. x - (it - {u})) \<circ> (\<lambda>X. X - {u}) = (\<lambda>x. x - it)"
        unfolding comp_def
        apply(rule ext)
        using UIT by blast
        
  
      show ?thesis
        apply unfold_locales
        subgoal for j apply(frule L_prog)
          using length_Cv LP R UND by fastforce
        subgoal
          using LP L_prog2 by fastforce
        subgoal using L_len by (simp add: LP)
        subgoal
          using L_sub by (auto simp: LP)
        subgoal
          unfolding mop_add_state_to_mec_def
          apply(auto simp: DP' UID get_mec_num_MDSKZ_alt D_prog append_right_upd nth_list_update' 
            dest: A intro!: nth_equalityI split: if_splits) 
          done
        subgoal
          unfolding mop_add_state_to_mec_def
          using S_prog MDSKZ1_def IL UID by (auto simp: SP)
        subgoal 
          apply (clarsimp simp: SP DP')
          using SD2_disj AUX2 by auto
        subgoal
          by (simp add: Scc_list)
        subgoal
          by (simp add: V_def_set)
        subgoal 
          by (simp add: V_distinct)
        subgoal
          by (simp add: MP)
        subgoal
          by (simp add: ZP)
        done
    qed
  
    lemma case3:
      assumes UIT: "u \<in> it"
      and IC: "i < length C"
      and UCI: "u \<in> C ! i"
      and NCOMP: "\<forall>x < length V. u \<notin> V ! x"
      and VDEF: "set V = {S' \<in> set C. closed_mdp S' K}"
      and VDIS: "distinct V"
      and MP: "M' = M"
      and LP: "L' = (map (\<lambda>X. X - {u}) L\<^sub>2)[i := insert u (L\<^sub>2 ! i)]"
      and DP: "D' = (map (\<lambda>X. X - {u}) D\<^sub>2)"
      and SP: "S' = S\<^sub>2"
      and ZP: "Z' = Z\<^sub>2"
      and US2: "u \<in> S\<^sub>2"
      shows "cull_graph_fine_loop_invar M\<^sub>0 MDSKZ\<^sub>1 C V (it - {u}) (M',L',D',S',K',Z')"
    proof -
  
      have AUX: "\<forall>S \<in> set V. u \<notin> S"
        using NCOMP
        by (force simp: in_set_conv_nth ) 
  
      have IL2: "i < length L\<^sub>2"
        using IC L_len by auto
  
      from US2 have "u \<notin> \<Union>(set D\<^sub>2)"
        using SD2_disj by blast
      hence "D\<^sub>2 = (map (\<lambda>X. X - {u}) D\<^sub>2)"
        by (simp add: map_idI)
      hence DP': "D'=D\<^sub>2"
        using DP by presburger
  
      from IC have ID: "i < length C"
        by (simp add: length_Cv)
  
  
      have LP': "j < length C \<Longrightarrow> map (\<lambda>x. x - (it - {u})) L' ! j = map (\<lambda>x. x - (it - {u})) Cv ! j" for j
        apply(frule L_prog)
        apply (simp add: LP ) 
        apply(cases "i=j")
        subgoal
          using L_len UCI AUX length_Cv mem_Cv_if_mem_C by auto
        subgoal
          using L_len UCI mem_C_if_mem_Cv scc_list_unique_index[OF Scc_list] 
          by (auto simp: length_Cv ID)
        done
  
      show ?thesis
        apply(unfold_locales)
        subgoal by (simp add: LP')
        subgoal 
          using ID LP L_prog2 by fastforce
        subgoal 
          by (simp add: LP L_len)
        subgoal
          apply(clarsimp simp: LP)
          apply(subst(asm) in_set_upd_eq)
          apply (simp add: IL2)
          apply(erule disjE)
          subgoal
            using ID S_prog US2 length_Cv L_sub IL2 by fastforce
          subgoal
            using S_prog US2 L_sub by auto
          done
        subgoal
          apply(clarsimp simp: D_prog VDEF DP')
          apply(rule disj_sub_sub_set)
          using AUX MDSKZ1_def 
          by (simp add: VDEF)
        subgoal
          by(auto simp: AUX S_prog VDEF SP)
        subgoal
          by (simp add: DP' SD2_disj SP)
        subgoal
          by (simp add: Scc_list)
        subgoal
          by (simp add: V_def_set)
        subgoal 
          by (simp add: V_distinct)
        subgoal
          by (simp add: MP)
        subgoal
          by (simp add: ZP)
        done
    qed
  
    lemma assert1: "u \<in> S\<^sub>2 \<Longrightarrow> \<exists>i<length C. u \<in> C ! i"
      apply(drule S\<^sub>2_mem_to_S)
      using Scc_list
      by (metis UnionE in_set_conv_nth scc_list_states_eq) 
  
    lemma assert2: "u \<in> S\<^sub>2 \<Longrightarrow> u \<notin> \<Union> (set D\<^sub>2)"
      using SD2_disj by blast
  
    lemma assert3: 
      assumes MLDSKZ: "MLDSKZ\<^sub>2 = (M',L',D',S',K',Z')"
      assumes EMP: "it = {}"
      shows "mop_untrack_sccs_pre_cull ((M',L',D',S',K',Z'), (C,V))"
    proof - 
      have [simp]: "M' = M\<^sub>2"
      and  [simp]: "L' = L\<^sub>2"
      and  [simp]: "D' = D\<^sub>2"
      and  [simp]: "S' = S\<^sub>2"
      and  [simp]: "K' = K\<^sub>2" 
      and  [simp]: "Z' = Z\<^sub>2" 
        using MLDSKZ by auto
  
      show ?thesis
        apply(rule mop_untrack_sccs_pre_cullI)
        apply(rule Scc_list[THEN scc_list_states_eq])
        using Scc_list apply simp
        apply (simp add: V_def_set)
        using M0 is_sub_mdp apply force
        using S_prog Scc_list[THEN scc_list_states_eq] apply fastforce
        using L_prog2 EMP apply simp
        using L_prog EMP unfolding Cv_def apply simp
        done
    qed
  
  
    lemma final: assumes "it = {}" shows "M\<^sub>2=M" "j < length C \<Longrightarrow> L\<^sub>2 ! j = Cv ! j" "D\<^sub>2 = D @ V" and "S\<^sub>2 = S - \<Union> (set V)" and "Z\<^sub>2=Z"
      using assms L_prog D_prog S_prog by (auto simp: MDSKZ1_def L_prog)
  
  end
  
  subsection \<open>Refined Operations and Algorithm\<close>
  
  context mec_algo 
  begin
  
  
    definition "identify_mecs_fine C' = ( \<lambda> (M,D,S,K,Z). do{
      ASSERT(distinct C');
      let (C,V) = op_create_filter_set C';
      (C,V) \<leftarrow> FOREACHi (identify_mecs_fine_loop1_invar (M,D,S,K,Z) M\<^sub>0 C') (states M\<^sub>0) (\<lambda> u (C,V). 
      do {
        ASSERT(u \<in> (states M\<^sub>0));
        if (u \<notin> S) then 
          RETURN (C,V)
        else
        do {
          ASSERT(u \<in> S \<and> scc_list C S K);
          if (\<not>op_all_succ_eq_map (M,D,S,K,Z) (C,V) u) then do {
            ASSERT(\<exists> i < length C. u \<in> C ! i);
            i \<leftarrow> get_scc_val u C;
            ASSERT(i < length C);
            RETURN (C,V - {C!i})
          }
          else 
            RETURN (C,V)
        }
      }) (C,V); \<^cancel>\<open>Output: filter_index_set\<close>
  
      (C,V) \<leftarrow> set_to_list (C,V);
      RETURN (C,V) \<^cancel>\<open>Output: filter_index_list\<close>
    })"
  
  
    definition "cull_graph_fine = (\<lambda> (C,V) (M\<^sub>1,D\<^sub>1,S\<^sub>1,K\<^sub>1,Z\<^sub>1). do {
      let num = length C;
      ASSERT(num \<le> card (states M\<^sub>0));
      let numD = length D\<^sub>1;
      let numV = length V;
      ASSERT(numD + numV \<le> card (states M\<^sub>0));
      let (M,D,S,K,Z) = op_expand_capacity (M\<^sub>1,D\<^sub>1,S\<^sub>1,K\<^sub>1,Z\<^sub>1) numV;
      (M,L,D,S,K,Z) \<leftarrow> mop_track_sccs (M,D,S,K,Z) (C,V);
  
      MLDSKZ \<leftarrow> FOREACHi (cull_graph_fine_loop_invar M\<^sub>0 (M\<^sub>1,D\<^sub>1,S\<^sub>1,K\<^sub>1,Z\<^sub>1) C V) (states M\<^sub>0) (\<lambda> u (M,L,D,S,K,Z). 
      do { 
        ASSERT(u \<in> (states M\<^sub>0));
        if (u \<notin> S) then 
        do {
          RETURN (M,L,D,S,K,Z)
        }
        else do{
          ASSERT((\<exists>i<length C. u \<in> C ! i) \<and> (\<forall> i j. i < length C \<longrightarrow> j < length C \<longrightarrow> u \<in> C ! i \<longrightarrow> u \<in> C ! j \<longrightarrow> i = j) \<and> set V \<subseteq> set C);
          io \<leftarrow> mop_get_state_mec_id (C,V) u;
          case io of None \<Rightarrow> do {
            ASSERT (u \<notin> \<Union> (set D) \<and> (\<exists>j. u \<in> C ! j \<and> j < length C \<and> j < length L));
            mop_add_state_unfinished (M,L,D,S,K,Z) (C,V) u
          }
          | Some i \<Rightarrow> do {
            ASSERT (numD + i < card (states M\<^sub>0));
            let i' = numD + i;
            ASSERT(u \<notin> \<Union> (set D) \<and> i' < length D \<and> length D \<le> card (states M\<^sub>0));
            mop_add_state_to_mec (M,L,D,S,K,Z) (C,V) u i'
          }
        }
      }) (M,L,D,S,K,Z);
  
      ASSERT(mop_untrack_sccs_pre_cull (MLDSKZ, (C,V)));
      mop_untrack_sccs MLDSKZ (C,V)
    })"
  
    definition(in -) "unborrow_pre M\<^sub>0 = (\<lambda>(M,D,S,K,Z). M = M\<^sub>0)"
  
    definition "compute_MEC_fine \<equiv> do {
    
      MDSKZ \<leftarrow> mop_init_mdp M\<^sub>0;
  
      MDSKZ \<leftarrow> WHILEIT (compute_MEC_invar M\<^sub>0) op_states_non_empty 
      (\<lambda>(M,D,S,K,Z). do {
        
        \<comment>\<open>Compute the SCCs and remove any transitions that have branches leaving an SCC\<close>
        C \<leftarrow> compute_sccs (M,D,S,K,Z);
  
        ASSERT(scc_list C S K \<and> length C \<le> card (states M\<^sub>0));
        
        \<comment>\<open>Identify the SCCs that are MECs\<close>
        (C',V) \<leftarrow> identify_mecs_fine C (M,D,S,K,Z);
  
        ASSERT(C'=C \<and> distinct V \<and> set V = {S' \<in> set C. closed_mdp S' K} \<and> length D + length V \<le> card (states M\<^sub>0));
  
        \<comment>\<open>Remove the MECs from the graph and cull edges\<close>
        MDSKZ \<leftarrow> cull_graph_fine (C,V) (M,D,S,K,Z);
  
        RETURN MDSKZ
      }) MDSKZ; 
    
      ASSERT(get_mec_pre MDSKZ \<and> unborrow_pre M\<^sub>0 MDSKZ);
      let (D,M) = op_get_mecs MDSKZ;
      RETURN D
    }"
  
  end
  
  subsection \<open>Refinement of Operations\<close>
  
  context mec_algo
  begin
  
    lemma init_mdp_refine: "(op_init_mdp M\<^sub>0, op_init_mdp M\<^sub>0) \<in> Id"
      by simp
  
    lemma identify_mecs_refine: 
      assumes INV: "compute_MEC_invar M\<^sub>0 (M,D,S,K,Z)"
      and SCC: "scc_list C S K"
      and CID: "(C',C) \<in> Id"
      and MID: "((M',D',S',K',Z'), (M,D,S,K,Z)) \<in> Id"
      shows "identify_mecs_fine C' (M',D',S',K',Z') \<le> \<Down>Id (identify_mecs C (M,D,S,K,Z))"
    proof -
  
      from INV interpret compute_MEC_invar M\<^sub>0 "(M,D,S,K,Z)" by blast
  
      from CID MID have [simp]: "M' = M" "C' = C" "D' = D" "S' = S" "K' = K" "Z' = Z" by auto 
  
      from SCC have "\<forall> i < length C. \<exists> u \<in> (states M\<^sub>0). u \<in> C ! i"
        using nth_mem scc_non_empty' subset_states
        by (fastforce dest: scc_listD2) 
  
      show ?thesis
        unfolding identify_mecs_fine_def identify_mecs_def get_scc_val_def set_to_list_def
        apply(refine_vcg WHILEIT_rule[where ?R="measure (\<lambda> (i,_). length C - i)"])
        apply(vc_solve simp: SCC op_create_filter_setD identify_mecs_fine_loop1_invar_initial identify_mecs_fine_loop1_invar.case1 
          identify_mecs_fine_loop1_invar.case2 identify_mecs_fine_loop1_invar.case3 
          elim!: op_create_filter_setE 
          solve: ordered_list_distinct[OF SCC] identify_mecs_fine_loop1_invar.final identify_mecs_fine_loop1_invar.assert1
            identify_mecs_fine_loop1_invar.assert2)
        apply blast
        apply (auto dest: identify_mecs_fine_loop1_invar.xs_eq) []
        done
    qed
  
    lemma cull_graph_refine: 
      assumes INV: "compute_MEC_invar M\<^sub>0 (M,D,S,K,Z)"
      and SCC: "scc_list C S K"
      and C_BOUND: "length C \<le> card (states M\<^sub>0)"
      and MV_BOUND: "length D + length V \<le> card (states M\<^sub>0)"
      and CID: "(C',C) \<in> Id"
      and VID: "(V',V) \<in> Id"
      and MID: "((M',D',S',K',Z'), (M,D,S,K,Z)) \<in> Id"
      and VDEF: "set V = {S' \<in> set C. closed_mdp S' K}"
      and VDIS: "distinct V"
      shows "cull_graph_fine (C',V') (M',D',S',K',Z') \<le> \<Down>Id (cull_graph (C,V) (M,D,S,K,Z))"
    proof -
  
      from INV interpret compute_MEC_invar M\<^sub>0 "(M,D,S,K,Z)" by blast
  
      from CID VID MID have [simp]: "C' = C" "V' = V" "M' = M" "D'=D" "S' = S" "K' = K" "Z'=Z" by auto 
  
      from SCC have "\<forall> i < length C. \<exists> u \<in> (states M\<^sub>0). u \<in> C ! i"
        using nth_mem scc_non_empty' subset_states
        by (fastforce dest: scc_listD2) 
  
      interpret cull_graph_fine_loop_invar_pre M\<^sub>0 "(M,D,S,K,Z)"
        unfolding cull_graph_fine_loop_invar_pre_def
        using compute_MEC_invar_axioms by blast
  
  
      show ?thesis
        unfolding cull_graph_fine_def cull_graph_def mop_track_sccs_def mop_get_state_mec_id_def
          op_expand_capacity_def mop_add_state_to_mec_def mop_add_state_unfinished_def mop_untrack_sccs_def
        apply(refine_vcg) 
        apply(all clarify)(*Will take a while!*)
        apply(vc_solve) 
        subgoal using C_BOUND .
        subgoal using MV_BOUND .
        subgoal 
          by(auto intro!: pre_initial[simplified] simp: SCC VDEF VDIS)
        subgoal
          by blast
        subgoal for u it T M S K L
          apply(rule cull_graph_fine_loop_invar.case1)
          using SCC VDEF VDIS by auto
        subgoal by(auto dest: cull_graph_fine_loop_invar.assert1) 
        subgoal by(auto intro: scc_list_unique_index[OF SCC])
        subgoal
          using cull_graph_fine_loop_invar.set_C_int_V_def by fastforce
        subgoal for L' u it L M S K i X j
          by (auto dest!: cull_graph_fine_loop_invar.assert2[where ?u=u])
        subgoal
          using cull_graph_fine_loop_invar.D_prog by fastforce
        subgoal apply(drule cull_graph_fine_loop_invar.length_D2) by force
        subgoal 
          apply(erule notE)
          apply(rule cull_graph_fine_loop_invar.case2)
          apply(clarsimp_all)
          using SCC VDEF VDIS by (fastforce dest: cull_graph_fine_loop_invar.MC)+
        subgoal for L' u it L M S K X i 
          by (auto dest!: cull_graph_fine_loop_invar.assert2[where ?u=u])
        subgoal
          by (fastforce dest: cull_graph_fine_loop_invar.L_len) 
        subgoal 
          using SCC VDEF VDIS
          by (auto dest: cull_graph_fine_loop_invar.MC intro!: cull_graph_fine_loop_invar.case3)
        subgoal by(auto elim: cull_graph_fine_loop_invar.assert3)
        subgoal
          by(auto dest!: cull_graph_fine_loop_invar.final(1))
        subgoal 
          by(auto dest!: cull_graph_fine_loop_invar.final(3))
        subgoal 
          by(auto dest!: cull_graph_fine_loop_invar.final(4))
        subgoal using M0 
          by(auto dest!: cull_graph_fine_loop_invar.final(1) simp: cull_graph_orig[simplified, OF SCC])
        subgoal 
          by(auto dest!: cull_graph_fine_loop_invar.final(5))
        done
        
    qed
  
    lemma compute_sccs_refine: "(MDSKZ',MDSKZ) \<in> Id \<Longrightarrow> compute_sccs MDSKZ' \<le> \<Down>Id (compute_sccs MDSKZ)"
      by simp
  end
  
  
  subsection \<open>Refinement of the algorithm\<close>
  
  
  context mec_algo
  begin
  
  
    lemma compute_MEC_fine_refine: "compute_MEC_fine \<le> \<Down>Id compute_MEC"
      unfolding compute_MEC_fine_def compute_MEC_def ASSERT_over_prod
      apply(refine_vcg 
        init_mdp_refine
        identify_mecs_refine 
        cull_graph_refine  
        compute_sccs_refine)
      apply assumption
      apply (vc_solve simp: unborrow_pre_def)
      done
  
  end


end
