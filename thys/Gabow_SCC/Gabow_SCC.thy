section \<open>Enumerating the SCCs of a Graph \label{sec:scc}\<close>
theory Gabow_SCC
imports Gabow_Skeleton
begin

  text \<open>
    We implement an algorithm that computes a list of SCCs 
    of a graph, in topological order. This is the standard variant described by
    Gabow~\cite{Gabow2000}.
  \<close>
  section \<open>General lemmas\<close>
    lemma insert_Suc_elem: "{P j |j. j < Suc n} = insert (P n) {P j |j. j < n}"
      apply auto
      by (metis less_SucE)
  
    lemma insert_Suc_elem_image: "n \<le> i \<Longrightarrow> A ` {n..<Suc i} = insert (A i) (A ` {n..<i})" 
      apply(induction i)
      apply auto
      by (metis atLeastLessThan_iff imageI less_SucE)
  
    lemma cond_set_eq: "\<lbrakk>\<And>x. P x \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> {f x |x. P x} = {g x |x. P x}"
      by metis
  
  
    lemma cond_set_eq_image: "\<lbrakk>\<And>i. i\<in>I \<Longrightarrow> P i = Q i\<rbrakk> \<Longrightarrow> P ` I = Q ` I"
      by simp 
  
    lemma fin_nonempty_card_gt_1:
      "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> card A \<ge> 1"
      apply(cases "card A = 0")
      apply simp
      by linarith
  
    lemma fin_disj_union_card: 
      assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
      and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
      and "\<forall>i \<in> I. A i \<noteq> {}" 
      shows "card I \<le> card (\<Union> (A ` I))"
    proof -
      have "\<forall>i\<in>I. card (A i) \<ge> 1"
        using fin_nonempty_card_gt_1 assms(2) assms(4) by fast
      hence "\<forall>i\<in>I.(\<Sum>x\<in>A i. Suc 0) \<ge> Suc 0" 
        by(simp add: card_eq_sum sum.UNION_disjoint del: sum_constant)
      hence "(\<Sum>x\<in>I. Suc 0) \<le> (\<Sum>x\<in>I. \<Sum>x\<in>A x. Suc 0)" 
        by (meson sum_mono)
      moreover have "(\<Sum>i\<in>I. card (A i)) = (\<Sum>i\<in>I. \<Sum>x\<in>A i. 1)"
        by simp
      ultimately show ?thesis using assms
        by(simp add: card_eq_sum sum.UNION_disjoint del: sum_constant)
    qed
  
  
  lemma card_UN_disjoint:
    assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
      and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
    shows "card (\<Union>(A ` I)) = (\<Sum>i\<in>I. card(A i))"
  proof -
    have "(\<Sum>i\<in>I. card (A i)) = (\<Sum>i\<in>I. \<Sum>x\<in>A i. 1)"
      by simp
    with assms show ?thesis
      by (simp add: card_eq_sum sum.UNION_disjoint del: sum_constant)
  qed
  
  context mdp_graph_defs
  begin
  
    definition "scc_set = {scc. is_scc E_\<alpha> scc \<and> scc \<subseteq> E_\<alpha>\<^sup>* `` V0}"
  
    lemma scc_set_mem: "s \<in> scc_set \<longleftrightarrow> is_scc E_\<alpha> s \<and> s \<subseteq> E_\<alpha>\<^sup>* `` V0"
      unfolding scc_set_def by simp
  
    lemma scc_set_of_scc: "scc_set \<subseteq> Collect (is_scc E_\<alpha>)"
      unfolding scc_set_def
      by blast
  
    lemma scc_set_disj: "SCC1 \<in> scc_set \<Longrightarrow> SCC2 \<in> scc_set \<Longrightarrow> SCC1 \<noteq> SCC2 \<Longrightarrow> SCC1 \<inter> SCC2 = {}"
      unfolding scc_set_def
      using scc_disj_or_eq by auto
  
    lemma scc_set_alt_def: "scc_set = scc_of E_\<alpha> ` (E_\<alpha>\<^sup>* `` V0)"
    proof -
      {
        fix S
        assume "S \<in> scc_set"
        hence "is_scc E_\<alpha> S" and "S \<subseteq> E_\<alpha>\<^sup>* `` V0" unfolding scc_set_def by auto
        moreover then obtain v where "v \<in> S" and "S = scc_of E_\<alpha> v"  
          by (metis is_scc_unique node_in_scc_of_node scc_non_empty' scc_of_is_scc subset_empty subset_emptyI)
        ultimately have "S \<in> scc_of E_\<alpha> ` E_\<alpha>\<^sup>* `` V0" by fast
      } note AUX1 = this
  
      {
        fix S
        assume "S \<in> scc_of E_\<alpha> ` E_\<alpha>\<^sup>* `` V0"
        then obtain v where VREACH: "v \<in> E_\<alpha>\<^sup>* `` V0" and "S = scc_of E_\<alpha> v" and SCC: "is_scc E_\<alpha> S" and VMEM: "v \<in> S"
          by(auto simp: image_iff)
        have "S \<subseteq> E_\<alpha>\<^sup>* `` V0" 
        proof safe
          fix x
          assume "x \<in> S"
          with SCC VMEM have "(v,x) \<in> E_\<alpha>\<^sup>*" 
            unfolding is_scc_def 
            by blast
          with VREACH show "x \<in> E_\<alpha>\<^sup>* `` V0" 
            using rtrancl_image_advance_rtrancl
            by fast
        qed
        hence  "S \<in> scc_set" 
          unfolding scc_set_def 
          using SCC 
          by simp
      } note AUX2 = this
      from AUX1 AUX2 show ?thesis by blast
    qed
  
    definition "ordered l = (\<forall>i j. i < j \<longrightarrow> j < length l \<longrightarrow> l!i \<times> l!j \<inter> E_\<alpha>\<^sup>* = {})"
  
    lemma empty_ordered[simp]: "ordered []"
      unfolding ordered_def by simp
  
    definition "compute_SCC_spec \<equiv> SPEC (\<lambda> l. set l = scc_set \<and> ordered l)"
  
  end
  
  section \<open>Specification\<close>
  context mdp_graph
  begin
    text \<open>We specify a distinct list that covers all reachable nodes and
      contains SCCs in topological order\<close>
  
    lemma scc_set_covers_state_space: "\<Union> scc_set = E_\<alpha>\<^sup>* `` V0"
      proof(safe)
        fix x SCC
        assume "x \<in> SCC" "SCC \<in> scc_set"
        then show "x \<in> E_\<alpha>\<^sup>* `` V0" 
          unfolding scc_set_def 
          by blast
      next
        fix u v
        assume "(u,v) \<in> E_\<alpha>\<^sup>*" "u \<in> V0"
        hence A: "v \<in> E_\<alpha>\<^sup>* `` V0" by blast
        obtain SCC where B: "v \<in> SCC" "is_scc E_\<alpha> SCC"
          by (meson is_scc_ex)
        hence "SCC \<subseteq> E_\<alpha>\<^sup>* `` V0"
          using A is_scc_connected rtrancl_trans by fast
        with B show "v \<in> \<Union> scc_set"
          unfolding scc_set_def by blast
      qed
        
  
    lemma finite_scc_set: "finite scc_set"
      using finite_reachableE_V0 unfolding scc_set_def by auto
  
  end
  
  section \<open>Extended Invariant\<close>
  
  locale cscc_invar_ext = mdp_graph MG V\<^sub>i for MG :: "'v mdpG" and  V\<^sub>i :: "'v set" + 
    fixes l :: "'v set list" and D :: "'v set"
    assumes scc_is_D: "\<Union> (set l) = D" \<comment> \<open>The output contains all done CNodes\<close>
    assumes is_scc_set: "set l \<subseteq> scc_set" \<comment> \<open>The output contains only SCCs\<close>
    assumes scc_nforward: "ordered l" \<comment> \<open>The output contains no forward edges\<close>
  begin
  
    lemma reachable_scc: assumes "U \<in> set l" shows "is_scc E_\<alpha> U" and "U \<subseteq> E_\<alpha>\<^sup>* `` V0"
      using assms is_scc_set
      apply(auto simp: scc_set_def)
      done
  
    lemma scc_nforward_append:
      assumes NBACK_IN_NEW: "(\<And> k1 k2. k1 < k2 \<Longrightarrow> k2 < length nl \<Longrightarrow> nl!k1 \<times> nl!k2 \<inter> E_\<alpha>\<^sup>* = {})"
      assumes NBACK_TO_NEW: "(\<And> k1 k2. k1 < length l \<Longrightarrow> k2 < length nl \<Longrightarrow> l!k1 \<times> nl!k2 \<inter> E_\<alpha>\<^sup>* = {})"
      assumes JLEN_LT: "j < length l + length nl"
      assumes IJ_LT: "i < j"
      shows "(l @ nl)!i \<times> (l @ nl)!j \<inter> E_\<alpha>\<^sup>* = {}"
      apply(cases "j < length l")
        subgoal using IJ_LT by (simp add: scc_nforward[unfolded ordered_def])
        subgoal apply(cases "i < length l")
          subgoal 
            apply(simp add: nth_append)
            apply(rule NBACK_TO_NEW)
            using JLEN_LT by auto
          subgoal 
            apply(simp add: nth_append)
            apply(rule NBACK_IN_NEW)
            using JLEN_LT IJ_LT by auto 
        done
      done
  
    lemma scc_done: "i < length l \<Longrightarrow> l!i \<subseteq> D"
      using scc_is_D by force
      
  end
    
  locale cscc_outer_invar_loc = outer_invar_loc MG V\<^sub>i it D + cscc_invar_ext MG V\<^sub>i l D
    for MG :: "'v mdpG" and  V\<^sub>i :: "'v set" and it l D 
  begin
    lemma locale_this: "cscc_outer_invar_loc MG V\<^sub>i it l D" by unfold_locales
    lemma abs_outer_this: "outer_invar_loc MG V\<^sub>i it D" by unfold_locales
  end
  
  locale cscc_invar_loc = invar_loc MG V\<^sub>i v0 D0 p D pE vE + cscc_invar_ext MG V\<^sub>i l D
    for MG :: "'v mdpG" and  V\<^sub>i :: "'v set" and v0 D0 and l :: "'v set list" 
    and p D pE vE
  begin
    lemma locale_this: "cscc_invar_loc MG V\<^sub>i v0 D0 l p D pE vE" by unfold_locales
    lemma invar_this: "invar_loc MG V\<^sub>i v0 D0 p D pE vE" by unfold_locales
  end
  
  context mdp_graph
  begin                                                    
    definition "cscc_outer_invar \<equiv> \<lambda>it (SCC,D). cscc_outer_invar_loc MG V\<^sub>i it SCC D"
    definition "cscc_invar \<equiv> \<lambda>v0 D0 (SCC,p,D,pE,vE). cscc_invar_loc MG V\<^sub>i v0 D0 SCC p D pE vE"
  end
  
  section \<open>Definition of the SCC-Algorithm\<close>
  
  context mdp_graph
  begin
  
    definition "build_scc = (\<lambda> (l,p,D,pE,vE). 
      do{
        let l = l @ [last p];
        let (p,D,pE,vE) = pop (p,D,pE,vE);
        (l,p,D,pE,vE)
      })"
  
    lemma invar_build_scc:
      assumes INV: "invar v0 D0 (p,D,pE,vE)"
      assumes NE[simp]: "p\<noteq>[]"
      assumes NO': "(set_mset pE) \<inter> (last p \<times> UNIV) = {}"
      shows "invar v0 D0 (snd (build_scc (l,p,D,pE,vE)))"
      unfolding build_scc_def
      using invar_pop[OF assms]
      by force
  
    lemma abs_wf_build_scc:
      assumes NE: "p\<noteq>[]"
      shows "(snd (build_scc (SCC,p,D,pE,vE)), (p, D, pE, vE)) \<in> abs_wf_rel v0"
      unfolding build_scc_def
      using abs_wf_pop[OF NE]
      by force
  
  
    definition "initial_S l v0 D0 \<equiv> do {
      s \<leftarrow> initial v0 D0;
      RETURN (l,s)
    }"
  
    definition "push_S v \<equiv> (\<lambda> (l,p,D,pE,vE). do {
      (p,D,pE,vE) \<leftarrow> push v (p,D,pE,vE);
      RETURN (l,p,D,pE,vE)
    })"
  
    definition "select_edge_S \<equiv> \<lambda>(l,PDPE). do { (r,PDPE)\<leftarrow>select_edge PDPE; RETURN (r,(l,PDPE)) }"
  
    definition compute_SCC :: "'v set list nres" where
      "compute_SCC \<equiv> do {
        let so = ([],{});
        (l,D) \<leftarrow> FOREACHi cscc_outer_invar V\<^sub>i (\<lambda>v0 (l0,D0). do {
          if v0 \<in> V0 \<and> v0\<notin>D0 then do {
            ASSERT(v0 \<in> E_\<alpha>\<^sup>*``V0);
            s \<leftarrow> initial_S l0 v0 D0;
  
            (l,p,D,pE,vE) \<leftarrow>
            WHILEIT (cscc_invar v0 D0)
              (\<lambda>(l,p,D,pE,vE). p \<noteq> []) (\<lambda>(l,p,D,pE,vE). 
            do {
              \<comment> \<open>Select edge from end of path\<close>
              (vo,(l,p,D,pE,vE)) \<leftarrow> select_edge_S (l,p,D,pE,vE);
  
              ASSERT (p\<noteq>[]);
              case vo of 
                Some v \<Rightarrow> do {
                  ASSERT (v \<in> E_\<alpha>\<^sup>* `` V0);
                  if v \<in> \<Union>(set p) then do {
                    \<comment> \<open>Collapse\<close>
                    RETURN (l,collapse v (p,D,pE,vE))
                  } else if v\<notin>D then do {
                    \<comment> \<open>Edge to new node. Append to path\<close>
                    push_S v (l,p,D,pE,vE)
                  } else RETURN (l,p,D,pE,vE)
                }
              | None \<Rightarrow> do {
                  \<comment> \<open>No more outgoing edges from current node on path\<close>
                  ASSERT ((set_mset pE) \<inter> last p \<times> UNIV = {});
                  RETURN (build_scc (l,p,D,pE,vE))
                }
            }) s;
            ASSERT (p=[] \<and> pE={#});
            RETURN (l,D)
          } else
            RETURN (l0,D0)
        }) so;
        RETURN l
      }"
  end
  
  
  context mdp_graph
  begin
    definition "cscc_invar_part \<equiv> \<lambda>(SCC,p,D,pE). cscc_invar_ext MG V\<^sub>i SCC D"
  
    lemma cscc_invarI:
      assumes "invar v0 D0 PDPE"
      assumes "invar v0 D0 PDPE \<Longrightarrow> cscc_invar_part (SCC,PDPE)"
      shows "cscc_invar v0 D0 (SCC,PDPE)"
      using assms
      unfolding cscc_invar_def invar_def
      apply (simp split: prod.split_asm)
      apply intro_locales
      apply (simp add: invar_loc_def)
      apply (simp add: cscc_invar_part_def cscc_invar_ext_def)
      done
  
  
    lemma cscc_outer_invarI[intro?]:
      assumes "outer_invar it D"
      assumes "outer_invar it D \<Longrightarrow> cscc_invar_ext MG V\<^sub>i SCC D"
      shows "cscc_outer_invar it (SCC,D)"
      using assms
      unfolding cscc_outer_invar_def outer_invar_def
      apply (simp split: prod.split_asm)
      apply intro_locales
      apply (simp add: outer_invar_loc_def)
      apply (simp add: cscc_invar_ext_def)
      done
  
    lemma cscc_invar_initial:
      assumes A: "v0\<in>it" "v0\<notin>D0"
      assumes INV: "cscc_outer_invar it (SCC,D0)"
      shows "initial v0 D0 \<le> SPEC (\<lambda> (p,D,pE,vE). cscc_invar_part (SCC,p,D,pE,vE))"
      unfolding initial_def out_edges_def
      apply refine_vcg
      apply clarsimp
    proof -
      fix pE'
      assume "set_mset pE' = E_\<alpha> \<inter> {v0} \<times> UNIV"
  
      from INV interpret cscc_outer_invar_loc MG V\<^sub>i it SCC D0 
        unfolding cscc_outer_invar_def by simp
      
      show "cscc_invar_part (SCC, [{v0}], D0, pE', E_\<alpha> \<inter> D0 \<times> UNIV)"
        unfolding cscc_invar_part_def initial_def
        apply simp
        by unfold_locales
    qed
  
    lemma cscc_invar_pop_aux:
      assumes INV: "cscc_invar v0 D0 (l,p,D,pE,vE)"
      assumes NE[simp]: "p\<noteq>[]"
      assumes NO': "(set_mset pE) \<inter> (last p \<times> UNIV) = {}"
      shows "cscc_invar_part (l @ [last p], pop (p,D,pE,vE))"
    proof -
      from INV interpret cscc_invar_loc MG V\<^sub>i v0 D0 l p D pE 
        unfolding cscc_invar_def by simp
  
      have AUX_l_scc: "is_scc E_\<alpha> (last p)"
        unfolding is_scc_pointwise
      proof safe
        {
          assume "last p = {}" thus False 
            using p_no_empty by (cases p rule: rev_cases) auto 
        }
  
        fix u v
        assume "u\<in>last p" "v\<in>last p"
        with p_sc[of "last p"] have "(u,v) \<in> (vE \<inter> last p \<times> last p)\<^sup>*" by auto
        with vE_ss_E show "(u,v)\<in>(E_\<alpha> \<inter> last p \<times> last p)\<^sup>*"
          by (metis Int_mono equalityE rtrancl_mono_mp)
        
        fix u'
        assume "u'\<notin>last p" "(u,u')\<in>E_\<alpha>\<^sup>*" "(u',v)\<in>E_\<alpha>\<^sup>*"
  
        from \<open>u'\<notin>last p\<close> \<open>u\<in>last p\<close> \<open>(u,u')\<in>E_\<alpha>\<^sup>*\<close>
          and rtrancl_reachable_induct[OF order_refl lastp_un_D_closed[OF NE NO']]
        have "u'\<in>D" by auto
        with \<open>(u',v)\<in>E_\<alpha>\<^sup>*\<close> and rtrancl_reachable_induct[OF order_refl D_closed] 
        have "v\<in>D" by auto
        with \<open>v\<in>last p\<close> p_not_D show False by (cases p rule: rev_cases) auto
      qed
  
      have scc_no_back: "i < length l \<Longrightarrow> l ! i \<times> last p \<inter> E_\<alpha>\<^sup>* = {}" for i
      proof(rule ccontr)
        assume A: "i < length l" and B: "l ! i \<times> last p \<inter> E_\<alpha>\<^sup>* \<noteq> {}"
        then obtain u v where UMEM: "u \<in> l ! i" and VMEM: "v \<in> last p" and UVE: "(u,v) \<in> E_\<alpha>\<^sup>*" by blast
        moreover have "u \<in> D" using scc_done[OF A] UMEM by blast
        ultimately have "v \<in> D" using D_image_closed by blast
        then show False using p_not_D VMEM by fastforce
      qed
  
        
      have "last p \<subseteq> E_\<alpha>\<^sup>* `` V0" using p_elem_reachable
        by force 
  
      thus ?thesis
        unfolding cscc_invar_part_def pop_def apply simp
        apply unfold_locales
        subgoal using scc_is_D by simp
        subgoal using is_scc_set AUX_l_scc by(simp add: scc_set_mem)
        subgoal
          unfolding ordered_def
          apply(rule allI)+
          apply(rule impI)+
          subgoal for i j
            apply(rule scc_nforward_append)
            by (auto intro!: scc_no_back)
          done
        done
    qed
  
  
    lemma cscc_invar_build_scc:
      assumes CINV: "cscc_invar v0 D0 (l,p,D,pE,vE)"
      assumes NE[simp]: "p\<noteq>[]"
      assumes NO': "(set_mset pE) \<inter> (last p \<times> UNIV) = {}"
      shows "cscc_invar v0 D0 (build_scc (l,p,D,pE,vE))"
    proof -
      from CINV have INV: "invar v0 D0 (p, D, pE, vE)" 
        unfolding cscc_invar_def invar_def 
        using cscc_invar_loc.invar_this 
        by fast
  
      have INV_BUILD: "invar v0 D0 (snd (build_scc (l, p, D, pE, vE)))" 
        using invar_build_scc[OF INV NE NO'] 
        by blast
  
      have build_scc_decomp: "(l @ [last p], snd (build_scc (l, p, D, pE, vE))) = build_scc (l, p, D, pE, vE)"
        unfolding build_scc_def by auto
  
      have "cscc_invar_part (build_scc (l, p, D, pE, vE))"
        using cscc_invar_pop_aux[OF assms] 
        unfolding build_scc_def
        by force
  
      thus ?thesis using cscc_invarI[OF INV_BUILD, of "l @ [last p]"] 
        unfolding build_scc_decomp by simp
    qed
  
  
    lemma cscc_invar_unchanged: 
      assumes INV: "cscc_invar v0 D0 (l,p,D,pE,vE)"
      shows "cscc_invar_part (l,p',D,pE',vE')"
      using INV unfolding cscc_invar_def cscc_invar_part_def cscc_invar_loc_def
      by simp
  
    corollary cscc_invar_collapse:
      assumes INV: "cscc_invar v0 D0 (l,p,D,pE,vE)"
      shows "cscc_invar_part (l,collapse v (p',D,pE',vE'))"
      unfolding collapse_def
      by (simp add: cscc_invar_unchanged[OF INV])
  
    corollary cscc_invar_push:
      assumes INV: "cscc_invar v0 D0 (l,p,D,pE,vE)"
      shows "push v (p',D,pE',vE') \<le> SPEC (\<lambda> (p,D,pE,vE). cscc_invar_part (l,p,D,pE,vE))"
      unfolding push_def out_edges_def
      apply refine_vcg
      by (simp add: cscc_invar_unchanged[OF INV])
  
  
    lemma cscc_outer_invar_initial: "cscc_invar_ext MG V\<^sub>i [] {}"
      by unfold_locales auto
  
  
    lemma cscc_invar_outer_newnode:
      assumes A: "v0\<notin>D0" "v0\<in>it" 
      assumes OINV: "cscc_outer_invar it (l,D0)"
      assumes INV: "cscc_invar v0 D0 (l',[],D',pE,vE)"
      shows "cscc_invar_ext MG V\<^sub>i l' D'"
    proof -
      from OINV interpret cscc_outer_invar_loc MG V\<^sub>i it l D0 
        unfolding cscc_outer_invar_def by simp
      from INV interpret inv: cscc_invar_loc MG V\<^sub>i v0 D0 l' "[]" D' pE vE
        unfolding cscc_invar_def by simp
      
      show ?thesis 
        by unfold_locales
  
    qed
  
    lemma cscc_invar_outer_Dnode:
      assumes "cscc_outer_invar it (SCC, D)"
      shows "cscc_invar_ext MG V\<^sub>i SCC D"
      using assms
      by (simp add: cscc_outer_invar_def cscc_outer_invar_loc_def)
      
    lemmas cscc_invar_preserve = invar_preserve
      abs_wf_build_scc cscc_invar_build_scc
       cscc_invar_collapse cscc_invar_push cscc_invar_unchanged 
      cscc_outer_invar_initial cscc_invar_outer_newnode cscc_invar_outer_Dnode
  
    text \<open>On termination, the invariant implies the specification\<close>
    lemma cscc_finI:
      assumes INV: "cscc_outer_invar {} (l,D)"
      shows fin_SCC_is_scc: "\<lbrakk>U\<in>set l\<rbrakk> \<Longrightarrow> is_scc E_\<alpha> U"
      and fin_SCC_is_reachable: "\<Union> (set l) = E_\<alpha>\<^sup>* `` V0"
      and fin_reach_scc_in_SCC: "is_scc E_\<alpha> U \<Longrightarrow> U \<subseteq> E_\<alpha>\<^sup>* `` V0\<Longrightarrow> U \<in> set l"
    proof -
      from INV interpret cscc_outer_invar_loc MG V\<^sub>i "{}" l D
        unfolding cscc_outer_invar_def by simp
  
      show "\<lbrakk>U\<in>set l\<rbrakk> \<Longrightarrow> is_scc E_\<alpha> U" using reachable_scc(1) .
  
      show A: "\<Union> (set l) = E_\<alpha>\<^sup>* `` V0"
        using fin_outer_D_is_reachable[OF outer_invar_this] scc_is_D
        by auto
      
      show "is_scc E_\<alpha> U \<Longrightarrow> U \<subseteq> E_\<alpha>\<^sup>* `` V0 \<Longrightarrow> U \<in> set l" 
      proof (rule ccontr)
        assume U_SCC: "is_scc E_\<alpha> U" and U_REACH: "U \<subseteq> E_\<alpha>\<^sup>* `` V0" and U_NOT_SCC: "U \<notin> set l"
        
        from U_NOT_SCC have "\<And> U2. U2 \<in> set l \<Longrightarrow> U2 \<inter> U = {}" 
          using scc_disj_or_eq[OF U_SCC] reachable_scc(1) by blast
        with A have "E_\<alpha>\<^sup>* `` V0 \<inter> U = {}" by blast
        hence "\<not>U \<subseteq> E_\<alpha>\<^sup>* `` V0" using scc_non_empty'[OF U_SCC] by blast
        thus False using U_REACH by simp
      qed
    qed
  
  end
  
  section \<open>Main Correctness Proof\<close>
  
  context mdp_graph 
  begin
    lemma invar_from_cscc_invarI: "cscc_invar v0 D0 (L,PDPE) \<Longrightarrow> invar v0 D0 PDPE"
      unfolding cscc_invar_def invar_def
      apply (simp split: prod.splits)
      unfolding cscc_invar_loc_def by simp
  
    lemma outer_invar_from_cscc_invarI: 
      "cscc_outer_invar it (L,D) \<Longrightarrow>outer_invar it D"
      unfolding cscc_outer_invar_def outer_invar_def
      apply (simp split: prod.splits)
      unfolding cscc_outer_invar_loc_def by simp
  
    text \<open>With the extended invariant and the auxiliary lemmas, the actual 
      correctness proof is straightforward:\<close>
  
    lemmas [refine_vcg del] = invar_initial
  
    theorem compute_SCC_correct: "compute_SCC \<le> compute_SCC_spec"
    proof -
      note [[goals_limit = 54]]
      note [simp del] = Union_iff
  
      note [refine_vcg del] = WHILEIT_rule
  
      show ?thesis
        unfolding compute_SCC_def compute_SCC_spec_def select_edge_def select_def initial_S_def push_S_def select_edge_S_def
        apply (refine_vcg 
          SPEC_rule_conjI[OF invar_initial cscc_invar_initial] 
          WHILEIT_rule[where R="inv_image (abs_wf_rel v0) snd" for v0])
        apply (vc_solve
          rec: cscc_outer_invarI
          solve: cscc_invar_preserve cscc_outer_invar_initial
          intro!: outer_invar_from_cscc_invarI
        )
  
        apply (auto intro!: outer_invar_from_cscc_invarI)
  
        apply (vc_solve
          rec: cscc_invarI cscc_outer_invarI
          solve: cscc_invar_preserve 
          intro!: invar_from_cscc_invarI outer_invar_from_cscc_invarI 
          simp: pE_fin'[OF invar_from_cscc_invarI] finite_V0 
        )
        apply(auto intro: invar_from_cscc_invarI invar_pE_is_node)[3]
  
        apply(refine_vcg SPEC_rule_conjI[OF cscc_invar_push invar_rel_push])
  
        apply (auto intro!: invar_from_cscc_invarI)[2]
        apply (auto intro!: cscc_invarI) [2]
        using cscc_invar_ext.is_scc_set cscc_invar_outer_Dnode apply blast
        apply (simp add: fin_reach_scc_in_SCC scc_set_def)
  
        unfolding cscc_outer_invar_def cscc_outer_invar_loc_def cscc_invar_ext_def cscc_invar_ext_axioms_def
        by blast
    qed
  
  end
  
  
  section \<open>Refinement to Gabow's Data Structure\<close>
  
  text \<open>
    Most work has already been done in the skeleton. We adapt for the extended refinement relation
    and implement the new function \<open>build_scc\<close> here.
  \<close>
  
  context GS begin
    definition "seg_set_impl l u \<equiv> do {
      (_,res) \<leftarrow> WHILET
        (\<lambda>(l,_). l<u) 
        (\<lambda>(l,res). do { 
          ASSERT (l<length S); 
          let x = S!l;
          ASSERT (x\<notin>res); 
          RETURN (Suc l,insert x res)
        }) 
        (l,{});
        
      RETURN res
    }"
  
    lemma seg_set_impl_aux:
      fixes l u
      shows "\<lbrakk>l<u; u\<le>length S; distinct S\<rbrakk> \<Longrightarrow> seg_set_impl l u 
      \<le> SPEC (\<lambda>r. r = {S!j | j. l\<le>j \<and> j<u})"
      unfolding seg_set_impl_def
      apply (refine_rcg 
        WHILET_rule[where 
          I="\<lambda>(l',res). res = {S!j | j. l\<le>j \<and> j<l'} \<and> l\<le>l' \<and> l'\<le>u"
          and R="measure (\<lambda>(l',_). u-l')" 
        ]
        refine_vcg)
  
      apply (auto simp: less_Suc_eq nth_eq_iff_index_eq)
      done
  
    lemma (in GS_invar) seg_set_impl_correct:
      assumes "i<length B"
      shows "seg_set_impl (seg_start i) (seg_end i) \<le> SPEC (\<lambda>r. r=p_\<alpha>!i)"
      apply (refine_rcg order_trans[OF seg_set_impl_aux] refine_vcg)
  
      using assms 
      apply (simp_all add: seg_start_less_end seg_end_bound S_distinct) [3]
  
      apply (auto simp: p_\<alpha>_def assms seg_def) []
      done
  
    definition "last_seg_impl 
      \<equiv> do {
        ASSERT (length B - 1 < length B);
        seg_set_impl (seg_start (length B - 1)) (seg_end (length B - 1))
      }"
  
    lemma (in GS_invar) last_seg_impl_correct:
      assumes "p_\<alpha> \<noteq> []"
      shows "last_seg_impl \<le> SPEC (\<lambda>r. r=last p_\<alpha>)"
      unfolding last_seg_impl_def
      apply (refine_rcg order_trans[OF seg_set_impl_correct] refine_vcg)
      using assms apply (auto simp add: p_\<alpha>_def last_conv_nth)
      done
  
  end
  
  
  definition oGSS_\<alpha> :: "'v oGS \<Rightarrow> nat \<Rightarrow> ('v set list \<times> 'v set)" where "oGSS_\<alpha> I i \<equiv> (SCC_\<alpha> I i, oGS_\<alpha> I)"
  
  
  locale GSS_invar_ext = mdp_graph MG V\<^sub>i for MG :: "'v mdpG" and V\<^sub>i :: "'v set" +
    fixes I :: "'v oGS"
    fixes i :: "nat"
    assumes non_empty_scc: "j < i \<Longrightarrow> SCC_at I j \<noteq> {}"
    assumes empty_not_scc: "j \<ge> i \<Longrightarrow> SCC_at I j = {}"
    assumes finite_scc: "finite (SCC_at I j)"
    assumes I_reachable: "I v \<noteq> None \<longrightarrow> v \<in> E_\<alpha>\<^sup>*``V0"
    assumes i_bound: "i \<le> card (E_\<alpha>\<^sup>*``V0)"
    assumes I_bound: "\<forall> j. case I j of 
      None \<Rightarrow> True
    | Some ns \<Rightarrow> (case ns of
        STACK n \<Rightarrow> n < card (E_\<alpha>\<^sup>*``V0)
      | DONE d \<Rightarrow> d < i
    )"
  begin
  
    lemma I_reachable': "I v = None \<or> v \<in> E_\<alpha>\<^sup>*``V0" 
      using I_reachable 
      by blast
  
    lemma SCC_at_disj: "j \<noteq> k \<Longrightarrow> SCC_at I j \<inter> SCC_at I k = {}" 
      unfolding SCC_at_def by fastforce
  
    lemma non_eq_scc: "j < i \<Longrightarrow> k \<noteq> j \<Longrightarrow> SCC_at I j \<noteq> SCC_at I k"
      using SCC_at_disj non_empty_scc by fast
  
    lemma card_scc_j: "j \<le> i \<Longrightarrow> length (SCC_\<alpha> I j) = j" 
      unfolding SCC_\<alpha>_def 
      proof (induction j)
        case 0
        then show ?case by simp
      next
        case (Suc j)
  
        have "card (SCC_at I  ` {0..<Suc j}) = card (insert (SCC_at I j) (SCC_at I  ` {0..<j}))" 
          unfolding insert_Suc_elem_image[of 0, simplified] by blast
        moreover have "SCC_at I j \<notin> (SCC_at I  ` {0..<j})" 
          using non_eq_scc[OF Suc_le_lessD[OF Suc.prems]]
          by fastforce
        moreover have "finite (SCC_at I  ` {0..<j})" by simp
        ultimately show ?case using card_insert_disjoint Suc 
          by simp
      qed
  
    lemma card_scc_i: "length (SCC_\<alpha> I i) = i"
      using card_scc_j
      by simp
  
    lemma "j < i \<Longrightarrow> \<exists> v. I v = Some (DONE j)"
      using non_empty_scc
      unfolding SCC_at_def
      by blast
  
  
    lemma "j \<ge> i \<Longrightarrow> \<forall> v. I v \<noteq> Some (DONE j)"
      using empty_not_scc
      unfolding SCC_at_def
      by blast
  
    lemma DONE_j_less_i: "I v = Some (DONE j) \<Longrightarrow> j < i"
      apply (rule ccontr)
      apply (drule leI)
      apply (drule empty_not_scc)
      unfolding SCC_at_def
      by blast
  
    lemma j_less_i_DONE: "j < i \<longleftrightarrow> (\<exists> v. I v = Some (DONE j))"
      using non_empty_scc empty_not_scc
      unfolding SCC_at_def 
      by fastforce
  
    lemma invar_card_D_bound: "outer_invar_loc MG V\<^sub>i it D \<Longrightarrow> card D \<le> card (E_\<alpha>\<^sup>*``V0)"
      apply (rule card_mono)
      apply (auto simp: outer_invar_loc_def outer_invar_loc_axioms_def)
      done
  
    lemma oGS_\<alpha>_alt_def: "oGS_\<alpha> I = \<Union> (set (SCC_\<alpha> I i))"
      by (auto simp: oGS_\<alpha>_def SCC_\<alpha>_def SCC_at_def dest: DONE_j_less_i) 
  
    lemma i_bound_SCC: "i \<le> card (\<Union> (set (SCC_\<alpha> I i)))"
      apply (rewrite at "\<hole>\<le> card (\<Union> (set (SCC_\<alpha> I i)))" diff_zero[of i, symmetric, unfolded card_atLeastLessThan[symmetric]])
      unfolding set_SCC_\<alpha>_alt
      apply (rule fin_disj_union_card)
      using finite_scc SCC_at_disj non_empty_scc 
      by auto
  
  end
  
  locale oGSS_invar = oGS_invar I + GSS_invar_ext V0 K I i
    for V0 and K and I and i
  
  
  context mdp_graph
  begin
                                                                    
  definition "oGSS_rel = br (\<lambda> (i, I). oGSS_\<alpha> I i) (\<lambda> (i, I). oGSS_invar MG V\<^sub>i I i)"
  abbreviation "SCC_rel' \<equiv> scc_map_defs.SCC_rel (card (E_\<alpha>\<^sup>*``V0)) (card (E_\<alpha>\<^sup>*``V0))"
  
  lemma oGSS_to_SCC_rel:"((i, I), (SCC, D0)) \<in> oGSS_rel \<Longrightarrow> ((i, I), SCC) \<in> SCC_rel'"
    apply(clarsimp simp: oGSS_rel_def in_br_conv oGSS_\<alpha>_def scc_map_defs.SCC_rel_def oGSS_invar_def
      split: option.splits node_state.splits)
    apply(frule GSS_invar_ext.i_bound)
    apply(auto simp: GSS_invar_ext_def GSS_invar_ext_axioms_def 
      split: option.splits node_state.splits)
    done
  
  lemma oGSS_to_oGS: "((i, I), (SCC, D0)) \<in> oGSS_rel \<Longrightarrow> (I, D0) \<in> oGS_rel"
    unfolding oGSS_rel_def
    apply(auto simp: in_br_conv oGS_rel_def oGSS_\<alpha>_def oGSS_invar_def)
    done
  
  lemma oGSS_relI: "GSS_invar_ext MG V\<^sub>i I i \<Longrightarrow> SCC = SCC_\<alpha> I i \<Longrightarrow> (I, D0) \<in> oGS_rel \<Longrightarrow> ((i, I), (SCC, D0)) \<in> oGSS_rel"
    unfolding oGSS_rel_def oGSS_\<alpha>_def oGS_rel_def oGSS_invar_def
    apply(auto simp: in_br_conv)
    done
  
  end
  
  
  locale GSS_defs = GS_defs MG V\<^sub>i SBIP for MG :: "'v mdpG" and V\<^sub>i :: "'v set" and SBIP +
    fixes i :: "nat"
  begin
  
    definition "s_\<alpha> = (SCC_\<alpha> I i, \<alpha>)"
  
    definition "build_scc_impl =
    do {
      ASSERT (i < card (E_\<alpha>\<^sup>*``V0));
      s\<leftarrow>pop_impl i;
      RETURN (i+1, s)
    }"
      
  
  end
  
  locale GSS = GSS_defs MG V\<^sub>i SBIP i + mdp_graph MG V\<^sub>i
    for MG :: "'v mdpG" and V\<^sub>i :: "'v set" and SBIP and i
   
  
  
  locale GSS_invar = GSS MG V\<^sub>i SBIP i + GS_invar MG V\<^sub>i SBIP + GSS_invar_ext MG V\<^sub>i I i for MG :: "'v mdpG" and V\<^sub>i :: "'v set" and SBIP and i 
  
  
  context mdp_graph
  begin
  
    definition "initial_S_impl i0 v0 I0 = do{
      s \<leftarrow> initial_impl v0 I0;
      RETURN (i0,s)
    }"
  
    definition "push_S_impl v \<equiv> (\<lambda> (i,S,B,I,P). do{
      s \<leftarrow> push_impl_fr v (S,B,I,P);
      RETURN (i, s)
    })"
  
  
    definition "GSS_rel \<equiv> { (c,SCC,p,D,pE,vE) . (c,SCC,p,D,pE) \<in> br (\<lambda> (i,SBIP). GSS_defs.s_\<alpha> SBIP i) (\<lambda> (i,SBIP). GSS_invar MG V\<^sub>i SBIP i) }"
  
    definition "GSS_rel_I_eq I \<equiv> { (c,SCC,p,D,pE,vE) . (c,SCC,p,D,pE) \<in> br (\<lambda> (i,SBIP). GSS_defs.s_\<alpha> SBIP i) (\<lambda> (i,SBIP). GSS_invar MG V\<^sub>i SBIP i \<and> GS_defs.I SBIP = I) }"
  
    definition "GSS_rel_I_upd I v j \<equiv> { (c,SCC,p,D,pE,vE) . (c,SCC,p,D,pE) \<in> br (\<lambda> (i,SBIP). GSS_defs.s_\<alpha> SBIP i) (\<lambda> (i,SBIP). GSS_invar MG V\<^sub>i SBIP i \<and> GS_defs.I SBIP = I(v\<mapsto>STACK j)) }"
  
    lemma GSS_rel_I_eqD: "s \<in> GSS_rel_I_eq I \<Longrightarrow> s \<in> GSS_rel"
      unfolding GSS_rel_I_eq_def GSS_rel_def
      by (auto simp: in_br_conv)
  
    lemma GSS_rel_I_updD: "s \<in> GSS_rel_I_upd I v j \<Longrightarrow> s \<in> GSS_rel"
      unfolding GSS_rel_I_upd_def GSS_rel_def
      by (auto simp: in_br_conv)
  
    lemma GSS_rel_I_eqI: "((i,SBIP),s) \<in> GSS_rel \<Longrightarrow> GS_defs.I (SBIP) = I \<Longrightarrow> ((i,SBIP),s) \<in> GSS_rel_I_eq I"
      unfolding GSS_rel_I_eq_def GSS_rel_def
      by (auto simp: in_br_conv)
  
    lemma GSS_rel_I_updI: "((i,SBIP),s) \<in> GSS_rel \<Longrightarrow> GS_defs.I (SBIP) = I(v\<mapsto>STACK j) \<Longrightarrow> ((i,SBIP),s) \<in> GSS_rel_I_upd I v j"
      unfolding GSS_rel_I_upd_def GSS_rel_def
      by (auto simp: in_br_conv)
  
    lemma "I v \<noteq> Some (STACK j) \<Longrightarrow> GSS_rel_I_eq I \<inter> GSS_rel_I_upd I v j = {}"
      unfolding GSS_rel_I_upd_def GSS_rel_I_eq_def GSS_rel_def
      apply(cases "I v")
      by (auto simp: in_br_conv dest!: fun_cong[of I "I(v \<mapsto> STACK j)" v])
  
  
    lemma GSS_rel_GS_eq: "((i,S,B,I,P), (SCC, p, D, pE)) \<in> GSS_rel \<longleftrightarrow> SCC = SCC_\<alpha> I i \<and> GSS_invar_ext MG V\<^sub>i I i \<and> ((S,B,I,P), (p, D, pE)) \<in> GS_rel"
      unfolding GSS_rel_def GSS_defs.s_\<alpha>_def GS_rel_def GSS_invar_def GSS_def GSS_invar_ext_def 
      apply(auto simp: in_br_conv)
      done
  
    
    lemma GSS_relI: "((S,B,I,P), (p, D, pE, vE)) \<in> GS_rel \<Longrightarrow> SCC = SCC_\<alpha> I i \<Longrightarrow> GSS_invar_ext MG V\<^sub>i I i \<Longrightarrow> ((i,S,B,I,P), (SCC, p, D, pE, vE)) \<in> GSS_rel"
      unfolding GSS_rel_def GSS_defs.s_\<alpha>_def GS_rel_def GSS_invar_def GSS_def GSS_invar_ext_def
      apply(auto simp: in_br_conv)
      done
  
    lemma GSS_relI': "(s, pdpe) \<in> GS_rel \<Longrightarrow> SCC = SCC_\<alpha> (GS_defs.I s) i \<Longrightarrow> GSS_invar_ext MG V\<^sub>i (GS_defs.I s) i \<Longrightarrow> pdpe = pdpe' \<Longrightarrow> s = s' \<Longrightarrow> ((i,s'), (SCC, pdpe')) \<in> GSS_rel"
      unfolding GSS_rel_def GSS_defs.s_\<alpha>_def GS_rel_def GSS_invar_def GSS_def GSS_invar_ext_def
      apply(auto simp: in_br_conv)
      done
  
    lemma GSS_relD: "((i,S,B,I,P), (SCC, p, D, pE)) \<in> GSS_rel \<Longrightarrow> SCC = SCC_\<alpha> I i \<and> GSS_invar_ext MG V\<^sub>i I i \<and> ((S,B,I,P), (p, D, pE)) \<in> GS_rel"
      unfolding GSS_rel_def
      apply(auto simp: in_br_conv GSS_defs.s_\<alpha>_def GS_rel_def GSS_invar_def)
      done
      
    lemma GSS_to_GS: "((i,SBIP), (SCC, p, D, pE)) \<in> GSS_rel \<Longrightarrow> (SBIP, (p, D, pE)) \<in> GS_rel"
      unfolding GSS_rel_def GSS_defs.s_\<alpha>_def GS_rel_def GSS_invar_def 
      apply(auto simp: in_br_conv)
      done
  
    lemma oinitial_S_refine: "((0, Map.empty), [], {}) \<in> oGSS_rel"
      apply (auto simp: oGSS_rel_def in_br_conv oGSS_\<alpha>_def SCC_\<alpha>_def oGS_\<alpha>_def)
      apply unfold_locales
      apply (auto simp: SCC_at_def)
      done
  
  
    lemma I_Stack: "initial_impl v I \<le> SPEC (\<lambda> (_,_,I',_). I' = I(v \<mapsto> (STACK 0)))"
      unfolding initial_impl_def 
      unfolding GS_initial_impl_def GS_defs.I_def
      by (auto simp: pw_le_iff refine_pw_simps index_begin_def) 
      
      
    lemma v0_not_done_None:
      assumes REL: "((i,I),(SCC,D0))\<in>oGSS_rel"
      and V0D: "v0 \<notin> D0"
      shows "I v0 = None" 
    proof (rule ccontr)
      assume "I v0 \<noteq> None"
      then obtain a where ALT: "I v0 = Some a" by blast
      show False
      proof (cases a)
        case (STACK x1)
        with REL ALT show ?thesis 
          by(auto simp: oGSS_rel_def in_br_conv oGSS_invar_def oGS_invar_def)
      next
        case (DONE x2)
        with REL ALT V0D show ?thesis 
          by(auto simp: oGSS_rel_def in_br_conv oGSS_\<alpha>_def oGS_\<alpha>_def)
      qed
    qed
    
  
    lemma initial_preserve_scc_at: "I v = None \<Longrightarrow> SCC_at (I(v \<mapsto> (STACK j))) i = SCC_at I i"
      unfolding SCC_at_def
      by auto
  
    lemma initial_preserve_scc: "I v = None \<Longrightarrow> SCC_\<alpha> (I(v \<mapsto> (STACK j))) i = SCC_\<alpha> I i"
      unfolding SCC_\<alpha>_def SCC_at_def
      by auto
  
    lemma push_preserve_I: "I0 v0 = None \<Longrightarrow> push_impl_fr v0 (S0,B0,I0,P0) 
        \<le>\<^sub>n SPEC(\<lambda> (S1,B1,I1,P1). I1 = I0(v0 \<mapsto> STACK (length S0)))"
      unfolding GS_defs.push_impl_def SCC_at_def push_impl_fr_def
      by (auto simp: pw_leof_iff refine_pw_simps Let_def SCC_\<alpha>_def ) 
  
  
    lemma oGS_ndone_maps_None: "\<not>is_done_oimpl v0 I \<Longrightarrow> oGS_invar I \<Longrightarrow> I v0 = None"
      unfolding is_done_oimpl_def oGS_invar_def
      apply(auto split: option.splits node_state.splits)
      done 

  
    lemma initial_S_refine:
      assumes "\<not>is_done_oimpl v0 I"
      and VV0: "v0\<in>V0"
      and VD0: "v0\<notin>D0"
      and OGSS: "((i,I),(SCC,D0))\<in>oGSS_rel"
      and ID: "(v0i,v0)\<in>Id"
      and INV: "cscc_outer_invar it (SCC,D0)"
      shows "initial_S_impl i v0i I \<le> \<Down> GSS_rel (initial_S SCC v0 D0)"
    proof -
  
      interpret oGSS_invar MG V\<^sub>i I i using OGSS
        by(auto simp: oGSS_rel_def in_br_conv)
  
      have OGS: "(I,D0) \<in> oGS_rel"
        using OGSS by(auto intro!: oGSS_to_oGS)
        
      have LE: "initial_impl v0i I \<le> \<Down> {((S',B',I',P'),s). ((S',B',I',P'),s) \<in> GS_rel \<and> I' = I(v0 \<mapsto> STACK 0)} (initial v0 D0)"
        using I_Stack initial_refine[OF VV0 VD0 OGS ID] 
        apply (clarsimp simp: pw_le_iff refine_pw_simps) 
        using ID 
        by fast
  
      have INIT_NSTACK: "oGSS_invar MG V\<^sub>i I i \<Longrightarrow> \<forall>j. I v0 \<noteq> Some (STACK j)"
        unfolding oGSS_invar_def
        by(auto dest!: oGS_invar.I_no_stack[where ?v=v0])
  
  
      note V0NONE = v0_not_done_None[OF OGSS VD0]
  
      have N0: "0 < card (E_\<alpha>\<^sup>* `` V0)" 
        using VV0 card_gt_0_iff by fastforce
  
  
      show ?thesis
        unfolding initial_S_impl_def initial_S_def
        apply(refine_vcg LE)
        using OGSS
        apply(auto intro!: GSS_relI GSS_rel_I_updI
          simp: oGSS_rel_def oGSS_\<alpha>_def in_br_conv initial_preserve_scc[of I v0, OF V0NONE] GS_rel_def)
  
        apply(unfold_locales)
        unfolding initial_preserve_scc_at[of I v0, OF V0NONE]
  
        subgoal using non_empty_scc by assumption
        subgoal using empty_not_scc by assumption
        subgoal using finite_scc by assumption
        subgoal using I_reachable VV0 by auto
        subgoal using i_bound by auto
        subgoal using I_bound N0 by auto
        done
    qed
  
  
    definition "last_seg_impl s \<equiv> GS.last_seg_impl s"
    lemmas last_seg_impl_def_opt = 
      last_seg_impl_def[abs_def, THEN opt_GSdef, 
        unfolded GS.last_seg_impl_def GS.seg_set_impl_def 
      GS_defs.seg_start_def GS_defs.seg_end_def GS_sel_simps] 
      (* TODO: Some potential for optimization here: the assertion 
        guarantees that length B - 1 + 1 = length B !*)
  
    lemma last_seg_impl_refine: 
      assumes A: "(s,(p,D,pE,vE))\<in>GS_rel"
      assumes NE: "p\<noteq>[]"
      shows "last_seg_impl s \<le> \<Down>Id (RETURN (last p))"
    proof -
      from A have 
        [simp]: "p=GS_defs.p_\<alpha> s \<and> D=GS_defs.D_\<alpha> s \<and> pE=GS_defs.pE_\<alpha> s" 
          and INV: "GS_invar MG V\<^sub>i s"
        by (auto simp add: GS_rel_def br_def GS_\<alpha>_split)
  
      show ?thesis
        unfolding last_seg_impl_def[abs_def]
        apply (rule order_trans[OF GS_invar.last_seg_impl_correct])
        using INV NE
        apply (simp_all) 
        done
    qed
  
  
    lemma push_S_refine:
      assumes A: "((i,s),(SCC,p,D,pE,vE))\<in>GSS_rel" 
      assumes B: "(v,v')\<in>Id"
      assumes C: "v\<notin>\<Union>(set p)" "v\<notin>D"
      assumes NSTACK: "\<not>is_on_stack_impl v s"
      assumes NDONE: "\<not>is_done_impl v s"
      assumes REACH: "v \<in> E_\<alpha>\<^sup>* `` V0"
      shows "push_S_impl v (i,s) \<le> \<Down>GSS_rel (push_S v' (SCC,p,D,pE,vE))"
    proof -
      from A B have XF[simp]: "p=GS_defs.p_\<alpha> s" "D=GS_defs.D_\<alpha> s" "pE=GS_defs.pE_\<alpha> s" "v'=v" and SCCD: "SCC = SCC_\<alpha> (GS_defs.I s) i"
        and INV: "GSS_invar MG V\<^sub>i s i"
        by (auto simp add: GSS_rel_def GSS_defs.s_\<alpha>_def GS_rel_def br_def GS_\<alpha>_split)
  
      have IVNONE: "(GS_defs.I s) v = None" using NDONE NSTACK 
        unfolding is_done_impl_def is_on_stack_impl_def GS_defs.is_done_impl_def GS_defs.is_on_stack_impl_def
        apply (auto split: option.splits node_state.splits)
        done
  
      interpret GSS_invar MG V\<^sub>i s i by fact
  
      note GS = GSS_to_GS[OF A]
  
      note CC1 = push_impl_core_correct[OF C[unfolded XF] REACH]
  
      have CC2: "push_impl v \<le>\<^sub>n
        Refine_Basic.SPEC (\<lambda>(S1, B1, I1, P1). I1 = I(v \<mapsto> STACK (length S)))"
        using push_preserve_I[of I v S B P, OF IVNONE]
        unfolding push_impl_fr_def
        apply(fold GS_sel_id) .
  
      note CC = SPEC_rule_conj_leofI2[OF CC2 CC1]
  
      note IP = initial_preserve_scc_at[of I v, OF IVNONE]
  
      have VNS: "v\<notin>set S" 
        using XF(1) assms(3) set_p_\<alpha>_is_set_S by blast
      hence LS: "length S < card (E_\<alpha>\<^sup>* `` V0)"
        by (metis REACH S_distinct S_length_nodes S_subset_nodes card_subset_eq distinct_card finite_reachableE_V0 le_neq_implies_less)
      hence LB: "length B < card (E_\<alpha>\<^sup>* `` V0)"
        by (metis B_distinct B_in_bound' B_length_nodes B_sorted order_le_imp_less_or_eq order_le_less_trans order_less_imp_not_eq2 sorted_wrt_less_idx strict_sorted_iff)
  
      have LP: "length P < card (E_\<alpha>\<^sup>* `` V0)"
      proof -
        have "v\<notin>set (map fst (GS_defs.P s))" 
          using P_bound VNS by auto
        hence "set (map fst (GS_defs.P s)) \<subseteq> E_\<alpha>\<^sup>* `` V0 - {v}" using P_bound S_subset_nodes by force
        hence "card (set (map fst (GS_defs.P s))) \<le> card (E_\<alpha>\<^sup>* `` V0 - {v})"
          by (auto intro: card_mono)
        moreover have "card (set (map fst (GS_defs.P s))) = length (GS_defs.P s)"
          by (metis P_distinct distinct_card length_map)
        moreover have "card (E_\<alpha>\<^sup>* `` V0 - {v}) = card (E_\<alpha>\<^sup>* `` V0) - 1"
          by (simp add: REACH)
        moreover have "card (E_\<alpha>\<^sup>* `` V0) \<noteq> 0"
          using REACH by auto
        ultimately show ?thesis by linarith
      qed
  
      have LE: "push_impl_fr v s \<le> \<Down> {((S',B',I',P'),s). ((S',B',I',P'),s) \<in> GS_rel \<and> I' = I(v \<mapsto> STACK (length S))} (push v (p_\<alpha>,D_\<alpha>,pE_\<alpha>,vE))"
        unfolding push_impl_fr_def
        apply(rule order_trans[OF CC])
        using LS LB LP 
        by (auto simp: E_\<alpha>_mem push_def out_edges_def pw_le_iff refine_pw_simps GS_rel_def in_br_conv SCCD)
  
      have INV: "((S', B', I', P'), p', D', pE', vE') \<in> GS_rel \<Longrightarrow>
        I' = I(v \<mapsto> STACK (length S)) \<Longrightarrow> GSS_invar_ext_axioms MG I' i" for S' B' I' P' p' D' pE' vE'
        apply clarsimp
        apply(unfold_locales)
        subgoal using non_empty_scc IP by presburger
        subgoal using empty_not_scc IP by presburger
        subgoal using finite_scc IP by presburger
        subgoal using I_reachable REACH by auto
        subgoal using i_bound by auto
        subgoal using I_bound LS by auto
        done
  
  
      show ?thesis
        unfolding push_S_impl_def push_S_def
        apply simp
        apply (refine_vcg LE) 
        apply(rule GSS_relI')
        by (auto simp: SCCD GSS_invar_ext_def mdp_graph_axioms INV SCC_\<alpha>_def IP)
    qed
  
  
    lemma (in GSS_invar) collapse_S_correct: (*TODO: Fix stacked auto proofs*)
      assumes A: "v\<in>\<Union>(set (p_\<alpha>))"
      shows "do{x \<leftarrow> collapse_impl v; RETURN (i,x)} \<le> \<Down>GSS_rel (RETURN (SCC_\<alpha> I i, collapse v (p_\<alpha>, D_\<alpha>, pE_\<alpha>, vE)))"
    proof -
      {
  
        fix i
        assume "i<length p_\<alpha>"
        hence ILEN: "i<length B" by (simp add: p_\<alpha>_def)
  
        let ?SBIP' = "(S, take (Suc i) B, I, P)"
  
        {
          have [simp]: "GS_defs.seg_start ?SBIP' i = seg_start i"
            by (simp add: GS_defs.seg_start_def)
  
          have [simp]: "GS_defs.seg_end ?SBIP' i = seg_end (length B - 1)"
            using ILEN by (simp add: GS_defs.seg_end_def min_absorb2)
  
          {
            fix j
            assume B: "seg_start i \<le> j" "j < seg_end (length B - Suc 0)"
            hence "j<length S" using ILEN seg_end_bound 
            proof -
              note B(2)
              also from \<open>i<length B\<close> have "(length B - Suc 0) < length B" by auto
              from seg_end_bound[OF this] 
              have "seg_end (length B - Suc 0) \<le> length S" .
              finally show ?thesis .
            qed
  
            have "i \<le> find_seg j \<and> find_seg j < length B 
              \<and> seg_start (find_seg j) \<le> j \<and> j < seg_end (find_seg j)" 
            proof (intro conjI)
              show "i\<le>find_seg j"
                by (metis le_trans not_less B(1) find_seg_bounds(2) 
                  seg_end_less_start ILEN \<open>j < length S\<close>)
            qed (simp_all add: find_seg_bounds[OF \<open>j<length S\<close>])
          } note AUX1 = this
  
          {
            fix Q and j::nat
            assume "Q j"
            hence "\<exists>i. S!j = S!i \<and> Q i"
              by blast
          } note AUX_ex_conj_SeqSI = this
  
          have "GS_defs.seg ?SBIP' i = \<Union> (seg ` {i..<length B})"
            unfolding GS_defs.seg_def[abs_def]
            apply simp
            apply (rule)
            apply (auto dest!: AUX1) []
  
            apply (auto 
              simp: seg_start_def seg_end_def 
              split: if_split_asm
              intro!: AUX_ex_conj_SeqSI
            )
  
           apply (metis diff_diff_cancel le_diff_conv le_eq_less_or_eq 
             lessI trans_le_add1 
             distinct_sorted_mono[OF B_sorted B_distinct, of i])
  
           apply (metis diff_diff_cancel le_diff_conv le_eq_less_or_eq 
             trans_le_add1 distinct_sorted_mono[OF B_sorted B_distinct, of i])
           
           apply (metis (opaque_lifting, no_types) Suc_lessD Suc_lessI less_trans_Suc
             B_in_bound')
           done
        } note AUX2 = this
        
        from ILEN have "GS_defs.p_\<alpha> (S, take (Suc i) B, I, P) = collapse_aux p_\<alpha> i"
          unfolding GS_defs.p_\<alpha>_def collapse_aux_def
          apply (simp add: min_absorb2 drop_map)
          apply (rule conjI)
          apply (auto 
            simp: GS_defs.seg_def[abs_def] GS_defs.seg_start_def GS_defs.seg_end_def take_map) []
  
          apply (simp add: AUX2)
          done
      } note AUX1 = this
  
      from A obtain j where [simp]: "I v = Some (STACK j)"
        using I_consistent set_p_\<alpha>_is_set_S
        by (auto simp: in_set_conv_nth)
  
      {
        have "(SCC_\<alpha> I i, collapse_aux p_\<alpha> (idx_of p_\<alpha> v), D_\<alpha>, pE_\<alpha>) =
          GSS_defs.s_\<alpha> (S, take (Suc (idx_of p_\<alpha> v)) B, I, P) i"
        apply(auto simp: GSS_defs.s_\<alpha>_def)
        unfolding GS_defs.\<alpha>_def
        using idx_of_props[OF p_\<alpha>_disjoint_sym A]
        by (simp add: AUX1)
      } note ABS=this
  
      {
        have "GSS_invar MG V\<^sub>i (S, take (Suc (idx_of p_\<alpha> v)) B, I, P) i"
          apply unfold_locales
          apply simp_all
  
          using B_in_bound B_sorted B_distinct
          apply (auto simp: sorted_wrt_take dest: in_set_takeD) [3]
  
          using B0 S_distinct apply auto [2]
  
          using I_consistent apply simp
  
          using P_sorted P_distinct P_bound apply auto[3]
  
          using S_subset_nodes apply auto[]
  
          using non_empty_scc empty_not_scc finite_scc I_reachable apply auto[4]
  
          using i_bound I_bound apply auto[2]
  
          done
      } note INV=this
  
      show ?thesis
        unfolding collapse_impl_fr_def collapse_impl_def 
        apply (refine_rcg SPEC_refine refine_vcg order_trans[OF idx_of_correct])
        apply fact
        apply force
  
        apply (simp add: collapse_def \<alpha>_def GSS_rel_def GS_rel_def in_br_conv)
        unfolding GSS_rel_def GS_rel_def
        apply (rule conjI)
          apply (rule ABS)
          apply (rule INV)
        done
    qed
  
    lemma collapse_S_refine:
      assumes A: "((i,s),(SCC,p,D,pE,vE))\<in>GSS_rel" "(v,v')\<in>Id"
      assumes B: "v'\<in>\<Union>(set p)"
      assumes STACK: "is_on_stack_impl v s"
      shows "do{x \<leftarrow> collapse_impl_fr v s; RETURN (i,x)} \<le> \<Down>GSS_rel (RETURN (SCC, collapse v' (p,D,pE,vE)))"
    proof -
      from A have [simp]: "p=GS_defs.p_\<alpha> s \<and> D=GS_defs.D_\<alpha> s \<and> pE=GS_defs.pE_\<alpha> s" "v'=v" "SCC = SCC_\<alpha> (GS_defs.I s) i"
        and INV: "GSS_invar MG V\<^sub>i s i"
        by (auto simp add: GSS_rel_def GS_rel_def br_def GS_\<alpha>_split GSS_defs.s_\<alpha>_def)
      show ?thesis 
        unfolding collapse_impl_fr_def
        apply (rule order_trans[OF GSS_invar.collapse_S_correct])
        using INV B 
        by (auto simp add: GS_defs.\<alpha>_def GSS_rel_def in_br_conv)
    qed
  
    
  
    lemma (in GSS_invar) SCC_at_mark_as_done_eq:
      assumes "p_\<alpha> \<noteq> []"
      shows "SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) i = last p_\<alpha>"
      unfolding mark_as_done_abs_def SCC_at_extend[of "(\<lambda> v. v \<in> {S ! j |j. seg_start (length B - 1) \<le> j \<and> j < seg_end (length B - 1)})"]
      unfolding seg_start_def seg_end_def 
      using empty_not_scc[of i, simplified] last_p_\<alpha>_alt_def[OF assms] assms[unfolded p_\<alpha>_B_empty]
      unfolding last_conv_nth[of B, unfolded p_\<alpha>_B_empty[symmetric], OF assms]
      by force
  
  
    lemma (in GSS_invar) SCC_\<alpha>_mark_as_done:
      assumes "p_\<alpha> \<noteq> []"
      shows "SCC_\<alpha> (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) (Suc i) = (SCC_\<alpha> I i) @ [last p_\<alpha>]"
    proof -
  
      {
        fix v j
        assume "I v = Some (DONE j)"
        hence "\<forall>i. \<not>(i < length S \<and> v = S ! i)"
          using I_consistent 
          by (metis node_state.distinct(1) option.inject)
        hence AUX1: "\<forall> i < length S. S!i \<noteq> v"
          by blast
      } note AUX1=this
  
      have AUX2: "map (SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i)) [0..<i] = map (SCC_at I) [0..<i]"
        apply(rule list.map_cong0)
        unfolding mark_as_done_abs_def
        apply (rule SCC_at_extend_neq[of _ _ "(\<lambda> v. v \<in> {S ! j |j. seg_start (length B - 1) \<le> j \<and> j < seg_end (length B - 1)})"])
        using AUX1 seg_end_last[OF assms[unfolded p_\<alpha>_B_empty]]
        by auto
  
      have "map (SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i))  [0..<Suc i] 
        = map (SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i)) [0..<i] @ [(SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) i)]"
        by simp
      also have "...= map(SCC_at I) [0..<i] @ [last p_\<alpha>]"
        unfolding SCC_at_mark_as_done_eq[OF assms] AUX2
        by blast
      finally show ?thesis
        unfolding SCC_\<alpha>_def
        by blast
    qed
  
  
    lemma (in GSS_invar) GSS_invar_mark_as_done:
      assumes NE: "p_\<alpha>\<noteq>[]"
      assumes I_UPPER_BOUND: "i < card (E_\<alpha>\<^sup>* `` V0)"
      shows "GSS_invar_ext MG V\<^sub>i (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) (Suc i)"
    proof -
  
      from NE have BNE: "B \<noteq> []" unfolding p_\<alpha>_def by simp
  
      {
        fix j
        assume A: "j < i"
        have "SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) j \<noteq> {}"
          unfolding SCC_at_def mark_as_done_abs_def
          using non_empty_scc[OF A, unfolded SCC_at_def] seg_start_less_end[of "length B - 1", simplified, OF BNE]
          apply (auto simp:)
          subgoal for x
            apply (rule exI[where x=x])
            apply (auto simp: A)
            by (metis BNE I_consistent One_nat_def node_state.distinct(1) option.inject seg_end_last)
          done
      } note AUX1 = this
  
      {
        have "SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) i \<noteq> {}" 
          unfolding SCC_at_def mark_as_done_abs_def seg_start_def seg_end_def
          using empty_not_scc[unfolded SCC_at_def, of i, simplified]
          by (auto simp: BNE B_in_bound')
      } note AUX2 = this
  
      {
        fix j
        assume A: "j \<ge> Suc i"
        then have "SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) j = {}" 
          unfolding SCC_at_def mark_as_done_abs_def
          using empty_not_scc[OF Suc_leD[OF A], unfolded SCC_at_def] 
          by auto
      } note AUX3 = this
  
      {
        fix j
        assume A: "j < i"
        have "I v = Some (DONE j) \<Longrightarrow> v \<notin> {S ! j |j. seg_start (length B - 1) \<le> j \<and> j < seg_end (length B - 1)}" for v 
          using I_consistent 
          apply auto 
          by (metis BNE One_nat_def node_state.distinct(1) option.inject seg_end_last)
        hence "SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) j = SCC_at I j" 
          using SCC_at_extend_neq[of I j "\<lambda> v. v \<in> {S ! j |j. seg_start (length B - 1) \<le> j \<and> j < seg_end (length B - 1)}" i] A
          unfolding mark_as_done_abs_def
          by blast
        hence "finite (SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) j)" 
        using finite_scc
        by presburger
      } note AUX4 = this
  
      {
        fix j
        assume A: "j > i"
        hence "I v \<noteq> Some (DONE j)" for v using empty_not_scc[of j] unfolding SCC_at_def by simp
        hence "SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) j = SCC_at I j" 
          using SCC_at_extend_neq[of I j "\<lambda> v. v \<in> {S ! j |j. seg_start (length B - 1) \<le> j \<and> j < seg_end (length B - 1)}" i] A 
          unfolding mark_as_done_abs_def 
          by blast
        hence "finite (SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) j)" 
        using finite_scc
        by presburger
      } note AUX5 = this
  
      {
        have "finite (SCC_at I i)" using empty_not_scc[of i, simplified] 
          by auto
        moreover have "finite {v. v \<in> {S ! j |j. seg_start (length B - 1) \<le> j \<and> j < seg_end (length B - 1)}}" 
          by fastforce
        ultimately have "finite (SCC_at (mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i) i)"
          unfolding mark_as_done_abs_def SCC_at_extend[of "\<lambda> v. v \<in> {S ! j |j. seg_start (length B - 1) \<le> j \<and> j < seg_end (length B - 1)}" i I]
          by blast
      } note AUX6 = this
  
      have BNE: "B \<noteq> []" using NE unfolding p_\<alpha>_def by force
  
      
      show ?thesis
        apply (unfold_locales)
        apply (simp add: mdp_graph_def mdp_graph_axioms)
        apply (metis One_nat_def less_SucE AUX1 AUX2)
        using AUX3 apply blast
        apply (metis AUX4 AUX5 AUX6 linorder_neqE_nat)
        unfolding mark_as_done_abs_def
        using S_subset_nodes I_reachable
        apply (auto split: if_splits simp: seg_end_last[OF BNE, simplified])[]
        subgoal using I_UPPER_BOUND by simp
        subgoal using I_bound by (force split: option.splits node_state.splits) 
        done
         
    qed
  
    lemma (in GSS_invar) pop_S_correct:
      assumes NE: "p_\<alpha>\<noteq>[]" and NS: "(set_mset pE_\<alpha>) \<inter> last p_\<alpha> \<times> UNIV = {}"
      shows "pop_impl i
        \<le> SPEC (\<lambda>s. (s, (butlast p_\<alpha>, D_\<alpha> \<union> last p_\<alpha>, pE_\<alpha>, vE)) \<in> GS_rel 
        \<and> (GS_defs.I s = mark_as_done_abs (seg_start (length B - 1)) (seg_end (length B - 1)) I i))"
    proof -
  
      from NE have BNE: "B \<noteq> []" by (auto simp: p_\<alpha>_def)
  
      show ?thesis
        apply (rule SPEC_rule_conjI)
        using pop_correct[OF NE NS] 
        apply (auto simp: pw_le_iff refine_pw_simps)[]
        unfolding pop_impl_def
        apply(refine_vcg order_trans[OF mark_as_done_aux])
        apply (auto simp: BNE intro!: seg_start_less_end seg_end_bound)
        using B_in_bound 
        by (metis BNE B_in_bound' Misc.last_in_set in_set_conv_nth order.strict_implies_order)
    qed
  
    lemma (in GS_invar) t1:
      "D_\<alpha> \<inter> \<Union> (set p_\<alpha>) = {}"
      unfolding D_\<alpha>_def p_\<alpha>_def seg_def
      using I_consistent seg_end_bound apply auto 
      by (metis dual_order.strict_trans1 node_state.distinct(1) option.inject)
        
    lemma (in GS_invar) t2:
      "\<Union> (set p_\<alpha>) \<subseteq> E_\<alpha>\<^sup>*``V0"
      by (simp add: S_subset_nodes set_p_\<alpha>_is_set_S)
  
    lemma (in GS_invar) t3:
      "p_\<alpha> \<noteq> [] \<Longrightarrow> \<Union> (set p_\<alpha>) \<noteq> {}"
      by (simp add: empty_eq p_\<alpha>_B_empty set_p_\<alpha>_is_set_S)
      
  
    lemma (in GS_invar) t4:
      assumes B: "p_\<alpha> \<noteq> []" and INV: "outer_invar_loc MG V\<^sub>i it D_\<alpha>"
        shows "D_\<alpha> \<subset> E_\<alpha>\<^sup>*``V0"
        using outer_invar_loc.D_reachable[OF INV] t1 t2 t3[OF B]
        by fast
  
  
    lemma (in GSS_invar) build_scc_impl_correct:
      assumes B: "p_\<alpha> \<noteq> []" "(set_mset pE_\<alpha>) \<inter> last (p_\<alpha>) \<times> UNIV = {}"
        shows "build_scc_impl \<le> \<Down>GSS_rel (RETURN (build_scc (SCC_\<alpha> I i, p_\<alpha>, D_\<alpha>, pE_\<alpha>, vE)))"
      proof-
  
        {
          have "D_\<alpha> \<inter> \<Union> (set p_\<alpha>) = {}"    
            unfolding D_\<alpha>_def p_\<alpha>_def seg_def
            using I_consistent seg_end_bound apply auto 
            by (metis dual_order.strict_trans1 node_state.distinct(1) option.inject)
          moreover have "\<Union> (set p_\<alpha>) \<subseteq> E_\<alpha>\<^sup>*``V0"
            by (simp add: S_subset_nodes set_p_\<alpha>_is_set_S)
          moreover have "\<Union> (set p_\<alpha>) \<noteq> {}"
            using B by (simp add: empty_eq p_\<alpha>_B_empty set_p_\<alpha>_is_set_S)
          moreover have "D_\<alpha> \<subseteq> E_\<alpha>\<^sup>*``V0"
            using I_reachable unfolding D_\<alpha>_def by blast
          ultimately have "D_\<alpha> \<subset> E_\<alpha>\<^sup>*``V0"
            using D_\<alpha>_alt_def 
            by fast
          hence A: "\<Union> (set (SCC_\<alpha> I i)) \<subset> E_\<alpha>\<^sup>*``V0" unfolding oGS_\<alpha>_alt_def D_\<alpha>_alt_def .
  
  
          have "i < card (E_\<alpha>\<^sup>* `` V0)" using psubset_card_mono[OF finite_reachableE_V0 A] i_bound_SCC
            by linarith
        } note AUX1 = this
  
  
        show ?thesis unfolding build_scc_impl_def build_scc_def pop_impl_fr_def
          apply (refine_rcg refine_vcg order_trans[OF GSS_invar.pop_S_correct])
          using B GSS_invar_axioms apply clarsimp_all 
          using AUX1 apply argo
          apply (auto simp: GS_rel_def br_def conc_fun_def pop_def 
            SCC_\<alpha>_mark_as_done[simplified] s_\<alpha>_def GS_defs.\<alpha>_def 
            GSS_invar_mark_as_done[simplified] intro!: GSS_relI)
          done
      qed
  
  
  
    lemma select_edge_refine_aux: 
      assumes A: "(s,(p,D,pE,vE))\<in>GS_rel"
      assumes NE: "p \<noteq> []"
      shows "select_edge_impl s \<le> 
        SPEC (\<lambda> (i,S,B,I,P). I = GS_defs.I s)"
    proof - 
      from A have "GS_invar MG V\<^sub>i s" 
        by(auto simp: GS_rel_def in_br_conv)
  
      interpret GS_invar MG V\<^sub>i s by fact
  
      {
        fix x1 x2
        assume "GS_defs.P s \<noteq> []" and "last P = (x1, x2)"
        hence "x1 \<in> set S" 
          using P_bound
          by fastforce
        hence "\<exists> j. (j < length S \<and> x1 = S ! j)"
          by (metis in_set_conv_nth)
        hence "\<exists> j. I x1 = Some (STACK j)"
          using I_consistent
          by blast
      } note AUX1 = this
  
      {
        assume "P \<noteq> []"
        hence "S \<noteq> []" 
          using P_bound 
          by force
        hence "B \<noteq> []"
          using B0
          by blast
      } note AUX2 = this
  
      show ?thesis
        unfolding select_edge_impl_def GS_defs.sel_rem_last_def
        apply(refine_vcg)
        apply auto
        using AUX1 AUX2 P_bound 
        by auto
    qed
  
  
    lemma select_edge_S_refine_aux: 
      assumes A: "(s,(p,D,pE,vE))\<in>GS_rel"
      assumes NE: "p \<noteq> []"
      shows "select_edge_impl s \<le> 
        SPEC (\<lambda> r. RETURN r \<le> \<Down>(Id \<times>\<^sub>r GS_rel) (select_edge (p,D,pE,vE)) \<and> (case r of (i,S,B,I,P) \<Rightarrow> I = GS_defs.I s))"
  
      apply (rule SPEC_rule_conjI)
      apply (rule order_trans[OF select_edge_refine])
      using A NE apply auto[2]
      apply (auto simp: pw_le_iff refine_pw_simps select_edge_def split: option.splits)[]
      using select_edge_refine_aux[OF A NE] by blast
      
    definition "select_edge_S_impl \<equiv> \<lambda>(i,s). do { (r,s')\<leftarrow>select_edge_impl s; RETURN (r,(i,s')) }"
  
    lemma (in GS_defs) sel_rem_last_pres_I: "sel_rem_last \<le>\<^sub>n SPEC (\<lambda>(_,(_,_,I',_)). I'=I)"
      unfolding sel_rem_last_def
      apply refine_vcg
      by auto
  
    lemma select_edge_impl_presI: "select_edge_impl (S,B,I,P) \<le>\<^sub>n SPEC (\<lambda>(_,(_,_,I',_)). I'=I)"
      unfolding select_edge_impl_def
      using GS_defs.sel_rem_last_pres_I[of MG V\<^sub>i "(S,B,I,P)"] 
      by simp
  
    lemma select_edge_S_refine: 
      assumes A: "(s,(SCC,p,D,pE,vE))\<in>GSS_rel"
      assumes NE: "p \<noteq> []"
      shows "select_edge_S_impl s \<le> \<Down>(Id \<times>\<^sub>r GSS_rel) (select_edge_S (SCC,p,D,pE,vE))"
      using assms 
      unfolding select_edge_S_impl_def select_edge_S_def 
      using select_edge_impl_presI select_edge_refine
      by (clarsimp simp: pw_le_iff pw_leof_iff refine_pw_simps GSS_rel_GS_eq split: prod.splits; blast) 
  
  
    lemma i_I_to_outer:
      assumes "((i, (S, B, I, P)), (SCC, ([], D, {#}, vE))) \<in> GSS_rel"
      shows "((i,I),(SCC,D))\<in>oGSS_rel"
      using assms
      unfolding GSS_rel_def GS_rel_def GSS_defs.s_\<alpha>_def oGSS_rel_def oGS_rel_def br_def oGS_\<alpha>_def GS_defs.\<alpha>_def GS_defs.D_\<alpha>_def GSS_invar_def GS_invar_def GS_invar_axioms_def oGSS_invar_def  oGS_invar_def oGSS_\<alpha>_def
      apply (auto simp: GS_defs.p_\<alpha>_def GS_defs.pE_\<alpha>_def SCC_\<alpha>_def SCC_at_def mdp_graph_axioms)
      done
  
  
    interpretation GSSX: GSS MG V\<^sub>i SBIP i for i SBIP by unfold_locales
  
    definition "build_scc_impl_fr s i = GSSX.build_scc_impl s i"
    sepref_register build_scc_impl_fr
  
    lemma build_scc_impl_refine: 
      assumes REL: "((i,s), (SCC,p,D,pE,vE)) \<in> GSS_rel"
          and B: "p \<noteq> []" "(set_mset pE) \<inter> last p \<times> UNIV = {}"
        shows "build_scc_impl_fr s i \<le> \<Down>GSS_rel (RETURN (build_scc (SCC,p,D,pE,vE)))"
    proof -
      from REL have [simp]: "p=GS_defs.p_\<alpha> s \<and> D=GS_defs.D_\<alpha> s \<and> pE=GS_defs.pE_\<alpha> s" "SCC = SCC_\<alpha> (GS_defs.I s) i"
        and INV: "GSS_invar MG V\<^sub>i s i"
        by (auto simp add: GSS_rel_def GS_rel_def br_def GS_\<alpha>_split GSS_defs.s_\<alpha>_def)
      show ?thesis
        unfolding build_scc_impl_fr_def
        apply auto
        apply (rule order_trans[OF GSS_invar.build_scc_impl_correct])
        using INV B
        by (auto simp: GSS_defs.s_\<alpha>_def GS_defs.\<alpha>_def GSS_rel_def in_br_conv)
    qed
  
    definition "compute_SCC_inner_while_body = (\<lambda> (i, s).
            do {
              \<comment> \<open>Select edge from end of path\<close>
              (vo,(i,s)) \<leftarrow> select_edge_S_impl (i,s);
  
              case vo of 
                Some v \<Rightarrow> do {
                  ASSERT (v \<in> E_\<alpha>\<^sup>*``V0);
                  if is_on_stack_impl v s then do {
                    s \<leftarrow> collapse_impl_fr v s;
                    RETURN (i, s)
                  } else if \<not>is_done_impl v s then do {
                    \<comment> \<open>Edge to new node. Append to path\<close>
                    push_S_impl v (i, s)
                  } else do {
                    \<comment> \<open>Edge to done node. Skip\<close>
                    RETURN (i, s)
                  }
                }
              | None \<Rightarrow> do {
                  \<comment> \<open>No more outgoing edges from current node on path\<close>
                  build_scc_impl_fr s i
                }
            })"
  
    definition "compute_SCC_impl \<equiv> do {
        let so = (0,Map.empty);
        (i,D) \<leftarrow> FOREACHi (\<lambda>it (i0,I0). cscc_outer_invar it (oGSS_\<alpha> I0 i0)) V\<^sub>i (\<lambda>v0 (i0, I0). do {
          ASSERT (v0 \<in> E_\<alpha>\<^sup>*``V\<^sub>i); 
          if (is_admissible MG v0 \<and> \<not>is_done_oimpl v0 I0) then do {
            ASSERT (v0 \<in> E_\<alpha>\<^sup>*``V0);
            s \<leftarrow> initial_S_impl i0 v0 I0;
  
            (i,(S,B,I,P))\<leftarrow> WHILEIT (\<lambda> (i,s). (\<lambda> (SCC,p,D,pE). \<exists>vE. cscc_invar v0 (oGS_\<alpha> I0) (SCC,p,D,pE,vE)) (GSS_defs.s_\<alpha> s i))
              (\<lambda> (_, s). \<not>path_is_empty_impl s) 
              compute_SCC_inner_while_body
              s;
            RETURN (i, I)
          } else
            RETURN (i0, I0)
          }) so;
        RETURN (i, D)
      }"
  
  
  
    lemma compute_SCC_impl_refine: "compute_SCC_impl \<le> \<Down>SCC_rel' compute_SCC"
    proof -
      note [[goals_limit = 3]]
      show ?thesis
        unfolding compute_SCC_impl_def compute_SCC_def compute_SCC_inner_while_body_def
  
        apply (refine_rcg
          bind_refine'
          select_edge_S_refine
          initial_S_refine
          oinitial_S_refine
          build_scc_impl_refine
          push_S_refine
          collapse_S_refine
          IdI
          inj_on_id
        )
        apply refine_dref_type
  
        apply (vc_solve (nopre) solve: asm_rl i_I_to_outer
          simp: GS_rel_def br_def GS_defs.\<alpha>_def oGS_rel_def oGS_\<alpha>_def 
          oGSS_\<alpha>_def oGSS_rel_def in_br_conv oGSS_invar_def GSS_defs.s_\<alpha>_def
          is_on_stack_refine path_is_empty_refine is_done_refine is_done_orefine is_admissible_refine
          intro: oGSS_to_SCC_rel
          dest!: GSS_relD 
        )
        done
    qed
    
  end

end
