section \<open>Skeleton for Gabow's SCC Algorithm \label{sec:skel}\<close>
theory Gabow_Skeleton
imports "../ds/SCC_map"
begin
  
  text \<open>
    In this theory, we formalize a skeleton of Gabow's SCC algorithm. 
    The skeleton serves as a starting point to develop concrete algorithms,
    like enumerating the SCCs or checking emptiness of a generalized Büchi automaton.
  \<close>
  
  section \<open>Abstract Algorithm\<close>
  text \<open>
    In this section, we formalize an abstract version of a path-based SCC algorithm.
    Later, this algorithm will be refined to use Gabow's data structure.
  \<close>
  
  subsection \<open>Preliminaries\<close>
  definition path_seg :: "'a set list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a set"
    \<comment> \<open>Set of nodes in a segment of the path\<close>
    where "path_seg p i j \<equiv> \<Union>{p!k|k. i\<le>k \<and> k<j}"
  
  lemma path_seg_simps[simp]: 
    "j\<le>i \<Longrightarrow> path_seg p i j = {}"
    "path_seg p i (Suc i) = p!i"
    unfolding path_seg_def
    apply auto []
    apply (auto simp: le_less_Suc_eq) []
    done
  
  lemma path_seg_drop:
    "\<Union>(set (drop i p)) = path_seg p i (length p)"
    unfolding path_seg_def
    by (fastforce simp: in_set_drop_conv_nth Bex_def)
  
  lemma path_seg_butlast: 
    "p\<noteq>[] \<Longrightarrow> path_seg p 0 (length p - Suc 0) = \<Union>(set (butlast p))"
    apply (cases p rule: rev_cases, simp)
    apply (fastforce simp: path_seg_def nth_append in_set_conv_nth)
    done
  
  definition idx_of :: "'a set list \<Rightarrow> 'a \<Rightarrow> nat"
    \<comment> \<open>Index of path segment that contains a node\<close>
    where "idx_of p v \<equiv> THE i. i<length p \<and> v\<in>p!i"
  
  lemma idx_of_props:
    assumes 
      p_disjoint_sym: "\<forall>i j v. i<length p \<and> j<length p \<and> v\<in>p!i \<and> v\<in>p!j \<longrightarrow> i=j"
    assumes ON_STACK: "v\<in>\<Union>(set p)"
    shows 
      "idx_of p v < length p" and
      "v \<in> p ! idx_of p v"
  proof -
    from ON_STACK obtain i where "i<length p" "v \<in> p ! i"
      by (auto simp add: in_set_conv_nth)
    moreover hence "\<forall>j<length p. v\<in>p ! j \<longrightarrow> i=j"
      using p_disjoint_sym by auto
    ultimately show "idx_of p v < length p" 
      and "v \<in> p ! idx_of p v" unfolding idx_of_def
      by (metis (lifting) theI')+
  qed
  
  lemma idx_of_uniq:
    assumes 
      p_disjoint_sym: "\<forall>i j v. i<length p \<and> j<length p \<and> v\<in>p!i \<and> v\<in>p!j \<longrightarrow> i=j"
    assumes A: "i<length p" "v\<in>p!i"
    shows "idx_of p v = i"
  proof -
    from A p_disjoint_sym have "\<forall>j<length p. v\<in>p ! j \<longrightarrow> i=j" by auto
    with A show ?thesis
      unfolding idx_of_def
      by (metis (lifting) the_equality)
  qed
  
  
  subsection \<open>Invariants\<close>
  text \<open>The state of the inner loop consists of the path \<open>p\<close> of
    collapsed nodes, the set \<open>D\<close> of finished (done) nodes, and the set
    \<open>pE\<close> of pending edges.\<close>
  type_synonym 'v abs_state = "'v set list \<times> 'v set \<times> ('v \<times> 'v) multiset \<times> ('v \<times> 'v) set"
  
  context mdp_graph
  begin
    definition touched :: "'v set list \<Rightarrow> 'v set \<Rightarrow> 'v set" 
      \<comment> \<open>Touched: Nodes that are done or on path\<close>
      where "touched p D \<equiv> D \<union> \<Union>(set p)"
  end
  
  locale outer_invar_loc \<comment> \<open>Invariant of the outer loop\<close>
    = mdp_graph MG V\<^sub>i for MG :: "'v mdpG" and V\<^sub>i +
    fixes it :: "'v set" \<comment> \<open>Remaining nodes to iterate over\<close>
    fixes D :: "'v set" \<comment> \<open>Finished nodes\<close>
  
    assumes it_initial: "it\<subseteq>V\<^sub>i"  \<comment> \<open>Only start nodes to iterate over\<close>
  
    assumes it_done: "V0 - it \<subseteq> D"  \<comment> \<open>Nodes already iterated over are visited\<close>
    assumes D_reachable: "D\<subseteq>E_\<alpha>\<^sup>*``V0" \<comment> \<open>Done nodes are reachable\<close>
    assumes D_closed: "E_\<alpha>``D \<subseteq> D" \<comment> \<open>Done is closed under transitions\<close>
  
    assumes adm_subset_it: "V0 \<subseteq> V\<^sub>i" \<comment> \<open>The admissible states are a subset of the iterated states (V1)\<close>
  begin
  
    lemma locale_this: "outer_invar_loc MG V\<^sub>i it D" by unfold_locales
  
    definition (in mdp_graph) "outer_invar \<equiv> \<lambda>it D. outer_invar_loc MG V\<^sub>i it D"
  
    lemma outer_invar_this[simp, intro!]: "outer_invar it D"
      unfolding outer_invar_def by unfold_locales 
  end
  
  locale invar_loc \<comment> \<open>Invariant of the inner loop\<close>
    = 
  mdp_graph MG V\<^sub>i
    for MG::"'v mdpG" and V\<^sub>i +
    fixes v0 :: "'v"
    fixes D0 :: "'v set"
    fixes p :: "'v set list"
    fixes D :: "'v set"
    fixes pE :: "('v \<times> 'v) multiset"
    fixes vE :: "('v \<times> 'v) set"
  
    assumes v0_initial[simp, intro!]: "v0\<in>V0"
    assumes D_incr: "D0 \<subseteq> D"
  
    assumes vE_ss_E: "vE \<subseteq> E_\<alpha>" \<comment> \<open>Visited edges are edges\<close>
  
    assumes pE_E_from_p: "(set_mset pE) \<subseteq> E_\<alpha> \<inter> (\<Union>(set p)) \<times> UNIV" 
      \<comment> \<open>Pending edges are edges from path\<close>
    assumes E_from_p_touched: "E_\<alpha> \<inter> (\<Union>(set p) \<times> UNIV) \<subseteq> (set_mset pE) \<union> UNIV \<times> touched p D" 
      \<comment> \<open>Edges from path are pending or touched\<close>
    assumes D_reachable: "D\<subseteq>E_\<alpha>\<^sup>*``V0" \<comment> \<open>Done nodes are reachable\<close>
    assumes p_connected: "Suc i<length p \<Longrightarrow> p!i \<times> p!Suc i \<inter> vE \<noteq> {}"
      \<comment> \<open>CNodes on path are connected by visited edges\<close>
  
    assumes p_disjoint: "\<lbrakk>i<j; j<length p\<rbrakk> \<Longrightarrow> p!i \<inter> p!j = {}" 
      \<comment> \<open>CNodes on path are disjoint\<close>
    assumes p_sc: "U\<in>set p \<Longrightarrow> U\<times>U \<subseteq> (vE \<inter> U\<times>U)\<^sup>*" 
      \<comment> \<open>Nodes in CNodes are mutually reachable by visited edges\<close>
  
    assumes root_v0: "p\<noteq>[] \<Longrightarrow> v0\<in>hd p" \<comment> \<open>Root CNode contains start node\<close>
    assumes p_empty_v0: "p=[] \<Longrightarrow> v0\<in>D" \<comment> \<open>Start node is done if path empty\<close>
    
    assumes D_closed: "E_\<alpha>``D \<subseteq> D" \<comment> \<open>Done is closed under transitions\<close>
  
    assumes vE_no_back: "\<lbrakk>i<j; j<length p\<rbrakk> \<Longrightarrow> vE \<inter> p!j \<times> p!i = {}" 
    \<comment> \<open>Visited edges do not go back on path\<close>
  
    assumes p_not_D: "\<Union>(set p) \<inter> D = {}" \<comment> \<open>Path does not contain done nodes\<close>
  
    assumes D_vis: "E_\<alpha>\<inter>D\<times>UNIV \<subseteq> vE" \<comment> \<open>All edges from done nodes are visited\<close>
  
    assumes vE_touched: "vE \<subseteq> touched p D \<times> touched p D" \<comment> \<open>Visited edges only between touched nodes\<close>
    assumes pE_if_not_visited: "(E_\<alpha> \<inter> \<Union>(set p) \<times> UNIV) - vE \<subseteq> set_mset pE" \<comment> \<open>Edges from path not yet visited must be pending\<close>
  
    assumes adm_subset_it: "V0 \<subseteq> V\<^sub>i" \<comment> \<open>The admissible states are a subset of the iterated states (V1)\<close>
  begin
    abbreviation ltouched where "ltouched \<equiv> touched p D"
  
    lemma locale_this: "invar_loc MG V\<^sub>i v0 D0 p D pE vE" by unfold_locales
  
    definition (in mdp_graph) 
      "invar \<equiv> \<lambda> v0 D0 (p,D,pE,vE). invar_loc MG V\<^sub>i v0 D0 p D pE vE"
  
    lemma invar_this[simp, intro!]: "invar v0 D0 (p,D,pE,vE)"
      unfolding invar_def apply simp by unfold_locales 
  
    lemma finite_reachableE_v0[simp, intro!]: "finite (E_\<alpha>\<^sup>*``{v0})"
      apply (rule finite_subset[OF _ finite_reachableE_V0])
      using v0_initial by auto
  
  
    lemma path_touched: "\<Union>(set p) \<subseteq> ltouched" by (auto simp: touched_def)
    lemma D_touched: "D \<subseteq> ltouched" by (auto simp: touched_def)
  
    lemma D_succs_in_D: "E_\<alpha> \<inter> (D \<times> UNIV) = E_\<alpha> \<inter> (D \<times> D)"
      using D_closed by blast
  
    lemma D_image_closed: "E_\<alpha>\<^sup>*``D = D"
      using D_closed
      by (simp add: Image_closed_trancl)
  
  end
  
  subsubsection \<open>Termination\<close>
  
  
  context mdp_graph 
  begin
    text \<open>The termination argument is based on unprocessed edges: 
      Reachable edges from untouched nodes and pending edges.\<close>
    definition "reachable_edges v0 \<equiv> E_\<alpha> \<inter> (E_\<alpha>\<^sup>*``{v0}) \<times> (E_\<alpha>\<^sup>*``{v0})"
    lemma reachable_edges_alt: "reachable_edges v0 = E_\<alpha> \<inter> (E_\<alpha>\<^sup>*``{v0}) \<times> UNIV" 
      unfolding reachable_edges_def
      by auto
  
    definition "unproc_edges v0 vE \<equiv> reachable_edges v0 - vE"
  
    text \<open>
      In each iteration of the loop, either the number of unprocessed edges
      decreases, or the path length decreases.\<close>
    definition "abs_wf_rel v0 \<equiv> inv_image (finite_psubset <*lex*> measure size <*lex*> measure length)
      (\<lambda>(p,D,pE,vE). (unproc_edges v0 vE, pE, p))"
  
    lemma abs_wf_rel_wf[simp, intro!]: "wf (abs_wf_rel v0)"
      unfolding abs_wf_rel_def
      by auto
  end
  
  subsection \<open>Abstract Skeleton Algorithm\<close>
  
  context mdp_graph
  begin
    \<comment> \<open>The edges starting in a specified state.\<close>
    definition out_edges :: "'v \<Rightarrow> (('v \<times> 'v) multiset) nres" where
      "out_edges v = SPEC (\<lambda> r. set_mset r = (E_\<alpha> \<inter> {v}\<times>UNIV))"
  
    \<comment> \<open>The initial loop state of the inner loop of our algorithm.\<close>
    definition initial :: "'v \<Rightarrow> 'v set \<Rightarrow> ('v abs_state) nres"
      where "initial v0 D \<equiv> do { pE \<leftarrow> out_edges v0; RETURN([{v0}], D, pE, E_\<alpha>\<inter>D\<times>UNIV)}"
  
    definition (in -) collapse_aux :: "'a set list \<Rightarrow> nat \<Rightarrow> 'a set list"
      where "collapse_aux p i \<equiv> take i p @ [\<Union>(set (drop i p))]"
    
    \<comment> \<open>Collapse all nodes on the path into one Cnode.\<close>
    definition (in -) collapse :: "'a \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" 
      where "collapse v PDPE \<equiv> 
      let 
        (p,D,pE,vE)=PDPE; 
        i=idx_of p v;
        p = collapse_aux p i
      in (p,D,pE,vE)"
  
    \<comment> \<open>Pick an edge starting from the last Cnode in the path.\<close>
    definition (in -) 
      select_edge :: "'a abs_state \<Rightarrow> ('a option \<times> 'a abs_state) nres"
      where
      "select_edge PDPE \<equiv> do {
        let (p,D,pE,vE) = PDPE;
        e \<leftarrow> SELECT (\<lambda>e. e \<in> (set_mset pE) \<inter> last p \<times> UNIV);
        case e of
          None \<Rightarrow> RETURN (None,(p,D,pE,vE))
        | Some (u,v) \<Rightarrow> RETURN (Some v, (p,D,pE - {#(u,v)#},insert (u,v) vE))
      }"
  
    \<comment> \<open>Add a node (as a Cnode) to the end of the path\<close>
    definition (in mdp_graph) push :: "'v \<Rightarrow> 'v abs_state \<Rightarrow> ('v abs_state) nres" 
      where "push v PDPE \<equiv> 
      do {
        let (p,D,pE,vE) = PDPE;
        let p = p@[{v}];
        pE' \<leftarrow> out_edges v;
        let pE = pE + pE';
        RETURN (p,D,pE,vE)
      }"
  
    \<comment> \<open>Remove the last state from the path and mark them as "done"\<close>
    definition (in -) pop :: "'v abs_state \<Rightarrow> 'v abs_state"
      where "pop PDPE \<equiv> let
        (p,D,pE,vE) = PDPE;
        (p,V) = (butlast p, last p);
        D = V \<union> D
      in
        (p,D,pE,vE)"
  
    \<comment> \<open>The skeleton algorithm which returns a set of "done" nodes\<close>
    definition skeleton :: "'v set nres" 
      \<comment> \<open>Abstract Skeleton Algorithm\<close>
      where
      "skeleton \<equiv> do {
        let D = {};
        r \<leftarrow> FOREACHi outer_invar V\<^sub>i (\<lambda> v0 D0. do {
          if v0 \<in> V0 \<and> v0\<notin>D0 then do {
            ASSERT(v0 \<in> E_\<alpha>\<^sup>*``V0);
            s \<leftarrow> initial v0 D0;
  
            (p,D,pE,vE) \<leftarrow> WHILEIT (invar v0 D0)
              (\<lambda>(p,D,pE,vE). p \<noteq> []) (\<lambda>(p,D,pE,vE). 
            do {
              \<comment> \<open>Select edge from end of path\<close>
              (vo,(p,D,pE,vE)) \<leftarrow> select_edge (p,D,pE,vE);
  
              ASSERT (p\<noteq>[]);
              case vo of 
                Some v \<Rightarrow> do { \<comment> \<open>Found outgoing edge to node \<open>v\<close>\<close>
                  ASSERT (v \<in> E_\<alpha>\<^sup>* `` V0);
                  if v \<in> \<Union>(set p) then do {
                    \<comment> \<open>Back edge: Collapse path\<close>
                    RETURN (collapse v (p,D,pE,vE))
                  } else if v\<notin>D then do {
                    \<comment> \<open>Edge to new node. Append to path\<close>
                    push v (p,D,pE,vE)
                  } else do {
                    \<comment> \<open>Edge to done node. Skip\<close>
                    RETURN (p,D,pE,vE)
                  }
                }
              | None \<Rightarrow> do {
                  ASSERT ((set_mset pE) \<inter> last p \<times> UNIV = {});
                  \<comment> \<open>No more outgoing edges from current node on path\<close>
                  RETURN (pop (p,D,pE,vE))
                }
            }) s;
            ASSERT (p=[] \<and> pE={#});
            RETURN D
          } else
            RETURN D0
        }) D;
        RETURN r
      }"
  
  end
  
  subsection \<open>Invariant Preservation\<close>
  
  context mdp_graph begin
  
    lemma set_collapse_aux[simp]: "\<Union>(set (collapse_aux p i)) = \<Union>(set p)"
      apply (subst (2) append_take_drop_id[of _ p,symmetric])
      apply (simp del: append_take_drop_id)
      unfolding collapse_aux_def by auto
  
    lemma touched_collapse[simp]: "touched (collapse_aux p i) D = touched p D"
      unfolding touched_def by simp
  
    lemma touched_push[simp]: "touched (p @ [V]) D = touched p D \<union> V"
      unfolding touched_def by auto
  
  end
  
  subsubsection \<open>Corollaries of the invariant\<close>
  text \<open>In this section, we prove some more corollaries of the invariant,
    which are helpful to show invariant preservation\<close>
  
  context invar_loc
  begin
    lemma cnode_connectedI: 
      "\<lbrakk>i<length p; u\<in>p!i; v\<in>p!i\<rbrakk> \<Longrightarrow> (u,v)\<in>(vE \<inter> p!i\<times>p!i)\<^sup>*"
      using p_sc[of "p!i"] by (auto simp: in_set_conv_nth)
  
    lemma cnode_connectedI': "\<lbrakk>i<length p; u\<in>p!i; v\<in>p!i\<rbrakk> \<Longrightarrow> (u,v)\<in>(vE)\<^sup>*"
      by (metis inf.cobounded1 rtrancl_mono_mp cnode_connectedI)
  
    lemma p_no_empty: "{} \<notin> set p"
    proof 
      assume "{}\<in>set p"
      then obtain i where IDX: "i<length p" "p!i={}" 
        by (auto simp add: in_set_conv_nth)
      show False proof (cases i)
        case 0 with root_v0 IDX show False by (cases p) auto
      next
        case [simp]: (Suc j)
        from p_connected[of j] IDX show False by simp
      qed
    qed
  
    corollary p_no_empty_idx: "i<length p \<Longrightarrow> p!i\<noteq>{}"
      using p_no_empty by (metis nth_mem)
    
    lemma p_disjoint_sym: "\<lbrakk>i<length p; j<length p; v\<in>p!i; v\<in>p!j\<rbrakk> \<Longrightarrow> i=j"
      by (metis disjoint_iff_not_equal linorder_neqE_nat p_disjoint)
  
    lemma pi_ss_path_seg_eq[simp]:
      assumes A: "i<length p" "u\<le>length p"
      shows "p!i\<subseteq>path_seg p l u \<longleftrightarrow> l\<le>i \<and> i<u"
    proof
      assume B: "p!i\<subseteq>path_seg p l u"
      from A obtain x where "x\<in>p!i" by (blast dest: p_no_empty_idx)
      with B obtain i' where C: "x\<in>p!i'" "l\<le>i'" "i'<u" 
        by (auto simp: path_seg_def)
      from p_disjoint_sym[OF \<open>i<length p\<close> _ \<open>x\<in>p!i\<close> \<open>x\<in>p!i'\<close>] \<open>i'<u\<close> \<open>u\<le>length p\<close>
      have "i=i'" by simp
      with C show "l\<le>i \<and> i<u" by auto
    qed (auto simp: path_seg_def)
  
    lemma path_seg_ss_eq[simp]:
      assumes A: "l1<u1" "u1\<le>length p" "l2<u2" "u2\<le>length p"
      shows "path_seg p l1 u1 \<subseteq> path_seg p l2 u2 \<longleftrightarrow> l2\<le>l1 \<and> u1\<le>u2"
    proof
      assume S: "path_seg p l1 u1 \<subseteq> path_seg p l2 u2"
      have "p!l1 \<subseteq> path_seg p l1 u1" using A by simp
      also note S finally have 1: "l2\<le>l1" using A by simp
      have "p!(u1 - 1) \<subseteq> path_seg p l1 u1" using A by simp
      also note S finally have 2: "u1\<le>u2" using A by auto
      from 1 2 show "l2\<le>l1 \<and> u1\<le>u2" ..
    next
      assume "l2\<le>l1 \<and> u1\<le>u2" thus "path_seg p l1 u1 \<subseteq> path_seg p l2 u2"
        using A
        apply (clarsimp simp: path_seg_def) []
        apply (metis dual_order.strict_trans1 dual_order.trans)
        done
    qed
  
    lemma pathI: 
      assumes "x\<in>p!i" "y\<in>p!j"
      assumes "i\<le>j" "j<length p"
      defines "seg \<equiv> path_seg p i (Suc j)"
      shows "(x,y)\<in>(vE \<inter> seg\<times>seg)\<^sup>*"
      \<comment> \<open>We can obtain a path between cnodes on path\<close>
      using assms(3,1,2,4) unfolding seg_def
    proof (induction arbitrary: y rule: dec_induct)
      case base thus ?case by (auto intro!: cnode_connectedI)
    next
      case (step j)
  
      let ?seg = "path_seg p i (Suc j)"
      let ?seg' = "path_seg p i (Suc (Suc j))"
  
      have SSS: "?seg \<subseteq> ?seg'" 
        apply (subst path_seg_ss_eq)
        using step.hyps step.prems by auto
  
      from p_connected[OF \<open>Suc j < length p\<close>] obtain u v where 
        UV: "(u,v)\<in>vE" "u\<in>p!j" "v\<in>p!Suc j" by auto
  
      have ISS: "p!j \<subseteq> ?seg'" "p!Suc j \<subseteq> ?seg'" 
        using step.hyps step.prems by simp_all
  
      from p_no_empty_idx[of j] \<open>Suc j < length p\<close> obtain x' where "x'\<in>p!j" 
        by auto
      with step.IH[of x'] \<open>x\<in>p!i\<close> \<open>Suc j < length p\<close> 
      have t: "(x,x')\<in>(vE\<inter>?seg\<times>?seg)\<^sup>*" by auto
      have "(x,x')\<in>(vE\<inter>?seg'\<times>?seg')\<^sup>*" using SSS 
        by (auto intro: rtrancl_mono_mp[OF _ t])
      also 
      from cnode_connectedI[OF _ \<open>x'\<in>p!j\<close> \<open>u\<in>p!j\<close>] \<open>Suc j < length p\<close> have
        t: "(x', u) \<in> (vE \<inter> p ! j \<times> p ! j)\<^sup>*" by auto
      have "(x', u) \<in> (vE\<inter>?seg'\<times>?seg')\<^sup>*" using ISS
        by (auto intro: rtrancl_mono_mp[OF _ t])
      also have "(u,v)\<in>vE\<inter>?seg'\<times>?seg'" using UV ISS by auto
      also from cnode_connectedI[OF \<open>Suc j < length p\<close> \<open>v\<in>p!Suc j\<close> \<open>y\<in>p!Suc j\<close>] 
      have t: "(v, y) \<in> (vE \<inter> p ! Suc j \<times> p ! Suc j)\<^sup>*" by auto
      have "(v, y) \<in> (vE\<inter>?seg'\<times>?seg')\<^sup>*" using ISS
        by (auto intro: rtrancl_mono_mp[OF _ t])
      finally show "(x,y)\<in>(vE\<inter>?seg'\<times>?seg')\<^sup>*" .
    qed
  
    lemma p_reachable: "\<Union>(set p) \<subseteq> E_\<alpha>\<^sup>*``{v0}" \<comment> \<open>Nodes on path are reachable\<close>
    proof 
      fix v
      assume A: "v\<in>\<Union>(set p)"
      then obtain i where "i<length p" and "v\<in>p!i" 
        by (metis UnionE in_set_conv_nth)
      moreover from A root_v0 have "v0\<in>p!0" by (cases p) auto
      ultimately have 
        t: "(v0,v)\<in>(vE \<inter> path_seg p 0 (Suc i) \<times> path_seg p 0 (Suc i))\<^sup>*"
        by (auto intro: pathI)
      from vE_ss_E have "(v0,v)\<in>E_\<alpha>\<^sup>*" by (auto intro: rtrancl_mono_mp[OF _ t])
      thus "v\<in>E_\<alpha>\<^sup>*``{v0}" by auto
    qed
  
    lemma p_elem_reachable: "X \<in> set p \<Longrightarrow> X \<subseteq> E_\<alpha>\<^sup>* `` {v0}"
      using p_reachable
      by blast
  
    lemma touched_reachable: "ltouched \<subseteq> E_\<alpha>\<^sup>*``V0" \<comment> \<open>Touched nodes are reachable\<close>
      unfolding touched_def using p_reachable D_reachable by blast
  
    lemma vE_reachable: "vE \<subseteq> E_\<alpha>\<^sup>*``V0 \<times> E_\<alpha>\<^sup>*``V0"
      apply (rule order_trans[OF vE_touched])
      using touched_reachable by blast
  
    lemma pE_reachable: "(set_mset pE) \<subseteq> E_\<alpha>\<^sup>*``{v0} \<times> E_\<alpha>\<^sup>*``{v0}"
    proof safe
      fix u v
      assume E: "(u,v)\<in>#pE"
      with pE_E_from_p p_reachable have "(v0,u)\<in>E_\<alpha>\<^sup>*" "(u,v)\<in>E_\<alpha>" by blast+
      thus "(v0,u)\<in>E_\<alpha>\<^sup>*" "(v0,v)\<in>E_\<alpha>\<^sup>*" by auto
    qed
  
    lemma D_closed_vE_rtrancl: "vE\<^sup>*``D \<subseteq> D"
      by (metis D_closed Image_closed_trancl eq_iff reachable_mono vE_ss_E)
  
    lemma D_closed_path: "\<lbrakk>path E_\<alpha> u q w; u\<in>D\<rbrakk> \<Longrightarrow> set q \<subseteq> D"
    proof -
      assume a1: "path E_\<alpha> u q w"
      assume "u \<in> D"
      hence f1: "{u} \<subseteq> D"
        using bot.extremum by force
      have "set q \<subseteq> E_\<alpha>\<^sup>* `` {u}"
        using a1 by (metis insert_subset path_nodes_reachable)
      thus "set q \<subseteq> D"
        using f1 by (metis D_closed rtrancl_reachable_induct subset_trans)
    qed
  
    lemma D_closed_path_vE: "\<lbrakk>path vE u q w; u\<in>D\<rbrakk> \<Longrightarrow> set q \<subseteq> D"
      by (metis D_closed_path path_mono vE_ss_E)
  
    lemma path_in_lastnode:
      assumes P: "path vE u q v"
      assumes [simp]: "p\<noteq>[]"
      assumes ND: "u\<in>last p" "v\<in>last p"
      shows "set q \<subseteq> last p"
      \<comment> \<open>A path from the last Cnode to the last Cnode remains in the last Cnode\<close>
      using P ND
    proof (induction)
      case (path_prepend u v l w) 
      from \<open>(u,v)\<in>vE\<close> vE_touched have "v\<in>ltouched" by auto
      hence "v\<in>\<Union>(set p)"
        unfolding touched_def
      proof
        assume "v\<in>D"
        moreover from \<open>path vE v l w\<close> have "(v,w)\<in>vE\<^sup>*" by (rule path_is_rtrancl)
        ultimately have "w\<in>D" using D_closed_vE_rtrancl by auto
        with \<open>w\<in>last p\<close> p_not_D have False
          by (metis IntI Misc.last_in_set Sup_inf_eq_bot_iff assms(2) 
            bex_empty path_prepend.hyps(2))
        thus ?thesis ..
      qed
      then obtain i where "i<length p" "v\<in>p!i"
        by (metis UnionE in_set_conv_nth)
      have "i=length p - 1"
      proof (rule ccontr)
        assume "i\<noteq>length p - 1"
        with \<open>i<length p\<close> have "i < length p - 1" by simp
        with vE_no_back[of i "length p - 1"] \<open>i<length p\<close> 
        have "vE \<inter> last p \<times> p!i = {}"
          by (simp add: last_conv_nth)
        with \<open>(u,v)\<in>vE\<close> \<open>u\<in>last p\<close> \<open>v\<in>p!i\<close> show False by auto
      qed
      with \<open>v\<in>p!i\<close> have "v\<in>last p" by (simp add: last_conv_nth)
      with path_prepend.IH \<open>w\<in>last p\<close> \<open>u\<in>last p\<close> show ?case by auto
    qed simp
  
    lemma loop_in_lastnode:
      assumes P: "path vE u q u"
      assumes [simp]: "p\<noteq>[]"
      assumes ND: "set q \<inter> last p \<noteq> {}"
      shows "u\<in>last p" and "set q \<subseteq> last p"
      \<comment> \<open>A loop that touches the last node is completely inside the last node\<close>
    proof -
      from ND obtain v where "v\<in>set q" "v\<in>last p" by auto
      then obtain q1 q2 where [simp]: "q=q1@v#q2" 
        by (auto simp: in_set_conv_decomp)
      from P have "path vE v (v#q2@q1) v" 
        by (auto simp: path_conc_conv path_cons_conv)
      from path_in_lastnode[OF this \<open>p\<noteq>[]\<close> \<open>v\<in>last p\<close> \<open>v\<in>last p\<close>] 
      show "set q \<subseteq> last p" by simp
      from P show "u\<in>last p" 
        apply (cases q, simp)
        
        apply simp
        using \<open>set q \<subseteq> last p\<close>
        apply (auto simp: path_cons_conv)
        done
    qed
  
  
    lemma no_D_p_edges: "E_\<alpha> \<inter> D \<times> \<Union>(set p) = {}"
      using D_closed p_not_D by auto
  
    lemma idx_of_props:
      assumes ON_STACK: "v\<in>\<Union>(set p)"
      shows 
        "idx_of p v < length p" and
        "v \<in> p ! idx_of p v"
      using idx_of_props[OF _ assms] p_disjoint_sym by blast+
  
  end
  
  subsubsection \<open>Auxiliary Lemmas Regarding the Operations\<close>
  
  
  context invar_loc
  begin
  
  
    lemma pE_fin: "p=[] \<Longrightarrow> pE={#}"
      using pE_E_from_p by auto
  
    lemma (in invar_loc) lastp_un_D_closed:
      assumes NE: "p \<noteq> []"
      assumes NO': "(set_mset pE) \<inter> (last p \<times> UNIV) = {}"
      shows "E_\<alpha>``(last p \<union> D) \<subseteq> (last p \<union> D)"
      \<comment> \<open>On pop, the popped CNode and D are closed under transitions\<close>
    proof (intro subsetI, elim ImageE)
  
      have "(E_\<alpha> - vE) \<inter> (last p \<times> UNIV) = (E_\<alpha> \<inter> \<Union> (set p) \<times> UNIV - vE) \<inter> (last p \<times> UNIV)" 
        using NE by blast
      also from pE_if_not_visited have "... \<subseteq> (set_mset pE) \<inter> (last p \<times> UNIV)"
        by fast
      finally have NO: "(E_\<alpha> - vE) \<inter> (last p \<times> UNIV) = {}" using NO' by blast
  
      let ?i = "length p - 1"
      from NE have [simp]: "last p = p!?i" by (metis last_conv_nth) 
      
      fix u v
      assume E: "(u,v)\<in>E_\<alpha>"
      assume UI: "u\<in>last p \<union> D" hence "u\<in>p!?i \<union> D" by simp
      
      {
        assume "u\<in>last p" "v\<notin>last p" 
        moreover from E NO \<open>u\<in>last p\<close> have "(u,v)\<in>vE" by auto
        ultimately have "v\<in>D \<or> v\<in>\<Union>(set p)" 
          using vE_touched unfolding touched_def by auto
        moreover {
          assume "v\<in>\<Union>(set p)"
          then obtain j where V: "j<length p" "v\<in>p!j" 
            by (metis UnionE in_set_conv_nth)
          with \<open>v\<notin>last p\<close> have "j<?i" by (cases "j=?i") auto
          from vE_no_back[OF \<open>j<?i\<close> _] \<open>(u,v)\<in>vE\<close> V \<open>u\<in>last p\<close> have False by auto
        } ultimately have "v\<in>D" by blast
      } with E UI D_closed show "v\<in>last p \<union> D" by auto
    qed
  
  
  
  end


  subsubsection \<open>Preservation of Invariant by Operations\<close>
  
  context mdp_graph
  begin
    lemma (in outer_invar_loc) invar_initial_aux: 
      assumes "v0\<in>it - D"
      assumes "v0 \<in> V0"
      shows "initial v0 D \<le> SPEC (invar v0 D)"
      unfolding invar_def initial_def out_edges_def
      apply refine_vcg
      apply clarsimp
      apply unfold_locales
      apply simp_all
      using assms it_initial apply auto []
      using D_reachable it_initial assms apply auto [] 
      using D_closed apply auto []
      using assms apply auto []
      unfolding touched_def 
      apply(subgoal_tac "E_\<alpha> \<inter> D \<times> UNIV \<subseteq> E_\<alpha> \<inter> D \<times> D")
        apply blast
        using D_closed apply blast
      apply blast
      using adm_subset_it apply blast
      done
  
    lemma invar_initial: 
      "\<lbrakk>outer_invar it D0; v0\<in>it; v0\<notin>D0; v0 \<in> V0\<rbrakk> \<Longrightarrow> initial v0 D0 \<le> SPEC (invar v0 D0)"
      unfolding outer_invar_def
      apply (drule outer_invar_loc.invar_initial_aux) 
      by auto
  
    lemma outer_invar_initial[simp, intro!]: "outer_invar V\<^sub>i {}"
      unfolding outer_invar_def
      apply unfold_locales 
      using adm_subset_it
      by auto
  
    lemma invar_pop:
      assumes INV: "invar v0 D0 (p,D,pE,vE)"
      assumes NE[simp]: "p\<noteq>[]"
      assumes NO': "(set_mset pE) \<inter> (last p \<times> UNIV) = {}"
      shows "invar v0 D0 (pop (p,D,pE,vE))"
      unfolding invar_def pop_def
      apply simp
    proof -
      from INV interpret invar_loc MG V\<^sub>i v0 D0 p D pE unfolding invar_def by simp
  
      have [simp]: "set p = insert (last p) (set (butlast p))" 
        using NE by (cases p rule: rev_cases) auto
  
      from p_disjoint have lp_dj_blp: "last p \<inter> \<Union>(set (butlast p)) = {}"
        apply (cases p rule: rev_cases)
        apply simp
        apply (fastforce simp: in_set_conv_nth nth_append)
        done
  
      {
        fix i
        assume A: "Suc i < length (butlast p)"
        hence A': "Suc i < length p" by auto
  
        from nth_butlast[of i p] A have [simp]: "butlast p ! i = p ! i" by auto
        from nth_butlast[of "Suc i" p] A 
        have [simp]: "butlast p ! Suc i = p ! Suc i" by auto
  
        from p_connected[OF A'] 
        have "butlast p ! i \<times> butlast p ! Suc i \<inter> vE \<noteq> {}"
          by simp
      } note AUX_p_connected = this
  
      have AUX_last_p_visited: "E_\<alpha> \<inter> last p \<times> UNIV \<subseteq> vE"
      proof safe
        fix u v
        assume UVE: "(u,v) \<in> E_\<alpha>"
        and ULP: "u \<in> last p"
        hence "(u,v) \<notin># pE" using NO' by blast
        moreover have "(u,v) \<in> E_\<alpha> \<inter> (\<Union>(set p)) \<times> UNIV" using ULP UVE by auto
        ultimately show "(u,v) \<in> vE" using pE_if_not_visited by blast
      qed
  
      show "invar_loc MG V\<^sub>i v0 D0 (butlast p) (last p \<union> D) pE vE"
        apply unfold_locales
  
        apply simp
  
        using D_incr apply auto []
        
        using vE_ss_E apply simp
  
        using pE_E_from_p NO' apply auto []
    
        using E_from_p_touched apply (auto simp: touched_def) []
    
        using D_reachable p_reachable NE apply auto []
  
        apply (rule AUX_p_connected, assumption+) []
  
        using p_disjoint apply (simp add: nth_butlast)
  
        using p_sc apply simp
  
        using root_v0 apply (cases p rule: rev_cases) apply auto [2]
  
        using root_v0 p_empty_v0 apply (cases p rule: rev_cases) apply auto [2]
  
        apply (rule lastp_un_D_closed, insert NO', auto) []
  
        using vE_no_back apply (auto simp: nth_butlast) []
  
        using p_not_D lp_dj_blp apply auto []
  
        using D_vis AUX_last_p_visited apply blast
  
        using vE_touched unfolding touched_def apply auto[1]
  
        using pE_if_not_visited apply auto[]
  
        using adm_subset_it apply auto[]
  
        done
    qed
  
    lemma set_mset_subtract_cases: obtains "set_mset (m-{#x#}) = set_mset m" | "set_mset (m-{#x#}) = set_mset m - {x}"
      by (meson at_most_one_mset_mset_diff more_than_one_mset_mset_diff)
  
    lemma "x \<in> A \<Longrightarrow> x \<notin> A - B \<Longrightarrow> x \<in> B" by simp
  
    lemma nmmem_diff_mmem_sub: "x \<in># A \<Longrightarrow> x \<notin># A - B \<Longrightarrow> x \<in># B"
      by (metis mset_diff_cancel1elem mset_le_subtract single_subset_iff)
  
  
    lemma invar_collapse:
      assumes INV: "invar v0 D0 (p,D,pE,vE)"
      assumes NE[simp]: "p\<noteq>[]"
      assumes E: "(u,v)\<in>#pE" and "u\<in>last p"
      assumes BACK: "v\<in>\<Union>(set p)"
      defines "i \<equiv> idx_of p v"
      defines "p' \<equiv> collapse_aux p i"
      shows "invar v0 D0 (collapse v (p,D,pE - {#(u,v)#},insert (u,v) vE))"
      unfolding invar_def collapse_def
      apply simp
      unfolding i_def[symmetric] p'_def[symmetric]
    proof -
      from INV interpret invar_loc MG V\<^sub>i v0 D0 p D pE unfolding invar_def by simp
  
      let ?thesis="invar_loc MG V\<^sub>i v0 D0 p' D (pE - {#(u,v)#}) (insert (u,v) vE)"
  
      have SETP'[simp]: "\<Union>(set p') = \<Union>(set p)" unfolding p'_def by simp
  
      have IL: "i < length p" and VMEM: "v\<in>p!i" 
        using idx_of_props[OF BACK] unfolding i_def by auto
  
      have [simp]: "length p' = Suc i" 
        unfolding p'_def collapse_aux_def using IL by auto
  
      have P'_IDX_SS: "\<forall>j<Suc i. p!j \<subseteq> p'!j"
        unfolding p'_def collapse_aux_def using IL 
        by (auto simp add: nth_append path_seg_drop)
  
      from \<open>u\<in>last p\<close> have "u\<in>p!(length p - 1)" by (auto simp: last_conv_nth)
  
      have defs_fold: 
        "touched p' D = ltouched"
        by (simp_all add: p'_def E)
  
      {
        fix j
        assume A: "Suc j < length p'" 
        hence "Suc j < length p" using IL by simp
        note p_connected[OF this]
        moreover from P'_IDX_SS A have "p!j\<subseteq>p'!j" and "p!Suc j \<subseteq> p'!Suc j"
          by auto
        ultimately have "p' ! j \<times> p' ! Suc j \<inter> insert (u,v) vE \<noteq> {}" 
          by blast
      } note AUX_p_connected = this
  
      have P_IDX_EQ[simp]: "\<forall>j. j < i \<longrightarrow> p'!j = p!j"
        unfolding p'_def collapse_aux_def using IL  
        by (auto simp: nth_append)
  
      have P'_LAST[simp]: "p'!i = path_seg p i (length p)" (is "_ = ?last_cnode")
        unfolding p'_def collapse_aux_def using IL 
        by (auto simp: nth_append path_seg_drop)
  
      {
        fix j k
        assume A: "j < k" "k < length p'" 
        have "p' ! j \<inter> p' ! k = {}"
        proof (safe, simp)
          fix v
          assume "v\<in>p'!j" and "v\<in>p'!k"
          with A have "v\<in>p!j" by simp
          show False proof (cases)
            assume "k=i"
            with \<open>v\<in>p'!k\<close> obtain k' where "v\<in>p!k'" "i\<le>k'" "k'<length p" 
              by (auto simp: path_seg_def)
            hence "p ! j \<inter> p ! k' = {}"
              using A by (auto intro!: p_disjoint)
            with \<open>v\<in>p!j\<close> \<open>v\<in>p!k'\<close> show False by auto
          next
            assume "k\<noteq>i" with A have "k<i" by simp
            hence "k<length p" using IL by simp
            note p_disjoint[OF \<open>j<k\<close> this] 
            also have "p!j = p'!j" using \<open>j<k\<close> \<open>k<i\<close> by simp
            also have "p!k = p'!k" using \<open>k<i\<close> by simp
            finally show False using \<open>v\<in>p'!j\<close> \<open>v\<in>p'!k\<close> by auto
          qed
        qed
      } note AUX_p_disjoint = this
  
      {
        fix U
        assume A: "U\<in>set p'"
        then obtain j where "j<Suc i" and [simp]: "U=p'!j"
          by (auto simp: in_set_conv_nth)
        hence "U \<times> U \<subseteq> (insert (u, v) vE \<inter> U \<times> U)\<^sup>*" 
        proof cases
          assume [simp]: "j=i"
          show ?thesis proof (clarsimp)
            fix x y
            assume "x\<in>path_seg p i (length p)" "y\<in>path_seg p i (length p)"
            then obtain ix iy where 
              IX: "x\<in>p!ix" "i\<le>ix" "ix<length p" and
              IY: "y\<in>p!iy" "i\<le>iy" "iy<length p"
              by (auto simp: path_seg_def)
              
  
            from IX have SS1: "path_seg p ix (length p) \<subseteq> ?last_cnode"
              by (subst path_seg_ss_eq) auto
  
            from IY have SS2: "path_seg p i (Suc iy) \<subseteq> ?last_cnode"
              by (subst path_seg_ss_eq) auto
  
            let ?rE = "\<lambda>R. (vE \<inter> R\<times>R)"
            let ?E = "(insert (u,v) vE \<inter> ?last_cnode \<times> ?last_cnode)"
  
            from pathI[OF \<open>x\<in>p!ix\<close> \<open>u\<in>p!(length p - 1)\<close>] have
              "(x,u)\<in>(?rE (path_seg p ix (Suc (length p - 1))))\<^sup>*" using IX by auto
            hence "(x,u)\<in>?E\<^sup>*" 
              apply (rule rtrancl_mono_mp[rotated]) 
              using SS1
              by auto
  
            also have "(u,v)\<in>?E" using \<open>i<length p\<close>
              apply (clarsimp)
              apply (intro conjI)
              apply (rule rev_subsetD[OF \<open>u\<in>p!(length p - 1)\<close>])
              apply (simp)
              apply (rule rev_subsetD[OF VMEM])
              apply (simp)
              done
            also 
            from pathI[OF \<open>v\<in>p!i\<close> \<open>y\<in>p!iy\<close>] have
              "(v,y)\<in>(?rE (path_seg p i (Suc iy)))\<^sup>*" using IY by auto
            hence "(v,y)\<in>?E\<^sup>*"
              apply (rule rtrancl_mono_mp[rotated]) 
              using SS2
              by auto
            finally show "(x,y)\<in>?E\<^sup>*" .
          qed
        next
          assume "j\<noteq>i"
          with \<open>j<Suc i\<close> have [simp]: "j<i" by simp
          with \<open>i<length p\<close> have "p!j\<in>set p"
            by (metis Suc_lessD in_set_conv_nth less_trans_Suc) 
  
          thus ?thesis using p_sc[of U] \<open>p!j\<in>set p\<close>
            apply (clarsimp)
            apply (subgoal_tac "(a,b)\<in>(vE \<inter> p ! j \<times> p ! j)\<^sup>*")
            apply (erule rtrancl_mono_mp[rotated])
            apply auto
            done
        qed
      } note AUX_p_sc = this
  
      { fix j k
        assume A: "j<k" "k<length p'"
        hence "j<i" by simp
        have "insert (u, v) vE \<inter> p' ! k \<times> p' ! j = {}"
        proof -
          have "{(u,v)} \<inter> p' ! k \<times> p' ! j = {}" 
            apply auto
            by (metis IL P_IDX_EQ Suc_lessD VMEM \<open>j < i\<close> 
              less_irrefl_nat less_trans_Suc p_disjoint_sym)
          moreover have "vE \<inter> p' ! k \<times> p' ! j = {}" 
          proof (cases "k<i")
            case True thus ?thesis
              using vE_no_back[of j k] A \<open>i<length p\<close> by auto
          next
            case False with A have [simp]: "k=i" by simp
            show ?thesis proof (rule disjointI, clarsimp simp: \<open>j<i\<close>)
              fix x y
              assume B: "(x,y)\<in>vE" "x\<in>path_seg p i (length p)" "y\<in>p!j"
              then obtain ix where "x\<in>p!ix" "i\<le>ix" "ix<length p" 
                by (auto simp: path_seg_def)
              moreover with A have "j<ix" by simp
              ultimately show False using vE_no_back[of j ix] B by auto
            qed
          qed
          ultimately show ?thesis by blast
        qed
      } note AUX_vE_no_back = this
  
      have V_TOUCHED: "v\<in>ltouched" using BACK path_touched by auto
  
      note pE_removed_cases = set_mset_subtract_cases[of pE "(u,v)"]
  
      
  
      show ?thesis
        apply unfold_locales
        unfolding defs_fold
  
        subgoal by simp
  
        subgoal using D_incr by auto []
  
        subgoal using vE_ss_E E pE_E_from_p by blast
  
        subgoal using pE_E_from_p in_diffD SETP' subset_eq by metis
        
        subgoal
          apply (simp) using E_from_p_touched V_TOUCHED 
          apply (cases rule: pE_removed_cases)
          by (auto)
  
        subgoal by (rule D_reachable)    
  
        subgoal by (rule AUX_p_connected)
  
        subgoal by (rule AUX_p_disjoint)
  
        subgoal for U by (rule AUX_p_sc)
  
        subgoal
          using root_v0 
          apply (cases i) 
          apply (simp add: p'_def collapse_aux_def)
          apply (metis NE hd_in_set)
          apply (cases p, simp_all add: p'_def collapse_aux_def) []
          done
  
        subgoal by (simp add: p'_def collapse_aux_def)
  
        subgoal by (rule D_closed)
  
        subgoal by (drule (1) AUX_vE_no_back, auto)
  
        subgoal using p_not_D by simp
  
        subgoal using D_vis by auto
  
        subgoal 
          using V_TOUCHED vE_touched 
          apply clarsimp
          using \<open>u\<in>last p\<close> path_touched 
          by fastforce
  
        subgoal 
          apply clarsimp
          subgoal for u v X
            apply(subgoal_tac "(u,v) \<in> E_\<alpha> \<inter> \<Union> (set p) \<times> UNIV - vE")
            subgoal
              apply(drule pE_if_not_visited[THEN in_mono[THEN mp], THEN nmmem_diff_mmem_sub] ) 
              by auto
            subgoal by blast
          done
        done
        
        subgoal 
          by (simp add: adm_subset_it)
      done
  
    qed
    
    lemma invar_push:
      assumes INV: "invar v0 D0 (p,D,pE,vE)"
      assumes NE[simp]: "p\<noteq>[]"
      assumes E: "(u,v)\<in>#pE" and UIL: "u\<in>last p"
      assumes VNE: "v\<notin>\<Union>(set p)" "v\<notin>D"
      shows "push v (p,D,pE - {#(u,v)#}, insert (u,v) vE) \<le> SPEC (invar v0 D0)"
      unfolding invar_def push_def out_edges_def
      apply refine_vcg
      apply clarsimp
    proof -
      fix succE
      assume succE_v: "set_mset succE = E_\<alpha> \<inter> {v} \<times> UNIV"
  
      from INV interpret invar_loc MG V\<^sub>i v0 D0 p D pE unfolding invar_def by simp
  
      let ?thesis 
        = "invar_loc MG V\<^sub>i v0 D0 (p @ [{v}]) D (pE - {#(u, v)#} + succE) (insert (u, v) vE)"
  
      note defs_fold = touched_push
  
      note pE_removed_cases = set_mset_subtract_cases[of pE "(u,v)"]
  
      {
        fix i
        assume SILL: "Suc i < length (p @ [{v}])"
        have "(p @ [{v}]) ! i \<times> (p @ [{v}]) ! Suc i 
               \<inter> insert (u, v) vE \<noteq> {}"
        proof (cases "i = length p - 1")
          case True thus ?thesis using SILL E pE_E_from_p UIL VNE
            by (simp add: nth_append last_conv_nth)
        next
          case False
          with SILL have SILL': "Suc i < length p" by simp
              
          with SILL' VNE have X1: "v\<notin>p!i" "v\<notin>p!Suc i" by auto
  
          from p_connected[OF SILL'] obtain a b where 
            "a\<in>p!i" "b\<in>p!Suc i" "(a,b)\<in>vE" by auto 
  
          with \<open>a\<in>p!i\<close> \<open>b\<in>p!Suc i\<close>
          show ?thesis using SILL'
            by (simp add: nth_append; blast) 
        qed
      } note AUX_p_connected = this
  
  
  
      {
        fix U
        assume A: "U \<in> set (p @ [{v}])"
        have "U \<times> U \<subseteq> (insert (u, v) vE \<inter> U \<times> U)\<^sup>*"
        proof cases
          assume "U\<in>set p"
          with p_sc have "U\<times>U \<subseteq> (vE \<inter> U\<times>U)\<^sup>*" .
          thus ?thesis
            by (metis (lifting, no_types) Int_insert_left_if0 Int_insert_left_if1 
              in_mono insert_subset rtrancl_mono_mp subsetI)
        next
          assume "U\<notin>set p" with A have "U={v}" by simp
          thus ?thesis by auto
        qed
      } note AUX_p_sc = this
  
      {
        fix i j
        assume A: "i < j" "j < length (p @ [{v}])"
        have "insert (u, v) vE \<inter> (p @ [{v}]) ! j \<times> (p @ [{v}]) ! i = {}"
        proof (cases "j=length p")
          case False with A have "j<length p" by simp
          from vE_no_back \<open>i<j\<close> this VNE show ?thesis 
            by (auto simp add: nth_append)
        next
          from p_not_D A have PDDJ: "p!i \<inter> D = {}" 
            by (auto simp: Sup_inf_eq_bot_iff)
          case True thus ?thesis
            using A apply (simp add: nth_append)
            apply (rule conjI)
            using UIL A p_disjoint_sym
            apply (metis Misc.last_in_set NE UnionI VNE(1))
  
            using vE_touched VNE PDDJ apply (auto simp: touched_def) []
            done
        qed
      } note AUX_vE_no_back = this
  
      have U_TOUCHED: "u\<in>ltouched"
        using \<open>u\<in>last p\<close> path_touched by fastforce
          
      show ?thesis
        apply unfold_locales
        unfolding defs_fold
  
        subgoal by simp
  
        subgoal using D_incr by auto []
  
        subgoal using vE_ss_E E pE_E_from_p by blast 
  
        subgoal using pE_E_from_p succE_v by (auto dest: in_diffD)
  
        subgoal      
          apply (cases rule: pE_removed_cases)
          using E_from_p_touched VNE succE_v
          by auto
          
        subgoal by (rule D_reachable)
  
        subgoal for i by (rule AUX_p_connected)
          
  
        subgoal using p_disjoint \<open>v\<notin>\<Union>(set p)\<close> by (auto simp: nth_append)
  
        subgoal for U by (rule AUX_p_sc)
  
        subgoal using root_v0 by simp
  
        subgoal by simp
  
        subgoal by (rule D_closed)
  
        subgoal for i j by (rule AUX_vE_no_back)
  
        subgoal using p_not_D VNE by auto
  
        subgoal using D_vis by auto
        subgoal using vE_touched U_TOUCHED by auto
        subgoal
          apply (cases rule: pE_removed_cases)
          using succE_v pE_if_not_visited
          by auto
        subgoal 
          by (simp add: adm_subset_it)
        done
    qed
  
    lemma invar_pE_is_node:
      assumes INV: "invar v0 D0 (p,D,pE,vE)"
      assumes E: "(u,v)\<in>#pE"
      shows "v\<in>E_\<alpha>\<^sup>*``V0"
    proof -
      from INV interpret invar_loc MG V\<^sub>i v0 D0 p D pE unfolding invar_def by simp
      from E pE_reachable show ?thesis by blast
    qed
  
    lemma invar_skip:
      assumes INV: "invar v0 D0 (p,D,pE,vE)"
      assumes NE[simp]: "p\<noteq>[]"
      assumes E: "(u,v)\<in>#pE" and UIL: "u\<in>last p"
      assumes VNP: "v\<notin>\<Union>(set p)" and VD: "v\<in>D"
      shows "invar v0 D0 (p,D,pE - {#(u, v)#}, insert (u,v) vE)"
      unfolding invar_def
      apply simp
    proof -
      from INV interpret invar_loc MG V\<^sub>i v0 D0 p D pE unfolding invar_def by simp
      let ?thesis = "invar_loc MG V\<^sub>i v0 D0 p D (pE - {#(u, v)#}) (insert (u,v) vE)"
  
      note pE_removed_cases = set_mset_subtract_cases[of pE "(u,v)"]
  
      have U_TOUCHED: "u\<in>ltouched"
        using \<open>u\<in>last p\<close> path_touched by fastforce
  
      have V_TOUCHED: "v \<in> ltouched"
        using \<open>v\<in>D\<close> D_touched by blast
  
      show ?thesis
        apply unfold_locales
        
        subgoal by simp
  
        subgoal using D_incr by auto
  
        subgoal using vE_ss_E E pE_E_from_p by blast 
  
        subgoal using pE_E_from_p apply (cases rule:pE_removed_cases) by auto
  
        subgoal using E_from_p_touched VD apply (cases rule:pE_removed_cases) by (auto simp: touched_def)
  
        subgoal by (rule D_reachable)
  
        subgoal using p_connected by auto []
  
        subgoal by (rule p_disjoint)
  
        subgoal 
          apply (drule p_sc)
          apply (erule order_trans)
          apply (rule rtrancl_mono)
          by blast []
  
        subgoal by (rule root_v0)
  
        subgoal by (rule p_empty_v0)
  
        subgoal by (rule D_closed)
  
        subgoal for i j
          using vE_no_back VD p_not_D 
          apply clarsimp
          by (metis Suc_lessD UnionI VNP less_trans_Suc nth_mem)
  
        subgoal by (rule p_not_D)
  
        subgoal using D_vis by auto
        subgoal using vE_touched U_TOUCHED V_TOUCHED by auto
        subgoal
          apply (cases rule: pE_removed_cases)
          using  pE_if_not_visited
          by auto
        subgoal 
          by (simp add: adm_subset_it)
        done
    qed
  
  
    lemma fin_D_is_reachable: 
      \<comment> \<open>When inner loop terminates, all nodes reachable from start node are
        finished\<close>
      assumes INV: "invar v0 D0 ([], D, pE, vE)"
      shows "D \<supseteq> E_\<alpha>\<^sup>*``{v0}"
    proof -
      from INV interpret invar_loc MG V\<^sub>i v0 D0 "[]" D pE vE unfolding invar_def by auto
  
      from p_empty_v0 rtrancl_reachable_induct[OF order_refl D_closed] D_reachable
      show ?thesis by auto
    qed
  
    lemma fin_reachable_path: 
      \<comment> \<open>When inner loop terminates, nodes reachable from start node are
        reachable over visited edges\<close>
      assumes INV: "invar v0 D0 ([], D, pE, vE)"
      assumes UR: "u\<in>E_\<alpha>\<^sup>*``{v0}"
      shows "path vE u q v \<longleftrightarrow> path E_\<alpha> u q v"
    proof -
      from INV interpret invar_loc MG V\<^sub>i v0 D0 "[]" D pE vE unfolding invar_def by auto
      
      show ?thesis
      proof
        assume "path vE u q v"
        thus "path E_\<alpha> u q v" using path_mono[OF vE_ss_E] by blast
      next
        assume "path E_\<alpha> u q v"
        thus "path vE u q v" using UR
        proof induction
          case (path_prepend u v p w)
          with fin_D_is_reachable[OF INV] have "u\<in>D" by auto
          with D_closed \<open>(u,v)\<in>E_\<alpha>\<close> have "v\<in>D" by auto
          from path_prepend.prems path_prepend.hyps have "v\<in>E_\<alpha>\<^sup>*``{v0}" by auto
          with path_prepend.IH fin_D_is_reachable[OF INV] have "path vE v p w" 
            by simp
          moreover from \<open>u\<in>D\<close> \<open>v\<in>D\<close> \<open>(u,v)\<in>E_\<alpha>\<close> D_vis have "(u,v)\<in>vE" by auto
          ultimately show ?case by (auto simp: path_cons_conv)
        qed simp
      qed
    qed
  
    lemma invar_outer_newnode: 
      assumes A: "v0\<notin>D0" "v0\<in>it" 
      assumes OINV: "outer_invar it D0"
      assumes INV: "invar v0 D0 ([],D',pE,vE)"
      shows "outer_invar (it-{v0}) D'"
    proof -
      from OINV interpret outer_invar_loc MG V\<^sub>i it D0 unfolding outer_invar_def .
      from INV interpret inv: invar_loc MG V\<^sub>i v0 D0 "[]" D' pE vE
        unfolding invar_def by simp
      
      from fin_D_is_reachable[OF INV] have [simp]: "v0\<in>D'" by auto
  
      show ?thesis
        unfolding outer_invar_def
        apply unfold_locales
        using it_initial apply auto []
        using it_done inv.D_incr apply auto []
        using inv.D_reachable apply assumption
        using inv.D_closed apply assumption 
        apply (simp add: adm_subset_it)
        done
    qed
  
    lemma invar_outer_Dnode:
      assumes A: "v0\<in>D0"
      assumes OINV: "outer_invar it D0"
      shows "outer_invar (it-{v0}) D0"
    proof -
      from OINV interpret outer_invar_loc MG V\<^sub>i it D0 unfolding outer_invar_def .
      
      show ?thesis
        unfolding outer_invar_def
        apply unfold_locales
        using it_initial apply auto []
        using it_done A apply auto []
        using D_reachable apply assumption
        using D_closed apply assumption
        apply (simp add: adm_subset_it)
        done
    qed
  
    lemma invar_outer_nV0node:
      assumes OINV: "outer_invar it D0"
      assumes A: "v0 \<notin> V0" 
      shows "outer_invar (it - {v0}) D0"
    proof -
      from OINV interpret outer_invar_loc MG V\<^sub>i it D0 unfolding outer_invar_def .
  
      show ?thesis
        unfolding outer_invar_def
        apply unfold_locales
        using it_initial apply auto []
        using it_done A apply auto []
        using D_reachable apply assumption
        using D_closed apply assumption
        apply (simp add: adm_subset_it)
        done
    qed
  
    lemma pE_fin': "invar x \<sigma> ([], D, pE, vE) \<Longrightarrow> pE={#}"
      unfolding invar_def by (simp add: invar_loc.pE_fin)
  
  end
  
  subsubsection \<open>Termination\<close>
  
  text \<open>
    For each branch in our inner loop, we prove that it leads to a lower state with regards to 
    the relation \<open>abs_wf_rel\<close>.
  \<close>
  
  context invar_loc 
  begin
    lemma reachable_finite[simp, intro!]: "finite (reachable_edges v0)"
      \<comment> \<open>The set of unprocessed edges is finite\<close>
    proof -
      have "reachable_edges v0 \<subseteq> E_\<alpha>\<^sup>*``{v0} \<times> E_\<alpha>\<^sup>*``{v0}"
        unfolding reachable_edges_def
        by auto
      thus ?thesis
        by (rule finite_subset) simp
    qed
  
  
    lemma unproc_finite[simp, intro!]: "finite (unproc_edges v0 vE)"
      \<comment> \<open>The set of unprocessed edges is finite\<close>
      unfolding unproc_edges_def
      by auto
  
    lemma pE_reachable_edges: "set_mset pE \<subseteq> reachable_edges v0"
      using pE_reachable pE_E_from_p unfolding reachable_edges_def
      by blast
      
  end
  
  
  context mdp_graph 
  begin
  
  
    lemma abs_wf_pop:
      assumes NE[simp]: "p\<noteq>[]"
      shows "(pop (p,D,pE,vE), (p, D, pE,vE)) \<in> abs_wf_rel v0"
      unfolding pop_def
      by (auto simp: abs_wf_rel_def)
  
    lemma abs_wf_take_edge:
      assumes INV: "invar v0 D0 (p,D,pE,vE)"
      assumes E: "(u,v) \<in># pE" 
      shows "((p',D',pE-{#(u,v)#}, insert(u,v) vE), (p, D, pE, vE))\<in> abs_wf_rel v0"
    proof -
      from INV interpret invar_loc MG V\<^sub>i v0 D0 p D pE unfolding invar_def by simp 
  
      have "size (pE - {#(u,v)#}) < size pE" using E 
        by (simp add: size_Diff1_less)
      then show ?thesis
        using assms
        by (clarsimp simp: abs_wf_rel_def unproc_edges_def)
  
    qed    
  
    lemma abs_wf_collapse:
      assumes INV: "invar v0 D0 (p,D,pE,vE)"
      assumes E: "(u,v)\<in>#pE"
      shows "(collapse v (p,D,pE-{#(u,v)#}, insert(u,v) vE), (p, D, pE, vE))\<in> abs_wf_rel v0"
      using INV E
      unfolding collapse_def
      by (simp add: abs_wf_take_edge)
      
    lemma abs_wf_push:
      assumes INV: "invar v0 D0 (p,D,pE,vE)"
      assumes NE[simp]: "p\<noteq>[]"
      assumes E: "(u,v)\<in>#pE" "u\<in>last p" and A: "v\<notin>D" "v\<notin>\<Union>(set p)"
      shows "push v (p,D,pE-{#(u,v)#},insert (u,v) vE) \<le> SPEC (\<lambda>r. (r, (p, D, pE, vE)) \<in> abs_wf_rel v0)"
      unfolding push_def out_edges_def
      apply refine_vcg
      apply clarsimp
    proof -
      fix succE
      assume succE_v: "set_mset succE = E_\<alpha> \<inter> {v} \<times> UNIV"
  
      from INV interpret invar_loc MG V\<^sub>i v0 D0 p D pE vE unfolding invar_def by simp 
      let ?thesis 
        = "((p@[{v}], D, pE - {#(u, v)#} + succE, insert (u, v) vE), (p, D, pE, vE)) \<in> abs_wf_rel v0"
  
      have "(u,v)\<notin>vE" using vE_touched A unfolding touched_def by blast
      hence "unproc_edges v0 (insert (u,v) vE) \<subset> unproc_edges v0 vE"
        unfolding unproc_edges_def using pE_reachable_edges E by blast
      thus ?thesis
      unfolding abs_wf_rel_def by simp
    qed
  
    lemma abs_wf_skip:
      assumes INV: "invar v0 D0 (p,D,pE,vE)"
      assumes E: "(u,v)\<in>#pE"
      shows "((p, D, pE-{#(u,v)#}, insert (u,v) vE), (p, D, pE, vE)) \<in> abs_wf_rel v0"
      using assms abs_wf_take_edge by simp
  end
  
  subsubsection \<open>Main Correctness Theorem\<close>
  
  context mdp_graph 
  begin
    lemmas invar_preserve = 
      invar_pop invar_skip invar_collapse 
      abs_wf_pop abs_wf_collapse  abs_wf_skip 
      outer_invar_initial invar_outer_newnode invar_outer_Dnode
      invar_outer_nV0node
      invar_pE_is_node
  
  
    lemma invar_rel_push:
      assumes INV: "invar v0 D0 (p,D,pE,vE)"
      assumes NE[simp]: "p\<noteq>[]"
      assumes E: "(u,v)\<in>#pE" and UIL: "u\<in>last p"
      assumes VNE: "v\<notin>\<Union>(set p)" "v\<notin>D"
      shows "push v (p,D,pE - {#(u,v)#}, insert (u,v) vE) \<le> SPEC (\<lambda>r. invar v0 D0 r \<and> (r,(p,D,pE,vE)) \<in> abs_wf_rel v0)"
      apply (rule SPEC_rule_conjI[OF invar_push abs_wf_push])
      by fact+
  
  
    lemmas [refine_vcg] = invar_initial
  
    text \<open>The main correctness theorem for the dummy-algorithm just states that
      it satisfies the invariant when finished, and the path is empty.
  \<close>
    theorem skeleton_spec: "skeleton \<le> SPEC (\<lambda>D. outer_invar {} D)"
    proof -
      note [simp del] = Union_iff
  
      note [refine_vcg del] = WHILEIT_rule
  
      note [simp] = invar_pE_is_node
  
      show ?thesis
        unfolding skeleton_def select_edge_def select_def
        apply (refine_vcg)
        apply (vc_solve solve: invar_preserve simp: pE_fin')
        apply auto
        apply (refine_vcg WHILEIT_rule[OF abs_wf_rel_wf])
        apply (vc_solve solve: invar_preserve simp: pE_fin')
        apply auto
        apply (refine_vcg invar_rel_push)
        done
    qed
  
  end
  
  subsection "Consequences of Invariant when Finished"
  context mdp_graph
  begin
    lemma fin_outer_D_is_reachable:
      \<comment> \<open>When outer loop terminates, exactly the reachable nodes are finished\<close>
      assumes INV: "outer_invar {} D"
      shows "D = E_\<alpha>\<^sup>*``V0"
    proof -
      from INV interpret outer_invar_loc MG V\<^sub>i "{}" D unfolding outer_invar_def by auto
  
      from it_done rtrancl_reachable_induct[OF order_refl D_closed] D_reachable
      show ?thesis by auto
    qed
  
  end
  
  section \<open>Refinement to Gabow's Data Structure\<close>text_raw\<open>\label{sec:algo-ds}\<close>
  
  text \<open>
    The implementation due to Gabow \cite{Gabow2000} represents a path as
    a stack \<open>S\<close> of single nodes, and a stack \<open>B\<close> that contains the
    boundaries of the collapsed segments. Moreover, a map \<open>I\<close> maps nodes
    to their stack indices.
  
    As we use a tail-recursive formulation, we use another stack 
    \<open>P :: ('v digraph) list\<close> to represent the pending edges. The
    entries in \<open>P\<close> are sorted by ascending first component,
    and \<open>P\<close> only contains entries with non-empty second component. 
    An entry \<open>(v,l)\<close> means that the edges from the node \<open>v\<close> to the 
    nodes stored in \<open>l\<close> are pending.
  \<close>
  
  subsection \<open>Preliminaries\<close>
  primrec find_max_nat :: "nat \<Rightarrow> (nat\<Rightarrow>bool) \<Rightarrow> nat" 
    \<comment> \<open>Find the maximum number below an upper bound for which a predicate holds\<close>
    where
    "find_max_nat 0 _ = 0"
  | "find_max_nat (Suc n) P = (if (P n) then n else find_max_nat n P)"
  
  lemma find_max_nat_correct: 
    "\<lbrakk>P 0; 0<u\<rbrakk> \<Longrightarrow> find_max_nat u P = Max {i. i<u \<and> P i}"
    apply (induction u)
    apply auto
  
    apply (rule Max_eqI[THEN sym])
    apply auto [3]
    
    apply (case_tac u)
    apply simp
    apply clarsimp
    by (metis less_SucI less_antisym)
  
  lemma find_max_nat_param[param]:
    assumes "(n,n')\<in>nat_rel"
    assumes "\<And>j j'. \<lbrakk>(j,j')\<in>nat_rel; j'<n'\<rbrakk> \<Longrightarrow> (P j,P' j')\<in>bool_rel"
    shows "(find_max_nat n P,find_max_nat n' P') \<in> nat_rel"
    using assms
    by (induction n arbitrary: n') auto
  
  context begin interpretation autoref_syn .
    lemma find_max_nat_autoref[autoref_rules]:
      assumes "(n,n')\<in>nat_rel"
      assumes "\<And>j j'. \<lbrakk>(j,j')\<in>nat_rel; j'<n'\<rbrakk> \<Longrightarrow> (P j,P'$j')\<in>bool_rel"
      shows "(find_max_nat n P,
          (OP find_max_nat ::: nat_rel \<rightarrow> (nat_rel\<rightarrow>bool_rel) \<rightarrow> nat_rel) $n'$P'
        ) \<in> nat_rel"
      using find_max_nat_param[OF assms]
      by simp
  
  end
  
  
  subsection \<open>Setup for mdp_graph in Gabow's data structure\<close>
  
  subsubsection \<open>Iterator lemmas\<close>
  
  context mdp_graph_defs
  begin

    definition "edges_of_succs = (\<lambda> (u,si). map (\<lambda>v. (u,v)) si)"
  
    lemma set_edges_of_succs_raw: "set (edges_of_succs (u,si)) = {(u,v) | v. v \<in> set si}"
      unfolding edges_of_succs_def by auto
    lemma mset_edges_of_succs_raw[simp]: "mset (edges_of_succs (u,si)) = Pair u `# mset si"
      unfolding edges_of_succs_def by auto
  
    lemma(in mdp_graph) empty_iter_no_successors_begin: "is_empty u \<Longrightarrow> index_begin u \<le> SPEC(\<lambda>(u,si). si = [])"
      unfolding index_begin_def is_empty_def by simp

    lemma(in succ_index_inv) no_next_remaining_successors: "\<not> has_next (ui,si) \<Longrightarrow> si = [successor_at (ui,si)]" 
      unfolding has_next_def successor_at_def using ne_succs 
      by (auto simp: not_less length_Suc_conv) 

    lemma (in succ_index_inv) remaining_successors_succ: 
      assumes VMEM: "v \<in> set si"
      shows "(ui,v) \<in> E_\<alpha>" 
      using assms sub_succs by(force simp: E_\<alpha>_mem) 
    
    lemma (in succ_index_inv) remaining_successors_K: "v \<in> set si \<Longrightarrow> v \<in> E_\<alpha> `` {ui}"
      apply(drule remaining_successors_succ) by blast+
  
    lemma(in succ_index_inv) successor_at_in_remaining_successors[simp, intro!]: "successor_at (ui,si) \<in> set si"
      using ne_succs
      by (auto simp: successor_at_def neq_Nil_conv) 
  
    lemma(in -) singular_upt: "n > 0 \<Longrightarrow> [n-Suc 0..<n] = [n-Suc 0]"
      apply(induction n) by auto

    lemma(in succ_index_inv) successor_at_cons_remaining_successors_eq: "successor_at (ui,si) # (snd (next_index (ui,si))) = si"
      apply(subst list.collapse[symmetric, of si])
      subgoal using ne_succs by auto
      subgoal by (auto simp: successor_at_def next_index_def ne_succs)
      done
  
    lemma fst_next_index: "fst (next_index (u,ci)) = u"
      unfolding next_index_def by (auto split: prod.splits)

    lemma(in succ_index_inv) next_succ_index_inv: assumes HN: "has_next (ui,si)" and NXT: "next_index (ui,si) = (un,sn)" shows "succ_index_inv MG V\<^sub>i (un,sn)"
    proof -
  
      show ?thesis
        apply(unfold_locales)
        subgoal
          using NXT sub_succs
          by(auto simp: next_index_def dest: in_set_tlD)
        subgoal
          using HN NXT unfolding has_next_def next_index_def
          apply (simp flip: length_greater_0_conv) 
          by (metis Suc_le_lessD length_tl nat_le_Suc_less_imp numeral_nat(7))
        done
    qed
  
  end
  
  
  subsection \<open>Gabow's Datastructure\<close>
  
  subsubsection \<open>Definition and Invariant\<close>
  
  definition oGS_\<alpha> :: "'v oGS \<Rightarrow> 'v set" where "oGS_\<alpha> I \<equiv> {v. \<exists> i. I v = Some (DONE i)}"
  
  locale oGS_invar = 
    fixes I :: "'v oGS"
    assumes I_no_stack: "I v \<noteq> Some (STACK j)"
  
  type_synonym 'a GS 
    = "'a list \<times> nat list \<times> ('a \<rightharpoonup> node_state) \<times> ('a succ_index) list"
  locale GS_defs = mdp_graph_defs MG V\<^sub>i for MG :: "'a mdpG" and  V\<^sub>i::"'a set" +
    fixes SBIP :: "'a GS"
  begin
    definition "S \<equiv> (\<lambda>(S,B,I,P). S) SBIP"
    definition "B \<equiv> (\<lambda>(S,B,I,P). B) SBIP"
    definition "I \<equiv> (\<lambda>(S,B,I,P). I) SBIP"
    definition "P \<equiv> (\<lambda>(S,B,I,P). P) SBIP"
  
    definition seg_start :: "nat \<Rightarrow> nat" \<comment> \<open>Start index of segment, inclusive\<close>
      where "seg_start i \<equiv> B!i" 
  
    definition seg_end :: "nat \<Rightarrow> nat"  \<comment> \<open>End index of segment, exclusive\<close>
      where "seg_end i \<equiv> if i+1 = length B then length S else B!(i+1)"
  
    definition seg :: "nat \<Rightarrow> 'a set" \<comment> \<open>Collapsed set at index\<close>
      where "seg i \<equiv> {S!j | j. seg_start i \<le> j \<and> j < seg_end i }"
  
    definition "p_\<alpha> \<equiv> map seg [0..<length B]" \<comment> \<open>Collapsed path\<close>
  
    definition "D_\<alpha> \<equiv> {v. \<exists> i. I v = Some (DONE i)}" \<comment> \<open>Done nodes\<close>
  
    definition "pE_\<alpha> = mset (concat (map (\<lambda> uc. edges_of_succs uc) P))"
  
    lemma set_mset_pE_\<alpha>: "set_mset (pE_\<alpha>) = { (u,v) . \<exists>si. (u,si)\<in>set P \<and> v\<in>set si }"
      unfolding pE_\<alpha>_def edges_of_succs_def
      apply clarsimp
      by fast
  
    definition "\<alpha> \<equiv> (p_\<alpha>,D_\<alpha>,pE_\<alpha>)" \<comment> \<open>Abstract state\<close>
  
    lemma D_\<alpha>_alt_def:  "D_\<alpha> = oGS_\<alpha> I" unfolding D_\<alpha>_def oGS_\<alpha>_def by simp
  
  end
  
  lemma GS_sel_simps[simp]:
    "GS_defs.S (S,B,I,P) = S"
    "GS_defs.B (S,B,I,P) = B"
    "GS_defs.I (S,B,I,P) = I"
    "GS_defs.P (S,B,I,P) = P"
    unfolding GS_defs.S_def GS_defs.B_def GS_defs.I_def GS_defs.P_def
    by auto
  
  
  lemma GS_sel_id: "s = (GS_defs.S s, GS_defs.B s, GS_defs.I s, GS_defs.P s)"
    unfolding GS_defs.S_def GS_defs.B_def GS_defs.I_def GS_defs.P_def
    by(auto split: prod.split)
  
  lemma GS_selI:
    "x = (S,B,I,P) \<Longrightarrow> GS_defs.S x = S"
    "x = (S,B,I,P) \<Longrightarrow> GS_defs.B x = B"
    "x = (S,B,I,P) \<Longrightarrow> GS_defs.I x = I"
    "x = (S,B,I,P) \<Longrightarrow> GS_defs.P x = P"
    unfolding GS_defs.S_def GS_defs.B_def GS_defs.I_def GS_defs.P_def
    by auto
    
  
  context GS_defs begin
    lemma seg_start_indep[simp]: "GS_defs.seg_start (S',B,I',P') = seg_start"  
      unfolding GS_defs.seg_start_def[abs_def] by (auto)
    lemma seg_end_indep[simp]: "GS_defs.seg_end (S,B,I',P') = seg_end"  
      unfolding GS_defs.seg_end_def[abs_def] by auto
    lemma seg_indep[simp]: "GS_defs.seg (S,B,I',P') = seg"  
      unfolding GS_defs.seg_def[abs_def] by auto
    lemma p_\<alpha>_indep[simp]: "GS_defs.p_\<alpha> (S,B,I',P') = p_\<alpha>"
      unfolding GS_defs.p_\<alpha>_def by auto
  
    lemma D_\<alpha>_indep[simp]: "GS_defs.D_\<alpha> (S',B',I,P') = D_\<alpha>"
      unfolding GS_defs.D_\<alpha>_def by auto
  
    lemma pE_\<alpha>_indep[simp]: "GS_defs.pE_\<alpha> (S',B',I',P) = pE_\<alpha>" 
      unfolding GS_defs.pE_\<alpha>_def by auto
  
    definition find_seg \<comment> \<open>Abs-path index for stack index\<close>
      where "find_seg j \<equiv> Max {i. i<length B \<and> B!i\<le>j}"
  
    definition S_idx_of \<comment> \<open>Stack index for node\<close>
      where "S_idx_of v \<equiv> val (the (I v))"
  
    lemma S_idx_of_indep[simp]: "GS_defs.S_idx_of (S', B', I, P') = S_idx_of"
      unfolding GS_defs.S_idx_of_def by simp
  
    lemma p_\<alpha>_B_empty: "p_\<alpha> \<noteq> [] \<longleftrightarrow> B \<noteq> []"
      unfolding p_\<alpha>_def
      by simp
  
    lemma seg_start_last: "B \<noteq> [] \<Longrightarrow> seg_start (length B - 1) = last B"
      unfolding seg_start_def
      apply(auto simp: last_conv_nth)
      done
  
    lemma seg_end_last: "B \<noteq> [] \<Longrightarrow> seg_end (length B - 1) = length S"
      unfolding seg_end_def
      by simp
  
    lemma S_idx_of_upd[simp]: "GS_defs.S_idx_of (S', B', I(v \<mapsto> STACK n), P') = (S_idx_of(v := n))"
      unfolding GS_defs.S_idx_of_def by auto
  
  end
  
  locale GS = GS_defs MG V\<^sub>i SBIP + mdp_graph MG V\<^sub>i for MG V\<^sub>i SBIP
  
  locale GS_invar = GS +
    
    assumes B_in_bound: "set B \<subseteq> {0..<length S}"
    assumes B_sorted: "sorted B"
    assumes B_distinct: "distinct B"
    assumes B0: "S\<noteq>[] \<Longrightarrow> B\<noteq>[] \<and> B!0=0"
    assumes S_distinct: "distinct S"
  
    assumes I_consistent: "(I v = Some (STACK j)) \<longleftrightarrow> (j<length S \<and> v = S!j)"
    
    assumes P_sorted: "sorted (map (S_idx_of o fst) P)"
    assumes P_bound: "set P \<subseteq> {(u,si). u \<in> set S \<and> succ_index_inv MG V\<^sub>i (u,si) \<and> set si \<subseteq> E_\<alpha> `` {u}}"
    assumes P_distinct: "distinct (map fst P)"
  
    assumes S_subset_nodes: "set S \<subseteq> (E_\<alpha>\<^sup>* `` V0)"
  begin
    lemma locale_this: "GS_invar MG V\<^sub>i SBIP" by unfold_locales
    
  
    lemma S_length_nodes: "length S \<le> card (E_\<alpha>\<^sup>* `` V0)"
      by (metis S_distinct S_subset_nodes card_mono distinct_card finite_reachableE_V0)
  
    lemma B_length_nodes: "length B \<le> card (E_\<alpha>\<^sup>* `` V0)"
      using distinct_card[OF B_distinct, symmetric] card_mono[OF _  B_in_bound] S_length_nodes
      by auto
  
    lemma P_length_nodes: "length P \<le> card (E_\<alpha>\<^sup>* `` V0)"
    proof -
      have "length P = length (map fst P)" by simp
      also have "length (map fst P) = card (fst ` set P)" using distinct_card[OF P_distinct, symmetric] by simp
      also have "\<dots> \<le> card (set S)" using P_bound
        by (fastforce intro: card_mono)
      also have "... = length S" using distinct_card[OF S_distinct] .
      also have "... \<le> card (E_\<alpha>\<^sup>* `` V0)" using S_length_nodes .
      finally show ?thesis .
    qed
  
  
  
  end
  
  
  
  
  context mdp_graph begin
  
  definition "oGS_rel \<equiv> br oGS_\<alpha> oGS_invar"
  lemma oGS_rel_sv[intro!,simp,relator_props]: "single_valued oGS_rel"
    unfolding oGS_rel_def by auto
  
  
  definition GS_rel :: "('v GS \<times> 'v abs_state) set"
    where "GS_rel \<equiv> { (c,(p,D,pE,vE)) . (c,(p,D,pE)) \<in> br (GS_defs.\<alpha>) (GS_invar MG V\<^sub>i) }"
  
  end
  
  context GS_invar
  begin
    lemma empty_eq: "S=[] \<longleftrightarrow> B=[]"
      using B_in_bound B0 by auto
  
    lemma B_in_bound': "i<length B \<Longrightarrow> B!i < length S"
      using B_in_bound nth_mem by fastforce
  
    lemma seg_start_bound:
      assumes A: "i<length B" shows "seg_start i < length S"
      using B_in_bound nth_mem[OF A] unfolding seg_start_def by auto
  
    lemma seg_end_bound:
      assumes A: "i<length B" shows "seg_end i \<le> length S"
    proof (cases "i+1=length B")
      case True thus ?thesis by (simp add: seg_end_def)
    next
      case False with A have "i+1<length B" by simp
      from nth_mem[OF this] B_in_bound have " B ! (i + 1) < length S" by auto
      thus ?thesis using False by (simp add: seg_end_def)
    qed
  
    lemma seg_start_less_end: "i<length B \<Longrightarrow> seg_start i < seg_end i"
      unfolding seg_start_def seg_end_def
      using B_in_bound' distinct_sorted_mono[OF B_sorted B_distinct]
      by auto
  
    lemma seg_end_less_start: "\<lbrakk>i<j; j<length B\<rbrakk> \<Longrightarrow> seg_end i \<le> seg_start j"
      unfolding seg_start_def seg_end_def
      by (auto simp: distinct_sorted_mono_iff[OF B_distinct B_sorted])
  
    lemma find_seg_bounds:
      assumes A: "j<length S"
      shows "seg_start (find_seg j) \<le> j" 
      and "j < seg_end (find_seg j)" 
      and "find_seg j < length B"
    proof -
      let ?M = "{i. i<length B \<and> B!i\<le>j}"
      from A have [simp]: "B\<noteq>[]" using empty_eq by (cases S) auto
      have NE: "?M\<noteq>{}" using A B0 by (cases B) auto
  
      have F: "finite ?M" by auto
      
      from Max_in[OF F NE]
      have LEN: "find_seg j < length B" and LB: "B!find_seg j \<le> j"
        unfolding find_seg_def
        by auto
  
      thus "find_seg j < length B" by -
      
      from LB show LB': "seg_start (find_seg j) \<le> j"
        unfolding seg_start_def by simp
  
      moreover show UB': "j < seg_end (find_seg j)"
        unfolding seg_end_def 
      proof (split if_split, intro impI conjI)
        show "j<length S" using A .
        
        assume "find_seg j + 1 \<noteq> length B" 
        with LEN have P1: "find_seg j + 1 < length B" by simp
  
        show "j < B ! (find_seg j + 1)"
        proof (rule ccontr, simp only: linorder_not_less)
          assume P2: "B ! (find_seg j + 1) \<le> j"
          with P1 Max_ge[OF F, of "find_seg j + 1", folded find_seg_def]
          show False by simp
        qed
      qed
    qed
      
    lemma find_seg_correct:
      assumes A: "j<length S"
      shows "S!j \<in> seg (find_seg j)" and "find_seg j < length B"
      using find_seg_bounds[OF A]
        unfolding seg_def by auto
  
    lemma set_p_\<alpha>_is_set_S:
      "\<Union>(set p_\<alpha>) = set S"
      apply rule
      unfolding p_\<alpha>_def seg_def[abs_def]
      using seg_end_bound apply fastforce []
  
      apply (auto simp: in_set_conv_nth)
  
      using find_seg_bounds
      apply (fastforce simp: in_set_conv_nth)
      done
  
    lemma last_p_\<alpha>_alt_def: "p_\<alpha> \<noteq> [] \<Longrightarrow> last p_\<alpha> = {S ! j |j. last B \<le> j \<and> j < length S}"
      unfolding p_\<alpha>_def seg_def seg_start_def seg_end_def
      apply(simp add: last_map last_conv_nth)
      done
  
    lemma last_p_\<alpha>_drop_B: "p_\<alpha> \<noteq> [] \<Longrightarrow> last p_\<alpha> = set (drop (last B) S)" 
      using set_drop_conv last_p_\<alpha>_alt_def 
      by fast
  
    lemma S_idx_uniq: 
      "\<lbrakk>i<length S; j<length S\<rbrakk> \<Longrightarrow> S!i=S!j \<longleftrightarrow> i=j"
      using S_distinct
      by (simp add: nth_eq_iff_index_eq)
  
    lemma S_idx_of_correct: 
      assumes A: "v\<in>\<Union>(set p_\<alpha>)"
      shows "S_idx_of v < length S" and "S!S_idx_of v = v"
    proof -
      from A have "v\<in>set S" by (simp add: set_p_\<alpha>_is_set_S)
      then obtain j where G1: "j<length S" "v=S!j" by (auto simp: in_set_conv_nth)
      with I_consistent have "I v = Some (STACK j)" by simp
      hence "S_idx_of v = j" by (simp add: S_idx_of_def)
      with G1 show "S_idx_of v < length S" and "S!S_idx_of v = v" by simp_all
    qed
  
    lemma p_\<alpha>_disjoint_sym: 
      shows "\<forall>i j v. i<length p_\<alpha> \<and> j<length p_\<alpha> \<and> v\<in>p_\<alpha>!i \<and> v\<in>p_\<alpha>!j \<longrightarrow> i=j"
    proof (intro allI impI, elim conjE)
      fix i j v
      assume A: "i < length p_\<alpha>" "j < length p_\<alpha>" "v \<in> p_\<alpha> ! i" "v \<in> p_\<alpha> ! j"
      from A have LI: "i<length B" and LJ: "j<length B" by (simp_all add: p_\<alpha>_def)
  
      from A have B1: "seg_start j < seg_end i" and B2: "seg_start i < seg_end j"
        unfolding p_\<alpha>_def seg_def[abs_def]
        apply clarsimp_all
        apply (subst (asm) S_idx_uniq)
        apply (metis dual_order.strict_trans1 seg_end_bound)
        apply (metis dual_order.strict_trans1 seg_end_bound)
        apply simp
        apply (subst (asm) S_idx_uniq)
        apply (metis dual_order.strict_trans1 seg_end_bound)
        apply (metis dual_order.strict_trans1 seg_end_bound)
        apply simp
        done
  
      from B1 have B1: "(B!j < B!Suc i \<and> Suc i < length B) \<or> i=length B - 1"
        using LI unfolding seg_start_def seg_end_def by (auto split: if_split_asm)
  
      from B2 have B2: "(B!i < B!Suc j \<and> Suc j < length B) \<or> j=length B - 1"
        using LJ unfolding seg_start_def seg_end_def by (auto split: if_split_asm)
  
      from B1 have B1: "j<Suc i \<or> i=length B - 1"
        using LI LJ distinct_sorted_strict_mono_iff[OF B_distinct B_sorted]
        by auto
  
      from B2 have B2: "i<Suc j \<or> j=length B - 1"
        using LI LJ distinct_sorted_strict_mono_iff[OF B_distinct B_sorted]
        by auto
  
      from B1 B2 show "i=j"
        using LI LJ
        by auto
    qed
  
  end
  
  
  subsection \<open>Refinement of the Operations\<close>
  
    definition(in mdp_graph) GS_initial_impl :: "'v oGS \<Rightarrow> 'v \<Rightarrow> 'v GS nres" where
    "GS_initial_impl I v0  \<equiv> do{
      cl \<leftarrow> (if is_empty v0 then RETURN [] else do{ ci \<leftarrow> index_begin v0; RETURN [ci]});
      RETURN (
      [v0],
      [0],
      I(v0\<mapsto>(STACK 0)),
      cl)}"
  
    definition mark_as_done 
      where "mark_as_done S I l u i \<equiv> do {
      (_,I)\<leftarrow>WHILET 
        (\<lambda>(l,I). l<u) 
        (\<lambda>(l,I). do { ASSERT (l<length S); RETURN (Suc l,I(S!l \<mapsto> DONE i))}) 
        (l,I);
      RETURN I
    }"
    sepref_register mark_as_done :: "'a list \<Rightarrow> (('a, node_state) i_map) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (('a, node_state) i_map) nres"
  
    definition open_GS :: "'a GS \<Rightarrow> 'a GS" where "open_GS s = (case s of (S,B,I,P) \<Rightarrow> (S,B,I,P))"
    sepref_register open_GS :: "'a list \<times> nat list \<times> ('a \<Rightarrow> node_state option) \<times> ('a \<times> 'a list) list
       \<Rightarrow> 'a list \<times> nat list \<times> (('a, node_state) i_map) \<times> ('a \<times> 'a list) list"
  
    definition close_GS :: "'a list \<Rightarrow> nat list \<Rightarrow> ('a \<rightharpoonup> node_state) \<Rightarrow> ('a \<times> 'a list) list \<Rightarrow> 'a GS" 
      where "close_GS S B I P = (S,B,I,P)"
    sepref_register close_GS :: "'a list \<Rightarrow> nat list \<Rightarrow> (('a, node_state) i_map) \<Rightarrow> ('a \<times> 'a list) list
       \<Rightarrow> 'a list \<times> nat list \<times> ('a \<Rightarrow> node_state option) \<times> ('a \<times> 'a list) list"
  
  context GS_defs
  begin
    definition "push_impl v \<equiv> do{ 
      ASSERT(length S < card(E_\<alpha>\<^sup>*``V0));
      ASSERT(length B < card(E_\<alpha>\<^sup>*``V0));
      ASSERT(length P < card(E_\<alpha>\<^sup>*``V0));
      let j = length S;
      let S = S@[v];
      let B = B@[j];
      let I = I(v \<mapsto> STACK j);
      P \<leftarrow> (if is_empty v then 
        RETURN P 
      else do{
        ci \<leftarrow> index_begin v;
        RETURN (P @ [ci])
      });
      RETURN (S,B,I,P)
    }"
  
    definition mark_as_done_abs where
      "\<And>l u I i. mark_as_done_abs l u I i
      \<equiv> (\<lambda>v. if v\<in>{S!j | j. l\<le>j \<and> j<u} then Some (DONE i) else I v)"
  
    lemma mark_as_done_aux:
      fixes I l u i
      shows "\<lbrakk>l<u; u\<le>length S\<rbrakk> \<Longrightarrow> mark_as_done S I l u i
      \<le> SPEC (\<lambda>r. r = mark_as_done_abs l u I i)"
      unfolding mark_as_done_def mark_as_done_abs_def
      apply (refine_rcg 
        WHILET_rule[where 
          I="\<lambda>(l',I'). 
            (I' = (\<lambda>v. if v\<in>{S!j | j. l\<le>j \<and> j<l'} then Some (DONE i) else I v))
            \<and> l\<le>l' \<and> l'\<le>u"
          and R="measure (\<lambda>(l',_). u-l')" 
        ]
        refine_vcg)
      
      apply (auto del: ext intro!: ext simp: less_Suc_eq)
      done    
  
    definition "pop_impl i \<equiv> 
      do {
        ASSERT (length B \<ge> 1);
        let lsi = length B - 1;
        ASSERT (lsi<length B);
        let l = (seg_start lsi);
        let u = (seg_end lsi);
        I \<leftarrow> mark_as_done S I l u i;
        ASSERT (B\<noteq>[]);
        S \<leftarrow> mop_list_take (last B) S;
        ASSERT (B\<noteq>[]);
        let B = butlast B;
        RETURN (S,B,I,P)
      }"
      
      
  
    definition "sel_rem_last \<equiv> 
      if P=[] then 
        RETURN (None,(S,B,I,P))
      else do {
        let ((v,si), P') = op_list_pop_last P;
        ASSERT (\<exists>j. I v = Some (STACK j));
        ASSERT (length B \<ge> 1);
        if S_idx_of v \<ge> seg_start (length B - 1) then do {
          ASSERT (succ_index_inv MG V\<^sub>i (v,si));
          let w = successor_at (v,si);
          let P = (if has_next (v,si) then op_list_append P' (next_index (v,si)) else P');
          RETURN (Some w,(S,B,I,P))
        } else RETURN (None,(S,B,I,P))
      }"
  
  
    definition "find_seg_impl' j \<equiv> find_max_nat (length B) (\<lambda>i. B!i\<le>j)"
  
    definition "find_seg_impl j = do {
      ASSERT(length B \<ge> 1);
      (i)\<leftarrow>WHILEIT
        (\<lambda>i. i < length B \<and> (\<forall>k . i < k & k < length B \<longrightarrow> B!k > j)) 
        (\<lambda>i. B!i > j) 
        (\<lambda>i. do { ASSERT (i \<ge> 1); RETURN (i - 1)}) 
        (length B - 1);
      RETURN i
    }"
  
  
    lemma(in GS_invar) "S \<noteq> [] \<Longrightarrow> {i. i < length B \<and> B ! i \<le> j} \<noteq> {}"
      using B0 by force
  
    lemma s_max_j_in_X:
      assumes SIN: "X \<noteq> []"
          and SORT: "sorted X"
          and JBOUND: "j \<ge> X ! s"
          and SLEN: "s < length X" 
          and SSMALL: "\<forall>k. s < k \<and> k < length X \<longrightarrow> j < X ! k"
        shows "s = Max {i. i < length X \<and> X ! i \<le> j}"
    proof -
      define s2 where "s2 \<equiv> Max {i. i < length X \<and> X ! i \<le> j}"
      have FIN:  "finite {i. i < length X \<and> X ! i \<le> j}" by fast
      hence NEMP: "{i. i < length X \<and> X ! i \<le> j} \<noteq> {}" using SIN SLEN JBOUND by fast
      have S2LEN: "s2 < length X" using s2_def FIN NEMP by force
      have L: "s2 \<le> s"
      proof(rule ccontr)
        assume "\<not> s2 \<le> s"
        hence "s2 > s" by force
        moreover have "s2 < length X" using s2_def FIN NEMP by force
        ultimately have "j < X ! s2" using SSMALL by blast
        thus False using s2_def eq_Max_iff[OF FIN NEMP, of s2] by force
      qed
  
      moreover have "s \<le> s2" using Max_ge[OF FIN] s2_def by (simp add: JBOUND SLEN)
      ultimately show ?thesis using s2_def by fastforce
    qed
  
  
    lemma (in GS_invar) find_seg_impl_aux:
      fixes j
      shows "j<length S \<Longrightarrow> find_seg_impl j 
      \<le> SPEC (\<lambda>r. r = find_seg j)"
      unfolding find_seg_impl_def find_seg_def
      apply (refine_rcg 
        WHILEIT_rule[where R="measure (\<lambda>i. i)" 
        ]
        refine_vcg)
      
      apply (auto simp: B0) 
      subgoal for s 
        apply(cases "s = 0")
        apply (auto simp: B0) 
        done
      subgoal for s k apply(cases "s = k")
        apply fast
        apply simp
        done          
      apply(rule s_max_j_in_X)
      apply(auto simp: B_sorted)
      done
      
  
    definition "idx_of_impl v \<equiv> do {
        ASSERT (\<exists> j. I v = Some (STACK j));
        let j = S_idx_of v;
        ASSERT (j<length S);
        i \<leftarrow> find_seg_impl j;
        RETURN i
      }"
  
  
    definition "collapse_impl v \<equiv> 
      do { 
        i\<leftarrow>idx_of_impl v;
        ASSERT (i+1 \<le> length B);
        let B = take (i+1) B;
        RETURN (S,B,I,P)
      }"
  
  end
  
  lemma (in mdp_graph) GS_initial_correct: 
    assumes REL: "(I,D)\<in>oGS_rel"
    assumes A: "v0\<notin>D"
    assumes REACH: "v0 \<in> V0"
    shows "GS_initial_impl I v0 \<le> SPEC(\<lambda> SBIP. GS_invar MG V\<^sub>i SBIP \<and> (\<exists> si. set si = K v0 \<and> GS_defs.\<alpha> SBIP = ([{v0}],D,mset (edges_of_succs (v0, si)))))"
  proof -
    from REL have [simp]: "D = oGS_\<alpha> I" and I: "oGS_invar I"
      by (simp_all add: oGS_rel_def br_def)
  
    then interpret oGS_invar I by blast
  
    from I have [simp]: "\<And>j v. I v \<noteq> Some (STACK j)"
      by (simp add: oGS_invar_def mdp_graph_axioms)
  
    {
      fix v s b
      assume A: "\<not> is_empty v" "v0 = v" "set b = successors_of v"
  
      have INV: "succ_index_inv MG V\<^sub>i (v, b)"
        apply(unfold_locales)
        subgoal using A(3) by auto
        subgoal using A(1) A(3) by (auto simp: is_empty_def)
        done 
  
      have "GS_invar MG V\<^sub>i ([v], [0], I(v \<mapsto> STACK 0), [(v, b)])"
        apply(unfold_locales)
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal 
          by (auto simp: is_empty_def in_set_conv_nth INV E_\<alpha>_mem A(3) dest!:  
            simp flip: index_begin_def) 
        subgoal by auto
        subgoal by (auto simp: REACH simp flip: A(2))
        done 
    } note INV = this
  
    show ?thesis
      unfolding GS_defs.\<alpha>_def GS_initial_impl_def edges_of_succs_def
      apply(refine_vcg)
      subgoal 
        apply unfold_locales
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal 
          by (auto simp: is_empty_def in_set_conv_nth dest!:  
            simp flip: index_begin_def)
        subgoal by auto
        subgoal by (auto simp: REACH)
        done
  
      subgoal
        apply (simp split del: if_split)
    
        unfolding GS_defs.p_\<alpha>_def GS_defs.seg_def[abs_def] GS_defs.seg_start_def GS_defs.seg_end_def
        apply (auto) []
    
        using A unfolding GS_defs.D_\<alpha>_def apply (auto simp: oGS_\<alpha>_def) []
    
        unfolding GS_defs.pE_\<alpha>_def by(auto simp: is_empty_def split: prod.split) 
  
      subgoal
        unfolding index_begin_def 
        unfolding GS_defs.p_\<alpha>_def GS_defs.seg_def[abs_def] GS_defs.seg_start_def GS_defs.seg_end_def
        unfolding GS_defs.D_\<alpha>_def
        unfolding GS_defs.pE_\<alpha>_def
        using assms(2) by (auto simp: INV oGS_\<alpha>_def ) 
      done
  qed

  context GS_invar
  begin
  
  
    lemma push_impl_core_correct:
      assumes A: "v\<notin>\<Union>(set p_\<alpha>)" and B: "v\<notin>D_\<alpha>" and REACH: "v \<in> E_\<alpha>\<^sup>* `` V0"
      assumes LS: "length S < card (E_\<alpha>\<^sup>* `` V0)"
      assumes LB: "length B < card (E_\<alpha>\<^sup>* `` V0)"
      assumes LP: "length P < card (E_\<alpha>\<^sup>* `` V0)"
      shows "push_impl v \<le> SPEC (\<lambda> SBIP. GS_invar MG V\<^sub>i SBIP \<and> (\<exists> si. set si = K v \<and> GS_defs.\<alpha> SBIP = (p_\<alpha>@[{v}],D_\<alpha>,pE_\<alpha> + mset (edges_of_succs (v,si)))))" 
    proof -
  
      note [simp] = Let_def
  
      have VNP: "v \<notin> set (map fst P)"
      proof(rule notI)
        assume "v \<in> set (map fst P)"
        hence "v \<in> set S" using P_bound by auto
        hence "v \<in> \<Union> (set p_\<alpha>)" using set_p_\<alpha>_is_set_S by blast
        with A show False by blast
      qed
  
      have iexI: "\<And>a b j P. \<lbrakk>a!j = b!j; P j\<rbrakk> \<Longrightarrow> \<exists>j'. a!j = b!j' \<and> P j'"
        by blast
  
      have Ap: "GS_defs.p_\<alpha> (S @ [v], B @ [length S], I(v \<mapsto> STACK (length S)), P @ xs) = p_\<alpha> @ [{v}]" for xs
        unfolding  GS_defs.p_\<alpha>_def GS_defs.seg_def[abs_def] 
          GS_defs.seg_start_def GS_defs.seg_end_def
        apply (clarsimp split del: if_split)
  
        apply clarsimp
        apply safe
        apply (((rule iexI)?, 
          (auto  
            simp: nth_append nat_in_between_eq 
            dest: order.strict_trans[OF _ B_in_bound']
          )) []
        ) +
        done
  
      {
        fix b
        assume B: "\<not> is_empty v" "set b = successors_of v"
  
        have INV: "succ_index_inv MG V\<^sub>i (v, b)"
          apply(unfold_locales)
          using B
          by (auto simp: is_empty_def)
  
        have "GS_invar MG V\<^sub>i (S @ [v], B @ [length S], I(v \<mapsto> STACK (length S)), P @ [(v, b)])"
          apply unfold_locales
    
          subgoal using B_in_bound by (auto simp: sorted_append)
          subgoal using B_in_bound B_sorted by (auto simp: sorted_append)
          subgoal using B_in_bound B_distinct by (auto simp: sorted_append)
    
          subgoal using B_in_bound B0 apply (cases S) by (auto simp: nth_append)
          subgoal using S_distinct A set_p_\<alpha>_is_set_S by simp
    
          subgoal using A I_consistent by (auto simp: nth_append set_p_\<alpha>_is_set_S  split: if_split_asm) []
    
          subgoal using P_sorted 
            by (clarsimp simp: map_fun_upd[OF VNP, unfolded map_map] sorted_append 
              dest!: mp[OF P_bound[THEN in_mono]] S_idx_of_correct(1)[unfolded set_p_\<alpha>_is_set_S]) 
    
          subgoal using P_bound INV E_\<alpha>_mem B(2) by auto
    
          subgoal using P_distinct VNP by (auto)
    
          subgoal using S_subset_nodes REACH by auto
    
          done
      } note INV = this
  
      show ?thesis
        unfolding push_impl_def  GS_defs.\<alpha>_def
        apply refine_vcg 
        subgoal by(rule LS)
        subgoal by(rule LB)
        subgoal by(rule LP)
        subgoal
          apply unfold_locales
    
          subgoal using B_in_bound by (auto simp: sorted_append)
          subgoal using B_in_bound B_sorted by (auto simp: sorted_append)
          subgoal using B_in_bound B_distinct by (auto simp: sorted_append)
    
          subgoal using B_in_bound B0 apply (cases S) by (auto simp: nth_append)
          subgoal using S_distinct A set_p_\<alpha>_is_set_S by simp
    
          subgoal using A I_consistent by (auto simp: nth_append set_p_\<alpha>_is_set_S  split: if_split_asm) []
    
          subgoal using P_sorted 
            by (clarsimp simp: map_fun_upd[OF VNP, unfolded map_map] sorted_append 
              dest!: mp[OF P_bound[THEN in_mono]] S_idx_of_correct(1)[unfolded set_p_\<alpha>_is_set_S]) 
    
          subgoal using P_bound by(auto) 
    
          subgoal using P_distinct VNP by (auto)
    
          subgoal using S_subset_nodes REACH by auto
    
          done
        subgoal
          using B unfolding GS_defs.D_\<alpha>_def
          by (auto simp: is_empty_def Ap[of "[]", simplified])
        subgoal
          unfolding index_begin_def
          apply (clarsimp simp: INV ) 
          subgoal for si'
            apply(rule exI[where ?x=si'])
            using B unfolding GS_defs.D_\<alpha>_def GS_defs.pE_\<alpha>_def
            by (auto simp: le_less_Suc_eq Ap)
          done
        done
  
    qed
  
  
    lemma no_last_out_P_aux':
      assumes NE: "p_\<alpha>\<noteq>[]" and NS: "set_mset pE_\<alpha> \<inter> last p_\<alpha> \<times> UNIV = {}"
      shows "set P \<subseteq> {(u,si). u \<in> set (take (last B) S) \<and> succ_index_inv MG V\<^sub>i (u, si) \<and> set si \<subseteq> E_\<alpha> `` {u}}"
    proof
      fix x
      assume XP: "x \<in> set P"
      then obtain v si where XDEF: "x = (v,si)" and VS: "v \<in> set S" 
        and INV: "succ_index_inv MG V\<^sub>i (v,si)" and CC: "set si \<subseteq> E_\<alpha> `` {v}"
        using P_bound by blast
      then interpret succ_index_inv MG V\<^sub>i "(v,si)" by blast
  
      obtain w where "w \<in> set si" using ne_succs
        by auto
      then have "(v,w) \<in># pE_\<alpha>" unfolding pE_\<alpha>_def edges_of_succs_def
        using XP XDEF apply clarsimp
        apply(rule bexI[where ?x="(v,si)"])
        by blast+
      hence "v \<notin> last p_\<alpha>" using NE NS by blast
      hence "v \<notin> set (drop (last B) S)" using last_p_\<alpha>_drop_B[OF NE] by blast
      moreover have "v \<in> set (take (last B) S) \<union> set (drop (last B) S)" using VS append_take_drop_id
        by (simp add: set_union_code)
      ultimately have "v \<in> set (take (last B) S)" by blast
      thus "x \<in> {(u, si). u \<in> set (take (last B) S) \<and> succ_index_inv MG V\<^sub>i (u, si) 
        \<and> set si \<subseteq> E_\<alpha> `` {u}}" 
        using CC XDEF INV successor_at_E_\<alpha> 
        by (auto intro!: remaining_successors_K[simplified])
    qed
  
  
    lemma map_update_snd_keeps_fst: "P ! n = (a,b) \<Longrightarrow> map fst (P[n := (a, b')]) = map fst P"
      by (metis fst_conv list_update_id map_update)
  
  
    lemma no_last_out_P_aux:
      assumes NE: "p_\<alpha>\<noteq>[]" and NS: "set_mset pE_\<alpha> \<inter> last p_\<alpha> \<times> UNIV = {}"
      shows "set (map (S_idx_of o fst) P) \<subseteq> {0..<last B}"
    proof -
      {
        fix v si
        assume jII: "(v,si)\<in>set P"
          and JL: "last B \<le> S_idx_of v"
        with P_bound have VPA: "v \<in> \<Union> (set p_\<alpha>)" and INV: "succ_index_inv MG V\<^sub>i (v,si)" by(auto simp: set_p_\<alpha>_is_set_S)
        then interpret succ_index_inv MG V\<^sub>i "(v,si)" by blast
  
        from VPA have JU: "S_idx_of v < length S" 
          using S_idx_of_correct(1) by blast
        with JL JU have "S!(S_idx_of v) \<in> last p_\<alpha>"
          using NE
          unfolding p_\<alpha>_def 
          apply (auto 
            simp: last_map seg_def seg_start_def seg_end_def last_conv_nth) 
          done
        hence "v \<in> last p_\<alpha>" using S_idx_of_correct(2)[OF VPA] by auto
        moreover from jII have "set (edges_of_succs (v,si)) \<subseteq> set_mset pE_\<alpha>" unfolding pE_\<alpha>_def 
          apply clarsimp
          apply(rule bexI[where ?x="(v,si)"])
          apply blast
          by assumption
        moreover note NS
        ultimately have False unfolding edges_of_succs_def using ne_succs
          by auto
      } thus ?thesis by fastforce
    qed
  
    lemma sorted_after_pop:
    fixes i
    assumes BNE: "B \<noteq> []"
    assumes PS: "set P \<subseteq> {(u,si). u \<in> set (take (last B) S) \<and> succ_index_inv MG V\<^sub>i (u, si)}"
    defines "S'\<equiv> take (last B) S"
    defines "B'\<equiv> butlast B"
    defines "I' \<equiv> mark_as_done_abs (seg_start (length B - Suc 0)) (seg_end (length B - Suc 0)) I i"
      shows "sorted (map (GS_defs.S_idx_of (S', B', I', P) \<circ> fst) P)"
    proof (cases P)
      case Nil
      then show ?thesis by simp
    next
      case (Cons a x)
  
      {
        fix p 
        assume P_MEM: "p \<in> set (map fst P)"
        hence P_MEM2: "p \<in> set (take (last B) S)" using PS by auto
        then obtain j where "p = (take (last B) S) ! j" and "j < last B" by(auto simp: in_set_conv_nth)
        hence "p \<notin> {S ! j |j. last B \<le> j \<and> j < length S}" using P_distinct S_distinct
          by(auto simp: nth_eq_iff_index_eq)
        hence EQ: "I' p = I p" unfolding I'_def mark_as_done_abs_def 
          seg_start_last[OF BNE, simplified] seg_end_last[OF BNE, simplified] by argo
      } note I'_to_I = this
      hence "\<forall>p2 \<in> set (map fst P). I' p2 = I p2" by blast
      hence "map (GS_defs.S_idx_of (S', B', I', P) \<circ> fst) P = map (GS_defs.S_idx_of (S', B', I, P) \<circ> fst) P" 
        unfolding GS_defs.S_idx_of_def GS_defs.I_def by force
      also have "... = map (S_idx_of \<circ> fst) P" unfolding S_idx_of_indep by simp
      finally show ?thesis using P_sorted by presburger
    qed
  
    lemma pop_correct:
      assumes NE: "p_\<alpha>\<noteq>[]" and NS: "set_mset pE_\<alpha> \<inter> last p_\<alpha> \<times> UNIV = {}"
      shows "pop_impl i
        \<le> \<Down>GS_rel (SPEC (\<lambda>r. r=(butlast p_\<alpha>, D_\<alpha> \<union> last p_\<alpha>, pE_\<alpha>, vE)))"
    proof -
      have iexI: "\<And>a b j P. \<lbrakk>a!j = b!j; P j\<rbrakk> \<Longrightarrow> \<exists>j'. a!j = b!j' \<and> P j'"
        by blast
      
      have [simp]: "\<And>n. n - Suc 0 \<noteq> n \<longleftrightarrow> n\<noteq>0" by auto
  
      from NE have BNE: "B\<noteq>[]"
        unfolding p_\<alpha>_def by auto
  
      {
        fix i j
        assume B: "j<B!i" and A: "i<length B"
        note B
        also from sorted_nth_mono[OF B_sorted, of i "length B - 1"] A 
        have "B!i \<le> last B"
          by (simp add: last_conv_nth)
        finally have "j < last B" .
        hence "take (last B) S ! j = S ! j" 
          and "take (B!(length B - Suc 0)) S !j = S!j"
          by (simp_all add: last_conv_nth BNE)
      } note AUX1=this
  
      {
        fix v j
        have "(mark_as_done_abs 
                (seg_start (length B - Suc 0))
                (seg_end (length B - Suc 0)) I i v = Some (STACK j)) 
          \<longleftrightarrow> (j < length S \<and> j < last B \<and> v = take (last B) S ! j)"
          apply (simp add: mark_as_done_abs_def)
          apply safe []
          using I_consistent
          apply (clarsimp_all
            simp: seg_start_def seg_end_def last_conv_nth BNE
            simp: S_idx_uniq)
  
          apply (force)
          apply (subst nth_take)
          apply force
          apply force
          done
      } note AUX2 = this
  
      define ci where "ci = ( 
        take (last B) S, 
        butlast B,
        mark_as_done_abs 
          (seg_start (length B - Suc 0)) (seg_end (length B - Suc 0)) I i,
        P)"
  
      have ABS: "GS_defs.\<alpha> ci = (butlast p_\<alpha>, D_\<alpha> \<union> last p_\<alpha>, pE_\<alpha>)"
        apply (simp add: GS_defs.\<alpha>_def ci_def)
        apply (intro conjI)
        apply (auto  
          simp del: map_butlast
          simp add: map_butlast[symmetric] butlast_upt
          simp add: GS_defs.p_\<alpha>_def GS_defs.seg_def[abs_def] GS_defs.seg_start_def GS_defs.seg_end_def
          simp: nth_butlast last_conv_nth nth_take AUX1
          cong: if_cong
          intro!: iexI
          dest: order.strict_trans[OF _ B_in_bound']
        ) []
  
        apply (auto 
          simp: GS_defs.D_\<alpha>_def p_\<alpha>_def last_map BNE seg_def mark_as_done_abs_def) []
  
        done
  
      note SUBP = no_last_out_P_aux'[OF NE NS]
  
      have INV: "GS_invar MG V\<^sub>i ci"
        apply unfold_locales
        apply (simp_all add: ci_def)
  
        subgoal using B_in_bound B_sorted B_distinct 
          apply (cases B rule: rev_cases, simp) 
          by (auto simp: sorted_append order.strict_iff_order)
  
        subgoal
          using B_sorted BNE by (auto simp: sorted_butlast)
  
        subgoal
          using B_distinct BNE by (auto simp: distinct_butlast)
  
        subgoal
          using B0 apply (cases B rule: rev_cases, simp add: BNE) 
          by (auto simp: nth_append split: if_split_asm)
     
        subgoal
          using S_distinct by (auto)
  
        subgoal by (rule AUX2)
        
        subgoal using sorted_after_pop[OF BNE] SUBP by fast
        
        subgoal using no_last_out_P_aux'[OF NE NS] by simp
  
        subgoal using P_distinct by simp
  
        using S_subset_nodes
          by (meson set_take_subset subset_trans)
        
  
      show ?thesis
        unfolding pop_impl_def
        apply (refine_rcg 
          SPEC_refine refine_vcg order_trans[OF mark_as_done_aux])
        apply (simp_all add: BNE seg_start_less_end seg_end_bound)
        subgoal
          using B_in_bound'[of "length B - 1", folded last_conv_nth[OF BNE], simplified, OF BNE] by force
        subgoal
          apply (fold ci_def)
          unfolding GS_rel_def
          by (simp_all add: ABS INV in_br_conv)
        done
    qed
  
    lemma node_state_rule[refine_vcg]: 
      "\<lbrakk> \<And>j. v=STACK j \<Longrightarrow> f1 j \<le> SPEC \<Phi>; \<And>i. v=DONE i \<Longrightarrow> f2 i \<le> SPEC \<Phi>\<rbrakk> 
      \<Longrightarrow> (case v of STACK j \<Rightarrow> f1 j | DONE i \<Rightarrow> f2 i) \<le> SPEC \<Phi>"
      by (auto split: node_state.split)
  
    lemma sel_rem_last_correct:
      assumes NE: "p_\<alpha>\<noteq>[]"
      shows
      "sel_rem_last \<le> \<Down>(Id \<times>\<^sub>r GS_rel) (select_edge (p_\<alpha>,D_\<alpha>,pE_\<alpha>,vE))"
    proof -
      from NE have BNE[simp]: "B\<noteq>[]" unfolding p_\<alpha>_def by simp
  
      {
        fix v C xs
        assume "xs \<noteq> []"
        hence "map f xs = map f (butlast xs) @ [f (last xs)]" for f
          apply(induction xs) 
          apply simp 
          by fastforce
      } note BAL=this
  
      {
        fix u si
        assume A: "last P = (u, si)" and B: "P \<noteq> []"
        from A have "(u, si) \<in> set P" using last_in_set[OF B]
          by presburger
  
        hence "u \<in> set S" using P_bound 
          by blast
      } note AUX1 = this
  
      {
          fix un sn uo so v
          assume INVN: "succ_index_inv MG V\<^sub>i (un, sn)"
          and NXT: "next_index (un, sn) = (uo, so)"
          and SUC: "v \<in> set so"
  
          from INVN interpret succ_index_inv MG V\<^sub>i "(un, sn)" .
  
          have INVO: "succ_index_inv MG V\<^sub>i (uo, so)" 
            apply(unfold_locales)
            subgoal
              using sub_succs NXT
              by(auto simp: next_index_def dest!:in_set_tlD)
            subgoal using SUC by force
            done
           
          have "(uo, v) \<in> E_\<alpha>" using succ_index_inv.remaining_successors_succ[OF INVO] SUC by force
      } note AUX2 = this
  
      have INVAR: "sel_rem_last \<le> SPEC (GS_invar MG V\<^sub>i o snd)"
        unfolding sel_rem_last_def
        apply (refine_rcg refine_vcg)
        using locale_this apply (cases SBIP) 
        
        subgoal by simp
        subgoal for x' P' v C 
        using I_consistent by(auto simp: in_set_conv_nth dest!: last_in_set mp[OF P_bound[THEN in_mono]])
  
        subgoal by auto[1]
        subgoal using P_bound by fastforce
  
        subgoal
          apply clarsimp apply(rule conjI; rule impI)
  
          apply (unfold_locales, simp_all) []
          using B_in_bound B_sorted B_distinct B0 S_distinct I_consistent 
          apply auto [6]
  
          subgoal using BAL[of P "S_idx_of \<circ> fst"] P_sorted
            by (auto simp: map_butlast sorted_butlast fst_next_index) 
          subgoal using P_bound by (auto simp: butlast_subset 
              dest: succ_index_inv.remaining_successors_K next_index_state_eq 
              intro: AUX1 AUX2 succ_index_inv.next_succ_index_inv) 
  
          subgoal using P_distinct by (auto simp: distinct_butlast fst_next_index dest!: BAL[of P fst])
  
          subgoal using S_subset_nodes by blast
  
          subgoal
            apply (unfold_locales, simp_all) []
            using B_in_bound B_sorted B_distinct B0 S_distinct I_consistent 
            apply auto [6]
            
            subgoal
              using BAL[of P "S_idx_of \<circ> fst"] P_sorted 
              by (auto simp: map_butlast sorted_butlast) 
            subgoal using P_bound by (auto simp: butlast_subset) 
            subgoal using P_distinct by (auto simp: distinct_butlast dest!: BAL[of P fst])
  
            subgoal using S_subset_nodes by blast
          done
        done
  
        using locale_this apply (cases SBIP) apply simp
        done
      
  
      {
        assume NS: "set_mset pE_\<alpha>\<inter>last p_\<alpha>\<times>UNIV = {}"
        hence "sel_rem_last 
          \<le> SPEC (\<lambda>r. case r of (None,SBIP') \<Rightarrow> SBIP'=SBIP | _ \<Rightarrow> False)"
          unfolding sel_rem_last_def
          apply (refine_rcg refine_vcg)
          apply (cases SBIP)
          apply simp
  
          subgoal for a b v succs  
          apply(subgoal_tac "v \<in> set S")
          using I_consistent apply (metis in_set_conv_nth)
          using P_bound I_consistent unfolding op_list_pop_last_def by auto
  
  
          apply simp
          using P_bound apply (cases P rule: rev_cases, auto) []
          apply simp
          
          using no_last_out_P_aux[OF NE NS] 
          apply(subgoal_tac "S_idx_of (fst (last P)) < last B") 
          unfolding seg_start_def
          apply (auto simp: last_conv_nth) []
          apply force
  
          apply (cases SBIP)
          apply simp
          done
      } note SPEC_E = this
      
      {
        assume NON_EMPTY: "set_mset pE_\<alpha>\<inter>last p_\<alpha>\<times>UNIV \<noteq> {}"
  
        then obtain v si P' where 
          EFMT: "P = P'@[(v,si)]"
          unfolding pE_\<alpha>_def
          by (cases P rule: rev_cases) auto
          
        with P_bound have VPA: "v \<in> \<Union> (set p_\<alpha>)" and SNE: "succ_index_inv MG V\<^sub>i (v,si)" 
          by(auto simp: set_p_\<alpha>_is_set_S)
  
        with P_bound have J_UPPER: "S_idx_of v<length S" 
          using S_idx_of_correct(1) by blast
  
        from SNE interpret succ_index_inv MG V\<^sub>i "(v,si)" .
  
        have J_LOWER: "seg_start (length B - Suc 0) \<le> S_idx_of v"
        proof (rule ccontr)
          assume "\<not>(seg_start (length B - Suc 0) \<le> S_idx_of v)"
          hence "S_idx_of v < seg_start (length B - 1)" by simp
          with EFMT P_sorted
          have P_bound': "set (map (S_idx_of \<circ> fst) P) \<subseteq> {0..<seg_start (length B - 1)}"
            by (auto simp: sorted_append)
          have "set_mset pE_\<alpha> \<inter> last p_\<alpha>\<times>UNIV = {}"
          proof (rule ccontr)
            assume ASM: "set_mset pE_\<alpha> \<inter> last p_\<alpha> \<times> UNIV \<noteq> {}"
            then obtain v1 v2 where INB: "(v1,v2) \<in> set_mset pE_\<alpha> \<inter> last p_\<alpha> \<times> UNIV" by blast
            hence VPA1: "v1 \<in> fst ` (set P)" 
              unfolding pE_\<alpha>_def edges_of_succs_def by auto
            hence "S_idx_of v1 < seg_start (length B - 1)" 
              unfolding edges_of_succs_def pE_\<alpha>_def using P_bound' INB 
              by fastforce
            moreover have "last B \<le> S_idx_of v1"
            proof -
              from INB have "v1 \<in> {S ! j |j. last B \<le> j \<and> j < length S}" 
                using last_p_\<alpha>_alt_def[OF NE] by blast
              then obtain j where JID: "v1 = S ! j" and LBJ: "last B \<le> j" and "j < length S" by blast
              hence "I v1 = Some (STACK j)" using I_consistent[of v1 j] by blast
              hence "S_idx_of v1 = j" unfolding S_idx_of_def by simp
              thus ?thesis using LBJ by blast
            qed
            ultimately show False unfolding seg_start_def by(simp add: last_conv_nth) 
          qed
          thus False using NON_EMPTY by simp
        qed
  
        from J_UPPER J_LOWER have SJL: "v\<in>last p_\<alpha>" 
          unfolding p_\<alpha>_def seg_def[abs_def] seg_end_def 
          apply (simp add: last_map)
          apply (rule exI[where ?x="S_idx_of v"]) 
          by (auto simp: S_idx_of_correct[OF VPA])
  
  
        from EFMT have SSS: "{v}\<times>set si \<subseteq> set_mset pE_\<alpha>"
          unfolding pE_\<alpha>_def edges_of_succs_def
          by (auto simp: S_idx_of_correct[OF VPA])
  
        {
          from SJL SSS have G: "(v,successor_at (v,si))\<in>set_mset pE_\<alpha> \<inter> last p_\<alpha>\<times>UNIV" 
            using successor_at_in_remaining_successors
            by auto
  
          have SUCCS_ALT: "si = successor_at (v,si) # snd (next_index (v,si))"
            using successor_at_cons_remaining_successors_eq by simp
          
          {
            fix v' ci'
            assume "v' = v" "(v', ci') \<in> set P'"
            with P_distinct \<open>(v', ci') \<in> set P'\<close> EFMT have False by auto
          } note AUX3=this
  
          have G1: "GS_defs.pE_\<alpha> (S,B,I,P' @ [ next_index (v,si) ]) = pE_\<alpha> - {#(v, successor_at (v,si))#}"
          proof -
            from EFMT have "pE_\<alpha> = GS_defs.pE_\<alpha> (S,B,I,P' @ [(v,si)])" 
              using pE_\<alpha>_indep by auto
            have "mset (tl si) = mset si - {#successor_at (v, si)#}" 
              by (metis SUCCS_ALT list.discI list.sel(1) mset_tl) 
            thus ?thesis
            unfolding GS_defs.pE_\<alpha>_def edges_of_succs_def using AUX3 EFMT SUCCS_ALT successor_at_in_remaining_successors
              by (auto simp: next_index_def image_mset_Diff) 
          qed
          {
            assume A:  "\<not> has_next (v,si)"
            hence RSS: "si = [successor_at (v,si)]" 
              using no_next_remaining_successors by auto
            from A have "pE_\<alpha> = GS_defs.pE_\<alpha> (S,B,I,P' @ [(v,si)])" 
              using pE_\<alpha>_indep[unfolded EFMT] SUCCS_ALT by simp
            hence "GS_defs.pE_\<alpha> (S,B,I,P') = pE_\<alpha> - {#(v,successor_at (v,si))#}"
              unfolding GS_defs.pE_\<alpha>_def edges_of_succs_def apply(simp)
              by (metis (mono_tags, lifting) RSS add_implies_diff image_mset_single mset_single_iff_right)
          } note G2 = this
  
          note G G1 G2
        } note AUX3 = this
  
        have "sel_rem_last \<le> SPEC (\<lambda>r. case r of 
          (Some v,SBIP') \<Rightarrow> \<exists>u. 
              (u,v)\<in>((set_mset pE_\<alpha>)\<inter>last p_\<alpha>\<times>UNIV) 
            \<and> GS_defs.\<alpha> SBIP' = (p_\<alpha>,D_\<alpha>,pE_\<alpha>-{#(u,v)#})
        | _ \<Rightarrow> False)"
          unfolding sel_rem_last_def
          apply (refine_rcg refine_vcg)
  
          using SNE apply (vc_solve simp: J_LOWER EFMT)
      
          apply(subgoal_tac "v \<in> set S")
          using I_consistent J_UPPER S_idx_of_correct(2) set_p_\<alpha>_is_set_S apply auto[1]
          using EFMT P_bound apply fastforce 
  
          apply(rule conjI)
  
          subgoal for j
            apply(rule impI)
            apply(rule exI[where ?x=v])
            using AUX3(1) apply clarsimp
            apply(auto simp: AUX3(2) GS_defs.\<alpha>_def)
            done
  
          subgoal for j
            apply(rule impI)
            apply(rule exI[where ?x=v])
            using AUX3(1) apply clarsimp
            apply (auto simp: GS_defs.\<alpha>_def intro!: AUX3(3))
            done
          
          done
  
      } note SPEC_NE=this
  
      have SPEC: "sel_rem_last \<le> SPEC (\<lambda>r. case r of 
          (None, SBIP') \<Rightarrow> SBIP' = SBIP \<and> (set_mset pE_\<alpha>) \<inter> last p_\<alpha> \<times> UNIV = {} \<and> GS_invar MG V\<^sub>i SBIP
        | (Some v, SBIP') \<Rightarrow> \<exists>u. (u, v) \<in> (set_mset pE_\<alpha>) \<inter> last p_\<alpha> \<times> UNIV 
                          \<and> GS_defs.\<alpha> SBIP' = (p_\<alpha>, D_\<alpha>, pE_\<alpha> - {#(u, v)#})
                          \<and> GS_invar MG V\<^sub>i SBIP'
      )"  
        using INVAR
        apply (cases "(set_mset pE_\<alpha>) \<inter> last p_\<alpha> \<times> UNIV = {}") 
        apply (frule SPEC_E)
        apply (auto split: option.splits simp: pw_le_iff; blast; fail)
        apply (frule SPEC_NE)
        apply (auto split: option.splits simp: pw_le_iff; blast; fail)
        done    
        
        
      have X1: "(\<exists>y. (y=None \<longrightarrow> \<Phi> y) \<and> (\<forall>a b. y=Some (a,b) \<longrightarrow> \<Psi> y a b)) \<longleftrightarrow>
        (\<Phi> None \<or> (\<exists>a b. \<Psi> (Some (a,b)) a b))" for \<Phi> \<Psi>
        by auto
        
  
      show ?thesis
        apply (rule order_trans[OF SPEC])
        unfolding select_edge_def select_def 
        apply (auto 
          simp: pw_le_iff refine_pw_simps prod_rel_sv in_br_conv GS_rel_def GS_defs.\<alpha>_def
          del: SELECT_pw
          split: option.splits prod.splits)
        apply (metis option.inject prod.inject)
        done
    qed
  
  
    lemma find_seg_idx_of_correct:
      assumes A: "v\<in>\<Union>(set p_\<alpha>)"
      shows "(find_seg (S_idx_of v)) = idx_of p_\<alpha> v"
    proof -
      note S_idx_of_correct[OF A] idx_of_props[OF p_\<alpha>_disjoint_sym A]
      from find_seg_correct[OF \<open>S_idx_of v < length S\<close>] have 
        "find_seg (S_idx_of v) < length p_\<alpha>" 
        and "S!S_idx_of v \<in> p_\<alpha>!find_seg (S_idx_of v)"
        unfolding p_\<alpha>_def by auto
      from idx_of_uniq[OF p_\<alpha>_disjoint_sym this] \<open>S ! S_idx_of v = v\<close> 
      show ?thesis by auto
    qed
  
  
    lemma idx_of_correct:
      assumes A: "v\<in>\<Union>(set p_\<alpha>)"
      shows "idx_of_impl v \<le> SPEC (\<lambda>x. x=idx_of p_\<alpha> v \<and> x<length B)"
      using assms
      unfolding idx_of_impl_def
      apply (refine_rcg SPEC_refine refine_vcg order_trans[OF find_seg_impl_aux])
      apply (metis I_consistent S_idx_of_correct(1) S_idx_of_correct(2))
      apply (erule S_idx_of_correct)
      using find_seg_idx_of_correct apply blast
      using find_seg_correct(2) by blast
  
  
    lemma collapse_correct:
      assumes A: "v\<in>\<Union>(set p_\<alpha>)"
      shows "collapse_impl v \<le>\<Down>GS_rel (SPEC (\<lambda>r. r=collapse v (p_\<alpha>, D_\<alpha>, pE_\<alpha>, vE)))"
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
  
      from A obtain i where [simp]: "I v = Some (STACK i)"
        using I_consistent set_p_\<alpha>_is_set_S
        by (auto simp: in_set_conv_nth)
  
      {
        have "(collapse_aux p_\<alpha> (idx_of p_\<alpha> v), D_\<alpha>, pE_\<alpha>) =
          GS_defs.\<alpha> (S, take (Suc (idx_of p_\<alpha> v)) B, I, P)"
        unfolding GS_defs.\<alpha>_def
        using idx_of_props[OF p_\<alpha>_disjoint_sym A]
        by (simp add: AUX1)
      } note ABS=this
  
      {
        have "GS_invar MG V\<^sub>i (S, take (Suc (idx_of p_\<alpha> v)) B, I, P)"
          apply unfold_locales
          apply simp_all
  
          using B_in_bound B_sorted B_distinct
          apply (auto simp: sorted_wrt_take dest: in_set_takeD) [3]
  
          using B0 S_distinct apply auto [2]
  
          using I_consistent apply simp
  
          using P_sorted P_distinct P_bound apply auto[3]
  
          using S_subset_nodes apply auto
  
          done
      } note INV=this
  
      show ?thesis
        unfolding collapse_impl_def
        apply (refine_rcg SPEC_refine refine_vcg order_trans[OF idx_of_correct])
        apply fact
        apply simp
  
        apply (simp add: collapse_def \<alpha>_def)
        unfolding GS_rel_def
        apply (clarsimp simp: in_br_conv)
          apply (rule conjI)
          apply (rule ABS)
          apply (rule INV)
        done
    qed
  
  end
  
  text \<open>Technical adjustment for avoiding case-splits for definitions
    extracted from GS-locale\<close>
  lemma opt_GSdef: "f \<equiv> g \<Longrightarrow> f s \<equiv> case s of (S,B,I,P) \<Rightarrow> g (S,B,I,P)" by auto
  
  lemma ext_def: "f\<equiv>g \<Longrightarrow> f x \<equiv> g x" by auto
  
  context mdp_graph begin
  
    interpretation GSX: GS MG V\<^sub>i SBIP for SBIP by unfold_locales
  
    definition "push_impl_fr v s \<equiv> GSX.push_impl s v" 
    lemmas push_impl_def_opt = 
      push_impl_fr_def[abs_def, 
      THEN ext_def, THEN opt_GSdef, unfolded GSX.push_impl_def GS_sel_simps]
  
    lemma GS_\<alpha>_split: 
      "GS_defs.\<alpha> s = (p,D,pE) \<longleftrightarrow> (p=GS_defs.p_\<alpha> s \<and> D=GS_defs.D_\<alpha> s \<and> pE=GS_defs.pE_\<alpha> s)"
      "(p,D,pE) = GS_defs.\<alpha> s \<longleftrightarrow> (p=GS_defs.p_\<alpha> s \<and> D=GS_defs.D_\<alpha> s \<and> pE=GS_defs.pE_\<alpha> s)"
      by (auto simp add: GS_defs.\<alpha>_def)
  
    lemma ex_tuple3_eq_conv_aux: "(\<exists>a b c. (a,b,c) = x \<and> P a b c) \<longleftrightarrow> (case x of (a,b,c) \<Rightarrow> P a b c)"
      apply (cases x)
      by auto
  
  
    lemma push_refine:
      assumes A: "(s,(p,D,pE,vE))\<in>GS_rel" "(v,v')\<in>Id"
      assumes B: "v\<notin>\<Union>(set p)" "v\<notin>D"
      assumes REACH: "v \<in> E_\<alpha>\<^sup>* `` V0"
      shows "push_impl_fr v s \<le> \<Down>GS_rel (push v' (p,D,pE,vE))"
    proof -
      from A have XF[simp]: "p=GS_defs.p_\<alpha> s" "D=GS_defs.D_\<alpha> s" "pE=GS_defs.pE_\<alpha> s" "v'=v" 
        and INV: "GS_invar MG V\<^sub>i s"
        by (auto simp add: GS_rel_def br_def GS_\<alpha>_split)
  
      interpret GS_invar MG V\<^sub>i s by fact
  
      note CC = push_impl_core_correct[OF B[unfolded XF] REACH]
  
      have VNS: "v\<notin>set (GSX.S s)" 
        using XF(1) B set_p_\<alpha>_is_set_S by argo
      hence LS: "length (GSX.S s) < card (E_\<alpha>\<^sup>* `` V0)"
        by (metis REACH S_distinct S_length_nodes S_subset_nodes card_subset_eq distinct_card finite_reachableE_V0 le_neq_implies_less)
      hence LB: "length (GSX.B s) < card (E_\<alpha>\<^sup>* `` V0)"
        by (metis B_distinct B_in_bound' B_length_nodes B_sorted order_le_imp_less_or_eq order_le_less_trans order_less_imp_not_eq2 sorted_wrt_less_idx strict_sorted_iff)
  
      have LP: "length (GSX.P s) < card (E_\<alpha>\<^sup>* `` V0)"
      proof -
        have "v\<notin>set (map fst (GSX.P s))" 
          using P_bound VNS by auto
        hence "set (map fst (GSX.P s)) \<subseteq> E_\<alpha>\<^sup>* `` V0 - {v}" using P_bound S_subset_nodes
          by force
        hence "card (set (map fst (GSX.P s))) \<le> card (E_\<alpha>\<^sup>* `` V0 - {v})"
          by (auto intro: card_mono)
        moreover have "card (set (map fst (GSX.P s))) = length (GSX.P s)"
          by (metis P_distinct distinct_card length_map)
        moreover have "card (E_\<alpha>\<^sup>* `` V0 - {v}) = card (E_\<alpha>\<^sup>* `` V0) - 1"
          by (simp add: REACH)
        moreover have "card (E_\<alpha>\<^sup>* `` V0) \<noteq> 0"
          using REACH by auto
        ultimately show ?thesis by linarith
      qed

      obtain si where B: "set si = successors_of v" 
        by (metis E_conv REACH finite_list finite_succ)
  
      show ?thesis
        unfolding push_impl_fr_def
        apply(rule order_trans[OF CC])
        apply(rule LS)
        apply(rule LB)
        apply(rule LP)
  
        unfolding push_impl_fr_def GSX.push_impl_def push_def out_edges_def using B
        apply (fastforce simp: pw_le_iff refine_pw_simps
            simp: GS_rel_def in_br_conv ex_tuple3_eq_conv_aux split: prod.splits
            simp: E_\<alpha>_mem set_edges_of_succs_raw ) 
        done
    qed
  
  
    definition "pop_impl_fr s \<equiv> GSX.pop_impl s"
    lemmas pop_impl_def_opt = 
      pop_impl_fr_def[abs_def, THEN opt_GSdef, unfolded GSX.pop_impl_def
      mark_as_done_def GS_defs.seg_start_def GS_defs.seg_end_def 
      GS_sel_simps]
  
    lemma pop_refine:
      assumes A: "(s,(p,D,pE,vE))\<in>GS_rel"
      assumes B: "p \<noteq> []" "set_mset pE \<inter> last p \<times> UNIV = {}"
      shows "pop_impl_fr s i \<le> \<Down>GS_rel (RETURN (pop (p,D,pE,vE)))"
    proof -
      from A have [simp]: "p=GS_defs.p_\<alpha> s \<and> D=GS_defs.D_\<alpha> s \<and> pE=GS_defs.pE_\<alpha> s" 
        and INV: "GS_invar MG V\<^sub>i s"
        by (auto simp add: GS_rel_def br_def GS_\<alpha>_split)
  
      show ?thesis
        unfolding pop_impl_fr_def[abs_def] pop_def
        apply (rule order_trans[OF GS_invar.pop_correct])
        using INV B
        apply (auto simp add: Un_commute RETURN_def)
        done
    qed
  
  
    definition "collapse_impl_fr v s \<equiv> GSX.collapse_impl s v"
    lemmas collapse_impl_fr_def_opt = 
      collapse_impl_fr_def[abs_def, 
      THEN ext_def, THEN opt_GSdef, unfolded GSX.collapse_impl_def GS_sel_simps]
  
    lemma collapse_refine:
      assumes A: "(s,(p,D,pE,vE))\<in>GS_rel" "(v,v')\<in>Id"
      assumes B: "v'\<in>\<Union>(set p)"
      shows "collapse_impl_fr v s \<le>\<Down>GS_rel (RETURN (collapse v' (p,D,pE,vE)))"
    proof -
      from A have [simp]: "p=GS_defs.p_\<alpha> s \<and> D=GS_defs.D_\<alpha> s \<and> pE=GS_defs.pE_\<alpha> s" "v'=v" 
        and INV: "GS_invar MG V\<^sub>i s"
        by (auto simp add: GS_rel_def br_def GS_\<alpha>_split)
  
      show ?thesis
        unfolding collapse_impl_fr_def[abs_def]
        apply (rule order_trans[OF GS_invar.collapse_correct])
        using INV B by (auto simp add: GS_defs.\<alpha>_def RETURN_def)
    qed
  
    definition "select_edge_impl s \<equiv> GSX.sel_rem_last s"
    sepref_register select_edge_impl :: "'v list \<times> nat list \<times> ('v \<Rightarrow> node_state option) \<times> ('v \<times> 'v list) list
       \<Rightarrow> ('v option \<times> 'v list \<times> nat list \<times> ('v \<Rightarrow> node_state option) \<times> ('v \<times> 'v list) list) nres"
  
  
    lemmas select_edge_impl_def_opt = 
      select_edge_impl_def[abs_def, 
        THEN opt_GSdef, 
        unfolded GSX.sel_rem_last_def GS_defs.seg_start_def GS_sel_simps]
  
    lemma select_edge_refine: 
      assumes A: "(s,(p,D,pE,vE))\<in>GS_rel"
      assumes NE: "p \<noteq> []"
      shows "select_edge_impl s \<le> \<Down>(Id \<times>\<^sub>r GS_rel) (select_edge (p,D,pE,vE))"
    proof -
      from A have [simp]: "p=GS_defs.p_\<alpha> s \<and> D=GS_defs.D_\<alpha> s \<and> pE=GS_defs.pE_\<alpha> s" 
        and INV: "GS_invar MG V\<^sub>i s"
        by (auto simp add: GS_rel_def br_def GS_\<alpha>_split)
  
      from INV NE show ?thesis
        unfolding select_edge_impl_def
        using GS_invar.sel_rem_last_correct[OF INV] NE
        by (simp)
    qed
  
    definition "initial_impl v0 I \<equiv> GS_initial_impl I v0"
    sepref_register initial_impl :: "'v \<Rightarrow> ('v \<Rightarrow> node_state option) \<Rightarrow> ('v list \<times> nat list \<times> ('v \<Rightarrow> node_state option) \<times> ('v \<times> 'v list) list) nres"
  
  
    lemma initial_refine:
      "\<lbrakk>v0\<in>V0;v0\<notin>D0; (I,D0)\<in>oGS_rel; (v0i,v0)\<in>Id\<rbrakk> 
      \<Longrightarrow> initial_impl v0i I \<le> \<Down>GS_rel (initial v0 D0)"
    proof -
      assume A1:"v0\<in>V0" and A2:"v0\<notin>D0" and A3:"(I,D0)\<in>oGS_rel" and A4:"(v0i,v0)\<in>Id"
  
      obtain si where B: "set si = successors_of v0i"
        by (metis A1 A4 E_conv Image_iff Misc.IdD finite_list finite_succ rtrancl.intros(1))
  
      show ?thesis
        unfolding initial_impl_def
        apply(refine_vcg order_trans[OF GS_initial_correct[of I D0 v0i]])
        using A3 apply assumption
        using A2 A4 apply simp
        using A1 A4 apply simp
        using B apply simp
        using A4 by (auto simp: B E_\<alpha>_mem set_edges_of_succs_raw pw_le_iff refine_pw_simps GS_rel_def in_br_conv initial_def GSX.\<alpha>_def out_edges_def)
    qed
  
  
  
    definition "path_is_empty_impl s \<equiv> GS_defs.S s = []"
    lemma path_is_empty_refine: 
      "GS_invar MG V\<^sub>i s \<Longrightarrow> path_is_empty_impl s \<longleftrightarrow> GS_defs.p_\<alpha> s=[]"
      unfolding path_is_empty_impl_def GS_defs.p_\<alpha>_def GS_invar.empty_eq
      by auto
  
    definition (in GS_defs) "is_on_stack_impl v 
      \<equiv> case I v of Some (STACK _) \<Rightarrow> True | _ \<Rightarrow> False"
  
    lemma (in GS_invar) is_on_stack_impl_correct:
      shows "is_on_stack_impl v \<longleftrightarrow> v\<in>\<Union>(set p_\<alpha>)"
      unfolding is_on_stack_impl_def
      using I_consistent[of v]
      apply (force 
        simp: set_p_\<alpha>_is_set_S in_set_conv_nth 
        split: option.split node_state.split)
      done
  
    definition "is_on_stack_impl v s \<equiv> GS_defs.is_on_stack_impl s v"
    lemmas is_on_stack_impl_def_opt = 
      is_on_stack_impl_def[abs_def, THEN ext_def, THEN opt_GSdef, 
        unfolded GS_defs.is_on_stack_impl_def GS_sel_simps]
  
    lemma is_on_stack_refine:
      "\<lbrakk> GS_invar MG V\<^sub>i s \<rbrakk> \<Longrightarrow> is_on_stack_impl v s \<longleftrightarrow> v\<in>\<Union>(set (GS_defs.p_\<alpha> s))"
      unfolding is_on_stack_impl_def GS_rel_def br_def
      by (simp add: GS_invar.is_on_stack_impl_correct)
  
  
    definition (in GS_defs) "is_done_impl v 
      \<equiv> case I v of Some (DONE i) \<Rightarrow> True | _ \<Rightarrow> False"
  
    lemma (in GS_invar) is_done_impl_correct:
      shows "is_done_impl v \<longleftrightarrow> v\<in>D_\<alpha>"
      unfolding is_done_impl_def D_\<alpha>_def
      apply (auto split: option.split node_state.split)
      done
  
    definition "is_done_oimpl v I \<equiv> case I v of Some (DONE i) \<Rightarrow> True | _ \<Rightarrow> False"
    sepref_register is_done_oimpl :: "'a \<Rightarrow> ('a, node_state) i_map \<Rightarrow> bool" 
  
    definition "is_done_impl v s \<equiv> GS_defs.is_done_impl s v"
  
    lemma is_done_orefine:
      "is_done_oimpl v s \<longleftrightarrow> v\<in>oGS_\<alpha> s"
      unfolding is_done_oimpl_def oGS_rel_def br_def
      by (auto 
        simp: oGS_invar_def oGS_\<alpha>_def 
        split: option.splits node_state.split)
  
    lemma is_done_refine:
      "\<lbrakk> GS_invar MG V\<^sub>i s \<rbrakk> \<Longrightarrow> is_done_impl v s \<longleftrightarrow> v\<in>GS_defs.D_\<alpha> s"
      unfolding is_done_impl_def GS_rel_def br_def
      by (simp add: GS_invar.is_done_impl_correct)
  
    lemma oinitial_refine: "(Map.empty, {}) \<in> oGS_rel"
      by (auto simp: oGS_rel_def br_def oGS_\<alpha>_def oGS_invar_def)
  
  end
  
  subsection \<open>Refined Skeleton Algorithm\<close>
  
  text \<open>
    This algorithm implements Gabow's data structure and uses data refinement using \<open>oGS_rel\<close> to
    connect the path-based algorithm to Gabow's implementation.
    In the next step (in Gabow_Skeleton_Code) we refine the algorithm down to LLVM.
  \<close>

  context mdp_graph begin
  
    lemma I_to_outer:
      assumes "((S, B, I, P), ([], D, {#}, vE)) \<in> GS_rel"
      shows "(I,D)\<in>oGS_rel"
      using assms
      unfolding GS_rel_def oGS_rel_def br_def oGS_\<alpha>_def GS_defs.\<alpha>_def GS_defs.D_\<alpha>_def GS_invar_def GS_invar_axioms_def oGS_invar_def
      apply (auto simp: GS_defs.p_\<alpha>_def)
      done
    
    
    definition "skeleton_inner_while_body s = 
            do {
              \<comment> \<open>Select edge from end of path\<close>
              (vo,s) \<leftarrow> select_edge_impl s;
  
              case vo of 
                Some v \<Rightarrow> do {
                  ASSERT (v \<in> E_\<alpha>\<^sup>*``V0);
                  if is_on_stack_impl v s then do {
                    collapse_impl_fr v s
                  } else if \<not>is_done_impl v s then do {
                    \<comment> \<open>Edge to new node. Append to path\<close>
                    push_impl_fr v s
                  } else do {
                    \<comment> \<open>Edge to done node. Skip\<close>
                    RETURN s
                  }
                }
              | None \<Rightarrow> do {
                  \<comment> \<open>No more outgoing edges from current node on path\<close>
                  pop_impl_fr s 0
                }
            }"
  
    definition skeleton_impl :: "'v oGS nres" where
      "skeleton_impl \<equiv> do {
        let I=Map.empty;
        r \<leftarrow> FOREACHi (\<lambda>it I. outer_invar it (oGS_\<alpha> I)) V\<^sub>i (\<lambda>v0 I0. do {
          ASSERT (v0 \<in> E_\<alpha>\<^sup>*``V\<^sub>i);
          if (is_admissible MG v0 \<and> \<not>is_done_oimpl v0 I0) then do {
            ASSERT (v0 \<in> E_\<alpha>\<^sup>*``V0);
            s \<leftarrow> initial_impl v0 I0;
  
            (S,B,I,P)\<leftarrow> WHILEIT ((\<lambda>(p,D,pE). \<exists>vE. invar v0 (oGS_\<alpha> I0) (p,D,pE,vE)) o (GS_defs.\<alpha>))
              (\<lambda>s. \<not>path_is_empty_impl s) 
              skeleton_inner_while_body s;
            RETURN I
          } else
            RETURN I0
        }) I;
        RETURN r
      }"
  
    subsubsection \<open>Correctness Theorem\<close>
  
    theorem skeleton_impl_refine: "skeleton_impl \<le> \<Down>oGS_rel skeleton"
      using [[goals_limit = 23]]
      unfolding skeleton_impl_def skeleton_def skeleton_inner_while_body_def
      apply (refine_rcg
        bind_refine'
        select_edge_refine push_refine 
        pop_refine
        collapse_refine 
        initial_refine
        oinitial_refine
        inj_on_id
      )
      using [[goals_limit = 5]]
      apply refine_dref_type  
  
      apply (vc_solve (nopre) solve: asm_rl I_to_outer
        simp: GS_rel_def br_def GS_defs.\<alpha>_def oGS_rel_def oGS_\<alpha>_def 
        is_on_stack_refine path_is_empty_refine is_done_refine is_done_orefine
        is_admissible_refine
      )
  
      done

  end

end

