theory Graph
imports "II_Modest_Base.Base_MEC"
begin

  text \<open>
    For the SCC algorithm, we need an abstract graph structure.
    For the integration in the MEC algorithm, we derive the graph structure from an MDP kernel.
    
    We use a list of lists because our iterator approach requires a fixed iteration sequence to work.
    We are planning to change this approach which would allow us to use a kernel of type 
    \<open>'v \<Rightarrow> 'v set set\<close> and possibly switch to a graph successor function \<open>'v \<Rightarrow> 'v set\<close> while
    maintaining compatibility with the MEC algorithm.
  \<close>
  
  
  type_synonym 'v mdp_K = "'v \<Rightarrow> 'v set"
  \<comment> \<open>We came up with this abstract data structure to allow efficient indexing over the 
    MDP structure. However, preferably, we would have a graph of type \<open>'v \<Rightarrow> 'v set\<close>.
    While possible (and easier to reason about on the abstract level), this would create
    issues with the separation logic, as the indexing requires knowledge about the data 
    structure.
  
    There is one workaround, which threads information about the data structure into a 
    parameter from the assertion, which can then be passed to other assertions (e.g. the index).
    This will require considerable amounts of work which so far has not been worth it for me.
  \<close>
  
  type_synonym 'v succ_index = "'v \<times> 'v list"
  
  type_synonym 'q digraph = "('q \<times> 'q) set"
  
  type_synonym 'v mdpG = "'v set \<times> 'v mdp_K"
  
  locale mdp_graph_defs = (*TODO: This can be simplified further by removing V\<^sub>i*)
    fixes MG :: "'v mdpG" \<comment> \<open>Mdp admissible states and kernel\<close>
    and V\<^sub>i :: "'v set" \<comment> \<open>Iteration states: This is the set of states that we iterate over, 
      even if they are not states in the graph. Within the loop, we determine whether the states are 
      "admissible, i.e. if we should proceed the DFS over them.\<close>
  begin
  
  
    definition "V0 = (\<lambda> (V0,K). V0) MG"
    definition "K = (\<lambda> (V0,K). K) MG"
  
    definition "E_\<alpha> = {(u,v) | u v. v \<in> K u}"
  
    lemma E_\<alpha>_mem: "(u,v) \<in> E_\<alpha> \<longleftrightarrow> (v \<in> K u)"
      unfolding E_\<alpha>_def by blast
  
    abbreviation "successors_of u \<equiv> K u"
  
    lemma E_conv: "successors_of u = E_\<alpha> `` {u}" unfolding E_\<alpha>_def by fast
  
  end
  
  lemma mdp_graph_defs_MG_simps[simp]:
    "mdp_graph_defs.V0 (V0,K) = V0"
    "mdp_graph_defs.K (V0,K) = K"
    unfolding mdp_graph_defs.V0_def mdp_graph_defs.K_def
    by auto
  
  locale mdp_graph = mdp_graph_defs MG V\<^sub>i for MG :: "'v mdpG" and V\<^sub>i:: "'v set" +
    assumes finite_reachableE_Vi[simp, intro!]: "finite (E_\<alpha>\<^sup>* `` V\<^sub>i)"
    assumes adm_subset_it: "V0 \<subseteq> V\<^sub>i"
  begin
  
    lemma subset_it_edges: "E_\<alpha>\<^sup>* `` V0 \<subseteq> E_\<alpha>\<^sup>* `` V\<^sub>i"
      by (simp add: Image_mono adm_subset_it)
  
    lemma finite_reachableE_V0[simp, intro!]: "finite (E_\<alpha>\<^sup>* `` V0)"
      using infinite_super subset_it_edges by blast
  
    lemma finite_Vi[simp, intro!]: "finite V\<^sub>i"
      by (metis Image_Id Un_Image finite_Un finite_reachableE_Vi rtrancl_trancl_reflcl)
  
    lemma finite_V0[simp, intro!]: "finite V0"
      using adm_subset_it infinite_super by blast
  
    lemma finite_succ:
      assumes "v \<in> (E_\<alpha>\<^sup>* `` V0)" 
      shows "finite (E_\<alpha> `` {v})"
    proof -
      obtain v0 where "v0 \<in> V0" and A: "(v0,v) \<in> E_\<alpha>\<^sup>*" using assms by blast
      hence "E_\<alpha>\<^sup>* `` {v0} \<subseteq> E_\<alpha>\<^sup>* `` V0" by blast
      hence "finite (E_\<alpha>\<^sup>* `` {v0})" using finite_subset by blast
      thus ?thesis using finite_reachable_advance A 
        by (metis finite_Image_subset r_le_rtrancl)
    qed
  
    lemma finite_out_edges:
      assumes "v \<in> (E_\<alpha>\<^sup>* `` V0)" 
      shows "finite (E_\<alpha> \<inter> {v} \<times> UNIV)"
    proof -
      {
        fix w
        assume "(v,w) \<in> E_\<alpha> \<inter> {v} \<times> UNIV"
        hence "w \<in> E_\<alpha> `` {v}" by blast
      }
      hence A: "E_\<alpha> \<inter> {v} \<times> UNIV \<subseteq> {(v,w) | w. w \<in> E_\<alpha> `` {v}}" by blast
      note finite_succ[OF assms]
      hence "finite {(v,w) | w. w \<in> E_\<alpha> `` {v}}" 
        using finite_image_set[of "\<lambda>w. w \<in> E_\<alpha> `` {v}" "\<lambda>w. (v,w)"] 
        by (metis Collect_mem_eq)
      then show ?thesis using finite_subset[OF A] by blast
    qed
  
  end
  
  
  locale succ_index_inv_defs = 
    mdp_graph_defs MG V\<^sub>i for MG and V\<^sub>i::"'v set" + fixes ci::"'v succ_index"
  begin
  
    definition "ui = (\<lambda> (u,s). u) ci"
    definition "si = (\<lambda> (u,s). s) ci"
  
  end
  
  lemma succ_index_inv_sel_simps[simp]:
    "succ_index_inv_defs.ui (u,s) = u"
    "succ_index_inv_defs.si (u,s) = s"
    unfolding succ_index_inv_defs.ui_def succ_index_inv_defs.si_def
    by auto
  
  
  locale succ_index_inv = 
    succ_index_inv_defs MG V\<^sub>i ci + mdp_graph MG V\<^sub>i for MG V\<^sub>i ci +
    assumes sub_succs: "set si \<subseteq> K ui"
    assumes ne_succs: "si \<noteq> []"
  begin
  
  end 
  
  context mdp_graph_defs
  begin
  
    definition(in -) is_admissible :: "'a mdpG \<Rightarrow> 'a \<Rightarrow> bool" where 
      "is_admissible = (\<lambda> (S,K) v. v \<in> S)"
  
    definition is_empty :: "'v \<Rightarrow> bool" where 
      "is_empty u \<equiv> K u = {}"
  
    definition index_begin :: "'v \<Rightarrow> 'v succ_index nres" where
      "index_begin u = SPEC (\<lambda>(u',si). u' = u \<and> set si = K u)"
  
    definition get_state :: "'v succ_index \<Rightarrow> 'v" where
      "get_state = (\<lambda> (u,si). u)"
  
    definition successor_at :: "'v succ_index \<Rightarrow> 'v" where 
      "successor_at = (\<lambda> (u,si). hd si)"
  
    definition has_next :: "'v succ_index \<Rightarrow> bool" where 
      "has_next \<equiv> (\<lambda> (u,si). length si > 1)"
  
    definition next_index :: "'v succ_index \<Rightarrow> 'v succ_index" where 
      "next_index = (\<lambda> (u,si). (u,tl si))"
  
  
    lemma is_admissible_refine: "is_admissible MG x \<longleftrightarrow> x \<in> V0"
      unfolding is_admissible_def by fastforce
  
    lemma is_empty_succ_map: "is_empty u \<longleftrightarrow> E_\<alpha> `` {u} = {}"
      unfolding is_empty_def E_\<alpha>_def 
      by blast
  
    lemma(in succ_index_inv) successor_at_E_\<alpha>: "(ui, successor_at (ui,si)) \<in> E_\<alpha>"
      unfolding successor_at_def E_\<alpha>_def 
      using hd_in_set ne_succs sub_succs by fast
  
    lemma next_index_state_eq: "next_index (u,ci) = (un,cn) \<Longrightarrow> un = u"
      unfolding next_index_def by(auto split: if_splits)
  end
  
  
  subsection \<open>Paths\<close>
  text \<open>Path are modeled as list of nodes, the last node of a path is not included
    into the list. This formalization allows for nice concatenation and splitting
    of paths.\<close>
  inductive path :: "'v digraph \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" for E where
    path0: "path E u [] u"
  | path_prepend: "\<lbrakk> (u,v)\<in>E; path E v l w \<rbrakk> \<Longrightarrow> path E u (u#l) w"
  
  lemma path1: "(u,v)\<in>E \<Longrightarrow> path E u [u] v"
    by (auto intro: path.intros)
  
  lemma path_empty_conv[simp]:
    "path E u [] v \<longleftrightarrow> u=v"
    by (auto intro: path0 elim: path.cases)
  
  inductive_cases path_uncons: "path E u (u'#l) w"
  inductive_simps path_cons_conv: "path E u (u'#l) w"
  
  lemma path_no_edges[simp]: "path {} u p v \<longleftrightarrow> (u=v \<and> p=[])"
    by (cases p) (auto simp: path_cons_conv)
  
  lemma path_conc: 
    assumes P1: "path E u la v" 
    assumes P2: "path E v lb w"
    shows "path E u (la@lb) w"
    using P1 P2 apply induct 
    by (auto intro: path.intros)
    
  lemma path_append:
    "\<lbrakk> path E u l v; (v,w)\<in>E \<rbrakk> \<Longrightarrow> path E u (l@[v]) w"
    using path_conc[OF _ path1] .
  
  lemma path_unconc:
    assumes "path E u (la@lb) w"
    obtains v where "path E u la v" and "path E v lb w"
    using assms
    apply (induct u "la@lb" w arbitrary: la lb rule: path.induct)
    apply (auto intro: path.intros elim!: list_Cons_eq_append_cases)
    done
  
  lemma path_conc_conv: 
    "path E u (la@lb) w \<longleftrightarrow> (\<exists>v. path E u la v \<and> path E v lb w)"
    by (auto intro: path_conc elim: path_unconc)
  
  lemma (in -) path_append_conv: "path E u (p@[v]) w \<longleftrightarrow> (path E u p v \<and> (v,w)\<in>E)"
    by (simp add: path_cons_conv path_conc_conv)
  
  lemmas path_simps = path_empty_conv path_cons_conv path_conc_conv
  
  
  lemmas path_trans[trans] = path_prepend path_conc path_append
  lemma path_from_edges: "\<lbrakk>(u,v)\<in>E; (v,w)\<in>E\<rbrakk> \<Longrightarrow> path E u [u] v" 
    by (auto simp: path_simps)
  
  
  lemma path_edge_cases[case_names no_use split]: 
    assumes "path (insert (u,v) E) w p x"
    obtains 
      "path E w p x" 
    | p1 p2 where "path E w p1 u" "path (insert (u,v) E) v p2 x"
    using assms
    apply induction
    apply simp
    apply (clarsimp)
    apply (metis path_simps path_cons_conv)
    done
  
  lemma path_edge_rev_cases[case_names no_use split]: 
    assumes "path (insert (u,v) E) w p x"
    obtains 
      "path E w p x" 
    | p1 p2 where "path (insert (u,v) E) w p1 u" "path E v p2 x"
    using assms
    apply (induction p arbitrary: x rule: rev_induct)
    apply simp
    apply (clarsimp simp: path_cons_conv path_conc_conv)
    apply (metis path_simps path_append_conv)
    done
  
  
  lemma path_mono: 
    assumes S: "E\<subseteq>E'" 
    assumes P: "path E u p v" 
    shows "path E' u p v"
    using P
    apply induction
    apply simp
    using S
    apply (auto simp: path_cons_conv)
    done
  
  lemma path_is_rtrancl: 
    assumes "path E u l v"
    shows "(u,v)\<in>E\<^sup>*"
    using assms 
    by induct auto
  
  lemma rtrancl_is_path:
    assumes "(u,v)\<in>E\<^sup>*"
    obtains l where "path E u l v"
    using assms 
    by induct (auto intro: path0 path_append)
  
  lemma path_is_trancl: 
    assumes "path E u l v"
    and "l\<noteq>[]"
    shows "(u,v)\<in>E\<^sup>+"
    using assms 
    apply induct
    apply auto []
    apply (case_tac l)
    apply auto
    done
  
  lemma trancl_is_path:
    assumes "(u,v)\<in>E\<^sup>+"
    obtains l where "l\<noteq>[]" and "path E u l v"
    using assms 
    by induct (auto intro: path0 path_append)
  
  lemma path_nth_conv: "path E u p v \<longleftrightarrow> (let p'=p@[v] in
    u=p'!0 \<and>
    (\<forall>i<length p' - 1. (p'!i,p'!Suc i)\<in>E))"
    apply (induct p arbitrary: v rule: rev_induct)
    apply (auto simp: path_conc_conv path_cons_conv nth_append)
    done
  
  lemma path_mapI:
    assumes "path E u p v"
    shows "path (pairself f ` E) (f u) (map f p) (f v)"
    using assms
    apply induction
    apply (simp)
    apply (force simp: path_cons_conv)
    done
  
  lemma path_restrict: 
    assumes "path E u p v" 
    shows "path (E \<inter> set p \<times> insert v (set (tl p))) u p v"
    using assms
  proof induction
    print_cases
    case (path_prepend u v p w)
    from path_prepend.IH have "path (E \<inter> set (u#p) \<times> insert w (set p)) v p w"
      apply (rule path_mono[rotated])
      by (cases p) auto
    thus ?case using \<open>(u,v)\<in>E\<close>
      by (cases p) (auto simp add: path_cons_conv)
  qed auto
  
  lemma path_restrict_closed:
    assumes CLOSED: "E``D \<subseteq> D"
    assumes I: "v\<in>D" and P: "path E v p v'"
    shows "path (E\<inter>D\<times>D) v p v'"
    using P CLOSED I
    by induction (auto simp: path_cons_conv)
  
  
  lemma path_set_induct:
    assumes "path E u p v" and "u\<in>I" and "E``I \<subseteq> I"
    shows "set p \<subseteq> I"
    using assms
    by (induction rule: path.induct) auto
  
  lemma path_nodes_reachable: "path E u p v \<Longrightarrow> insert v (set p) \<subseteq> E\<^sup>*``{u}"
    apply (auto simp: in_set_conv_decomp path_cons_conv path_conc_conv)
    apply (auto dest!: path_is_rtrancl)
    done
  
  lemma path_nodes_edges: "path E u p v \<Longrightarrow> set p \<subseteq> fst`E"
    by (induction rule: path.induct) auto
  
  lemma path_tl_nodes_edges: 
    assumes "path E u p v"
    shows "set (tl p) \<subseteq> fst`E \<inter> snd`E"
  proof -
    from path_nodes_edges[OF assms] have "set (tl p) \<subseteq> fst`E"
      by (cases p) auto
  
    moreover have "set (tl p) \<subseteq> snd`E"
      using assms
      apply (cases)
      apply simp
      apply simp
      apply (erule path_set_induct[where I = "snd`E"])
      apply auto
      done
    ultimately show ?thesis
      by auto
  qed
  
  lemma path_loop_shift: 
    assumes P: "path E u p u"
    assumes S: "v\<in>set p"
    obtains p' where "set p' = set p" "path E v p' v"
  proof -
    from S obtain p1 p2 where [simp]: "p = p1@v#p2" by (auto simp: in_set_conv_decomp)
    from P obtain v' where A: "path E u p1 v" "(v, v') \<in> E" "path E v' p2 u" 
      by (auto simp: path_simps)
    hence "path E v (v#p2@p1) v" by (auto simp: path_simps)
    thus ?thesis using that[of "v#p2@p1"] by auto
  qed
  
  lemma path_hd:
    assumes "p \<noteq> []" "path E v p w"
    shows "hd p = v"
    using assms
    by (auto simp: path_cons_conv neq_Nil_conv)
  
  
  lemma path_last_is_edge:
    assumes "path E x p y"
    and "p \<noteq> []"
    shows "(last p, y) \<in> E"
    using assms
    by (auto simp: neq_Nil_rev_conv path_simps)
  
  lemma path_member_reach_end:
    assumes P: "path E x p y"
    and v: "v \<in> set p"
    shows "(v,y) \<in> E\<^sup>+"
    using assms 
    by (auto intro!: path_is_trancl simp: in_set_conv_decomp path_simps)
  
  lemma path_tl_induct[consumes 2, case_names single step]:
    assumes P: "path E x p y"
    and NE: "x \<noteq> y"
    and S: "\<And>u. (x,u) \<in> E \<Longrightarrow> P x u"
    and ST: "\<And>u v. \<lbrakk>(x,u) \<in> E\<^sup>+; (u,v) \<in> E; P x u\<rbrakk> \<Longrightarrow> P x v"
    shows "P x y \<and> (\<forall> v \<in> set (tl p). P x v)"
  proof -
    from P NE have "p \<noteq> []" by auto
    thus ?thesis using P
    proof (induction p arbitrary: y rule: rev_nonempty_induct)
      case (single u) hence "(x,y) \<in> E" by (simp add: path_cons_conv)
      with S show ?case by simp
    next
      case (snoc u us) hence "path E x us u" by (simp add: path_append_conv)
      with snoc path_is_trancl have 
        "P x u" "(x,u) \<in> E\<^sup>+" "\<forall>v \<in> set (tl us). P x v" 
        by simp_all
      moreover with snoc have "\<forall>v \<in> set (tl (us@[u])). P x v" by simp
      moreover from snoc have "(u,y) \<in> E" by (simp add: path_append_conv)
      ultimately show ?case by (auto intro: ST)
    qed
  qed
  
  
  lemma path_restrict_tl: 
    "\<lbrakk> u\<notin>R; path (E \<inter> UNIV \<times> -R) u p v \<rbrakk> \<Longrightarrow> path (rel_restrict E R) u p v"
    apply (induction p arbitrary: u)
    apply (auto simp: path_simps rel_restrict_def)
    done
  
  lemma path1_restr_conv: "path (E\<inter>UNIV \<times> -R) u (x#xs) v 
    \<longleftrightarrow> (\<exists>w. w\<notin>R \<and> x=u \<and> (u,w)\<in>E \<and> path (rel_restrict E R) w xs v)"
  proof -
    have 1: "rel_restrict E R \<subseteq> E \<inter> UNIV \<times> - R" by (auto simp: rel_restrict_def)
  
    show ?thesis
      by (auto simp: path_simps intro: path_restrict_tl path_mono[OF 1])
  qed
  
  
  
  lemma dropWhileNot_path:
    assumes "p \<noteq> []"
    and "path E w p x"
    and "v \<in> set p"
    and "dropWhile ((\<noteq>) v) p = c"
    shows "path E v c x"
    using assms
  proof (induction arbitrary: w c rule: list_nonempty_induct)
    case (single p) thus ?case by (auto simp add: path_simps)
  next
    case (cons p ps) hence [simp]: "w = p" by (simp add: path_cons_conv)
    show ?case
    proof (cases "p=v")
      case True with cons show ?thesis by simp
    next
      case False with cons have "c = dropWhile ((\<noteq>) v) ps" by simp
      moreover from cons.prems obtain y where "path E y ps x" 
        using path_uncons by metis
      moreover from cons.prems False have "v \<in> set ps" by simp
      ultimately show ?thesis using cons.IH by metis
    qed
  qed
  
  lemma takeWhileNot_path:
    assumes "p \<noteq> []"
    and "path E w p x"
    and "v \<in> set p"
    and "takeWhile ((\<noteq>) v) p = c"
    shows "path E w c v"
    using assms
  proof (induction arbitrary: w c rule: list_nonempty_induct)
    case (single p) thus ?case by (auto simp add: path_simps)
  next
    case (cons p ps) hence [simp]: "w = p" by (simp add: path_cons_conv)
    show ?case
    proof (cases "p=v")
      case True with cons show ?thesis by simp
    next
      case False with cons obtain c' where 
        "c' = takeWhile ((\<noteq>) v) ps" and 
        [simp]: "c = p#c'"
        by simp_all
      moreover from cons.prems obtain y where 
        "path E y ps x" and "(w,y) \<in> E" 
        using path_uncons by metis+
      moreover from cons.prems False have "v \<in> set ps" by simp
      ultimately have "path E y c' v" using cons.IH by metis
      with \<open>(w,y) \<in> E\<close> show ?thesis by (auto simp add: path_cons_conv)
    qed
  qed
  
  
  subsection \<open>Infinite Paths\<close>
  definition ipath :: "'q digraph \<Rightarrow> 'q Omega_Words_Fun.word \<Rightarrow> bool"
    \<comment> \<open>Predicate for an infinite path in a digraph\<close>
    where "ipath E r \<equiv> \<forall>i. (r i, r (Suc i))\<in>E"
  
  
  lemma ipath_conc_conv: 
    "ipath E (u \<frown> v) \<longleftrightarrow> (\<exists>a. path E a u (v 0) \<and> ipath E v)"
    apply (auto simp: conc_def ipath_def path_nth_conv nth_append)
    apply (metis add_Suc_right diff_add_inverse not_add_less1)
    by (metis Suc_diff_Suc diff_Suc_Suc not_less_eq)
  
  lemma ipath_iter_conv:
    assumes "p\<noteq>[]"
    shows "ipath E (p\<^sup>\<omega>) \<longleftrightarrow> (path E (hd p) p (hd p))"
  proof (cases p)
    case Nil thus ?thesis using assms by simp
  next
    case (Cons u p') hence PLEN: "length p > 0" by simp
    show ?thesis proof 
      assume "ipath E (iter (p))"
      hence "\<forall>i. (iter (p) i, iter (p) (Suc i)) \<in> E"
        unfolding ipath_def by simp
      hence "(\<forall>i<length p. (p!i,(p@[hd p])!Suc i)\<in>E)" 
        apply (simp add: assms)
        apply safe
        apply (drule_tac x=i in spec)
        apply simp
        apply (case_tac "Suc i = length p")
        apply (simp add: Cons)
        apply (simp add: nth_append)
        done
      thus "path E (hd p) p (hd p)"
        by (auto simp: path_nth_conv Cons nth_append nth_Cons')
    next
      assume "path E (hd p) p (hd p)"
      thus "ipath E (iter p)"
        apply (auto simp: path_nth_conv ipath_def assms Let_def)
        apply (drule_tac x="i mod length p" in spec)
        apply (auto simp: nth_append assms split: if_split_asm)
        apply (metis less_not_refl mod_Suc)
        by (metis PLEN diff_self_eq_0 mod_Suc nth_Cons_0 mod_less_divisor)
    qed
  qed
  
  lemma ipath_to_rtrancl:
    assumes R: "ipath E r"
    assumes I: "i1\<le>i2"
    shows "(r i1,r i2)\<in>E\<^sup>*"
    using I
  proof (induction i2)
    case (Suc i2)
    show ?case proof (cases "i1=Suc i2")
      assume "i1\<noteq>Suc i2"
      with Suc have "(r i1,r i2)\<in>E\<^sup>*" by auto
      also from R have "(r i2,r (Suc i2))\<in>E" unfolding ipath_def by auto
      finally show ?thesis .
    qed simp
  qed simp
      
  lemma ipath_to_trancl:
    assumes R: "ipath E r"
    assumes I: "i1<i2"
    shows "(r i1,r i2)\<in>E\<^sup>+"
  proof -
    from R have "(r i1,r (Suc i1))\<in>E"
      by (auto simp: ipath_def)
    also have "(r (Suc i1),r i2)\<in>E\<^sup>*"
      using ipath_to_rtrancl[OF R,of "Suc i1" i2] I by auto
    finally (rtrancl_into_trancl2) show ?thesis .
  qed
  
  lemma run_limit_two_connectedI:
    assumes A: "ipath E r" 
    assumes B: "a \<in> limit r" "b\<in>limit r"
    shows "(a,b)\<in>E\<^sup>+"
  proof -
    from B have "{a,b} \<subseteq> limit r" by simp
    with A show ?thesis
      by (metis ipath_to_trancl two_in_limit_iff)
  qed
  
  
  lemma ipath_subpath:
    assumes P: "ipath E r"
    assumes LE: "l\<le>u"
    shows "path E (r l) (map r [l..<u]) (r u)"
    using LE
  proof (induction "u-l" arbitrary: u l)
    case (Suc n)
    note IH=Suc.hyps(1)
    from \<open>Suc n = u-l\<close> \<open>l\<le>u\<close> obtain u' where [simp]: "u=Suc u'" 
      and A: "n=u'-l" "l \<le> u'" 
      by (cases u) auto
      
    note IH[OF A]
    also from P have "(r u',r u)\<in>E"
      by (auto simp: ipath_def)
    finally show ?case using \<open>l \<le> u'\<close> by (simp add: upt_Suc_append)
  qed auto  
  
  lemma ipath_restrict_eq: "ipath (E \<inter> (E\<^sup>*``{r 0} \<times> E\<^sup>*``{r 0})) r \<longleftrightarrow> ipath E r"
    unfolding ipath_def
    by (auto simp: relpow_fun_conv rtrancl_power)
  lemma ipath_restrict: "ipath E r \<Longrightarrow> ipath (E \<inter> (E\<^sup>*``{r 0} \<times> E\<^sup>*``{r 0})) r"
    by (simp add: ipath_restrict_eq)
  
  
  lemma ipathI[intro?]: "\<lbrakk>\<And>i. (r i, r (Suc i)) \<in> E\<rbrakk> \<Longrightarrow> ipath E r"
    unfolding ipath_def by auto
  
  lemma ipathD: "ipath E r \<Longrightarrow> (r i, r (Suc i)) \<in> E"
    unfolding ipath_def by auto
  
  lemma ipath_in_Domain: "ipath E r \<Longrightarrow> r i \<in> Domain E"
    unfolding ipath_def by auto
  
  lemma ipath_in_Range: "\<lbrakk>ipath E r; i\<noteq>0\<rbrakk> \<Longrightarrow> r i \<in> Range E"
    unfolding ipath_def by (cases i) auto
  
  lemma ipath_suffix: "ipath E r \<Longrightarrow> ipath E (Omega_Words_Fun.suffix i r)"
    unfolding suffix_def ipath_def by auto
  
  
  
  
  subsection \<open>Strongly Connected Components\<close>
  
  
  
  text \<open>A strongly connected component is a maximal mutually connected
  set
    of nodes\<close>
  definition is_scc :: "'q digraph \<Rightarrow> 'q set \<Rightarrow> bool"
    where "is_scc E U \<longleftrightarrow> U\<times>U\<subseteq>E\<^sup>* \<and> (\<forall>V. V\<supset>U \<longrightarrow> \<not> (V\<times>V\<subseteq>E\<^sup>*))"
  
  lemma scc_non_empty[simp]: "\<not>is_scc E {}" unfolding is_scc_def by auto
  
  lemma scc_non_empty'[simp]: "is_scc E U \<Longrightarrow> U\<noteq>{}" unfolding is_scc_def by
  auto
  
  lemma is_scc_closed:
    assumes SCC: "is_scc E U"
    assumes MEM: "x\<in>U"
    assumes P: "(x,y)\<in>E\<^sup>*" "(y,x)\<in>E\<^sup>*"
    shows "y\<in>U"
  proof -
    from SCC MEM P have "insert y U \<times> insert y U \<subseteq> E\<^sup>*"
      unfolding is_scc_def
      apply clarsimp
      apply (rule; clarsimp)
      apply (meson SigmaI rtrancl_trans subset_iff)
      by (meson SigmaI rtrancl_trans subset_eq)
    with SCC show ?thesis unfolding is_scc_def by blast
  qed
  
  lemma is_scc_connected:
    assumes SCC: "is_scc E U"
    assumes MEM: "x\<in>U" "y\<in>U"
    shows "(x,y)\<in>E\<^sup>*"
    using assms unfolding is_scc_def by auto
  
  text \<open>In the following, we play around with alternative
  characterizations, and
    prove them all equivalent .\<close>
  
  text \<open>A common characterization is to define an equivalence relation
    ,,mutually connected'' on nodes, and characterize the SCCs as its
    equivalence classes:\<close>
  
  definition mconn :: "('a\<times>'a) set \<Rightarrow> ('a \<times> 'a) set"
    \<comment> \<open>Mutually connected relation on nodes\<close>
    where "mconn E = E\<^sup>* \<inter> (E\<inverse>)\<^sup>*"
  
  lemma mconn_pointwise:
     "mconn E = {(u,v). (u,v)\<in>E\<^sup>* \<and> (v,u)\<in>E\<^sup>*}"
    by (auto simp add: mconn_def rtrancl_converse)
  
  text \<open>\<open>mconn\<close> is an equivalence relation:\<close>
  lemma mconn_refl[simp]: "Id\<subseteq>mconn E"
    by (auto simp add: mconn_def)
  
  lemma mconn_sym: "mconn E = (mconn E)\<inverse>"
    by (auto simp add: mconn_pointwise)
  
  lemma mconn_trans: "mconn E O mconn E = mconn E"
    by (auto simp add: mconn_def)
  
  lemma mconn_refl': "refl (mconn E)"
    by (auto intro: refl_onI simp: mconn_pointwise)
  
  lemma mconn_sym': "sym (mconn E)"
    by (auto intro: symI simp: mconn_pointwise)
  
  lemma mconn_trans': "trans (mconn E)"
    by (metis mconn_def trans_Int trans_rtrancl)
  
  lemma mconn_equiv: "equiv UNIV (mconn E)"
    using mconn_refl' mconn_sym' mconn_trans' 
    by (auto intro!: equivI)

  
  
  lemma is_scc_mconn_eqclasses: "is_scc E U \<longleftrightarrow> U \<in> UNIV // mconn E"
    \<comment> \<open>The strongly connected components are the equivalence classes of
  the
      mutually-connected relation on nodes\<close>
  proof
    assume A: "is_scc E U"
    then obtain x where "x\<in>U" unfolding is_scc_def by auto
    hence "U = mconn E `` {x}" using A
      unfolding mconn_pointwise is_scc_def
      apply clarsimp
      apply rule
      apply auto []
      apply clarsimp
      by (metis A is_scc_closed)
    thus "U \<in> UNIV // mconn E"
      by (auto simp: quotient_def)
  next
    assume "U \<in> UNIV // mconn E"
    thus "is_scc E U"
      by (auto simp: is_scc_def mconn_pointwise quotient_def)
  qed
  
  (* For presentation in the paper *)
  lemma "is_scc E U \<longleftrightarrow> U \<in> UNIV // (E\<^sup>* \<inter> (E\<inverse>)\<^sup>*)"
    unfolding is_scc_mconn_eqclasses mconn_def by simp
  
  text \<open>We can also restrict the notion of "reachability" to nodes
    inside the SCC
  \<close>
  
  lemma find_outside_node:
    assumes "(u,v)\<in>E\<^sup>*"
    assumes "(u,v)\<notin>(E\<inter>U\<times>U)\<^sup>*"
    assumes "u\<in>U" "v\<in>U"
    shows "\<exists>u'. u'\<notin>U \<and> (u,u')\<in>E\<^sup>* \<and> (u',v)\<in>E\<^sup>*"
    using assms
    apply (induction)
    apply auto []
    apply clarsimp
    by (metis IntI mem_Sigma_iff rtrancl.simps)
  
  lemma is_scc_restrict1:
    assumes SCC: "is_scc E U"
    shows "U\<times>U\<subseteq>(E\<inter>U\<times>U)\<^sup>*"
    using assms
    unfolding is_scc_def
    apply clarsimp
    apply (rule ccontr)
    apply (drule (2) find_outside_node[rotated])
    apply auto []
    by (metis is_scc_closed[OF SCC] mem_Sigma_iff rtrancl_trans subsetD)
  
  lemma is_scc_restrict2:
    assumes SCC: "is_scc E U"
    assumes "V\<supset>U"
    shows "\<not> (V\<times>V\<subseteq>(E\<inter>V\<times>V)\<^sup>*)"
    using assms
    unfolding is_scc_def
    apply clarsimp
    using rtrancl_mono[of "E \<inter> V \<times> V" "E"]
    apply clarsimp
    apply blast
    done
  
  lemma is_scc_restrict3:
    assumes SCC: "is_scc E U"
    shows "((E\<^sup>*``((E\<^sup>*``U) - U)) \<inter> U = {})"
    apply auto
    by (metis assms is_scc_closed is_scc_connected rtrancl_trans)
   
  lemma is_scc_alt_restrict_path:
    "is_scc E U \<longleftrightarrow> U\<noteq>{} \<and>
      (U\<times>U \<subseteq> (E\<inter>U\<times>U)\<^sup>*) \<and> ((E\<^sup>*``((E\<^sup>*``U) - U)) \<inter> U = {})"
    apply rule
    apply (intro conjI)
    apply simp
    apply (blast dest: is_scc_restrict1)
    apply (blast dest: is_scc_restrict3)
   
    unfolding is_scc_def
    apply rule
    apply clarsimp
    apply (meson Int_lower1 SigmaI in_mono rtrancl_mono)
    apply blast
    done
  
  lemma is_scc_pointwise:
    "is_scc E U \<longleftrightarrow>
      U\<noteq>{}
    \<and> (\<forall>u\<in>U. \<forall>v\<in>U. (u,v)\<in>(E\<inter>U\<times>U)\<^sup>*)
    \<and> (\<forall>u\<in>U. \<forall>v. (v\<notin>U \<and> (u,v)\<in>E\<^sup>*) \<longrightarrow> (\<forall>u'\<in>U. (v,u')\<notin>E\<^sup>*))"
    \<comment> \<open>Alternative, pointwise characterization\<close>
    unfolding is_scc_alt_restrict_path
    by blast 
  
  lemma scc_disj_or_eq: assumes SCC: "is_scc E scc" "is_scc E scc'" shows "scc = scc' \<or> scc \<inter> scc' = {}"
    using SCC quotient_disj[OF mconn_equiv]
    by (simp add: is_scc_mconn_eqclasses)
  
  
  lemma is_scc_unique:
    assumes SCC: "is_scc E scc" "is_scc E scc'"
    and v: "v \<in> scc" "v \<in> scc'"
    shows "scc = scc'"
    using scc_disj_or_eq[OF SCC] v 
    by blast
  
  lemma is_scc_ex1:
    "\<exists>!scc. is_scc E scc \<and> v \<in> scc"
  proof (rule ex1I, rule conjI)
    let ?scc = "mconn E `` {v}"
    have "?scc \<in> UNIV // mconn E" by (auto intro: quotientI)
    thus "is_scc E ?scc" by (simp add: is_scc_mconn_eqclasses)
    moreover show "v \<in> ?scc" by (blast intro: refl_onD[OF mconn_refl'])
    ultimately show "\<And>scc. is_scc E scc \<and> v \<in> scc \<Longrightarrow> scc = ?scc"
      by (metis is_scc_unique)
  qed
  
  lemma is_scc_ex:
    "\<exists>scc. is_scc E scc \<and> v \<in> scc"
    by (metis is_scc_ex1)
  
  lemma is_scc_connected':
    "\<lbrakk>is_scc E scc; x \<in> scc; y \<in> scc\<rbrakk> \<Longrightarrow> (x,y)\<in>(Restr E scc)\<^sup>*"
    unfolding is_scc_pointwise
    by blast
  
  definition scc_of :: "('v\<times>'v) set \<Rightarrow> 'v \<Rightarrow> 'v set"
    where
    "scc_of E v = (THE scc. is_scc E scc \<and> v \<in> scc)"
  
  lemma scc_of_is_scc[simp]:
    "is_scc E (scc_of E v)"
    using is_scc_ex1[of E v]
    by (auto dest!: theI' simp: scc_of_def)
  
  lemma node_in_scc_of_node[simp]:
    "v \<in> scc_of E v"
    using is_scc_ex1[of E v]
    by (auto dest!: theI' simp: scc_of_def)
  
  lemma scc_of_unique:
    assumes "w \<in> scc_of E v"
    shows "scc_of E v = scc_of E w"
  proof -
    have "is_scc E (scc_of E v)" by simp
    moreover have "is_scc E (scc_of E w)" by simp
    moreover have "w \<in> scc_of E w" by simp
    ultimately show ?thesis using is_scc_unique assms by metis
  qed
  
  subsubsection \<open>SCC Additions\<close>
  
  lemma scc_nodes_eq_reach:
    assumes SCC: "is_scc E U"
    assumes MEM: "x\<in>U" "y\<in>U"
    shows "E\<^sup>* `` {x} = E\<^sup>* `` {y}"
    apply safe
    apply(subgoal_tac "(y,x) \<in> E\<^sup>*")
    apply simp
    using is_scc_connected assms apply metis 
    apply(subgoal_tac "(x,y) \<in> E\<^sup>*") 
    apply simp
    using is_scc_connected assms by metis
  
  
  lemma non_singleton_scc_node_succ_aux:
    assumes SCC: "is_scc E U"
    assumes NE:  "x \<noteq> y"
    assumes MEM: "x\<in>U" "y\<in>U"
    shows "(E \<inter> U \<times> U) `` {x} \<noteq> {}"
    apply(subgoal_tac "(x, y) \<in> (E \<inter> U \<times> U)\<^sup>+")
    apply (metis Image_empty_trancl_Image_empty Image_singleton_iff empty_iff)
    using is_scc_restrict1[OF SCC] MEM NE 
    by (metis SCC is_scc_pointwise rtranclD)
  
  lemma non_singleton_scc_node_succ:
    assumes SCC: "is_scc E U"
    assumes NE:  "\<not> is_singleton U"
    assumes MEM: "x\<in>U"
    shows "(E \<inter> U \<times> U) `` {x} \<noteq> {}"
    using non_singleton_scc_node_succ_aux MEM NE SCC is_singletonI' memb_imp_not_empty
    by metis
  
  lemma is_scc_restrict4: "is_scc E U \<Longrightarrow> is_scc (E\<inter>U\<times>U) U"
    apply(frule is_scc_restrict1)
    unfolding is_scc_def
    apply(subgoal_tac "(Restr E U)\<^sup>* \<subseteq> E\<^sup>*")
    apply (meson subset_trans)
    by (simp add: rtrancl_mono)
    
  lemma scc_strongly_connected: "is_scc E U \<Longrightarrow> U\<times>U\<subseteq>E\<^sup>*"
    unfolding is_scc_def by argo
  
  lemma sc_sub_scc: "u \<in> U \<Longrightarrow> u \<in> V \<Longrightarrow> V \<times> V \<subseteq> E\<^sup>* \<Longrightarrow> is_scc E U \<Longrightarrow> V \<subseteq> U"
  proof(rule ccontr)
    assume UU: "u \<in> U" 
    and UV: "u \<in> V" 
    and SC: "V \<times> V \<subseteq> E\<^sup>*" 
    and SCC: "is_scc E U"
    and CC: "\<not> V \<subseteq> U"
  
    from CC obtain v where "v \<in> V" and VNU: "v \<notin> U" by blast
    with SC UV have E1: "(u,v) \<in> E\<^sup>*" and E2: "(v,u) \<in> E\<^sup>*"
      by fast+
    show False using is_scc_closed[OF SCC UU E1 E2] VNU by fast
  qed
  
  lemma rtrancl_eq_scc: "E\<^sup>* = E'\<^sup>* \<Longrightarrow> is_scc E S \<longleftrightarrow> is_scc E' S"
    unfolding is_scc_def by presburger


  lemma rtrancl_eq_scc': 
    assumes ES1: "E `` S \<subseteq> S"
    assumes ES2: "E' `` S \<subseteq> S"
    assumes ERE: "E\<^sup>* \<inter> (S \<times> UNIV) = E'\<^sup>* \<inter> (S \<times> UNIV)"
    assumes SUB: "scc \<subseteq> S"
    shows "is_scc E scc \<longleftrightarrow> is_scc E' scc"
  proof -

    from ES1 ES2 ERE have ERE': "E\<^sup>* \<inter> (S \<times> S) = E'\<^sup>* \<inter> (S \<times> S)"
      by blast

    {
      fix E E'
      assume ES1: "E `` S \<subseteq> S"
      assume ES2: "E' `` S \<subseteq> S"
      assume ERE':"E\<^sup>* \<inter> (S \<times> S) = E'\<^sup>* \<inter> (S \<times> S)"
      assume SCC: "is_scc E scc"

      hence "scc \<times> scc \<subseteq> E\<^sup>*" and S2: "(\<forall>V. scc \<subset> V \<longrightarrow> \<not> V \<times> V \<subseteq> E\<^sup>*)" 
        unfolding is_scc_def by presburger+

      hence "scc \<times> scc \<subseteq> E\<^sup>* \<inter> (S \<times> S)"
        by (simp add: Sigma_mono SUB)
      hence "scc \<times> scc \<subseteq> E'\<^sup>* \<inter> (S \<times> S)"
        using ERE' by simp
      hence "scc \<times> scc \<subseteq> E'\<^sup>*"
        by simp

      moreover have "(\<forall>V. scc \<subset> V \<longrightarrow> \<not> V \<times> V \<subseteq> E'\<^sup>*)"
      proof(rule allI; rule impI; rule notI)
        fix V u
        assume SUBV: "scc \<subset> V"
        and VE: "V \<times> V \<subseteq> E'\<^sup>*"

        have "V \<subseteq> S"
        proof
          fix v
          assume VV: "v \<in> V"
          with SCC obtain u where "u \<in> scc"
            by fastforce
          with SUB SUBV have "u \<in> V" and "u \<in> S"
            by auto
          with VV VE have "v \<in> E'\<^sup>* `` S"
            by blast
          thus "v \<in> S"
            using Image_closed_trancl[OF ES2] 
            by blast
        qed

        with VE have "V \<times> V \<subseteq> E'\<^sup>* \<inter> (S \<times> S)"
          by blast
        hence "V \<times> V \<subseteq> E\<^sup>* \<inter> (S \<times> S)"
          using ERE' by presburger
        hence "V \<times> V \<subseteq> E\<^sup>*"
          by simp

        with S2 SUBV show False
          by presburger
      qed

      ultimately have "is_scc E' scc"
        unfolding is_scc_def by presburger
    } note AUX = this

    show "is_scc E scc = is_scc E' scc"
      apply(safe)
      using AUX ES1 ES2 ERE'
      by presburger+
  qed

  definition "scc_set_of E V = {scc. is_scc E scc \<and> scc \<subseteq> V}"
  
  subsection \<open>Bottom Strongly Connected Components\<close>
  
  definition "is_bottom_scc E V \<equiv> is_scc E V \<and> (\<forall> (u,v) \<in> E. u \<in> V \<longrightarrow> v \<in> V)"
  
  lemma bscc_is_sccD: "is_bottom_scc E V \<Longrightarrow> is_scc E V"
    unfolding is_bottom_scc_def by simp
  
  lemma bscc_not_leavingD: "is_bottom_scc E V \<Longrightarrow> (u,v) \<in> E \<Longrightarrow> u \<in> V \<Longrightarrow> v \<in> V"
    unfolding is_bottom_scc_def by fast
  
  lemma bscc_not_leaving: assumes "is_bottom_scc E U" and "u \<in> U" shows "E `` {u} \<subseteq> U"
    using assms
    unfolding is_bottom_scc_def is_scc_def Image_def
    by fastforce
  
  lemma is_bscc_restrict: "is_bottom_scc E U \<Longrightarrow> is_bottom_scc (E\<inter>U\<times>U) U"
    unfolding is_bottom_scc_def by(auto simp: is_scc_restrict4)
  
  lemma bssc_non_empty: "~is_bottom_scc E {}"
    unfolding is_bottom_scc_def
    by force
  
  lemma bssc_non_empty': "is_bottom_scc E U \<Longrightarrow> U \<noteq> {}"
    unfolding is_bottom_scc_def
    by force
  
  lemma non_empty_non_singleton_has_two_elems:
    assumes "V \<noteq> {}" 
    and "\<not>is_singleton V " 
    obtains u v where "u \<in> V" and "v \<in> V" and "u \<noteq> v"
    using assms
    by (meson assms(2) is_singletonI')
  
  lemma singleton_rtrancl_eq_reflcl: "{(u, v)}\<^sup>* = {(u,v)}\<^sup>="
    by (simp add: rtrancl_trancl_reflcl)
  
  lemma singleton_rtrancl_cases:
  "V \<times> V \<subseteq> {(u, v)}\<^sup>* \<Longrightarrow> (V = {} \<Longrightarrow> P) \<Longrightarrow> (is_singleton V \<Longrightarrow> P) \<Longrightarrow> P"
  proof(rule ccontr)
    assume A: "V \<times> V \<subseteq> {(u, v)}\<^sup>*" and "(V = {} \<Longrightarrow> P)" 
    and "(is_singleton V \<Longrightarrow> P)" and "\<not> P"
    hence "V \<noteq> {}" and "\<not> is_singleton V" by auto
    then obtain s t where "s \<in> V" and "t \<in> V" and NEQ: "s \<noteq> t" 
      by(erule non_empty_non_singleton_has_two_elems)
    with A have "(s,t) \<in> {(u,v)}\<^sup>=" and "(t,s) \<in> {(u,v)}\<^sup>="
      by(auto simp: singleton_rtrancl_eq_reflcl)
    hence "s = t" by fastforce
    with NEQ show False by simp
  qed
  
  lemma dst_scc_in_V: "E \<subseteq> V \<times> V \<Longrightarrow> v \<in> scc \<Longrightarrow> (u,v) \<in> E \<Longrightarrow> is_scc E scc \<Longrightarrow> scc \<subseteq> V"
    unfolding is_scc_def
    by (metis mem_Sigma_iff rtranclE subset_iff)
  
  lemma src_scc_in_V: "E \<subseteq> V \<times> V \<Longrightarrow> u \<in> scc \<Longrightarrow> (u,v) \<in> E \<Longrightarrow> is_scc E scc \<Longrightarrow> scc \<subseteq> V"
    unfolding is_scc_def
    by (metis SigmaD2 SigmaI rtrancl_mono_rightI subset_eq trancl_subset_Sigma_aux)
  
  lemma scc_int_V_is_subset: "is_scc E scc \<Longrightarrow> E \<subseteq> V \<times> V \<Longrightarrow> scc \<inter> V \<noteq> {} \<Longrightarrow> scc \<subseteq> V"
  proof safe
    fix u v
    assume A: "is_scc E scc" and B: "E \<subseteq> V \<times> V" and C: "u \<in> scc" and D: "u \<notin> V" and E: "v \<in> scc" and F: "v \<in> V"
    hence "scc = {u}" 
      by (metis is_scc_connected trancl_subset_Sigma_aux)
    hence "u = v" using C E by blast
    thus "v \<in> {}" using D F by presburger
  qed
  
  lemma ex_bscc: 
    "finite (E\<^sup>* `` {u}) \<Longrightarrow> \<exists> V \<subseteq> (E\<^sup>* `` {u}). is_bottom_scc E V"
  proof(induction "(E\<^sup>* `` {u})" arbitrary: u rule: finite_psubset_induct)
    case psubset
      case psubset
      obtain scc where is_scc: "is_scc E scc" and u_scc: "u \<in> scc"
        by (meson node_in_scc_of_node scc_of_is_scc)
      then show ?case
      proof(cases "is_bottom_scc E scc")
        case True
        then show ?thesis using is_scc u_scc
          by (meson Image_singleton_iff is_scc_connected subsetI)
      next
        case False
        then obtain u1 v1 where UV1E: "(u1,v1) \<in> E" and U1S: "u1 \<in> scc" and V1S: "v1 \<notin> scc" 
          using is_scc unfolding is_bottom_scc_def by blast
        have "E\<^sup>* `` {v1} \<subseteq> E\<^sup>* `` {u1}" 
          using UV1E converse_rtrancl_into_rtrancl by auto
        moreover have "u1 \<notin> E\<^sup>* `` {v1}" 
          by (meson Image_singleton_iff UV1E U1S V1S is_scc(1) is_scc_closed r_into_rtrancl)
        ultimately have "E\<^sup>* `` {v1} \<subset> E\<^sup>* `` {u1}" by blast
        moreover have "E\<^sup>* `` {u} = E\<^sup>* `` {u1}"
          using scc_nodes_eq_reach[OF is_scc u_scc U1S] .
        ultimately show ?thesis 
          using psubset(2) 
          by (metis \<open>E\<^sup>* `` {v1} \<subseteq> E\<^sup>* `` {u1}\<close> subset_iff)
      qed
    qed

(* 
  lemma ex_bscc: 
    assumes ENEMP: "E \<noteq> {}"
    and FINE: "finite E"
    and ESV: "E \<subseteq> V \<times> V"
    shows "\<exists> V' \<subseteq> V. is_bottom_scc E V'"
  proof -
    obtain u v where UDEF: "u \<in> V" and VDEF: "v \<in> V" and UVE: "(u,v) \<in> E" using ESV ENEMP by fast
    have "finite (E\<^sup>* `` {v})" using FINE by auto
    thus ?thesis using UVE
    proof(induction "(E\<^sup>* `` {v})" arbitrary: u v rule: finite_psubset_induct)
      case psubset
      obtain scc where is_scc: "is_scc E scc" "v \<in> scc" and in_V: "scc \<subseteq> V" 
        using dst_scc_in_V[OF ESV _ psubset.prems] is_scc_ex by meson
      then show ?case
      proof(cases "is_bottom_scc E scc")
        case True
        then show ?thesis using in_V by blast
      next
        case False
        then obtain u1 v1 where UV1E: "(u1,v1) \<in> E" and U1S: "u1 \<in> scc" and V1S: "v1 \<notin> scc" 
          using is_scc unfolding is_bottom_scc_def by blast
        have "E\<^sup>* `` {v1} \<subseteq> E\<^sup>* `` {u1}" 
          using UV1E converse_rtrancl_into_rtrancl by auto
        moreover have "u1 \<notin> E\<^sup>* `` {v1}" 
          by (meson Image_singleton_iff UV1E U1S V1S is_scc(1) is_scc_closed r_into_rtrancl)
        ultimately have "E\<^sup>* `` {v1} \<subset> E\<^sup>* `` {u1}" by blast
        then show ?thesis 
          using psubset(2)[OF _ UV1E] scc_nodes_eq_reach[OF is_scc U1S] by argo
      qed
    qed
  qed
*)
  
  definition mop_is_admissible :: "'v mdpG \<Rightarrow> 'v \<Rightarrow> bool nres" where
    "mop_is_admissible MG u = RETURN (is_admissible MG u)"
  
  sepref_register mop_is_admissible
  
  
  definition mop_is_empty :: "'v mdpG \<Rightarrow> 'v \<Rightarrow> bool nres" where
    "mop_is_empty MG u \<equiv> RETURN (mdp_graph_defs.is_empty MG u)"
  
  sepref_register mop_is_empty
  
  
  definition mop_index_begin :: "'v mdpG \<Rightarrow> 'v \<Rightarrow> 'v succ_index nres" where
    "mop_index_begin MG u = (mdp_graph_defs.index_begin MG u)"
  
  sepref_register mop_index_begin
  
  
  definition mop_get_state :: "'v succ_index \<Rightarrow> 'v nres" where
    "mop_get_state uc = RETURN (mdp_graph_defs.get_state uc)"
  
  sepref_register mop_get_state
  
  
  definition mop_graph_succ_at :: "'v mdpG \<Rightarrow> 'v succ_index \<Rightarrow> 'v nres" where
    "mop_graph_succ_at MG uc \<equiv> RETURN (mdp_graph_defs.successor_at uc)"
  
  sepref_register mop_graph_succ_at 
  
  
  definition mop_has_succ :: "'v mdpG \<Rightarrow> 'v succ_index \<Rightarrow> bool nres" where
    "mop_has_succ MG uc = RETURN (mdp_graph_defs.has_next uc)"
  
  sepref_register mop_has_succ
  
  
  definition mop_next_id :: "'v mdpG \<Rightarrow> 'v succ_index \<Rightarrow> 'v succ_index nres" where
    "mop_next_id MG uc = RETURN (mdp_graph_defs.next_index uc)"
  
  sepref_register mop_next_id
  
  
  
  lemma(in mdp_graph) mop_index_begin_conv[simp]: "mop_index_begin MG u = index_begin u"
    unfolding mop_index_begin_def by simp
  
  lemma(in mdp_graph) mop_graph_succ_at_conv[simp]: "mop_graph_succ_at MG uc = RETURN (successor_at uc)"
    unfolding mop_graph_succ_at_def by simp
  
  lemma(in mdp_graph) mop_has_succ[simp]: "mop_has_succ MG uc = RETURN (has_next uc)"
    unfolding mop_has_succ_def by simp
  
  lemma(in mdp_graph) mop_next_id_conv[simp]: "mop_next_id MG uc = RETURN (next_index uc)"
    unfolding mop_next_id_def by simp

end
