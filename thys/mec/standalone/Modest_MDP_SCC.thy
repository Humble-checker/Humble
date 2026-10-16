theory Modest_MDP_SCC                
  imports "../../ds/Graph"
    "../../ds/Modest_MDP_input" "../../ds/Array_Nat_Tuple_Partition" "../../mec/MDP_MEC"
begin


  section \<open>General Lemmas\<close>

    lemma empty_leading_hd_concat: "xss ! i \<noteq> [] \<Longrightarrow> (\<And> j. j < i \<Longrightarrow> xss ! j = []) \<Longrightarrow> i < length xss \<Longrightarrow> hd (concat xss) = hd (xss ! i)"
      apply(induction xss rule: rev_induct)
      subgoal by simp
      subgoal for a xss 
        apply(cases "i = length xss")
        subgoal  
          by (auto simp: in_set_conv_nth hd_append) 
        subgoal 
          by (auto simp: hd_append)
        done
      done

    lemma empty_leading_tl_concat: "xss ! i \<noteq> [] \<Longrightarrow> (\<And> j. j < i \<Longrightarrow> xss ! j = []) \<Longrightarrow> i < length xss \<Longrightarrow> tl (concat xss) = concat (xss[i := tl (xss ! i)])"
      apply(induction xss rule: rev_induct)
      subgoal by simp
      subgoal for a xss 
        apply(cases "i = length xss")
        subgoal  
          apply (clarsimp simp: tl_append split: list.splits)
          by (metis concat_eq_Nil_conv in_set_conv_nth list.distinct(1)) 
        subgoal 
          by (auto simp: tl_append list_update_append1 split: list.splits)
        done
      done

    lemma(in -) eq_Cons_hd_tl: "xs = y # ys \<Longrightarrow> y = hd xs \<and> ys = tl xs"
      by simp

  section \<open>Modest MEC Input Data Structure\<close>



  section \<open>Modest Cullable Data Structure SCC operations\<close>

  text \<open>
    The second notion adds a map to the input data structure which determines which states and 
    transitions are removed. \<open>Mm\<close> is a tuple of lists of sets. Transitions between the same
    sets are preserved while the others are removed. By putting each set into their own set we
    automatically remove the desired transitions. The tuple construction allows us to model removed
    states. The first element of the tuple contains the MECs and the second one the unfinished SCCs
    grouped per SCC. When the algorithm is done, this list therefore also contains the MEC 
    decomposition. As an optimization we included the number of remaining states \<open>Nr\<close> which is the
    a counter that keeps track of the number of states for which we have not found a MEC. We only
    use this for the termination criterion.
  \<close>    

  subsection \<open>Basic definition\<close>

  type_synonym modest_mdp = "nat list \<times> nat list \<times> nat list \<times> nat set \<times> nat set \<times> antpar \<times> nat"

  locale modest_mdp_cullable_pre =
    fixes N::nat
    fixes DS :: "modest_mdp"
  begin 
  
    definition "St = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr). St) DS"
    definition "Tr = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr). Tr) DS"
    definition "Br = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr). Br) DS"
    definition "Av = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr). Av) DS"
    definition "Ta = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr). Ta) DS"
    definition "Mm = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr). Mm) DS"
    definition "Nr = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr). Nr) DS"

    lemma DS_alt: "DS = (St,Tr,Br,Av,Ta,Mm,Nr)"
      unfolding St_def Tr_def Br_def Av_def Ta_def Mm_def Nr_def 
      apply(cases DS) by fast

  end

  lemma DS_sel_simps[simp]:
    "modest_mdp_cullable_pre.St (St,Tr,Br,Av,Ta,Mm,Nr) = St"
    "modest_mdp_cullable_pre.Tr (St,Tr,Br,Av,Ta,Mm,Nr) = Tr"
    "modest_mdp_cullable_pre.Br (St,Tr,Br,Av,Ta,Mm,Nr) = Br"
    "modest_mdp_cullable_pre.Av (St,Tr,Br,Av,Ta,Mm,Nr) = Av"
    "modest_mdp_cullable_pre.Ta (St,Tr,Br,Av,Ta,Mm,Nr) = Ta"
    "modest_mdp_cullable_pre.Mm (St,Tr,Br,Av,Ta,Mm,Nr) = Mm"
    "modest_mdp_cullable_pre.Nr (St,Tr,Br,Av,Ta,Mm,Nr) = Nr"
    unfolding modest_mdp_cullable_pre.St_def modest_mdp_cullable_pre.Tr_def modest_mdp_cullable_pre.Br_def 
      modest_mdp_cullable_pre.Av_def modest_mdp_cullable_pre.Ta_def modest_mdp_cullable_pre.Mm_def
      modest_mdp_cullable_pre.Nr_def
    by auto

  locale modest_mdp_cullable_def = modest_mdp_cullable_pre N DS + modest_mdp_input_struc_def N St Tr Br Av Ta for N DS
  begin 

    text\<open>
      To deal with the cullable data structure, we need to be able to reason about the activated
      transition. This part focuses purely on building an infrastructure to make it easier to
      reason about that.
    \<close>

    subsubsection \<open>Predicate Representation\<close>
    (*TODO Make names shorter*)
    definition "is_activated_transition u t = ( in_intv (StI ! u) t \<and> (\<forall> b. in_intv (TrI ! t) b \<longrightarrow> op_antpar_eq_set_mem Mm u (Br ! b)))"

    lemma is_activated_transitionD1: "is_activated_transition u t \<Longrightarrow> in_intv (StI ! u) t"
      unfolding is_activated_transition_def by simp

    lemma is_activated_transitionE: "is_activated_transition u t \<Longrightarrow> (in_intv (StI ! u) t \<Longrightarrow> (\<And>b. in_intv (TrI ! t) b \<Longrightarrow> op_antpar_eq_set_mem Mm u (Br ! b)) \<Longrightarrow> P) \<Longrightarrow> P"
      unfolding is_activated_transition_def by blast

    lemma is_activated_transitionI: "in_intv (StI ! u) t \<Longrightarrow> (\<And>b. in_intv (TrI ! t) b \<Longrightarrow> op_antpar_eq_set_mem Mm u (Br ! b)) \<Longrightarrow> is_activated_transition u t"
      unfolding is_activated_transition_def by blast


    lemma ex_unfiltered_index: "i < length (filter P xs) \<Longrightarrow> \<exists> j. j < length xs \<and> (filter P xs) ! i = xs ! j \<and> P (xs ! j)"
      apply(induction xs arbitrary: i)
      apply clarsimp
      subgoal for x xs i
        apply(cases i)
        subgoal
          by fastforce
        subgoal
          by fastforce
        done
      done

    subsubsection \<open>Set of activated transitions following a specified transition\<close>

    definition "activated_transitions_after u t \<equiv> {t1. t1 > t \<and> is_activated_transition u t1}"

    lemma finite_activated_transitions: "finite (activated_transitions_after u t)"
      apply (clarsimp simp: activated_transitions_after_def)
      apply (subgoal_tac "{t1. t < t1 \<and> is_activated_transition u t1} \<subseteq> sn_intv (StI ! u)")
      apply (auto simp: finite_subset dest!: is_activated_transitionD1) 
      done

    lemma activated_transitions_after_mem: "t1 \<in> activated_transitions_after u t \<longleftrightarrow> t1 > t \<and> is_activated_transition u t1"
      unfolding activated_transitions_after_def by fast

    lemma activated_transitions_after_lower: "\<forall> t1 \<in> activated_transitions_after u t. t < t1"
      using activated_transitions_after_mem
      by fastforce

    lemma activated_transitions_after_mono: "t1 \<le> t2 \<Longrightarrow> activated_transitions_after v t2 \<subseteq> activated_transitions_after v t1"
      unfolding activated_transitions_after_def by force

    lemma activated_transitions_after_upper: "\<forall> t1 \<in> activated_transitions_after u t. t1 < uid (StI ! u)"
      by (auto simp: activated_transitions_after_mem in_intv_ubD less_imp_le_nat dest!: is_activated_transitionD1)

    lemma uid_St_not_in_activated_transitions_after: "uid (StI ! u) \<notin> activated_transitions_after u t"
      using activated_transitions_after_upper by blast

    subsubsection \<open>The next transition in the list from the specified one\<close>

    definition "next_activated_transition u t = (let X = activated_transitions_after u t in 
      (if X = {} then (uid (StI ! u)) else Min (activated_transitions_after u t)))"

    lemma next_activated_transition_id: "next_activated_transition u t = uid (StI ! u) \<longleftrightarrow> activated_transitions_after u t = {}"
      unfolding next_activated_transition_def apply clarsimp 
      using uid_St_not_in_activated_transitions_after
      by (metis Min_in empty_iff finite_activated_transitions)

    lemma next_activated_transition_gt: "next_activated_transition u t < uid (StI ! u) \<longleftrightarrow> activated_transitions_after u t \<noteq> {}"
      unfolding next_activated_transition_def 
      apply (simp add: activated_transitions_after_mem finite_activated_transitions)
      by (metis Min_in activated_transitions_after_upper finite_activated_transitions)

    lemma next_activated_transition_lower: "t < uid (StI ! u) \<Longrightarrow> next_activated_transition u t > t"
      unfolding next_activated_transition_def
      apply(cases "activated_transitions_after u t = {}")
      by (auto simp add: memb_imp_not_empty modest_mdp_cullable_def.activated_transitions_after_mem modest_mdp_cullable_def.finite_activated_transitions)

    lemma next_activated_transition_lid: "next_activated_transition u t \<ge> lid (StI ! u)"
      using Min_in[OF finite_activated_transitions, of u t] activated_transitions_after_mem 
      unfolding next_activated_transition_def by (fastforce elim: is_activated_transitionE)

    lemma next_activated_transition_uid: "next_activated_transition u t \<le> uid (StI ! u)"
      unfolding next_activated_transition_def
      apply(cases "activated_transitions_after u t = {}")
      subgoal by presburger
      subgoal apply clarsimp 
        by (metis all_not_in_conv next_activated_transition_def next_activated_transition_gt order_less_imp_le)
      done

    lemma next_activated_transition_is_activated: "activated_transitions_after u t \<noteq> {} \<Longrightarrow> is_activated_transition u (next_activated_transition u t)"
      unfolding next_activated_transition_def 
      apply(subgoal_tac "Min (activated_transitions_after u t) \<in> activated_transitions_after u t")
      subgoal 
        by(auto simp: activated_transitions_after_mem)
      subgoal
        by (simp add: finite_activated_transitions)
      done

    lemma next_activated_transition_mono: "t1 \<le> t2 \<Longrightarrow> next_activated_transition v t1 \<le> next_activated_transition v t2"
      apply(frule activated_transitions_after_mono[where ?v=v])
      apply(cases "activated_transitions_after v t1 = {}")
      subgoal by (auto simp: next_activated_transition_def)
      subgoal
        apply(cases "activated_transitions_after v t2 = {}") 
        subgoal
          apply(drule next_activated_transition_is_activated) 
          using modest_mdp_cullable_def.next_activated_transition_def modest_mdp_cullable_def.next_activated_transition_uid by presburger
        subgoal 
          by (simp add: finite_activated_transitions next_activated_transition_def subset_eq)
        done
      done

    lemma next_activated_transition_no_act_pred: "t < t2 \<Longrightarrow> t2 \<le> uid (StI ! u) \<Longrightarrow> \<forall>t'>t. t' < t2 \<longrightarrow> \<not> is_activated_transition u t' \<Longrightarrow> is_activated_transition u t2 \<Longrightarrow> next_activated_transition u t = t2"
      apply(cases "activated_transitions_after u t = {}")
      subgoal
        apply(subgoal_tac "next_activated_transition u t > t")
        using next_activated_transition_gt activated_transitions_after_mem by blast+
      subgoal
        unfolding next_activated_transition_def 
        apply clarsimp
        apply(rule MinI)
        subgoal using finite_activated_transitions by presburger 
        subgoal by assumption
        subgoal using activated_transitions_after_mem by blast
        subgoal by (meson activated_transitions_after_mem linorder_le_less_linear)
        done
      done


    lemma next_activated_le_greater_activated: "is_activated_transition u t2 \<Longrightarrow> t1 < t2 \<Longrightarrow> next_activated_transition u t1 \<le> t2"
      unfolding next_activated_transition_def
      by (auto simp add: activated_transitions_after_mem next_activated_transition_gt finite_activated_transitions activated_transitions_after_mem)

    lemma activated_transitions_after_empty1: "\<forall>t1 > t. t1 < uid (StI ! u) \<longrightarrow> \<not>is_activated_transition u t1 \<Longrightarrow> activated_transitions_after u t = {}"
      unfolding activated_transitions_after_def 
      using activated_transitions_after_upper activated_transitions_after_mem by blast

    lemma activated_transitions_after_empty2: "activated_transitions_after u t = {} \<Longrightarrow> \<forall>t1 > t. t1 < uid (StI ! u) \<longrightarrow> \<not>is_activated_transition u t1"
      unfolding activated_transitions_after_def 
      using activated_transitions_after_upper activated_transitions_after_mem by blast
                                     
    lemma activated_transitions_after_empty: "activated_transitions_after u t = {} \<longleftrightarrow> (\<forall>t1 > t. t1 < uid (StI ! u) \<longrightarrow> \<not>is_activated_transition u t1)"
      using activated_transitions_after_empty1 activated_transitions_after_empty2 by blast

    lemmas next_activated_transition_eq = 
      next_activated_transition_id[unfolded activated_transitions_after_empty, symmetric]

    lemma next_activated_transition_not_act_between: "t' = next_activated_transition u t \<Longrightarrow> (\<And>i. t < i \<Longrightarrow> i < t' \<Longrightarrow> \<not> is_activated_transition u i)"
      unfolding next_activated_transition_def 
      using activated_transitions_after_empty2 
      by (auto split: if_splits simp: activated_transitions_after_mem finite_activated_transitions leD)


    subsubsection \<open>The next branch\<close>

    text \<open>
      Branches are only deactivated when their transition is deactivated. When the last 
      branch of a transition is reached, the first branch of the next activated transition is 
      selected
    \<close>

    definition "next_activated_branch u t b = (
      if Suc b < uid (TrI ! t) then 
        (t,Suc b) 
      else 
        let tn = next_activated_transition u t in (
        if tn < uid (StI ! u) then 
          (tn,lid (TrI ! tn)) 
        else 
          (tn,b)
        )
      )"

    lemma next_activated_branch_t_in_intv: "next_activated_branch u t b = (t',b') \<Longrightarrow> in_intv (StI ! u) t \<Longrightarrow> t' < uid (StI ! u) \<Longrightarrow> in_intv (StI ! u) t'"
      unfolding next_activated_branch_def
      apply (clarsimp split: if_splits simp: Let_def in_intv_def next_activated_transition_uid)
      using in_intv_def in_intv_gt next_activated_transition_lower by presburger

    lemma next_activated_branch_succ: "t < uid (StI ! u) \<Longrightarrow> b < uid (TrI ! t) \<Longrightarrow> next_activated_branch u t b = (t',b') \<Longrightarrow> 
        t' \<ge> t \<and> (if t' = t then b' = Suc b else (if t' < uid (StI ! u) then (Suc b = uid (TrI ! t) \<and> b' = lid (TrI ! t')) else t' = uid (StI ! u) \<and> b' = b))"
      unfolding next_activated_branch_def
      using next_activated_transition_lower[of t' u] 
      by (auto split: if_splits simp: Let_def next_activated_transition_uid le_antisym intro: next_activated_transition_lower less_imp_le_nat) 

    lemma next_activated_branch_same_trans: "next_activated_branch u t b = (t',b') \<Longrightarrow> Suc b < uid (TrI ! t) \<Longrightarrow> t' = t \<and> b' = Suc b"
      unfolding next_activated_branch_def by simp

    lemma next_activated_branch_not_act_between: "next_activated_branch u t b = (t',b') \<Longrightarrow> (\<And>i. t < i \<Longrightarrow> i < t' \<Longrightarrow> \<not> is_activated_transition u i)"
      unfolding next_activated_branch_def 
      by (auto split: if_splits simp: next_activated_transition_not_act_between Let_def dest!: next_activated_transition_not_act_between)

    lemma next_activated_branch_no_act_after: "next_activated_branch u t b = (t',b') \<Longrightarrow> t' = uid (StI ! u) \<Longrightarrow> activated_transitions_after u t = {}"
      unfolding next_activated_branch_def
      by(auto simp: Let_def next_activated_transition_id next_activated_transition_gt activated_transitions_after_empty 
        dest: in_intv_ubD elim: is_activated_transitionE split: if_splits) 


    definition "act_trans u = {t. is_activated_transition u t}"

    lemma act_trans_iff[iff]: "t \<in> act_trans u \<longleftrightarrow> is_activated_transition u t"
      unfolding act_trans_def by blast

    lemma in_act_transE: "t \<in> act_trans u \<Longrightarrow> (is_activated_transition u t \<Longrightarrow> P) \<Longrightarrow> P"
      unfolding act_trans_def by blast

    lemma in_act_transI: "is_activated_transition u t \<Longrightarrow> t \<in> act_trans u"
      unfolding act_trans_def by blast

    subsection \<open>Abstraction functions\<close>

    (*TODO: this is the edge adjacency function, rename K to Ea or something similar*)
    definition "K_\<alpha>' = (\<lambda> u. if u \<in> Cm then (\<Union>x\<in>act_trans u. (!) Br ` sn_intv (TrI ! x)) else {})"

    definition "S_\<alpha> = (case Mm of (Mm1,Mm2) \<Rightarrow> {v. v < N \<and> (\<forall> i < length Mm1. v \<notin> Mm1 ! i)})" \<comment> \<open>states in Mm1 are part of a discovered MEC\<close>

    definition "SK_\<alpha> = (S_\<alpha>,K_\<alpha>')"

    lemma V0_MG_\<alpha>[simp]: "mdp_graph_defs.V0 SK_\<alpha> = S_\<alpha>"
      unfolding SK_\<alpha>_def by simp

    lemma K_MG_\<alpha>[simp]: "mdp_graph_defs.K SK_\<alpha> = K_\<alpha>'"
      unfolding SK_\<alpha>_def by simp

    lemma S_\<alpha>_in_len_St: "S_\<alpha> \<subseteq> {0..< N}"
      unfolding S_\<alpha>_def
      by force


    subsection \<open>Graph structure\<close>

    abbreviation "E_\<alpha>' \<equiv> mdp_graph_defs.E_\<alpha> (S_\<alpha>,K_\<alpha>')"


  end

  locale modest_mdp_cullable_invar' = modest_mdp_cullable_def N DS + modest_mdp_input_struc_invar N St Tr Br Av Ta for N DS + 
    \<comment> \<open>Specific to the cullable MDP, keep these around as they are needed for the MEC computation\<close>
    assumes Nr_S: "Nr = card S_\<alpha>"

    assumes Mm_all_states: "v < N \<Longrightarrow> ((\<exists> i < length (fst Mm). v \<in> (fst Mm) ! i) \<or> (\<exists> i < length (snd Mm). v \<in> (snd Mm) ! i))" 
    assumes Mm_disj: "(\<forall> i < length (fst Mm). v \<notin> (fst Mm) ! i) \<or> (\<forall> i < length (snd Mm). v \<notin> (snd Mm) ! i)"

    assumes Mm1_disj: "i < length (fst Mm) \<Longrightarrow> j < length (fst Mm) \<Longrightarrow> v \<in> (fst Mm) ! i \<Longrightarrow> v \<in> (fst Mm) ! j \<Longrightarrow> i = j"
    assumes Mm2_disj: "i < length (snd Mm) \<Longrightarrow> j < length (snd Mm) \<Longrightarrow> v \<in> (snd Mm) ! i \<Longrightarrow> v \<in> (snd Mm) ! j \<Longrightarrow> i = j"

    assumes Mm1_len: "length (fst Mm) \<le> N"
    assumes Mm2_len: "length (snd Mm) = N"

    assumes Mm1_sub: "\<Union>(set (fst Mm)) \<subseteq> {0..<N}"
    assumes Mm2_sub: "\<Union>(set (snd Mm)) \<subseteq> {0..<N}"

  begin


    lemma E_\<alpha>_len_St[simp]: "E_\<alpha>' \<subseteq> {0..<N} \<times> {0..<N}"
      unfolding mdp_graph_defs.E_\<alpha>_def K_\<alpha>'_def SK_\<alpha>_def
      apply (clarsimp intro!: Br_in_bound) 
      by(auto simp: Cm_def is_activated_transitionD1 dest!: Tr_in_bound_intvD Br_in_bound_intvD intro!: Br_in_bound split: if_splits)

    lemma finite_E_\<alpha>[simp]: "finite E_\<alpha>'"
      using finite_subset[OF E_\<alpha>_len_St] by simp


    lemma finite_S_\<alpha>[simp]: "finite S_\<alpha>"
      using finite_subset[OF S_\<alpha>_in_len_St] by simp

    lemma Nr_0_empty_iff[simp]: "Nr = 0 \<longleftrightarrow> S_\<alpha> = {}"
      using Nr_S by simp

    lemma E_\<alpha>_succ_N: "E_\<alpha>' `` {0..<N} \<subseteq> {0..<N}"
      unfolding SK_\<alpha>_def K_\<alpha>'_def S_\<alpha>_def
      by (fastforce simp: mdp_graph_defs.E_\<alpha>_mem act_trans_iff split: if_splits 
        intro!: Br_in_bound Br_in_bound_intvD Tr_in_bound_intvD is_activated_transitionD1) 

    lemma E_\<alpha>_reach_N: "E_\<alpha>'\<^sup>* `` {0..<N} \<subseteq> {0..<N}"
      apply clarsimp
      subgoal for u v
        apply(induction rule: rtrancl_induct)
        using E_\<alpha>_succ_N
        by fastforce+
      done

    lemma map_ls_intv[simp]: "i < cnt sn \<Longrightarrow> map f (ls_intv sn) ! i = f (i + lid sn)"
      by simp

    lemma mdp_graph_impl_modest: "mdp_graph SK_\<alpha> {0..<N}"
      apply(unfold_locales)
      subgoal
        unfolding SK_\<alpha>_def
        using E_\<alpha>_reach_N N_DEF finite_subset by auto
      subgoal using S_\<alpha>_in_len_St[folded N_DEF] by simp
      done

    lemma succ_in_bound: 
      assumes "(u,v) \<in> E_\<alpha>'" 
      shows "v < N"
    proof -
      obtain i j where "lid (StI!u) \<le> i" and IU:"i < uid (StI!u)" and "lid (TrI!i) \<le> j" and JU:"j < uid (TrI!i)" and V_DEF: "v = Br!j" and UU: "u \<in> Cm"
        using assms 
        unfolding in_intv_def mdp_graph_defs.E_\<alpha>_def K_\<alpha>'_def SK_\<alpha>_def
        using is_activated_transitionD1 apply (clarsimp simp: act_trans_iff split: if_splits) 
        by blast
      hence "j < length Br"  
        unfolding Cm_def
        by(auto intro!: Br_in_boundD Tr_in_boundD)
      then show ?thesis 
        using Br_in_bound
        unfolding N_DEF V_DEF 
        by fast
    qed

    lemma tn_sub_lid_lt_cnt: "in_intv (StI!v) tn \<Longrightarrow> tn - lid (StI ! v) < cnt (StI ! v)"
      by(simp add: uid_as_cnt_plus_lid less_diff_conv2 in_intv_def) 

    lemma bn_sub_lid_lt_cnt: "in_intv (StI!v) tn \<Longrightarrow> in_intv (TrI!tn) bn \<Longrightarrow> bn - lid (TrI ! tn) < cnt (TrI ! tn)"
      by(simp add: uid_as_cnt_plus_lid less_diff_conv2 in_intv_def) 

    lemma state_has_transition: assumes "u < N" obtains tn where "in_intv (StI ! u) tn"
      using St_nonempty assms i_lt_cnt_ls_intv_in_intv by blast

    lemma transition_has_branch: assumes "u < N" and "in_intv (StI ! u) tn" obtains bn where "in_intv (TrI ! tn) bn"
      using assms i_lt_cnt_ls_intv_in_intv Tr_in_bound_intvD Tr_nonempty by blast

    lemma next_activated_branch_b_in_intv: "u < N \<Longrightarrow> next_activated_branch u t b = (t',b') \<Longrightarrow> in_intv (StI ! u) t \<Longrightarrow> in_intv (TrI ! t) b \<Longrightarrow> t' < uid (StI ! u) \<Longrightarrow> in_intv (TrI ! t') b'"
      unfolding next_activated_branch_def
      apply(frule in_intv_ubD)
      by (auto split: if_splits simp: Let_def next_activated_transition_uid next_activated_transition_lower intro!: Tr_nonempty Tr_in_bound_intvD next_activated_transition_uid elim: in_intv_gt) 

    lemma next_activated_branch_next_trans: "in_intv (TrI ! t) b \<Longrightarrow> next_activated_branch u t b = (t',b') \<Longrightarrow> t' < uid (StI ! u) \<Longrightarrow> t < t' \<Longrightarrow> b = uid(TrI!t) - 1 \<and> b' = lid(TrI!t')"
      unfolding next_activated_branch_def 
      by (auto split: if_splits simp: Let_def intro!: Suc_to_right Suc_lessI)

    lemma next_activated_branch_next_branch: "next_activated_branch v t b = (t',b') \<Longrightarrow> t = t' \<Longrightarrow> b' < b \<Longrightarrow> b' = Suc b"
      unfolding next_activated_branch_def
      using next_activated_transition_lower[of t v] 
      by (auto split: if_splits simp: Let_def)

    lemma next_activated_branch_activated: "next_activated_branch u t b = (t',b') \<Longrightarrow> t' < uid (StI ! u) \<Longrightarrow> is_activated_transition u t \<Longrightarrow> is_activated_transition u t'"
      unfolding next_activated_branch_def
      by (auto split: if_splits simp: Let_def next_activated_transition_gt next_activated_transition_is_activated ) 

    interpretation mdp_graph SK_\<alpha> "{0..<N}" using mdp_graph_impl_modest .

    lemma is_empty_not_activated: "u \<in> Cm \<Longrightarrow> is_empty u \<longleftrightarrow> (\<forall>x. \<not>is_activated_transition u x)"
      unfolding is_empty_def mdp_graph_defs.is_empty_def K_\<alpha>'_def K_def SK_\<alpha>_def
      apply clarsimp
      apply(rule iffI)
      subgoal 
        apply (clarsimp)
        subgoal for x
          apply(frule is_activated_transitionD1)
          apply(subgoal_tac "x\<in>act_trans u") 
          by(auto simp: Cm_def dest!: Tr_in_bound_intvD Tr_nonempty) 
        done
      subgoal 
        by (fastforce simp: K_\<alpha>'_def)
      done

  end

  locale modest_mdp_cullable_invar = modest_mdp_cullable_invar' N DS\<^sub>c for N DS\<^sub>c +
    fixes DS
    assumes DS_DEF: "DS = DS\<^sub>c"

  lemma modest_mdp_cullable_invar_alt: "DS = DS\<^sub>c \<Longrightarrow> modest_mdp_cullable_invar N DS\<^sub>c DS = modest_mdp_cullable_invar' N DS"
    unfolding modest_mdp_cullable_invar_def modest_mdp_cullable_invar_axioms_def by blast


  definition "modest_mdp_succ_DS_rel N DS\<^sub>c = br (modest_mdp_cullable_def.SK_\<alpha> N) (modest_mdp_cullable_invar N DS\<^sub>c)"

  definition "modest_mdp_succ_rel N \<equiv> { (DS,MG). (DS,MG) \<in> modest_mdp_succ_DS_rel N DS }"

  lemma modest_mdp_succ_rel_DS_eq: "(DS, K) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c \<Longrightarrow> DS = DS\<^sub>c"
    unfolding modest_mdp_succ_DS_rel_def
    by(auto simp: in_br_conv modest_mdp_cullable_invar_def modest_mdp_cullable_invar_axioms_def)

  lemma modest_mdp_succ_rel_alt: "(DS, K) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c \<longleftrightarrow> DS\<^sub>c = DS \<and> (DS, K) \<in> modest_mdp_succ_rel N"
    using modest_mdp_succ_rel_DS_eq
    unfolding modest_mdp_succ_DS_rel_def modest_mdp_succ_rel_def br_def modest_mdp_cullable_invar_def modest_mdp_cullable_invar_axioms_def 
    by auto


  subsection \<open>Successor index\<close>

  text \<open>A successor index for modest is a quintuple that contains the vertex \<open>vI\<close>, a transition 
    index \<open>tcI\<close>, the next transition index \<open>tnI\<close>, a branch index \<open>bcI\<close> and the next branch index 
    \<open>bnI\<close>. This is an implementation specifically for the SCC algorithm which needs to store 
    the progress of the DFS efficiently. We keep track of that progress by storing a stack of
    successor indices which is updated every time we progress in the DFS.\<close>
  type_synonym 'v modest_succ_index = "('v \<times> nat \<times> nat \<times> nat \<times> nat)"

  locale modest_successor_index_def = modest_mdp_cullable_def +
    fixes IDX :: "nat modest_succ_index"
  begin

    definition "vI = (\<lambda> (v,tc,tn,bc,bn). v) IDX"
    definition "tcI = (\<lambda> (v,tc,tn,bc,bn). tc) IDX"
    definition "tnI = (\<lambda> (v,tc,tn,bc,bn). tn) IDX"
    definition "bcI = (\<lambda> (v,tc,tn,bc,bn). bc) IDX"
    definition "bnI = (\<lambda> (v,tc,tn,bc,bn). bn) IDX"

    definition "Bri_\<alpha> tc \<equiv> if tc < tcI \<or> \<not>is_activated_transition vI tc then [] 
      else if tc = tcI then map ((!) Br) (ls_intv (set_lid (TrI!tc) bcI)) 
      else map ((!) Br) (ls_intv (TrI!tc))" 

    definition "Tri_\<alpha> = map Bri_\<alpha> (ls_intv (StI ! vI))"

    definition "si_\<alpha> = concat Tri_\<alpha>"

    definition "\<alpha> = (vI, si_\<alpha>)"

    definition "Brin_\<alpha> tn \<equiv> if tn < tnI \<or> \<not>is_activated_transition vI tn then [] 
      else if tn = tnI then map ((!) Br) (ls_intv (set_lid (TrI!tn) bnI)) 
      else map ((!) Br) (ls_intv (TrI!tn))" 

    definition "Trin_\<alpha> = map Brin_\<alpha> (ls_intv (StI ! vI))"

    definition "tl_si_\<alpha> = concat Trin_\<alpha>"


    definition "is_pred_index t b \<equiv> t < tcI \<or> (t = tcI \<and> b \<le> bcI)"

    definition "is_succ_index t b \<equiv> tcI < t \<or> (t = tcI \<and> bcI \<le> b)"

    lemma is_pred_index_cases[case_names Tr Br]: "is_pred_index t b \<Longrightarrow> (t < tcI \<Longrightarrow> P) \<Longrightarrow> (t = tcI \<Longrightarrow> b \<le> bcI \<Longrightarrow> P) \<Longrightarrow> P"
      unfolding is_pred_index_def by blast

    lemma is_succ_index_cases[case_names Tr Br]: "is_succ_index t b \<Longrightarrow> (tcI < t \<Longrightarrow> P) \<Longrightarrow> (t = tcI \<Longrightarrow> bcI \<le> b \<Longrightarrow> P) \<Longrightarrow> P"
      unfolding is_succ_index_def by blast

    lemma is_succ_indexI1: "tcI < t \<Longrightarrow> is_succ_index t b"
      unfolding is_succ_index_def by blast

    lemma is_succ_indexI2: "t = tcI \<Longrightarrow> bcI \<le> b \<Longrightarrow> is_succ_index t b"
      unfolding is_succ_index_def by blast

  end

  lemma modest_successor_index_simps[simp]:
    "modest_successor_index_def.vI (v,tc,tn,bc,bn) = v"
    "modest_successor_index_def.tcI (v,tc,tn,bc,bn) = tc"
    "modest_successor_index_def.tnI (v,tc,tn,bc,bn) = tn"
    "modest_successor_index_def.bcI (v,tc,tn,bc,bn) = bc"
    "modest_successor_index_def.bnI (v,tc,tn,bc,bn) = bn"
    unfolding modest_successor_index_def.vI_def modest_successor_index_def.tcI_def modest_successor_index_def.tnI_def
      modest_successor_index_def.bcI_def modest_successor_index_def.bnI_def by auto

  subsubsection \<open>Invariant\<close>

  locale modest_successor_index_invar = modest_successor_index_def N DS IDX + modest_mdp_cullable_invar' N DS for N DS IDX +
    assumes TBOUNDS: "tcI < uid (StI ! vI)" \<comment> \<open>The current transition index is in range of the state's interval.\<close>
    and BCUPP: "bcI < uid (TrI ! tcI)" \<comment> \<open>The current branch index is in range of the transition's interval.\<close>
    and NB: "next_activated_branch vI tcI bcI = (tnI, bnI)" \<comment> \<open>\<open>tnI\<close> and \<open>bnI\<close> represent the next transition and branch index.\<close>
    and TLOW: "lid (StI ! vI) \<le> tcI" \<comment> \<open>The current transition index is in range of the state's interval.\<close>
    and BCLOW: "lid (TrI ! tcI) \<le> bcI" \<comment> \<open>The current branch index is in range of the transition's interval.\<close>
    and BNLOW: "tnI < uid (StI ! vI) \<Longrightarrow> lid (TrI ! tnI) \<le> bnI" \<comment> \<open>If the next transition is in range, its branch is greater than the lower bound.\<close>
    and VCM: "vI \<in> Cm"  \<comment> \<open>vI is a state that is neither a target nor avoid state.\<close>
    and ACT: "is_activated_transition vI tcI" \<comment> \<open>the transition is activated.\<close>
    and ACTN: "tnI < uid (StI ! vI) \<Longrightarrow> is_activated_transition vI tnI" \<comment> \<open>the next index is activated if the current one is not the last index.\<close>
  begin (*TODO: Update these to not contain StI and TrI*)

    lemma VBOUND: "vI < N"
      using VCM unfolding Cm_def by simp

    lemma NAV: "vI \<notin> Av"
      using VCM unfolding Cm_def by simp

    lemma NTA: "vI \<notin> Ta" 
      using VCM unfolding Cm_def by simp

    lemma TBOUND: "tcI \<le> tnI"
      using ACT BCUPP NB modest_mdp_cullable_def.is_activated_transitionD1 modest_mdp_cullable_def.next_activated_branch_succ by blast

    lemma TUPP: "tnI \<le> uid (StI ! vI)" 
      by (metis ACT BCUPP NB in_intv_bounds is_activated_transitionD1 less_or_eq_imp_le next_activated_branch_succ)
  
    lemma BNUPP: "tnI < uid (StI ! vI) \<Longrightarrow> bnI < uid (TrI ! tnI)" 
      using ACT BCLOW BCUPP NB VBOUND in_intvI is_activated_transitionD1 next_activated_branch_b_in_intv N_DEF by blast

    lemma in_intv_tcI[simp, intro!]: "in_intv (StI ! vI) tcI"
      unfolding in_intv_def
      using TBOUND TUPP TLOW TBOUNDS by blast

    lemma in_intv_tnI[simp, intro!]: "tnI < uid (StI ! vI) \<Longrightarrow> in_intv (StI ! vI) tnI"
      unfolding in_intv_def
      using TBOUND TUPP TLOW by simp

    lemma in_intv_bcI[simp, intro!]: "in_intv (TrI ! tcI) bcI"
      unfolding in_intv_def
      using BCUPP BCLOW by simp

    lemma in_intv_bnI[simp, intro!]: "tnI < uid (StI ! vI) \<Longrightarrow> in_intv (TrI ! tnI) bnI"
      unfolding in_intv_def
      using BNUPP BNLOW by simp

    lemma ls_intv_nth_eq_tcI[simp]: "ls_intv (StI ! vI) ! (tcI - lid (StI ! vI)) = tcI"
      using ACT in_intv_nth is_activated_transition_def by blast

    lemma ls_intv_nth_eq_bcI[simp]: "ls_intv (TrI ! tcI) ! (bcI - lid (TrI ! tcI)) = bcI"
      by(auto intro: in_intv_nth)

    lemma ls_intv_nth_eq_tnI[simp]: "tnI < uid (StI ! vI) \<Longrightarrow> ls_intv (StI ! vI) ! (tnI - lid (StI ! vI)) = tnI"
      using ACTN in_intv_nth is_activated_transition_def by blast

    lemma ls_intv_nth_eq_bnI[simp]: "tnI < uid (StI ! vI) \<Longrightarrow> ls_intv (TrI ! tnI) ! (bnI - lid (TrI ! tnI)) = bnI"
      by(auto intro: in_intv_nth)

    lemma tcI_act_trans[simp, intro!]: "tcI \<in> act_trans vI"
      unfolding act_trans_def using ACT by blast

    lemma tnI_act_trans[simp, intro!]: "tnI < uid (StI ! vI) \<Longrightarrow> tnI \<in> act_trans vI"
      unfolding act_trans_def using ACTN by blast

    lemma tn_eq_tc_dest: "tnI = tcI \<Longrightarrow> tnI < uid (StI ! vI)" "tcI = tnI \<Longrightarrow> tnI < uid (StI ! vI)"
      using TBOUNDS by presburger+

    lemma ls_intv_nth_tcI_id_val[dest]: "ls_intv (StI ! vI) ! i = tcI \<Longrightarrow> i < cnt (StI ! vI) \<Longrightarrow> i = (tcI - lid (StI ! vI))" 
    proof(rule ccontr)
      assume A: "i < cnt (StI ! vI)" and B: "ls_intv (StI ! vI) ! i = tcI" and C: "i \<noteq> tcI - lid (StI ! vI)"
      moreover have D: "distinct (ls_intv (StI ! vI))" by simp
      moreover have E: "tcI - lid (StI ! vI) < cnt (StI ! vI)" 
        using ACT is_activated_transitionD1 tn_sub_lid_lt_cnt by blast
      ultimately show False using nth_eq_iff_index_eq[OF D, simplified, OF A E] 
        by force
    qed

    lemma ls_intv_nth_bcI_id_val[dest]: "ls_intv (TrI ! tcI) ! i = bcI \<Longrightarrow> i < cnt (TrI ! tcI) \<Longrightarrow> i = (bcI - lid (TrI ! tcI))" 
    proof(rule ccontr)
      assume A: "i < cnt (TrI ! tcI)" and B: "ls_intv (TrI ! tcI) ! i = bcI" and C: "i \<noteq> bcI - lid (TrI ! tcI)"
      moreover have D: "distinct (ls_intv (TrI ! tcI))" by simp
      moreover have E: "bcI - lid (TrI ! tcI) < cnt (TrI ! tcI)"
        using VBOUND bn_sub_lid_lt_cnt 
        using in_intv_bcI in_intv_tcI 
        using ACT is_activated_transitionD1 by blast
      ultimately show False using nth_eq_iff_index_eq[OF D, simplified, OF A E] 
        by force
    qed

    lemma ls_intv_nth_tnI_id_val[dest]: "ls_intv (StI ! vI) ! i = tnI \<Longrightarrow> i < cnt (StI ! vI) \<Longrightarrow> i = (tnI - lid (StI ! vI))" 
    proof(rule ccontr)
      assume A: "i < cnt (StI ! vI)" and B: "ls_intv (StI ! vI) ! i = tnI" and C: "i \<noteq> tnI - lid (StI ! vI)"
      moreover have D: "distinct (ls_intv (StI ! vI))" by simp
      moreover have E: "tcI - lid (StI ! vI) < cnt (StI ! vI)" 
        using ACT is_activated_transitionD1 tn_sub_lid_lt_cnt by blast
      ultimately show False using nth_eq_iff_index_eq[OF D, simplified, OF A E] 
        by force
    qed

    lemma ls_intv_nth_bnI_id_val[dest]: "ls_intv (TrI ! tnI) ! i = bnI \<Longrightarrow> i < cnt (TrI ! tnI) \<Longrightarrow> i = (bnI - lid (TrI ! tnI))" 
    proof(rule ccontr)
      assume A: "i < cnt (TrI ! tnI)" and B: "ls_intv (TrI ! tnI) ! i = bnI" and C: "i \<noteq> bnI - lid (TrI ! tnI)"
      moreover have D: "distinct (ls_intv (TrI ! tnI))" by simp
      moreover have E: "bnI - lid (TrI ! tnI) < cnt (TrI ! tnI)"
        using VBOUND bn_sub_lid_lt_cnt 
        using in_intv_bnI in_intv_tnI 
        using ACT is_activated_transitionD1
        using B calculation(1) by force
      ultimately show False using nth_eq_iff_index_eq[OF D, simplified, OF A E] 
        by force
    qed

    lemma tc_sub_lid_lt_cnt[simp]: "tcI - lid (StI ! vI) < cnt (StI ! vI)"
      using tn_sub_lid_lt_cnt[OF in_intv_tcI] .

    lemma bc_sub_lid_lt_cnt[simp]: "bcI - lid (TrI ! tcI) < cnt (TrI ! tcI)"
      using bn_sub_lid_lt_cnt[OF in_intv_tcI in_intv_bcI] .

    lemma tn_sub_lid_lt_cnt[simp]: "tnI < uid (StI ! vI) \<Longrightarrow> tnI - lid (StI ! vI) < cnt (StI ! vI)"
      using tn_sub_lid_lt_cnt[OF in_intv_tnI] .

    lemma bn_sub_lid_lt_cnt[simp]: "tnI < uid (StI ! vI) \<Longrightarrow> bnI - lid (TrI ! tnI) < cnt (TrI ! tnI)"
      using bn_sub_lid_lt_cnt[OF in_intv_tnI in_intv_bnI] .

    lemma teI_bound: "tnI \<le> length Tr - Suc 0" 
      using Tr_in_bound_intvD VBOUND in_intv_tnI
      using St_in_bound TUPP dual_order.trans 
      by fastforce

    lemma teI_bound_strict: "tnI < uid (StI ! vI) \<Longrightarrow> tnI < length Tr - Suc 0" 
      using Tr_in_bound_intvD VBOUND in_intv_tnI by blast

    lemma tcI_bound: "tcI < length Tr - Suc 0"
      using Tr_in_bound_intvD VBOUND in_intv_tcI by blast

    lemma beI_bound: "bnI < length Br" 
      using Br_in_bound_intvD in_intv_bnI less_or_eq_imp_le teI_bound 
      by (metis BCUPP NB TBOUNDS Tr_in_bound_intvD VBOUND in_intv_bcI in_intv_tcI next_activated_branch_succ teI_bound_strict)

    lemma bcI_bound: "bcI < length Br"
      using Br_in_bound_intvD in_intv_bcI tcI_bound by blast

    lemma lid_lt_uid_tc: "lid (TrI ! tcI) < uid (TrI ! tcI)"
      using BCLOW BCUPP by auto

    lemma lid_lt_uid_tn: "tnI < uid (StI ! vI) \<Longrightarrow> lid (TrI ! tnI) < uid (TrI ! tnI)"
      using BNLOW BNUPP by auto

    lemma I1: "tcI = tnI \<Longrightarrow> (bnI > 0 \<and> bcI = bnI - 1)" 
      by (metis BCUPP NB TBOUNDS diff_Suc_1 next_activated_branch_succ zero_less_Suc)

    lemma I2: "tnI = uid (StI ! vI) \<Longrightarrow> bcI = bnI \<and> tcI < tnI \<and> bnI = uid (TrI ! tcI) - 1"
      using ACT BCUPP NB in_intv_def is_activated_transitionD1 next_activated_branch_succ
      by (metis Suc_lessI diff_Suc_1 less_irrefl next_activated_branch_same_trans )


    lemma I3: "tcI < tnI \<Longrightarrow> tnI < uid (StI ! vI) \<Longrightarrow> bcI = uid (TrI ! tcI) - 1 \<and> bnI = lid (TrI ! tnI)"
      using BCLOW BCUPP NB in_intvI next_activated_branch_next_trans by blast

    lemma I3': "tnI \<noteq> tcI \<Longrightarrow> tnI < uid (StI ! vI) \<Longrightarrow> bcI = uid (TrI ! tcI) - 1 \<and> bnI = lid (TrI ! tnI)"
      using I3 TBOUND by auto

    lemma Bri_\<alpha>_tcI_ne: "Bri_\<alpha> tcI \<noteq> []"
      unfolding Bri_\<alpha>_def
      using ACT by auto

    lemma ne_si_\<alpha>: "si_\<alpha> \<noteq> []"
      unfolding si_\<alpha>_def Tri_\<alpha>_def
      using Bri_\<alpha>_tcI_ne ACT by auto

    lemma hd_si_\<alpha>: "hd si_\<alpha> = Br!bcI"
      unfolding si_\<alpha>_def
      apply(subst empty_leading_hd_concat[where ?i="tcI - lid (StI ! vI)"])
      subgoal unfolding Tri_\<alpha>_def 
        by (auto simp: Bri_\<alpha>_tcI_ne)
      subgoal 
        unfolding Tri_\<alpha>_def 
        apply(subst nth_map)
        subgoal by (auto intro!:less_trans[OF _ tc_sub_lid_lt_cnt])
        subgoal unfolding Bri_\<alpha>_def 
          using basic_trans_rules(19) by fastforce
        done
      subgoal unfolding Tri_\<alpha>_def
        by (auto intro!: pos_cnt_set_lid simp: hd_ls_intv_set_lid[OF BCUPP])
      subgoal unfolding Tri_\<alpha>_def Bri_\<alpha>_def
        apply clarsimp
        apply(subst hd_map)
        by (auto simp: ACT hd_ls_intv_set_lid[OF BCUPP] intro!: pos_cnt_set_lid)
      done

    lemma Brin_\<alpha>_tcI_ne: "tnI < uid (StI ! vI) \<longleftrightarrow> Brin_\<alpha> tnI \<noteq> []"
      unfolding Brin_\<alpha>_def
      using ACTN is_activated_transitionD1 by auto

    lemma ne_tl_si_\<alpha>: "tnI < uid (StI ! vI) \<Longrightarrow> tl_si_\<alpha> \<noteq> []"
      unfolding tl_si_\<alpha>_def Trin_\<alpha>_def
      using Brin_\<alpha>_tcI_ne ACTN by auto

    lemma empty_tl_si_\<alpha>: "tnI = uid (StI ! vI) \<Longrightarrow> tl_si_\<alpha> = []"
      unfolding tl_si_\<alpha>_def Trin_\<alpha>_def
      apply clarsimp using Brin_\<alpha>_tcI_ne 
      using Brin_\<alpha>_def in_intv_ubD by presburger

    lemma hd_tl_si_\<alpha>: "tnI < uid (StI ! vI) \<Longrightarrow> hd tl_si_\<alpha> = Br!bnI"
      unfolding tl_si_\<alpha>_def Trin_\<alpha>_def Brin_\<alpha>_def
      apply(subst empty_leading_hd_concat[where ?i="tnI - lid (StI ! vI)"])
      subgoal 
        by (auto simp: ACTN in_intv_lbD intro!: pos_cnt_set_lid)
      subgoal apply(subst nth_map)
        subgoal by (auto intro!:less_trans[OF _ tn_sub_lid_lt_cnt])
        subgoal using basic_trans_rules(19) by fastforce
        done
      subgoal 
        by (auto intro!: pos_cnt_set_lid simp: hd_ls_intv_set_lid[OF BCUPP])
      subgoal
        using TBOUND TLOW apply clarsimp
        apply(subst hd_map)
        by (auto simp: ACTN hd_ls_intv_set_lid[OF BNUPP] intro!: pos_cnt_set_lid)
      done


    lemma length_Trin_\<alpha>: "length Trin_\<alpha> = length Tri_\<alpha>"
      unfolding Trin_\<alpha>_def Tri_\<alpha>_def by simp

    lemma length_Tri_\<alpha>: "length Tri_\<alpha> = cnt (StI ! vI)"
      unfolding Tri_\<alpha>_def by simp


    lemma Trin_\<alpha>_nth_eq_upd_Tri_\<alpha>:
      fixes itcI
      defines "itcI \<equiv> tcI - lid (StI ! vI)" 
      assumes IC: "i < cnt (StI ! vI)"
      shows "Trin_\<alpha> ! i = Tri_\<alpha>[itcI := tl (Tri_\<alpha> ! (itcI))] ! i"
    proof(cases "tnI = uid (StI ! vI)")
      case True
      note [simp] = True
      with I2 have [simp]:  "bcI = bnI" "uid (TrI ! tcI) = Suc bnI" and "tcI < tnI"
        using BCUPP by auto 

      have NAA: "i > itcI \<Longrightarrow> \<not>is_activated_transition vI (i + lid (StI ! vI))"
        using next_activated_branch_no_act_after[OF NB True]
        unfolding activated_transitions_after_def itcI_def by auto

      consider (le)"i < itcI" | (eq) "i = itcI" | (ge) "i > itcI"
        by linarith

      hence "Tri_\<alpha>[itcI := tl (Tri_\<alpha> ! (itcI))] ! i = []"
        apply(cases)
        subgoal
          unfolding Tri_\<alpha>_def Bri_\<alpha>_def
          using IC by(auto simp: itcI_def)
        subgoal
          unfolding Tri_\<alpha>_def Bri_\<alpha>_def
          using IC TLOW by(auto simp: itcI_def)
        subgoal
          unfolding Tri_\<alpha>_def Bri_\<alpha>_def
          using IC itcI_def length_ls_intv tc_sub_lid_lt_cnt NAA
          by force
        done

      moreover have "Trin_\<alpha> ! i = []" unfolding Trin_\<alpha>_def Brin_\<alpha>_def
        apply(subst nth_map)
        using IC apply simp
        using IC by (auto simp: uid_as_cnt_plus_lid)

      ultimately show ?thesis
        by presburger
    next
      case False

      define itnI where "itnI \<equiv> tnI - lid (StI ! vI)" 
      have toI1:"tnI \<noteq> tcI \<Longrightarrow> itcI < itnI"
        unfolding itcI_def itnI_def using TBOUND TLOW by linarith

      have itcIC: "itcI < cnt (StI ! vI)"
        by (simp add: assms(1))

      have ILE: "itcI \<le> itnI"
        unfolding itcI_def itnI_def using TBOUND by simp

      have itnIC: "itnI \<le> cnt (StI ! vI)"
        using TUPP itnI_def nat_less_le tn_sub_lid_lt_cnt by force

      have TLU: "tnI < uid (StI ! vI)"
        using False TUPP by simp


      consider (le)"i < itcI" | (eq) "i = itcI" | (ge) "i > itcI"
        by linarith
      thus ?thesis
      proof(cases)
        case le

        moreover have BLE: "i < itcI \<Longrightarrow> Brin_\<alpha> (ls_intv (StI ! vI) ! i) = []"
        proof -
          assume "i < itcI"
          moreover have "i < itnI \<Longrightarrow> Brin_\<alpha> (ls_intv (StI ! vI) ! i) = []"
            unfolding Brin_\<alpha>_def itnI_def
            using assms(2) by auto
          ultimately show ?thesis
            using ILE by linarith
        qed
        moreover have  BLEN: "i < itcI \<Longrightarrow> Bri_\<alpha> (ls_intv (StI ! vI) ! i) = []"
          unfolding Bri_\<alpha>_def itcI_def
          using assms(2) by auto
        ultimately show ?thesis unfolding Trin_\<alpha>_def Tri_\<alpha>_def   
          using BLE BLEN itcIC by auto

      next
        case eq
        note [simp] = eq

        show ?thesis
          unfolding Trin_\<alpha>_def Tri_\<alpha>_def
          using IC BCUPP I1 I3' BNUPP TLU TBOUND 
          apply (clarsimp simp: TLOW assms(1))
          unfolding Brin_\<alpha>_def Bri_\<alpha>_def
          by(auto split: if_splits simp: map_tl[symmetric])

      next
        case ge

        have NE: "i \<noteq> itcI"
          using ge by blast


        show ?thesis 
        proof(cases "tnI = tcI")
          case True
          hence "itnI = itcI"
            using assms(1) itnI_def by argo
          thus ?thesis 
            unfolding Trin_\<alpha>_def Tri_\<alpha>_def Brin_\<alpha>_def Bri_\<alpha>_def
            using NE by (auto simp: IC True itnI_def)

        next
          case False

          then show ?thesis 
            unfolding Trin_\<alpha>_def Tri_\<alpha>_def Brin_\<alpha>_def Bri_\<alpha>_def
            using TBOUND IC NE I3'[OF False TLU] 
            next_activated_branch_not_act_between[OF NB]
            by (auto simp: itcI_def)
        qed

      qed
    qed


    lemma tl_si_\<alpha>_eq: "tl_si_\<alpha> = tl si_\<alpha>"
      unfolding si_\<alpha>_def tl_si_\<alpha>_def
      apply(subst empty_leading_tl_concat[where ?i="tcI-lid (StI ! vI)"])
      subgoal by (auto intro!: pos_cnt_set_lid simp: ACT Tri_\<alpha>_def Bri_\<alpha>_def )
      subgoal 
        unfolding Tri_\<alpha>_def Bri_\<alpha>_def
        apply(subst nth_map)
        subgoal by (auto intro!:less_trans[OF _ tc_sub_lid_lt_cnt])
        subgoal using basic_trans_rules(19) by fastforce
        done
      subgoal by (auto simp: Tri_\<alpha>_def Bri_\<alpha>_def )
      subgoal 
        apply(rule arg_cong[where ?f = concat])
        apply(rule nth_equalityI)

        by(auto simp: length_Trin_\<alpha> length_Tri_\<alpha> intro!: Trin_\<alpha>_nth_eq_upd_Tri_\<alpha>)                           
      done

    lemma Bri_\<alpha>_next:  "modest_successor_index_def.Bri_\<alpha> DS (vI, tnI, tn', bnI, bn') = Brin_\<alpha>"
      unfolding modest_successor_index_def.Bri_\<alpha>_def Brin_\<alpha>_def
      by auto

    lemma Tri_\<alpha>_next: "modest_successor_index_def.Tri_\<alpha> DS (vI, tnI, tn', bnI, bn') = Trin_\<alpha>"
      unfolding modest_successor_index_def.Tri_\<alpha>_def Trin_\<alpha>_def
      using Bri_\<alpha>_next by force

    lemma si_\<alpha>_next: "modest_successor_index_def.si_\<alpha> DS (vI,tnI,tn',bnI,bn') = tl_si_\<alpha>"
      unfolding modest_successor_index_def.si_\<alpha>_def tl_si_\<alpha>_def
      using Tri_\<alpha>_next by presburger


    lemma "tnI < uid (StI ! vI) \<Longrightarrow> length si_\<alpha> > Suc 0"
      using ne_si_\<alpha> ne_tl_si_\<alpha> apply (clarsimp simp: neq_Nil_conv)  
      by (auto simp: neq_Nil_conv simp flip: tl_si_\<alpha>_eq dest: eq_Cons_hd_tl)

    lemma assumes L1: "length si_\<alpha> > Suc 0" shows "tnI < uid (StI ! vI)"
    proof -

      from L1 have "length tl_si_\<alpha> > 0"
        using tl_si_\<alpha>_eq by simp

      hence "tl_si_\<alpha> \<noteq> []"
        by blast

      hence "tnI \<noteq> uid (StI ! vI)"
        using empty_tl_si_\<alpha>
        by presburger

      thus ?thesis
        using TUPP by simp
    qed

    lemma length_si_\<alpha>_has_next: "length si_\<alpha> > Suc 0 \<longleftrightarrow> tnI < uid (StI ! vI)"
    proof(rule iffI)
      assume "Suc 0 < length si_\<alpha>"

      hence "length tl_si_\<alpha> > 0"
        using tl_si_\<alpha>_eq by simp

      hence "tl_si_\<alpha> \<noteq> []"
        by blast

      hence "tnI \<noteq> uid (StI ! vI)"
        using empty_tl_si_\<alpha>
        by presburger

      thus "tnI < uid (StI ! vI)"
        using TUPP by simp
    next
      show "tnI < uid (StI ! vI) \<Longrightarrow> Suc 0 < length si_\<alpha>"
        using ne_si_\<alpha> ne_tl_si_\<alpha> apply (clarsimp simp: neq_Nil_conv)  
        by (auto simp: neq_Nil_conv simp flip: tl_si_\<alpha>_eq dest: eq_Cons_hd_tl)
    qed

    lemma set_Bri_\<alpha>D: "u \<in> set (Bri_\<alpha> t) \<Longrightarrow> is_activated_transition vI t"
      unfolding Bri_\<alpha>_def by (auto split: if_splits)

    lemma Bri_\<alpha>_set_img_Br: "in_intv (StI ! vI) t \<Longrightarrow> u \<in> set (Bri_\<alpha> t) \<Longrightarrow> u \<in> (!) Br ` sn_intv (TrI ! t)"
      unfolding Bri_\<alpha>_def using BCLOW BCUPP 
      by (auto split: if_splits intro!: in_intvI image_sn_intv elim!: in_intv_smaller_set_lid) 

    lemma Br_in_Bri_\<alpha>_succ_tr: "is_succ_index t b \<Longrightarrow> is_activated_transition vI t \<Longrightarrow> in_intv (TrI ! t) b
      \<Longrightarrow> Br ! b \<in> set (Bri_\<alpha> t)"
      apply(erule is_succ_index_cases)
      subgoal
        unfolding Bri_\<alpha>_def
        by (auto)
      subgoal
        unfolding Bri_\<alpha>_def
        by (auto intro!: image_sn_intv elim!: in_intv_le_set_lid) 
      done

    lemma si_\<alpha>_to_K_\<alpha>: "u \<in> set si_\<alpha> \<Longrightarrow> u \<in> K_\<alpha>' vI"
      unfolding K_\<alpha>'_def si_\<alpha>_def Tri_\<alpha>_def
      using VCM
      apply clarsimp
      by (auto simp: act_trans_def intro: set_Bri_\<alpha>D elim: Bri_\<alpha>_set_img_Br)

    lemma K_\<alpha>_to_si_\<alpha>: 
      assumes K: "u \<in> K_\<alpha>' vI"
      assumes NACT: "\<And>t. in_intv (StI ! vI) t \<Longrightarrow> t < tcI \<Longrightarrow> \<not>is_activated_transition vI t"
      assumes BC[simp]: "bcI = lid (TrI ! tcI)"
      shows "u \<in> set si_\<alpha>"
    proof -

      have AUX1: "is_succ_index t b" if "is_activated_transition vI t" and "in_intv (TrI ! t) b" for t b
      proof(cases "t = tcI")
        case True
        note [simp] = True

        then show ?thesis
        using that by (auto intro!: is_succ_indexI2)
      next
        case False
        hence "tcI < t" 
          using NACT[of t] that(1) is_activated_transitionD1 by force
        then show ?thesis 
          by(auto intro: is_succ_indexI1)
      qed

      show ?thesis
        using K
        unfolding K_\<alpha>'_def si_\<alpha>_def Tri_\<alpha>_def
        apply (clarsimp split: if_splits simp: act_trans_iff )
        subgoal for t b
          using AUX1[THEN Br_in_Bri_\<alpha>_succ_tr, of t b, simplified] apply clarsimp 
          using is_activated_transitionD1 sn_intv_member by blast
        done
    qed
  end


  subsubsection \<open>Successor index refinement relation\<close>
  definition "modest_succ_index_DS_rel N DS = br (modest_successor_index_def.\<alpha> DS) (modest_successor_index_invar N DS)"

  definition "modest_succ_index_rel N = {(ci,c). \<exists>DS. (ci,c) \<in> modest_succ_index_DS_rel N DS}"

  lemma modest_succ_index_rel_vD: "((v,tc,te,bc,be), v',si) \<in> modest_succ_index_DS_rel N DS \<Longrightarrow> v'=v"
    by(auto simp: modest_succ_index_DS_rel_def in_br_conv modest_successor_index_def.\<alpha>_def)
  
  subsection \<open>Concrete Operations for Indices\<close>

  context modest_mdp_cullable_def
  begin

    interpretation disj_set_list_tuple_defs .

    definition "get_successor_of_branch b =
      do{ 
        ASSERT(b < length Br);
        let r = Br ! b;
        ASSERT (r < N);
        let r = op_bound_val (\<lambda> x. x < N) r;
        RETURN r
      }"


    definition "modest_eq_set_mem = (\<lambda> v w. do {
      RETURN (op_antpar_eq_set_mem Mm v w)
    })"

    definition "modest_valid_branch = (\<lambda> v b. do {
      w \<leftarrow> get_successor_of_branch b;
      ASSERT(w < N);
      modest_eq_set_mem v w
    })"

    definition "modest_is_activated v t = do {
      ASSERT(Suc t < length Tr \<and> t < length Tr);
      let bl = Tr ! t;
      let bu = Tr ! (Suc t);
      (res,b) \<leftarrow> WHILEIT (\<lambda> (flag,b). bl \<le> b \<and> b \<le> bu \<and> (flag \<longleftrightarrow> (\<forall> b'. bl \<le> b' \<longrightarrow> b' < b \<longrightarrow> op_antpar_eq_set_mem Mm v (Br ! b')))) 
          (\<lambda> (flag,b). b < bu \<and> flag) (\<lambda> (flag,b). do {
        g \<leftarrow> modest_valid_branch v b;
      if g then do{
        ASSERT (Suc b \<le> bu);
        RETURN (flag, Suc b) 
      }
      else do{
        ASSERT (Suc b \<le> bu);
        RETURN (False, Suc b)
      }
      }) (True, bl);
      RETURN res
    }"

    definition "modest_get_next_activated v t\<^sub>0 = do{
        ASSERT(Suc v < length St);
        let tu = St ! (Suc v);
        ASSERT(Suc t\<^sub>0 \<le> tu);
        (flag,t) \<leftarrow> WHILEIT (\<lambda> (flag,t). t\<^sub>0 < t \<and> t \<le> tu \<and> (\<forall> t'. t\<^sub>0 < t' \<longrightarrow> t' < t \<longrightarrow> \<not>is_activated_transition v t') \<and> (is_activated_transition v t \<or> flag)) 
            (\<lambda> (flag,t). t < tu \<and> flag) (\<lambda> (flag,t). do {
          g \<leftarrow> modest_is_activated v t;
          if g then 
            RETURN (False,t)
          else do {
            ASSERT (Suc t \<le> tu);
            RETURN (flag, Suc t) 
          }
        }) (True,Suc t\<^sub>0);
        if flag then
          RETURN tu
        else
          RETURN t
      }"

    definition "modest_calculate_successor v t b = do {
      ASSERT(Suc b \<le> length Br);
      let bn = Suc b;
      ASSERT(Suc t < length Tr);
      if (bn < Tr ! (Suc t)) 
      then do {
        RETURN (t,bn)
      } else do {
        tn \<leftarrow> modest_get_next_activated v t;
        ASSERT(Suc v < length St);
        if(tn < St ! (Suc v)) then do{
          ASSERT (tn < length Tr);
          RETURN (tn, Tr ! tn) 
        } else
          RETURN (tn,b)
      }
    }"

    (*TODO: Optimization: It would be more efficient if we could use this as a constructor of the initial index somehow *)
    definition "modest_any_activated u = do {
      ASSERT(u < length St);
      let t = St ! u;
      g \<leftarrow> modest_is_activated u t;
      if g then
        RETURN True
      else do{
        tn \<leftarrow> modest_get_next_activated u t;
        ASSERT(Suc u < length St);
        RETURN (tn < St ! (Suc u))
      }
    }"

    definition "modest_is_disabled_transitions u \<longleftrightarrow> u \<in> Av \<or> u \<in> Ta"

    definition "modest_activated_transition_in_scc = (\<lambda> (C,V) u t. do{
      let flag = True;
      ASSERT (t < length Tr);
      let bl = Tr ! t;
      ASSERT (Suc t < length Tr);
      let bu = Tr ! (Suc t);
      ASSERT(\<exists> i < length C. u \<in> C ! i); 
      ui \<leftarrow> mop_get_index_unbounded C u;
      (flag,b) \<leftarrow> WHILEIT (\<lambda> (flag,b). bl \<le> b \<and> b \<le> bu \<and> (flag \<longleftrightarrow> (\<forall>b' i. i < length C \<longrightarrow> bl \<le> b' \<longrightarrow> b' < b \<longrightarrow> (Br ! b' \<in> C ! i \<longleftrightarrow> u \<in> C ! i)))) (\<lambda> (flag,b). b < bu \<and> flag) (\<lambda> (flag,b). do {
        v \<leftarrow> get_successor_of_branch b;
        ASSERT(\<exists> i < length C. v \<in> C ! i); 
        vi \<leftarrow> mop_get_index_unbounded C v;
        ASSERT(Suc b \<le> length Br);
        RETURN (ui = vi, Suc b)
      }) (flag, bl);
      RETURN flag
    })"
  
    definition "modest_iterate_succs_eq_scc = (\<lambda> (C,V) u. do{
      if modest_is_disabled_transitions u then
        RETURN True
      else do{
        let flag = True;
        ASSERT(u < length St);
        let tl = St ! u;
        ASSERT(Suc u < length St);
        let tu = St ! (Suc u);
        (flag,t) \<leftarrow> WHILEIT (\<lambda> (flag,t). tl \<le> t \<and> t \<le> tu \<and> (flag \<longleftrightarrow> (\<forall>t' \<in> (act_trans u). tl \<le> t' \<longrightarrow> t' < t \<longrightarrow> (\<forall>b \<in> sn_intv (TrI!t'). \<forall> i < length C. (Br ! b \<in> C ! i \<longleftrightarrow> u \<in> C ! i))))) (\<lambda> (flag,t). t < tu \<and> flag) 
        (\<lambda> (flag, t). do {
          g \<leftarrow> modest_is_activated u t;
          ASSERT(Suc t \<le> length Tr);
          if g then do {
            flag \<leftarrow> modest_activated_transition_in_scc (C,V) u t;
            RETURN (flag, Suc t)
          } else 
            RETURN (flag, Suc t)
        }) (flag, tl);
        RETURN flag
      }
    })"

  end


  context modest_mdp_cullable_invar'
  begin

    lemma get_successor_of_branch_refine:
      assumes "b < length Br"
      shows "get_successor_of_branch b \<le> SPEC (\<lambda> r. r = Br ! b)"
      unfolding get_successor_of_branch_def
      apply(refine_vcg)
      using Br_in_bound assms 
      apply(auto simp: N_DEF)
      done


    lemma modest_eq_set_mem_refine:
      "v < N \<Longrightarrow> w < N \<Longrightarrow> modest_eq_set_mem v w \<le> RETURN (op_antpar_eq_set_mem Mm v w)"
      unfolding modest_eq_set_mem_def
      apply(refine_vcg) 
      using N_DEF by auto

    lemma modest_valid_branch_refine: 
      "v < N \<Longrightarrow> b < length Br \<Longrightarrow> modest_valid_branch v b \<le> RETURN (op_antpar_eq_set_mem Mm v (Br ! b))"
      unfolding modest_valid_branch_def mop_bound_val_def
      apply(refine_vcg get_successor_of_branch_refine modest_eq_set_mem_refine[THEN order_trans])
      subgoal using Br_in_bound N_DEF by blast
      subgoal using N_DEF by fastforce
      done

    lemma modest_is_activated_correct: "v < N \<Longrightarrow> in_intv (StI ! v) t \<Longrightarrow> modest_is_activated v t \<le> RETURN (is_activated_transition v t)"
      unfolding modest_is_activated_def modest_mdp_cullable_def.modest_is_activated_def 
      apply(refine_vcg WHILEIT_rule[where ?R = "less_than_bool <*lex*> (greater_bounded (uid(TrI!t)))"] modest_valid_branch_refine[THEN order_trans] )
      subgoal using N_DEF Tr_in_bound_intvD less_minus_Suc_zero by blast
      subgoal using N_DEF Tr_in_bound_intvD by fastforce
      subgoal by(auto intro!: Tr_in_boundD)
      subgoal by force
      subgoal 
        by (auto simp flip: uid_sorted_intvs[OF sorted_Tr] lid_sorted_intvs[OF sorted_Tr]) 
      subgoal by simp
      subgoal by (force simp flip: uid_sorted_intvs[OF sorted_Tr] lid_sorted_intvs[OF sorted_Tr] intro!: Br_in_boundD)
      subgoal by force
      subgoal by force
      subgoal 
       using Br_in_boundD N_DEF Tr_in_bound_intvD by blast
      subgoal 
        using less_Suc_eq by blast 
      subgoal 
        using sorted_Tr uid_sorted_intvs by fastforce 
      subgoal by force
      subgoal by force
      subgoal by fast
      subgoal 
        using less_Suc_eq by blast
      subgoal by force

      subgoal for s a b
        unfolding in_intv_def is_activated_transition_def N_DEF less_minus_Suc_zero
        using uid_sorted_intvs[OF sorted_Tr] lid_sorted_intvs[OF sorted_Tr] 
        by fastforce
      done


    lemma modest_get_next_activated_correct:
      assumes VL: "v < N"
      assumes INTV: "in_intv (StI ! v) t" 
      shows "modest_get_next_activated v t \<le> RETURN (next_activated_transition v t)"
      unfolding modest_get_next_activated_def
      apply(refine_vcg WHILEIT_rule[where ?R = "less_than_bool <*lex*> (greater_bounded (uid(StI!v)))"])
      subgoal 
        using N_DEF VL less_minus_Suc_zero by blast
      subgoal 
        using INTV N_DEF Suc_leI assms(1) in_intv_sorted_intvs sorted_St by blast
      subgoal 
        using INTV N_DEF Suc_leI assms(1) in_intv_sorted_intvs sorted_St by blast
      subgoal by (simp add: Suc_leI in_intv_ubD INTV)
      subgoal by fast
      subgoal 
        using assms by fastforce
      subgoal by force
      subgoal for s f t2
        apply(clarsimp simp flip: uid_sorted_intvs[OF sorted_St])
        apply(cases "t2 = uid (StI ! v)")
        subgoal by fastforce
        subgoal 
          apply clarsimp
          apply(subgoal_tac "in_intv (StI ! v) t2")
          subgoal using order_trans[OF modest_is_activated_correct]
            using less_Suc_eq VL by simp
          subgoal 
            using assms in_intv_def by auto
          done
        done
      subgoal for s f t2
        by (auto simp: next_activated_transition_eq simp flip: uid_sorted_intvs[OF sorted_St])
      subgoal for s f t2
        by (auto intro: next_activated_transition_no_act_pred simp flip: uid_sorted_intvs[OF sorted_St])
      done

    lemma modest_calculate_successor_correct: "v < N \<Longrightarrow> in_intv (StI ! v) t \<Longrightarrow> in_intv (TrI ! t) b \<Longrightarrow> modest_calculate_successor v t b \<le> RETURN (next_activated_branch v t b)"
      unfolding modest_calculate_successor_def next_activated_branch_def 
      apply(refine_vcg order_trans[OF modest_get_next_activated_correct])
      subgoal
        using Br_in_bound_intvD N_DEF Tr_in_bound_intvD le_simps(3) by blast
      subgoal 
        using N_DEF Tr_in_bound_intvD less_minus_Suc_zero by blast
      subgoal by (auto simp flip: uid_sorted_intvs[OF sorted_Tr] simp: less_minus_Suc_zero Let_def split: if_splits) 
      subgoal by (auto simp: N_DEF less_minus_Suc_zero simp flip: uid_sorted_intvs[OF sorted_Tr]) 
      subgoal by (auto simp flip: uid_sorted_intvs[OF sorted_St] elim: less_trans intro!: St_in_bound) 
      subgoal by(auto simp: Let_def split: if_splits simp flip: uid_sorted_intvs[OF sorted_Tr] 
        uid_sorted_intvs[OF sorted_St] intro!: lid_sorted_intvs[OF sorted_Tr] Tr_in_boundD)
      subgoal 
        by (auto simp add: sorted_Tr sorted_St uid_sorted_intvs)


      done
        

    lemma modest_any_activated_correct: "u < N \<Longrightarrow> modest_any_activated u \<le> RETURN (\<exists> t \<in> sn_intv (StI ! u). is_activated_transition u t)"
      unfolding modest_any_activated_def
      apply(refine_vcg order_trans[OF modest_get_next_activated_correct] order_trans[OF modest_is_activated_correct])
      subgoal using N_DEF by linarith
      subgoal by(auto simp: N_DEF intro!: nth_in_intv_sorted_intvs Sorted_St) 
      subgoal         
        apply (clarsimp simp flip: lid_sorted_intvs[OF sorted_St])
        apply(rule bexI[where ?x="lid (StI ! u)"]) 
        subgoal by (simp add: N_DEF sorted_St)
        subgoal by(auto simp: dest: St_nonempty)
        done
      subgoal by(auto simp: N_DEF intro!: nth_in_intv_sorted_intvs Sorted_St) 
      subgoal by(auto simp: N_DEF dest: St_nonempty)
      subgoal 
        apply (clarsimp simp flip: lid_sorted_intvs[OF sorted_St] uid_sorted_intvs[OF sorted_St]) 
        apply (clarsimp simp: next_activated_transition_gt activated_transitions_after_empty) 
        by (metis in_intv_lbD in_intv_ubD is_activated_transitionD1 order_neq_le_trans sn_intv_member)
      done

    lemma S_\<alpha>D1: "u \<in> S_\<alpha> \<Longrightarrow> u < N"
      unfolding S_\<alpha>_def by blast

  end

  subsection \<open>Index operations\<close>

  
  context modest_mdp_cullable_def
  begin

    definition "modest_admissible v = 
      RETURN (\<not>op_antpar_mem_any1 Mm v)"

    text\<open> 
      For efficiency, one could try to combine modest_is_empty and modest_index_begin, currently, 
      we are iterating the transitions once in each one, this could be combined in \<open>modest_is_empty\<close>.
    \<close>

    definition "modest_is_empty v = do{
      if modest_is_disabled_transitions v then do{
        RETURN True 
      } else do {
        g \<leftarrow> modest_any_activated v;
        RETURN (\<not>g)
      }
    }"

    definition "modest_index_begin v = do{
    let tl = St ! v;
      g \<leftarrow> modest_is_activated v tl;
      if g then do{
        ASSERT(tl < length Tr);
        let b = Tr ! tl;
        (tn,bn) \<leftarrow> modest_calculate_successor v tl b;
        RETURN (v,tl,tn,b,bn)
      }
      else do{
        t \<leftarrow> modest_get_next_activated v tl;
        ASSERT(t < length Tr);
        let b = Tr ! t;
        (tn,bn) \<leftarrow> modest_calculate_successor v t b;
        RETURN (v,t,tn,b,bn)
      }
    }"

  end

  context modest_successor_index_def 
  begin
    
    definition "modest_get_state = vI"

    definition "modest_succ_at \<equiv> Br!bcI"

    definition "modest_has_successor \<equiv> (tnI < St ! (Suc vI))"

    definition "modest_next_index = do{
      (tn',bn') \<leftarrow> modest_calculate_successor vI tnI bnI;
      RETURN (vI,tnI,tn',bnI,bn')
    }"

  end

  
  subsection \<open>Correctness of operations\<close>


  context modest_mdp_cullable_invar'
  begin
    interpretation mdp_graph SK_\<alpha> "{0..<N}" using mdp_graph_impl_modest .

    lemma non_empty_act_trans_list: "\<not> is_empty u \<Longrightarrow> act_trans u \<noteq> {}"
      unfolding is_empty_def mdp_graph_defs.is_empty_def  
      by (auto simp: K_\<alpha>'_def split: if_splits)

    lemma activated_transitions_after_alt: "activated_transitions_after u t = {t'. t' > t \<and> t' \<in> act_trans u}"
      unfolding activated_transitions_after_def
      by auto

    lemma activated_transitions_after_eq_act_trans: "in_intv (StI ! u) t \<Longrightarrow> (\<And>t'. t' \<le> t \<Longrightarrow> in_intv (StI ! u) t' \<Longrightarrow> \<not>is_activated_transition u t') \<Longrightarrow> activated_transitions_after u t = act_trans u"
      unfolding activated_transitions_after_def 
      using is_activated_transitionD1 linorder_le_less_linear by blast
                                                                                 
    lemma in_intv_next_activated_transition: "activated_transitions_after u t \<noteq> {} \<Longrightarrow> in_intv (StI ! u) (next_activated_transition u t)"
      apply(drule Min_in[OF finite_activated_transitions])
      unfolding next_activated_transition_def 
      by (auto simp: activated_transitions_after_mem is_activated_transitionD1)

    lemma init_id_modest_index_begin_correct: 
      assumes VN: "v < N" 
      and NE: "\<not>is_empty v"
      shows"modest_index_begin v \<le> \<Down>(modest_succ_index_DS_rel N DS) (index_begin v)"
    proof -         

      (*We introduce this intermediate function as part of a two-step refinement*)

      define index_begin_inter where "index_begin_inter \<equiv> do{
      let tl = St ! v;
        let g = is_activated_transition v tl;
        if g then do{
          ASSERT(tl < length Tr);
          let b = Tr ! tl;
          let (tn,bn) = next_activated_branch v tl b;
          RETURN (v,tl,tn,b,bn)
        }
        else do{
          let t = next_activated_transition v tl;
          ASSERT(t < length Tr);
          let b = Tr ! t;
          let (tn,bn) = next_activated_branch v t b;
          RETURN (v,t,tn,b,bn)
        }
      }"

      have AUX1: "x = y \<Longrightarrow> (x,y) \<in> Id" for x y
        by blast

      (*First refinement step*)

      have ITVACT: "in_intv (StI ! v) (next_activated_transition v t)" 
        if "in_intv (StI ! v) t" and "\<And>t'. t' \<le> t \<Longrightarrow> in_intv (StI ! v) t' \<Longrightarrow> \<not> is_activated_transition v t'" for t
        apply(rule in_intv_next_activated_transition)
        using non_empty_act_trans_list[OF NE] activated_transitions_after_eq_act_trans that by blast
      have AUX2: "in_intv (StI ! v) (next_activated_transition v (St ! v))"
        if "\<not> is_activated_transition v (St ! v)"
          apply(rule ITVACT)
          using VN N_DEF sorted_St Sorted_St 
          by (auto dest!: in_intv_lbD simp: that)

      have REF1: "modest_index_begin v \<le> \<Down>Id index_begin_inter"
        unfolding modest_index_begin_def index_begin_inter_def
        apply(refine_vcg order_trans[OF modest_is_activated_correct] order_trans[OF modest_calculate_successor_correct]
          order_trans[OF modest_get_next_activated_correct] AUX1)
        apply(clarsimp_all)
        subgoal using VN .
        subgoal using VN N_DEF Sorted_St by auto
        subgoal using VN .
        subgoal using VN N_DEF Sorted_St by auto
        subgoal using Sorted_Tr N_DEF Sorted_St Tr_in_bound_intvD assms(1) by blast
        subgoal using VN by blast
        subgoal using VN N_DEF Sorted_St by auto
        subgoal using VN by blast
        subgoal by(erule AUX2)
        subgoal using VN N_DEF Sorted_Tr 
          by (auto intro!: Tr_in_bound_intvD elim: AUX2)
        done

      (*Second refinement step*)

      have INV1: "next_activated_branch v (St ! v) (Tr ! (St ! v)) = (tn, bn) \<Longrightarrow> is_activated_transition v (St ! v) \<Longrightarrow>
          modest_successor_index_invar N DS (v, St ! v, tn, Tr ! (St ! v), bn)" for tn bn
        apply(unfold_locales)
        apply clarsimp_all
        subgoal
          using is_activated_transition_def by blast
        subgoal
          using Sorted_Tr Sorted_St VN
          by (auto simp: N_DEF intro!: in_intv_ubD Tr_in_boundD) 
        subgoal 
          by (simp add: VN[unfolded N_DEF] sorted_St)
        subgoal
          using Sorted_Tr Sorted_St VN
          by (auto simp: N_DEF intro!: in_intv_lbD Tr_in_boundD) 
        subgoal 
          using Sorted_Tr Sorted_St VN
          by (auto simp: N_DEF elim!: next_activated_branch_b_in_intv[OF VN] intro!: in_intv_lbD Tr_in_boundD) 
        subgoal
          by (metis K_MG_\<alpha> assms(2) mdp_graph_defs.is_empty_def modest_mdp_cullable_def.K_\<alpha>'_def)
        subgoal
          using next_activated_branch_activated by blast 
        done

      have \<alpha>1: "modest_successor_index_def.\<alpha> DS (v, St ! v, tn, Tr ! (St ! v), bn) \<in> {v} \<times> {si. set si = K_\<alpha>' v}" 
        if "next_activated_branch v (St ! v) (Tr ! (St ! v)) = (tn, bn)" and "is_activated_transition v (St ! v)"
        for tn bn 
      proof -
        interpret modest_successor_index_invar N DS "(v, St ! v, tn, Tr ! (St ! v), bn)"
          using INV1[OF that] .

        have "K_\<alpha>' vI = set si_\<alpha>"
          apply(rule equalityI)
          subgoal
            apply(safe; erule K_\<alpha>_to_si_\<alpha>)
            using sorted_Tr tcI_bound 
            by (auto simp: VN[unfolded N_DEF] in_intv_sorted_intvs sorted_St )
          subgoal
            using si_\<alpha>_to_K_\<alpha> by auto
          done

        thus ?thesis
          unfolding \<alpha>_def by auto
      qed

      have INV2: "modest_successor_index_invar N DS
        (v, next_activated_transition v (St ! v), tn, Tr ! next_activated_transition v (St ! v), bn)"
      if "next_activated_branch v (next_activated_transition v (St ! v)) (Tr ! next_activated_transition v (St ! v)) = (tn, bn)"
         "\<not> is_activated_transition v (St ! v)"
         "next_activated_transition v (St ! v) < length Tr" for tn bn
        apply(unfold_locales)
        apply clarsimp_all
        subgoal
          by (simp add: AUX2 in_intv_ubD that(2))
        subgoal
          using AUX2 Sorted_Tr Tr_in_bound_intvD VN that(2) by blast
        subgoal using that(1) by blast
        subgoal using AUX2 that(2) by blast
        subgoal 
          using AUX2 Sorted_Tr Tr_in_bound_intvD VN that(2) by blast
        subgoal
          using AUX2 Sorted_Tr VN Tr_in_bound_intvD next_activated_branch_b_in_intv that by blast
        subgoal 
          by (metis K_\<alpha>'_def NE local.is_empty_def modest_mdp_cullable_def.K_MG_\<alpha>)
        subgoal 
          apply(rule next_activated_transition_is_activated)
          by (auto simp add: AUX2 in_intv_ubD that(2) simp flip: next_activated_transition_gt)
        subgoal
          apply(rule next_activated_branch_activated[OF that(1)])
          apply(assumption)
          apply(rule next_activated_transition_is_activated)
          by (auto simp add: AUX2 in_intv_ubD that(2) simp flip: next_activated_transition_gt)
       done

      have \<alpha>2: "modest_successor_index_def.\<alpha> DS (v, next_activated_transition v (St ! v), tn, Tr ! next_activated_transition v (St ! v), bn)
        \<in> {v} \<times> {si. set si = K_\<alpha>' v}"
      if "next_activated_branch v (next_activated_transition v (St ! v)) (Tr ! next_activated_transition v (St ! v)) = (tn, bn)"
         "\<not> is_activated_transition v (St ! v)"
         "next_activated_transition v (St ! v) < length Tr" for tn bn
      proof -
        interpret modest_successor_index_invar N DS "(v, next_activated_transition v (St ! v), tn, Tr ! next_activated_transition v (St ! v), bn)"
          using INV2[OF that] .

        have "K_\<alpha>' vI = set si_\<alpha>"
          apply(rule equalityI)
          subgoal
            apply(safe; erule K_\<alpha>_to_si_\<alpha>)
            using sorted_Tr tcI_bound 
            apply (clarsimp_all simp: VN[unfolded N_DEF] in_intv_sorted_intvs sorted_St )
            using le_neq_implies_less next_activated_transition_not_act_between that(2) by blast
          subgoal
            using si_\<alpha>_to_K_\<alpha> by auto
          done

        thus ?thesis
          unfolding \<alpha>_def by auto
      qed


      have REF2: "index_begin_inter \<le> \<Down>(modest_succ_index_DS_rel N DS) (index_begin v)"
        unfolding index_begin_inter_def index_begin_def
        apply(clarsimp simp: Let_def)
        apply(refine_vcg)
        subgoal using St_in_bound[OF VN] by(auto dest!: is_activated_transitionD1 in_intv_ubD)
        subgoal for tn bn
          unfolding modest_succ_index_DS_rel_def
          by (auto simp: refine_pw_simps pw_le_iff in_br_conv INV1 \<alpha>1)
        subgoal 
          apply(rule less_trans[OF _ St_in_bound[OF VN]])
          using AUX2 by blast
        subgoal for tn bn
          unfolding modest_succ_index_DS_rel_def
          by (auto simp: refine_pw_simps pw_le_iff in_br_conv INV2 \<alpha>2)
        done

      show ?thesis
        using REF1 REF2 by auto
    qed

  end

  subsection \<open>Refinement to concrete\<close>

  lemma modest_is_admissible_refine_aux:
    assumes VB: "v < N"
    and GREL: "(DS, MG) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c"
    shows "modest_mdp_cullable_def.modest_admissible DS v \<le> mop_is_admissible MG v"
  proof -
    have INV': "modest_mdp_cullable_invar' N DS"
      by (metis GREL in_br_conv modest_mdp_cullable_invar.axioms(1) modest_mdp_succ_DS_rel_def modest_mdp_succ_rel_DS_eq)

    from GREL interpret modest_mdp_cullable_invar N DS\<^sub>c DS unfolding modest_mdp_succ_DS_rel_def
      by(auto simp: in_br_conv)

    from GREL have EDEF[simp]: "MG = SK_\<alpha>" unfolding modest_mdp_succ_DS_rel_def modest_mdp_cullable_def.SK_\<alpha>_def
      by(auto simp: in_br_conv DS_DEF)

    show ?thesis
      unfolding modest_mdp_cullable_def.modest_admissible_def mop_is_admissible_def
      apply(refine_vcg)
      apply(cases DS)
      using VB by (auto simp:  is_admissible_def modest_mdp_cullable_def.SK_\<alpha>_def 
        modest_mdp_cullable_def.S_\<alpha>_def op_antpar_mem_any1_def DS_DEF)
  qed


  lemma modest_is_empty_refine_aux:
    assumes VB: "v < N" 
    and GREL: "(DS,MG) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c" 
    shows "modest_mdp_cullable_def.modest_is_empty N DS v \<le> mop_is_empty MG v"
  proof -
    have INV': "modest_mdp_cullable_invar' N DS"
      by (metis GREL in_br_conv modest_mdp_cullable_invar.axioms(1) modest_mdp_succ_DS_rel_def modest_mdp_succ_rel_DS_eq)

    from GREL interpret modest_mdp_cullable_invar N DS\<^sub>c DS unfolding modest_mdp_succ_DS_rel_def
      by(auto simp: in_br_conv)

    from GREL have EDEF[simp]: "MG = SK_\<alpha>" unfolding modest_mdp_succ_DS_rel_def modest_mdp_cullable_def.SK_\<alpha>_def
      by(auto simp: in_br_conv DS_DEF)

    obtain i where A: "i\<in>sn_intv (StI ! v)" "cnt (TrI ! i) > 0"
      using state_has_transition[OF VB]
      by(auto simp: Tr_in_bound_intvD[OF VB, THEN Tr_nonempty] )

    have E1: "v \<notin> Cm \<Longrightarrow> mdp_graph_defs.is_empty SK_\<alpha> v"
      unfolding mdp_graph_defs.is_empty_def SK_\<alpha>_def K_\<alpha>'_def by auto

    show ?thesis
      unfolding modest_mdp_cullable_def.modest_is_empty_def mop_is_empty_def modest_mdp_cullable_def.modest_is_disabled_transitions_def
      apply(refine_vcg modest_mdp_cullable_invar'.modest_any_activated_correct[OF INV', THEN order_trans])
      subgoal
        using DS_DEF VB E1 by (auto dest: Av_Cm Ta_Cm)
      subgoal
        using DS_DEF VB by blast
      subgoal 
        apply (clarsimp simp: DS_DEF) 
        using VB is_activated_transition_def is_empty_not_activated by (auto simp: Cm_def)
      done
  qed


  lemma modest_index_begin_refine_aux: 
    assumes VB: "v < N"
    and NE: "\<not>mdp_graph_defs.is_empty MG v "
    and GREL: "(DS,MG) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c" 
    shows "modest_mdp_cullable_def.modest_index_begin N DS v \<le> \<Down>(modest_succ_index_DS_rel N DS) (mop_index_begin MG v)"
  proof -

    have INV': "modest_mdp_cullable_invar' N DS"
      by (metis GREL in_br_conv modest_mdp_cullable_invar.axioms(1) modest_mdp_succ_DS_rel_def modest_mdp_succ_rel_DS_eq)

    from GREL interpret modest_mdp_cullable_invar N DS\<^sub>c DS unfolding modest_mdp_succ_DS_rel_def
      by(auto simp: in_br_conv)

    from GREL have EDEF[simp]: "MG = SK_\<alpha>" "DS = DS\<^sub>c" unfolding modest_mdp_succ_DS_rel_def modest_mdp_cullable_def.SK_\<alpha>_def
      by(auto simp: in_br_conv DS_DEF)
 

    show ?thesis
      unfolding mop_index_begin_def 
      apply(rule modest_mdp_cullable_invar'.init_id_modest_index_begin_correct[OF INV', THEN order_trans] )
      subgoal using VB
        using N_DEF DS_DEF by blast
      subgoal using NE by (auto simp: DS_DEF)
      subgoal by auto
      done
  qed


  lemma modest_get_state_refine: "((v,tc,te,bc,be),(v',i)) \<in> modest_succ_index_DS_rel N DS \<Longrightarrow> 
      RETURN (modest_successor_index_def.modest_get_state (v,tc,te,bc,be)) \<le> \<Down>(node_rel' N) (mop_get_state (v',i))"
    unfolding modest_successor_index_def.modest_get_state_def mop_get_state_def mdp_graph_defs.get_state_def
      modest_succ_index_DS_rel_def
    by (auto simp: in_br_conv modest_successor_index_def.\<alpha>_def dest: modest_successor_index_invar.VBOUND)


  lemma modest_succ_at_refine_aux:
    assumes SREL: "((v,tc,te,bc,be),(v',si)) \<in> modest_succ_index_DS_rel N DS" 
    and GREL: "(DS,MG) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c"        
    shows "RETURN (modest_successor_index_def.modest_succ_at DS (v,tc,te,bc,be)) \<le> \<Down>(node_rel' N) (mop_graph_succ_at MG (v',si))"
  proof -

    from SREL interpret modest_successor_index_invar N DS"(v,tc,te,bc,be)" 
      unfolding modest_succ_index_DS_rel_def by(auto simp: in_br_conv)

    from SREL have I_DEF[simp]: "v' = v" "si = si_\<alpha>" 
      unfolding modest_succ_index_DS_rel_def by(auto simp: in_br_conv \<alpha>_def)

    from GREL have E_SUCC_DEF[simp]: "MG = SK_\<alpha>"
      unfolding modest_mdp_succ_DS_rel_def modest_mdp_cullable_def.SK_\<alpha>_def by(auto simp: in_br_conv)

    show ?thesis
      unfolding mop_graph_succ_at_def modest_succ_at_def mdp_graph_defs.successor_at_def
        modest_succ_index_DS_rel_def modest_mdp_succ_rel_def 
      using bcI_bound Br_in_bound[of bc]
      by(auto simp: in_br_conv N_DEF hd_si_\<alpha> intro!: Br_in_bound) 
  qed


  lemma(in modest_successor_index_invar) modest_has_successor_correct: 
    shows "modest_has_successor = mdp_graph_defs.has_next \<alpha>"
    unfolding modest_has_successor_def mdp_graph_defs.has_next_def \<alpha>_def
    by(auto simp: length_si_\<alpha>_has_next uid_sorted_intvs[OF sorted_St VBOUND[unfolded N_DEF]]) 


  lemma modest_has_successor_refine_aux: 
    assumes SREL: "((v,tc,te,bc,be),(v',si)) \<in> modest_succ_index_DS_rel N DS" 
    and GREL: "(DS,MG) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c" 
    shows "RETURN (modest_successor_index_def.modest_has_successor DS (v,tc,te,bc,be)) \<le> (mop_has_succ MG (v',si))"
  proof -

    from SREL interpret modest_successor_index_invar N DS "(v,tc,te,bc,be)" 
      unfolding modest_succ_index_DS_rel_def by(auto simp: in_br_conv)

    from SREL have I_DEF[simp]: "v' = v" "si = si_\<alpha>"
      unfolding modest_succ_index_DS_rel_def by(auto simp: in_br_conv \<alpha>_def)

    from GREL have E_SUCC_DEF[simp]: "MG = SK_\<alpha>"
      unfolding modest_mdp_succ_DS_rel_def modest_mdp_cullable_def.SK_\<alpha>_def by(auto simp: in_br_conv)


    show ?thesis
      unfolding mop_has_succ_def
      using TBOUND TUPP modest_has_successor_correct 
      using ACTN NAV NTA VBOUND is_empty_not_activated  
      by (auto simp: \<alpha>_def)
  qed


  lemma(in modest_successor_index_invar) modest_next_index_correct: 
    assumes NB': "next_activated_branch vI tnI bnI = (t, b)"
    assumes VD[simp]: "v' = vI"
    assumes SID[simp]: "si' = si_\<alpha>"
    assumes HN: "mdp_graph_defs.has_next \<alpha>"
    shows "((vI, tnI, t, bnI, b), mdp_graph_defs.next_index (v', si'))
           \<in> modest_succ_index_DS_rel N DS"
  proof -

    have ABS: "modest_successor_index_def.\<alpha> DS (vI, tnI, t, bnI, b) = mdp_graph_defs.next_index (v', si')" 
    unfolding mdp_graph_defs.next_index_def modest_successor_index_def.\<alpha>_def
    by (auto simp: VD si_\<alpha>_next tl_si_\<alpha>_eq) 

    have HN': "tnI < uid (StI ! vI)"
      using VBOUND HN modest_has_successor_correct modest_has_successor_def sorted_St uid_sorted_intvs N_DEF by metis

    have INV: "modest_successor_index_invar N DS (vI, tnI, t, bnI, b)"
      apply(unfold_locales)
      apply(clarsimp_all)
      subgoal 
        using HN' .
      subgoal 
        using HN' by blast
      subgoal 
        by (simp add: assms(1))
      subgoal 
        using TBOUND TLOW by linarith
      subgoal 
        using HN' by blast
      subgoal 
        using HN' next_activated_branch_b_in_intv[OF VBOUND NB'] by blast
      subgoal 
        using VCM .
      subgoal 
        by (simp add: ACTN HN')
      subgoal
        using ACTN NB' HN' next_activated_branch_activated by blast
      done

    show ?thesis
      by(auto simp: modest_succ_index_DS_rel_def in_br_conv INV ABS)
  qed


  lemma modest_next_index_refine_aux: 
    assumes SREL: "((v,tc,te,bc,be),(v',si')) \<in> modest_succ_index_DS_rel N DS" 
    and GREL: "(DS,MG) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c" 
    and HN: "mdp_graph_defs.has_next (v',si')"
    shows "(modest_successor_index_def.modest_next_index N DS (v,tc,te,bc,be)) \<le> \<Down>(modest_succ_index_DS_rel N DS\<^sub>c) (mop_next_id MG (v',si'))"
  proof -

      
    from SREL interpret modest_successor_index_invar N DS "(v,tc,te,bc,be)" 
      unfolding modest_succ_index_DS_rel_def by(auto simp: in_br_conv)

    from SREL have I_DEF[simp]: "v' = v" "si' = si_\<alpha>"
      unfolding modest_succ_index_DS_rel_def modest_successor_index_def.\<alpha>_def by(auto simp: in_br_conv \<alpha>_def)

    from GREL have E_SUCC_DEF[simp]: "MG = SK_\<alpha>"
      unfolding modest_mdp_succ_DS_rel_def modest_mdp_cullable_def.SK_\<alpha>_def by(auto simp: in_br_conv)

    have DS\<^sub>c_eq[simp]: "DS\<^sub>c = DS"
      using GREL modest_mdp_succ_rel_DS_eq by blast

    from HN have HN': "mdp_graph_defs.has_next \<alpha>"
      unfolding \<alpha>_def by auto
    have HS: "modest_has_successor" using HN' modest_has_successor_correct by blast
    hence HS': "tnI < uid (StI ! vI)" unfolding modest_has_successor_def 
      using VBOUND sorted_St uid_sorted_intvs N_DEF by metis

    show ?thesis
      unfolding mop_next_id_def modest_next_index_def
      apply(refine_vcg order_trans[OF modest_calculate_successor_correct]) 
      subgoal using N_DEF VBOUND by blast
      subgoal using HS' in_intv_tnI by blast
      subgoal
        using HS' in_intv_bnI by blast
      subgoal
        using HN' modest_next_index_correct by force
      done
  qed


  context modest_init_mdp_env_defs
  begin
  
    interpretation disj_set_list_tuple_defs N N ni ni .
  
    definition op_modest_is_disabled_transitions :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool" where 
      "op_modest_is_disabled_transitions = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr) v. op_set_member v Av \<or> op_set_member v Ta)"
    sepref_register op_modest_is_disabled_transitions :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool"
  
  
    lemma modest_is_disabled_transitions_alt: 
      "op_modest_is_disabled_transitions = modest_mdp_cullable_def.modest_is_disabled_transitions"
      unfolding op_modest_is_disabled_transitions_def modest_mdp_cullable_def.modest_is_disabled_transitions_def
        op_set_member_def by auto

    definition St_nth_lid :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat" where "St_nth_lid = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr) u. b_assn_open_block_fun2 u St (\<lambda> u St. (St ! u)))"
    definition St_nth_uid :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat" where "St_nth_uid = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr) u. b_assn_open_block_fun2 u St (\<lambda> u St. (St ! (Suc u))))"
  
    definition Tr_nth :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat" where "Tr_nth = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr) t. b_assn_open_block_fun Tr (\<lambda> Tr. (Tr ! t)))"
  
    lemma St_nth_lid_alt: "St_nth_lid DS t = modest_mdp_cullable_pre.St DS ! t"
      unfolding St_nth_lid_def modest_mdp_cullable_pre.St_def b_assn_open_block_fun2_def by (cases DS; auto)
    lemma St_nth_uid_alt: "St_nth_uid DS t = modest_mdp_cullable_pre.St DS ! (Suc t)"
      unfolding St_nth_uid_def modest_mdp_cullable_pre.St_def b_assn_open_block_fun2_def by (cases DS; auto)
  
    lemma Tr_nth_alt: "Tr_nth DS t = modest_mdp_cullable_pre.Tr DS ! t"
      unfolding Tr_nth_def modest_mdp_cullable_pre.Tr_def b_assn_open_block_fun_def by (cases DS; auto)
  
    definition mop_modest_get_target_of_branch :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat nres" where 
      "mop_modest_get_target_of_branch = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr) b. 
      do {
        ASSERT (b < length Br);
        r \<leftarrow> b_assn_open_block Br (\<lambda>Br. RETURN (Br ! b));
        ASSERT (r < N);
        let r = op_bound_val (\<lambda> x. x < N) r;
        RETURN r
      })"
    sepref_register mop_modest_get_target_of_branch :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat nres"
  
                                                                                               
    lemma modest_get_target_of_branch_alt: "mop_modest_get_target_of_branch = modest_mdp_cullable_def.get_successor_of_branch N"
      unfolding modest_mdp_cullable_def.get_successor_of_branch_def mop_modest_get_target_of_branch_def b_assn_open_block_def
      apply(rule ext)+
      apply (auto simp: Let_def)
      done
  
    definition mop_modest_eq_set_mem :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where 
      "mop_modest_eq_set_mem = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr) v w. do {
        RETURN (op_antpar_eq_set_mem Mm v w)
      })"
    sepref_register mop_modest_eq_set_mem :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres"
  
  
    lemma mop_modest_eq_set_mem_alt: "mop_modest_eq_set_mem = modest_mdp_cullable_def.modest_eq_set_mem"
      unfolding mop_modest_eq_set_mem_def modest_mdp_cullable_def.modest_eq_set_mem_def
      by auto
  
    definition mop_modest_valid_branch :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where 
    "mop_modest_valid_branch = (\<lambda> DS v b. 
    do {
      w \<leftarrow> mop_modest_get_target_of_branch DS b;
      ASSERT(w < N);
      mop_modest_eq_set_mem DS v w
    })"
    sepref_register mop_modest_valid_branch :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres"
  
  
    lemma modest_valid_branch_alt: "mop_modest_valid_branch = modest_mdp_cullable_def.modest_valid_branch N"
      unfolding mop_modest_eq_set_mem_alt mop_modest_valid_branch_def modest_mdp_cullable_def.modest_valid_branch_def 
        modest_get_target_of_branch_alt
      apply(rule ext)+
      by auto
  
  
  subsection \<open>Locale independent operations\<close>
  
    definition mop_modest_is_activated :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where 
    "mop_modest_is_activated DS v t = do {
      ASSERT(Suc t < length (modest_mdp_cullable_pre.Tr DS) \<and> t < length (modest_mdp_cullable_pre.Tr DS));
      let bl = Tr_nth DS t;
      let bu = Tr_nth DS (Suc t);
      (res,b) \<leftarrow> WHILEIT (\<lambda> (flag,b). bl \<le> b \<and> b \<le> bu \<and> (flag \<longleftrightarrow> (\<forall> b'. bl \<le> b' \<longrightarrow> b' < b \<longrightarrow> op_antpar_eq_set_mem (modest_mdp_cullable_pre.Mm DS) v ((modest_mdp_cullable_pre.Br DS) ! b'))))   
          (\<lambda> (flag,b). b < bu \<and> flag) (\<lambda> (flag,b). do {
        g \<leftarrow> mop_modest_valid_branch DS v b;
        if g then do{
          ASSERT (Suc b \<le> bu);
          RETURN (flag, Suc b) 
        }
        else do{
          ASSERT (Suc b \<le> bu);
          RETURN (False, Suc b)
        }
      }) (True, bl);
      RETURN res
    }"
    sepref_register mop_modest_is_activated :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres"
  
  
    lemma modest_is_activated_alt: "mop_modest_is_activated DS v t = modest_mdp_cullable_def.modest_is_activated N DS v t"
      unfolding mop_modest_is_activated_def modest_mdp_cullable_def.modest_is_activated_def 
         modest_valid_branch_alt b_assn_open_block_fun_def Tr_nth_alt
      by presburger
  
    definition mop_modest_get_next_activated :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where 
    "mop_modest_get_next_activated DS v t\<^sub>0 = do{
      ASSERT(Suc v < length (modest_mdp_cullable_pre.St DS));
      let tu = St_nth_uid DS v;
      ASSERT(Suc t\<^sub>0 \<le> tu);
      (flag,t) \<leftarrow> WHILEIT (\<lambda> (flag,t). t\<^sub>0 < t \<and> t \<le> tu \<and> (\<forall> t'. t\<^sub>0 < t' \<longrightarrow> t' < t \<longrightarrow> \<not>modest_mdp_cullable_def.is_activated_transition DS v t') \<and> (modest_mdp_cullable_def.is_activated_transition DS v t \<or> flag)) 
          (\<lambda> (flag,t). t < tu \<and> flag) (\<lambda> (flag,t). do {
        g \<leftarrow> mop_modest_is_activated DS v t;
        if g then 
          RETURN (False,t)
        else do {
          ASSERT (Suc t \<le> tu);
          RETURN (flag, Suc t) 
        }
      }) (True,Suc t\<^sub>0);
      if flag then
        RETURN tu
      else
        RETURN t
    }"
    sepref_register mop_modest_get_next_activated :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres"
  
  
    lemma modest_get_next_activated_alt: "mop_modest_get_next_activated DS v t = modest_mdp_cullable_def.modest_get_next_activated N DS v t"
      unfolding mop_modest_get_next_activated_def modest_mdp_cullable_def.modest_get_next_activated_def
        St_nth_uid_alt modest_is_activated_alt
      by blast
  
    definition mop_modest_calculate_successor :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) nres" where 
    "mop_modest_calculate_successor DS v t b = do {
      ASSERT(Suc b \<le> length (modest_mdp_cullable_pre.Br DS));
      let bn = Suc b;
      ASSERT(Suc t < length (modest_mdp_cullable_pre.Tr DS));
      if (bn < Tr_nth DS (Suc t)) 
      then do {
        RETURN (t,bn)
      } else do {
        tn \<leftarrow> mop_modest_get_next_activated DS v t;
        ASSERT(Suc v < length (modest_mdp_cullable_pre.St DS));
        if(tn < St_nth_uid DS v) then do{
          ASSERT (tn < length (modest_mdp_cullable_pre.Tr DS));
          RETURN (tn,Tr_nth DS tn) 
        } else
          RETURN (tn,b)
      }
    }"
    sepref_register mop_modest_calculate_successor :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) nres"
  
  
    lemma modest_calculate_successor_alt: "mop_modest_calculate_successor DS v t b = modest_mdp_cullable_def.modest_calculate_successor N DS v t b"
      unfolding mop_modest_calculate_successor_def modest_mdp_cullable_def.modest_calculate_successor_def
        St_nth_uid_alt Tr_nth_alt modest_get_next_activated_alt
        by auto 
  
      (*TODO: Optimization: It would be more efficient if we could use this as a constructor of the initial index somehow *)
    definition mop_modest_any_activated :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool nres" where 
    "mop_modest_any_activated DS u = do {
      ASSERT(u < length (modest_mdp_cullable_pre.St DS));
      let t = St_nth_lid DS u;
      g \<leftarrow> mop_modest_is_activated DS u t;
      if g then
        RETURN True
      else do{
        tn \<leftarrow> mop_modest_get_next_activated DS u t;
        ASSERT(Suc u < length (modest_mdp_cullable_pre.St DS));
        RETURN (tn < St_nth_uid DS u)
      }
    }"
    sepref_register mop_modest_any_activated :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool nres"
  
  
    lemma modest_any_activated_alt: "mop_modest_any_activated DS v = modest_mdp_cullable_def.modest_any_activated N DS v"
      unfolding mop_modest_any_activated_def modest_mdp_cullable_def.modest_any_activated_def
        modest_is_activated_alt modest_get_next_activated_alt St_nth_lid_alt St_nth_uid_alt
      by auto
  
  
  
    definition mop_modest_is_admissible :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool nres" where
      "mop_modest_is_admissible = (\<lambda> (St,Tr,Br,Av,Ta,Mm,Nr) v.  RETURN (\<not>op_antpar_mem_any1 Mm v))"
    sepref_register mop_modest_is_admissible
  
  
    lemma mop_modest_is_admissible_alt: "mop_modest_is_admissible = modest_mdp_cullable_def.modest_admissible"
      unfolding mop_modest_is_admissible_def modest_mdp_cullable_def.modest_admissible_def
      by auto
  
  
    definition mop_modest_is_empty :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool nres" where 
    "mop_modest_is_empty DS v \<equiv> do{
      if op_modest_is_disabled_transitions DS v then do{
        RETURN True 
      } else do {
        g \<leftarrow> mop_modest_any_activated DS v;
        RETURN (\<not>g)
      }
    }"
    sepref_register mop_modest_is_empty :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool nres"
  
  
    lemma modest_is_empty_alt: "mop_modest_is_empty = modest_mdp_cullable_def.modest_is_empty N"
      unfolding mop_modest_is_empty_def modest_mdp_cullable_def.modest_is_empty_def 
        modest_any_activated_alt modest_is_disabled_transitions_alt by presburger
  
    definition "mop_modest_index_begin = (\<lambda> DS v. do{
      let tl = St_nth_lid DS v;
      g \<leftarrow> mop_modest_is_activated DS v tl;
      if g then do{
        ASSERT(tl < length (modest_mdp_cullable_pre.Tr DS));
        let b = Tr_nth DS tl;                  
        (tn,bn) \<leftarrow> mop_modest_calculate_successor DS v tl b;
        RETURN (v,tl,tn,b,bn)
      }
      else do{
        t \<leftarrow> mop_modest_get_next_activated DS v tl;
        ASSERT(t < length (modest_mdp_cullable_pre.Tr DS));
        let b = Tr_nth DS t;
        (tn,bn) \<leftarrow> mop_modest_calculate_successor DS v t b;
        RETURN (v,t,tn,b,bn)
      }
    })"
    sepref_register mop_modest_index_begin :: "modest_mdp \<Rightarrow> nat \<Rightarrow> (nat modest_succ_index) nres"
  
  
    lemma modest_index_begin_refine: "mop_modest_index_begin DS v = modest_mdp_cullable_def.modest_index_begin N DS v"
      unfolding mop_modest_index_begin_def modest_mdp_cullable_def.modest_index_begin_def
        modest_calculate_successor_alt modest_is_activated_alt modest_get_next_activated_alt
        St_nth_lid_alt Tr_nth_alt
      by blast
  
  
    definition mop_modest_get_state :: "nat modest_succ_index \<Rightarrow> nat nres" where 
      "mop_modest_get_state = (\<lambda> (v,tc,tn,bc,bn). RETURN v)"
    sepref_register mop_modest_get_state :: "nat modest_succ_index \<Rightarrow> nat nres"
  
    lemma mop_modest_get_state_refine: "mop_modest_get_state ci = RETURN (modest_successor_index_def.modest_get_state ci)"
      unfolding mop_modest_get_state_def modest_successor_index_def.modest_get_state_def 
      by (auto split: prod.splits)
  
  
    definition mop_modest_succ_at :: "modest_mdp \<Rightarrow> nat modest_succ_index \<Rightarrow> nat nres" where 
    "mop_modest_succ_at = (\<lambda> DS (v,tc,te,bc,be).
      do{
        mop_modest_get_target_of_branch DS bc
      })"
    sepref_register mop_modest_succ_at :: "modest_mdp \<Rightarrow> nat modest_succ_index \<Rightarrow> nat nres"
  
  
    lemma modest_succ_at_refine: "bc < length Br \<Longrightarrow> modest_mdp_cullable_invar N DS\<^sub>c (St,Tr,Br,Av,Ta,Mm,Nr) \<Longrightarrow> mop_modest_succ_at (St,Tr,Br,Av,Ta,Mm,Nr) (v,tc,te,bc,be) \<le> RETURN (modest_successor_index_def.modest_succ_at (St,Tr,Br,Av,Ta,Mm,Nr) (v,tc,te,bc,be))"
      unfolding mop_modest_succ_at_def modest_successor_index_def.modest_succ_at_def 
        modest_get_target_of_branch_alt modest_mdp_cullable_def.get_successor_of_branch_def
      apply(refine_vcg) 
      apply simp
      apply (simp add: modest_mdp_cullable_invar_def modest_mdp_cullable_invar_axioms_def modest_mdp_cullable_invar'_def
        modest_mdp_cullable_invar'_axioms_def modest_mdp_input_struc_invar_def) 
      apply (meson atLeastLessThan_iff nth_mem subset_code(1))
      by simp
  
  
    definition mop_modest_has_successor :: "modest_mdp \<Rightarrow> nat modest_succ_index \<Rightarrow> bool nres" where 
    "mop_modest_has_successor = (\<lambda> DS (v,tc,tn,bc,bn).
      do{
        RETURN (tn < St_nth_uid DS v)
      })"
    sepref_register mop_modest_has_successor :: "modest_mdp \<Rightarrow> nat modest_succ_index \<Rightarrow> bool nres"
  
  
    lemma modest_has_successor_refine:
      assumes INV: "modest_successor_index_invar N DS (v,tc,te,bc,be)" 
      shows "mop_modest_has_successor DS (v,tc,te,bc,be) \<le> RETURN (modest_successor_index_def.modest_has_successor DS (v,tc,te,bc,be))"
    proof-
      from INV interpret modest_successor_index_invar N DS "(v,tc,te,bc,be)" .
  
      show ?thesis
        unfolding mop_modest_has_successor_def modest_has_successor_def St_nth_uid_alt
        apply(refine_vcg)
        subgoal using VBOUND by auto
        done
    qed
  
  
    definition mop_modest_next_index :: "modest_mdp \<Rightarrow> nat modest_succ_index \<Rightarrow> (nat modest_succ_index) nres" where 
    "mop_modest_next_index = (\<lambda> DS (v,tc,tn,bc,bn).
      do{
        \<^cancel>\<open>ASSERT(mdp_graph_defs.has_next MG_\<alpha> ci);\<close>
        (tn',bn') \<leftarrow> mop_modest_calculate_successor DS v tn bn;
        RETURN (v,tn,tn',bn,bn')
      }
    )"
    sepref_register mop_modest_next_index :: "modest_mdp \<Rightarrow> nat modest_succ_index \<Rightarrow> (nat modest_succ_index) nres"
  
  
    lemma modest_next_index_refine: 
      assumes INV: "modest_successor_index_invar N DS (v,tc,te,bc,be)" 
      assumes NEXT: "mdp_graph_defs.has_next (modest_successor_index_def.\<alpha> DS (v,tc,te,bc,be))"
      shows "mop_modest_next_index DS (v,tc,te,bc,be) \<le> modest_successor_index_def.modest_next_index N DS (v,tc,te,bc,be)"
    proof -
      from INV interpret modest_successor_index_invar N DS "(v,tc,te,bc,be)" .
  
      show ?thesis
        unfolding mop_modest_next_index_def modest_next_index_def
          modest_calculate_successor_alt
        by force
    qed 
  
    subsubsection \<open>Correctness\<close>
  
    lemma mop_modest_is_admissible_correct: "(mop_modest_is_admissible, mop_is_admissible) \<in> modest_mdp_succ_DS_rel N DS \<rightarrow> node_rel' N \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
      apply (refine_vcg) 
      by (auto intro: modest_is_admissible_refine_aux simp: mop_modest_is_admissible_alt)
  
    lemma modest_is_empty_correct:  "(PR_CONST mop_modest_is_empty, mop_is_empty) \<in> modest_mdp_succ_DS_rel N DS \<rightarrow> node_rel' N \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
      apply (refine_vcg) 
      by (auto intro: modest_is_empty_refine_aux simp: modest_is_empty_alt)
  
    lemma modest_index_begin_correct: "(uncurry (PR_CONST mop_modest_index_begin), uncurry mop_index_begin) \<in> [\<lambda> (MG, v). \<not>mdp_graph_defs.is_empty MG v]\<^sub>f (modest_mdp_succ_DS_rel N DS) \<times>\<^sub>r node_rel' N \<rightarrow> \<langle>(modest_succ_index_DS_rel N DS)\<rangle>nres_rel"
      apply(clarsimp intro!: frefI nres_relI)
      apply(clarsimp simp: in_br_conv modest_mdp_succ_DS_rel_def)
      apply(frule modest_mdp_cullable_invar.DS_DEF[symmetric])
      unfolding modest_index_begin_refine
      apply(drule modest_mdp_cullable_invar.axioms(1))
      apply clarsimp
      apply(rule modest_index_begin_refine_aux[THEN order_trans])
      by (auto simp: in_br_conv modest_mdp_succ_DS_rel_def intro: modest_mdp_cullable_invar_axioms.intro modest_mdp_cullable_invar.intro)
  
  
    lemma modest_get_state_get_state_correct: "(mop_modest_get_state, mop_get_state) \<in> modest_succ_index_DS_rel N DS \<rightarrow> \<langle>node_rel' N\<rangle>nres_rel"
      apply(refine_vcg)
      by(auto intro!: modest_get_state_refine simp: mop_modest_get_state_refine)
  
  
    lemma modest_succ_at_correct: "((PR_CONST mop_modest_succ_at), mop_graph_succ_at) \<in> (modest_mdp_succ_DS_rel N DS\<^sub>c) \<rightarrow> (modest_succ_index_DS_rel N DS\<^sub>c) \<rightarrow> \<langle>node_rel' N\<rangle>nres_rel"
      apply (refine_vcg)
      apply(frule modest_mdp_succ_rel_DS_eq)
      apply clarsimp
      apply(rule modest_succ_at_refine[THEN order_trans])
      subgoal for St Tr Br Av Ta Mm1 Mm2 K v tc te bc be v' ti bi
        apply(clarsimp simp: modest_succ_index_DS_rel_def in_br_conv ) 
        apply(frule modest_successor_index_invar.beI_bound) 
        using modest_successor_index_invar.bcI_bound by force
      apply(auto simp: modest_mdp_succ_DS_rel_def in_br_conv)[]
      apply(rule modest_succ_at_refine_aux)
      by assumption+
  
  
    lemma modest_has_successor_correct: "(mop_modest_has_successor, mop_has_succ) \<in> (modest_mdp_succ_DS_rel N DS\<^sub>c) \<rightarrow> (modest_succ_index_DS_rel N DS\<^sub>c) \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
      apply(refine_vcg)
      apply clarsimp
      apply(rule modest_has_successor_refine[THEN order_trans])
      apply(auto simp: modest_succ_index_DS_rel_def in_br_conv dest: modest_mdp_succ_rel_DS_eq)[]
      apply(rule modest_has_successor_refine_aux)
      apply(auto dest: modest_mdp_succ_rel_DS_eq)
      done
  
  
    lemma modest_next_index_correct: "(uncurry (PR_CONST mop_modest_next_index), uncurry mop_next_id) \<in> [\<lambda> (MG,ci). mdp_graph_defs.has_next ci]\<^sub>f (modest_mdp_succ_DS_rel N DS\<^sub>c) \<times>\<^sub>r (modest_succ_index_DS_rel N DS\<^sub>c) \<rightarrow> \<langle>(modest_succ_index_DS_rel N DS\<^sub>c)\<rangle>nres_rel"
      apply(clarsimp intro!: frefI nres_relI)
      apply(rule modest_next_index_refine[THEN order_trans])
      apply(drule modest_mdp_succ_rel_DS_eq)
      apply(auto simp: modest_succ_index_DS_rel_def in_br_conv)[]
      subgoal
        apply(frule modest_mdp_succ_rel_DS_eq)
        by(auto simp: modest_mdp_succ_DS_rel_def modest_succ_index_DS_rel_def in_br_conv)[] 
      subgoal
        by (auto intro!: modest_next_index_refine_aux 
          dest: modest_mdp_succ_rel_DS_eq modest_succ_index_rel_vD)
      done
  
  
    subsection \<open>LLVM Data Structures\<close>
  
    subsubsection \<open>Modest graph\<close>
  
  
    type_synonym modest_mdpi = "
      size_t ptr 
    \<times> size_t ptr
    \<times> size_t ptr
    \<times> bitseti
    \<times> bitseti
    \<times> antpari
    \<times> size_t
    "
  
    (*TODO: Add cullable to name*)
    definition modest_mdp_assn_aux :: "modest_mdp \<Rightarrow> modest_mdpi \<Rightarrow> assn"
    where "modest_mdp_assn_aux = 
       node_array_slice_assn (Suc N) size_assn \<comment> \<open>List of states\<close>
    \<times>\<^sub>a small_array_slice_assn size_assn \<comment> \<open>List of transitions\<close>
    \<times>\<^sub>a small_array_slice_assn (node_assn' N) \<comment> \<open>List of Branches\<close>
    \<times>\<^sub>a (bitset_assn N)
    \<times>\<^sub>a (bitset_assn N)
    \<times>\<^sub>a (disj_set_list_tuple_assn)
    \<times>\<^sub>a size_assn"
  
  
    lemma modest_mdp_assn_boundsD[sepref_bounds_dest]: 
      assumes "rdomp modest_mdp_assn_aux (St,Tr,Br,Av,Ta,Mm,Nr)"
      shows "length Tr < max_size_t" and "length Br < max_size_t"
      using assms unfolding modest_mdp_assn_aux_def
      apply auto
      done
  
    definition "modest_mdp_succ_DS_assn DS = hr_comp modest_mdp_assn_aux (modest_mdp_succ_DS_rel N DS)"
  
    definition "modest_mdp_succ_assn = hr_comp modest_mdp_assn_aux (modest_mdp_succ_rel N)"
  
    lemma modest_mdp_succ_assn_alt: "modest_mdp_succ_assn MG Ei = (EXS DS. modest_mdp_succ_DS_assn DS MG Ei)"
      unfolding modest_mdp_succ_DS_assn_def modest_mdp_succ_rel_def modest_mdp_succ_assn_def
      apply(cases MG)
      using modest_mdp_succ_rel_DS_eq
      by (fastforce simp: fun_eq_iff hr_comp_def sep_algebra_simps)
  
  
    subsubsection \<open>Modest Graph Index\<close>
  
    type_synonym modest_indexi = "
      node_t 
    \<times> size_t 
    \<times> size_t 
    \<times> size_t 
    \<times> size_t
    "
  
    definition modest_index_assn_aux :: "nat modest_succ_index \<Rightarrow> modest_indexi \<Rightarrow> assn"
    where "modest_index_assn_aux = (node_assn' N) \<times>\<^sub>a size_assn \<times>\<^sub>a size_assn \<times>\<^sub>a size_assn \<times>\<^sub>a size_assn"
  
    definition "modest_index_DS_assn DS = hr_comp modest_index_assn_aux (modest_succ_index_DS_rel N DS)"
  
    lemma is_pure_modest_index_assn[safe_constraint_rules]: 
        "is_pure (modest_index_DS_assn DS)" unfolding modest_index_DS_assn_def modest_index_assn_aux_def by solve_constraint
  
  
  end

  





  subsection \<open>Refinement to LLVM\<close>

  context modest_init_mdp_env
  begin
  
    lemma N_BOUND2: "N < max_size_t - N"
      using N_BOUND by simp
  
    lemma N_max_size_t: "x \<le> N \<Longrightarrow> x < max_size_t"
      using N_BOUND by simp
  
    lemmas [sepref_import_param] = n_impl
    sepref_register N
  
  
    concrete_definition (in -) teq_set_member_ll' [llvm_code] is disj_set_list_tuple_env.teq_set_member_ll_def
    concrete_definition (in -) is_member_any1_ll' [llvm_code] is disj_set_list_tuple_env.is_member_any1_ll_def
  
    interpretation disj_set_list_tuple_env N N ni ni
      apply(unfold_locales)
      using n_impl .
  
    lemmas [unfolded teq_set_member_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_eq_set_mem_hnr[OF disj_set_list_tuple_env_axioms]
    lemmas [unfolded is_member_any1_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_mem_any1_hnr[OF disj_set_list_tuple_env_axioms]
  
  end
  
  
  
  
  context modest_init_mdp_env
  begin
  
    lemma Suc_N_leq_max: "x < N \<Longrightarrow> Suc x < max_size_t"
      using n_impl
      by (simp add: N_max_size_t)
  
    sepref_definition modest_is_disabled_transitions_ll is "uncurry (RETURN oo op_modest_is_disabled_transitions)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding op_modest_is_disabled_transitions_def modest_mdp_assn_aux_def
      apply sepref
      done
    concrete_definition (in -) modest_is_disabled_transitions_ll' [llvm_code] is modest_init_mdp_env.modest_is_disabled_transitions_ll_def
    lemmas modest_is_disabled_transitions_hnr[sepref_fr_rules] = modest_is_disabled_transitions_ll.refine[unfolded modest_is_disabled_transitions_ll'.refine[OF modest_init_mdp_env_axioms]]  
  
                                                                                         
    sepref_definition St_nth_lid_ll is "uncurry (RETURN \<circ>\<circ> St_nth_lid)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding St_nth_lid_def modest_mdp_assn_aux_def
      apply sepref
      done
    concrete_definition (in -) St_nth_lid_ll' [llvm_code] is modest_init_mdp_env.St_nth_lid_ll_def
    lemmas St_nth_lid_hnr[sepref_fr_rules] = St_nth_lid_ll.refine[unfolded St_nth_lid_ll'.refine[OF modest_init_mdp_env_axioms]]  
  
  
    sepref_definition St_nth_uid_ll is "uncurry (RETURN \<circ>\<circ> St_nth_uid)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding St_nth_uid_def modest_mdp_assn_aux_def
      supply[elim] = Suc_N_leq_max
      apply sepref
      done
    concrete_definition (in -) St_nth_uid_ll' [llvm_code] is modest_init_mdp_env.St_nth_uid_ll_def
    lemmas St_nth_uid_hnr[sepref_fr_rules] = St_nth_uid_ll.refine[unfolded St_nth_uid_ll'.refine[OF modest_init_mdp_env_axioms]]  
  
  
    sepref_definition Tr_nth_ll is "uncurry (RETURN \<circ>\<circ> Tr_nth)" :: "[\<lambda> ((St,Tr,Br,Av,Ta,Mm,Nr), t). t < length Tr]\<^sub>a modest_mdp_assn_aux\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> size_assn"
      unfolding Tr_nth_def modest_mdp_assn_aux_def
      by sepref
    concrete_definition (in -) Tr_nth_ll' [llvm_code] is modest_init_mdp_env.Tr_nth_ll_def
    lemmas Tr_nth_hnr[sepref_fr_rules] = Tr_nth_ll.refine[unfolded Tr_nth_ll'.refine[OF modest_init_mdp_env_axioms]]  
  
  
    sepref_definition get_successor_of_branch_ll is "uncurry (PR_CONST mop_modest_get_target_of_branch)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a (node_assn' N)"
      unfolding mop_modest_get_target_of_branch_def modest_mdp_assn_aux_def PR_CONST_def
      apply sepref
      done
    concrete_definition (in -) get_successor_of_branch_ll' [llvm_code] is modest_init_mdp_env.get_successor_of_branch_ll_def
    lemmas get_successor_of_branch_hnr[sepref_fr_rules] = get_successor_of_branch_ll.refine[unfolded get_successor_of_branch_ll'.refine[OF modest_init_mdp_env_axioms]]  
  
  
    sepref_definition modest_succ_at_ll is "uncurry (PR_CONST mop_modest_succ_at)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a modest_index_assn_aux\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(node_T)"
      unfolding mop_modest_succ_at_def modest_index_assn_aux_def PR_CONST_def
      apply sepref
      done
    concrete_definition (in -) modest_succ_at_ll' [llvm_code] is modest_init_mdp_env.modest_succ_at_ll_def
    lemmas modest_succ_at_hnr[sepref_fr_rules] = modest_succ_at_ll.refine[unfolded modest_succ_at_ll'.refine[OF modest_init_mdp_env_axioms]]  
  
  
    sepref_definition modest_has_successor_ll is "uncurry mop_modest_has_successor" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a modest_index_assn_aux\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding mop_modest_has_successor_def modest_index_assn_aux_def
      apply sepref
      done
    concrete_definition (in -) modest_has_successor_ll' [llvm_code] is modest_init_mdp_env.modest_has_successor_ll_def
    lemmas modest_has_successor_hnr[sepref_fr_rules] = modest_has_successor_ll.refine[unfolded modest_has_successor_ll'.refine[OF modest_init_mdp_env_axioms]]  
  
  
  
    sepref_definition modest_eq_set_mem_ll is "uncurry2 mop_modest_eq_set_mem" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding mop_modest_eq_set_mem_def modest_mdp_assn_aux_def
      apply sepref
      done
    concrete_definition (in -) modest_eq_set_mem_ll' [llvm_code] is modest_init_mdp_env.modest_eq_set_mem_ll_def
    lemmas modest_eq_set_mem_hnr[sepref_fr_rules] = modest_eq_set_mem_ll.refine[unfolded modest_eq_set_mem_ll'.refine[OF modest_init_mdp_env_axioms]]  
  
  
  
    sepref_definition modest_valid_branch_ll is "uncurry2 (PR_CONST mop_modest_valid_branch)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding mop_modest_valid_branch_def PR_CONST_def
      apply sepref
      done
    concrete_definition (in -) modest_valid_branch_ll' [llvm_code] is modest_init_mdp_env.modest_valid_branch_ll_def
    lemmas modest_valid_branch_hnr[sepref_fr_rules] = modest_valid_branch_ll.refine[unfolded modest_valid_branch_ll'.refine[OF modest_init_mdp_env_axioms]]
  
  
    sepref_definition mop_modest_is_activated_ll is "uncurry2 (PR_CONST mop_modest_is_activated)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding mop_modest_is_activated_def PR_CONST_def
      supply[elim] = modest_mdp_assn_boundsD(1)[THEN less_trans[rotated]]
      apply sepref
      done
    concrete_definition (in -) mop_modest_is_activated_ll' [llvm_code] is modest_init_mdp_env.mop_modest_is_activated_ll_def
    lemmas mop_modest_is_activated_hnr[sepref_fr_rules] = mop_modest_is_activated_ll.refine[unfolded mop_modest_is_activated_ll'.refine[OF modest_init_mdp_env_axioms]]
      
  
    sepref_definition mop_modest_get_next_activated_ll is "uncurry2 (PR_CONST mop_modest_get_next_activated)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding mop_modest_get_next_activated_def PR_CONST_def
      apply sepref
      done
    concrete_definition (in -) mop_modest_get_next_activated_ll' [llvm_code] is modest_init_mdp_env.mop_modest_get_next_activated_ll_def
    lemmas mop_modest_get_next_activated_hnr[sepref_fr_rules] = mop_modest_get_next_activated_ll.refine[unfolded mop_modest_get_next_activated_ll'.refine[OF modest_init_mdp_env_axioms]]
  
  
    sepref_definition mop_modest_calculate_successor_ll is "uncurry3 (PR_CONST mop_modest_calculate_successor)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn \<times>\<^sub>a size_assn"
      unfolding mop_modest_calculate_successor_def PR_CONST_def
      supply[elim] = modest_mdp_assn_boundsD(1)[THEN less_trans[rotated]]
      apply sepref
      done
  
    concrete_definition (in -) mop_modest_calculate_successor_ll' [llvm_code] is modest_init_mdp_env.mop_modest_calculate_successor_ll_def
    lemmas mop_modest_calculate_successor_hnr[sepref_fr_rules] = mop_modest_calculate_successor_ll.refine[unfolded mop_modest_calculate_successor_ll'.refine[OF modest_init_mdp_env_axioms]]
  
  
    sepref_definition mop_modest_any_activated_ll is "uncurry (PR_CONST mop_modest_any_activated)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding mop_modest_any_activated_def PR_CONST_def
      apply sepref
      done
    concrete_definition (in -) mop_modest_any_activated_ll' [llvm_code] is modest_init_mdp_env.mop_modest_any_activated_ll_def
    lemmas mop_modest_any_activated_hnr[sepref_fr_rules] = mop_modest_any_activated_ll.refine[unfolded mop_modest_any_activated_ll'.refine[OF modest_init_mdp_env_axioms]]
  
  
    sepref_definition mop_modest_is_admissible_ll is "uncurry (mop_modest_is_admissible)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k\<rightarrow>\<^sub>a bool1_assn"
      unfolding mop_modest_is_admissible_def modest_mdp_assn_aux_def
      apply sepref
      done
  
    concrete_definition (in -) mop_modest_is_admissible_ll' [llvm_code] is modest_init_mdp_env.mop_modest_is_admissible_ll_def
    lemmas mop_modest_is_admissible_hnr[sepref_fr_rules] = mop_modest_is_admissible_ll.refine[unfolded mop_modest_is_admissible_ll'.refine[OF modest_init_mdp_env_axioms]]
  
    sepref_definition modest_is_empty_ll is "uncurry (PR_CONST mop_modest_is_empty)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k\<rightarrow>\<^sub>a bool1_assn"
      unfolding mop_modest_is_empty_def PR_CONST_def
      apply sepref
      done
    concrete_definition (in -) modest_is_empty_ll' [llvm_code] is modest_init_mdp_env.modest_is_empty_ll_def
    lemmas modest_is_empty_hnr[sepref_fr_rules] = modest_is_empty_ll.refine[unfolded modest_is_empty_ll'.refine[OF modest_init_mdp_env_axioms]]
  
  
    sepref_definition modest_index_begin_ll is "uncurry (PR_CONST mop_modest_index_begin)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k \<rightarrow>\<^sub>a modest_index_assn_aux"
      unfolding mop_modest_index_begin_def modest_index_assn_aux_def PR_CONST_def
      modest_mdp_cullable_pre.St_def
      apply sepref
      done
  
    concrete_definition (in -) modest_index_begin_ll' [llvm_code] is modest_init_mdp_env.modest_index_begin_ll_def
    lemmas modest_index_begin_hnr[sepref_fr_rules] = modest_index_begin_ll.refine[unfolded modest_index_begin_ll'.refine[OF modest_init_mdp_env_axioms]]
  
    sepref_definition modest_get_state_ll is "mop_modest_get_state" :: "modest_index_assn_aux\<^sup>k \<rightarrow>\<^sub>a (node_assn' N)"
      unfolding mop_modest_get_state_def modest_index_assn_aux_def
      apply sepref
      done
    concrete_definition (in -) modest_get_state_ll' [llvm_code] is modest_init_mdp_env.modest_get_state_ll_def
    lemmas modest_get_state_hnr[sepref_fr_rules] = modest_get_state_ll.refine[unfolded modest_get_state_ll'.refine[OF modest_init_mdp_env_axioms]]
  
    sepref_definition modest_next_index_ll is "uncurry (PR_CONST mop_modest_next_index)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a modest_index_assn_aux\<^sup>d \<rightarrow>\<^sub>a modest_index_assn_aux"
      unfolding mop_modest_next_index_def  modest_index_assn_aux_def PR_CONST_def
      apply sepref
      done
  
    concrete_definition (in -) modest_next_index_ll' [llvm_code] is modest_init_mdp_env.modest_next_index_ll_def
    lemmas modest_next_index_hnr[sepref_fr_rules] = modest_next_index_ll.refine[unfolded modest_next_index_ll'.refine[OF modest_init_mdp_env_axioms]]
  
      
          
    lemmas [fcomp_norm_unfold] = modest_mdp_succ_DS_assn_def[symmetric] modest_index_DS_assn_def[symmetric]
  
  
    lemmas mop_is_admissible_hnr[sepref_fr_rules] = mop_modest_is_admissible_hnr[FCOMP mop_modest_is_admissible_correct]
    
    lemmas mop_is_empty_hnr[sepref_fr_rules] = modest_is_empty_hnr[FCOMP modest_is_empty_correct, of DS for DS]
    lemmas mop_index_begin_hnr[sepref_fr_rules] = modest_index_begin_hnr[FCOMP modest_index_begin_correct, of DS for DS]
    lemmas mop_get_state_hnr[sepref_fr_rules] = modest_get_state_hnr[FCOMP modest_get_state_get_state_correct, of DS for DS]
    lemmas mop_graph_succ_at_hnr[sepref_fr_rules] = modest_succ_at_hnr[FCOMP modest_succ_at_correct, of DS for DS]
    lemmas mop_has_succ_hnr[sepref_fr_rules] = modest_has_successor_hnr[FCOMP modest_has_successor_correct, of DS for DS]
    lemmas mop_next_id_hnr[sepref_fr_rules] = modest_next_index_hnr[FCOMP modest_next_index_correct, of DS for DS]
  
  
  end


end