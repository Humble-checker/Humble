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

  type_synonym modest_mdp = "nat list \<times> nat list \<times> nat list \<times> nat set \<times> nat set"

  locale modest_mdp_pre =
    fixes N::nat
    fixes DS :: "modest_mdp"
  begin 
  
    definition "St = (\<lambda> (St,Tr,Br,Av,Ta). St) DS"
    definition "Tr = (\<lambda> (St,Tr,Br,Av,Ta). Tr) DS"
    definition "Br = (\<lambda> (St,Tr,Br,Av,Ta). Br) DS"
    definition "Av = (\<lambda> (St,Tr,Br,Av,Ta). Av) DS"
    definition "Ta = (\<lambda> (St,Tr,Br,Av,Ta). Ta) DS"

    lemma DS_alt: "DS = (St,Tr,Br,Av,Ta)"
      unfolding St_def Tr_def Br_def  Av_def Ta_def
      apply(cases DS) by fast

  end

  lemma DS_sel_simps[simp]:
    "modest_mdp_pre.St (St,Tr,Br,Av,Ta) = St"
    "modest_mdp_pre.Tr (St,Tr,Br,Av,Ta) = Tr"
    "modest_mdp_pre.Br (St,Tr,Br,Av,Ta) = Br"
    "modest_mdp_pre.Av (St,Tr,Br,Av,Ta) = Av"
    "modest_mdp_pre.Ta (St,Tr,Br,Av,Ta) = Ta"
    unfolding modest_mdp_pre.St_def modest_mdp_pre.Tr_def modest_mdp_pre.Br_def 
      modest_mdp_pre.Av_def modest_mdp_pre.Ta_def 
    by auto

  locale modest_mdp_def = modest_mdp_pre N DS + modest_mdp_input_struc_def N St Tr Br Av Ta for N DS
  begin 

    text\<open>
      To deal with the cullable data structure, we need to be able to reason about the activated
      transition. This part focuses purely on building an infrastructure to make it easier to
      reason about that.
    \<close>

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
        let tn = Suc t in (
        if tn < uid (StI ! u) then 
          (tn,lid (TrI ! tn)) 
        else 
          (tn,b)
        )
      )"

    lemma next_activated_branch_t_in_intv: "next_activated_branch u t b = (t',b') \<Longrightarrow> in_intv (StI ! u) t \<Longrightarrow> t' < uid (StI ! u) \<Longrightarrow> in_intv (StI ! u) t'"
      unfolding next_activated_branch_def
      by (auto split: if_splits simp: Let_def in_intv_def)

    lemma next_activated_branch_succ: "t < uid (StI ! u) \<Longrightarrow> b < uid (TrI ! t) \<Longrightarrow> next_activated_branch u t b = (t',b') \<Longrightarrow> 
        t' \<ge> t \<and> (if t' = t then b' = Suc b else (if t' < uid (StI ! u) then (Suc b = uid (TrI ! t) \<and> b' = lid (TrI ! t')) else t' = uid (StI ! u) \<and> b' = b))"
      unfolding next_activated_branch_def
      by (auto split: if_splits simp: Let_def  le_antisym intro: less_imp_le_nat) 

    lemma next_activated_branch_same_trans: "next_activated_branch u t b = (t',b') \<Longrightarrow> Suc b < uid (TrI ! t) \<Longrightarrow> t' = t \<and> b' = Suc b"
      unfolding next_activated_branch_def by simp


    subsection \<open>Abstraction functions\<close>


    definition "K_\<alpha> = (\<lambda> u. if u \<in> Cm then (\<Union>x\<in>sn_intv (StI ! u). (!) Br ` sn_intv (TrI ! x)) else {})"

    definition "S_\<alpha> = {v. v < N}" 

    definition "SK_\<alpha> = (S_\<alpha>,K_\<alpha>)"

    lemma V0_MG_\<alpha>[simp]: "mdp_graph_defs.V0 SK_\<alpha> = S_\<alpha>"
      unfolding SK_\<alpha>_def by simp

    lemma K_MG_\<alpha>[simp]: "mdp_graph_defs.K SK_\<alpha> = K_\<alpha>"
      unfolding SK_\<alpha>_def by simp

    lemma S_\<alpha>_in_len_St: "S_\<alpha> \<subseteq> {0..< N}"
      unfolding S_\<alpha>_def
      by force


    subsection \<open>Graph structure\<close>

    abbreviation "E_\<alpha>' \<equiv> mdp_graph_defs.E_\<alpha> (S_\<alpha>,K_\<alpha>)"


  end

  locale modest_mdp_invar' = modest_mdp_def N DS + modest_mdp_input_struc_invar N St Tr Br Av Ta for N DS
  begin


    lemma E_\<alpha>_len_St[simp]: "E_\<alpha>' \<subseteq> {0..<N} \<times> {0..<N}"
      unfolding mdp_graph_defs.E_\<alpha>_def K_\<alpha>_def SK_\<alpha>_def
      apply (clarsimp intro!: Br_in_bound) 
      by(auto simp: Cm_def dest!: Tr_in_bound_intvD Br_in_bound_intvD intro!: Br_in_bound split: if_splits)

    lemma finite_E_\<alpha>[simp]: "finite E_\<alpha>'"
      using finite_subset[OF E_\<alpha>_len_St] by simp


    lemma finite_S_\<alpha>[simp]: "finite S_\<alpha>"
      using finite_subset[OF S_\<alpha>_in_len_St] by simp


    lemma E_\<alpha>_succ_N: "E_\<alpha>' `` {0..<N} \<subseteq> {0..<N}"
      unfolding SK_\<alpha>_def K_\<alpha>_def S_\<alpha>_def
      by (fastforce simp: mdp_graph_defs.E_\<alpha>_mem split: if_splits 
        intro!: Br_in_bound Br_in_bound_intvD Tr_in_bound_intvD) 

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
        unfolding in_intv_def mdp_graph_defs.E_\<alpha>_def K_\<alpha>_def SK_\<alpha>_def
        apply (clarsimp split: if_splits) 
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
      by (auto split: if_splits simp: Let_def intro!: Tr_nonempty Tr_in_bound_intvD elim: in_intv_gt) 

    lemma next_activated_branch_next_trans: "in_intv (TrI ! t) b \<Longrightarrow> next_activated_branch u t b = (t',b') \<Longrightarrow> t' < uid (StI ! u) \<Longrightarrow> t < t' \<Longrightarrow> b = uid(TrI!t) - 1 \<and> b' = lid(TrI!t')"
      unfolding next_activated_branch_def 
      by (auto split: if_splits simp: Let_def intro!: Suc_to_right Suc_lessI)

    lemma next_activated_branch_next_branch: "next_activated_branch v t b = (t',b') \<Longrightarrow> t = t' \<Longrightarrow> b' < b \<Longrightarrow> b' = Suc b"
      unfolding next_activated_branch_def
      by (auto split: if_splits simp: Let_def)


    interpretation mdp_graph SK_\<alpha> "{0..<N}" using mdp_graph_impl_modest .

    lemma Cm_not_empty: "u \<in> Cm \<longleftrightarrow> \<not>is_empty u"
      unfolding is_empty_def 
      by (auto simp: Tr_in_bound_intvD[of u, THEN Tr_nonempty] K_\<alpha>_def SK_\<alpha>_def Cm_mem elim!: state_has_transition[of u] ) 

  end

  locale modest_mdp_invar = modest_mdp_invar' N DS\<^sub>c for N DS\<^sub>c +
    fixes DS
    assumes DS_DEF: "DS = DS\<^sub>c"

  lemma modest_mdp_invar_alt: "DS = DS\<^sub>c \<Longrightarrow> modest_mdp_invar N DS\<^sub>c DS = modest_mdp_invar' N DS"
    unfolding modest_mdp_invar_def modest_mdp_invar_axioms_def by blast


  definition "modest_mdp_succ_DS_rel N DS\<^sub>c = br (modest_mdp_def.SK_\<alpha> N) (modest_mdp_invar N DS\<^sub>c)"

  definition "modest_mdp_succ_rel N \<equiv> { (DS,MG). (DS,MG) \<in> modest_mdp_succ_DS_rel N DS }"

  lemma modest_mdp_succ_rel_DS_eq: "(DS, K) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c \<Longrightarrow> DS = DS\<^sub>c"
    unfolding modest_mdp_succ_DS_rel_def
    by(auto simp: in_br_conv modest_mdp_invar_def modest_mdp_invar_axioms_def)

  lemma modest_mdp_succ_rel_alt: "(DS, K) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c \<longleftrightarrow> DS\<^sub>c = DS \<and> (DS, K) \<in> modest_mdp_succ_rel N"
    using modest_mdp_succ_rel_DS_eq
    unfolding modest_mdp_succ_DS_rel_def modest_mdp_succ_rel_def br_def modest_mdp_invar_def modest_mdp_invar_axioms_def 
    by auto


  subsection \<open>Successor index\<close>

  text \<open>A successor index for modest is a quintuple that contains the vertex \<open>iv\<close>, a transition 
    index \<open>itc\<close>, the next transition index \<open>itn\<close>, a branch index \<open>ibc\<close> and the next branch index 
    \<open>ibn\<close>. This is an implementation specifically for the SCC algorithm which needs to store 
    the progress of the DFS efficiently. We keep track of that progress by storing a stack of
    successor indices which is updated every time we progress in the DFS.\<close>
  type_synonym 'v modest_succ_index = "('v \<times> nat \<times> nat \<times> nat \<times> nat)"

  locale modest_successor_index_def = modest_mdp_def +
    fixes IDX :: "nat modest_succ_index"
  begin

    definition "iv = (\<lambda> (v,tc,tn,bc,bn). v) IDX"
    definition "itc = (\<lambda> (v,tc,tn,bc,bn). tc) IDX"
    definition "itn = (\<lambda> (v,tc,tn,bc,bn). tn) IDX"
    definition "ibc = (\<lambda> (v,tc,tn,bc,bn). bc) IDX"
    definition "ibn = (\<lambda> (v,tc,tn,bc,bn). bn) IDX"

    definition "Bri_\<alpha> tc \<equiv> if tc < itc then [] 
      else if tc = itc then map ((!) Br) (ls_intv (set_lid (TrI!tc) ibc)) 
      else map ((!) Br) (ls_intv (TrI!tc))" 

    definition "Tri_\<alpha> = map Bri_\<alpha> (ls_intv (StI ! iv))"

    definition "si_\<alpha> = concat Tri_\<alpha>"

    definition "\<alpha> = (iv, si_\<alpha>)"

    definition "Brin_\<alpha> tn \<equiv> if tn < itn then [] 
      else if tn = itn then map ((!) Br) (ls_intv (set_lid (TrI!tn) ibn)) 
      else map ((!) Br) (ls_intv (TrI!tn))" 

    definition "Trin_\<alpha> = map Brin_\<alpha> (ls_intv (StI ! iv))"

    definition "tl_si_\<alpha> = concat Trin_\<alpha>"


    definition "is_pred_index t b \<equiv> t < itc \<or> (t = itc \<and> b \<le> ibc)"

    definition "is_succ_index t b \<equiv> itc < t \<or> (t = itc \<and> ibc \<le> b)"

    lemma is_pred_index_cases[case_names Tr Br]: "is_pred_index t b \<Longrightarrow> (t < itc \<Longrightarrow> P) \<Longrightarrow> (t = itc \<Longrightarrow> b \<le> ibc \<Longrightarrow> P) \<Longrightarrow> P"
      unfolding is_pred_index_def by blast

    lemma is_succ_index_cases[case_names Tr Br]: "is_succ_index t b \<Longrightarrow> (itc < t \<Longrightarrow> P) \<Longrightarrow> (t = itc \<Longrightarrow> ibc \<le> b \<Longrightarrow> P) \<Longrightarrow> P"
      unfolding is_succ_index_def by blast

    lemma is_succ_indexI1: "itc < t \<Longrightarrow> is_succ_index t b"
      unfolding is_succ_index_def by blast

    lemma is_succ_indexI2: "t = itc \<Longrightarrow> ibc \<le> b \<Longrightarrow> is_succ_index t b"
      unfolding is_succ_index_def by blast

  end

  lemma modest_successor_index_simps[simp]:
    "modest_successor_index_def.iv (v,tc,tn,bc,bn) = v"
    "modest_successor_index_def.itc (v,tc,tn,bc,bn) = tc"
    "modest_successor_index_def.itn (v,tc,tn,bc,bn) = tn"
    "modest_successor_index_def.ibc (v,tc,tn,bc,bn) = bc"
    "modest_successor_index_def.ibn (v,tc,tn,bc,bn) = bn"
    unfolding modest_successor_index_def.iv_def modest_successor_index_def.itc_def modest_successor_index_def.itn_def
      modest_successor_index_def.ibc_def modest_successor_index_def.ibn_def by auto

  subsubsection \<open>Invariant\<close>

  locale modest_successor_index_invar = modest_successor_index_def N DS IDX + modest_mdp_invar' N DS for N DS IDX +
    assumes TBOUNDS: "itc < uid (StI ! iv)" \<comment> \<open>The current transition index is in range of the state's interval.\<close>
    and BCUPP: "ibc < uid (TrI ! itc)" \<comment> \<open>The current branch index is in range of the transition's interval.\<close>
    and NB: "next_activated_branch iv itc ibc = (itn, ibn)" \<comment> \<open>\<open>itn\<close> and \<open>ibn\<close> represent the next transition and branch index.\<close>
    and TLOW: "lid (StI ! iv) \<le> itc" \<comment> \<open>The current transition index is in range of the state's interval.\<close>
    and BCLOW: "lid (TrI ! itc) \<le> ibc" \<comment> \<open>The current branch index is in range of the transition's interval.\<close>
    and BNLOW: "itn < uid (StI ! iv) \<Longrightarrow> lid (TrI ! itn) \<le> ibn" \<comment> \<open>If the next transition is in range, its branch is greater than the lower bound.\<close>
    and VCM: "iv \<in> Cm"  \<comment> \<open>iv is a state that is neither a target nor avoid state.\<close>
  begin (*TODO: Update these to not contain StI and TrI*)

    lemma VBOUND: "iv < N"
      using VCM unfolding Cm_def by simp

    lemma NAV: "iv \<notin> Av"
      using VCM unfolding Cm_def by simp

    lemma NTA: "iv \<notin> Ta" 
      using VCM unfolding Cm_def by simp

    lemma TBOUND: "itc \<le> itn"
      using BCUPP NB TBOUNDS modest_mdp_def.next_activated_branch_succ by blast

    lemma TUPP: "itn \<le> uid (StI ! iv)" 
      by (metis BCUPP NB TBOUNDS le_def nat_le_linear next_activated_branch_succ)
  
    lemma BNUPP: "itn < uid (StI ! iv) \<Longrightarrow> ibn < uid (TrI ! itn)" 
      using BCLOW BCUPP NB VBOUND TBOUNDS TLOW in_intvI next_activated_branch_b_in_intv N_DEF by blast

    lemma in_intv_itc[simp, intro!]: "in_intv (StI ! iv) itc"
      unfolding in_intv_def
      using TBOUND TUPP TLOW TBOUNDS by blast

    lemma in_intv_itn[simp, intro!]: "itn < uid (StI ! iv) \<Longrightarrow> in_intv (StI ! iv) itn"
      unfolding in_intv_def
      using TBOUND TUPP TLOW by simp

    lemma in_intv_ibc[simp, intro!]: "in_intv (TrI ! itc) ibc"
      unfolding in_intv_def
      using BCUPP BCLOW by simp

    lemma in_intv_ibn[simp, intro!]: "itn < uid (StI ! iv) \<Longrightarrow> in_intv (TrI ! itn) ibn"
      unfolding in_intv_def
      using BNUPP BNLOW by simp

    lemma ls_intv_nth_eq_itc[simp]: "ls_intv (StI ! iv) ! (itc - lid (StI ! iv)) = itc"
      using in_intv_nth by blast

    lemma ls_intv_nth_eq_ibc[simp]: "ls_intv (TrI ! itc) ! (ibc - lid (TrI ! itc)) = ibc"
      by(auto intro: in_intv_nth)

    lemma ls_intv_nth_eq_itn[simp]: "itn < uid (StI ! iv) \<Longrightarrow> ls_intv (StI ! iv) ! (itn - lid (StI ! iv)) = itn"
      using in_intv_nth by blast

    lemma ls_intv_nth_eq_ibn[simp]: "itn < uid (StI ! iv) \<Longrightarrow> ls_intv (TrI ! itn) ! (ibn - lid (TrI ! itn)) = ibn"
      by(auto intro: in_intv_nth)

    lemma itc_act_trans[simp, intro!]: "itc \<in> sn_intv (StI ! iv)"
      by auto

    lemma itn_act_trans[simp, intro!]: "itn < uid (StI ! iv) \<Longrightarrow> itn \<in> sn_intv (StI ! iv)"
      by auto

    lemma tn_eq_tc_dest: "itn = itc \<Longrightarrow> itn < uid (StI ! iv)" "itc = itn \<Longrightarrow> itn < uid (StI ! iv)"
      using TBOUNDS by presburger+

    lemma ls_intv_nth_itc_id_val[dest]: "ls_intv (StI ! iv) ! i = itc \<Longrightarrow> i < cnt (StI ! iv) \<Longrightarrow> i = (itc - lid (StI ! iv))" 
    proof(rule ccontr)
      assume A: "i < cnt (StI ! iv)" and B: "ls_intv (StI ! iv) ! i = itc" and C: "i \<noteq> itc - lid (StI ! iv)"
      moreover have D: "distinct (ls_intv (StI ! iv))" by simp
      moreover have E: "itc - lid (StI ! iv) < cnt (StI ! iv)" 
        using tn_sub_lid_lt_cnt by blast
      ultimately show False using nth_eq_iff_index_eq[OF D, simplified, OF A E] 
        by force
    qed

    lemma ls_intv_nth_ibc_id_val[dest]: "ls_intv (TrI ! itc) ! i = ibc \<Longrightarrow> i < cnt (TrI ! itc) \<Longrightarrow> i = (ibc - lid (TrI ! itc))" 
    proof(rule ccontr)
      assume A: "i < cnt (TrI ! itc)" and B: "ls_intv (TrI ! itc) ! i = ibc" and C: "i \<noteq> ibc - lid (TrI ! itc)"
      moreover have D: "distinct (ls_intv (TrI ! itc))" by simp
      moreover have E: "ibc - lid (TrI ! itc) < cnt (TrI ! itc)"
        using VBOUND bn_sub_lid_lt_cnt 
        using in_intv_ibc in_intv_itc 
        by blast
      ultimately show False using nth_eq_iff_index_eq[OF D, simplified, OF A E] 
        by force
    qed

    lemma ls_intv_nth_itn_id_val[dest]: "ls_intv (StI ! iv) ! i = itn \<Longrightarrow> i < cnt (StI ! iv) \<Longrightarrow> i = (itn - lid (StI ! iv))" 
    proof(rule ccontr)
      assume A: "i < cnt (StI ! iv)" and B: "ls_intv (StI ! iv) ! i = itn" and C: "i \<noteq> itn - lid (StI ! iv)"
      moreover have D: "distinct (ls_intv (StI ! iv))" by simp
      moreover have E: "itc - lid (StI ! iv) < cnt (StI ! iv)" 
        using tn_sub_lid_lt_cnt by blast
      ultimately show False using nth_eq_iff_index_eq[OF D, simplified, OF A E] 
        by force
    qed

    lemma ls_intv_nth_ibn_id_val[dest]: "ls_intv (TrI ! itn) ! i = ibn \<Longrightarrow> i < cnt (TrI ! itn) \<Longrightarrow> i = (ibn - lid (TrI ! itn))" 
    proof(rule ccontr)
      assume A: "i < cnt (TrI ! itn)" and B: "ls_intv (TrI ! itn) ! i = ibn" and C: "i \<noteq> ibn - lid (TrI ! itn)"
      moreover have D: "distinct (ls_intv (TrI ! itn))" by simp
      moreover have E: "ibn - lid (TrI ! itn) < cnt (TrI ! itn)"
        using VBOUND bn_sub_lid_lt_cnt 
        using in_intv_ibn in_intv_itn 
        using B calculation(1) by force
      ultimately show False using nth_eq_iff_index_eq[OF D, simplified, OF A E] 
        by force
    qed

    lemma tc_sub_lid_lt_cnt[simp]: "itc - lid (StI ! iv) < cnt (StI ! iv)"
      using tn_sub_lid_lt_cnt[OF in_intv_itc] .

    lemma bc_sub_lid_lt_cnt[simp]: "ibc - lid (TrI ! itc) < cnt (TrI ! itc)"
      using bn_sub_lid_lt_cnt[OF in_intv_itc in_intv_ibc] .

    lemma tn_sub_lid_lt_cnt[simp]: "itn < uid (StI ! iv) \<Longrightarrow> itn - lid (StI ! iv) < cnt (StI ! iv)"
      using tn_sub_lid_lt_cnt[OF in_intv_itn] .

    lemma bn_sub_lid_lt_cnt[simp]: "itn < uid (StI ! iv) \<Longrightarrow> ibn - lid (TrI ! itn) < cnt (TrI ! itn)"
      using bn_sub_lid_lt_cnt[OF in_intv_itn in_intv_ibn] .

    lemma teI_bound: "itn \<le> length Tr - Suc 0" 
      using Tr_in_bound_intvD VBOUND in_intv_itn
      using St_in_bound TUPP dual_order.trans 
      by fastforce

    lemma teI_bound_strict: "itn < uid (StI ! iv) \<Longrightarrow> itn < length Tr - Suc 0" 
      using Tr_in_bound_intvD VBOUND in_intv_itn by blast

    lemma itc_bound: "itc < length Tr - Suc 0"
      using Tr_in_bound_intvD VBOUND in_intv_itc by blast

    lemma beI_bound: "ibn < length Br" 
      using Br_in_bound_intvD in_intv_ibn less_or_eq_imp_le teI_bound 
      by (metis BCUPP NB TBOUNDS Tr_in_bound_intvD VBOUND in_intv_ibc in_intv_itc next_activated_branch_succ teI_bound_strict)

    lemma ibc_bound: "ibc < length Br"
      using Br_in_bound_intvD in_intv_ibc itc_bound by blast

    lemma lid_lt_uid_tc: "lid (TrI ! itc) < uid (TrI ! itc)"
      using BCLOW BCUPP by auto

    lemma lid_lt_uid_tn: "itn < uid (StI ! iv) \<Longrightarrow> lid (TrI ! itn) < uid (TrI ! itn)"
      using BNLOW BNUPP by auto

    lemma I1: "itc = itn \<Longrightarrow> (ibn > 0 \<and> ibc = ibn - 1)" 
      by (metis BCUPP NB TBOUNDS diff_Suc_1 next_activated_branch_succ zero_less_Suc)

    lemma I2: "itn = uid (StI ! iv) \<Longrightarrow> ibc = ibn \<and> itc < itn \<and> ibn = uid (TrI ! itc) - 1"
      using BCUPP NB in_intv_def next_activated_branch_succ
      by (metis Suc_lessI TBOUNDS diff_Suc_1 less_not_refl next_activated_branch_same_trans)


    lemma I3: "itc < itn \<Longrightarrow> itn < uid (StI ! iv) \<Longrightarrow> ibc = uid (TrI ! itc) - 1 \<and> ibn = lid (TrI ! itn)"
      using BCLOW BCUPP NB in_intvI next_activated_branch_next_trans by blast

    lemma I3': "itn \<noteq> itc \<Longrightarrow> itn < uid (StI ! iv) \<Longrightarrow> ibc = uid (TrI ! itc) - 1 \<and> ibn = lid (TrI ! itn)"
      using I3 TBOUND by auto

    lemma Bri_\<alpha>_itc_ne: "Bri_\<alpha> itc \<noteq> []"
      unfolding Bri_\<alpha>_def
      by auto

    lemma ne_si_\<alpha>: "si_\<alpha> \<noteq> []"
      unfolding si_\<alpha>_def Tri_\<alpha>_def
      using Bri_\<alpha>_itc_ne by auto

    lemma hd_si_\<alpha>: "hd si_\<alpha> = Br!ibc"
      unfolding si_\<alpha>_def
      apply(subst empty_leading_hd_concat[where ?i="itc - lid (StI ! iv)"])
      subgoal unfolding Tri_\<alpha>_def 
        by (auto simp: Bri_\<alpha>_itc_ne)
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
        by (auto simp: hd_ls_intv_set_lid[OF BCUPP] intro!: pos_cnt_set_lid)
      done

    lemma Brin_\<alpha>_itc_ne: "itn < uid (StI ! iv) \<Longrightarrow> Brin_\<alpha> itn \<noteq> []"
      unfolding Brin_\<alpha>_def by auto 

    lemma ne_tl_si_\<alpha>: "itn < uid (StI ! iv) \<Longrightarrow> tl_si_\<alpha> \<noteq> []"
      unfolding tl_si_\<alpha>_def Trin_\<alpha>_def
      using Brin_\<alpha>_itc_ne by auto

    lemma empty_tl_si_\<alpha>: "itn = uid (StI ! iv) \<Longrightarrow> tl_si_\<alpha> = []"
      unfolding tl_si_\<alpha>_def Trin_\<alpha>_def
      apply clarsimp using Brin_\<alpha>_itc_ne 
      using Brin_\<alpha>_def in_intv_ubD by presburger

    lemma hd_tl_si_\<alpha>: "itn < uid (StI ! iv) \<Longrightarrow> hd tl_si_\<alpha> = Br!ibn"
      unfolding tl_si_\<alpha>_def Trin_\<alpha>_def Brin_\<alpha>_def
      apply(subst empty_leading_hd_concat[where ?i="itn - lid (StI ! iv)"])
      subgoal 
        by (auto simp: in_intv_lbD intro!: pos_cnt_set_lid)
      subgoal apply(subst nth_map)
        subgoal by (auto intro!:less_trans[OF _ tn_sub_lid_lt_cnt])
        subgoal using basic_trans_rules(19) by fastforce
        done
      subgoal 
        by (auto intro!: pos_cnt_set_lid simp: hd_ls_intv_set_lid[OF BCUPP])
      subgoal
        using TBOUND TLOW apply clarsimp
        apply(subst hd_map)
        by (auto simp: hd_ls_intv_set_lid[OF BNUPP] intro!: pos_cnt_set_lid)
      done


    lemma length_Trin_\<alpha>: "length Trin_\<alpha> = length Tri_\<alpha>"
      unfolding Trin_\<alpha>_def Tri_\<alpha>_def by simp

    lemma length_Tri_\<alpha>: "length Tri_\<alpha> = cnt (StI ! iv)"
      unfolding Tri_\<alpha>_def by simp


    lemma Trin_\<alpha>_nth_eq_upd_Tri_\<alpha>:
      fixes iitc
      defines "iitc \<equiv> itc - lid (StI ! iv)" 
      assumes IC: "i < cnt (StI ! iv)"
      shows "Trin_\<alpha> ! i = Tri_\<alpha>[iitc := tl (Tri_\<alpha> ! (iitc))] ! i"
    proof(cases "itn = uid (StI ! iv)")
      case True
      note [simp] = True
      with I2 have [simp]:  "ibc = ibn" "uid (TrI ! itc) = Suc ibn" and "itc < itn"
        using BCUPP by auto 

      consider (le)"i < iitc" | (eq) "i = iitc" | (ge) "i > iitc"
        by linarith

      hence "Tri_\<alpha>[iitc := tl (Tri_\<alpha> ! (iitc))] ! i = []"
        apply(cases)
        subgoal
          unfolding Tri_\<alpha>_def Bri_\<alpha>_def
          using IC by(auto simp: iitc_def)
        subgoal
          unfolding Tri_\<alpha>_def Bri_\<alpha>_def
          using IC TLOW by(auto simp: iitc_def)
        subgoal
          unfolding Tri_\<alpha>_def Bri_\<alpha>_def iitc_def
          using TLOW NB IC tc_sub_lid_lt_cnt Suc_diff_le
          by (fastforce simp: next_activated_branch_def split: if_splits)
        done

      moreover have "Trin_\<alpha> ! i = []" unfolding Trin_\<alpha>_def Brin_\<alpha>_def
        apply(subst nth_map)
        using IC apply simp
        using IC by (auto simp: uid_as_cnt_plus_lid)

      ultimately show ?thesis
        by presburger
    next
      case False

      define iitn where "iitn \<equiv> itn - lid (StI ! iv)" 
      have toI1:"itn \<noteq> itc \<Longrightarrow> iitc < iitn"
        unfolding iitc_def iitn_def using TBOUND TLOW by linarith

      have iitcC: "iitc < cnt (StI ! iv)"
        by (simp add: assms(1))

      have ILE: "iitc \<le> iitn"
        unfolding iitc_def iitn_def using TBOUND by simp

      have iitnC: "iitn \<le> cnt (StI ! iv)"
        using TUPP iitn_def nat_less_le tn_sub_lid_lt_cnt by force

      have TLU: "itn < uid (StI ! iv)"
        using False TUPP by simp


      consider (le)"i < iitc" | (eq) "i = iitc" | (ge) "i > iitc"
        by linarith
      thus ?thesis
      proof(cases)
        case le

        moreover have BLE: "i < iitc \<Longrightarrow> Brin_\<alpha> (ls_intv (StI ! iv) ! i) = []"
        proof -
          assume "i < iitc"
          moreover have "i < iitn \<Longrightarrow> Brin_\<alpha> (ls_intv (StI ! iv) ! i) = []"
            unfolding Brin_\<alpha>_def iitn_def
            using assms(2) by auto
          ultimately show ?thesis
            using ILE by linarith
        qed
        moreover have  BLEN: "i < iitc \<Longrightarrow> Bri_\<alpha> (ls_intv (StI ! iv) ! i) = []"
          unfolding Bri_\<alpha>_def iitc_def
          using assms(2) by auto
        ultimately show ?thesis unfolding Trin_\<alpha>_def Tri_\<alpha>_def   
          using BLE BLEN iitcC by auto

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

        have NE: "i \<noteq> iitc"
          using ge by blast


        show ?thesis 
        proof(cases "itn = itc")
          case True
          hence "iitn = iitc"
            using assms(1) iitn_def by argo
          thus ?thesis 
            unfolding Trin_\<alpha>_def Tri_\<alpha>_def Brin_\<alpha>_def Bri_\<alpha>_def
            using NE by (auto simp: IC True iitn_def)

        next
          case False

          then show ?thesis 
            unfolding Trin_\<alpha>_def Tri_\<alpha>_def Brin_\<alpha>_def Bri_\<alpha>_def
            using TBOUND IC NE I3'[OF False TLU] NB
            by (auto simp: iitc_def next_activated_branch_def split: if_splits)
        qed
      qed
    qed


    lemma tl_si_\<alpha>_eq: "tl_si_\<alpha> = tl si_\<alpha>"
      unfolding si_\<alpha>_def tl_si_\<alpha>_def
      apply(subst empty_leading_tl_concat[where ?i="itc-lid (StI ! iv)"])
      subgoal by (auto intro!: pos_cnt_set_lid simp:  Tri_\<alpha>_def Bri_\<alpha>_def )
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

    lemma Bri_\<alpha>_next:  "modest_successor_index_def.Bri_\<alpha> DS (iv, itn, tn', ibn, bn') = Brin_\<alpha>"
      unfolding modest_successor_index_def.Bri_\<alpha>_def Brin_\<alpha>_def
      by auto

    lemma Tri_\<alpha>_next: "modest_successor_index_def.Tri_\<alpha> DS (iv, itn, tn', ibn, bn') = Trin_\<alpha>"
      unfolding modest_successor_index_def.Tri_\<alpha>_def Trin_\<alpha>_def
      using Bri_\<alpha>_next by force

    lemma si_\<alpha>_next: "modest_successor_index_def.si_\<alpha> DS (iv,itn,tn',ibn,bn') = tl_si_\<alpha>"
      unfolding modest_successor_index_def.si_\<alpha>_def tl_si_\<alpha>_def
      using Tri_\<alpha>_next by presburger


    lemma "itn < uid (StI ! iv) \<Longrightarrow> length si_\<alpha> > Suc 0"
      using ne_si_\<alpha> ne_tl_si_\<alpha> apply (clarsimp simp: neq_Nil_conv)  
      by (auto simp: neq_Nil_conv simp flip: tl_si_\<alpha>_eq dest: eq_Cons_hd_tl)

    lemma assumes L1: "length si_\<alpha> > Suc 0" shows "itn < uid (StI ! iv)"
    proof -

      from L1 have "length tl_si_\<alpha> > 0"
        using tl_si_\<alpha>_eq by simp

      hence "tl_si_\<alpha> \<noteq> []"
        by blast

      hence "itn \<noteq> uid (StI ! iv)"
        using empty_tl_si_\<alpha>
        by presburger

      thus ?thesis
        using TUPP by simp
    qed

    lemma length_si_\<alpha>_has_next: "length si_\<alpha> > Suc 0 \<longleftrightarrow> itn < uid (StI ! iv)"
    proof(rule iffI)
      assume "Suc 0 < length si_\<alpha>"

      hence "length tl_si_\<alpha> > 0"
        using tl_si_\<alpha>_eq by simp

      hence "tl_si_\<alpha> \<noteq> []"
        by blast

      hence "itn \<noteq> uid (StI ! iv)"
        using empty_tl_si_\<alpha>
        by presburger

      thus "itn < uid (StI ! iv)"
        using TUPP by simp
    next
      show "itn < uid (StI ! iv) \<Longrightarrow> Suc 0 < length si_\<alpha>"
        using ne_si_\<alpha> ne_tl_si_\<alpha> apply (clarsimp simp: neq_Nil_conv)  
        by (auto simp: neq_Nil_conv simp flip: tl_si_\<alpha>_eq dest: eq_Cons_hd_tl)
    qed


    lemma Bri_\<alpha>_set_img_Br: "in_intv (StI ! iv) t \<Longrightarrow> u \<in> set (Bri_\<alpha> t) \<Longrightarrow> u \<in> (!) Br ` sn_intv (TrI ! t)"
      unfolding Bri_\<alpha>_def using BCLOW BCUPP 
      by (auto split: if_splits intro!: in_intvI image_sn_intv elim!: in_intv_smaller_set_lid) 

    lemma Br_in_Bri_\<alpha>_succ_tr: "is_succ_index t b \<Longrightarrow> in_intv (TrI ! t) b
      \<Longrightarrow> Br ! b \<in> set (Bri_\<alpha> t)"
      apply(erule is_succ_index_cases)
      subgoal
        unfolding Bri_\<alpha>_def
        by (auto)
      subgoal
        unfolding Bri_\<alpha>_def
        by (auto intro!: image_sn_intv elim!: in_intv_le_set_lid) 
      done

    lemma si_\<alpha>_to_K_\<alpha>: "u \<in> set si_\<alpha> \<Longrightarrow> u \<in> K_\<alpha> iv"
      unfolding K_\<alpha>_def si_\<alpha>_def Tri_\<alpha>_def
      using VCM
      apply clarsimp
      by (auto elim: Bri_\<alpha>_set_img_Br)

    lemma K_\<alpha>_to_si_\<alpha>: 
      assumes K: "u \<in> K_\<alpha> iv"
      assumes TC[simp]: "itc = lid (StI ! iv)"
      assumes BC[simp]: "ibc = lid (TrI ! itc)"
      shows "u \<in> set si_\<alpha>"
    proof -

      have AUX1: "is_succ_index t b" if "in_intv (StI ! iv) t" and "in_intv (TrI ! t) b" for t b
      proof(cases "t = itc")
        case True
        note [simp] = True

        then show ?thesis
        using that(2) by (auto intro!: is_succ_indexI2)
      next
        case False
        hence "itc < t" 
          using that(1) 
          by (simp add: in_intv_def)
        then show ?thesis 
          by(auto intro: is_succ_indexI1)
      qed

      show ?thesis
        using K
        unfolding K_\<alpha>_def si_\<alpha>_def Tri_\<alpha>_def
        apply (clarsimp split: if_splits simp: )
        subgoal for t b
          using AUX1[THEN Br_in_Bri_\<alpha>_succ_tr, of t b, simplified] sn_intv_member by blast
        done
    qed
  end


  subsubsection \<open>Successor index refinement relation\<close>
  definition "modest_succ_index_DS_rel N DS = br (modest_successor_index_def.\<alpha> DS) (modest_successor_index_invar N DS)"

  definition "modest_succ_index_rel N = {(ci,c). \<exists>DS. (ci,c) \<in> modest_succ_index_DS_rel N DS}"

  lemma modest_succ_index_rel_vD: "((v,tc,te,bc,be), v',si) \<in> modest_succ_index_DS_rel N DS \<Longrightarrow> v'=v"
    by(auto simp: modest_succ_index_DS_rel_def in_br_conv modest_successor_index_def.\<alpha>_def)
  
  subsection \<open>Concrete Operations for Indices\<close>

  context modest_mdp_def
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

    definition "modest_calculate_successor v t b = do {
      ASSERT(Suc b \<le> length Br);
      let bn = Suc b;
      ASSERT(Suc t < length Tr);
      if (bn < Tr ! (Suc t)) 
      then do {
        RETURN (t,bn)
      } else do {
        let tn = Suc t;
        ASSERT(Suc v < length St);
        if(tn < St ! (Suc v)) then do{
          ASSERT (tn < length Tr);
          RETURN (tn, Tr ! tn) 
        } else
          RETURN (tn,b)
      }
    }"

  end


  context modest_mdp_invar'
  begin

    lemma get_successor_of_branch_refine:
      assumes "b < length Br"
      shows "get_successor_of_branch b \<le> SPEC (\<lambda> r. r = Br ! b)"
      unfolding get_successor_of_branch_def
      apply(refine_vcg)
      using Br_in_bound assms 
      apply(auto simp: N_DEF)
      done




    lemma modest_calculate_successor_correct: "v < N \<Longrightarrow> in_intv (StI ! v) t \<Longrightarrow> in_intv (TrI ! t) b \<Longrightarrow> modest_calculate_successor v t b \<le> RETURN (next_activated_branch v t b)"
      unfolding modest_calculate_successor_def next_activated_branch_def 
      apply(refine_vcg)
      subgoal using Br_in_bound_intvD  Tr_in_bound_intvD le_simps(3) by blast
      subgoal using Tr_in_bound_intvD less_minus_Suc_zero by blast
      subgoal by (auto simp flip: uid_sorted_intvs[OF sorted_Tr]) 
      subgoal by (auto simp: N_DEF) 
      subgoal by (auto simp: sorted_Tr simp flip: uid_sorted_intvs[OF sorted_St] elim: Tr_in_boundD)
      subgoal by (auto simp flip: uid_sorted_intvs[OF sorted_Tr] uid_sorted_intvs[OF sorted_St] )
      done

    lemma S_\<alpha>D1: "u \<in> S_\<alpha> \<Longrightarrow> u < N"
      unfolding S_\<alpha>_def by blast

  end

  subsection \<open>Index operations\<close>

  
  context modest_mdp_def
  begin

    text\<open> 
      For efficiency, one could try to combine modest_is_empty and modest_index_begin, currently, 
      we are iterating the transitions once in each one, this could be combined in \<open>modest_is_empty\<close>.
    \<close>

    definition "modest_admissible v = RETURN True"

    definition "modest_is_empty u = RETURN (u \<in> Av \<or> u \<in> Ta)"

    definition "modest_index_begin v = do{
      let tl = St ! v;
      ASSERT(tl < length Tr);
      let b = Tr ! tl;
      (tn,bn) \<leftarrow> modest_calculate_successor v tl b;
      RETURN (v,tl,tn,b,bn)
    }"

  end

  context modest_successor_index_def 
  begin
    
    definition "modest_get_state = iv"

    definition "modest_succ_at \<equiv> Br!ibc"

    definition "modest_has_successor \<equiv> (itn < St ! (Suc iv))"

    definition "modest_next_index = do{
      (tn',bn') \<leftarrow> modest_calculate_successor iv itn ibn;
      RETURN (iv,itn,tn',ibn,bn')
    }"

  end

  
  subsection \<open>Correctness of operations\<close>


  context modest_mdp_invar'
  begin
    interpretation mdp_graph SK_\<alpha> "{0..<N}" using mdp_graph_impl_modest .


    lemma init_id_modest_index_begin_correct: 
      assumes VN: "v < N" 
      and NE: "\<not>is_empty v"
      shows"modest_index_begin v \<le> \<Down>(modest_succ_index_DS_rel N DS) (index_begin v)"
    proof -         

      (*We introduce this intermediate function as part of a two-step refinement*)

      define index_begin_inter where "index_begin_inter \<equiv> do{
        let tl = St ! v;
        ASSERT(tl < length Tr);
        let b = Tr ! tl;
        let (tn,bn) = next_activated_branch v tl b;
        RETURN (v,tl,tn,b,bn)
      }"

      have AUX1: "x = y \<Longrightarrow> (x,y) \<in> Id" for x y
        by blast

      (*First refinement step*)

      have REF1: "modest_index_begin v \<le> \<Down>Id index_begin_inter"
        unfolding modest_index_begin_def index_begin_inter_def
        apply(refine_vcg order_trans[OF modest_calculate_successor_correct] AUX1)
        apply(clarsimp_all)
        subgoal using VN .
        subgoal using VN N_DEF Sorted_St by auto
        subgoal using Sorted_Tr N_DEF Sorted_St Tr_in_bound_intvD assms(1) by blast
        done

      (*Second refinement step*)

      have INV1: "next_activated_branch v (St ! v) (Tr ! (St ! v)) = (tn, bn) \<Longrightarrow>
          modest_successor_index_invar N DS (v, St ! v, tn, Tr ! (St ! v), bn)" for tn bn
        apply(unfold_locales)
        apply clarsimp_all
        subgoal
          using Sorted_St VN
          by (auto simp: N_DEF) 
        subgoal
          using Sorted_Tr Sorted_St VN
          by (auto simp: N_DEF intro!: Tr_in_boundD) 
        subgoal 
          by (simp add: VN[unfolded N_DEF] sorted_St)
        subgoal
          using Sorted_Tr Sorted_St VN
          by (auto simp: N_DEF intro!: Tr_in_boundD) 
        subgoal 
          using Sorted_Tr Sorted_St VN
          by (auto simp: N_DEF elim!: next_activated_branch_b_in_intv[OF VN] intro!: Tr_in_boundD) 
        subgoal
          by(auto simp: Cm_not_empty assms(2))
        done

      have \<alpha>1: "modest_successor_index_def.\<alpha> DS (v, St ! v, tn, Tr ! (St ! v), bn) \<in> {v} \<times> {si. set si = K_\<alpha> v}" 
        if "next_activated_branch v (St ! v) (Tr ! (St ! v)) = (tn, bn)"
        for tn bn 
      proof -
        interpret modest_successor_index_invar N DS "(v, St ! v, tn, Tr ! (St ! v), bn)"
          using INV1[OF that] .

        have "K_\<alpha> iv = set si_\<alpha>"
          apply(rule equalityI)
          subgoal
            apply(safe; erule K_\<alpha>_to_si_\<alpha>)
            using sorted_Tr itc_bound 
            by (auto simp: VN[unfolded N_DEF] in_intv_sorted_intvs sorted_St )
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
        subgoal
          using N_DEF Sorted_St assms(1) by(auto intro!: less_trans[OF _ St_in_bound[OF VN] ])
        subgoal for tn bn
          unfolding modest_succ_index_DS_rel_def
          by (auto simp: refine_pw_simps pw_le_iff in_br_conv INV1 \<alpha>1)
        done

      show ?thesis
        using REF1 REF2 by auto
    qed

  end

  subsection \<open>Refinement to concrete\<close>

  lemma modest_is_empty_refine_aux:
    assumes VB: "v < N" 
    and GREL: "(DS,MG) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c" 
    shows "modest_mdp_def.modest_is_empty DS v \<le> mop_is_empty MG v"
  proof -
    have INV': "modest_mdp_invar' N DS"
      by (metis GREL in_br_conv modest_mdp_invar.axioms(1) modest_mdp_succ_DS_rel_def modest_mdp_succ_rel_DS_eq)

    from GREL interpret modest_mdp_invar N DS\<^sub>c DS unfolding modest_mdp_succ_DS_rel_def
      by(auto simp: in_br_conv)

    from GREL have EDEF[simp]: "MG = SK_\<alpha>" unfolding modest_mdp_succ_DS_rel_def modest_mdp_def.SK_\<alpha>_def
      by(auto simp: in_br_conv DS_DEF)

    obtain i where A: "i\<in>sn_intv (StI ! v)" "cnt (TrI ! i) > 0"
      using state_has_transition[OF VB]
      by(auto simp: Tr_in_bound_intvD[OF VB, THEN Tr_nonempty] )

    have E1: "v \<notin> Cm \<Longrightarrow> mdp_graph_defs.is_empty SK_\<alpha> v"
      unfolding mdp_graph_defs.is_empty_def SK_\<alpha>_def K_\<alpha>_def by auto

    show ?thesis                                   
      unfolding modest_mdp_def.modest_is_empty_def mop_is_empty_def mdp_graph_defs.is_empty_def
      using A(1,2) VB
      by (auto simp: Cm_mem Av_Cm Ta_Cm DS_DEF modest_mdp_def.K_\<alpha>_def) 
  qed


  lemma modest_is_admissible_refine_aux:
    assumes VB: "v < N"
    and GREL: "(DS, MG) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c"
    shows "modest_mdp_def.modest_admissible v \<le> mop_is_admissible MG v"
  proof -
    have INV': "modest_mdp_invar' N DS"
      by (metis GREL in_br_conv modest_mdp_invar.axioms(1) modest_mdp_succ_DS_rel_def modest_mdp_succ_rel_DS_eq)

    from GREL interpret modest_mdp_invar N DS\<^sub>c DS unfolding modest_mdp_succ_DS_rel_def
      by(auto simp: in_br_conv)

    from GREL have EDEF[simp]: "MG = SK_\<alpha>" unfolding modest_mdp_succ_DS_rel_def modest_mdp_def.SK_\<alpha>_def
      by(auto simp: in_br_conv DS_DEF)

    show ?thesis
      unfolding modest_mdp_def.modest_admissible_def mop_is_admissible_def
      apply(refine_vcg)
      apply(cases DS)
      using VB by (auto simp:  is_admissible_def modest_mdp_def.SK_\<alpha>_def 
        modest_mdp_def.S_\<alpha>_def op_antpar_mem_any1_def DS_DEF)
  qed


  lemma modest_index_begin_refine_aux: 
    assumes VB: "v < N"
    and NE: "\<not>mdp_graph_defs.is_empty MG v "
    and GREL: "(DS,MG) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c" 
    shows "modest_mdp_def.modest_index_begin DS v \<le> \<Down>(modest_succ_index_DS_rel N DS) (mop_index_begin MG v)"
  proof -

    have INV': "modest_mdp_invar' N DS"
      by (metis GREL in_br_conv modest_mdp_invar.axioms(1) modest_mdp_succ_DS_rel_def modest_mdp_succ_rel_DS_eq)

    from GREL interpret modest_mdp_invar N DS\<^sub>c DS unfolding modest_mdp_succ_DS_rel_def
      by(auto simp: in_br_conv)

    from GREL have EDEF[simp]: "MG = SK_\<alpha>" "DS = DS\<^sub>c" unfolding modest_mdp_succ_DS_rel_def modest_mdp_def.SK_\<alpha>_def
      by(auto simp: in_br_conv DS_DEF)
 

    show ?thesis
      unfolding mop_index_begin_def 
      apply(rule modest_mdp_invar'.init_id_modest_index_begin_correct[OF INV', THEN order_trans] )
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
      unfolding modest_mdp_succ_DS_rel_def modest_mdp_def.SK_\<alpha>_def by(auto simp: in_br_conv)

    show ?thesis
      unfolding mop_graph_succ_at_def modest_succ_at_def mdp_graph_defs.successor_at_def
        modest_succ_index_DS_rel_def modest_mdp_succ_rel_def 
      using ibc_bound Br_in_bound[of bc]
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
      unfolding modest_mdp_succ_DS_rel_def modest_mdp_def.SK_\<alpha>_def by(auto simp: in_br_conv)


    show ?thesis
      unfolding mop_has_succ_def
      using TBOUND TUPP modest_has_successor_correct 
      using NAV NTA VBOUND  
      by (auto simp: \<alpha>_def)
  qed


  lemma(in modest_successor_index_invar) modest_next_index_correct: 
    assumes NB': "next_activated_branch iv itn ibn = (t, b)"
    assumes VD[simp]: "v' = iv"
    assumes SID[simp]: "si' = si_\<alpha>"
    assumes HN: "mdp_graph_defs.has_next \<alpha>"
    shows "((iv, itn, t, ibn, b), mdp_graph_defs.next_index (v', si'))
           \<in> modest_succ_index_DS_rel N DS"
  proof -

    have ABS: "modest_successor_index_def.\<alpha> DS (iv, itn, t, ibn, b) = mdp_graph_defs.next_index (v', si')" 
    unfolding mdp_graph_defs.next_index_def modest_successor_index_def.\<alpha>_def
    by (auto simp: VD si_\<alpha>_next tl_si_\<alpha>_eq) 

    have HN': "itn < uid (StI ! iv)"
      using VBOUND HN modest_has_successor_correct modest_has_successor_def sorted_St uid_sorted_intvs N_DEF by metis

    have INV: "modest_successor_index_invar N DS (iv, itn, t, ibn, b)"
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
      done

    show ?thesis
      by(auto simp: modest_succ_index_DS_rel_def in_br_conv INV ABS)
  qed


  lemma modest_next_index_refine_aux: 
    assumes SREL: "((v,tc,te,bc,be),(v',si')) \<in> modest_succ_index_DS_rel N DS" 
    and GREL: "(DS,MG) \<in> modest_mdp_succ_DS_rel N DS\<^sub>c" 
    and HN: "mdp_graph_defs.has_next (v',si')"
    shows "(modest_successor_index_def.modest_next_index DS (v,tc,te,bc,be)) \<le> \<Down>(modest_succ_index_DS_rel N DS\<^sub>c) (mop_next_id MG (v',si'))"
  proof -

      
    from SREL interpret modest_successor_index_invar N DS "(v,tc,te,bc,be)" 
      unfolding modest_succ_index_DS_rel_def by(auto simp: in_br_conv)

    from SREL have I_DEF[simp]: "v' = v" "si' = si_\<alpha>"
      unfolding modest_succ_index_DS_rel_def modest_successor_index_def.\<alpha>_def by(auto simp: in_br_conv \<alpha>_def)

    from GREL have E_SUCC_DEF[simp]: "MG = SK_\<alpha>"
      unfolding modest_mdp_succ_DS_rel_def modest_mdp_def.SK_\<alpha>_def by(auto simp: in_br_conv)

    have DS\<^sub>c_eq[simp]: "DS\<^sub>c = DS"
      using GREL modest_mdp_succ_rel_DS_eq by blast

    from HN have HN': "mdp_graph_defs.has_next \<alpha>"
      unfolding \<alpha>_def by auto
    have HS: "modest_has_successor" using HN' modest_has_successor_correct by blast
    hence HS': "itn < uid (StI ! iv)" unfolding modest_has_successor_def 
      using VBOUND sorted_St uid_sorted_intvs N_DEF by metis

    show ?thesis
      unfolding mop_next_id_def modest_next_index_def
      apply(refine_vcg order_trans[OF modest_calculate_successor_correct]) 
      subgoal using N_DEF VBOUND by blast
      subgoal using HS' in_intv_itn by blast
      subgoal
        using HS' in_intv_ibn by blast
      subgoal
        using HN' modest_next_index_correct by force
      done
  qed


  context modest_init_mdp_env_defs
  begin
  
    interpretation disj_set_list_tuple_defs N N ni ni .
  
    definition op_modest_is_disabled_transitions :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool" where 
      "op_modest_is_disabled_transitions = (\<lambda> (St,Tr,Br,Av,Ta) v. op_set_member v Av \<or> op_set_member v Ta)"
    sepref_register op_modest_is_disabled_transitions :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool"
  

    definition St_nth_lid :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat" where "St_nth_lid = (\<lambda> (St,Tr,Br,Av,Ta) u. b_assn_open_block_fun2 u St (\<lambda> u St. (St ! u)))"
    definition St_nth_uid :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat" where "St_nth_uid = (\<lambda> (St,Tr,Br,Av,Ta) u. b_assn_open_block_fun2 u St (\<lambda> u St. (St ! (Suc u))))"
  
    definition Tr_nth :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat" where "Tr_nth = (\<lambda> (St,Tr,Br,Av,Ta) t. b_assn_open_block_fun Tr (\<lambda> Tr. (Tr ! t)))"
  
    lemma St_nth_lid_alt: "St_nth_lid DS t = modest_mdp_pre.St DS ! t"
      unfolding St_nth_lid_def modest_mdp_pre.St_def b_assn_open_block_fun2_def by (cases DS; auto)
    lemma St_nth_uid_alt: "St_nth_uid DS t = modest_mdp_pre.St DS ! (Suc t)"
      unfolding St_nth_uid_def modest_mdp_pre.St_def b_assn_open_block_fun2_def by (cases DS; auto)
  
    lemma Tr_nth_alt: "Tr_nth DS t = modest_mdp_pre.Tr DS ! t"
      unfolding Tr_nth_def modest_mdp_pre.Tr_def b_assn_open_block_fun_def by (cases DS; auto)
  
    definition mop_modest_get_target_of_branch :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat nres" where 
      "mop_modest_get_target_of_branch = (\<lambda> (St,Tr,Br,Av,Ta) b. 
      do {
        ASSERT (b < length Br);
        r \<leftarrow> b_assn_open_block Br (\<lambda>Br. RETURN (Br ! b));
        ASSERT (r < N);
        let r = op_bound_val (\<lambda> x. x < N) r;
        RETURN r
      })"
    sepref_register mop_modest_get_target_of_branch :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat nres"
  
                                                                                               
    lemma modest_get_target_of_branch_alt: "mop_modest_get_target_of_branch = modest_mdp_def.get_successor_of_branch N"
      unfolding modest_mdp_def.get_successor_of_branch_def mop_modest_get_target_of_branch_def b_assn_open_block_def
      apply(rule ext)+
      apply (auto simp: Let_def)
      done
  
  
  subsection \<open>Locale independent operations\<close>

  
    definition mop_modest_calculate_successor :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) nres" where 
    "mop_modest_calculate_successor DS v t b = do {
      ASSERT(Suc b \<le> length (modest_mdp_pre.Br DS));
      let bn = Suc b;
      ASSERT(Suc t < length (modest_mdp_pre.Tr DS));
      if (bn < Tr_nth DS (Suc t)) 
      then do {
        RETURN (t,bn)
      } else do {
        let tn = Suc t;
        ASSERT(Suc v < length (modest_mdp_pre.St DS));
        if(tn < St_nth_uid DS v) then do{
          ASSERT (tn < length (modest_mdp_pre.Tr DS));
          RETURN (tn,Tr_nth DS tn) 
        } else
          RETURN (tn,b)
      }
    }"
    sepref_register mop_modest_calculate_successor :: "modest_mdp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) nres"
  
  
    lemma modest_calculate_successor_alt: "mop_modest_calculate_successor DS v t b = modest_mdp_def.modest_calculate_successor DS v t b"
      unfolding mop_modest_calculate_successor_def modest_mdp_def.modest_calculate_successor_def
        St_nth_uid_alt Tr_nth_alt
        by auto 

    definition mop_modest_is_admissible :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool nres" where
      "mop_modest_is_admissible = (\<lambda> (St,Tr,Br,Av,Ta) v.  RETURN True)"
    sepref_register mop_modest_is_admissible
  
  
    lemma mop_modest_is_admissible_alt: "mop_modest_is_admissible DS = modest_mdp_def.modest_admissible"
      unfolding mop_modest_is_admissible_def modest_mdp_def.modest_admissible_def
      by auto
  
    definition mop_modest_is_empty :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool nres" where 
    "mop_modest_is_empty = (\<lambda> (St,Tr,Br,Av,Ta) v. RETURN (op_set_member v Av \<or> op_set_member v Ta))"
    sepref_register mop_modest_is_empty :: "modest_mdp \<Rightarrow> nat \<Rightarrow> bool nres"
  
  
    lemma modest_is_empty_alt: "mop_modest_is_empty = modest_mdp_def.modest_is_empty"
      unfolding mop_modest_is_empty_def modest_mdp_def.modest_is_empty_def 
        modest_mdp_pre.Av_def modest_mdp_pre.Ta_def op_set_member_def by auto
  
    definition "mop_modest_index_begin = (\<lambda> DS v. do{
      let tl = St_nth_lid DS v;
      ASSERT(tl < length (modest_mdp_pre.Tr DS));
      let b = Tr_nth DS tl;                  
      (tn,bn) \<leftarrow> mop_modest_calculate_successor DS v tl b;
      RETURN (v,tl,tn,b,bn)
    })"
    sepref_register mop_modest_index_begin :: "modest_mdp \<Rightarrow> nat \<Rightarrow> (nat modest_succ_index) nres"
  
  
    lemma modest_index_begin_refine: "mop_modest_index_begin DS v = modest_mdp_def.modest_index_begin DS v"
      unfolding mop_modest_index_begin_def modest_mdp_def.modest_index_begin_def
        modest_calculate_successor_alt St_nth_lid_alt Tr_nth_alt
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
  
  
    lemma modest_succ_at_refine: "bc < length Br \<Longrightarrow> modest_mdp_invar N DS\<^sub>c (St,Tr,Br,Av,Ta) \<Longrightarrow> mop_modest_succ_at (St,Tr,Br,Av,Ta) (v,tc,te,bc,be) \<le> RETURN (modest_successor_index_def.modest_succ_at (St,Tr,Br,Av,Ta) (v,tc,te,bc,be))"
      unfolding mop_modest_succ_at_def modest_successor_index_def.modest_succ_at_def 
        modest_get_target_of_branch_alt modest_mdp_def.get_successor_of_branch_def
      apply(refine_vcg) 
      apply simp
      apply (simp add: modest_mdp_invar_def modest_mdp_invar_axioms_def modest_mdp_invar'_def
         modest_mdp_input_struc_invar_def) 
      apply (meson atLeastLessThan_iff in_set_conv_nth subsetD)
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
      shows "mop_modest_next_index DS (v,tc,te,bc,be) \<le> modest_successor_index_def.modest_next_index DS (v,tc,te,bc,be)"
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
      apply(frule modest_mdp_invar.DS_DEF[symmetric])
      unfolding modest_index_begin_refine
      apply(drule modest_mdp_invar.axioms(1))
      apply clarsimp
      apply(rule modest_index_begin_refine_aux[THEN order_trans])
      by (auto simp: in_br_conv modest_mdp_succ_DS_rel_def intro: modest_mdp_invar_axioms.intro modest_mdp_invar.intro)
  
  
    lemma modest_get_state_get_state_correct: "(mop_modest_get_state, mop_get_state) \<in> modest_succ_index_DS_rel N DS \<rightarrow> \<langle>node_rel' N\<rangle>nres_rel"
      apply(refine_vcg)
      by(auto intro!: modest_get_state_refine simp: mop_modest_get_state_refine)
  
  
    lemma modest_succ_at_correct: "((PR_CONST mop_modest_succ_at), mop_graph_succ_at) \<in> (modest_mdp_succ_DS_rel N DS\<^sub>c) \<rightarrow> (modest_succ_index_DS_rel N DS\<^sub>c) \<rightarrow> \<langle>node_rel' N\<rangle>nres_rel"
      apply (refine_vcg)
      apply(frule modest_mdp_succ_rel_DS_eq)
      apply clarsimp
      apply(rule modest_succ_at_refine[THEN order_trans])
      subgoal for St Tr Br Av Ta K v tc te bc be v' ti bi
        apply(clarsimp simp: modest_succ_index_DS_rel_def in_br_conv ) 
        apply(frule modest_successor_index_invar.beI_bound) 
        using modest_successor_index_invar.ibc_bound by force
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
    "
  
    (*TODO: Add cullable to name*)
    definition modest_mdp_assn_aux :: "modest_mdp \<Rightarrow> modest_mdpi \<Rightarrow> assn"
    where "modest_mdp_assn_aux = 
       node_array_slice_assn (Suc N) size_assn \<comment> \<open>List of states\<close>
    \<times>\<^sub>a small_array_slice_assn size_assn \<comment> \<open>List of transitions\<close>
    \<times>\<^sub>a small_array_slice_assn (node_assn' N) \<comment> \<open>List of Branches\<close>
    \<times>\<^sub>a (bitset_assn N)
    \<times>\<^sub>a (bitset_assn N)"
  
  
    lemma modest_mdp_assn_boundsD[sepref_bounds_dest]: 
      assumes "rdomp modest_mdp_assn_aux (St,Tr,Br,Av,Ta)"
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
  
  
    sepref_definition Tr_nth_ll is "uncurry (RETURN \<circ>\<circ> Tr_nth)" :: "[\<lambda> ((St,Tr,Br,Av,Ta), t). t < length Tr]\<^sub>a modest_mdp_assn_aux\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> size_assn"
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

    sepref_definition mop_modest_calculate_successor_ll is "uncurry3 (mop_modest_calculate_successor)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn \<times>\<^sub>a size_assn"
      unfolding mop_modest_calculate_successor_def PR_CONST_def
      supply[elim] = modest_mdp_assn_boundsD(1)[THEN less_trans[rotated]]
      apply sepref
      done
    concrete_definition (in -) mop_modest_calculate_successor_ll' [llvm_code] is modest_init_mdp_env.mop_modest_calculate_successor_ll_def
    lemmas mop_modest_calculate_successor_hnr[sepref_fr_rules] = mop_modest_calculate_successor_ll.refine[unfolded mop_modest_calculate_successor_ll'.refine[OF modest_init_mdp_env_axioms]]
  

    sepref_definition mop_modest_is_admissible_ll is "uncurry (mop_modest_is_admissible)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k\<rightarrow>\<^sub>a bool1_assn"
      unfolding mop_modest_is_admissible_def modest_mdp_assn_aux_def
      apply sepref
      done
  
    concrete_definition (in -) mop_modest_is_admissible_ll' [llvm_code] is modest_init_mdp_env.mop_modest_is_admissible_ll_def
    lemmas mop_modest_is_admissible_hnr[sepref_fr_rules] = mop_modest_is_admissible_ll.refine[unfolded mop_modest_is_admissible_ll'.refine[OF modest_init_mdp_env_axioms]]


    sepref_definition modest_is_empty_ll is "uncurry (PR_CONST mop_modest_is_empty)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k\<rightarrow>\<^sub>a bool1_assn"
      unfolding mop_modest_is_empty_def PR_CONST_def modest_mdp_assn_aux_def
      apply sepref
      done
    concrete_definition (in -) modest_is_empty_ll' [llvm_code] is modest_init_mdp_env.modest_is_empty_ll_def
    lemmas modest_is_empty_hnr[sepref_fr_rules] = modest_is_empty_ll.refine[unfolded modest_is_empty_ll'.refine[OF modest_init_mdp_env_axioms]]
  

    sepref_definition modest_index_begin_ll is "uncurry (PR_CONST mop_modest_index_begin)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a (node_assn' N)\<^sup>k \<rightarrow>\<^sub>a modest_index_assn_aux"
      unfolding mop_modest_index_begin_def modest_index_assn_aux_def PR_CONST_def
      modest_mdp_pre.St_def
      apply sepref_dbg_keep
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