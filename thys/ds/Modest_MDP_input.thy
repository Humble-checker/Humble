theory Modest_MDP_input
  imports "../ds/BitSet" "../II/II_Def" "II_Modest_Base.Nat_Interval"
begin

  hide_const (open) r measure MDP_Components.is_scc Omega_Words_Fun.prefix

  text \<open>
    This theory implements the operations for the Modest data structure for the MDP structure.

    The Modest data structure contains three lists respresenting States, Transitions and 
    Branches. The list of states is a tuple which respectively contains the number of transitions 
      and the starting index in the list of transitions.
    The list of transitions similarly is a tuple which contains respectively the number of branches 
      that the transition has as well as the starting index in the branch list.
    The list of branches contains a tuple (single value in this representation) with the index of 
      the successor state in the state list.\<close>

  section \<open>General Lemmas\<close>

  lemma nth_len_prefix: "xs = ys @ zs \<Longrightarrow> zs = z#zs' \<Longrightarrow> xs ! (length ys) = z"
    apply(induction ys)
    by auto

  lemma strict_prefix_upt1: "m \<le> n1 \<Longrightarrow> n1 < n2 \<Longrightarrow> strict_prefix [m..<n1] [m..<n2]"
    by (simp add: strict_prefixI' upt_eq_lel_conv)

  lemma prefix_upt: "n1 \<le> n2 \<Longrightarrow> prefix [m..<n1] [m..<n2]"
    unfolding prefix_def
    apply(induction n2)
    apply simp
    subgoal for n2
      apply(cases "n1=Suc n2") 
      apply auto
      done
    done

  lemma less_minus_Suc_zero: "i < j - Suc 0 \<longleftrightarrow> Suc i < j"
    by linarith

  lemma dom_ite_partial: "dom (\<lambda>x. if P x then Some (f x) else None) = Collect P"
    by(auto split: if_splits)

  lemma map_nth_zip: "set zs \<subseteq> {0..<min (length xs) (length ys)} \<Longrightarrow> map ((!) (zip xs ys)) zs = zip (map ((!) xs) zs) (map ((!) ys) zs)"
    apply(induction zs)
    by (auto intro!: nth_zip) 

  lemma filter_fst_zip: "set zs \<subseteq> {0..<min (length xs) (length ys)} \<Longrightarrow> filter (((\<lambda>w. P (fst w)) \<circ>\<circ> (!)) (zip xs ys)) zs = filter ((P \<circ>\<circ> (!)) xs) zs"
    apply(induction zs)
    by auto

  lemma filter_snd_zip:"set zs \<subseteq> {0..<min (length xs) (length ys)} \<Longrightarrow> filter (((\<lambda>w. P (snd w)) \<circ>\<circ> (!)) (zip xs ys)) zs = filter ((P \<circ>\<circ> (!)) ys) zs"
    apply(induction zs)
    by auto

  lemma fst_zip_nth: "i < min (length xs) (length ys) \<Longrightarrow> fst (zip xs ys ! i) = xs ! i"
    by auto

  lemma snd_zip_nth: "i < min (length xs) (length ys) \<Longrightarrow> snd (zip xs ys ! i) = ys ! i"
    by auto

  lemma map_fst_zip: "set zs \<subseteq> {0..<min (length xs) (length ys)} \<Longrightarrow> map ((fst \<circ>\<circ> (!)) (zip xs ys)) zs = map ((!) xs) zs"
    apply(induction zs)
    by auto

  lemma map_snd_zip: "set zs \<subseteq> {0..<min (length xs) (length ys)} \<Longrightarrow> map ((snd \<circ>\<circ> (!)) (zip xs ys)) zs = map ((!) ys) zs"
    apply(induction zs)
    by auto

  section \<open>Modest MEC Input Data Structure\<close>

  text \<open>
    We distinguish two different notions of the Modest data structure. The first one is the input
    data structure. This is the data as it is passed on from the Modest Toolset without any
    additional data. Apart from the number of states \<open>N\<close>, there is the list of states \<open>St\<close>
    which defines an interval encoded as a tuple (see SharedNat.thy) onto the list of transitions 
    \<open>Tr\<close>. That list is a list of intervals onto the list of Branches \<open>Br\<close> which is a list of 
    states, i.e. indices onto \<open>St\<close>.
    Depending on the property that we want to check, we have a set of avoid \<open>Av\<close> and target \<open>Ta\<close> 
    states. These states are considered to have no outgoing transitions for the purpose of this 
    algorithms as these states must be part of their own MEC.
  \<close>

  type_synonym modest_input_struc_mdp = "nat list \<times> nat list \<times> nat list \<times> nat set \<times> nat set"

  subsection \<open>Invariant\<close>

  locale modest_mdp_input_struc_def =
    fixes N::nat
    and St :: "nat list"
    fixes Tr :: "nat list"
    fixes Br :: "nat list"
    fixes Av :: "nat set"
    fixes Ta :: "nat set"
  begin 

    definition "Cm = {0..<N} - Av - Ta" \<comment> \<open>Computation states, i.e. states that are not avoid or target states.\<close>

    abbreviation "StI \<equiv> sorted_intvs St"

    abbreviation "TrI \<equiv> sorted_intvs Tr"

    definition "succs u = (if u \<in> Cm then (\<lambda> t. (!) Br ` (sn_intv (TrI ! t))) ` (sn_intv (StI ! u)) else {{u}} )"


    definition "K\<^sub>0_\<alpha> = (\<lambda> u. if u < N then (if u \<in> Cm then {(!) Br ` sn_intv (TrI ! x) | x. in_intv (StI ! u) x} else {{u}}) else {})"

    definition "S\<^sub>0_\<alpha> = {v. v < N}" 

    definition "SK\<^sub>0_\<alpha> = (S\<^sub>0_\<alpha>,K\<^sub>0_\<alpha>)"

    lemma finite_Cm[simp,intro!]: "finite Cm"
      unfolding Cm_def by blast

    lemma Cm_mem: "u \<in> Cm \<longleftrightarrow> u < N \<and> u \<notin> Av \<and> u \<notin> Ta"
      unfolding Cm_def by simp

    lemma Av_Cm: "u \<in> Av \<Longrightarrow> u \<notin> Cm"
      unfolding Cm_def by blast

    lemma Ta_Cm: "u \<in> Ta \<Longrightarrow> u \<notin> Cm"
      unfolding Cm_def by blast

    lemma succs_ua: "u \<in> Av \<Longrightarrow> succs u = {{u}}"
      unfolding succs_def by (auto simp: Cm_mem)

    lemma succs_ut: "u \<in> Ta \<Longrightarrow> succs u = {{u}}"
      unfolding succs_def by (auto simp: Cm_mem)

    lemma "u \<in> Cm \<Longrightarrow> in_intv (StI ! u) t \<Longrightarrow> in_intv (TrI ! t) b \<Longrightarrow> Br ! b \<in> \<Union>(succs u)"
      unfolding succs_def by fastforce

    lemma succs_mem: "u \<in> Cm \<Longrightarrow> v \<in> \<Union>(succs u) \<longleftrightarrow> (\<exists> t b. in_intv (StI ! u) t \<and> in_intv (TrI ! t) b \<and> v = Br ! b)"
      unfolding succs_def by force

    lemma N_cases: "u < N \<Longrightarrow> (u \<in> Cm \<Longrightarrow> P) \<Longrightarrow> (u \<in> Av \<Longrightarrow> P) \<Longrightarrow> (u \<in> Ta \<Longrightarrow> P) \<Longrightarrow> P"
      unfolding Cm_mem by satx

  end

  locale modest_mdp_input_struc_invar = modest_mdp_input_struc_def N St Tr Br Av Ta for N St Tr Br Av Ta +
  
    assumes N_DEF: "N = length St - Suc 0"
    assumes N0: "N > 0"

    assumes AN: "Av \<subseteq> {0..<N}"
    assumes TN: "Ta \<subseteq> {0..<N}"
    assumes AT: "Av \<inter> Ta = {}"

    assumes St_dom: "set St \<subseteq> {0..<length Tr}"
    assumes Tr_dom: "set Tr \<subseteq> {0..length Br}"
    assumes Br_dom: "set Br \<subseteq> {0..<N}"

    assumes Sorted_St: "sorted_wrt (<) St"
    assumes Sorted_Tr: "sorted_wrt (<) Tr"

  begin

    lemma AvN: "u \<in> Av \<Longrightarrow> u < N"
      using AN by fastforce

    lemma TaN: "u \<in> Ta \<Longrightarrow> u < N"
      using TN by fastforce

    lemma finite_Av[simp,intro!]: "finite Av"
      using AN finite_subset by blast

    lemma finite_Ta[simp,intro!]: "finite Ta"
      using TN finite_subset by blast

    lemma sorted_St: "sorted St" and distinct_St: "distinct St"
      using Sorted_St 
      by (auto simp add: strict_sorted_iff)

    lemma sorted_Tr: "sorted Tr" and distinct_Tr: "distinct Tr"
      using Sorted_Tr
      by (auto simp add: strict_sorted_iff)


    lemma St_in_bound: "i < N \<Longrightarrow> uid (StI!i) < length Tr"
      using uid_sorted_intvs[OF sorted_St, of i] St_dom 
      by(fastforce simp: N_DEF less_minus_Suc_zero dest: nth_mem) 

    lemma Tr_in_bound: "i < length Tr - Suc 0 \<Longrightarrow> uid (TrI!i) \<le> length Br"
      using uid_sorted_intvs[OF sorted_Tr, of i] Tr_dom 
      by(fastforce simp: less_minus_Suc_zero dest: nth_mem)

    lemma Br_in_bound: "i < length Br \<Longrightarrow> Br!i < N"
      using Br_dom by(fastforce dest: nth_mem)

    lemma St_nonempty: "i < N \<Longrightarrow> cnt (StI!i) > 0"
      by(auto simp: N_DEF Sorted_St intro!: strict_sorted_intvs_cnt_gt_0)

    lemma Tr_nonempty: "i < length Tr - Suc 0 \<Longrightarrow> cnt (TrI!i) > 0"
      by(auto simp: Sorted_Tr intro!: strict_sorted_intvs_cnt_gt_0)

    lemma St_intv_disj: "i < j \<Longrightarrow> j < N \<Longrightarrow> sn_intv (StI ! i) \<inter> sn_intv (StI ! j) = {}"
      apply(rule sorted_intvs_disj) by (auto simp: N_DEF sorted_St)

    lemma Tr_intv_disj: "i < j \<Longrightarrow> j < length Tr - Suc 0 \<Longrightarrow> sn_intv (TrI ! i) \<inter> sn_intv (TrI ! j) = {}"
      apply(rule sorted_intvs_disj) by (auto simp: sorted_Tr)

    lemma Tr_in_boundD: "u < N \<Longrightarrow> t < uid (StI ! u) \<Longrightarrow> t < length Tr - Suc 0" 
      by (force dest: St_in_bound)

    lemma Tr_in_boundD': "u < N \<Longrightarrow> t < uid (StI ! u) \<Longrightarrow> t \<le> length Tr"
      using Tr_in_boundD 
      by force

    lemma Br_in_boundD: "t < length Tr - Suc 0 \<Longrightarrow> b < uid (TrI ! t) \<Longrightarrow> b < length Br"
      apply(drule Tr_in_bound)
      by force

    lemma Tr_in_bound_intvD: "u < N \<Longrightarrow> in_intv (StI ! u) t \<Longrightarrow> t < length Tr - Suc 0"
      by(auto elim!: Tr_in_boundD dest: in_intv_ubD)

    lemma Tr_in_bound_intvD': "u < N \<Longrightarrow> in_intv (StI ! u) t \<Longrightarrow> t \<le> length Tr"
      by(auto dest: Tr_in_bound_intvD)

    lemma Br_in_bound_intvD: "t < length Tr - Suc 0 \<Longrightarrow> in_intv (TrI ! t) b \<Longrightarrow> b < length Br"
      by(auto elim!: Br_in_boundD dest: in_intv_ubD)

    lemma succs_in_Br: "u \<in> Cm \<Longrightarrow> \<Union> (succs u) \<subseteq> set Br"
      unfolding succs_def by (auto simp: Cm_mem intro!: nth_mem Br_in_boundD Tr_in_bound_intvD)

    lemma succs_on_St: "u < N \<Longrightarrow> \<Union> (succs u) \<subseteq> {0..<N}"
      using succs_in_Br Br_dom succs_ua succs_def by auto


  end


  type_synonym modest_input_mdp = "nat list \<times> nat list \<times> nat list \<times> real list \<times> nat set \<times> nat set"

  locale modest_mdp_input_def = modest_mdp_input_struc_def N St Tr Br Av Ta for N St Tr Br Av Ta + 
    fixes Pr :: "real list"
  begin 

    abbreviation "pmf_list t \<equiv> map ((!) (zip Br Pr)) (ls_intv (TrI ! t))"

    definition "Tr_to_pmf t = pmf_of_list (pmf_list t)"

    definition "St_to_pmfs u = (if u \<in> Cm then {Tr_to_pmf t | t. in_intv (StI ! u) t} else {return_pmf u})"

    definition M\<^sub>0_\<alpha> :: "nat mdpc" where "M\<^sub>0_\<alpha> = Abs_mdpc (\<lambda> u. if u < N then Some (St_to_pmfs u) else None)"  

    definition "\<M>_\<alpha> = Abs_mdptc (M\<^sub>0_\<alpha>, Av, Ta)"

    definition "N_len xs \<longleftrightarrow> N = length xs" \<comment> \<open>To stop automatic rewriting\<close>

    lemma \<M>_\<alpha>_simps[simp]: "to_mdpc \<M>_\<alpha> = M\<^sub>0_\<alpha>" "avoids \<M>_\<alpha> = Av" "targets \<M>_\<alpha> = Ta"
      unfolding \<M>_\<alpha>_def
      by (transfer; simp)+

    lemma St_to_pmfs_ua: "u \<in> Av \<Longrightarrow> St_to_pmfs u = {return_pmf u}"
      unfolding St_to_pmfs_def Cm_def by auto

    lemma St_to_pmfs_ut: "u \<in> Ta \<Longrightarrow> St_to_pmfs u = {return_pmf u}"
      unfolding St_to_pmfs_def Cm_def by auto

    lemma St_to_pmfs_nta: "u \<in> Cm \<Longrightarrow> St_to_pmfs u = Tr_to_pmf ` sn_intv (StI ! u)"
      unfolding St_to_pmfs_def by auto

    lemma St_to_pmfs_alt: "St_to_pmfs u = (if u \<in> Cm then Tr_to_pmf ` sn_intv (StI ! u) else {return_pmf u})"
      unfolding St_to_pmfs_def by auto


  end

  locale modest_mdp_input_invar = modest_mdp_input_struc_invar N St Tr Br Av Ta + modest_mdp_input_def N St Tr Br Av Ta Pr for N St Tr Br Pr Av Ta +

    assumes Pr_lt_one: "t < length Tr - Suc 0 \<Longrightarrow> sum_list (map ((!) Pr) [Tr ! t ..< Tr ! Suc t]) = 1"
    assumes Pr_gt_zero: "p \<in> set Pr \<Longrightarrow> p > 0"
    assumes Len_Pr_Br[simp]: "length Pr = length Br"

  begin

    lemma Pr_nth_gt_0: "b < length Br \<Longrightarrow> 0 < Pr ! b"
      by (simp add: Pr_gt_zero)

    lemma Pr_nth_ge_0: "b < length Br \<Longrightarrow> 0 \<le> Pr ! b"
      by (auto dest: Pr_nth_gt_0)

    lemma Pr_lt_one': "t < length Tr - Suc 0 \<Longrightarrow> sum_list (map ((!) Pr) (ls_intv (TrI ! t))) = 1"
      using ls_intv_sorted_intvs[OF sorted_Tr] Pr_lt_one
      by presburger

    lemma N_card: "N = card (states M\<^sub>0_\<alpha>)"
      apply (simp add: N_DEF modest_mdp_input_def.M\<^sub>0_\<alpha>_def)
      apply transfer
      by (auto simp: dom_ite_partial states.abs_eq split:if_splits)

    lemma St_to_pmfs_ne: "u < N \<Longrightarrow> St_to_pmfs u \<noteq> {}"
      unfolding St_to_pmfs_def by (auto simp: N_DEF intro!: ex_in_intv St_nonempty) 

    lemma finite_St_to_pmfs[simp]: "finite (St_to_pmfs s)"
      unfolding St_to_pmfs_def using in_intv_set by auto

    lemma states_M\<^sub>0_\<alpha>: "states M\<^sub>0_\<alpha> = {0..<N}"
      using AN TN unfolding M\<^sub>0_\<alpha>_def
      by (auto simp: states.abs_eq split: if_splits) 

    lemma actions_M\<^sub>0_\<alpha>: "u < N \<Longrightarrow> actions M\<^sub>0_\<alpha> u = St_to_pmfs u"
      unfolding M\<^sub>0_\<alpha>_def
      by (auto simp: actions.abs_eq)


    lemma ne_actions_M\<^sub>0_\<alpha>: "actions M\<^sub>0_\<alpha> u \<noteq> {} \<Longrightarrow> u < N"
      using AN TN unfolding M\<^sub>0_\<alpha>_def by (auto simp: actions.abs_eq)

    lemma ne_actions_M\<^sub>0_\<alpha>': "d \<in> actions M\<^sub>0_\<alpha> u \<Longrightarrow> u < N"
      using ne_actions_M\<^sub>0_\<alpha> by blast

    lemma map_fst_pmf_list: "t < length Tr - Suc 0 \<Longrightarrow> map fst (pmf_list t) = map ((!) Br) (ls_intv (TrI ! t))"
      apply clarsimp 
      apply(subst fst_zip_nth) 
      by (auto intro!: Br_in_bound_intvD )

    lemma map_snd_pmf_list: "t < length Tr - Suc 0 \<Longrightarrow> map snd (pmf_list t) = map ((!) Pr) (ls_intv (TrI ! t))"
      apply clarsimp 
      apply(subst snd_zip_nth) 
      by (auto intro!: Br_in_bound_intvD )


    lemma pmf_list_wf: "t < length Tr - Suc 0 \<Longrightarrow> pmf_of_list_wf (pmf_list t)"
      apply(rule pmf_of_list_wfI)
      subgoal for i
        apply clarsimp
        apply(subst snd_zip_nth) 
        by (auto intro!: Br_in_bound_intvD Pr_nth_ge_0) 
      subgoal
        unfolding map_snd_pmf_list
        using Pr_lt_one' .
      done

    lemma pmf_list_alt: "t < length Tr - Suc 0 \<Longrightarrow> pmf_list t = zip (map ((!) Br) (ls_intv (TrI ! t))) (map ((!) Pr) (ls_intv (TrI ! t)))"
      by(subst map_nth_zip; auto simp: Br_in_bound_intvD)

    lemma map_filter_pmf_list: "t < length Tr - Suc 0 \<Longrightarrow> map snd (filter (\<lambda>w. fst w = v) (pmf_list t)) = map ((!) Pr) (filter (\<lambda> b. v = Br ! b) (ls_intv (TrI ! t)))"
      apply(clarsimp simp: filter_map )
      apply(subst filter_fst_zip) apply (clarsimp simp: Br_in_bound_intvD)[]
      apply(subst map_snd_zip) apply (clarsimp simp: Br_in_bound_intvD)[]
      by (metis comp_apply)

    lemma pmf_Tr_to_pmf: "t < length Tr - Suc 0 \<Longrightarrow> pmf (Tr_to_pmf t) v = sum_list (map ((!) Pr) (filter (\<lambda>b. v = Br ! b) (ls_intv (TrI ! t))))"
      by(clarsimp simp: pmf_list_wf[THEN pmf_pmf_of_list, folded Tr_to_pmf_def] map_filter_pmf_list)
    
    lemma pmf_Tr_to_pmf_set: "t < length Tr - Suc 0 \<Longrightarrow> pmf (Tr_to_pmf t) v = (\<Sum> b \<in> {b \<in> sn_intv (TrI ! t). v = Br ! b}. Pr ! b)"
      by(auto simp:  pmf_Tr_to_pmf sum_list_distinct_conv_sum_set)

    lemma set_pmf_Tr_to_pmf: "t < length Tr - Suc 0 \<Longrightarrow> set_pmf (Tr_to_pmf t) = (!) Br ` sn_intv (TrI ! t)"
      apply(frule set_pmf_of_list_eq[OF pmf_list_wf]) 
      using Br_in_bound_intvD Pr_gt_zero apply force
      using Tr_to_pmf_def map_fst_pmf_list by (auto intro!: image_eqI)[1]

    lemma set_pmf_in_succs: "u < N \<Longrightarrow> p \<in> St_to_pmfs u \<Longrightarrow> set_pmf p \<in> succs u"
      unfolding St_to_pmfs_def succs_def  
      by (auto simp: N_DEF Tr_in_bound_intvD set_pmf_Tr_to_pmf)

    lemma succs_alt: "u < N \<Longrightarrow> succs u = set_pmf ` (St_to_pmfs u)"
      unfolding St_to_pmfs_def succs_def   
      by (auto simp: N_DEF Tr_in_bound_intvD setcompr_eq_image simp flip: set_pmf_Tr_to_pmf) 

    lemma en_Abs_mdpc: "en (Abs_mdpc f) = {(a,b). \<exists>d e. f a = Some e \<and> d \<in> e \<and> b \<in> set_pmf d}"
      unfolding en_def by (force simp: actions.abs_eq split: option.splits)

    lemma en_M\<^sub>0_\<alpha>_def: "u < N \<Longrightarrow> en M\<^sub>0_\<alpha> `` {u} = \<Union> (succs u)"
      unfolding M\<^sub>0_\<alpha>_def using AT by (auto simp: succs_alt en_Abs_mdpc succs_ut St_to_pmfs_ut)

    lemma en_M\<^sub>0_\<alpha>_sub: "en M\<^sub>0_\<alpha> \<subseteq> {0..<N} \<times> {0..<N}"
    proof safe
      fix u v
      assume "(u, v) \<in> en M\<^sub>0_\<alpha>"
      thus "u \<in> {0..<N}"
        unfolding en_def by (auto simp: ne_actions_M\<^sub>0_\<alpha>' )
    next
      fix u v
      assume A: "(u, v) \<in> en M\<^sub>0_\<alpha>"
      hence UN: "u < N" unfolding en_def by (auto simp: ne_actions_M\<^sub>0_\<alpha>' )
      with A have "v \<in> \<Union> (succs u)" using en_M\<^sub>0_\<alpha>_def 
        by blast
      thus "v \<in> {0..<N}"
        using UN succs_on_St by blast
    qed

    lemma closed_mdpc_M\<^sub>0_\<alpha>: "closed_mdpc M\<^sub>0_\<alpha>" 
      unfolding closed_mdpc_def using en_M\<^sub>0_\<alpha>_sub by (auto simp: states_M\<^sub>0_\<alpha> )

    lemma Finite_MDP_M\<^sub>0_\<alpha>: "Finite_MDP M\<^sub>0_\<alpha>"
      apply(unfold_locales)
      subgoal using closed_mdpc_M\<^sub>0_\<alpha> .
      subgoal using N0 N_card by force
      subgoal by (simp add: actions_M\<^sub>0_\<alpha> states_M\<^sub>0_\<alpha> St_to_pmfs_ne)
      subgoal unfolding states_M\<^sub>0_\<alpha> by blast
      subgoal for u
        by (metis actions_M\<^sub>0_\<alpha> finite.intros(1) finite_St_to_pmfs ne_actions_M\<^sub>0_\<alpha>)
      done

  end


  
  locale modest_init_mdp_env_defs = 
    fixes N::nat \<comment> \<open>For the implementation of this data structure, we assume that there is a value \<open>N\<close> which represents the number of states\<close>
  begin

    abbreviation "node_rel \<equiv> node_rel' N"
    abbreviation "node_assn \<equiv> node_assn' N"

  end

  locale modest_init_mdp_env = modest_init_mdp_env_defs N for N and ni +
    assumes n_impl: "(ni, N) \<in> size_rel"
    assumes N_BOUND: "2*N < max_size_t"

  definition "modest_mdp_input_rel N = br (\<lambda> (St, Tr, Br, Pr, Av, Ta). modest_mdp_input_def.M\<^sub>0_\<alpha> N St Tr Br Av Ta Pr) (\<lambda> (St, Tr, Br, Pr, Av, Ta). modest_mdp_input_invar N St Tr Br Pr Av Ta)"

  definition "modest_mdp_input_DS_rel N DS = br (\<lambda> (St, Tr, Br, Pr, Av, Ta). modest_mdp_input_def.M\<^sub>0_\<alpha> N St Tr Br Av Ta Pr) (\<lambda> (St, Tr, Br, Pr, Av, Ta). modest_mdp_input_invar N St Tr Br Pr Av Ta \<and> DS = (St, Tr, Br, Pr, Av, Ta))"

  lemma modest_mdp_input_DS_rel_props: "(DS,M) \<in> modest_mdp_input_DS_rel N DS \<Longrightarrow> states M = {0..<N} \<and> Finite_MDP M"
    unfolding modest_mdp_input_DS_rel_def
    by(auto simp: in_br_conv modest_mdp_input_invar.states_M\<^sub>0_\<alpha> modest_mdp_input_invar.Finite_MDP_M\<^sub>0_\<alpha>)


  definition "modest_mdp_input_struc_rel N = br (\<lambda> (St, Tr, Br, Av, Ta). modest_mdp_input_struc_def.SK\<^sub>0_\<alpha> N St Tr Br Av Ta) (\<lambda> (St, Tr, Br, Av, Ta). modest_mdp_input_struc_invar N St Tr Br Av Ta)"

  definition "modest_mdp_input_struc_DS_rel N DS = br (\<lambda> (St, Tr, Br, Av, Ta). modest_mdp_input_struc_def.SK\<^sub>0_\<alpha> N St Tr Br Av Ta) (\<lambda> (St, Tr, Br, Av, Ta). modest_mdp_input_struc_invar N St Tr Br Av Ta \<and> DS = (St, Tr, Br, Av, Ta))"

  subsection \<open>LLVM Data Structures\<close>

  abbreviation "node_array_slice_assn N' A \<equiv> b_assn (IICF_Array.array_slice_assn A) (\<lambda>xs. length xs = N')"

  type_synonym modest_input_mdpi = "
    size_t ptr 
  \<times> size_t ptr
  \<times> size_t ptr
  \<times> (double \<times> double) ptr
  \<times> bitseti
  \<times> bitseti
  "

  subsubsection \<open>Modest graph\<close>

  context modest_init_mdp_env_defs
  begin
  
    definition Modest_mdp_assn_aux :: "modest_input_mdp \<Rightarrow> modest_input_mdpi \<Rightarrow> assn"
    where "Modest_mdp_assn_aux = 
       node_array_slice_assn (Suc N) size_assn 
    \<times>\<^sub>a small_array_slice_assn size_assn 
    \<times>\<^sub>a small_array_slice_assn node_assn 
    \<times>\<^sub>a small_array_slice_assn pfin_real_intv_assn 
    \<times>\<^sub>a bitset_assn N 
    \<times>\<^sub>a bitset_assn N
    "

    definition "Modest_MDP_assn = hr_comp Modest_mdp_assn_aux (modest_mdp_input_rel N)"

    definition "Modest_MDP_DS_assn DS = hr_comp Modest_mdp_assn_aux (modest_mdp_input_DS_rel N DS)"


  end

end
