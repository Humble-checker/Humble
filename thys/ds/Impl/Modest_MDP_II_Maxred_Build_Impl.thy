theory Modest_MDP_II_Maxred_Build_Impl
  imports "Modest_MDP_II_Maxred_Impl" "../Intf/Modest_MDP_II_Maxred_Build"
begin


text \<open>LLVM code refinement for the state-space building step of the max-reduction pipeline. The
  abstract builder and its five passes live in \<open>Modest_MDP_II_Maxred_Build\<close>; here each pass is refined
  in the \<open>nres\<close> monad and synthesised with \<open>sepref\<close>. The collapsed state space is built decentrally
  (one op per pass), all sized by the MEC count \<open>M = length D\<close> (see the environment below).\<close>


section \<open>The collapse-builder environment: the MEC-count size parameter \<open>M\<close>\<close>

text \<open>All the collapsed-MDP data (the per-MEC count arrays, the target/avoid/output-avoid bitsets, the
  CSR offset arrays) is indexed by MEC, so its size is \<open>length D\<close>, and a \<^const>\<open>bitset_assn\<close> needs that
  length \<^emph>\<open>in its assertion\<close>. As on the min/SCC side, where \<open>N\<close> (the number of states,
  \<^locale>\<open>disj_set_list_tuple_defs\<close>'s \<open>N\<close>/\<open>L\<^sub>1\<close>) is fixed as a locale parameter that is BOTH a value in
  the algorithm and the size of a bounded assertion, we fix the MEC count \<open>M\<close> the same way: a logical
  parameter with a concrete \<open>Mi\<close> and refinement \<open>M_impl\<close>, so \<^const>\<open>bitset_assn\<close>\<open> M\<close> and \<open>M\<close>-sized
  arrays can be instantiated over it. \<open>M\<close> is the number of MECs; the refinement lemmas assume
  \<open>M = length D\<close> (discharged when the builder is applied to a concrete decomposition, exactly as \<open>N\<close>
  is discharged against the concrete state count). We extend \<^locale>\<open>interval_iteration_env\<close> for \<open>N\<close>
  and the structural accessors, and interpret the MEC-map environment for
  \<open>op_in_eq_mec\<close>/\<open>op_mec_index_of\<close>.\<close>

locale collapse_build_env = interval_iteration_env +
  fixes M :: nat and Mi
  assumes M_impl: "(Mi, M) \<in> b_rel size_rel (\<lambda>i. Suc i < max_size_t)"
begin

  lemmas [sepref_import_param] = M_impl
  sepref_register M

  lemma M_Suc_upper: "Suc M < max_size_t"
    using M_impl by (auto simp: b_rel_def in_br_conv)

  lemma M_upper: "M < max_size_t"
    using M_Suc_upper by simp

  lemma M_incr_max[sepref_bounds_dest]: "x < M \<Longrightarrow> x + 1 < max_size_t"
    using M_upper by simp

  lemma M_incr_max_Suc[sepref_bounds_dest]: "x < M \<Longrightarrow> Suc x < max_size_t"
    using M_upper by simp

  lemma M_Suc_max: "M + 1 < max_size_t"
    using M_Suc_upper by simp

  \<comment> \<open>The CSR offset arrays are \<open>M + 1\<close> long, so their cursors range over \<^term>\<open>{0..<M+1}\<close>; the
    increment is still in range, since \<open>M_impl\<close> bounds \<^term>\<open>Suc M\<close>.\<close>
  lemma M1_incr_max[sepref_bounds_dest]: "x < M + 1 \<Longrightarrow> x + 1 < max_size_t"
    using M_Suc_max by simp

  lemma M1_incr_max_Suc[sepref_bounds_dest]: "x < Suc M \<Longrightarrow> Suc x < max_size_t"
    using M_Suc_max by simp

  text \<open>Bring the MEC-map operations (\<open>op_in_eq_mec\<close>, \<open>op_mec_index_of\<close>) into scope, as the min side
    does for \<open>is_trivial_impl\<close>.\<close>
  interpretation disj_set_list_tuple_env N N ni ni
    apply unfold_locales using n_impl by auto

  text \<open>Needed whenever a locale-local LLVM constant is replaced by its extracted global
    counterpart (\<open>..._ll'.refine\<close> has the locale predicate as its premise).\<close>
  lemma collapse_build_env_loc: "collapse_build_env N \<epsilon> ni \<epsilon>i M Mi"
    by unfold_locales

  lemma mec_map_eq_set_mem_preI:
    "i<length D \<Longrightarrow> Br ! b \<in> D ! i \<Longrightarrow> mec_map_eq_mec_mem_pre D (Br_nth (St,Tr,Br,Pr,Av,Ta) b)"
    "i<length D \<Longrightarrow> u \<in> D ! i \<Longrightarrow> mec_map_eq_mec_mem_pre D u"
    unfolding mec_map_eq_mec_mem_pre_def Br_nth_def b_assn_open_block_fun_def by auto


  subsection \<open>Pass 2: empty-EC --- the output avoid set, a bitset over \<open>M\<close>\<close>

  text \<open>Body of the sweep, shared by the \<^const>\<open>WHILET\<close> definition (for \<open>sepref\<close>) and the \<^const>\<open>nfoldli\<close>
    characterization (for the refinement to \<open>modest_collapse_invar.empty_ec_pass\<close>).\<close>
  definition empty_ec_body :: "nat list \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set nres" where
    "empty_ec_body cntT Ta' avm c Av' = do {
        ASSERT (c < M);
        ASSERT (c < length cntT);
        RETURN (if \<not>(c \<in> Ta') \<and> (c \<in> avm \<or> cntT ! c = 0) then insert c Av' else Av')
     }"

  text \<open>\<open>sepref\<close> cannot translate \<^const>\<open>nfoldli\<close>, so the implementation is a \<^const>\<open>WHILET\<close> counter
    loop (exactly the \<open>nfoldli_upt_by_while\<close> normal form); the refinement converts it back to
    \<^const>\<open>nfoldli\<close> to relate it to the abstract \<^const>\<open>FOREACH\<close>-based pass.\<close>
  definition empty_ec_impl :: "nat list \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat set nres" where
    "empty_ec_impl cntT Ta' avm Av0 = do {
       (_, Av') \<leftarrow> WHILET (\<lambda>(i, Av'). i < M \<and> True) (\<lambda>(i, Av'). do {
           Av' \<leftarrow> empty_ec_body cntT Ta' avm i Av';
           ASSERT (i < M);
           RETURN (i + 1, Av')
       }) (0, Av0);
       RETURN Av'
    }"

  lemma empty_ec_impl_nfoldli:
    "empty_ec_impl cntT Ta' avm Av0
       = nfoldli [0..<M] (\<lambda>_. True) (empty_ec_body cntT Ta' avm) Av0"
    unfolding empty_ec_impl_def by (rule nfoldli_upt_by_while[symmetric])

  text \<open>\<open>empty_ec_impl\<close> refines the abstract pass 2 (with \<open>M = length D\<close>): convert the \<^const>\<open>WHILET\<close> to
    \<^const>\<open>nfoldli\<close>, refine over the bounded element relation \<open>br id (\<lambda>x. x < M)\<close> (carries \<open>x < M\<close>,
    discharging the \<open>empty_ec_body\<close> \<open>ASSERT\<close>ions), then \<open>LFO_refine\<close> to the abstract \<^const>\<open>FOREACH\<close>.
    The abstract constant's defining equation is guarded by the locale predicate, so we assume it.\<close>
  lemma empty_ec_impl_refine:
    assumes MD: "M = length D" and LEN: "length cntT = M"
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    shows "empty_ec_impl cntT Ta' avm {} \<le> modest_collapse_invar.empty_ec_pass D cntT Ta' avm"
  proof -
    let ?body = "\<lambda>c Av'. if c \<notin> Ta' \<and> (c \<in> avm \<or> cntT ! c = 0)
                          then RETURN (insert c Av') else RETURN Av'"
    have step1: "nfoldli [0..<M] (\<lambda>_. True) (empty_ec_body cntT Ta' avm) {}
        \<le> \<Down>Id (nfoldli [0..<M] (\<lambda>_. True) ?body {})"
      apply (rule nfoldli_refine[where S="br id (\<lambda>x. x < M)" and R=Id])
      subgoal by (auto simp: list_rel_def in_br_conv list_all2_conv_all_nth)
      subgoal by simp
      subgoal by simp
      subgoal for xi x si s
        using LEN M_upper by (auto simp: empty_ec_body_def in_br_conv pw_le_iff refine_pw_simps)
      done
    have step2: "nfoldli [0..<M] (\<lambda>_. True) ?body {} \<le> \<Down>Id (FOREACH {0..<M} ?body {})"
      apply (rule LFO_refine[where A=Id])
      subgoal by (rule upt_list_set_rel)
      subgoal by simp
      subgoal by simp
      done
    from step1 have s1: "nfoldli [0..<M] (\<lambda>_. True) (empty_ec_body cntT Ta' avm) {}
        \<le> nfoldli [0..<M] (\<lambda>_. True) ?body {}" by simp
    from step2 have s2: "nfoldli [0..<M] (\<lambda>_. True) ?body {} \<le> FOREACH {0..<M} ?body {}" by simp
    from s1 s2 have R: "nfoldli [0..<M] (\<lambda>_. True) (empty_ec_body cntT Ta' avm) {}
        \<le> FOREACH {0..<M} ?body {}" by (rule order_trans)
    have EP: "modest_collapse_invar.empty_ec_pass D cntT Ta' avm = FOREACH {0..<M} ?body {}"
      unfolding modest_collapse_invar.empty_ec_pass_def[OF LOC] MD[symmetric] by (rule refl)
    show ?thesis unfolding empty_ec_impl_nfoldli EP by (rule R)
  qed

  sepref_definition empty_ec_ll is "uncurry3 (PR_CONST empty_ec_impl)"
    :: "(IICF_Array.array_assn size_assn)\<^sup>k *\<^sub>a (bitset_own_assn M)\<^sup>k *\<^sub>a (bitset_own_assn M)\<^sup>k
        *\<^sub>a (bitset_own_assn M)\<^sup>d \<rightarrow>\<^sub>a bitset_own_assn M"
    unfolding PR_CONST_def empty_ec_impl_def empty_ec_body_def conj.comm_neutral
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done


  subsection \<open>Pass 1: count --- per-MEC leaving-transition / branch counts + target/avoid MEC sets\<close>

  text \<open>\<open>trans_leaves\<close> as a branch loop, phrased via the state \<open>u\<close> (with \<open>c = op_mec_index_of D u\<close>):
    does some branch of transition \<open>t\<close> target a different MEC than \<open>u\<close>'s? Exactly the inner loop of
    the min-side \<open>is_trivial_impl\<close> (uses \<open>op_in_eq_mec\<close>, which sepref translates directly).\<close>
  definition trans_leaves_impl :: "modest_mdp \<Rightarrow> mec_map \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
    "trans_leaves_impl MDP D u t = do {
       ASSERT (t < length (tTr MDP) - Suc 0);
       (_, flag) \<leftarrow> WHILET (\<lambda>(b, flag). b < Tr_nth MDP (Suc t) \<and> \<not>flag) (\<lambda>(b, flag). do {
          ASSERT (b < length (tBr MDP) \<and> (\<exists>i<length D. u \<in> D ! i) \<and> (\<exists>i<length D. Br_nth MDP b \<in> D ! i));
          RETURN (Suc b, \<not> op_in_eq_mec D u (Br_nth MDP b))
       }) (Tr_nth MDP t, False);
       RETURN flag
    }"

  sepref_definition trans_leaves_ll is "uncurry3 trans_leaves_impl"
    :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a mec_map_assn\<^sup>k *\<^sub>a node_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding trans_leaves_impl_def
    supply [elim] = less_trans_Suc[OF _ Modest_mdp_assn_boundsD(2), rotated]
      less_trans_Suc[OF _ Modest_mdp_assn_boundsD(1), rotated] mec_map_eq_set_mem_preI
    apply sepref
    done

end

concrete_definition (in -) trans_leaves_ll' [llvm_code] is
  collapse_build_env.trans_leaves_ll_def

context collapse_build_env
begin

  interpretation disj_set_list_tuple_env N N ni ni
    apply unfold_locales using n_impl by auto

  \<comment> \<open>Register the inner \<open>trans_leaves\<close> loop as a sepref op so the outer \<open>count_pass_ll\<close> uses it as one
    pre-translated call (avoids re-translating the nested branch loop per transition).\<close>
  sepref_register trans_leaves_impl
  lemmas trans_leaves_hnr[sepref_fr_rules] =
    trans_leaves_ll.refine[unfolded trans_leaves_ll'.refine[OF collapse_build_env_loc]]

  text \<open>The inner transition sweep for one state \<open>u\<close> as a NAMED op, so it stays opaque in the outer
    \<open>count_pass_impl_refine\<close> (\<open>refine_vcg\<close> never normalises its body --- mirroring
    \<open>get_state_val_opt_lb_impl\<close> used inside \<open>updated_state_val_gs_impl_refine\<close>). Its refinement to the
    abstract inner \<^const>\<open>FOREACH\<close> is \<open>count_inner_refine\<close>; \<open>count_pass_ll\<close> unfolds it for synthesis.\<close>
  definition count_inner_impl ::
    "modest_mdp \<Rightarrow> mec_map \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat list \<times> nat list) nres" where
    "count_inner_impl MDP D u cntT cntB = do {
       (_, cntT, cntB) \<leftarrow> WHILET (\<lambda>(t, _). t < St_nth_uid MDP u) (\<lambda>(t, cntT, cntB). do {
          ASSERT (t < length (tTr MDP) - Suc 0);
          leaves \<leftarrow> trans_leaves_impl MDP D u t;
          (cntT, cntB) \<leftarrow> (if leaves then do {
            ASSERT (op_mec_index_of D u < length cntT \<and> op_mec_index_of D u < length cntB
                    \<and> Tr_nth MDP t \<le> Tr_nth MDP (Suc t)
                    \<and> cntT ! op_mec_index_of D u < length (tTr MDP)
                    \<and> cntB ! op_mec_index_of D u + (Tr_nth MDP (Suc t) - Tr_nth MDP t) \<le> length (tBr MDP));
            RETURN (cntT[op_mec_index_of D u := cntT ! op_mec_index_of D u + 1],
                    cntB[op_mec_index_of D u := cntB ! op_mec_index_of D u + (Tr_nth MDP (Suc t) - Tr_nth MDP t)])
          } else RETURN (cntT, cntB));
          ASSERT (t < length (tTr MDP));
          RETURN (Suc t, cntT, cntB)
       }) (St_nth_lid MDP u, cntT, cntB);
       RETURN (cntT, cntB) }"

  text \<open>Pass 1 outer sweep --- LLVM synthesis. The per-state count step (target/avoid MEC record + a
    nested transition/branch \<^const>\<open>WHILET\<close> with the \<open>trans_leaves\<close> test inlined) is written directly into
    the \<^const>\<open>nfoldli\<close> over the states \<^term>\<open>[0..<N]\<close> (min-side style; the loop element \<open>u\<close> narrows to
    \<open>node_assn\<close> via the structural accessors). The count arrays are created with \<^const>\<open>replicate\<close>; the
    target/avoid bitsets are passed IN empty (\<^const>\<open>bitset_assn\<close> has no fresh-creation \<open>hnr\<close>).\<close>
  definition count_pass_impl ::
    "modest_mdp \<Rightarrow> mec_map \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> (nat list \<times> nat list \<times> nat set \<times> nat set) nres" where
    "count_pass_impl MDP D Ta'0 avm0 = do {
       let cntT = replicate M 0;
       let cntB = replicate M 0;
       (cntT, cntB, Ta', avm) \<leftarrow> nfoldli [0..<N] (\<lambda>_. True)
         (\<lambda>u (cntT, cntB, Ta', avm). do {
            ASSERT (u < N \<and> (\<exists>i<length D. u \<in> D ! i));
            let c = op_mec_index_of D u;
            ASSERT (c < M);
            let Ta' = (if isT MDP u then insert c Ta' else Ta');
            let avm = (if isA MDP u then insert c avm else avm);
            (cntT, cntB) \<leftarrow> count_inner_impl MDP D u cntT cntB;
            RETURN (cntT, cntB, Ta', avm)
         }) (cntT, cntB, Ta'0, avm0);
       RETURN (cntT, cntB, Ta', avm) }"

  subsection \<open>Refinement of the count / copy passes to their abstract counterparts\<close>

  text \<open>The shared inner bridge: the early-exit branch \<^const>\<open>WHILET\<close> of \<open>trans_leaves_impl\<close> computes the
    abstract predicate \<^const>\<open>modest_collapse_invar.trans_leaves\<close> (\<open>\<exists>\<close> a branch of \<open>t\<close> targets another
    MEC). Reused by both the count and copy sweeps.\<close>
  lemma trans_leaves_impl_refine:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    assumes UB: "u < N" and TB: "t < length Tr - Suc 0"
    shows "trans_leaves_impl (St,Tr,Br,Pr,Av,Ta) D u t
           \<le> RETURN (modest_collapse_invar.trans_leaves Tr Br D (op_mec_index_of D u) t)"
  proof -
    interpret CI: modest_collapse_invar N St Tr Br Pr Av Ta D by (rule LOC)
    have TL1: "t < length Tr - Suc 0" using TB .
    hence SucL: "Suc t < length Tr" by simp
    have TLE: "Tr ! t \<le> Tr ! Suc t" using CI.sorted_Tr SucL by (simp add: sorted_nth_mono)
    have snI: "sn_intv (sorted_intvs Tr ! t) = {Tr ! t ..< Tr ! Suc t}"
      using sn_intv_sorted_intvs[OF CI.sorted_Tr TL1] .
    have inI: "in_intv (sorted_intvs Tr ! t) b" if "Tr ! t \<le> b" "b < Tr ! Suc t" for b
      using that snI by (auto simp: sn_intv_member[symmetric])
    have brange: "b < length Br" if "Tr ! t \<le> b" "b < Tr ! Suc t" for b
      using CI.Br_in_bound_intvD[OF TL1 inI[OF that]] .
    have brN: "Br ! b < N" if "Tr ! t \<le> b" "b < Tr ! Suc t" for b
      using CI.Br_in_bound[OF brange[OF that]] .
    have inD_u: "\<exists>i<length D. u \<in> D ! i" using CI.u_in_mec_of[OF UB] CI.mec_of_lt[OF UB] by blast
    have inD_br: "\<exists>i<length D. Br ! b \<in> D ! i" if "Tr ! t \<le> b" "b < Tr ! Suc t" for b
      using CI.u_in_mec_of[OF brN[OF that]] CI.mec_of_lt[OF brN[OF that]] by blast
    have eqmec: "(\<not> op_in_eq_mec D u (Br ! b)) = (op_mec_index_of D (Br ! b) \<noteq> op_mec_index_of D u)"
      if "Tr ! t \<le> b" "b < Tr ! Suc t" for b
    proof -
      have "op_in_eq_mec D u (Br!b) = (op_mec_index_of D u = op_mec_index_of D (Br!b))"
        unfolding op_in_eq_mec_def CI.mec_of_op_index
        by (metis CI.in_D_iff_mec_of[OF UB] CI.in_D_iff_mec_of[OF brN[OF that]]
                  CI.mec_of_lt[OF UB] CI.mec_of_lt[OF brN[OF that]])
      thus ?thesis by auto
    qed
    have TLrw: "modest_collapse_invar.trans_leaves Tr Br D (op_mec_index_of D u) t
                = (\<exists>b\<in>{Tr!t..<Tr!Suc t}. \<not> op_in_eq_mec D u (Br ! b))"
      unfolding CI.trans_leaves_def set_ls_intv snI using eqmec by (auto simp: atLeastLessThan_iff)
    show ?thesis
      unfolding trans_leaves_impl_def Tr_nth_alt Br_nth_alt TLrw
      apply simp
      apply (refine_vcg WHILET_rule[where R="Wellfounded.measure (\<lambda>(b,_). Tr ! Suc t - b)"
          and I="\<lambda>(b,flag). Tr ! t \<le> b \<and> b \<le> Tr ! Suc t
                 \<and> (flag = (\<exists>b'\<in>{Tr!t..<b}. \<not> op_in_eq_mec D u (Br ! b')))"])
      using TL1 TLE inD_u
      by (auto simp: atLeastLessThanSuc atLeastLessThan_iff intro: brange inD_br)
  qed

  text \<open>The inner transition sweep for one state \<open>u\<close> (with \<open>c = op_mec_index_of D u\<close>): the concrete
    counter \<^const>\<open>WHILET\<close> refines the abstract inner \<^const>\<open>FOREACH\<close> of \<open>count_pass\<close>. Proved with the
    2-step \<open>f\<close> (\<^const>\<open>WHILE_intv\<close>) bridge of \<open>get_state_val_opt_lb_impl_refine\<close>; \<open>u < N\<close> is available,
    so the counter bound discharges here. All the impl's write bounds are \<^emph>\<open>relative\<close> to the input
    arrays (\<open>cntT ! c < length Tr\<close>, \<open>cntB ! c + \<dots> \<le> length Br\<close>) --- literally the abstract pass's own
    assertions --- so they need no machine-word side conditions; the \<open>sepref\<close> layer turns them into
    the snat overflow bounds via @{thm [source] Modest_mdp_assn_boundsD}.\<close>
  lemma count_inner_refine:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    assumes UB: "u < N"
    shows "count_inner_impl (St, Tr, Br, Pr, Av, Ta) D u cntT cntB
           \<le> FOREACH (sn_intv (sorted_intvs St ! u))
          (\<lambda>t (cntT, cntB). do {
             ASSERT (t < length Tr - Suc 0);
             if modest_collapse_invar.trans_leaves Tr Br D (op_mec_index_of D u) t
             then do {
               ASSERT (op_mec_index_of D u < length cntT \<and> op_mec_index_of D u < length cntB
                       \<and> cntT ! op_mec_index_of D u < length Tr
                       \<and> cntB ! op_mec_index_of D u + length (ls_intv (sorted_intvs Tr ! t)) \<le> length Br);
               RETURN (cntT[op_mec_index_of D u := cntT ! op_mec_index_of D u + 1],
                       cntB[op_mec_index_of D u := cntB ! op_mec_index_of D u + length (ls_intv (sorted_intvs Tr ! t))]) }
             else RETURN (cntT, cntB) })
          (cntT, cntB)"
  proof -
    interpret CI: modest_collapse_invar N St Tr Br Pr Av Ta D by (rule LOC)
    define f where "f = WHILE_intv (tSt (St, Tr, Br, Pr, Av, Ta)) u (\<lambda>t (cntT, cntB). do {
           ASSERT (t < length (tTr (St, Tr, Br, Pr, Av, Ta)) - Suc 0);
           leaves \<leftarrow> trans_leaves_impl (St, Tr, Br, Pr, Av, Ta) D u t;
           (if leaves then do {
             ASSERT (op_mec_index_of D u < length cntT \<and> op_mec_index_of D u < length cntB
                     \<and> Tr_nth (St, Tr, Br, Pr, Av, Ta) t \<le> Tr_nth (St, Tr, Br, Pr, Av, Ta) (Suc t)
                     \<and> cntT ! op_mec_index_of D u < length Tr
                     \<and> cntB ! op_mec_index_of D u + (Tr_nth (St, Tr, Br, Pr, Av, Ta) (Suc t) - Tr_nth (St, Tr, Br, Pr, Av, Ta) t) \<le> length Br);
             RETURN (cntT[op_mec_index_of D u := cntT ! op_mec_index_of D u + 1],
                     cntB[op_mec_index_of D u := cntB ! op_mec_index_of D u + (Tr_nth (St, Tr, Br, Pr, Av, Ta) (Suc t) - Tr_nth (St, Tr, Br, Pr, Av, Ta) t)])
           } else RETURN (cntT, cntB))
        }) (cntT, cntB)"
    have SucU: "St ! Suc u < length Tr"
      using CI.St_in_bound[OF UB] uid_sorted_intvs[OF CI.sorted_St, of u] UB by (simp add: CI.N_DEF)
    have LenEq: "length (ls_intv (sorted_intvs Tr ! t)) = Tr ! Suc t - Tr ! t" if "t < length Tr - Suc 0" for t
      using that by (simp add: CI.sorted_Tr)
    have TrMono: "Tr ! t \<le> Tr ! Suc t" if "t < length Tr - Suc 0" for t
      using that CI.sorted_Tr by (simp add: sorted_nth_mono)
    have TLbridge: "trans_leaves_impl (St, Tr, Br, Pr, Av, Ta) D u t \<bind> g
        \<le> g (modest_collapse_invar.trans_leaves Tr Br D (op_mec_index_of D u) t)"
      if "t < length Tr - Suc 0" for t and g :: "bool \<Rightarrow> 'b nres"
    proof -
      have "trans_leaves_impl (St, Tr, Br, Pr, Av, Ta) D u t \<bind> g
          \<le> RETURN (modest_collapse_invar.trans_leaves Tr Br D (op_mec_index_of D u) t) \<bind> g"
        by (rule bind_mono(1)[OF trans_leaves_impl_refine[OF LOC UB that]]) auto
      thus ?thesis by simp
    qed
    have S1: "count_inner_impl (St, Tr, Br, Pr, Av, Ta) D u cntT cntB \<le> f"
      unfolding count_inner_impl_def f_def WHILE_intv_def St_nth_uid_alt St_nth_lid_alt
      apply refine_mono
      subgoal for x a b
        apply (cases b)
        apply (simp only: prod.case nres_monad_laws)
        apply refine_mono
        using SucU apply (auto simp: pw_le_iff refine_pw_simps split: prod.splits)
        done
      subgoal by (auto split: prod.splits)
      done
    have S2: "f \<le> FOREACH (sn_intv (sorted_intvs St ! u))
          (\<lambda>t (cntT, cntB). do {
             ASSERT (t < length Tr - Suc 0);
             if modest_collapse_invar.trans_leaves Tr Br D (op_mec_index_of D u) t
             then do {
               ASSERT (op_mec_index_of D u < length cntT \<and> op_mec_index_of D u < length cntB
                       \<and> cntT ! op_mec_index_of D u < length Tr
                       \<and> cntB ! op_mec_index_of D u + length (ls_intv (sorted_intvs Tr ! t)) \<le> length Br);
               RETURN (cntT[op_mec_index_of D u := cntT ! op_mec_index_of D u + 1],
                       cntB[op_mec_index_of D u := cntB ! op_mec_index_of D u + length (ls_intv (sorted_intvs Tr ! t))]) }
             else RETURN (cntT, cntB) })
          (cntT, cntB)"
      unfolding f_def
      apply (clarsimp simp flip: FOREACH_intv_def)
      apply (refine_vcg WHILE_intv_refine[where R=Id, simplified] while.ibind_mono)
      subgoal by (rule CI.sorted_St)
      subgoal using UB by (simp add: CI.N_DEF)
      subgoal by simp
      subgoal by simp
      subgoal for x xi s si x1 x2 x1a x2a
        apply (rule order_trans[OF TLbridge], assumption)
        apply (auto simp: pw_le_iff refine_pw_simps Tr_nth_alt cnt_sorted_intvs[OF CI.sorted_Tr] TrMono split: if_splits)
        done
      subgoal by simp
      done
    from S1 S2 show ?thesis by (rule order_trans)
  qed

  lemma count_pass_impl_refine:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    assumes MD: "M = length D"
    shows "count_pass_impl (St, Tr, Br, Pr, Av, Ta) D {} {}
           \<le> modest_collapse_invar.count_pass N St Tr Br Av Ta D"
  proof -
    interpret CI: modest_collapse_invar N St Tr Br Pr Av Ta D by (rule LOC)
    have isTeq: "isT (St, Tr, Br, Pr, Av, Ta) u = (u \<in> Ta)" for u
      by (simp add: isT_alt modest_mdp_input_def.is_target_state_def)
    have isAeq: "isA (St, Tr, Br, Pr, Av, Ta) u = (u \<in> Av)" for u
      by (simp add: isA_alt modest_mdp_input_def.is_avoid_state_def)
    have RT: "(\<lambda>(a::nat list, b::nat list, c::nat set, d::nat set). RETURN (a, b, c, d)) = RETURN"
      by (auto simp: fun_eq_iff)
    have RTpair: "(\<lambda>(cntT::nat list, cntB::nat list). RETURN (cntT, cntB)) = RETURN"
      by (auto simp: fun_eq_iff split: prod.splits)
    show ?thesis
      unfolding count_pass_impl_def CI.count_pass_def
      unfolding MD Let_def
      apply (simp only: RT nres_monad2)
      apply (rule refine_IdD)
      apply (rule LFO_refine[where A=Id and R=Id])
      subgoal by (rule upt_list_set_rel)
      subgoal
        apply clarsimp
        apply (refine_vcg count_inner_refine[OF LOC])
        subgoal using CI.u_in_mec_of CI.mec_of_lt by blast
        subgoal by (auto simp: CI.mec_of_op_index CI.mec_of_lt)
        subgoal
          apply (simp only: prod.inject)
          apply (rule bind_mono(1))
           apply (rule count_inner_refine[OF LOC])
           apply blast
          apply (auto simp: isTeq isAeq)
          done
        done
      subgoal by simp
      done
  qed

  \<comment> \<open>The inner \<open>trans_leaves\<close> branch loop is now a registered sub-op (\<open>trans_leaves_ll\<close> + the
    \<open>sepref_fr_rules\<close> above), called directly in \<open>count_pass_impl\<close>, so this sepref translates only the
    outer state/transition sweep with the branch loop as one pre-synthesised call --- avoiding the
    ~34 min blow-up of re-translating the nested branch loop per transition.\<close>
  sepref_definition count_pass_ll is "uncurry3 (PR_CONST count_pass_impl)"
    :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a mec_map_assn\<^sup>k *\<^sub>a (bitset_own_assn M)\<^sup>d *\<^sub>a (bitset_own_assn M)\<^sup>d
        \<rightarrow>\<^sub>a (IICF_Array.array_assn size_assn \<times>\<^sub>a IICF_Array.array_assn size_assn
             \<times>\<^sub>a bitset_own_assn M \<times>\<^sub>a bitset_own_assn M)"
    unfolding PR_CONST_def count_pass_impl_def count_inner_impl_def nfoldli_upt_by_while
      Suc_eq_plus1[symmetric] conj.comm_neutral
    apply (rewrite array_fold_custom_replicate)
    apply (rewrite array_fold_custom_replicate)
    supply [elim] = less_trans_Suc[OF _ Modest_mdp_assn_boundsD(2), rotated]
      less_trans_Suc[OF _ Modest_mdp_assn_boundsD(1), rotated]
      le_less_trans[OF _ Modest_mdp_assn_boundsD(2), rotated]
      mec_map_eq_set_mem_preI Suc_N_leq_max
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done


  subsection \<open>Pass 3: offset / prefix-sum --- the CSR block-opening arrays\<close>

  text \<open>Prefix-sum over the MECs \<open>[0..<M]\<close>: \<open>St'!c = ctA c\<close> (transition-block opening), \<open>boff!c = cbA c\<close>
    (branch-block opening), returning the totals \<open>nT = cnt_T\<close>, \<open>nB = cnt_B\<close>. Sink MECs (\<open>c \<in> Ta' \<union> Av'\<close>)
    contribute a single self-loop slot (\<open>1\<close>/\<open>1\<close>); non-sinks contribute their counts \<open>cntT!c\<close>/\<open>cntB!c\<close>.
    The accumulators \<open>ct\<close>/\<open>cb\<close> are snat sums, so the body carries the \<^emph>\<open>relative\<close> capacity
    \<open>ASSERT\<close>s \<open>ct + dT \<le> length Tr\<close> / \<open>cb + dB \<le> length Br\<close> --- the running block openings never
    exceed the input CSR arrays. They are exactly the assertions of the abstract pass, and are what
    the \<open>sepref\<close> layer turns into the snat overflow bounds (via @{thm [source]
    Modest_mdp_assn_boundsD}); this is why the pass takes the input MDP as a kept argument.\<close>
  definition offset_body ::
    "modest_mdp \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat
      \<Rightarrow> (nat list \<times> nat list \<times> nat \<times> nat) \<Rightarrow> (nat list \<times> nat list \<times> nat \<times> nat) nres" where
    "offset_body MDP cntT cntB Ta' Av' c = (\<lambda>(St', boff, ct, cb). do {
        ASSERT (c < M \<and> c < length St' \<and> c < length boff \<and> c < length cntT \<and> c < length cntB);
        let dT = (if c \<in> Ta' \<or> c \<in> Av' then 1 else cntT ! c);
        let dB = (if c \<in> Ta' \<or> c \<in> Av' then 1 else cntB ! c);
        ASSERT (ct + dT \<le> length (tTr MDP) \<and> cb + dB \<le> length (tBr MDP));
        RETURN (St'[c := ct], boff[c := cb], ct + dT, cb + dB)
     })"

  definition offset_impl ::
    "modest_mdp \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat set \<Rightarrow> nat set
      \<Rightarrow> (nat list \<times> nat list \<times> nat \<times> nat) nres" where
    "offset_impl MDP cntT cntB Ta' Av' = do {
       let St'0 = replicate (M + 1) 0;
       let boff0 = replicate (M + 1) 0;
       (_, (St', boff, ct, cb)) \<leftarrow> WHILET (\<lambda>(i, _). i < M \<and> True) (\<lambda>(i, \<sigma>). do {
           \<sigma> \<leftarrow> offset_body MDP cntT cntB Ta' Av' i \<sigma>;
           ASSERT (i < M);
           RETURN (i + 1, \<sigma>)
       }) (0, (St'0, boff0, 0, 0));
       ASSERT (M < length St' \<and> M < length boff);
       RETURN (St'[M := ct], boff[M := cb], ct, cb)
    }"

  lemma offset_impl_nfoldli:
    "offset_impl MDP cntT cntB Ta' Av' = do {
       let St'0 = replicate (M + 1) 0;
       let boff0 = replicate (M + 1) 0;
       (St', boff, ct, cb) \<leftarrow> nfoldli [0..<M] (\<lambda>_. True) (offset_body MDP cntT cntB Ta' Av') (St'0, boff0, 0, 0);
       ASSERT (M < length St' \<and> M < length boff);
       RETURN (St'[M := ct], boff[M := cb], ct, cb)
    }"
    unfolding offset_impl_def nfoldli_upt_by_while
    by (simp add: split_def)

  lemma offset_impl_refine:
    assumes MD: "M = length D"
    assumes LcT: "length cntT = M" and LcB: "length cntB = M"
    assumes cntTcap: "(\<Sum>c = 0..<M. if c \<in> Ta' \<or> c \<in> Av' then 1 else cntT ! c) \<le> length Tr"
    assumes cntBcap: "(\<Sum>c = 0..<M. if c \<in> Ta' \<or> c \<in> Av' then 1 else cntB ! c) \<le> length Br"
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    shows "offset_impl (St, Tr, Br, Pr, Av, Ta) cntT cntB Ta' Av'
           \<le> modest_collapse_invar.offset_pass D cntT cntB Ta' Av'"
  proof -
    interpret CI: modest_collapse_invar N St Tr Br Pr Av Ta D by (rule LOC)
    let ?dT = "\<lambda>c. if c \<in> Ta' \<or> c \<in> Av' then (1::nat) else cntT ! c"
    let ?dB = "\<lambda>c. if c \<in> Ta' \<or> c \<in> Av' then (1::nat) else cntB ! c"
    have ovfT: "(\<Sum>c = 0..<i. ?dT c) + ?dT i \<le> length Tr" if "i < M" for i
    proof -
      have "(\<Sum>c = 0..<i. ?dT c) + ?dT i = (\<Sum>c = 0..<Suc i. ?dT c)"
        by (simp add: sum.atLeast0_lessThan_Suc)
      also have "\<dots> \<le> (\<Sum>c = 0..<M. ?dT c)" using that by (intro sum_mono2) auto
      finally show ?thesis using cntTcap by simp
    qed
    have ovfB: "(\<Sum>c = 0..<i. ?dB c) + ?dB i \<le> length Br" if "i < M" for i
    proof -
      have "(\<Sum>c = 0..<i. ?dB c) + ?dB i = (\<Sum>c = 0..<Suc i. ?dB c)"
        by (simp add: sum.atLeast0_lessThan_Suc)
      also have "\<dots> \<le> (\<Sum>c = 0..<M. ?dB c)" using that by (intro sum_mono2) auto
      finally show ?thesis using cntBcap by simp
    qed
    let ?I = "\<lambda>l1i l2i (St'::nat list, boff::nat list, ct, cb).
               ct = (\<Sum>c = 0..<length l1i. ?dT c) \<and> cb = (\<Sum>c = 0..<length l1i. ?dB c)"
    let ?R = "br id (\<lambda>(St'::nat list, boff::nat list, ct::nat, cb::nat). length St' = M + 1 \<and> length boff = M + 1)"
    show ?thesis
      unfolding offset_impl_nfoldli modest_collapse_invar.offset_pass_def[OF LOC] MD[symmetric] Let_def
      apply (rule refine_IdD)
      apply (rule bind_refine[where R'="?R"])
      subgoal
        apply (rule nfoldli_invar_refine[where I="?I" and R="?R" and S=Id])
        subgoal by simp
        subgoal by (simp add: in_br_conv)
        subgoal by simp
        subgoal by simp
        subgoal for l1i xi l2i si
          by (auto simp: offset_body_def Let_def pw_leof_iff refine_pw_simps sum.atLeast0_lessThan_Suc
              split: prod.splits dest!: CI.upt_split_elem)
        subgoal premises prems for l1i xi l2i l1 x l2 si s
        proof -
          from prems(1) have xi_eq: "xi = length l1i" and xi_lt: "length l1i < M"
            using CI.upt_split_elem by blast+
          from prems have xx: "x = xi" by simp
          obtain St' boff ct cb where si: "si = (St', boff, ct, cb)" by (cases si) auto
          from prems have I: "ct = (\<Sum>c = 0..<length l1i. ?dT c)"
            and Ib: "cb = (\<Sum>c = 0..<length l1i. ?dB c)" by (auto simp: si)
          from prems have "(si, s) \<in> ?R" by simp
          then have s_eq: "s = si" and lenSt: "length St' = M + 1" and lenbo: "length boff = M + 1"
            by (auto simp: in_br_conv si)
          have ov1: "ct + ?dT xi \<le> length Tr" using ovfT[OF xi_lt] by (simp only: I xi_eq)
          have ov2: "cb + ?dB xi \<le> length Br" using ovfB[OF xi_lt] by (simp only: Ib xi_eq)
          show ?thesis
            unfolding si s_eq xx offset_body_def
            using xi_eq xi_lt lenSt lenbo ov1 ov2 LcT LcB
            by (auto simp: in_br_conv pw_le_iff refine_pw_simps Let_def)
        qed
        done
      subgoal for x x'
        by (auto simp: in_br_conv pw_le_iff refine_pw_simps split: prod.splits)
      done
  qed

  sepref_definition offset_ll is "uncurry4 (PR_CONST offset_impl)"
    :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>k
        *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>k
        *\<^sub>a (bitset_own_assn M)\<^sup>k *\<^sub>a (bitset_own_assn M)\<^sup>k
        \<rightarrow>\<^sub>a (IICF_Array.array_assn size_assn \<times>\<^sub>a IICF_Array.array_assn size_assn \<times>\<^sub>a size_assn \<times>\<^sub>a size_assn)"
    unfolding PR_CONST_def offset_impl_def offset_body_def
    supply [elim] = le_less_trans[OF _ Modest_mdp_assn_boundsD(1), rotated]
      le_less_trans[OF _ Modest_mdp_assn_boundsD(2), rotated]
    supply [simp] = M_Suc_max
    apply (rewrite array_fold_custom_replicate)
    apply (rewrite array_fold_custom_replicate)
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done


  subsection \<open>Passes 4 and 5: copy / scatter and self-loops\<close>

  text \<open>Generic outer-sweep bridge: an ordered \<^const>\<open>nfoldli\<close> over \<^term>\<open>[0..<n]\<close> refines the
    order-free \<^const>\<open>FOREACH\<close> over \<^term>\<open>{0..<n}\<close> when the body is unchanged (the body subgoal
    reduces to \<open>B \<le> \<Down>Id B\<close> after identifying the related indices/states). Both the copy pass and the
    self-loop pass replace only their outer \<^const>\<open>FOREACH\<close> sweeps by \<^const>\<open>nfoldli\<close> (which \<open>sepref\<close>
    can translate), keeping their bodies verbatim.\<close>
  lemma nfoldli_upt_FOREACH_Id:
    "nfoldli [0..<n] (\<lambda>_. True) f \<sigma> \<le> \<Down>Id (FOREACH {0..<n} f \<sigma>)"
    apply (rule LFO_refine[where A=Id])
    subgoal by (rule upt_list_set_rel)
    subgoal by (auto simp: conc_Id)
    subgoal by simp
    done

  lemma nfoldli_upt_le_FOREACH: "nfoldli [0..<n] (\<lambda>_. True) f \<sigma> \<le> FOREACH {0..<n} f \<sigma>"
    using nfoldli_upt_FOREACH_Id[of n f \<sigma>] by (simp add: conc_Id)

  text \<open>Pass 4 (copy / scatter): the abstract \<^const>\<open>modest_collapse_invar.copy_pass\<close> with its two
    outer \<^const>\<open>FOREACH\<close> sweeps (the \<open>Tr'\<close>-prefill over \<^term>\<open>[0..<length D]\<close> and the state scatter
    over \<^term>\<open>[0..<N]\<close>) turned into \<^const>\<open>nfoldli\<close>; the inner per-transition / per-branch loops stay
    \<^const>\<open>FOREACH\<close> (order-free).\<close>
  definition copy_pass_impl where
    "copy_pass_impl St Tr Br Pr D St' boff Ta' Av' nT nB = do {
       let Tr' = replicate (nT + 1) 0;
       let Br' = replicate nB 0;
       let Pr' = replicate nB 1;
       Tr' \<leftarrow> nfoldli [0..<length D] (\<lambda>_. True) (\<lambda>c Tr'. RETURN (Tr'[St' ! c := boff ! c])) Tr';
       let curT = St';
       let curB = boff;
       (Tr', Br', Pr', curT, curB) \<leftarrow> nfoldli [0..<N] (\<lambda>_. True)
         (\<lambda>u (Tr', Br', Pr', curT, curB). do {
            let c = op_mec_index_of D u;
            if c \<in> Ta' \<or> c \<in> Av' then RETURN (Tr', Br', Pr', curT, curB)
            else FOREACH (sn_intv (sorted_intvs St ! u))
               (\<lambda>t (Tr', Br', Pr', curT, curB).
                  if modest_collapse_invar.trans_leaves Tr Br D c t then do {
                    ASSERT (c < length curT \<and> c < length curB
                            \<and> curT ! c < length Tr' \<and> curT ! c + 1 < length Tr'
                            \<and> curT ! c < length Tr
                            \<and> curB ! c + cnt (sorted_intvs Tr ! t) \<le> length Br'
                            \<and> length Pr' = length Br' \<and> length Br' \<le> length Br);
                    let Tr' = Tr'[curT ! c := curB ! c];
                    (Br', Pr', cbc) \<leftarrow> FOREACH (sn_intv (sorted_intvs Tr ! t))
                       (\<lambda>b (Br', Pr', cbc).
                          RETURN (Br'[cbc := op_mec_index_of D (Br ! b)], Pr'[cbc := Pr ! b], cbc + 1))
                       (Br', Pr', curB ! c);
                    let curB = curB[c := cbc];
                    let Tr' = Tr'[curT ! c + 1 := curB ! c];
                    RETURN (Tr', Br', Pr', curT[c := curT ! c + 1], curB)
                  } else RETURN (Tr', Br', Pr', curT, curB))
               (Tr', Br', Pr', curT, curB) })
         (Tr', Br', Pr', curT, curB);
       RETURN (Tr', Br', Pr', curT, curB) }"

  text \<open>Step-2 refinement: the concrete \<open>copy_pass_impl\<close> refines the abstract
    \<^const>\<open>modest_collapse_invar.copy_pass\<close>. They are identical except (i) the abstract has a leading
    \<open>ASSERT (nT < length Tr)\<close> (the impl drops it --- absorbed by \<open>base\<close>, since \<open>m \<le> ASSERT P \<bind>
    (\<lambda>_. m)\<close> always: on \<open>\<not>P\<close> the RHS is \<^const>\<open>FAIL\<close>), and (ii) the two OUTER sweeps (the \<open>Tr'\<close>-prefill
    over \<^term>\<open>[0..<length D]\<close> and the state scatter over \<^term>\<open>[0..<N]\<close>) are \<^const>\<open>nfoldli\<close> vs
    \<^const>\<open>FOREACH\<close> --- reduced by \<open>nfoldli_upt_le_FOREACH\<close> since the bodies (with the inner
    \<^const>\<open>FOREACH\<close>es kept verbatim) are syntactically identical.\<close>
  lemma copy_pass_impl_refine:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    shows "copy_pass_impl St Tr Br Pr D St' boff Ta' Av' nT nB
             \<le> modest_collapse_invar.copy_pass N St Tr Br Pr D St' boff Ta' Av' nT nB"
  proof -
    interpret CI: modest_collapse_invar N St Tr Br Pr Av Ta D by (rule LOC)
    have base: "copy_pass_impl St Tr Br Pr D St' boff Ta' Av' nT nB
        \<le> ASSERT (nT < length Tr) \<bind> (\<lambda>_. copy_pass_impl St Tr Br Pr D St' boff Ta' Av' nT nB)"
      by (cases "nT < length Tr") (auto simp: pw_le_iff refine_pw_simps)
    show ?thesis
      apply (rule order_trans[OF base])
      unfolding CI.copy_pass_def
      apply (rule bind_mono(1)[OF order_refl])
      unfolding copy_pass_impl_def Let_def
      apply (rule bind_mono(1))
       apply (rule nfoldli_upt_le_FOREACH)
      apply (rule bind_mono(1))
       apply (rule nfoldli_upt_le_FOREACH)
      apply (rule order_refl)
      done
  qed

  text \<open>Pass 5 (self-loops): the abstract \<^const>\<open>modest_collapse_invar.selfloop_pass\<close> sweep over the
    sink MECs \<^term>\<open>[0..<length D]\<close>, turned into \<^const>\<open>nfoldli\<close>; the body is verbatim.\<close>
  definition selfloop_pass_impl where
    "selfloop_pass_impl D Tr' Br' Pr' St' boff Ta' Av' =
       nfoldli [0..<length D] (\<lambda>_. True)
          (\<lambda>c (Tr', Br', Pr').
             if c \<in> Ta' \<or> c \<in> Av' then
               RETURN (Tr'[St' ! c := boff ! c, St' ! c + 1 := boff ! c + 1],
                       Br'[boff ! c := c], Pr'[boff ! c := 1])
             else RETURN (Tr', Br', Pr'))
          (Tr', Br', Pr')"

  lemma selfloop_pass_impl_refine:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    shows "selfloop_pass_impl D Tr' Br' Pr' St' boff Ta' Av'
             \<le> modest_collapse_invar.selfloop_pass D Tr' Br' Pr' St' boff Ta' Av'"
    unfolding selfloop_pass_impl_def modest_collapse_invar.selfloop_pass_def[OF LOC]
    by (rule nfoldli_upt_le_FOREACH)


  subsection \<open>The built probability constant \<open>1\<close> at \<^const>\<open>pfin_real_intv_assn\<close>\<close>

  text \<open>The built MDP's probability array \<open>Pr'\<close> refines to \<^const>\<open>pfin_real_intv_assn\<close> (a pair of
    doubles), the same encoding the input \<open>Pr\<close> uses (so the II backup's \<open>op_fma_*_nn_intv\<close> can consume
    it). Building \<open>Pr'\<close> needs a \<^emph>\<open>constant\<close> probability (\<open>1\<close> for the sink self-loops, and a dummy fill
    for the initial \<^const>\<open>replicate\<close>, overwritten by the copy pass). \<^const>\<open>pfin_real_invar\<close> excludes
    \<open>0\<close>, so there is no pfin \<open>0\<close>; we use \<open>1\<close> throughout. There is no idiom in the codebase to build a
    pfin constant (probabilities are only ever read from the input), so we synthesise it manually: a
    double pair \<^term>\<open>(op_fp64_1, op_fp64_1)\<close> composed with the interval relation.\<close>

  definition op_one_pfin :: real where "op_one_pfin \<equiv> 1"

  definition op_zero_pfin :: real where "op_zero_pfin \<equiv> 0"

  lemma pfin_real_invar_op_fp64_1: "pfin_real_invar op_fp64_1"
    unfolding pfin_real_invar_def by (simp add: is_zero_iff_valof0)

  lemma op_one_pfin_refine: "((op_fp64_1, op_fp64_1), op_one_pfin) \<in> pfin_real_intv_rel"
    unfolding pfin_real_intv_rel_def op_one_pfin_def
    using pfin_real_invar_op_fp64_1 by simp

  text \<open>A ground constant tuple \<^term>\<open>RETURN (op_fp64_1, op_fp64_1)\<close> is one atomic "invalid abstract
    head" for \<open>sepref\<close>; binding each \<^const>\<open>op_fp64_1\<close> as a monadic variable (and unfolding it to its
    float literal) lets \<open>sepref\<close> build each double and pair the variables.\<close>
  definition mk_pfin_one_pair :: "((11,52) IEEE.float \<times> (11,52) IEEE.float) nres" where
    "mk_pfin_one_pair = do { a \<leftarrow> RETURN op_fp64_1; b \<leftarrow> RETURN op_fp64_1; RETURN (a, b) }"

  sepref_def mk_pfin_one_pair_ll is "uncurry0 mk_pfin_one_pair"
    :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_intv_assn"
    unfolding mk_pfin_one_pair_def word_float_test_def op_fp64_1_def
    by sepref

  lemma mk_pfin_one_pair_alt: "mk_pfin_one_pair = RETURN (op_fp64_1, op_fp64_1)"
    unfolding mk_pfin_one_pair_def by simp

end

text \<open>Extracted here, before its caller \<open>selfloop_ll\<close> is synthesised, so that the emitted code calls
  the \<^emph>\<open>global\<close> constant. Otherwise \<open>export_llvm\<close> later stops with \<open>No code equation
  collapse_build_env.mk_pfin_one_pair_ll\<close>: a locale-local LLVM constant has only a \<^emph>\<open>conditional\<close>
  defining equation, which the code generator cannot use.\<close>
concrete_definition (in -) mk_pfin_one_pair_ll' [llvm_code] is
  collapse_build_env.mk_pfin_one_pair_ll_def

context collapse_build_env
begin

  interpretation disj_set_list_tuple_env N N ni ni
    apply unfold_locales using n_impl by auto

  text \<open>Compose the double-pair op with the interval relation (\<open>folded pfin_real_intv_assn_alt\<close> refolds
    the FCOMP output \<open>hr_comp dfloat_intv_assn pfin_real_intv_rel\<close> back to \<^const>\<open>pfin_real_intv_assn\<close>,
    so array alloc/write over the built \<open>Pr'\<close> leaves no residual frame goal).\<close>
  sepref_register op_one_pfin
  lemmas op_one_pfin_hnr[sepref_fr_rules] =
    mk_pfin_one_pair_ll.refine[unfolded mk_pfin_one_pair_alt, FCOMP op_one_pfin_refine,
      folded pfin_real_intv_assn_alt,
      unfolded mk_pfin_one_pair_ll'.refine[OF collapse_build_env_loc]]


  subsection \<open>Pass 5: self-loops --- LLVM synthesis\<close>

  text \<open>The \<open>sepref\<close>-translatable form of the self-loop pass: one \<^const>\<open>WHILET\<close> sweep over the MECs
    \<^term>\<open>[0..<M]\<close>; each sink \<open>c\<close> writes its one-slot self-loop block into \<open>Tr'\<close>/\<open>Br'\<close>/\<open>Pr'\<close> (with
    \<open>Pr'\<close> the probability array, filled with \<^const>\<open>op_one_pfin\<close> \<open>= 1\<close>). All \<open>ASSERT\<close>s are array-index
    bounds --- the two write cursors also sit inside the \<^emph>\<open>input\<close> CSR arrays, which is what lets the
    \<open>sepref\<close> layer bound the cursor increments (via @{thm [source] Modest_mdp_assn_boundsD}); hence the
    kept input-MDP argument. They are discharged in the refinement from the offset semantics.\<close>
  definition selfloop_body ::
    "modest_mdp \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat
      \<Rightarrow> (nat list \<times> nat list \<times> real list) \<Rightarrow> (nat list \<times> nat list \<times> real list) nres" where
    "selfloop_body MDP St' boff Ta' Av' c = (\<lambda>(Tr', Br', Pr'). do {
       ASSERT (c < M);
       if c \<in> Ta' \<or> c \<in> Av' then do {
          ASSERT (c < length St' \<and> c < length boff);
          let a = St' ! c;
          let b = boff ! c;
          ASSERT (a < length Tr' \<and> a + 1 < length Tr' \<and> b < length Br' \<and> b < length Pr'
                  \<and> a < length (tTr MDP) \<and> b < length (tBr MDP));
          let Tr' = Tr'[a := b];
          let Tr' = Tr'[a + 1 := b + 1];
          let Br' = Br'[b := c];
          let Pr' = Pr'[b := op_one_pfin];
          RETURN (Tr', Br', Pr')
       } else RETURN (Tr', Br', Pr') })"

  definition selfloop_impl ::
    "modest_mdp \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> real list
      \<Rightarrow> (nat list \<times> nat list \<times> real list) nres" where
    "selfloop_impl MDP St' boff Ta' Av' Tr'0 Br'0 Pr'0 = do {
       (_, (Tr', Br', Pr')) \<leftarrow> WHILET (\<lambda>(i, _). i < M \<and> True) (\<lambda>(i, \<sigma>). do {
           \<sigma> \<leftarrow> selfloop_body MDP St' boff Ta' Av' i \<sigma>;
           ASSERT (i < M);
           RETURN (i + 1, \<sigma>)
       }) (0, (Tr'0, Br'0, Pr'0));
       RETURN (Tr', Br', Pr') }"

  lemma selfloop_impl_nfoldli:
    "selfloop_impl MDP St' boff Ta' Av' Tr'0 Br'0 Pr'0 = do {
       (Tr', Br', Pr') \<leftarrow> nfoldli [0..<M] (\<lambda>_. True) (selfloop_body MDP St' boff Ta' Av') (Tr'0, Br'0, Pr'0);
       RETURN (Tr', Br', Pr') }"
    unfolding selfloop_impl_def nfoldli_upt_by_while
    by (simp add: split_def)

  text \<open>Correctness of the self-loop LLVM impl: \<open>selfloop_impl \<le> selfloop_pass\<close>. The impl's \<^const>\<open>WHILET\<close>
    refines the abstract \<^const>\<open>FOREACH\<close> (bodies agree, \<^const>\<open>op_one_pfin\<close>\<open> = 1\<close>); the array-index /
    overflow \<open>ASSERT\<close>s are discharged from the bound hypothesis \<open>BND\<close> (supplied at assembly time by
    \<open>modest_collapse_invar.selfloop_sink_bounds\<close> from the offset semantics).\<close>
  lemma selfloop_impl_refine:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D" and MD: "M = length D"
    assumes BND: "\<forall>c<M. (c \<in> Ta' \<or> c \<in> Av') \<longrightarrow>
        c < length St' \<and> c < length boff \<and> St' ! c < length Tr'0 \<and> St' ! c + 1 < length Tr'0
        \<and> boff ! c < length Br'0 \<and> boff ! c < length Pr'0
        \<and> St' ! c < length Tr \<and> boff ! c < length Br"
    shows "selfloop_impl (St, Tr, Br, Pr, Av, Ta) St' boff Ta' Av' Tr'0 Br'0 Pr'0
           \<le> modest_collapse_invar.selfloop_pass D Tr'0 Br'0 Pr'0 St' boff Ta' Av'"
  proof -
    interpret CI: modest_collapse_invar N St Tr Br Pr Av Ta D by (rule LOC)
    let ?abody = "\<lambda>c (Tr', Br', Pr').
        if c \<in> Ta' \<or> c \<in> Av' then
          RETURN (Tr'[St' ! c := boff ! c, St' ! c + 1 := boff ! c + 1], Br'[boff ! c := c], Pr'[boff ! c := 1])
        else RETURN (Tr', Br', Pr') :: (nat list \<times> nat list \<times> real list) nres"
    \<comment> \<open>Length-preserving diagonal relation: carries \<open>length Tr' = length Tr'0\<close> etc. across the fold so
       the impl's array-bound \<^const>\<open>ASSERT\<close>s (on the evolving arrays) reduce to \<open>BND\<close> (on \<open>Tr'0\<close>...).\<close>
    let ?R = "br id (\<lambda>(Tr'::nat list, Br'::nat list, Pr'::real list).
                length Tr' = length Tr'0 \<and> length Br' = length Br'0 \<and> length Pr' = length Pr'0)"
    have Rsub: "?R \<subseteq> Id" by (auto simp: in_br_conv)
    have si_eq: "selfloop_impl (St, Tr, Br, Pr, Av, Ta) St' boff Ta' Av' Tr'0 Br'0 Pr'0
                 = nfoldli [0..<M] (\<lambda>_. True) (selfloop_body (St, Tr, Br, Pr, Av, Ta) St' boff Ta' Av') (Tr'0, Br'0, Pr'0)"
      unfolding selfloop_impl_nfoldli by (simp add: split_def)
    have EP: "selfloop_pass_impl D Tr'0 Br'0 Pr'0 St' boff Ta' Av'
              = nfoldli [0..<M] (\<lambda>_. True) ?abody (Tr'0, Br'0, Pr'0)"
      unfolding selfloop_pass_impl_def MD[symmetric] by (rule refl)
    have step: "nfoldli [0..<M] (\<lambda>_. True) (selfloop_body (St, Tr, Br, Pr, Av, Ta) St' boff Ta' Av') (Tr'0, Br'0, Pr'0)
                \<le> \<Down>?R (nfoldli [0..<M] (\<lambda>_. True) ?abody (Tr'0, Br'0, Pr'0))"
      apply (rule nfoldli_invar_refine[where I="\<lambda>_ _ _. True" and R="?R" and S=Id])
      subgoal by simp
      subgoal by (simp add: in_br_conv)
      subgoal by simp
      subgoal by simp
      subgoal by (simp add: pw_leof_iff)
      subgoal premises prems for l1i xi l2i l1 x l2 si s
      proof -
        from prems(1) have xi_eq: "xi = length l1i" and xilt': "length l1i < M"
          using CI.upt_split_elem by blast+
        from xi_eq xilt' have xi_lt: "xi < M" by simp
        from prems have xx: "x = xi" by simp
        obtain Tr' Br' Pr' where si: "si = (Tr', Br', Pr')" by (cases si)
        from prems have "(si, s) \<in> ?R" by simp
        then have s_eq: "s = si" and lenT: "length Tr' = length Tr'0"
          and lenB: "length Br' = length Br'0" and lenP: "length Pr' = length Pr'0"
          by (auto simp: in_br_conv si)
        show ?thesis
        proof (cases "xi \<in> Ta' \<or> xi \<in> Av'")
          case True
          with BND[rule_format, OF xi_lt] xi_lt
          show ?thesis unfolding si s_eq xx selfloop_body_def op_one_pfin_def
            by (auto simp: in_br_conv pw_le_iff refine_pw_simps Let_def lenT lenB lenP)
        next
          case False
          then show ?thesis unfolding si s_eq xx selfloop_body_def
            using xi_lt by (auto simp: in_br_conv pw_le_iff refine_pw_simps lenT lenB lenP)
        qed
      qed
      done
    have shrink: "\<Down>?R (nfoldli [0..<M] (\<lambda>_. True) ?abody (Tr'0, Br'0, Pr'0))
                  \<le> nfoldli [0..<M] (\<lambda>_. True) ?abody (Tr'0, Br'0, Pr'0)"
      using conc_fun_R_mono[OF Rsub] by (simp add: conc_Id)
    have core: "selfloop_impl (St, Tr, Br, Pr, Av, Ta) St' boff Ta' Av' Tr'0 Br'0 Pr'0
                \<le> selfloop_pass_impl D Tr'0 Br'0 Pr'0 St' boff Ta' Av'"
      unfolding si_eq EP using step shrink by (rule order_trans)
    from core selfloop_pass_impl_refine[OF LOC] show ?thesis by (rule order_trans)
  qed

  sepref_definition selfloop_ll is "uncurry7 (PR_CONST selfloop_impl)"
    :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>k
        *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>k
        *\<^sub>a (bitset_own_assn M)\<^sup>k *\<^sub>a (bitset_own_assn M)\<^sup>k
        *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>d *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>d
        *\<^sub>a (IICF_Array.array_assn pfin_real_intv_assn)\<^sup>d
        \<rightarrow>\<^sub>a (IICF_Array.array_assn size_assn \<times>\<^sub>a IICF_Array.array_assn size_assn
             \<times>\<^sub>a IICF_Array.array_assn pfin_real_intv_assn)"
    unfolding PR_CONST_def selfloop_impl_def selfloop_body_def conj.comm_neutral
    supply [elim] = less_trans_Suc[OF _ Modest_mdp_assn_boundsD(1), rotated]
      less_trans_Suc[OF _ Modest_mdp_assn_boundsD(2), rotated]
    apply (annot_snat_const "TYPE(size_T)")
    by sepref


  subsection \<open>Pass 4: copy / scatter --- LLVM synthesis\<close>

  text \<open>The innermost branch scatter for one leaving transition \<open>t\<close>, synthesised to LLVM ON ITS OWN so
    the outer copy sweep calls it as one pre-translated op (the \<open>trans_leaves\<close> sub-op trick). It copies
    the branches of \<open>t\<close> into the CSR block starting at cursor \<open>cbc0\<close>: each branch's MEC index into \<open>Br'\<close>
    and its probability into \<open>Pr'\<close>, returning the advanced cursor. Splitting this loop off keeps the
    outer \<open>copy_ll\<close> sepref from re-translating a 3-deep nest (states \<rightarrow> transitions \<rightarrow> branches), which
    blows up frame inference; \<open>copy_ll\<close> then translates only a 2-deep nest with two pre-synthesised
    inner calls (\<^const>\<open>trans_leaves_impl\<close> and this).\<close>
  definition copy_scatter_impl ::
    "modest_mdp \<Rightarrow> mec_map \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> real list \<Rightarrow> nat \<Rightarrow> (nat list \<times> real list \<times> nat) nres" where
    "copy_scatter_impl MDP D t Br' Pr' cbc0 = do {
       ASSERT (t < length (tTr MDP) - Suc 0);
       (_, Br', Pr', cbc) \<leftarrow> WHILET (\<lambda>(b, _, _, _). b < Tr_nth MDP (Suc t))
         (\<lambda>(b, Br', Pr', cbc). do {
            ASSERT (b < length (tBr MDP) \<and> b < length (tPr MDP) \<and> (\<exists>i<length D. Br_nth MDP b \<in> D ! i)
                    \<and> cbc < length Br' \<and> cbc < length Pr' \<and> cbc < length (tBr MDP));
            RETURN (Suc b, Br'[cbc := op_mec_index_of D (Br_nth MDP b)], Pr'[cbc := Pr_nth MDP b], cbc + 1)
         }) (Tr_nth MDP t, Br', Pr', cbc0);
       RETURN (Br', Pr', cbc) }"

  sepref_definition copy_scatter_ll is "uncurry5 copy_scatter_impl"
    :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a mec_map_assn\<^sup>k *\<^sub>a size_assn\<^sup>k
        *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>d *\<^sub>a (IICF_Array.array_assn pfin_real_intv_assn)\<^sup>d
        *\<^sub>a size_assn\<^sup>k
        \<rightarrow>\<^sub>a (IICF_Array.array_assn size_assn \<times>\<^sub>a IICF_Array.array_assn pfin_real_intv_assn \<times>\<^sub>a size_assn)"
    unfolding copy_scatter_impl_def Suc_eq_plus1[symmetric] conj.comm_neutral
    supply [elim] = less_trans_Suc[OF _ Modest_mdp_assn_boundsD(2), rotated]
      less_trans_Suc[OF _ Modest_mdp_assn_boundsD(1), rotated]
      less_trans_Suc[OF _ Modest_mdp_assn_boundsD(3), rotated]
      mec_map_eq_set_mem_preI
    apply sepref
    done

end

concrete_definition (in -) copy_scatter_ll' [llvm_code] is
  collapse_build_env.copy_scatter_ll_def

context collapse_build_env
begin

  interpretation disj_set_list_tuple_env N N ni ni
    apply unfold_locales using n_impl by auto

  \<comment> \<open>Register the branch scatter as a sepref op so \<open>copy_ll\<close> uses it as one pre-translated call.\<close>
  sepref_register copy_scatter_impl
  lemmas copy_scatter_hnr[sepref_fr_rules] =
    copy_scatter_ll.refine[unfolded copy_scatter_ll'.refine[OF collapse_build_env_loc]]

  text \<open>The full copy / scatter pass: a sweep (states \<rightarrow> leaving transitions) scattering each non-sink
    MEC's transitions into its CSR block, with per-MEC cursor arrays \<open>curT\<close>/\<open>curB\<close>. \<open>St'\<close>/\<open>boff\<close> are
    read-only (the self-loop pass needs them), so \<open>curT\<close>/\<open>curB\<close> are fresh copies (no array-copy op, so a
    copy loop). \<open>Tr'\<close>/\<open>Br'\<close> are \<open>nat\<close> arrays, \<open>Pr'\<close> a \<^const>\<open>pfin_real_intv_assn\<close> probability array. The
    \<open>trans_leaves\<close> test and the branch scatter are BOTH pre-synthesised ops (\<^const>\<open>trans_leaves_impl\<close>,
    \<^const>\<open>copy_scatter_impl\<close>), so only the state / transition sweep is translated here.\<close>
  text \<open>The per-state transition sweep of the copy pass, split off as its own op for the same two
    reasons as \<^const>\<open>copy_scatter_impl\<close>: it keeps the outer \<open>copy_ll\<close> \<open>sepref\<close> down to a single
    (state-level) loop with pre-synthesised inner calls, and --- crucially for the \<open>nres\<close> refinement ---
    it gives the loop a \<^emph>\<open>named, opaque\<close> head, so the bridge lemma can be applied with \<open>rule\<close>. Inlined,
    \<open>refine_vcg\<close>/\<open>clarsimp\<close> normalise the loop body (re-associating binds and distributing the \<open>if\<close>) and
    unification against the bridge lemma fails --- exactly the trap already hit with
    \<^const>\<open>count_inner_impl\<close>.\<close>
  definition copy_trans_impl ::
    "modest_mdp \<Rightarrow> mec_map \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> real list \<Rightarrow> nat list \<Rightarrow> nat list
      \<Rightarrow> (nat list \<times> nat list \<times> real list \<times> nat list \<times> nat list) nres" where
    "copy_trans_impl MDP D u Tr' Br' Pr' curT curB = do {
       ASSERT (u < N \<and> (\<exists>i<length D. u \<in> D ! i));
       let c = op_mec_index_of D u;
       ASSERT (c < M);
       (_, Tr', Br', Pr', curT, curB) \<leftarrow> WHILET (\<lambda>(t, _). t < St_nth_uid MDP u)
         (\<lambda>(t, Tr', Br', Pr', curT, curB). do {
            ASSERT (t < length (tTr MDP) - Suc 0);
            leaves \<leftarrow> trans_leaves_impl MDP D u t;
            (Tr', Br', Pr', curT, curB) \<leftarrow> (if leaves then do {
               ASSERT (c < length curT \<and> c < length curB \<and> curT ! c < length Tr' \<and> curT ! c + 1 < length Tr'
                       \<and> Tr_nth MDP t \<le> Tr_nth MDP (Suc t) \<and> curT ! c < length (tTr MDP));
               let Tr' = Tr'[curT ! c := curB ! c];
               (Br', Pr', cbc) \<leftarrow> copy_scatter_impl MDP D t Br' Pr' (curB ! c);
               ASSERT (c < length curB \<and> c < length curT \<and> curT ! c + 1 < length Tr');
               let curB = curB[c := cbc];
               let Tr' = Tr'[curT ! c + 1 := curB ! c];
               let curT = curT[c := curT ! c + 1];
               RETURN (Tr', Br', Pr', curT, curB)
            } else RETURN (Tr', Br', Pr', curT, curB));
            ASSERT (t < length (tTr MDP));
            RETURN (Suc t, Tr', Br', Pr', curT, curB)
         }) (St_nth_lid MDP u, Tr', Br', Pr', curT, curB);
       RETURN (Tr', Br', Pr', curT, curB) }"

  sepref_definition copy_trans_ll is "uncurry7 (PR_CONST copy_trans_impl)"
    :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a mec_map_assn\<^sup>k *\<^sub>a size_assn\<^sup>k
        *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>d *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>d
        *\<^sub>a (IICF_Array.array_assn pfin_real_intv_assn)\<^sup>d
        *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>d *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>d
        \<rightarrow>\<^sub>a (IICF_Array.array_assn size_assn \<times>\<^sub>a IICF_Array.array_assn size_assn
             \<times>\<^sub>a IICF_Array.array_assn pfin_real_intv_assn
             \<times>\<^sub>a IICF_Array.array_assn size_assn \<times>\<^sub>a IICF_Array.array_assn size_assn)"
    unfolding PR_CONST_def copy_trans_impl_def Suc_eq_plus1[symmetric] conj.comm_neutral
    supply [elim] = less_trans_Suc[OF _ Modest_mdp_assn_boundsD(2), rotated]
      less_trans_Suc[OF _ Modest_mdp_assn_boundsD(1), rotated]
      less_trans_Suc[OF _ Modest_mdp_assn_boundsD(3), rotated]
      mec_map_eq_set_mem_preI Suc_N_leq_max
    apply sepref
    done

end

concrete_definition (in -) copy_trans_ll' [llvm_code] is
  collapse_build_env.copy_trans_ll_def

context collapse_build_env
begin

  interpretation disj_set_list_tuple_env N N ni ni
    apply unfold_locales using n_impl by auto

  \<comment> \<open>Register the transition sweep as a sepref op so \<open>copy_ll\<close> uses it as one pre-translated call.\<close>
  sepref_register copy_trans_impl
  lemmas copy_trans_hnr[sepref_fr_rules] =
    copy_trans_ll.refine[unfolded copy_trans_ll'.refine[OF collapse_build_env_loc]]

  definition copy_ll_impl ::
    "modest_mdp \<Rightarrow> mec_map \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat
      \<Rightarrow> (nat list \<times> nat list \<times> real list) nres" where
    "copy_ll_impl MDP D St' boff Ta' Av' nT nB = do {
       ASSERT (nT < length (tTr MDP));
       let Tr' = replicate (nT + 1) 0;
       let Br' = replicate nB 0;
       let Pr' = replicate nB op_one_pfin;
       let curT = replicate (M + 1) 0;
       let curB = replicate (M + 1) 0;
       (_, curT, curB) \<leftarrow> WHILET (\<lambda>(i, _, _). i < M + 1) (\<lambda>(i, curT, curB). do {
          ASSERT (i < M + 1 \<and> i < length St' \<and> i < length boff \<and> i < length curT \<and> i < length curB);
          RETURN (i + 1, curT[i := St' ! i], curB[i := boff ! i])
       }) (0, curT, curB);
       (_, Tr') \<leftarrow> WHILET (\<lambda>(c, _). c < M) (\<lambda>(c, Tr'). do {
          ASSERT (c < M \<and> c < length St' \<and> c < length boff \<and> St' ! c < length Tr');
          RETURN (c + 1, Tr'[St' ! c := boff ! c])
       }) (0, Tr');
       (Tr', Br', Pr', curT, curB) \<leftarrow> nfoldli [0..<N] (\<lambda>_. True)
         (\<lambda>u (Tr', Br', Pr', curT, curB). do {
            ASSERT (u < N \<and> (\<exists>i<length D. u \<in> D ! i));
            let c = op_mec_index_of D u;
            ASSERT (c < M);
            if c \<in> Ta' \<or> c \<in> Av' then RETURN (Tr', Br', Pr', curT, curB)
            else copy_trans_impl MDP D u Tr' Br' Pr' curT curB
         }) (Tr', Br', Pr', curT, curB);
       RETURN (Tr', Br', Pr') }"

  sepref_definition copy_ll is "uncurry7 (PR_CONST copy_ll_impl)"
    :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a mec_map_assn\<^sup>k *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>k
        *\<^sub>a (IICF_Array.array_assn size_assn)\<^sup>k *\<^sub>a (bitset_own_assn M)\<^sup>k *\<^sub>a (bitset_own_assn M)\<^sup>k
        *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k
        \<rightarrow>\<^sub>a (IICF_Array.array_assn size_assn \<times>\<^sub>a IICF_Array.array_assn size_assn
             \<times>\<^sub>a IICF_Array.array_assn pfin_real_intv_assn)"
    unfolding PR_CONST_def copy_ll_impl_def nfoldli_upt_by_while Suc_eq_plus1[symmetric]
      conj.comm_neutral
    apply (rewrite array_fold_custom_replicate)
    apply (rewrite array_fold_custom_replicate)
    apply (rewrite array_fold_custom_replicate)
    apply (rewrite array_fold_custom_replicate)
    apply (rewrite array_fold_custom_replicate)
    supply [elim] = less_trans_Suc[OF _ Modest_mdp_assn_boundsD(2), rotated]
      less_trans_Suc[OF _ Modest_mdp_assn_boundsD(1), rotated]
      less_trans_Suc[OF _ Modest_mdp_assn_boundsD(3), rotated]
      le_less_trans[OF _ Modest_mdp_assn_boundsD(1), rotated]
      mec_map_eq_set_mem_preI Suc_N_leq_max
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done


end

text \<open>Extract the synthesised LLVM implementation as a global \<open>llvm_code\<close> constant (abstracting the
  locale parameters), ready for \<open>export_llvm\<close> in a downstream Code theory.\<close>
concrete_definition (in -) count_pass_ll' [llvm_code] is collapse_build_env.count_pass_ll_def
concrete_definition (in -) copy_ll' [llvm_code] is collapse_build_env.copy_ll_def
concrete_definition (in -) empty_ec_ll' [llvm_code] is collapse_build_env.empty_ec_ll_def
concrete_definition (in -) offset_ll' [llvm_code] is collapse_build_env.offset_ll_def
concrete_definition (in -) selfloop_ll' [llvm_code] is collapse_build_env.selfloop_ll_def


section \<open>Assertions for the builder's interface\<close>

text \<open>The built MDP's raw assertion. Unlike the \<^emph>\<open>input\<close> MDP --- whose CSR parts are caller-owned
  slices (\<^const>\<open>node_array_slice_assn\<close> etc. inside \<^const>\<open>modest_init_mdp_env_defs.Modest_mdp_assn_aux\<close>)
  --- the builder allocates its own arrays, so the built state space refines at
  \<^const>\<open>IICF_Array.array_assn\<close>; its two sets are bitsets over the MEC count \<^term>\<open>M\<close>, not \<^term>\<open>N\<close>.\<close>
definition "built_mdp_assn M =
  IICF_Array.array_assn size_assn \<times>\<^sub>a IICF_Array.array_assn size_assn
  \<times>\<^sub>a IICF_Array.array_assn size_assn \<times>\<^sub>a IICF_Array.array_assn pfin_real_intv_assn
  \<times>\<^sub>a bitset_own_assn M \<times>\<^sub>a bitset_own_assn M"

text \<open>The builder's \<^emph>\<open>input\<close> assertion: a Modest MDP together with its MEC decomposition, composed
  with \<^const>\<open>modest_collapse_rel\<close> --- so it abstracts to the collapsed MDP \<^term>\<open>(M_mec \<M>, D)\<close>.
  The pair is one \<open>sepref\<close> argument, which is what makes the \<open>FCOMP\<close> against a relation on pairs
  normalise (\<^const>\<open>hrp_comp\<close> of a two-argument product with a pair relation does not).\<close>
definition "Modest_collapse_assn N =
  hr_comp (modest_init_mdp_env_defs.Modest_mdp_assn_aux N
           \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N)
          (modest_collapse_rel N)"

text \<open>The builder's \<^emph>\<open>output\<close> assertion, the counterpart of \<^const>\<open>modest_build_rel\<close>: the preserved
  input MDP, the freshly built state space, and the decomposition. It abstracts to
  \<^term>\<open>\<M>_\<alpha>_sup' (length D) built\<close> --- a valid \<open>Sup\<close> interval-iteration input --- and by
  \<open>build_statespace_hnr\<close> that value is the indexed max reduction \<^term>\<open>op_to_index (\<M>c, D)\<close>.\<close>
definition "Modest_build_assn N M =
  hr_comp ((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn M)
           \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N)
          (modest_build_rel N)"

text \<open>The builder as \<^emph>\<open>one\<close> abstract operation, so that the collapsed \<open>hnr\<close> rule has a proper
  abstract head and can be registered for callers. The two scratch bitsets carry no abstract
  content --- they must be empty on entry, and come back as the built target / avoid sets --- so
  abstractly the builder is exactly \<^const>\<open>op_to_index\<close>.\<close>
definition op_build_index ::
  "(nat mdpc mdptc \<times> nat set list) \<Rightarrow> nat mdptc nres" where
  "op_build_index x = RETURN (op_to_index x)"

sepref_register op_build_index


context collapse_build_env
begin

  lemma copy_scatter_refine:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    assumes TB: "t < length Tr - Suc 0"
    assumes FIT: "cbc0 + (Tr ! Suc t - Tr ! t) \<le> length BR"
    assumes LBP: "length PR = length BR"
    assumes BM: "length BR \<le> length Br"
    shows "copy_scatter_impl (St, Tr, Br, Pr, Av, Ta) D t BR PR cbc0
           \<le> FOREACH (sn_intv (sorted_intvs Tr ! t))
              (\<lambda>b (Bx, Px, cbc).
                 RETURN (Bx[cbc := op_mec_index_of D (Br ! b)], Px[cbc := Pr ! b], cbc + 1))
              (BR, PR, cbc0)"
  proof -
    interpret CI: modest_collapse_invar N St Tr Br Pr Av Ta D by (rule LOC)
    define fP :: "nat \<Rightarrow> nat list \<times> real list \<times> nat \<Rightarrow> (nat list \<times> real list \<times> nat) nres" where
      "fP = (\<lambda>b (Bx, Px, cbc). do {
          ASSERT (b < length Br \<and> b < length Pr \<and> (\<exists>i<length D. Br ! b \<in> D ! i)
                  \<and> cbc < length Bx \<and> cbc < length Px \<and> cbc < length Br);
          RETURN (Bx[cbc := op_mec_index_of D (Br ! b)], Px[cbc := Pr ! b], cbc + 1) })"
    define f :: "nat \<Rightarrow> nat list \<times> real list \<times> nat \<Rightarrow> (nat list \<times> real list \<times> nat) nres" where
      "f = (\<lambda>b (Bx, Px, cbc).
          RETURN (Bx[cbc := op_mec_index_of D (Br ! b)], Px[cbc := Pr ! b], cbc + 1))"
    have S1: "copy_scatter_impl (St, Tr, Br, Pr, Av, Ta) D t BR PR cbc0
        \<le> nfoldli [Tr ! t..<Tr ! Suc t] (\<lambda>_. True) fP (BR, PR, cbc0)"
      unfolding nfoldli_upt_by_while copy_scatter_impl_def fP_def
      apply (simp add: TB Tr_nth_alt Br_nth_alt Pr_nth_alt split_def prod.collapse)
      apply refine_mono
      apply (auto simp: pw_le_iff refine_pw_simps)
      done
    have SucT: "Suc t < length Tr" using TB by (cases "length Tr") auto
    have hB: "Tr ! Suc t \<le> length Br"
      using CI.Tr_dom nth_mem[OF SucT] by auto
    have S2: "nfoldli [Tr ! t..<Tr ! Suc t] (\<lambda>_. True) fP (BR, PR, cbc0)
        \<le> nfoldli [Tr ! t..<Tr ! Suc t] (\<lambda>_. True) f (BR, PR, cbc0)"
      apply (rule refine_IdD)
      apply (rule nfoldli_invar_refine[where S = Id and R = Id
              and I = "\<lambda>l1i l2i (Bx, Px, cbc). cbc = cbc0 + length l1i
                        \<and> length Bx = length BR \<and> length Px = length PR"])
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by (auto simp: fP_def pw_leof_iff refine_pw_simps split: prod.splits)
      subgoal premises prems for l1i xi l2i l1 x l2 si s
      proof -
        obtain Bx Px cbc where SI: "si = (Bx, Px, cbc)" by (cases si) auto
        from prems have xx: "x = xi" and ss: "s = si" by simp_all
        from prems have LI: "[Tr ! t..<Tr ! Suc t] = l1i @ xi # l2i" by simp
        from prems SI have Icbc: "cbc = cbc0 + length l1i"
          and IlB: "length Bx = length BR" and IlP: "length Px = length PR" by auto
        have LEN: "length l1i < Tr ! Suc t - Tr ! t"
          using arg_cong[where f = length, OF LI] by simp
        have XIlt: "Tr ! t + length l1i < Tr ! Suc t" using LEN by simp
        have XI: "xi = Tr ! t + length l1i"
        proof -
          have "xi = (l1i @ xi # l2i) ! length l1i" by (simp add: nth_append)
          also have "\<dots> = [Tr ! t..<Tr ! Suc t] ! length l1i" using LI by simp
          also have "\<dots> = Tr ! t + length l1i" using XIlt by simp
          finally show ?thesis .
        qed
        have XIBr: "xi < length Br" using XI XIlt hB by simp
        have XIPr: "xi < length Pr" using XIBr by (simp add: CI.Len_Pr_Br)
        have MEC: "\<exists>i<length D. Br ! xi \<in> D ! i"
          using CI.mec_of_unique[of "Br ! xi"] CI.Br_dom XIBr nth_mem by fastforce
        have CBC: "cbc < length Bx" using Icbc LEN FIT IlB by simp
        have CBCP: "cbc < length Px" using CBC IlB IlP LBP by simp
        have CBCBr: "cbc < length Br" using Icbc LEN FIT BM by simp
        show ?thesis
          unfolding SI ss xx fP_def f_def
          using XIBr XIPr MEC CBC CBCP CBCBr
          by (auto simp: conc_Id pw_le_iff refine_pw_simps)
      qed
      done
    have S3: "nfoldli [Tr ! t..<Tr ! Suc t] (\<lambda>_. True) f (BR, PR, cbc0)
        \<le> FOREACH (sn_intv (sorted_intvs Tr ! t)) f (BR, PR, cbc0)"
      unfolding sn_intv_sorted_intvs[OF CI.sorted_Tr TB]
      apply (rule refine_IdD)
      apply (rule LFO_refine[where A = Id and R = Id])
      subgoal by (rule upt_list_set_rel_Id[OF IdI IdI])
      subgoal by (simp add: conc_Id)
      subgoal by simp
      done
    from S1 S2 S3 have "copy_scatter_impl (St, Tr, Br, Pr, Av, Ta) D t BR PR cbc0
        \<le> FOREACH (sn_intv (sorted_intvs Tr ! t)) f (BR, PR, cbc0)"
      by (blast intro: order_trans)
    thus ?thesis unfolding f_def .
  qed

  text \<open>Step-2 bridge for the per-state transition sweep: \<^const>\<open>copy_trans_impl\<close>'s \<open>WHILE\<close> refines the
    transition \<^const>\<open>FOREACH\<close> of \<open>copy_pass_impl\<close>. Unlike the branch scatter this one needs no
    positional invariant: the abstract side now carries the cursor \<open>ASSERT\<close>, so a per-element \<open>FREF\<close>
    suffices --- on \<open>\<not>P\<close> the abstract \<open>ASSERT\<close> is \<^const>\<open>FAIL\<close> (hence above anything), and on \<open>P\<close> it
    hands us exactly the facts needed to discharge the impl's own asserts and to feed
    \<open>copy_scatter_refine\<close>'s room/length preconditions. Template: \<open>count_inner_refine\<close>.\<close>
  lemma copy_trans_refine:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    assumes MD: "M = length D"
    assumes UB: "u < N"
    assumes C: "c = op_mec_index_of D u"
    shows "copy_trans_impl (St, Tr, Br, Pr, Av, Ta) D u TR BR PR cT cB
           \<le> FOREACH (sn_intv (sorted_intvs St ! u))
              (\<lambda>t (Tr', Br', Pr', curT, curB).
                 if modest_collapse_invar.trans_leaves Tr Br D c t then do {
                   ASSERT (c < length curT \<and> c < length curB
                           \<and> curT ! c < length Tr' \<and> curT ! c + 1 < length Tr'
                           \<and> curT ! c < length Tr
                           \<and> curB ! c + cnt (sorted_intvs Tr ! t) \<le> length Br'
                           \<and> length Pr' = length Br' \<and> length Br' \<le> length Br);
                   let Tr' = Tr'[curT ! c := curB ! c];
                   (Br', Pr', cbc) \<leftarrow> FOREACH (sn_intv (sorted_intvs Tr ! t))
                      (\<lambda>b (Br', Pr', cbc).
                         RETURN (Br'[cbc := op_mec_index_of D (Br ! b)], Pr'[cbc := Pr ! b], cbc + 1))
                      (Br', Pr', curB ! c);
                   let curB = curB[c := cbc];
                   let Tr' = Tr'[curT ! c + 1 := curB ! c];
                   RETURN (Tr', Br', Pr', curT[c := curT ! c + 1], curB)
                 } else RETURN (Tr', Br', Pr', curT, curB))
              (TR, BR, PR, cT, cB)"
  proof -
    interpret CI: modest_collapse_invar N St Tr Br Pr Av Ta D by (rule LOC)
    have MEC: "\<exists>i<length D. u \<in> D ! i" using CI.mec_of_unique[OF UB] by blast
    have cM: "c < M" using C MD CI.mec_lt_lenD[OF UB] by simp
    have SucU: "St ! Suc u < length Tr"
      using CI.St_in_bound[OF UB] uid_sorted_intvs[OF CI.sorted_St, of u] UB by (simp add: CI.N_DEF)
    have snSt: "sn_intv (sorted_intvs St ! u) = {St ! u..<St ! Suc u}"
      using sn_intv_sorted_intvs[OF CI.sorted_St] UB by (simp add: CI.N_DEF)
    \<comment> \<open>the impl's loop body (\<open>g\<close>) and the abstract one (\<open>gA\<close>), with the loop plumbing factored out.
      \<open>g\<close> keeps the impl's trailing \<open>ASSERT (t < length Tr)\<close>, so that in S1 the two loop bodies differ
      only by the \<^emph>\<open>extra\<close> \<open>ASSERT (t < St ! Suc u)\<close> of the \<^const>\<open>nfoldli\<close> normal form, which only
      makes the right-hand side larger.\<close>
    define g where "g = (\<lambda>t (Tr', Br', Pr', curT, curB). do {
         ASSERT (t < length Tr - Suc 0);
         leaves \<leftarrow> trans_leaves_impl (St, Tr, Br, Pr, Av, Ta) D u t;
         (Tr', Br', Pr', curT, curB) \<leftarrow> (if leaves then do {
            ASSERT (c < length curT \<and> c < length curB \<and> curT ! c < length Tr'
                    \<and> curT ! c + 1 < length Tr' \<and> Tr ! t \<le> Tr ! Suc t
                    \<and> curT ! c < length Tr);
            let Tr' = Tr'[curT ! c := curB ! c];
            (Br', Pr', cbc) \<leftarrow> copy_scatter_impl (St, Tr, Br, Pr, Av, Ta) D t Br' Pr' (curB ! c);
            ASSERT (c < length curB \<and> c < length curT \<and> curT ! c + 1 < length Tr');
            let curB = curB[c := cbc];
            let Tr' = Tr'[curT ! c + 1 := curB ! c];
            let curT = curT[c := curT ! c + 1];
            RETURN (Tr', Br', Pr', curT, curB)
         } else RETURN (Tr', Br', Pr', curT, curB));
         ASSERT (t < length Tr);
         RETURN (Tr', Br', Pr', curT, curB) })"
    define gA where "gA = (\<lambda>t (Tr', Br', Pr', curT, curB).
         if modest_collapse_invar.trans_leaves Tr Br D c t then do {
           ASSERT (c < length curT \<and> c < length curB
                   \<and> curT ! c < length Tr' \<and> curT ! c + 1 < length Tr'
                   \<and> curT ! c < length Tr
                   \<and> curB ! c + cnt (sorted_intvs Tr ! t) \<le> length Br'
                   \<and> length Pr' = length Br' \<and> length Br' \<le> length Br);
           let Tr' = Tr'[curT ! c := curB ! c];
           (Br', Pr', cbc) \<leftarrow> FOREACH (sn_intv (sorted_intvs Tr ! t))
              (\<lambda>b (Br', Pr', cbc).
                 RETURN (Br'[cbc := op_mec_index_of D (Br ! b)], Pr'[cbc := Pr ! b], cbc + 1))
              (Br', Pr', curB ! c);
           let curB = curB[c := cbc];
           let Tr' = Tr'[curT ! c + 1 := curB ! c];
           RETURN (Tr', Br', Pr', curT[c := curT ! c + 1], curB)
         } else RETURN (Tr', Br', Pr', curT, curB))"
    have S1: "copy_trans_impl (St, Tr, Br, Pr, Av, Ta) D u TR BR PR cT cB
        \<le> nfoldli [St ! u..<St ! Suc u] (\<lambda>_. True) g (TR, BR, PR, cT, cB)"
      unfolding nfoldli_upt_by_while copy_trans_impl_def g_def
        St_nth_uid_alt St_nth_lid_alt Tr_nth_alt
      apply (simp add: UB MEC cM C[symmetric] Let_def)
      apply refine_mono
      subgoal for x a b
        apply (cases b)
        apply (simp only: prod.case nres_monad_laws)
        apply refine_mono
        apply (auto simp: pw_le_iff refine_pw_simps split: prod.splits)
        done
      done
    have S2: "nfoldli [St ! u..<St ! Suc u] (\<lambda>_. True) g (TR, BR, PR, cT, cB)
        \<le> nfoldli [St ! u..<St ! Suc u] (\<lambda>_. True) gA (TR, BR, PR, cT, cB)"
      apply (rule refine_IdD)
      apply (rule nfoldli_invar_refine[where S = Id and R = Id and I = "\<lambda>_ _ _. True"])
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by (simp add: pw_leof_iff)
      subgoal premises prems for l1i xi l2i l1 x l2 si s
      proof -
        from prems have xx: "x = xi" and ss: "s = si" by simp_all
        from prems have LI: "[St ! u..<St ! Suc u] = l1i @ xi # l2i" by simp
        have XImem: "xi \<in> {St ! u..<St ! Suc u}"
          using arg_cong[where f = set, OF LI] by auto
        have TB: "xi < length Tr - Suc 0" using XImem SucU by auto
        have TrLe: "Tr ! xi \<le> Tr ! Suc xi"
          using TB CI.sorted_Tr by (simp add: sorted_nth_mono)
        have CNT: "cnt (sorted_intvs Tr ! xi) = Tr ! Suc xi - Tr ! xi"
          by (rule cnt_sorted_intvs[OF CI.sorted_Tr TB])
        \<comment> \<open>replace the impl's leaves test by the abstract predicate\<close>
        have TL: "trans_leaves_impl (St, Tr, Br, Pr, Av, Ta) D u xi \<bind> h
            \<le> h (modest_collapse_invar.trans_leaves Tr Br D c xi)" for h
        proof -
          have "trans_leaves_impl (St, Tr, Br, Pr, Av, Ta) D u xi \<bind> h
              \<le> RETURN (modest_collapse_invar.trans_leaves Tr Br D (op_mec_index_of D u) xi) \<bind> h"
            by (rule bind_mono(1)[OF trans_leaves_impl_refine[OF LOC UB TB]]) auto
          thus ?thesis using C by simp
        qed
        obtain TR0 BR0 PR0 cT0 cB0 where SI: "si = (TR0, BR0, PR0, cT0, cB0)"
          by (cases si) auto
        show ?thesis
          unfolding ss xx SI g_def gA_def
          apply (simp only: prod.case)
          apply (simp add: TB)
          apply (intro conjI impI)
          subgoal   \<comment> \<open>the transition leaves \<open>c\<close>: bridge the scatter\<close>
            apply (rule order_trans[OF TL])
            apply (simp only: if_True)
            apply (rule le_ASSERTI_pres)
            apply (elim conjE)
            apply (simp add: TrLe)
            \<comment> \<open>\<open>simp\<close> has normalised \<open>cbc + 1\<close> to \<open>Suc cbc\<close>, so normalise the bridge lemma the same way\<close>
            apply (rule bind_mono(1)[OF copy_scatter_refine[OF LOC TB,
                    unfolded Suc_eq_plus1[symmetric]]])
            subgoal using CNT by simp                              \<comment> \<open>FIT: the branch block has room\<close>
            subgoal by simp                                        \<comment> \<open>LBP\<close>
            subgoal by simp                                        \<comment> \<open>BM\<close>
            subgoal using TB by (auto simp: pw_le_iff refine_pw_simps split: prod.splits)
            done
          subgoal   \<comment> \<open>the transition stays inside \<open>c\<close>: both sides leave the state alone\<close>
            apply (rule order_trans[OF TL])
            using TB by (simp add: pw_le_iff refine_pw_simps)
          done
      qed
      done
    have S3: "nfoldli [St ! u..<St ! Suc u] (\<lambda>_. True) gA (TR, BR, PR, cT, cB)
        \<le> FOREACH (sn_intv (sorted_intvs St ! u)) gA (TR, BR, PR, cT, cB)"
      unfolding snSt
      apply (rule refine_IdD)
      apply (rule LFO_refine[where A = Id and R = Id])
      subgoal by (rule upt_list_set_rel_Id[OF IdI IdI])
      subgoal by (simp add: conc_Id)
      subgoal by simp
      done
    from S1 S2 S3 have "copy_trans_impl (St, Tr, Br, Pr, Av, Ta) D u TR BR PR cT cB
        \<le> FOREACH (sn_intv (sorted_intvs St ! u)) gA (TR, BR, PR, cT, cB)"
      by (blast intro: order_trans)
    thus ?thesis unfolding gA_def .
  qed

  text \<open>The impl copies \<open>St'\<close>/\<open>boff\<close> into \<^emph>\<open>fresh\<close> \<open>curT\<close>/\<open>curB\<close> arrays (the self-loop pass still needs
    the originals, and there is no array-copy op), where the abstract pass simply aliases them with
    \<open>let curT = St'\<close>. That is the one place where the two are operationally different rather than merely
    differently-looped, so the copy loop has to be shown to reproduce its sources exactly.\<close>
  lemma copy_init_loop:
    assumes LA: "length A = M + 1" and LB: "length B = M + 1"
    shows "WHILET (\<lambda>(i, _, _). i < M + 1)
             (\<lambda>(i, cA, cB). do {
                ASSERT (i < M + 1 \<and> i < length A \<and> i < length B \<and> i < length cA \<and> i < length cB);
                RETURN (i + 1, cA[i := A ! i], cB[i := B ! i]) })
             (0, replicate (M + 1) 0, replicate (M + 1) 0)
           \<le> SPEC (\<lambda>(i, cA, cB). i = M + 1 \<and> cA = A \<and> cB = B)"
    apply (refine_vcg WHILET_rule[where ?I = "\<lambda>(i, cA, cB). i \<le> M + 1
                \<and> length cA = M + 1 \<and> length cB = M + 1
                \<and> (\<forall>j<i. cA ! j = A ! j \<and> cB ! j = B ! j)"
              and ?R = "Wellfounded.measure (\<lambda>(i, _). M + 1 - i)"])
    \<comment> \<open>\<open>refine_vcg\<close> splits the conjunctive invariant and every \<open>ASSERT\<close> conjunct into its own goal;
      they are all either vacuous, a length fact, or the \<open>j = i\<close>/\<open>j < i\<close> case of the pointwise update.\<close>
    apply (auto simp: LA LB M_Suc_upper nth_list_update less_Suc_eq intro!: nth_equalityI)
    done

  text \<open>Determinised form: the loop's result is exactly \<open>(M + 1, A, B)\<close>. Phrasing it as a
    \<^const>\<open>RETURN\<close> makes composing it with a continuation a first-order step (\<open>bind_mono\<close> plus
    \<open>nres_monad1\<close>), which avoids the higher-order match that plain \<open>order_trans\<close> could not find.\<close>
  lemma copy_init_loop_RETURN:
    assumes LA: "length A = M + 1" and LB: "length B = M + 1"
    shows "WHILET (\<lambda>(i, _, _). i < M + 1)
             (\<lambda>(i, cA, cB). do {
                ASSERT (i < M + 1 \<and> i < length A \<and> i < length B \<and> i < length cA \<and> i < length cB);
                RETURN (i + 1, cA[i := A ! i], cB[i := B ! i]) })
             (0, replicate (M + 1) 0, replicate (M + 1) 0)
           \<le> RETURN (M + 1, A, B)"
    using copy_init_loop[OF LA LB] by (auto simp: pw_le_iff refine_pw_simps)

  text \<open>The \<open>Tr'\<close>-prefill: the impl's WHILE refines the abstract pass's \<^const>\<open>nfoldli\<close>. Same two-step
    shape as the other bridges --- reach the \<^const>\<open>nfoldli\<close> normal form, then discharge the impl's
    array-bound asserts against the assert-free abstract loop using a state invariant (here just
    \<open>length Tr' = nT + 1\<close>, which is what \<open>St' ! c < length Tr'\<close> needs).\<close>
  lemma copy_prefill_refine:
    assumes MD: "M = length D"
    assumes lenSt: "length St' = M + 1" and lenboff: "length boff = M + 1"
    assumes StTr: "\<And>c. c < M \<Longrightarrow> St' ! c < nT + 1"
    shows "do { (_, Tr') \<leftarrow> WHILET (\<lambda>(c, _). c < M)
                   (\<lambda>(c, Tr'). do {
                      ASSERT (c < M \<and> c < length St' \<and> c < length boff \<and> St' ! c < length Tr');
                      RETURN (c + 1, Tr'[St' ! c := boff ! c]) })
                   (0, replicate (nT + 1) 0);
                RETURN Tr' }
           \<le> nfoldli [0..<length D] (\<lambda>_. True) (\<lambda>c Tr'. RETURN (Tr'[St' ! c := boff ! c]))
                (replicate (nT + 1) 0)"
  proof -
    define gP where "gP = (\<lambda>c Tr'. do {
         ASSERT (c < M \<and> c < length St' \<and> c < length boff \<and> St' ! c < length Tr');
         RETURN (Tr'[St' ! c := boff ! c]) })"
    have S1: "do { (_, Tr') \<leftarrow> WHILET (\<lambda>(c, _). c < M)
                     (\<lambda>(c, Tr'). do {
                        ASSERT (c < M \<and> c < length St' \<and> c < length boff \<and> St' ! c < length Tr');
                        RETURN (c + 1, Tr'[St' ! c := boff ! c]) })
                     (0, replicate (nT + 1) 0);
                  RETURN Tr' }
        \<le> nfoldli [0..<M] (\<lambda>_. True) gP (replicate (nT + 1) 0)"
      \<comment> \<open>\<open>conj.comm_neutral\<close> is essential: the normal form's condition is \<open>i < M \<and> True\<close>, which does
        not match the impl's \<open>c < M\<close>, and then \<open>refine_mono\<close> cannot descend into the loop at all\<close>
      unfolding nfoldli_upt_by_while gP_def conj.comm_neutral
      apply refine_mono
      apply (auto simp: pw_le_iff refine_pw_simps split: prod.splits)
      done
    have S2: "nfoldli [0..<M] (\<lambda>_. True) gP (replicate (nT + 1) 0)
        \<le> nfoldli [0..<M] (\<lambda>_. True) (\<lambda>c Tr'. RETURN (Tr'[St' ! c := boff ! c]))
             (replicate (nT + 1) 0)"
      apply (rule refine_IdD)
      apply (rule nfoldli_invar_refine[where S = Id and R = Id
              and I = "\<lambda>_ _ Tr'. length Tr' = nT + 1"])
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by (auto simp: gP_def pw_leof_iff refine_pw_simps)
      subgoal premises prems for l1i xi l2i l1 x l2 si s
      proof -
        from prems have xx: "x = xi" and ss: "s = si" by simp_all
        from prems have LI: "[0..<M] = l1i @ xi # l2i" by simp
        have XI: "xi < M" using arg_cong[where f = set, OF LI] by auto
        from prems have LEN: "length si = nT + 1" by simp
        show ?thesis
          unfolding ss xx gP_def
          using XI LEN lenSt lenboff StTr[OF XI] M_incr_max[OF XI]
          by (auto simp: conc_Id pw_le_iff refine_pw_simps)
      qed
      done
    from S1 S2 show ?thesis unfolding MD[symmetric] by (rule order_trans)
  qed

  text \<open>Bind form, matching the shape the assembly actually meets: the impl's prefill loop returns a
    \<open>(counter, Tr')\<close> pair and its continuation destructures it, whereas the abstract loop returns \<open>Tr'\<close>
    directly. Stating the step this way keeps the assembly first-order.\<close>
  lemma copy_prefill_refine_bind:
    assumes MD: "M = length D"
    assumes lenSt: "length St' = M + 1" and lenboff: "length boff = M + 1"
    assumes StTr: "\<And>c. c < M \<Longrightarrow> St' ! c < nT + 1"
    shows "WHILET (\<lambda>(c, _). c < M)
                   (\<lambda>(c, Tr'). do {
                      ASSERT (c < M \<and> c < length St' \<and> c < length boff \<and> St' ! c < length Tr');
                      RETURN (c + 1, Tr'[St' ! c := boff ! c]) })
                   (0, replicate (nT + 1) 0)
             \<bind> (\<lambda>(_, Tr'). k Tr')
           \<le> nfoldli [0..<length D] (\<lambda>_. True) (\<lambda>c Tr'. RETURN (Tr'[St' ! c := boff ! c]))
                (replicate (nT + 1) 0) \<bind> k"
  proof -
    have "WHILET (\<lambda>(c, _). c < M)
                   (\<lambda>(c, Tr'). do {
                      ASSERT (c < M \<and> c < length St' \<and> c < length boff \<and> St' ! c < length Tr');
                      RETURN (c + 1, Tr'[St' ! c := boff ! c]) })
                   (0, replicate (nT + 1) 0)
             \<bind> (\<lambda>(_, Tr'). k Tr')
        = (do { (_, Tr') \<leftarrow> WHILET (\<lambda>(c, _). c < M)
                   (\<lambda>(c, Tr'). do {
                      ASSERT (c < M \<and> c < length St' \<and> c < length boff \<and> St' ! c < length Tr');
                      RETURN (c + 1, Tr'[St' ! c := boff ! c]) })
                   (0, replicate (nT + 1) 0);
                RETURN Tr' }) \<bind> k"
      by (simp add: nres_monad1 nres_monad2 split_def)
    also have "\<dots> \<le> nfoldli [0..<length D] (\<lambda>_. True)
                        (\<lambda>c Tr'. RETURN (Tr'[St' ! c := boff ! c])) (replicate (nT + 1) 0) \<bind> k"
      by (rule bind_mono(1)[OF copy_prefill_refine[OF MD lenSt lenboff StTr] order_refl])
    finally show ?thesis .
  qed

  text \<open>The state sweep. Both sides are already \<^const>\<open>nfoldli\<close> over \<^term>\<open>[0..<N]\<close>, so only the bodies
    need relating, and no invariant is required: everything the impl's asserts need comes from list
    membership (\<open>u < N\<close>) plus the locale (\<open>mec_of_unique\<close>, \<open>mec_lt_lenD\<close>). The transition loop itself is
    handed off to \<open>copy_trans_refine\<close>.\<close>
  lemma copy_sweep_refine:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    assumes MD: "M = length D"
    shows "nfoldli [0..<N] (\<lambda>_. True)
             (\<lambda>u (Tr', Br', Pr', curT, curB). do {
                ASSERT (u < N \<and> (\<exists>i<length D. u \<in> D ! i));
                let c = op_mec_index_of D u;
                ASSERT (c < M);
                if c \<in> Ta' \<or> c \<in> Av' then RETURN (Tr', Br', Pr', curT, curB)
                else copy_trans_impl (St, Tr, Br, Pr, Av, Ta) D u Tr' Br' Pr' curT curB })
             \<sigma>
           \<le> nfoldli [0..<N] (\<lambda>_. True)
             (\<lambda>u (Tr', Br', Pr', curT, curB).
                let c = op_mec_index_of D u in
                if c \<in> Ta' \<or> c \<in> Av' then RETURN (Tr', Br', Pr', curT, curB)
                else FOREACH (sn_intv (sorted_intvs St ! u))
                   (\<lambda>t (Tr', Br', Pr', curT, curB).
                      if modest_collapse_invar.trans_leaves Tr Br D c t then do {
                        ASSERT (c < length curT \<and> c < length curB
                                \<and> curT ! c < length Tr' \<and> curT ! c + 1 < length Tr'
                                \<and> curT ! c < length Tr
                                \<and> curB ! c + cnt (sorted_intvs Tr ! t) \<le> length Br'
                                \<and> length Pr' = length Br' \<and> length Br' \<le> length Br);
                        let Tr' = Tr'[curT ! c := curB ! c];
                        (Br', Pr', cbc) \<leftarrow> FOREACH (sn_intv (sorted_intvs Tr ! t))
                           (\<lambda>b (Br', Pr', cbc).
                              RETURN (Br'[cbc := op_mec_index_of D (Br ! b)], Pr'[cbc := Pr ! b],
                                      cbc + 1))
                           (Br', Pr', curB ! c);
                        let curB = curB[c := cbc];
                        let Tr' = Tr'[curT ! c + 1 := curB ! c];
                        RETURN (Tr', Br', Pr', curT[c := curT ! c + 1], curB)
                      } else RETURN (Tr', Br', Pr', curT, curB))
                   (Tr', Br', Pr', curT, curB))
             \<sigma>"
  proof -
    interpret CI: modest_collapse_invar N St Tr Br Pr Av Ta D by (rule LOC)
    show ?thesis
      apply (rule refine_IdD)
      apply (rule nfoldli_invar_refine[where S = Id and R = Id and I = "\<lambda>_ _ _. True"])
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by (simp add: pw_leof_iff)
      subgoal premises prems for l1i xi l2i l1 x l2 si s
      proof -
        from prems have xx: "x = xi" and ss: "s = si" by simp_all
        from prems have LI: "[0..<N] = l1i @ xi # l2i" by simp
        have UB: "xi < N" using arg_cong[where f = set, OF LI] by auto
        have MEC: "\<exists>i<length D. xi \<in> D ! i" using CI.mec_of_unique[OF UB] by blast
        have cM: "op_mec_index_of D xi < M" using MD CI.mec_lt_lenD[OF UB] by simp
        show ?thesis
          unfolding ss xx
          apply (cases si)
          apply (simp only: prod.case Let_def)
          apply (simp add: UB MEC cM)
          apply (intro conjI impI)
          \<comment> \<open>the goal's \<open>let\<close>s were unfolded by the \<open>simp\<close> above, so unfold them in the rule too\<close>
          subgoal by (simp add: copy_trans_refine[OF LOC MD UB refl, unfolded Let_def])
          done
      qed
      done
  qed

  lemma RT5: "(\<lambda>(Tr', Br', Pr', curT, curB). RETURN (Tr', Br', Pr', curT, curB)) = RETURN"
    by (auto simp: fun_eq_iff split: prod.splits)

  \<comment> \<open>applied form: after \<open>nres_monad3\<close> re-associates, the tuple-\<open>RETURN\<close> occurs applied to a
    variable, where the function-level equation above no longer matches\<close>
  lemma RT5': "(case \<sigma> of (Tr', Br', Pr', curT, curB) \<Rightarrow> RETURN (Tr', Br', Pr', curT, curB))
                = RETURN \<sigma>"
    by (simp split: prod.splits)

  text \<open>Phase-B goal: the \<^emph>\<open>synthesised\<close> \<^const>\<open>copy_ll_impl\<close> refines the step-3
    \<^const>\<open>copy_pass_impl\<close> (projected to the three built arrays --- the impl drops the spent cursors).
    Composing with \<open>copy_pass_impl_refine\<close> closes the last gap in the copy chain. The preconditions are
    exactly the offset-pass postconditions that \<open>copy_pass_correct\<close> already assumes, so they discharge
    at the call site.\<close>
  lemma copy_ll_impl_refine:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    assumes MD: "M = length D"
    assumes lenSt: "length St' = M + 1" and lenboff: "length boff = M + 1"
    assumes StTr: "\<And>c. c < M \<Longrightarrow> St' ! c < nT + 1"
    assumes nTmax: "nT < length Tr"
    shows "copy_ll_impl (St, Tr, Br, Pr, Av, Ta) D St' boff Ta' Av' nT nB
           \<le> copy_pass_impl St Tr Br Pr D St' boff Ta' Av' nT nB
               \<bind> (\<lambda>(Tr', Br', Pr', curT, curB). RETURN (Tr', Br', Pr'))"
  proof -
    interpret CI: modest_collapse_invar N St Tr Br Pr Av Ta D by (rule LOC)
    show ?thesis
      unfolding copy_ll_impl_def copy_pass_impl_def op_one_pfin_def Let_def
      \<comment> \<open>Put BOTH sides in the same monadic normal form first: right-nested binds, and the abstract
        pass's trailing \<open>RETURN\<close> of its own 5-tuple collapsed away. \<open>simp only\<close> with just these rules
        touches neither the asserts nor the arithmetic, so the steps below still match.\<close>
      apply (simp only: RT5 nres_monad_laws)
      \<comment> \<open>strip ONLY the leading ASSERT\<close>
      apply (subst bind_ASSERT_eq_if)
      apply (simp only: prod.case nTmax if_True)
      \<comment> \<open>the fresh-copy loop is exactly the abstract pass's aliases\<close>
      apply (rule order_trans[OF bind_mono(1)[OF copy_init_loop_RETURN[OF lenSt lenboff] order_refl]])
      apply (simp only: nres_monad1 prod.case)
      \<comment> \<open>the \<open>Tr'\<close>-prefill\<close>
      apply (rule order_trans[OF copy_prefill_refine_bind[OF MD lenSt lenboff StTr]])
      apply simp
      \<comment> \<open>prefill now identical on both sides; descend and hand the rest to the sweep bridge\<close>
      apply (rule bind_mono(1)[OF order_refl])
      apply (rule bind_mono(1))
       apply (rule copy_sweep_refine[OF LOC MD, unfolded Let_def])
      apply (rule order_refl)
      done
  qed

  text \<open>The Phase-B bridge in its final shape: composing with \<open>copy_pass_impl_refine\<close> relates the
    \<^emph>\<open>synthesised\<close> \<^const>\<open>copy_ll_impl\<close> directly to the abstract pass
    \<^const>\<open>modest_collapse_invar.copy_pass\<close>, which is what the combined builder needs. Copy is now on
    a par with the other four passes.\<close>
  lemma copy_ll_impl_copy_pass:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    assumes MD: "M = length D"
    assumes lenSt: "length St' = M + 1" and lenboff: "length boff = M + 1"
    assumes StTr: "\<And>c. c < M \<Longrightarrow> St' ! c < nT + 1"
    assumes nTmax: "nT < length Tr"
    shows "copy_ll_impl (St, Tr, Br, Pr, Av, Ta) D St' boff Ta' Av' nT nB
           \<le> modest_collapse_invar.copy_pass N St Tr Br Pr D St' boff Ta' Av' nT nB
               \<bind> (\<lambda>(Tr', Br', Pr', curT, curB). RETURN (Tr', Br', Pr'))"
    by (rule order_trans[OF copy_ll_impl_refine[OF LOC MD lenSt lenboff StTr nTmax]
                            bind_mono(1)[OF copy_pass_impl_refine[OF LOC] order_refl]])


  subsection \<open>The five passes as pre-synthesised \<open>sepref\<close> sub-operations\<close>

  text \<open>Each pass is registered as one operation and its synthesis theorem installed as a
    \<open>sepref_fr_rules\<close> entry, so the combined builder's \<open>sepref\<close> treats a pass as a single call instead
    of re-translating its loops. The \<open>[unfolded \<dots>_ll'.refine]\<close> step rewrites the concrete side from the
    locale-local constant to the global \<open>llvm_code\<close> one (the min-side pattern, cf.
    \<open>mop_min_red_impl_hnr_raw\<close>), which is what \<open>export_llvm\<close> needs.\<close>

  sepref_register count_pass_impl
  lemmas count_pass_hnr[sepref_fr_rules] =
    count_pass_ll.refine[unfolded count_pass_ll'.refine[OF collapse_build_env_axioms]]

  sepref_register empty_ec_impl
  lemmas empty_ec_hnr[sepref_fr_rules] =
    empty_ec_ll.refine[unfolded empty_ec_ll'.refine[OF collapse_build_env_axioms]]

  sepref_register offset_impl
  lemmas offset_hnr[sepref_fr_rules] =
    offset_ll.refine[unfolded offset_ll'.refine[OF collapse_build_env_axioms]]

  sepref_register copy_ll_impl
  lemmas copy_hnr[sepref_fr_rules] =
    copy_ll.refine[unfolded copy_ll'.refine[OF collapse_build_env_axioms]]

  sepref_register selfloop_impl
  lemmas selfloop_hnr[sepref_fr_rules] =
    selfloop_ll.refine[unfolded selfloop_ll'.refine[OF collapse_build_env_axioms]]


  subsection \<open>The combined builder\<close>

  text \<open>Sequencing the five passes needs a \<^emph>\<open>context-sensitive\<close> monotonicity rule: pass \<open>k+1\<close>'s
    implementation only refines its abstract counterpart under the postcondition of passes
    \<open>1..k\<close> (array lengths, the offset semantics, the overflow bounds). \<open>bind_mono_spec\<close> is
    \<open>bind_mono\<close> plus exactly that: the continuation goal may assume the first component's
    specification. It is the \<open>\<le>\<close>-level counterpart of @{thm [source] bind_refine'}.\<close>

  lemma le_ASSERT_bindI: "(P \<Longrightarrow> m \<le> m') \<Longrightarrow> m \<le> ASSERT P \<bind> (\<lambda>_. m')"
    by (cases P) auto

  lemma bind_spec_assert: "A \<le> SPEC \<Phi> \<Longrightarrow> A \<bind> f = A \<bind> (\<lambda>x. ASSERT (\<Phi> x) \<bind> (\<lambda>_. f x))"
    by (auto simp: pw_eq_iff pw_le_iff refine_pw_simps)

  lemma bind_mono_spec:
    assumes A: "A' \<le> A" and S: "A \<le> SPEC \<Phi>"
    assumes B: "\<And>x. \<Phi> x \<Longrightarrow> f' x \<le> f x"
    shows "A' \<bind> f' \<le> A \<bind> f"
    apply (subst bind_spec_assert[OF S])
    apply (rule bind_mono(1)[OF A])
    apply (rule le_ASSERT_bindI)
    apply (erule B)
    done

  \<comment> \<open>the copy pass is the one place where the two sides bind different tuples (the implementation
    drops the spent cursors), so its abstract side is re-associated through the projection\<close>
  lemma bind_proj3:
    "A \<bind> (\<lambda>(a, b, c, d, e). g a b c)
       = (A \<bind> (\<lambda>(a, b, c, d, e). RETURN (a, b, c))) \<bind> (\<lambda>(a, b, c). g a b c)"
    by (simp add: nres_monad_laws split_def)

  text \<open>The empty bitset over the MEC count \<open>M\<close>, as one \<^emph>\<open>monadic\<close> operation. Monadic (rather than a
    pure \<^term>\<open>{}\<close> constant like \<^const>\<open>op_one_pfin\<close>) so that each of the builder's three occurrences
    is translated to its own allocation and \<open>monadify\<close> cannot share them --- they must be three
    distinct buffers.\<close>
  definition mop_empty_bitset :: "nat set nres" where "mop_empty_bitset = RETURN {}"

  lemma mop_empty_bitset_correct:
    "(uncurry0 (bitset_empty_impl M), uncurry0 mop_empty_bitset)
       \<in> unit_rel \<rightarrow>\<^sub>f \<langle>bitset_rel M\<rangle>nres_rel"
    unfolding mop_empty_bitset_def bitset_empty_impl_alt
    by (auto intro!: frefI nres_relI simp: bitset_empty_rel RETURN_refine)

  sepref_definition mk_empty_bitset_ll is "uncurry0 (bitset_empty_impl M)"
    :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bitset_own_assn_raw"
    unfolding bitset_empty_impl_def bitset_own_assn_raw_def
    apply (rewrite array_fold_custom_replicate)
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done

end

text \<open>Same treatment as \<open>mk_pfin_one_pair_ll\<close>: extracted before its caller
  \<open>build_statespace_ll\<close>.\<close>
concrete_definition (in -) mk_empty_bitset_ll' [llvm_code] is
  collapse_build_env.mk_empty_bitset_ll_def

context collapse_build_env
begin

  sepref_register mop_empty_bitset
  lemmas mop_empty_bitset_hnr[sepref_fr_rules] =
    mk_empty_bitset_ll.refine[FCOMP mop_empty_bitset_correct, folded bitset_own_assn_def,
      unfolded mk_empty_bitset_ll'.refine[OF collapse_build_env_loc]]

  text \<open>The combined concrete builder: the five synthesised passes in the dataflow of
    \<^const>\<open>modest_collapse_invar.build_statespace'\<close>. It allocates its own three bitsets, so the
    operation is \<^emph>\<open>total\<close> --- there is no \<open>= {}\<close> precondition for a caller to violate. Two of the
    three come back as the built target / avoid sets; the third is freed (owned bitsets are freeable,
    unlike the input MDP's slice-backed ones).\<close>
  definition build_statespace_impl ::
    "modest_mdp \<Rightarrow> mec_map
      \<Rightarrow> (nat list \<times> nat list \<times> nat list \<times> real list \<times> nat set \<times> nat set) nres" where
    "build_statespace_impl MDP D = do {
       bT \<leftarrow> mop_empty_bitset;
       bA \<leftarrow> mop_empty_bitset;
       bV \<leftarrow> mop_empty_bitset;
       (cntT, cntB, Ta', avm) \<leftarrow> count_pass_impl MDP D bT bA;
       Av' \<leftarrow> empty_ec_impl cntT Ta' avm bV;
       (St', boff, nT, nB) \<leftarrow> offset_impl MDP cntT cntB Ta' Av';
       (Tr', Br', Pr') \<leftarrow> copy_ll_impl MDP D St' boff Ta' Av' nT nB;
       (Tr', Br', Pr') \<leftarrow> selfloop_impl MDP St' boff Ta' Av' Tr' Br' Pr';
       ASSERT (nT < length Tr');
       RETURN (St', Tr'[nT := nB], Br', Pr', Av', Ta') }"

  text \<open>Step 3 of the refinement scheme for the whole builder: the combined concrete program refines
    the locale-level abstract one. Each pass contributes its own \<open>_impl_refine\<close> (pass 4 the Phase-B
    bridge \<open>copy_ll_impl_copy_pass\<close>), and its precondition is discharged from the \<^emph>\<open>abstract\<close>
    postcondition of the passes before it --- which is what \<open>bind_mono_spec\<close> makes available.\<close>
  lemma build_statespace_impl_refine:
    assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
    assumes MD: "M = length D"
    shows "build_statespace_impl (St, Tr, Br, Pr, Av, Ta) D
           \<le> modest_collapse_invar.build_statespace' N St Tr Br Pr Av Ta D"
  proof -
    interpret CI: modest_collapse_invar N St Tr Br Pr Av Ta D by (rule LOC)
    show ?thesis
      unfolding build_statespace_impl_def CI.build_statespace'_def mop_empty_bitset_def
      \<comment> \<open>the three self-allocated bitsets are \<^term>\<open>{}\<close> abstractly, so they vanish by \<open>nres_monad1\<close>
        and the rest of the proof is unchanged\<close>
      apply (simp only: nres_monad1)
      apply (rule bind_mono_spec[OF count_pass_impl_refine[OF LOC MD]
                                    CI.count_pass_correct])
      subgoal premises P1 for x1
      proof -
        obtain cntT cntB Ta' avm where X1: "x1 = (cntT, cntB, Ta', avm)" by (cases x1) auto
        from P1[unfolded X1 prod.case]
        have LcT: "length cntT = length D" and LcB: "length cntB = length D"
          and cntTv: "\<forall>c<length D. cntT ! c = CI.tc c"
          and cntBv: "\<forall>c<length D. cntB ! c = CI.bc c"
          and Ta'eq: "Ta' = {c. c < length D \<and> CI.is_target_mec c}"
          and avmeq: "avm = {c. c < length D \<and> CI.is_avoid_mec c}"
          by auto
        show ?thesis
          unfolding X1 prod.case
          apply (rule bind_mono_spec[OF empty_ec_impl_refine[OF MD _ LOC]
                                        CI.empty_ec_pass_correct[OF cntTv Ta'eq avmeq]])
           apply (simp add: LcT MD)
          subgoal premises P2 for Av'
          proof -
            from P2 have Av'eq: "Av' = {c. c < length D \<and> CI.out_avoid c}" by simp
            have sumT: "(\<Sum>c = 0..<M. if c \<in> Ta' \<or> c \<in> Av' then 1 else cntT ! c) = CI.cnt_T"
              unfolding CI.cnt_T_ctA CI.ctA_def MD
              by (rule sum.cong[OF refl]) (auto simp: CI.contrib_T_alt Ta'eq Av'eq cntTv)
            have sumB: "(\<Sum>c = 0..<M. if c \<in> Ta' \<or> c \<in> Av' then 1 else cntB ! c) = CI.cnt_B"
              unfolding CI.cnt_B_cbA CI.cbA_def MD
              by (rule sum.cong[OF refl]) (auto simp: CI.contrib_B_alt Ta'eq Av'eq cntBv)
            show ?thesis
              apply (rule bind_mono_spec[OF offset_impl_refine[OF MD _ _ _ _ LOC]
                                            CI.offset_pass_correct[OF cntTv cntBv Ta'eq Av'eq]])
                 apply (simp add: LcT MD)
                apply (simp add: LcB MD)
               apply (simp add: sumT CI.cnt_T_le_length_Tr)
              apply (simp add: sumB CI.cnt_B_le_length_Br)
              subgoal premises P3 for x3
              proof -
                obtain St' boff nT nB where X3: "x3 = (St', boff, nT, nB)" by (cases x3) auto
                from P3[unfolded X3 prod.case]
                have lenSt: "length St' = length D + 1" and lenboff: "length boff = length D + 1"
                  and StA: "\<forall>c\<le>length D. St' ! c = CI.ctA c"
                  and bA: "\<forall>c\<le>length D. boff ! c = CI.cbA c"
                  and nTeq: "nT = CI.cnt_T" and nBeq: "nB = CI.cnt_B"
                  by auto
                have StTr: "St' ! c < nT + 1" if c: "c < M" for c
                proof -
                  have "St' ! c = CI.ctA c" using StA c MD by simp
                  also have "CI.ctA c \<le> CI.ctA (length D)" using c MD by (simp add: CI.ctA_mono)
                  finally show ?thesis using nTeq CI.cnt_T_ctA by simp
                qed
                show ?thesis
                  unfolding X3 prod.case
                  apply (subst bind_proj3)
                  apply (rule bind_mono_spec[OF copy_ll_impl_copy_pass[OF LOC MD _ _ StTr]
                      CI.copy_pass_correct3[OF StA bA lenSt lenboff Ta'eq Av'eq nTeq nBeq]])
                      apply (simp add: lenSt MD)
                     apply (simp add: lenboff MD)
                    apply simp
                   apply (simp add: nTeq CI.cnt_T_lt_length_Tr)
                  subgoal premises P4 for x4
                  proof -
                    obtain Tr' Br' Pr' where X4: "x4 = (Tr', Br', Pr')" by (cases x4) auto
                    from P4[unfolded X4 prod.case] have cp: "CI.copy_post Tr' Br' Pr'" by simp
                    have BND: "\<forall>c<M. (c \<in> Ta' \<or> c \<in> Av') \<longrightarrow>
                        c < length St' \<and> c < length boff \<and> St' ! c < length Tr'
                        \<and> St' ! c + 1 < length Tr' \<and> boff ! c < length Br' \<and> boff ! c < length Pr'
                        \<and> St' ! c < length Tr \<and> boff ! c < length Br"
                      using CI.selfloop_sink_bounds[OF cp StA bA lenSt lenboff] MD by auto
                    show ?thesis
                      unfolding X4 prod.case
                      by (rule bind_mono(1)[OF selfloop_impl_refine[OF LOC MD BND] order_refl])
                  qed
                  done
              qed
              done
          qed
          done
      qed
      done
  qed

  text \<open>Step-7 packaging, mirroring \<^const>\<open>op_build_statespace'\<close>: bundle the preserved input MDP, the
    freshly built state space, and the decomposition --- the shape \<^const>\<open>modest_build_rel\<close> relates,
    hence the \<open>FCOMP\<close> target. The input MDP and \<open>D\<close> are handed back rather than kept, because their
    assertions (CSR slices, and the MEC map) are the caller's memory: the builder owns nothing new
    except the arrays it allocated.\<close>
  definition op_build_statespace_impl where
    "op_build_statespace_impl = (\<lambda>(MDP, D). do {
       out \<leftarrow> build_statespace_impl MDP D;
       RETURN ((MDP, out), D) })"

  text \<open>Step 4: the whole builder to LLVM. With the five passes pre-synthesised (and their bodies
    therefore opaque here) this translates only the straight-line dataflow, the final
    \<open>Tr'[nT := nB]\<close> write --- whose bound comes from the \<^const>\<open>ASSERT\<close> cascaded into
    \<^const>\<open>modest_collapse_invar.build_statespace'\<close> --- and the result packaging.\<close>
  \<comment> \<open>The MEC-map environment was interpreted in the \<^emph>\<open>first\<close> \<open>collapse_build_env\<close> block, so
    \<open>mec_map_assn\<close> does not resolve to the same assertion here; re-interpret before the synthesis, or
    the pass \<open>hnr\<close> rules silently fail to match (their \<open>D\<close> argument is at a different assertion).\<close>
  interpretation disj_set_list_tuple_env N N ni ni
    apply unfold_locales using n_impl by auto

  sepref_definition build_statespace_ll is "PR_CONST op_build_statespace_impl"
    :: "(Modest_mdp_assn_aux \<times>\<^sub>a mec_map_assn)\<^sup>d
        \<rightarrow>\<^sub>a ((Modest_mdp_assn_aux \<times>\<^sub>a built_mdp_assn M) \<times>\<^sub>a mec_map_assn)"
    unfolding PR_CONST_def op_build_statespace_impl_def build_statespace_impl_def
      built_mdp_assn_def
    apply sepref
    done

  text \<open>Step 3 at the interface --- the \<open>build_statespace'_correct\<close> statement for the \<^emph>\<open>concrete\<close>
    builder: it refines \<^const>\<open>op_to_index\<close> over \<^const>\<open>modest_collapse_rel\<close> \<open>\<rightarrow>\<close>
    \<^const>\<open>modest_build_rel\<close>. Obtained by composing the step-3 refinement
    \<open>build_statespace_impl_refine\<close> with the abstract step-7 correctness
    @{thm [source] build_statespace'_refine} --- the packaging is literally
    \<^const>\<open>op_build_statespace'\<close>'s, so the two chain by \<open>order_trans\<close>.\<close>
  lemma op_build_statespace_impl_refine:
    assumes REL: "(((St,Tr,Br,Pr,Av,Ta), D), (\<M>c, D2)) \<in> modest_collapse_rel N"
    assumes MD: "M = length D2"
    shows "op_build_statespace_impl ((St,Tr,Br,Pr,Av,Ta), D)
             \<le> \<Down>(modest_build_rel N) (RETURN (op_to_index (\<M>c, D2)))"
  proof -
    have LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D" and DD: "D2 = D"
      using REL by (simp_all add: modest_collapse_rel_iff)
    have "op_build_statespace_impl ((St,Tr,Br,Pr,Av,Ta), D)
            \<le> op_build_statespace' N ((St,Tr,Br,Pr,Av,Ta), D)"
      unfolding op_build_statespace_impl_def op_build_statespace'_def prod.case
      by (rule bind_mono(1)[OF build_statespace_impl_refine[OF LOC MD[unfolded DD]] order_refl])
    also have "\<dots> \<le> \<Down>(modest_build_rel N) (RETURN (op_to_index (\<M>c, D2)))"
      by (rule build_statespace'_refine[OF REL])
    finally show ?thesis .
  qed

  lemma build_statespace_correct:
    "(PR_CONST op_build_statespace_impl, op_build_index)
     \<in> [\<lambda>x. M = length (snd x)]\<^sub>f
        modest_collapse_rel N \<rightarrow> \<langle>modest_build_rel N\<rangle>nres_rel"
    unfolding op_build_index_def
    apply (intro frefI nres_relI)
    \<comment> \<open>\<open>clarsimp\<close> splits the argument tuples and uses \<open>M = length D\<close> left-to-right, so the goal
      mentions \<open>length D\<close> where the lemma mentions the locale's \<open>M\<close>; rewrite the lemma the same way\<close>
    apply (clarsimp simp: PR_CONST_def)
    subgoal premises prems for St Tr Br Pr Av Ta D \<M>c D2
      using op_build_statespace_impl_refine[OF prems(2) prems(1), unfolded prems(1)] by simp
    done

  text \<open>Step 5: \<open>FCOMP\<close> collapses the chain, relating the abstract \<^const>\<open>op_to_index\<close> --- the
    indexed max reduction --- directly to the synthesised LLVM builder, at the interface assertions
    \<^const>\<open>Modest_collapse_assn\<close> \<open>\<rightarrow>\<close> \<^const>\<open>Modest_build_assn\<close>.\<close>
  context
    notes [fcomp_norm_unfold] = f_triple_aux Modest_collapse_assn_def[symmetric]
      Modest_build_assn_def[symmetric]
  begin
    lemmas build_statespace_hnr[sepref_fr_rules] =
      build_statespace_ll.refine[FCOMP build_statespace_correct]
  end

end

text \<open>The whole builder as a global \<open>llvm_code\<close> constant, ready for \<open>export_llvm\<close>.\<close>
concrete_definition (in -) build_statespace_ll' [llvm_code] is
  collapse_build_env.build_statespace_ll_def

end
