theory Modest_MDP_II_Maxred_Build
  imports Modest_MDP_II_Maxred
begin

text \<open>Steps 6 and 7: the state-space builder for the max reduction, and the proof that what it
  builds is the indexed max reduction of the input MDP.

  The theory is organised in three parts. (Names are given as plain text here because the header
  precedes every definition it mentions.)

  \<^item> \<^emph>\<open>The abstract account of the built state space\<close> (first \<^theory_text>\<open>context modest_collapse_invar\<close>
    block): which transitions leave a MEC (\<open>lvt\<close>), how many transitions and branches each MEC
    contributes (\<open>tc\<close> / \<open>bc\<close>, totals \<open>cnt_T\<close> / \<open>cnt_B\<close>, block offsets \<open>ctA\<close> / \<open>cbA\<close>), and what the
    CSR row of a MEC must contain (\<open>rowset\<close>, read back by \<open>seg\<close>).

  \<^item> \<^emph>\<open>The step-7 interface and obligations\<close>: the invariant \<open>modest_build_invar\<close> of a built state
    space, the refinement relation \<open>modest_build_rel\<close>, the operational postcondition \<open>built_post\<close>,
    and the two obligations discharged from it --- O1 validity (\<open>build_valid\<close>) and O2 semantics
    (\<open>build_semantics\<close>, the built MDP \<^emph>\<open>is\<close> the indexed max reduction). These depend only on
    \<open>built_post\<close>, never on how the arrays were produced.

  \<^item> \<^emph>\<open>The builder itself\<close>: an efficient, array-based (counting-sort / CSR-construction) five-pass
    program \<open>build_statespace'\<close> establishing exactly that postcondition, packaged as
    \<open>op_build_statespace'\<close>.\<close>

  context modest_collapse_invar
  begin

    subsection \<open>Leaving transitions and sink MECs\<close>

    text \<open>Separate (quantifier) predicates, each a bounded search implementable as a loop over
      \<^term>\<open>[0..<N]\<close> / the branches of a transition.\<close>

    text \<open>Transition \<^term>\<open>t\<close> (of a member of MEC \<^term>\<open>i\<close>) leaves MEC \<^term>\<open>i\<close>: some branch target lands
      in another MEC. A transition that does not leave is a collapsed self-loop and is dropped. The
      MEC index of a state is the refined \<^const>\<open>op_mec_index_of\<close> operation of the MEC map.\<close>
    definition "trans_leaves i t = (\<exists>b \<in> set (ls_intv (TrI ! t)). op_mec_index_of D (Br ! b) \<noteq> i)"

    text \<open>MEC \<^term>\<open>i\<close> is a target / avoid MEC iff it contains a target / avoid state (these are
      singleton MECs).\<close>
    definition "is_target_mec i = (\<exists>u \<in> {0..<N}. op_mec_index_of D u = i \<and> u \<in> Ta)"
    definition "is_avoid_mec i = (\<exists>u \<in> {0..<N}. op_mec_index_of D u = i \<and> u \<in> Av)"

    subsubsection \<open>The abstract counts\<close>

    text \<open>The sizes the built arrays must have: the leaving transitions of a member state, and the
      per-MEC / total transition and branch counts. The builder's counting pass is proved against
      these.\<close>
    definition "lvt i u = {t \<in> sn_intv (StI ! u). trans_leaves i t}"
    definition "tc i = (\<Sum>u \<in> {u \<in> {0..<N}. op_mec_index_of D u = i}. card (lvt i u))"
    definition "bc i = (\<Sum>u \<in> {u \<in> {0..<N}. op_mec_index_of D u = i}. \<Sum>t \<in> lvt i u. length (ls_intv (TrI ! t)))"
    text \<open>Each MEC contributes: a single self-loop transition/branch if it is a sink (target/avoid MEC,
      or a bottom MEC with no leaving transition), otherwise its \<^term>\<open>tc i\<close> transitions / \<^term>\<open>bc i\<close>
      branches.\<close>
    definition "cnt_T = (\<Sum>i \<in> {0..<length D}. if is_target_mec i \<or> is_avoid_mec i then 1 else if tc i = 0 then 1 else tc i)"
    definition "cnt_B = (\<Sum>i \<in> {0..<length D}. if is_target_mec i \<or> is_avoid_mec i then 1 else if tc i = 0 then 1 else bc i)"

    lemma finite_sn_intv[simp, intro]: "finite (sn_intv sn)"
      by (rule finite_subset[of _ "{..< uid sn}"]) (auto simp: sn_intv_def in_intv_def)

    lemma lvt_sub: "lvt i u \<subseteq> sn_intv (StI ! u)" by (auto simp: lvt_def)
    lemma finite_lvt[simp, intro]: "finite (lvt i u)" using lvt_sub finite_sn_intv by (rule finite_subset)
    lemma lvt_diff_sn[simp]: "lvt i u - sn_intv (StI ! u) = {}" using lvt_sub by blast
    lemma lvt_diff_it: "lvt i u - (it - {t})
      = (if trans_leaves i t \<and> t \<in> sn_intv (StI ! u) then insert t (lvt i u - it) else lvt i u - it)"
      by (auto simp: lvt_def)

    subsubsection \<open>Correctness of the fill pass\<close>

    text \<open>The per-MEC contribution to the transition / branch arrays: a sink (target/avoid/bottom MEC)
      emits one self-loop, any other MEC emits its \<^term>\<open>tc i\<close> transitions / \<^term>\<open>bc i\<close> branches.\<close>
    definition "contrib_T i = (if is_target_mec i \<or> is_avoid_mec i then 1 else if tc i = 0 then 1 else tc i)"
    definition "contrib_B i = (if is_target_mec i \<or> is_avoid_mec i then 1 else if tc i = 0 then 1 else bc i)"

    lemma length_ls_intv: "length (ls_intv sn) = cnt sn"
      by (simp add: ls_intv_def uid_def lid_def cnt_def split: prod.split)

    lemma lvt_real_trans: "t \<in> lvt i u \<Longrightarrow> u < N \<Longrightarrow> t < length Tr - Suc 0"
      using lvt_sub by (auto simp: sn_intv_def intro: Tr_in_bound_intvD)

    lemma length_ls_intv_lvt_pos: "t \<in> lvt i u \<Longrightarrow> u < N \<Longrightarrow> 0 < length (ls_intv (TrI ! t))"
      by (simp add: length_ls_intv Tr_nonempty lvt_real_trans)

    text \<open>A MEC with a leaving transition (\<^term>\<open>tc i > 0\<close>) also has a leaving branch (\<^term>\<open>bc i > 0\<close>),
      since every real transition has at least one branch.\<close>
    lemma bc_pos: "0 < tc i \<Longrightarrow> 0 < bc i"
    proof -
      have "tc i \<le> bc i" unfolding tc_def bc_def
      proof (rule sum_mono)
        fix u assume "u \<in> {u \<in> {0..<N}. op_mec_index_of D u = i}"
        then have uN: "u < N" by simp
        have "card (lvt i u) = (\<Sum>t\<in>lvt i u. Suc 0)" by simp
        also have "\<dots> \<le> (\<Sum>t\<in>lvt i u. length (ls_intv (TrI ! t)))"
        proof (rule sum_mono)
          fix t assume tl: "t \<in> lvt i u"
          from length_ls_intv_lvt_pos[OF tl uN]
          show "Suc 0 \<le> length (ls_intv (TrI ! t))" by (simp add: Suc_le_eq)
        qed
        finally show "card (lvt i u) \<le> (\<Sum>t\<in>lvt i u. length (ls_intv (TrI ! t)))" .
      qed
      moreover assume "0 < tc i"
      ultimately show "0 < bc i" by simp
    qed

    lemma contrib_T_pos: "contrib_T i \<ge> 1"
      unfolding contrib_T_def by auto
    lemma contrib_B_pos: "contrib_B i \<ge> 1"
      unfolding contrib_B_def using bc_pos by (auto simp: Suc_le_eq)

    text \<open>The cursor positions: \<^term>\<open>ctA i\<close> / \<^term>\<open>cbA i\<close> are where MEC \<^term>\<open>i\<close>'s transition / branch
      block starts (the running cursors at the top of outer iteration \<^term>\<open>i\<close>).\<close>
    definition "ctA i = (\<Sum>j \<in> {0..<i}. contrib_T j)"
    definition "cbA i = (\<Sum>j \<in> {0..<i}. contrib_B j)"

    lemma ctA_0[simp]: "ctA 0 = 0" and cbA_0[simp]: "cbA 0 = 0"
      unfolding ctA_def cbA_def by auto

    lemma ctA_Suc: "ctA (Suc i) = ctA i + contrib_T i"
      and cbA_Suc: "cbA (Suc i) = cbA i + contrib_B i"
      unfolding ctA_def cbA_def by simp_all

    lemma ctA_mono: "i \<le> j \<Longrightarrow> ctA i \<le> ctA j"
      unfolding ctA_def by (auto intro!: sum_mono2)
    lemma cbA_mono: "i \<le> j \<Longrightarrow> cbA i \<le> cbA j"
      unfolding cbA_def by (auto intro!: sum_mono2)

    lemma ctA_strict_mono: "i < j \<Longrightarrow> ctA i < ctA j"
      using ctA_mono[of "Suc i" j] ctA_Suc[of i] contrib_T_pos[of i] by simp
    lemma cbA_strict_mono: "i < j \<Longrightarrow> cbA i < cbA j"
      using cbA_mono[of "Suc i" j] cbA_Suc[of i] contrib_B_pos[of i] by simp

    lemma cnt_T_ctA: "cnt_T = ctA (length D)"
      unfolding cnt_T_def ctA_def contrib_T_def by simp
    lemma cnt_B_cbA: "cnt_B = cbA (length D)"
      unfolding cnt_B_def cbA_def contrib_B_def by simp

    text \<open>\<^const>\<open>mec_of\<close> is the executable MEC-index operation on \<^term>\<open>D\<close>.\<close>
    lemma mec_of_eq_op: "mec_of u = op_mec_index_of D u"
      by (simp add: mec_of_def op_mec_index_of_def)

    lemma sn_intv_eq: "sn_intv sn = {lid sn ..< uid sn}"
      by (auto simp: sn_intv_def in_intv_def)

    lemma card_sn_intv: "card (sn_intv sn) = cnt sn"
      by (cases sn) (simp add: sn_intv_eq uid_def lid_def cnt_def)

    subsubsection \<open>The branch-fill loop\<close>

    text \<open>Filling the branch block of one transition: after the loop, cursor \<^term>\<open>cb\<close> advanced by the
      branch count, cells outside the written block \<open>{c0..<cb}\<close> are untouched, and the block's
      \<open>(Br', Pr')\<close> cells are -- as a multiset -- exactly the original branches remapped by
      \<^term>\<open>op_mec_index_of D\<close>. The multiset (not list) formulation makes it order-independent, matching
      \<^const>\<open>FOREACH\<close>.\<close>
    definition "fill_inv t B0 P0 c0 it Br' Pr' cb \<longleftrightarrow>
      cb = c0 + card (sn_intv (TrI ! t) - it) \<and> c0 \<le> cb \<and>
      length Br' = length B0 \<and> length Pr' = length P0 \<and>
      (\<forall>c. (c < c0 \<or> cb \<le> c) \<longrightarrow> Br' ! c = B0 ! c \<and> Pr' ! c = P0 ! c) \<and>
      image_mset (\<lambda>c. (Br' ! c, Pr' ! c)) (mset_set {c0..<cb})
        = image_mset (\<lambda>b. (op_mec_index_of D (Br ! b), Pr ! b)) (mset_set (sn_intv (TrI ! t) - it))"

    lemma fill_inner_step:
      assumes room: "c0 + cnt (TrI ! t) \<le> length B0" "length P0 = length B0"
      assumes b: "b \<in> it" and itsub: "it \<subseteq> sn_intv (TrI ! t)"
      assumes INV: "fill_inv t B0 P0 c0 it Br' Pr' cb"
      shows "fill_inv t B0 P0 c0 (it - {b}) (Br'[cb := op_mec_index_of D (Br ! b)]) (Pr'[cb := Pr ! b]) (cb + 1)"
    proof -
      from INV[unfolded fill_inv_def]
      have cbeq: "cb = c0 + card (sn_intv (TrI ! t) - it)" and c0cb: "c0 \<le> cb"
        and lenB: "length Br' = length B0" and lenP: "length Pr' = length P0"
        and frozen: "\<And>c. (c < c0 \<or> cb \<le> c) \<Longrightarrow> Br' ! c = B0 ! c \<and> Pr' ! c = P0 ! c"
        and mset_eq: "image_mset (\<lambda>c. (Br' ! c, Pr' ! c)) (mset_set {c0..<cb})
             = image_mset (\<lambda>b. (op_mec_index_of D (Br ! b), Pr ! b)) (mset_set (sn_intv (TrI ! t) - it))"
        by auto
      have bsn: "b \<in> sn_intv (TrI ! t)" using b itsub by blast
      have bni: "b \<notin> sn_intv (TrI ! t) - it" using b by blast
      have cblt: "cb < c0 + cnt (TrI ! t)"
      proof -
        have "sn_intv (TrI ! t) - it \<subset> sn_intv (TrI ! t)" using bsn b by blast
        then have "card (sn_intv (TrI ! t) - it) < cnt (TrI ! t)"
          using psubset_card_mono[OF finite_sn_intv] by (simp add: card_sn_intv)
        then show ?thesis using cbeq by simp
      qed
      then have cbB: "cb < length Br'" and cbP: "cb < length Pr'"
        using room lenB lenP by auto
      let ?Br = "Br'[cb := op_mec_index_of D (Br ! b)]"
      let ?Pr = "Pr'[cb := Pr ! b]"
      have finS: "finite (sn_intv (TrI ! t) - it)" by simp
      have diff_ins: "sn_intv (TrI ! t) - (it - {b}) = insert b (sn_intv (TrI ! t) - it)"
        using bsn by blast
      have cnt_ins: "Suc cb = c0 + card (sn_intv (TrI ! t) - (it - {b}))"
        using cbeq by (simp add: diff_ins card_insert_disjoint[OF finS bni])
      have setins: "{c0..<Suc cb} = insert cb {c0..<cb}" using c0cb by auto
      have cbval: "(?Br ! cb, ?Pr ! cb) = (op_mec_index_of D (Br ! b), Pr ! b)"
        using cbB cbP by simp
      have seg_cong: "image_mset (\<lambda>c. (?Br ! c, ?Pr ! c)) (mset_set {c0..<cb})
          = image_mset (\<lambda>c. (Br' ! c, Pr' ! c)) (mset_set {c0..<cb})"
        by (rule image_mset_cong) (simp add: nth_list_update)
      have M: "image_mset (\<lambda>c. (?Br ! c, ?Pr ! c)) (mset_set {c0..<Suc cb})
          = image_mset (\<lambda>b. (op_mec_index_of D (Br ! b), Pr ! b)) (mset_set (sn_intv (TrI ! t) - (it - {b})))"
      proof -
        have "image_mset (\<lambda>c. (?Br ! c, ?Pr ! c)) (mset_set {c0..<Suc cb})
            = add_mset (op_mec_index_of D (Br ! b), Pr ! b) (image_mset (\<lambda>c. (Br' ! c, Pr' ! c)) (mset_set {c0..<cb}))"
          by (simp add: setins mset_set.insert cbval seg_cong)
        also have "\<dots> = add_mset (op_mec_index_of D (Br ! b), Pr ! b)
            (image_mset (\<lambda>b. (op_mec_index_of D (Br ! b), Pr ! b)) (mset_set (sn_intv (TrI ! t) - it)))"
          by (simp add: mset_eq)
        also have "\<dots> = image_mset (\<lambda>b. (op_mec_index_of D (Br ! b), Pr ! b)) (mset_set (sn_intv (TrI ! t) - (it - {b})))"
          by (simp add: diff_ins mset_set.insert[OF finS bni] image_mset_add_mset)
        finally show ?thesis .
      qed
      \<comment> \<open>Prove the invariant conjunct-by-conjunct: the multiset part is closed by \<open>M\<close> directly,
        so \<open>auto\<close> never re-derives the \<open>image_mset\<close> equation (which blows up).\<close>
      \<comment> \<open>Prove the invariant conjunct-by-conjunct. The frozen \<open>\<forall>c\<close> part is discharged by hand
        (the earlier \<open>auto\<close> exploded on it), and the multiset part is closed by \<open>M\<close> directly.\<close>
      show ?thesis unfolding fill_inv_def
      proof (intro conjI)
        show "cb + 1 = c0 + card (sn_intv (TrI ! t) - (it - {b}))" using cnt_ins by simp
        show "c0 \<le> cb + 1" using c0cb by simp
        show "length ?Br = length B0" using lenB by simp
        show "length ?Pr = length P0" using lenP by simp
        show "\<forall>c. (c < c0 \<or> cb + 1 \<le> c) \<longrightarrow> ?Br ! c = B0 ! c \<and> ?Pr ! c = P0 ! c"
        proof (intro allI impI)
          fix c assume A: "c < c0 \<or> cb + 1 \<le> c"
          then have "c \<noteq> cb" using c0cb by auto
          then have "?Br ! c = Br' ! c" and "?Pr ! c = Pr' ! c"
            by (simp_all add: nth_list_update)
          moreover have "c < c0 \<or> cb \<le> c" using A by auto
          ultimately show "?Br ! c = B0 ! c \<and> ?Pr ! c = P0 ! c" using frozen by simp
        qed
        show "image_mset (\<lambda>c. (?Br ! c, ?Pr ! c)) (mset_set {c0..<cb + 1})
              = image_mset (\<lambda>b. (op_mec_index_of D (Br ! b), Pr ! b))
                  (mset_set (sn_intv (TrI ! t) - (it - {b})))"
          using M by (simp add: Suc_eq_plus1[symmetric])
      qed
    qed

    lemma fill_inv_start: "fill_inv t B0 P0 c0 (sn_intv (TrI ! t)) B0 P0 c0"
      by (auto simp: fill_inv_def)

    lemma fill_inner:
      assumes room: "c0 + cnt (TrI ! t) \<le> length B0" "length P0 = length B0"
      shows "FOREACH (sn_intv (TrI ! t))
         (\<lambda>b (Br', Pr', cb). RETURN (Br'[cb := op_mec_index_of D (Br ! b)], Pr'[cb := Pr ! b], cb + 1))
         (B0, P0, c0)
       \<le> SPEC (\<lambda>(Br', Pr', cb). fill_inv t B0 P0 c0 {} Br' Pr' cb)"
      apply (refine_vcg FOREACH_rule[where I="\<lambda>it (Br', Pr', cb). fill_inv t B0 P0 c0 it Br' Pr' cb"])
      subgoal by simp
      subgoal by (auto intro: fill_inv_start)
      subgoal premises prems for x it \<sigma> a b aa ba x1 x2 x1a x2a
        using prems fill_inner_step[OF room, of x it a aa ba] by auto
      done

    text \<open>The post-condition of \<^const>\<open>fill_inv\<close> at \<open>it = {}\<close>, in explicit form.\<close>
    lemma fill_inv_emptyD:
      assumes "fill_inv t B0 P0 c0 {} Br' Pr' cb"
      shows "cb = c0 + cnt (TrI ! t) \<and> length Br' = length B0 \<and> length Pr' = length P0 \<and>
        (\<forall>c. (c < c0 \<or> cb \<le> c) \<longrightarrow> Br' ! c = B0 ! c \<and> Pr' ! c = P0 ! c) \<and>
        image_mset (\<lambda>c. (Br' ! c, Pr' ! c)) (mset_set {c0..<cb})
          = image_mset (\<lambda>b. (op_mec_index_of D (Br ! b), Pr ! b)) (mset_set (sn_intv (TrI ! t)))"
      using assms by (auto simp: fill_inv_def card_sn_intv)

    subsubsection \<open>Segments and the per-state fill\<close>

    text \<open>\<open>rmt t\<close> is the remapped branch multiset of transition \<open>t\<close> (its branches with targets
      relabelled by \<^const>\<open>op_mec_index_of\<close>); \<open>seg Tr' Br' Pr' s\<close> is the \<open>(Br', Pr')\<close> content of the
      CSR segment of slot \<open>s\<close>, i.e. \<open>{Tr'!s ..< Tr'!(Suc s)}\<close>. An emitted transition's segment reads
      back as its \<open>rmt\<close>.\<close>
    definition "rmt t = image_mset (\<lambda>b. (op_mec_index_of D (Br ! b), Pr ! b)) (mset_set (sn_intv (TrI ! t)))"
    definition "seg Tr' Br' Pr' s = image_mset (\<lambda>c. (Br' ! c, Pr' ! c)) (mset_set {Tr' ! s ..< Tr' ! Suc s})"

    text \<open>Reading back a freshly emitted transition \<open>t\<close> at slot \<open>ct\<close>: opening pointer \<open>cb\<close>, branches
      filling \<open>{cb ..< cb'}\<close> (multiset \<open>rmt t\<close>, from \<^const>\<open>fill_inv\<close>), closing pointer \<open>cb'\<close>.\<close>
    lemma seg_emit:
      assumes op: "Tr' ! ct = cb" and cl: "Tr' ! Suc ct = cb'"
        and blk: "image_mset (\<lambda>c. (Br' ! c, Pr' ! c)) (mset_set {cb..<cb'})
                  = image_mset (\<lambda>b. (op_mec_index_of D (Br ! b), Pr ! b)) (mset_set (sn_intv (TrI ! t)))"
      shows "seg Tr' Br' Pr' ct = rmt t"
      unfolding seg_def rmt_def using assms by simp

    text \<open>Invariant of the per-state transition loop for member \<^term>\<open>u\<close> of MEC \<^term>\<open>i\<close>. Processing the
      transitions of \<^term>\<open>u\<close>, after handling \<open>done = sn_intv (StI!u) - it\<close>: the cursors advanced by the
      leaving transitions handled (\<open>lvt i u - it\<close>), the opening pointer \<open>Tr'!ct = cb\<close> is live, the arrays
      are frozen outside the region just written, and the emitted segments read back as the remapped
      leaving transitions.\<close>
    definition "fill_state_inv u i TR BR PR ct0 cb0 em0 it Tr' Br' Pr' ct cb em \<longleftrightarrow>
      ct = ct0 + card (lvt i u - it) \<and>
      cb = cb0 + (\<Sum>t \<in> lvt i u - it. cnt (TrI ! t)) \<and>
      em = (em0 \<or> lvt i u - it \<noteq> {}) \<and>
      ct0 \<le> ct \<and> Tr' ! ct = cb \<and>
      length Tr' = length TR \<and> length Br' = length BR \<and> length Pr' = length PR \<and>
      (\<forall>s. ct0 \<le> s \<and> s \<le> ct \<longrightarrow> Tr' ! s \<le> cb) \<and>
      (\<forall>s. (s \<le> ct0 \<or> ct < s) \<longrightarrow> Tr' ! s = TR ! s) \<and>
      (\<forall>c. (c < cb0 \<or> cb \<le> c) \<longrightarrow> Br' ! c = BR ! c \<and> Pr' ! c = PR ! c) \<and>
      seg Tr' Br' Pr' ` {ct0..<ct} = rmt ` (lvt i u - it)"

    lemma lvt_mem: "x \<in> lvt i u \<longleftrightarrow> x \<in> sn_intv (StI ! u) \<and> trans_leaves i x"
      by (auto simp: lvt_def)

    lemma lvt_diff_insert: "x \<in> lvt i u \<Longrightarrow> x \<in> it \<Longrightarrow> lvt i u - (it - {x}) = insert x (lvt i u - it)"
      by auto

    lemma lvt_diff_skip: "\<not> trans_leaves i x \<Longrightarrow> lvt i u - (it - {x}) = lvt i u - it"
      by (auto simp: lvt_mem)

    lemma lvt_sum_room:
      assumes x: "x \<in> lvt i u" and xS: "x \<notin> S" and Ssub: "S \<subseteq> lvt i u"
      shows "(\<Sum>t\<in>S. cnt (TrI ! t)) + cnt (TrI ! x) \<le> (\<Sum>t\<in>lvt i u. cnt (TrI ! t))"
    proof -
      have fin: "finite S" using Ssub finite_lvt by (rule finite_subset)
      have "(\<Sum>t\<in>S. cnt (TrI ! t)) + cnt (TrI ! x) = (\<Sum>t\<in>insert x S. cnt (TrI ! t))"
        using fin xS by simp
      also have "\<dots> \<le> (\<Sum>t\<in>lvt i u. cnt (TrI ! t))"
        using x Ssub by (intro sum_mono2) auto
      finally show ?thesis .
    qed

    text \<open>The emit step of the per-state loop: emitting leaving transition \<^term>\<open>x\<close> at slot \<^term>\<open>ct\<close>
      (with its branch block filled -- \<open>FI\<close> -- and pointers written) preserves the invariant, extending
      the emitted-segment set by \<^term>\<open>rmt x\<close>.\<close>
    lemma fill_state_emit_step:
      assumes xlvt: "x \<in> lvt i u" and xit: "x \<in> it"
      assumes op0: "TR ! ct0 = cb0" and roomT: "ct0 + card (lvt i u) < length TR"
      assumes INV: "fill_state_inv u i TR BR PR ct0 cb0 em0 it Tr' Br' Pr' ct cb em"
      assumes FI: "fill_inv x Br' Pr' cb {} Br2 Pr2 cb'"
      shows "fill_state_inv u i TR BR PR ct0 cb0 em0 (it - {x})
               (Tr'[ct := cb, Suc ct := cb']) Br2 Pr2 (Suc ct) cb' True"
    proof -
      from INV[unfolded fill_state_inv_def] have
        ict: "ct = ct0 + card (lvt i u - it)" and
        icb: "cb = cb0 + (\<Sum>t\<in>lvt i u - it. cnt (TrI ! t))" and
        ct0ct: "ct0 \<le> ct" and iop: "Tr' ! ct = cb" and
        lenT: "length Tr' = length TR" and lenB: "length Br' = length BR" and
        lenP: "length Pr' = length PR" and
        ibnd: "\<forall>s. ct0 \<le> s \<and> s \<le> ct \<longrightarrow> Tr' ! s \<le> cb" and
        ifrzT: "\<forall>s. (s \<le> ct0 \<or> ct < s) \<longrightarrow> Tr' ! s = TR ! s" and
        ifrzB: "\<forall>c. (c < cb0 \<or> cb \<le> c) \<longrightarrow> Br' ! c = BR ! c \<and> Pr' ! c = PR ! c" and
        iseg: "seg Tr' Br' Pr' ` {ct0..<ct} = rmt ` (lvt i u - it)"
        by auto
      from fill_inv_emptyD[OF FI] have
        fcb: "cb' = cb + cnt (TrI ! x)" and flenB: "length Br2 = length Br'" and
        flenP: "length Pr2 = length Pr'" and
        ffrz: "\<forall>c. (c < cb \<or> cb' \<le> c) \<longrightarrow> Br2 ! c = Br' ! c \<and> Pr2 ! c = Pr' ! c" and
        fblk: "image_mset (\<lambda>c. (Br2 ! c, Pr2 ! c)) (mset_set {cb..<cb'})
               = image_mset (\<lambda>b. (op_mec_index_of D (Br ! b), Pr ! b)) (mset_set (sn_intv (TrI ! x)))"
        by auto
      have xni: "x \<notin> lvt i u - it" using xit by blast
      have di: "lvt i u - (it - {x}) = insert x (lvt i u - it)" using xlvt xit by (rule lvt_diff_insert)
      have cbcb': "cb \<le> cb'" using fcb by simp
      have Nct: "Suc ct = ct0 + card (lvt i u - (it - {x}))" using ict di xni by simp
      have Ncb: "cb' = cb0 + (\<Sum>t\<in>lvt i u - (it - {x}). cnt (TrI ! t))"
        using fcb icb di xni by simp
      have le: "card (lvt i u - (it - {x})) \<le> card (lvt i u)"
        by (rule card_mono[OF finite_lvt Diff_subset])
      have SucLt: "Suc ct < length TR" using Nct le roomT by linarith
      have ctltT: "ct < length Tr'" and succtltT: "Suc ct < length Tr'"
        using SucLt lenT by simp_all
      let ?T = "Tr'[ct := cb, Suc ct := cb']"
      have Tct: "?T ! ct = cb" using iop ctltT by (simp add: nth_list_update)
      have TSuc: "?T ! Suc ct = cb'" using succtltT by simp
      \<comment> \<open>the new segment reads back as \<open>rmt x\<close>\<close>
      have segx: "seg ?T Br2 Pr2 ct = rmt x"
        using Tct TSuc fblk by (rule seg_emit)
      \<comment> \<open>old segments are unchanged\<close>
      have segold: "\<And>s. s \<in> {ct0..<ct} \<Longrightarrow> seg ?T Br2 Pr2 s = seg Tr' Br' Pr' s"
      proof -
        fix s assume s: "s \<in> {ct0..<ct}"
        then have s0: "ct0 \<le> s" and sct: "s < ct" by auto
        have Ts: "?T ! s = Tr' ! s" using sct by (simp add: nth_list_update)
        have TsucS: "?T ! Suc s = Tr' ! Suc s"
        proof (cases "Suc s = ct")
          case True then show ?thesis using iop ctltT by (simp add: nth_list_update)
        next
          case False then show ?thesis using sct by (simp add: nth_list_update)
        qed
        have cells: "\<And>c. c \<in> {Tr' ! s..<Tr' ! Suc s} \<Longrightarrow> (Br2 ! c, Pr2 ! c) = (Br' ! c, Pr' ! c)"
        proof -
          fix c assume "c \<in> {Tr' ! s..<Tr' ! Suc s}"
          then have "c < Tr' ! Suc s" by simp
          also have "Tr' ! Suc s \<le> cb" using ibnd s0 sct by simp
          finally have "c < cb" .
          then show "(Br2 ! c, Pr2 ! c) = (Br' ! c, Pr' ! c)" using ffrz by simp
        qed
        show "seg ?T Br2 Pr2 s = seg Tr' Br' Pr' s"
          unfolding seg_def Ts TsucS by (rule image_mset_cong) (simp add: cells)
      qed
      have Nseg: "seg ?T Br2 Pr2 ` {ct0..<Suc ct} = rmt ` (lvt i u - (it - {x}))"
      proof -
        have "{ct0..<Suc ct} = insert ct {ct0..<ct}" using ct0ct by auto
        then have "seg ?T Br2 Pr2 ` {ct0..<Suc ct}
            = insert (rmt x) (seg ?T Br2 Pr2 ` {ct0..<ct})" by (simp add: segx)
        also have "seg ?T Br2 Pr2 ` {ct0..<ct} = seg Tr' Br' Pr' ` {ct0..<ct}"
          by (rule image_cong[OF refl segold])
        also have "insert (rmt x) (seg Tr' Br' Pr' ` {ct0..<ct}) = insert (rmt x) (rmt ` (lvt i u - it))"
          by (simp add: iseg)
        also have "\<dots> = rmt ` (lvt i u - (it - {x}))" by (simp add: di)
        finally show ?thesis .
      qed
      \<comment> \<open>the new pointer bound\<close>
      have Nbnd: "\<forall>s. ct0 \<le> s \<and> s \<le> Suc ct \<longrightarrow> ?T ! s \<le> cb'"
      proof (intro allI impI)
        fix s assume "ct0 \<le> s \<and> s \<le> Suc ct"
        then have s0: "ct0 \<le> s" and s: "s \<le> Suc ct" by auto
        show "?T ! s \<le> cb'"
        proof (cases "s = Suc ct")
          case True then show ?thesis using TSuc by simp
        next
          case False
          with s have sct: "s \<le> ct" by simp
          show ?thesis
          proof (cases "s = ct")
            case True then show ?thesis using Tct cbcb' by simp
          next
            case False
            with sct have "s < ct" by simp
            then have "?T ! s = Tr' ! s" by (simp add: nth_list_update)
            also have "Tr' ! s \<le> cb" using ibnd s0 sct by simp
            finally show ?thesis using cbcb' by simp
          qed
        qed
      qed
      \<comment> \<open>freezing of the transition-pointer array\<close>
      have NfrzT: "\<forall>s. (s \<le> ct0 \<or> Suc ct < s) \<longrightarrow> ?T ! s = TR ! s"
      proof (intro allI impI)
        fix s assume A: "s \<le> ct0 \<or> Suc ct < s"
        show "?T ! s = TR ! s"
        proof (cases "s = ct")
          case True
          with A ct0ct have ctct0: "ct = ct0" by auto
          then have "card (lvt i u - it) = 0" using ict by simp
          then have empty: "lvt i u - it = {}" by simp
          have "cb = cb0" using icb by (simp add: empty)
          then show ?thesis using True Tct op0 ctct0 by simp
        next
          case False
          have sne: "s \<noteq> Suc ct" using A ct0ct by auto
          have "?T ! s = Tr' ! s" using False sne by (simp add: nth_list_update)
          also have "Tr' ! s = TR ! s" using ifrzT A False ct0ct by auto
          finally show ?thesis .
        qed
      qed
      have NfrzB: "\<forall>c. (c < cb0 \<or> cb' \<le> c) \<longrightarrow> Br2 ! c = BR ! c \<and> Pr2 ! c = PR ! c"
      proof (intro allI impI)
        fix c assume "c < cb0 \<or> cb' \<le> c"
        then show "Br2 ! c = BR ! c \<and> Pr2 ! c = PR ! c"
          using ffrz ifrzB icb cbcb' by (cases "c < cb0") auto
      qed
      show ?thesis unfolding fill_state_inv_def
        using Nct Ncb ct0ct TSuc lenT lenB lenP flenB flenP Nbnd NfrzT NfrzB Nseg di
        by simp
    qed

    subsubsection \<open>The leaving transitions of a whole MEC\<close>

    text \<open>\<open>ltdone i itu\<close>: the leaving transitions of MEC \<open>i\<close> belonging to the already-processed member
      states (\<open>{0..<N} - itu\<close>). At \<open>itu = {}\<close> this is all of MEC \<open>i\<close>'s leaving transitions.\<close>
    definition "ltdone i itu = (\<Union>u \<in> {u \<in> {0..<N} - itu. op_mec_index_of D u = i}. lvt i u)"

    lemma finite_ltdone[simp, intro]: "finite (ltdone i itu)"
      unfolding ltdone_def by auto

    lemma ltdone_step: "u \<in> itu \<Longrightarrow> u < N \<Longrightarrow> op_mec_index_of D u = i
      \<Longrightarrow> ltdone i (itu - {u}) = ltdone i itu \<union> lvt i u"
      unfolding ltdone_def by auto

    lemma ltdone_skip: "u \<in> itu \<Longrightarrow> op_mec_index_of D u \<noteq> i \<Longrightarrow> ltdone i (itu - {u}) = ltdone i itu"
      unfolding ltdone_def by auto

    lemma lvt_disj_states: "u < N \<Longrightarrow> v < N \<Longrightarrow> u \<noteq> v \<Longrightarrow> lvt i u \<inter> lvt i v = {}"
    proof -
      assume u: "u < N" and v: "v < N" and ne: "u \<noteq> v"
      have "sn_intv (StI ! u) \<inter> sn_intv (StI ! v) = {}"
      proof (cases "u < v")
        case True show ?thesis using St_intv_disj[OF True v] .
      next
        case False with ne have vu: "v < u" by simp
        show ?thesis using St_intv_disj[OF vu u] by (simp add: inf_commute)
      qed
      then show ?thesis using lvt_sub by blast
    qed

    lemma lvt_ltdone_disj: "u \<in> itu \<Longrightarrow> u < N \<Longrightarrow> lvt i u \<inter> ltdone i itu = {}"
      unfolding ltdone_def using lvt_disj_states by fastforce

    text \<open>The post-condition of \<^const>\<open>fill_state_inv\<close> at \<open>it = {}\<close>.\<close>
    lemma fill_state_emptyD:
      assumes "fill_state_inv u i TR BR PR ct0 cb0 em0 {} Tr' Br' Pr' ct cb em"
      shows "ct = ct0 + card (lvt i u) \<and> cb = cb0 + (\<Sum>t\<in>lvt i u. cnt (TrI ! t)) \<and>
        em = (em0 \<or> lvt i u \<noteq> {}) \<and> ct0 \<le> ct \<and> Tr' ! ct = cb \<and>
        length Tr' = length TR \<and> length Br' = length BR \<and> length Pr' = length PR \<and>
        (\<forall>s. ct0 \<le> s \<and> s \<le> ct \<longrightarrow> Tr' ! s \<le> cb) \<and>
        (\<forall>s. (s \<le> ct0 \<or> ct < s) \<longrightarrow> Tr' ! s = TR ! s) \<and>
        (\<forall>c. (c < cb0 \<or> cb \<le> c) \<longrightarrow> Br' ! c = BR ! c \<and> Pr' ! c = PR ! c) \<and>
        seg Tr' Br' Pr' ` {ct0..<ct} = rmt ` (lvt i u)"
      using assms by (auto simp: fill_state_inv_def)

    lemma tc_card: "tc i = card (ltdone i {})"
      unfolding tc_def ltdone_def
      by (subst card_UN_disjoint) (auto simp: lvt_disj_states)

    lemma bc_sum: "bc i = (\<Sum>t \<in> ltdone i {}. cnt (TrI ! t))"
      unfolding bc_def ltdone_def
      apply (subst sum.UNION_disjoint)
      by (auto simp: lvt_disj_states length_ls_intv)

    lemma ltdone_sub_full: "ltdone i itu \<subseteq> ltdone i {}"
      unfolding ltdone_def by auto

    lemma lvt_sub_full: "u \<in> {0..<N} \<Longrightarrow> op_mec_index_of D u = i \<Longrightarrow> lvt i u \<subseteq> ltdone i {}"
      unfolding ltdone_def by auto

    lemma room_card: "x \<in> it \<Longrightarrow> x < N \<Longrightarrow> op_mec_index_of D x = i
      \<Longrightarrow> card (ltdone i it) + card (lvt i x) \<le> tc i"
    proof -
      assume xit: "x \<in> it" and xN: "x < N" and mecx: "op_mec_index_of D x = i"
      have disj: "lvt i x \<inter> ltdone i it = {}" using xit xN by (rule lvt_ltdone_disj)
      have sub: "ltdone i it \<union> lvt i x \<subseteq> ltdone i {}"
        using ltdone_sub_full lvt_sub_full[of x] xN mecx by auto
      have "card (ltdone i it) + card (lvt i x) = card (ltdone i it \<union> lvt i x)"
        using disj by (simp add: card_Un_disjoint Int_commute)
      also have "\<dots> \<le> card (ltdone i {})" using sub by (simp add: card_mono)
      finally show ?thesis by (simp add: tc_card)
    qed

    lemma room_sum: "x \<in> it \<Longrightarrow> x < N \<Longrightarrow> op_mec_index_of D x = i
      \<Longrightarrow> (\<Sum>t\<in>ltdone i it. cnt (TrI ! t)) + (\<Sum>t\<in>lvt i x. cnt (TrI ! t)) \<le> bc i"
    proof -
      assume xit: "x \<in> it" and xN: "x < N" and mecx: "op_mec_index_of D x = i"
      have disj: "lvt i x \<inter> ltdone i it = {}" using xit xN by (rule lvt_ltdone_disj)
      have sub: "ltdone i it \<union> lvt i x \<subseteq> ltdone i {}"
        using ltdone_sub_full lvt_sub_full[of x] xN mecx by auto
      have "(\<Sum>t\<in>ltdone i it. cnt (TrI ! t)) + (\<Sum>t\<in>lvt i x. cnt (TrI ! t))
          = (\<Sum>t\<in>ltdone i it \<union> lvt i x. cnt (TrI ! t))"
        using disj by (simp add: sum.union_disjoint Int_commute)
      also have "\<dots> \<le> (\<Sum>t\<in>ltdone i {}. cnt (TrI ! t))"
        using sub by (simp add: sum_mono2)
      finally show ?thesis by (simp add: bc_sum)
    qed

    subsubsection \<open>Row content: what a MEC's CSR block must contain\<close>

    text \<open>The classification of a MEC index in the built state space, and the multiset content of its
      CSR row. Target/avoid/bottom MECs are sinks (a single self-loop \<open>{#(j,1)#}\<close>); other MECs collect
      their leaving transitions \<^term>\<open>rmt ` ltfull j\<close>.\<close>
    definition "out_avoid j \<longleftrightarrow> \<not> is_target_mec j \<and> (is_avoid_mec j \<or> tc j = 0)"
    definition "ltfull i = ltdone i {}"
    definition "rowset j = (if is_target_mec j \<or> out_avoid j then {{#(j, 1::real)#}} else rmt ` ltfull j)"

    text \<open>Cursor position bounds inside the built arrays for MEC \<open>i < length D\<close>.\<close>
    lemma ctA_le_cnt_T: "i \<le> length D \<Longrightarrow> ctA i \<le> cnt_T"
      using ctA_mono[of i "length D"] by (simp add: cnt_T_ctA)
    lemma cbA_le_cnt_B: "i \<le> length D \<Longrightarrow> cbA i \<le> cnt_B"
      using cbA_mono[of i "length D"] by (simp add: cnt_B_cbA)

  end


  section \<open>The built state space: invariant, abstraction, and refinement relation (step 7)\<close>

  text \<open>Invariant for a built state space. We compose \<^locale>\<open>modest_collapse_invar\<close> (the original
    Modest MDP with its MEC decomposition \<^term>\<open>D\<close>, giving the \<^term>\<open>D\<close>-invariant and keeping the old
    data live as a separate construct) with the \<open>Sup\<close>-mode interval-iteration invariant
    \<^locale>\<open>modest_mdp_ii_invar_sup\<close> for the built state space at size \<^term>\<open>length D\<close> -- i.e. exactly
    the invariant of \<^const>\<open>modest_mdp_sup_rel\<close>, the relation the Sup interval iteration consumes, so
    build output and II input line up. We do NOT assume the built space is the max reduction here (the
    builder only achieves that at the end): that is a postcondition of \<open>build_statespace'\<close> (the step-7
    refinement, via the specification of \<^const>\<open>to_index\<close>), not a locale invariant.\<close>
  locale modest_build_invar =
    modest_collapse_invar N St Tr Br Pr Av Ta D +
    N': modest_mdp_ii_invar_sup "length D" St' Tr' Br' Pr' Av' Ta'
    for N St Tr Br Pr Av Ta D St' Tr' Br' Pr' Av' Ta' +
    \<comment> \<open>The built CSR arrays fit inside the input ones. Stated \<^emph>\<open>relatively\<close>: a machine-word
      bound is not provable here (see the hard rule in \<open>CLAUDE.md\<close>), but the code layer needs one,
      and it recovers it by chaining these against the \<^emph>\<open>input\<close> MDP's own assertion --- which sits
      in the very same \<open>modest_build_rel\<close> tuple.\<close>
    assumes Tr'_cap: "length Tr' \<le> length Tr"
      and Br'_cap: "length Br' \<le> length Br"

  text \<open>The step-7 refinement relation, parameterised by the original MDP's size \<^term>\<open>N\<close> (threaded
    like \<^const>\<open>modest_collapse_rel\<close>; it is part of the preserved old-MDP data, no dependent typing).
    The concrete side keeps three separate constructs -- the original MDP, the built state space, and
    the MEC decomposition \<^term>\<open>D\<close> (a physical component: mapped to memory and kept owned so \<open>sepref\<close>
    does not free the old MDP). The built space is sized \<^term>\<open>length D\<close>, not \<^term>\<open>N\<close>. \<open>build_\<alpha>\<close> and
    \<open>build_inv\<close> reuse the \<^emph>\<open>same\<close> abstraction \<^const>\<open>\<M>_\<alpha>_sup'\<close> and invariant
    \<^const>\<open>modest_mdp_ii_invar_sup\<close> as \<^const>\<open>modest_mdp_sup_rel\<close> for the collapsed part, so the built
    MDP is directly a valid Sup-II input; the step-7 refinement shows \<open>build_\<alpha>\<close> equals the indexed
    max reduction \<open>to_index (M_mec \<M>_\<alpha>) D\<close>.\<close>
  abbreviation "build_\<alpha> \<equiv>
    (\<lambda>(((St,Tr,Br,Pr,Av,Ta), (St',Tr',Br',Pr',Av',Ta')), D).
       \<M>_\<alpha>_sup' (length D) (St',Tr',Br',Pr',Av',Ta'))"
  abbreviation "build_inv N \<equiv>
    (\<lambda>(((St,Tr,Br,Pr,Av,Ta), (St',Tr',Br',Pr',Av',Ta')), D).
       modest_build_invar N St Tr Br Pr Av Ta D St' Tr' Br' Pr' Av' Ta')"

  definition modest_build_rel ::
    "nat \<Rightarrow> (((modest_input_mdp \<times> modest_input_mdp) \<times> nat set list) \<times> nat mdptc) set" where
    "modest_build_rel N = br build_\<alpha> (build_inv N)"

  lemma modest_build_rel_sv[simp, intro!]: "single_valued (modest_build_rel N)"
    unfolding modest_build_rel_def by (rule br_sv)


  section \<open>The step-7 obligations: validity (O1) and semantics (O2)\<close>

  context modest_collapse_invar
  begin

    text \<open>The operational postcondition a builder has to establish, named so that the validity (O1)
      and semantics (O2) obligations below can be stated against it independently of \<^emph>\<open>how\<close> the
      arrays were produced. It is discharged, for the builder below, by \<open>build_statespace'_post\<close>.\<close>
    definition built_post :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> real list \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> bool" where
      "built_post St' Tr' Br' Pr' Av' Ta' \<longleftrightarrow>
          length St' = length D + 1 \<and> length Tr' = cnt_T + 1 \<and>
          length Br' = cnt_B \<and> length Pr' = cnt_B \<and>
          (\<forall>j\<le>length D. St' ! j = ctA j) \<and>
          Av' = {j. j < length D \<and> out_avoid j} \<and>
          Ta' = {j. j < length D \<and> is_target_mec j} \<and>
          Tr' ! 0 = 0 \<and> Tr' ! cnt_T = cnt_B \<and> (\<forall>s\<le>cnt_T. Tr' ! s \<le> cnt_B) \<and>
          (\<forall>j<length D. seg Tr' Br' Pr' ` {ctA j..<ctA (Suc j)} = rowset j)"

    subsection \<open>Row content lemmas (shared by O1 and O2)\<close>

    text \<open>Every transition in @{term \<open>ltfull j\<close>} is an actual transition (a member's leaving transition),
      hence a proper index into @{term Tr}.\<close>
    lemma ltfull_real_trans: "t \<in> ltfull j \<Longrightarrow> t < length Tr - Suc 0"
      unfolding ltfull_def ltdone_def using lvt_real_trans by fastforce

    text \<open>An emitted (remapped) transition row @{term \<open>rmt t\<close>} is a nonempty multiset of
      @{text \<open>(mec-index, prob)\<close>} pairs whose indices are below @{term \<open>length D\<close>}, whose probabilities
      are strictly positive, and whose probabilities sum to 1.\<close>
    lemma rmt_nonempty: "t \<in> ltfull j \<Longrightarrow> rmt t \<noteq> {#}"
    proof -
      assume "t \<in> ltfull j"
      then have "0 < cnt (TrI ! t)" using ltfull_real_trans Tr_nonempty by blast
      then have "sn_intv (TrI ! t) \<noteq> {}" using card_sn_intv[of "TrI ! t"] by fastforce
      then show ?thesis by (simp add: rmt_def mset_set_empty_iff)
    qed

    lemma rmt_index_lt:
      assumes "t \<in> ltfull j" "(k, p) \<in># rmt t"
      shows "k < length D"
    proof -
      from assms(2) obtain b where b: "b \<in> sn_intv (TrI ! t)" and k: "k = op_mec_index_of D (Br ! b)"
        by (auto simp: rmt_def)
      from assms(1) have t: "t < length Tr - Suc 0" by (rule ltfull_real_trans)
      from b have "in_intv (TrI ! t) b" by (simp add: sn_intv_def)
      then have "b < length Br" by (rule Br_in_bound_intvD[OF t])
      then have "Br ! b < N" by (rule Br_in_bound)
      then show ?thesis using k by (simp add: mec_of_op_index mec_of_lt)
    qed

    lemma rmt_prob_pos:
      assumes "t \<in> ltfull j" "(k, p) \<in># rmt t"
      shows "0 < p"
    proof -
      from assms(2) obtain b where b: "b \<in> sn_intv (TrI ! t)" and p: "p = Pr ! b"
        by (auto simp: rmt_def)
      from assms(1) have t: "t < length Tr - Suc 0" by (rule ltfull_real_trans)
      from b have "in_intv (TrI ! t) b" by (simp add: sn_intv_def)
      then have "b < length Br" by (rule Br_in_bound_intvD[OF t])
      then show ?thesis using p by (simp add: Pr_nth_gt_0)
    qed

    lemma rmt_prob_sum:
      assumes "t \<in> ltfull j"
      shows "(\<Sum>x\<in>#rmt t. snd x) = 1"
    proof -
      from assms have t: "t < length Tr - Suc 0" by (rule ltfull_real_trans)
      have "(\<Sum>x\<in>#rmt t. snd x) = (\<Sum>b\<in>sn_intv (TrI ! t). Pr ! b)"
        by (simp add: rmt_def multiset.map_comp o_def sum_unfold_sum_mset)
      also have "\<dots> = sum_list (map ((!) Pr) (ls_intv (TrI ! t)))"
        by (simp add: ls_intv_def sn_intv_eq sum_list_distinct_conv_sum_set)
      also have "\<dots> = 1" using t by (rule Pr_lt_one')
      finally show ?thesis .
    qed

    text \<open>The same four properties, lifted to any element of a built row set @{term \<open>rowset j\<close>} (the
      sink rows @{term \<open>{#(j, 1)#}\<close>} satisfy them trivially).\<close>
    lemma rowset_elem_nonempty: "j < length D \<Longrightarrow> m \<in> rowset j \<Longrightarrow> m \<noteq> {#}"
      by (auto simp: rowset_def rmt_nonempty split: if_splits)

    lemma rowset_elem_index: "j < length D \<Longrightarrow> m \<in> rowset j \<Longrightarrow> (k, p) \<in># m \<Longrightarrow> k < length D"
      by (auto simp: rowset_def rmt_index_lt split: if_splits)

    lemma rowset_elem_pos: "j < length D \<Longrightarrow> m \<in> rowset j \<Longrightarrow> (k, p) \<in># m \<Longrightarrow> 0 < p"
      by (auto simp: rowset_def rmt_prob_pos split: if_splits)

    lemma rowset_elem_sum: "j < length D \<Longrightarrow> m \<in> rowset j \<Longrightarrow> (\<Sum>x\<in>#m. snd x) = 1"
      by (auto simp: rowset_def rmt_prob_sum split: if_splits)

    subsection \<open>Block/interval partition structure (for O1)\<close>

    text \<open>Every transition slot @{term \<open>s < cnt_T\<close>} lies in exactly one MEC block
      @{term \<open>{ctA j..<ctA (Suc j)}\<close>}: the cursors @{const ctA} run @{term \<open>0 = ctA 0\<close>} up to
      @{term \<open>ctA (length D) = cnt_T\<close>} strictly, so they cover @{term \<open>{0..<cnt_T}\<close>}.\<close>
    lemma block_cover:
      assumes s: "s < cnt_T"
      shows "\<exists>j<length D. ctA j \<le> s \<and> s < ctA (Suc j)"
    proof -
      let ?J = "{j. j \<le> length D \<and> ctA j \<le> s}"
      have fin: "finite ?J" by auto
      have "0 \<in> ?J" by simp
      then have ne: "?J \<noteq> {}" by blast
      define j where "j = Max ?J"
      have jJ: "j \<in> ?J" unfolding j_def using fin ne by (rule Max_in)
      then have jle: "j \<le> length D" and cj: "ctA j \<le> s" by auto
      have jlt: "j < length D"
      proof (rule ccontr)
        assume "\<not> j < length D"
        then have "ctA (length D) \<le> s" using cj jle by simp
        then show False using s cnt_T_ctA by simp
      qed
      have "s < ctA (Suc j)"
      proof (rule ccontr)
        assume "\<not> s < ctA (Suc j)"
        then have "Suc j \<in> ?J" using jlt by simp
        then have "Suc j \<le> j" unfolding j_def using fin by (simp add: Max_ge)
        then show False by simp
      qed
      with cj jlt show ?thesis by blast
    qed

    text \<open>Consequently every slot's emitted segment is one of MEC @{term j}'s rows.\<close>
    lemma built_slot_seg:
      assumes P: "built_post St' Tr' Br' Pr' Av' Ta'" and s: "s < cnt_T"
      shows "\<exists>j<length D. seg Tr' Br' Pr' s \<in> rowset j"
    proof -
      from block_cover[OF s] obtain j where j: "j < length D" "ctA j \<le> s" "s < ctA (Suc j)" by blast
      from P j(1) have "seg Tr' Br' Pr' ` {ctA j..<ctA (Suc j)} = rowset j" by (simp add: built_post_def)
      moreover have "s \<in> {ctA j..<ctA (Suc j)}" using j(2,3) by simp
      ultimately show ?thesis using j(1) by blast
    qed

    text \<open>Each emitted transition slot is nonempty (its row is a nonempty multiset), so @{term Tr'} is
      strictly increasing on @{term \<open>{0..<cnt_T}\<close>}.\<close>
    lemma built_Tr_strict:
      assumes P: "built_post St' Tr' Br' Pr' Av' Ta'" and s: "s < cnt_T"
      shows "Tr' ! s < Tr' ! Suc s"
    proof -
      from built_slot_seg[OF P s] obtain j where j: "j < length D" and m: "seg Tr' Br' Pr' s \<in> rowset j"
        by blast
      from rowset_elem_nonempty[OF j m] have "seg Tr' Br' Pr' s \<noteq> {#}" .
      then have "{Tr' ! s..<Tr' ! Suc s} \<noteq> {}" by (auto simp: seg_def)
      then show ?thesis by simp
    qed

    text \<open>Every branch position @{term \<open>c < cnt_B\<close>} lies in exactly one transition interval
      @{term \<open>{Tr' ! s..<Tr' ! Suc s}\<close>}: @{term Tr'} runs @{term \<open>0 = Tr' ! 0\<close>} up to
      @{term \<open>Tr' ! cnt_T = cnt_B\<close>}.\<close>
    lemma built_interval_cover:
      assumes P: "built_post St' Tr' Br' Pr' Av' Ta'" and c: "c < cnt_B"
      shows "\<exists>s<cnt_T. Tr' ! s \<le> c \<and> c < Tr' ! Suc s"
    proof -
      from P have Tr0: "Tr' ! 0 = 0" and TrcT: "Tr' ! cnt_T = cnt_B" by (simp_all add: built_post_def)
      let ?S = "{s. s \<le> cnt_T \<and> Tr' ! s \<le> c}"
      have fin: "finite ?S" by auto
      have "0 \<in> ?S" using Tr0 by simp
      then have ne: "?S \<noteq> {}" by blast
      define s where "s = Max ?S"
      have sS: "s \<in> ?S" unfolding s_def using fin ne by (rule Max_in)
      then have sle: "s \<le> cnt_T" and cs: "Tr' ! s \<le> c" by auto
      have slt: "s < cnt_T"
      proof (rule ccontr)
        assume "\<not> s < cnt_T"
        then have "cnt_B \<le> c" using cs sle TrcT by simp
        then show False using c by simp
      qed
      have "c < Tr' ! Suc s"
      proof (rule ccontr)
        assume "\<not> c < Tr' ! Suc s"
        then have "Suc s \<in> ?S" using slt by simp
        then have "Suc s \<le> s" unfolding s_def using fin by (simp add: Max_ge)
        then show False by simp
      qed
      with cs slt show ?thesis by blast
    qed

    subsection \<open>O1: validity of the built state space\<close>

    text \<open>The built arrays form a well-formed Modest MDP over the @{term \<open>length D\<close>} MEC-index states:
      sorted CSR pointers, in-bounds branch targets, and probabilities that are positive and sum to 1
      on each transition (each row is one of the pmf-carrying @{const rowset} entries).\<close>
    lemma built_input_invar:
      assumes P: "built_post St' Tr' Br' Pr' Av' Ta'"
      shows "modest_mdp_input_invar (length D) St' Tr' Br' Pr' Av' Ta'"
    proof -
      from P have LSt: "length St' = length D + 1" and LTr: "length Tr' = cnt_T + 1"
        and LBr: "length Br' = cnt_B" and LPr: "length Pr' = cnt_B"
        and StN: "\<forall>j\<le>length D. St' ! j = ctA j"
        and AvE: "Av' = {j. j < length D \<and> out_avoid j}"
        and TaE: "Ta' = {j. j < length D \<and> is_target_mec j}"
        and Tr0: "Tr' ! 0 = 0" and TrcT: "Tr' ! cnt_T = cnt_B"
        and TrB: "\<forall>s\<le>cnt_T. Tr' ! s \<le> cnt_B"
        by (simp_all add: built_post_def)

      have Stbound: "\<And>j. j < length St' \<Longrightarrow> St' ! j \<le> cnt_T"
      proof -
        fix j assume "j < length St'"
        then have "j \<le> length D" using LSt by simp
        then show "St' ! j \<le> cnt_T" using StN ctA_le_cnt_T by auto
      qed
      have SortSt: "sorted_wrt (<) St'"
        unfolding sorted_wrt_iff_nth_less
      proof (intro allI impI)
        fix i j assume ij: "i < j" "j < length St'"
        then have "j \<le> length D" using LSt by simp
        then have "St' ! i = ctA i" "St' ! j = ctA j" using StN ij(1) by auto
        then show "St' ! i < St' ! j" using ctA_strict_mono ij(1) by simp
      qed

      have TrConsec: "\<And>s. s < cnt_T \<Longrightarrow> Tr' ! s < Tr' ! Suc s" using built_Tr_strict[OF P] .
      have SortTr: "sorted_wrt (<) Tr'"
        unfolding sorted_wrt_iff_nth_less
      proof (intro allI impI)
        fix i j assume "i < j" "j < length Tr'"
        then show "Tr' ! i < Tr' ! j"
        proof (induct j)
          case 0 then show ?case by simp
        next
          case (Suc j)
          from Suc.prems have jcT: "j < cnt_T" using LTr by simp
          show ?case
          proof (cases "i = j")
            case True then show ?thesis using TrConsec[OF jcT] by simp
          next
            case False
            then have "i < j" using Suc.prems(1) by simp
            then have "Tr' ! i < Tr' ! j" using Suc.hyps jcT LTr by simp
            also have "Tr' ! j < Tr' ! Suc j" using TrConsec[OF jcT] .
            finally show ?thesis .
          qed
        qed
      qed

      have BrLt: "\<And>c. c < length Br' \<Longrightarrow> Br' ! c < length D"
      proof -
        fix c assume "c < length Br'"
        then have c: "c < cnt_B" using LBr by simp
        from built_interval_cover[OF P c] obtain s where s: "s < cnt_T" "Tr' ! s \<le> c" "c < Tr' ! Suc s"
          by blast
        from built_slot_seg[OF P s(1)] obtain j where j: "j < length D" and m: "seg Tr' Br' Pr' s \<in> rowset j"
          by blast
        have "(Br' ! c, Pr' ! c) \<in># seg Tr' Br' Pr' s" using s(2,3) by (auto simp: seg_def)
        then show "Br' ! c < length D" using rowset_elem_index[OF j m] by blast
      qed

      have PrPos: "\<And>c. c < length Pr' \<Longrightarrow> 0 < Pr' ! c"
      proof -
        fix c assume "c < length Pr'"
        then have c: "c < cnt_B" using LPr by simp
        from built_interval_cover[OF P c] obtain s where s: "s < cnt_T" "Tr' ! s \<le> c" "c < Tr' ! Suc s"
          by blast
        from built_slot_seg[OF P s(1)] obtain j where j: "j < length D" and m: "seg Tr' Br' Pr' s \<in> rowset j"
          by blast
        have "(Br' ! c, Pr' ! c) \<in># seg Tr' Br' Pr' s" using s(2,3) by (auto simp: seg_def)
        then show "0 < Pr' ! c" using rowset_elem_pos[OF j m] by blast
      qed

      have PrSum: "\<And>t. t < length Tr' - Suc 0 \<Longrightarrow> sum_list (map ((!) Pr') [Tr' ! t..<Tr' ! Suc t]) = 1"
      proof -
        fix t assume "t < length Tr' - Suc 0"
        then have t: "t < cnt_T" using LTr by simp
        from built_slot_seg[OF P t] obtain j where j: "j < length D" and m: "seg Tr' Br' Pr' t \<in> rowset j"
          by blast
        have "sum_list (map ((!) Pr') [Tr' ! t..<Tr' ! Suc t]) = (\<Sum>c\<in>{Tr' ! t..<Tr' ! Suc t}. Pr' ! c)"
          by (simp add: sum_list_distinct_conv_sum_set)
        also have "\<dots> = (\<Sum>x\<in>#seg Tr' Br' Pr' t. snd x)"
          by (simp add: seg_def multiset.map_comp o_def sum_unfold_sum_mset)
        also have "\<dots> = 1" using rowset_elem_sum[OF j m] .
        finally show "sum_list (map ((!) Pr') [Tr' ! t..<Tr' ! Suc t]) = 1" .
      qed

      show ?thesis
        apply unfold_locales
        subgoal using LSt by simp
        subgoal by (rule length_D_pos)
        subgoal using AvE by auto
        subgoal using TaE by auto
        subgoal using AvE TaE by (auto simp: out_avoid_def)
        subgoal using Stbound LTr by (fastforce simp: in_set_conv_nth less_Suc_eq_le)
        subgoal using TrB LTr LBr by (fastforce simp: in_set_conv_nth)
        subgoal using BrLt by (auto simp: in_set_conv_nth)
        subgoal by (rule SortSt)
        subgoal by (rule SortTr)
        subgoal using PrSum by simp
        subgoal using PrPos by (auto simp: in_set_conv_nth)
        subgoal using LPr LBr by simp
        done
    qed

    text \<open>O1 (validity): the built arrays are a well-formed @{term Sup}-mode interval-iteration input.\<close>
    lemma build_valid:
      assumes P: "built_post St' Tr' Br' Pr' Av' Ta'"
      shows "modest_mdp_ii_invar_sup (length D) St' Tr' Br' Pr' Av' Ta'"
    proof -
      interpret I: modest_mdp_input_invar "length D" St' Tr' Br' Pr' Av' Ta'
        using built_input_invar[OF P] .
      show ?thesis
        by unfold_locales
           (auto simp: reachability_opt_mode_defs.vDom_def reachability_opt_mode_defs.in_vDom_def)
    qed

    subsection \<open>O2: the built MDP is the indexed max reduction\<close>

    text \<open>Bridges to the abstract max reduction: the reduced MDP is exactly @{const Max_red} of the
      source MDP, and indexing a collapsed state @{term \<open>col u\<close>} recovers its MEC index @{term \<open>mec_of u\<close>}.\<close>
    lemma reduce_collapse: "reduce (M_mec \<M>_\<alpha>) = Max_red \<M>_\<alpha>"
      by (rule reduce_M_mec)

    lemma idx_of_col: "u < N \<Longrightarrow> idx_of D (col u) = mec_of u"
    proof -
      assume u: "u < N"
      have st: "states (col u) = D ! mec_of u" by (simp add: col_def states_mec_mdp)
      have "(THE i. i < length D \<and> states (col u) = D ! i) = mec_of u"
      proof (rule the_equality)
        show "mec_of u < length D \<and> states (col u) = D ! mec_of u" using u mec_of_lt st by simp
      next
        fix i assume i: "i < length D \<and> states (col u) = D ! i"
        then have "D ! i = D ! mec_of u" using st by simp
        then show "i = mec_of u"
          using i u mec_of_lt distinct_D nth_eq_iff_index_eq by metis
      qed
      then show ?thesis by (simp add: idx_of_def)
    qed

    text \<open>@{const mec_of} is onto the index set: every class @{term \<open>D ! j\<close>} is nonempty.\<close>
    lemma mec_class_subs_N: "j < length D \<Longrightarrow> D ! j \<subseteq> {0..<N}"
      using set_D nth_mem states_in_decomp mec_decomp_\<M>_\<alpha> states_\<M>_\<alpha>
      by (metis nth_mem set_D mec_class_sub)

    lemma mem_D_less_N[dest]: "v \<in> D ! j \<Longrightarrow> j < length D \<Longrightarrow> v < N"
      using mec_class_subs_N by (meson atLeastLessThan_iff subsetD)

    lemma mec_of_onto: "mec_of ` {0..<N} = {0..<length D}"
    proof (intro Set.equalityI subsetI)
      fix j assume "j \<in> mec_of ` {0..<N}"
      then show "j \<in> {0..<length D}" using mec_of_lt by auto
    next
      fix j assume j: "j \<in> {0..<length D}"
      then have "D ! j \<in> mec_decomp' \<M>_\<alpha>" using set_D nth_mem by (metis atLeastLessThan_iff)
      then have "D ! j \<noteq> {}" by (rule mec_class_ne)
      then obtain u where u: "u \<in> D ! j" by blast
      then have "u < N" using mec_class_subs_N j by auto
      then have "mec_of u = j" using u j in_D_iff_mec_of by auto
      then show "j \<in> mec_of ` {0..<N}" using \<open>u < N\<close> by force
    qed

    text \<open>The target index set of the reduction is exactly the target-MEC indices.\<close>
    lemma targets_reduce_collapse: "idx_of D ` targets (reduce (M_mec \<M>_\<alpha>)) = {j. j < length D \<and> is_target_mec j}"
    proof -
      have "idx_of D ` targets (reduce (M_mec \<M>_\<alpha>)) = (\<lambda>u. idx_of D (col u)) ` Ta"
        by (simp add: targets_reduce targets_collapse image_image)
      also have "\<dots> = mec_of ` Ta" using idx_of_col TaN by (auto cong: image_cong)
      also have "\<dots> = {j. j < length D \<and> is_target_mec j}"
      proof (intro Set.equalityI subsetI)
        fix j assume "j \<in> mec_of ` Ta"
        then obtain u where u: "u \<in> Ta" "j = mec_of u" by auto
        then have uN: "u < N" using TaN by simp
        then have "j < length D" using u mec_of_lt by simp
        moreover have "is_target_mec j" using u uN by (auto simp: is_target_mec_def mec_of_op_index)
        ultimately show "j \<in> {j. j < length D \<and> is_target_mec j}" by simp
      next
        fix j assume "j \<in> {j. j < length D \<and> is_target_mec j}"
        then obtain u where "u \<in> {0..<N}" "op_mec_index_of D u = j" "u \<in> Ta"
          by (auto simp: is_target_mec_def)
        then show "j \<in> mec_of ` Ta" by (auto simp: mec_of_op_index)
      qed
      finally show ?thesis .
    qed

    text \<open>The built MDP fits in the input: \<open>cnt_T\<close> (its transition count) is at most \<^term>\<open>length Tr\<close>.
      Each MEC contributes either its leaving transitions (\<open>tc i\<close>) or \<open>1\<close>; and since every state has
      at least one transition, that many distinct input transitions exist for each MEC (the CSR slices
      \<^term>\<open>sn_intv (StI ! u)\<close> partition \<^term>\<open>{0..<length Tr - 1}\<close> by source state).\<close>
    lemma Suc_cnt_T_le_length_Tr: "Suc cnt_T \<le> length Tr"
    proof -
      have pos: "0 < length Tr"
      proof (cases St)
        case Nil
        with N0 show ?thesis by (simp add: N_DEF)
      next
        case (Cons a list)
        then have "a \<in> set St" by simp
        with St_dom show ?thesis by auto
      qed
      define Si where "Si i = {u \<in> {0..<N}. op_mec_index_of D u = i}" for i
      define Ti where "Ti i = (\<Union>u \<in> Si i. sn_intv (StI ! u))" for i
      have finSi: "finite (Si i)" for i unfolding Si_def by simp
      have SiN: "u < N" if "u \<in> Si i" for u i using that unfolding Si_def by simp
      have snb: "t < length Tr - Suc 0" if "t \<in> sn_intv (StI ! u)" "u < N" for t u
        using that by (auto simp: sn_intv_def intro: Tr_in_bound_intvD)
      have disjU: "sn_intv (StI ! u) \<inter> sn_intv (StI ! v) = {}" if "u \<noteq> v" "u < N" "v < N" for u v
        using that by (metis St_intv_disj inf_commute nat_neq_iff)
      have cardTi: "card (Ti i) = (\<Sum>u \<in> Si i. cnt (StI ! u))" for i
        unfolding Ti_def
        by (subst card_UN_disjoint) (auto simp: finSi card_sn_intv SiN disjU)
      have tc_le: "tc i \<le> card (Ti i)" for i
        unfolding tc_def cardTi Si_def
        by (intro sum_mono) (metis card_mono card_sn_intv finite_sn_intv lvt_sub)
      have contrib_le: "contrib_T i \<le> card (Ti i)" if iD: "i < length D" for i
      proof (cases "is_target_mec i \<or> is_avoid_mec i \<or> tc i = 0")
        case True
        then have c1: "contrib_T i = 1" by (auto simp: contrib_T_def)
        from iD have "i \<in> mec_of ` {0..<N}" by (simp add: mec_of_onto)
        then obtain u where uN: "u \<in> {0..<N}" and mu: "mec_of u = i" by blast
        then have uSi: "u \<in> Si i" by (simp add: Si_def mec_of_eq_op)
        have "sn_intv (StI ! u) \<noteq> {}"
          using uN St_nonempty by (metis atLeastLessThan_iff card_gt_0_iff card_sn_intv)
        then have "Ti i \<noteq> {}" using uSi unfolding Ti_def by blast
        moreover have "finite (Ti i)" unfolding Ti_def using finSi finite_sn_intv by blast
        ultimately have "0 < card (Ti i)" by (simp add: card_gt_0_iff)
        with c1 show ?thesis by simp
      next
        case False
        then have "contrib_T i = tc i" by (simp add: contrib_T_def)
        with tc_le show ?thesis by simp
      qed
      have finTi: "finite (Ti i)" for i unfolding Ti_def using finSi finite_sn_intv by blast
      have disjTi: "Ti i \<inter> Ti j = {}" if "i \<noteq> j" for i j
      proof (rule ccontr)
        assume "Ti i \<inter> Ti j \<noteq> {}"
        then obtain x u v where uv: "u \<in> Si i" "x \<in> sn_intv (StI ! u)" "v \<in> Si j" "x \<in> sn_intv (StI ! v)"
          unfolding Ti_def by blast
        then have "u \<noteq> v" using that unfolding Si_def by auto
        with uv show False using disjU SiN by blast
      qed
      have UNsub: "(\<Union>i \<in> {0..<length D}. Ti i) \<subseteq> {0..<length Tr - Suc 0}"
        unfolding Ti_def Si_def using snb by fastforce
      have "cnt_T = (\<Sum>i = 0..<length D. contrib_T i)" by (simp add: cnt_T_def contrib_T_def)
      also have "\<dots> \<le> (\<Sum>i = 0..<length D. card (Ti i))"
        by (intro sum_mono contrib_le) simp
      also have "\<dots> = card (\<Union>i \<in> {0..<length D}. Ti i)"
        by (subst card_UN_disjoint) (auto simp: finTi disjTi)
      also have "\<dots> \<le> card {0..<length Tr - Suc 0}"
        using UNsub by (intro card_mono) auto
      finally have "cnt_T \<le> length Tr - Suc 0" by simp
      then show ?thesis using pos by linarith
    qed

    text \<open>Dually, \<open>cnt_B\<close> (the built branch count) is at most \<^term>\<open>length Br\<close>: each MEC's branches are
      those of its leaving transitions (\<open>bc i\<close>) or a single self-loop branch, and every transition of
      every state has at least one branch (the \<^term>\<open>sn_intv (TrI ! t)\<close> slices partition
      \<^term>\<open>{0..<length Br - 1}\<close>).\<close>
    lemma cnt_B_le_length_Br: "cnt_B \<le> length Br"
    proof -
      define Si where "Si i = {u \<in> {0..<N}. op_mec_index_of D u = i}" for i
      define Ti where "Ti i = (\<Union>u \<in> Si i. sn_intv (StI ! u))" for i
      define Bi where "Bi i = (\<Union>t \<in> Ti i. sn_intv (TrI ! t))" for i
      have finSi: "finite (Si i)" for i unfolding Si_def by simp
      have SiN: "u < N" if "u \<in> Si i" for u i using that unfolding Si_def by simp
      have finTi: "finite (Ti i)" for i unfolding Ti_def using finSi finite_sn_intv by blast
      have TiTr: "t < length Tr - Suc 0" if "t \<in> Ti i" for t i
        using that unfolding Ti_def by (auto simp: sn_intv_def intro: Tr_in_bound_intvD dest: SiN)
      have snBr: "b < length Br" if "b \<in> sn_intv (TrI ! t)" "t < length Tr - Suc 0" for b t
        using that by (auto simp: sn_intv_def intro: Br_in_bound_intvD)
      have disjSt: "sn_intv (StI ! u) \<inter> sn_intv (StI ! v) = {}" if "u \<noteq> v" "u < N" "v < N" for u v
        using that by (metis St_intv_disj inf_commute nat_neq_iff)
      have disjTi: "Ti i \<inter> Ti j = {}" if "i \<noteq> j" for i j
      proof (rule ccontr)
        assume "Ti i \<inter> Ti j \<noteq> {}"
        then obtain x u v where uv: "u \<in> Si i" "x \<in> sn_intv (StI ! u)" "v \<in> Si j" "x \<in> sn_intv (StI ! v)"
          unfolding Ti_def by blast
        then have "u \<noteq> v" using that unfolding Si_def by auto
        with uv show False using disjSt SiN by blast
      qed
      have disjTr: "sn_intv (TrI ! s) \<inter> sn_intv (TrI ! t) = {}"
          if "s \<noteq> t" "s < length Tr - Suc 0" "t < length Tr - Suc 0" for s t
        using that by (metis Tr_intv_disj inf_commute nat_neq_iff)
      have cardBi: "card (Bi i) = (\<Sum>t \<in> Ti i. cnt (TrI ! t))" for i
        unfolding Bi_def
        by (subst card_UN_disjoint) (auto simp: finTi card_sn_intv TiTr disjTr)
      have bc_le: "bc i \<le> card (Bi i)" for i
      proof -
        have lvtsub: "(\<Union>u\<in>Si i. lvt i u) \<subseteq> Ti i" unfolding Ti_def using lvt_sub by fastforce
        have "bc i = (\<Sum>u\<in>Si i. \<Sum>t\<in>lvt i u. cnt (TrI ! t))"
          unfolding bc_def Si_def by (simp add: length_ls_intv)
        also have "\<dots> = (\<Sum>t\<in>(\<Union>u\<in>Si i. lvt i u). cnt (TrI ! t))"
          by (subst sum.UNION_disjoint) (auto simp: finSi lvt_disj_states SiN)
        also have "\<dots> \<le> (\<Sum>t\<in>Ti i. cnt (TrI ! t))"
          by (intro sum_mono2) (auto simp: finTi lvtsub)
        also have "\<dots> = card (Bi i)" using cardBi[of i] by simp
        finally show ?thesis .
      qed
      have contrib_le: "contrib_B i \<le> card (Bi i)" if iD: "i < length D" for i
      proof (cases "is_target_mec i \<or> is_avoid_mec i \<or> tc i = 0")
        case True
        then have c1: "contrib_B i = 1" by (auto simp: contrib_B_def)
        from iD have "i \<in> mec_of ` {0..<N}" by (simp add: mec_of_onto)
        then obtain u where uN: "u \<in> {0..<N}" and mu: "mec_of u = i" by blast
        then have uSi: "u \<in> Si i" by (simp add: Si_def mec_of_eq_op)
        have "sn_intv (StI ! u) \<noteq> {}"
          using uN St_nonempty by (metis atLeastLessThan_iff card_gt_0_iff card_sn_intv)
        then obtain t where t: "t \<in> sn_intv (StI ! u)" by blast
        then have tTi: "t \<in> Ti i" using uSi unfolding Ti_def by blast
        then have "t < length Tr - Suc 0" by (rule TiTr)
        then have "sn_intv (TrI ! t) \<noteq> {}" using Tr_nonempty by (metis card_gt_0_iff card_sn_intv)
        then have "Bi i \<noteq> {}" using tTi unfolding Bi_def by blast
        moreover have "finite (Bi i)" unfolding Bi_def using finTi finite_sn_intv by blast
        ultimately have "0 < card (Bi i)" by (simp add: card_gt_0_iff)
        with c1 show ?thesis by simp
      next
        case False
        then have "contrib_B i = bc i" by (auto simp: contrib_B_def)
        with bc_le show ?thesis by simp
      qed
      have finBi: "finite (Bi i)" for i unfolding Bi_def using finTi finite_sn_intv by blast
      have disjBi: "Bi i \<inter> Bi j = {}" if ij: "i \<noteq> j" for i j
      proof (rule ccontr)
        assume "Bi i \<inter> Bi j \<noteq> {}"
        then obtain b where "b \<in> Bi i" "b \<in> Bi j" by blast
        then obtain s t where s: "s \<in> Ti i" "b \<in> sn_intv (TrI ! s)"
          and t: "t \<in> Ti j" "b \<in> sn_intv (TrI ! t)" unfolding Bi_def by blast
        have "s \<noteq> t" using s t ij disjTi by blast
        moreover have "s < length Tr - Suc 0" "t < length Tr - Suc 0" using s t TiTr by auto
        ultimately have "sn_intv (TrI ! s) \<inter> sn_intv (TrI ! t) = {}" by (rule disjTr)
        with s t show False by blast
      qed
      have UNsub: "(\<Union>i \<in> {0..<length D}. Bi i) \<subseteq> {0..<length Br}"
        unfolding Bi_def using TiTr snBr by fastforce
      have "cnt_B = (\<Sum>i = 0..<length D. contrib_B i)" by (simp add: cnt_B_def contrib_B_def)
      also have "\<dots> \<le> (\<Sum>i = 0..<length D. card (Bi i))"
        by (intro sum_mono contrib_le) simp
      also have "\<dots> = card (\<Union>i \<in> {0..<length D}. Bi i)"
        by (subst card_UN_disjoint) (auto simp: finBi disjBi)
      also have "\<dots> \<le> card {0..<length Br}"
        using UNsub by (intro card_mono) auto
      also have "\<dots> \<le> length Br" by simp
      finally show ?thesis .
    qed

    text \<open>Relabelling each branch target of a transition by its MEC index (keeping probabilities) is
      the multiset @{const rmt}, and doing so distribution-wise is @{term \<open>map_pmf mec_of\<close>} of the
      transition pmf.\<close>
    lemma mset_remap_pmf_list:
      assumes t: "t < length Tr - Suc 0"
      shows "mset (map (\<lambda>(v, p). (op_mec_index_of D v, p)) (pmf_list t)) = rmt t"
    proof -
      have bnd: "\<And>b. b \<in> sn_intv (TrI ! t) \<Longrightarrow> b < min (length Br) (length Pr)"
        using t Br_in_bound_intvD by (auto simp: sn_intv_def)
      have "mset (map (\<lambda>(v, p). (op_mec_index_of D v, p)) (pmf_list t))
          = image_mset ((\<lambda>(v, p). (op_mec_index_of D v, p)) \<circ> (!) (zip Br Pr)) (mset_set (sn_intv (TrI ! t)))"
        by (simp add: mset_map ls_intv_def sn_intv_eq mset_upt)
      also have "\<dots> = image_mset (\<lambda>b. (op_mec_index_of D (Br ! b), Pr ! b)) (mset_set (sn_intv (TrI ! t)))"
      proof (rule image_mset_cong)
        fix b assume "b \<in># mset_set (sn_intv (TrI ! t))"
        then have "b \<in> sn_intv (TrI ! t)" by simp
        then have "b < length Br" "b < length Pr" using bnd by auto
        then show "((\<lambda>(v, p). (op_mec_index_of D v, p)) \<circ> (!) (zip Br Pr)) b = (op_mec_index_of D (Br ! b), Pr ! b)"
          by (simp add: nth_zip)
      qed
      finally show ?thesis by (simp add: rmt_def)
    qed

    lemma pmf_bridge:
      assumes t: "t < length Tr - Suc 0"
      shows "map_pmf mec_of (Tr_to_pmf t) = pmf_of_list (map (\<lambda>(v, p). (op_mec_index_of D v, p)) (pmf_list t))"
      using map_pmf_of_list[OF pmf_list_wf[OF t], of mec_of]
      by (simp add: Tr_to_pmf_def flip: mec_of_op_index)

    text \<open>The concrete leaving-test coincides with the abstract notion: transition @{term t} leaves MEC
      @{term i} iff its distribution's support is not contained in the class @{term \<open>D ! i\<close>}.\<close>
    lemma trans_leaves_iff:
      assumes t: "t < length Tr - Suc 0" and i: "i < length D"
      shows "trans_leaves i t \<longleftrightarrow> \<not> set_pmf (Tr_to_pmf t) \<subseteq> D ! i"
    proof -
      have sp: "set_pmf (Tr_to_pmf t) = (!) Br ` sn_intv (TrI ! t)" using t by (rule set_pmf_Tr_to_pmf)
      have bN: "\<And>b. b \<in> sn_intv (TrI ! t) \<Longrightarrow> Br ! b < N"
        using t by (auto simp: sn_intv_def intro: Br_in_bound Br_in_bound_intvD)
      show ?thesis
        unfolding trans_leaves_def sp
        using i bN by (auto simp: ls_intv_def sn_intv_eq mec_of_op_index in_D_iff_mec_of)
    qed

    text \<open>The built MDP's actions at a compute MEC @{term j} are exactly the leaving-transition
      distributions relabelled by MEC index: each block slot reads back one of MEC @{term j}'s rows,
      which by the pmf bridge is @{term \<open>map_pmf mec_of (Tr_to_pmf t)\<close>} for the corresponding leaving
      transition @{term t}.\<close>
    lemma built_actions_compute:
      assumes P: "built_post St' Tr' Br' Pr' Av' Ta'"
      assumes j: "j < length D" and NT: "\<not> is_target_mec j" and NA: "\<not> out_avoid j"
      shows "modest_mdp_input_def.St_to_pmfs (length D) St' Tr' Br' Av' Ta' Pr' j
             = (\<lambda>t. map_pmf mec_of (Tr_to_pmf t)) ` ltfull j"
    proof -
      interpret B: modest_mdp_input_invar "length D" St' Tr' Br' Pr' Av' Ta'
        using built_input_invar[OF P] .
      from P have LSt: "length St' = length D + 1" and LTr: "length Tr' = cnt_T + 1"
        and LBr: "length Br' = cnt_B" and LPr: "length Pr' = cnt_B"
        and StN: "\<forall>j\<le>length D. St' ! j = ctA j"
        and AvE: "Av' = {j. j < length D \<and> out_avoid j}"
        and TaE: "Ta' = {j. j < length D \<and> is_target_mec j}"
        and TrB: "\<forall>s\<le>cnt_T. Tr' ! s \<le> cnt_B"
        and segR: "\<forall>j<length D. seg Tr' Br' Pr' ` {ctA j..<ctA (Suc j)} = rowset j"
        by (simp_all add: built_post_def)
      have jCm: "j \<in> B.Cm"
      proof -
        have "j \<notin> Av'" using NA AvE by simp
        moreover have "j \<notin> Ta'" using NT TaE by simp
        ultimately show ?thesis using j by (simp add: B.Cm_mem)
      qed
      have blk: "sn_intv (B.StI ! j) = {ctA j..<ctA (Suc j)}"
      proof -
        have "j < length St' - Suc 0" using j LSt by simp
        then have "sn_intv (B.StI ! j) = {St' ! j..<St' ! Suc j}"
          using B.sorted_St by (simp add: sn_intv_sorted_intvs)
        then show ?thesis using StN j by simp
      qed
      have blk_lt: "\<And>s. s \<in> {ctA j..<ctA (Suc j)} \<Longrightarrow> s < cnt_T"
        using j ctA_le_cnt_T[of "Suc j"] by auto
      have rs: "rowset j = rmt ` ltfull j" using NT NA by (simp add: rowset_def)
      \<comment> \<open>The per-slot pmf readback: a slot whose row is @{term \<open>rmt t\<close>} reads back as the relabelled
        transition pmf.\<close>
      have bridge_st: "\<And>s t. s < cnt_T \<Longrightarrow> t \<in> ltfull j \<Longrightarrow> seg Tr' Br' Pr' s = rmt t
          \<Longrightarrow> B.Tr_to_pmf s = map_pmf mec_of (Tr_to_pmf t)"
      proof -
        fix s t assume scT: "s < cnt_T" and t: "t \<in> ltfull j" and st: "seg Tr' Br' Pr' s = rmt t"
        have sTr: "s < length Tr' - Suc 0" using scT LTr by simp
        have tTr: "t < length Tr - Suc 0" using t by (rule ltfull_real_trans)
        have msetBs: "mset (B.pmf_list s) = seg Tr' Br' Pr' s"
        proof -
          have ls: "ls_intv (B.TrI ! s) = [Tr' ! s..<Tr' ! Suc s]"
            using B.sorted_Tr sTr by (simp add: ls_intv_sorted_intvs)
          have "\<And>c. c \<in> {Tr' ! s..<Tr' ! Suc s} \<Longrightarrow> c < min (length Br') (length Pr')"
          proof -
            fix c assume "c \<in> {Tr' ! s..<Tr' ! Suc s}"
            then have "c < Tr' ! Suc s" by simp
            also have "Tr' ! Suc s \<le> cnt_B" using TrB scT by simp
            finally show "c < min (length Br') (length Pr')" using LBr LPr by simp
          qed
          then show ?thesis
            by (simp add: ls mset_map mset_upt seg_def)
               (rule image_mset_cong, auto)
        qed
        have "B.Tr_to_pmf s = pmf_of_list (B.pmf_list s)" by (simp add: B.Tr_to_pmf_def)
        also have "\<dots> = pmf_of_list (map (\<lambda>(v, p). (op_mec_index_of D v, p)) (pmf_list t))"
        proof (rule pmf_of_list_cong_mset[OF B.pmf_list_wf[OF sTr]])
          have "mset (B.pmf_list s) = seg Tr' Br' Pr' s" by (rule msetBs)
          also have "\<dots> = rmt t" by (rule st)
          also have "\<dots> = mset (map (\<lambda>(v, p). (op_mec_index_of D v, p)) (pmf_list t))"
            by (rule mset_remap_pmf_list[OF tTr, symmetric])
          finally show "mset (B.pmf_list s) = mset (map (\<lambda>(v, p). (op_mec_index_of D v, p)) (pmf_list t))" .
        qed
        also have "\<dots> = map_pmf mec_of (Tr_to_pmf t)" using pmf_bridge[OF tTr] by simp
        finally show "B.Tr_to_pmf s = map_pmf mec_of (Tr_to_pmf t)" .
      qed
      have "B.St_to_pmfs j = B.Tr_to_pmf ` {ctA j..<ctA (Suc j)}"
        using jCm blk by (simp add: B.St_to_pmfs_nta)
      also have "\<dots> = (\<lambda>t. map_pmf mec_of (Tr_to_pmf t)) ` ltfull j"
      proof (intro Set.equalityI subsetI)
        fix p assume "p \<in> B.Tr_to_pmf ` {ctA j..<ctA (Suc j)}"
        then obtain s where sblk: "s \<in> {ctA j..<ctA (Suc j)}" and ps: "p = B.Tr_to_pmf s" by blast
        have "seg Tr' Br' Pr' s \<in> rowset j" using segR j sblk by blast
        then obtain t where t: "t \<in> ltfull j" and st: "seg Tr' Br' Pr' s = rmt t" using rs by auto
        show "p \<in> (\<lambda>t. map_pmf mec_of (Tr_to_pmf t)) ` ltfull j"
          using ps bridge_st[OF blk_lt[OF sblk] t st] t by blast
      next
        fix p assume "p \<in> (\<lambda>t. map_pmf mec_of (Tr_to_pmf t)) ` ltfull j"
        then obtain t where t: "t \<in> ltfull j" and pt: "p = map_pmf mec_of (Tr_to_pmf t)" by blast
        have "rmt t \<in> rowset j" using rs t by blast
        then have "rmt t \<in> seg Tr' Br' Pr' ` {ctA j..<ctA (Suc j)}" using segR j by simp
        then obtain s where sblk: "s \<in> {ctA j..<ctA (Suc j)}" and st: "seg Tr' Br' Pr' s = rmt t" by auto
        show "p \<in> B.Tr_to_pmf ` {ctA j..<ctA (Suc j)}"
          using pt bridge_st[OF blk_lt[OF sblk] t st] sblk by (metis imageI)
      qed
      finally show ?thesis .
    qed

    text \<open>Concrete unfolding of the collapsed MDP's outer actions: relabel each member state's actions by
      @{const col}. Two collapsed states coincide iff their MEC indices do.\<close>
    lemma to_mdpc_collapse: "to_mdpc (M_mec \<M>_\<alpha>) = map_mdpc col M\<^sub>0_\<alpha>"
      by (simp add: Mmec_unfold to_mdpc.abs_eq)

    lemma col_inj_iff:
      assumes u: "u < N" and v: "v < N"
      shows "(col v = col u) = (mec_of v = mec_of u)"
    proof
      assume "col v = col u"
      then have "D ! mec_of v = D ! mec_of u" unfolding col_def by (metis states_mec_mdp)
      then show "mec_of v = mec_of u" using u v mec_of_lt distinct_D by (metis nth_eq_iff_index_eq)
    next
      assume "mec_of v = mec_of u" then show "col v = col u" by (simp add: col_def)
    qed

    lemma actions_collapse_members:
      assumes u: "u < N"
      shows "actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) = (\<Union>v\<in>D ! mec_of u. map_pmf col ` St_to_pmfs v)"
    proof -
      have jlt: "mec_of u < length D" using u by (rule mec_of_lt)
      have "actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) = (\<Union>t\<in>col -` {col u}. map_pmf col ` actions M\<^sub>0_\<alpha> t)"
        unfolding to_mdpc_collapse by (simp add: actions_map_mdpc image_UN)
      also have "\<dots> = (\<Union>v\<in>D ! mec_of u. map_pmf col ` St_to_pmfs v)"
      proof (intro Set.equalityI subsetI)
        fix p assume "p \<in> (\<Union>t\<in>col -` {col u}. map_pmf col ` actions M\<^sub>0_\<alpha> t)"
        then obtain t where t: "col t = col u" and pt: "p \<in> map_pmf col ` actions M\<^sub>0_\<alpha> t" by auto
        from pt have "actions M\<^sub>0_\<alpha> t \<noteq> {}" by auto
        then have tN: "t < N" by (rule ne_actions_M\<^sub>0_\<alpha>)
        then have "t \<in> D ! mec_of u" using t u jlt by (auto simp: col_inj_iff in_D_iff_mec_of)
        then show "p \<in> (\<Union>v\<in>D ! mec_of u. map_pmf col ` St_to_pmfs v)"
          using pt tN by (auto simp: actions_M\<^sub>0_\<alpha>)
      next
        fix p assume "p \<in> (\<Union>v\<in>D ! mec_of u. map_pmf col ` St_to_pmfs v)"
        then obtain v where v: "v \<in> D ! mec_of u" and pv: "p \<in> map_pmf col ` St_to_pmfs v" by auto
        have vN: "v < N" using v jlt by auto
        then have cvu: "col v = col u" using v u jlt by (auto simp: col_inj_iff in_D_iff_mec_of)
        have pav: "p \<in> map_pmf col ` actions M\<^sub>0_\<alpha> v"
          using pv actions_M\<^sub>0_\<alpha>[OF vN] by simp
        have "v \<in> col -` {col u}" using cvu by simp
        with pav show "p \<in> (\<Union>t\<in>col -` {col u}. map_pmf col ` actions M\<^sub>0_\<alpha> t)" by blast
      qed
      finally show ?thesis .
    qed

    text \<open>The reduction's actions at a collapsed state: drop the self-loop on a non-bottom compute
      state, otherwise the pure self-loop.\<close>
    lemma to_mdpc_reduce_collapse:
      "to_mdpc (reduce (M_mec \<M>_\<alpha>))
       = map_actions (\<lambda>m a. if m \<in> computes (M_mec \<M>_\<alpha>) - bots (M_mec \<M>_\<alpha>) then a - {return_pmf m} else {return_pmf m})
           (to_mdpc (M_mec \<M>_\<alpha>))"
      by (simp add: reduce_def to_mdpc.abs_eq)

    lemma actions_reduce_collapse:
      assumes u: "u < N"
      shows "actions (to_mdpc (reduce (M_mec \<M>_\<alpha>))) (col u)
           = (if col u \<in> computes (M_mec \<M>_\<alpha>) - bots (M_mec \<M>_\<alpha>)
              then actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) - {return_pmf (col u)} else {return_pmf (col u)})"
    proof -
      have "col u \<in> states (to_mdpc (M_mec \<M>_\<alpha>))" using u by (simp add: states_collapse)
      then show ?thesis unfolding to_mdpc_reduce_collapse by simp
    qed

    text \<open>Under a non-avoid/non-target MEC, every member is a compute state and the collapsed state is a
      compute state of the (M_mec \<M>_\<alpha>).\<close>
    lemma members_Cm:
      assumes j: "j < length D" and NT: "\<not> is_target_mec j" and NA: "\<not> is_avoid_mec j" and v: "v \<in> D ! j"
      shows "v \<in> Cm"
    proof -
      have vN: "v < N" using v j mec_class_subs_N by auto
      have mj: "mec_of v = j" using v vN j in_D_iff_mec_of by auto
      have "v \<notin> Av" using NA vN mj by (auto simp: is_avoid_mec_def mec_of_op_index)
      moreover have "v \<notin> Ta" using NT vN mj by (auto simp: is_target_mec_def mec_of_op_index)
      ultimately show ?thesis using vN by (simp add: Cm_mem)
    qed

    lemma col_computes:
      assumes u: "u < N" and NT: "\<not> is_target_mec (mec_of u)" and NA: "\<not> is_avoid_mec (mec_of u)"
      shows "col u \<in> computes (M_mec \<M>_\<alpha>)"
    proof -
      have "col u \<in> states (M_mec \<M>_\<alpha>)" using u by (auto simp: states_collapse)
      moreover have "col u \<notin> avoids (M_mec \<M>_\<alpha>)"
      proof
        assume "col u \<in> avoids (M_mec \<M>_\<alpha>)"
        then obtain w where w: "w \<in> Av" and cw: "col u = col w" by (auto simp: avoids_collapse)
        from w have wN: "w < N" by (rule AvN)
        then have "mec_of w = mec_of u" using cw u by (simp add: col_inj_iff)
        then show False using NA w wN by (auto simp: is_avoid_mec_def mec_of_op_index)
      qed
      moreover have "col u \<notin> targets (M_mec \<M>_\<alpha>)"
      proof
        assume "col u \<in> targets (M_mec \<M>_\<alpha>)"
        then obtain w where w: "w \<in> Ta" and cw: "col u = col w" by (auto simp: targets_collapse)
        from w have wN: "w < N" by (rule TaN)
        then have "mec_of w = mec_of u" using cw u by (simp add: col_inj_iff)
        then show False using NT w wN by (auto simp: is_target_mec_def mec_of_op_index)
      qed
      ultimately show ?thesis unfolding computes_def by blast
    qed

    text \<open>The outer @{term \<open>idx_of D\<close>} relabelling: the indexed MDP's actions at @{term \<open>mec_of u\<close>} are
      the reduced (M_mec \<M>_\<alpha>)'s actions at @{term \<open>col u\<close>} pushed through @{term \<open>idx_of D\<close>} (which is
      injective on the (M_mec \<M>_\<alpha>) states, so the unique preimage of @{term \<open>mec_of u\<close>} is @{term \<open>col u\<close>}).\<close>
    lemma actions_toindex:
      assumes u: "u < N"
      shows "actions (to_mdpc (to_index (M_mec \<M>_\<alpha>) D)) (mec_of u)
           = map_pmf (idx_of D) ` (actions (to_mdpc (reduce (M_mec \<M>_\<alpha>))) (col u))"
    proof -
      have "actions (to_mdpc (to_index (M_mec \<M>_\<alpha>) D)) (mec_of u)
          = (\<Union>m\<in>idx_of D -` {mec_of u}. map_pmf (idx_of D) ` actions (to_mdpc (reduce (M_mec \<M>_\<alpha>))) m)"
        unfolding to_index_to_mdpc by (simp add: actions_map_mdpc image_UN)
      also have "\<dots> = map_pmf (idx_of D) ` (actions (to_mdpc (reduce (M_mec \<M>_\<alpha>))) (col u))"
      proof (intro Set.equalityI subsetI)
        fix p assume "p \<in> (\<Union>m\<in>idx_of D -` {mec_of u}. map_pmf (idx_of D) ` actions (to_mdpc (reduce (M_mec \<M>_\<alpha>))) m)"
        then obtain m where im: "idx_of D m = mec_of u"
          and pm: "p \<in> map_pmf (idx_of D) ` actions (to_mdpc (reduce (M_mec \<M>_\<alpha>))) m" by auto
        from pm have "actions (to_mdpc (reduce (M_mec \<M>_\<alpha>))) m \<noteq> {}" by auto
        then have "m \<in> states (to_mdpc (reduce (M_mec \<M>_\<alpha>)))" by (rule in_states)
        then have "m \<in> col ` {0..<N}" by (simp add: states_reduce states_collapse)
        then obtain w where wN: "w < N" and mw: "m = col w" by auto
        then have "mec_of w = mec_of u" using im by (simp add: idx_of_col)
        then have "m = col u" using mw wN u by (simp add: col_inj_iff)
        then show "p \<in> map_pmf (idx_of D) ` actions (to_mdpc (reduce (M_mec \<M>_\<alpha>))) (col u)" using pm by simp
      next
        fix p assume pc: "p \<in> map_pmf (idx_of D) ` actions (to_mdpc (reduce (M_mec \<M>_\<alpha>))) (col u)"
        have "idx_of D (col u) = mec_of u" using u by (rule idx_of_col)
        then show "p \<in> (\<Union>m\<in>idx_of D -` {mec_of u}. map_pmf (idx_of D) ` actions (to_mdpc (reduce (M_mec \<M>_\<alpha>))) m)"
          using pc by (auto simp: vimage_eq)
      qed
      finally show ?thesis .
    qed

    text \<open>A member transition's collapsed action is the MEC self-loop iff it does not leave the MEC.\<close>
    lemma set_pmf_Tr_sub_N:
      assumes t: "t < length Tr - Suc 0"
      shows "set_pmf (Tr_to_pmf t) \<subseteq> {0..<N}"
    proof (rule subsetI)
      fix y assume "y \<in> set_pmf (Tr_to_pmf t)"
      then obtain b where b: "in_intv (TrI ! t) b" and y: "y = Br ! b"
        using t by (auto simp: set_pmf_Tr_to_pmf sn_intv_def)
      from b have "b < length Br" by (rule Br_in_bound_intvD[OF t])
      then show "y \<in> {0..<N}" by (simp add: y Br_in_bound)
    qed

    lemma map_col_selfloop_iff:
      assumes v: "v < N" and t: "t \<in> sn_intv (StI ! v)"
      shows "(map_pmf col (Tr_to_pmf t) = return_pmf (col v)) = (\<not> trans_leaves (mec_of v) t)"
    proof -
      from v t have tTr: "t < length Tr - Suc 0" by (auto simp: sn_intv_def dest: Tr_in_bound_intvD)
      have sp: "set_pmf (Tr_to_pmf t) \<subseteq> {0..<N}"
        by (rule set_pmf_Tr_sub_N[OF tTr])
      have "(map_pmf col (Tr_to_pmf t) = return_pmf (col v)) = (\<forall>x\<in>set_pmf (Tr_to_pmf t). col x = col v)"
        by (simp add: map_pmf_eq_return_pmf_iff)
      also have "\<dots> = (set_pmf (Tr_to_pmf t) \<subseteq> D ! mec_of v)"
        using sp v by (auto simp: col_inj_iff in_D_iff_mec_of mec_of_lt subset_eq)
      also have "\<dots> = (\<not> trans_leaves (mec_of v) t)"
        using trans_leaves_iff[OF tTr mec_of_lt[OF v]] by blast
      finally show ?thesis .
    qed

    text \<open>The member states of MEC @{term j} are exactly the class @{term \<open>D ! j\<close>}.\<close>
    lemma mec_index_set:
      assumes j: "j < length D"
      shows "{u \<in> {0..<N}. op_mec_index_of D u = j} = D ! j"
    proof (intro Set.equalityI subsetI)
      fix u assume "u \<in> {u \<in> {0..<N}. op_mec_index_of D u = j}"
      then have "u < N" "mec_of u = j" by (auto simp: mec_of_op_index)
      then show "u \<in> D ! j" using j in_D_iff_mec_of by auto
    next
      fix u assume u: "u \<in> D ! j"
      then have uN: "u < N" using j mec_class_subs_N by auto
      then have "mec_of u = j" using u j in_D_iff_mec_of by auto
      then show "u \<in> {u \<in> {0..<N}. op_mec_index_of D u = j}" using uN by (auto simp: mec_of_op_index)
    qed

    text \<open>The bottom-MEC bridge: a compute MEC's collapsed state is a self-loop-only (bottom) state iff
      the concrete leaving-transition count @{term \<open>tc j\<close>} is zero.\<close>
    lemma tc_zero_iff:
      assumes j: "j < length D"
      shows "(tc j = 0) = (\<forall>v\<in>D ! j. lvt j v = {})"
    proof -
      have finDj: "finite (D ! j)" using j mec_class_subs_N finite_subset by blast
      have "tc j = (\<Sum>v\<in>D ! j. card (lvt j v))"
        unfolding tc_def by (rule sum.cong[OF mec_index_set[OF j] refl])
      then show ?thesis using finDj by (simp add: sum_eq_0_iff card_eq_0_iff)
    qed

    lemma selfloop_iff_tc:
      assumes u: "u < N" and NT: "\<not> is_target_mec (mec_of u)" and NA: "\<not> is_avoid_mec (mec_of u)"
      shows "(actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) = {return_pmf (col u)}) = (tc (mec_of u) = 0)"
    proof -
      have jlt: "mec_of u < length D" using u by (rule mec_of_lt)
      have acts: "actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u)
          = (\<Union>v\<in>D ! mec_of u. map_pmf col ` (Tr_to_pmf ` sn_intv (StI ! v)))"
      proof -
        have "actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) = (\<Union>v\<in>D ! mec_of u. map_pmf col ` St_to_pmfs v)"
          using u by (rule actions_collapse_members)
        also have "\<dots> = (\<Union>v\<in>D ! mec_of u. map_pmf col ` (Tr_to_pmf ` sn_intv (StI ! v)))"
          using jlt NT NA members_Cm by (auto simp: St_to_pmfs_nta)
        finally show ?thesis .
      qed
      have vN: "\<And>v. v \<in> D ! mec_of u \<Longrightarrow> v < N" using jlt by auto
      have colv: "\<And>v. v \<in> D ! mec_of u \<Longrightarrow> col v = col u"
      proof -
        fix v assume v: "v \<in> D ! mec_of u"
        have "v < N" by (rule mem_D_less_N[OF v jlt])
        then show "col v = col u" using v u jlt by (simp add: col_inj_iff in_D_iff_mec_of)
      qed
      have mecv: "\<And>v. v \<in> D ! mec_of u \<Longrightarrow> mec_of v = mec_of u"
      proof -
        fix v assume v: "v \<in> D ! mec_of u"
        have "v < N" by (rule mem_D_less_N[OF v jlt])
        then show "mec_of v = mec_of u" using v jlt by (simp add: in_D_iff_mec_of)
      qed
      have DjNE: "D ! mec_of u \<noteq> {}"
        using jlt set_D nth_mem mec_class_ne by (metis atLeastLessThan_iff)
      then obtain v0 where v0: "v0 \<in> D ! mec_of u" by blast
      have ne: "actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) \<noteq> {}"
      proof -
        have "St_to_pmfs v0 \<noteq> {}" using vN[OF v0] by (rule St_to_pmfs_ne)
        then show ?thesis using v0 by (auto simp: actions_collapse_members[OF u])
      qed
      have selfloop: "\<And>v t. v \<in> D ! mec_of u \<Longrightarrow> t \<in> sn_intv (StI ! v)
          \<Longrightarrow> (map_pmf col (Tr_to_pmf t) = return_pmf (col u)) = (\<not> trans_leaves (mec_of u) t)"
        using colv mecv vN map_col_selfloop_iff by metis
      have "(actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) = {return_pmf (col u)})
          = (\<forall>p\<in>actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u). p = return_pmf (col u))"
        using ne by fastforce
      also have "\<dots> = (\<forall>v\<in>D ! mec_of u. \<forall>t\<in>sn_intv (StI ! v). \<not> trans_leaves (mec_of u) t)"
        unfolding acts using selfloop by blast
      also have "\<dots> = (\<forall>v\<in>D ! mec_of u. lvt (mec_of u) v = {})" by (auto simp: lvt_def)
      also have "\<dots> = (tc (mec_of u) = 0)" using tc_zero_iff[OF jlt] by blast
      finally show ?thesis .
    qed

    text \<open>Composing the two relabellings: @{term \<open>idx_of D \<circ> col\<close>} on a transition's support is
      @{const mec_of}.\<close>
    lemma map_idx_col:
      assumes t: "t < length Tr - Suc 0"
      shows "map_pmf (idx_of D) (map_pmf col (Tr_to_pmf t)) = map_pmf mec_of (Tr_to_pmf t)"
    proof -
      have sp: "set_pmf (Tr_to_pmf t) \<subseteq> {0..<N}"
        by (rule set_pmf_Tr_sub_N[OF t])
      have "map_pmf (idx_of D) (map_pmf col (Tr_to_pmf t)) = map_pmf (idx_of D \<circ> col) (Tr_to_pmf t)"
        by (simp add: pmf.map_comp)
      also have "\<dots> = map_pmf mec_of (Tr_to_pmf t)"
        using sp by (auto intro!: map_pmf_cong simp: idx_of_col)
      finally show ?thesis .
    qed

    lemma ltfull_eq:
      assumes j: "j < length D"
      shows "ltfull j = (\<Union>v\<in>D ! j. lvt j v)"
      unfolding ltfull_def ltdone_def using mec_index_set[OF j] by auto

    text \<open>The indexed MDP's actions at a compute MEC: the leaving-transition distributions relabelled by
      MEC index --- the same set @{thm [source] built_actions_compute} produces for the built MDP.\<close>
    lemma toindex_actions_compute:
      assumes u: "u < N" and NT: "\<not> is_target_mec (mec_of u)" and NA: "\<not> is_avoid_mec (mec_of u)"
        and NB: "tc (mec_of u) \<noteq> 0"
      shows "actions (to_mdpc (to_index (M_mec \<M>_\<alpha>) D)) (mec_of u)
             = (\<lambda>t. map_pmf mec_of (Tr_to_pmf t)) ` ltfull (mec_of u)"
    proof -
      let ?j = "mec_of u"
      have jlt: "?j < length D" using u by (rule mec_of_lt)
      have acts: "actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u)
          = (\<Union>v\<in>D ! ?j. map_pmf col ` (Tr_to_pmf ` sn_intv (StI ! v)))"
      proof -
        have "actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) = (\<Union>v\<in>D ! ?j. map_pmf col ` St_to_pmfs v)"
          using u by (rule actions_collapse_members)
        also have "\<dots> = (\<Union>v\<in>D ! ?j. map_pmf col ` (Tr_to_pmf ` sn_intv (StI ! v)))"
          using jlt NT NA members_Cm by (auto simp: St_to_pmfs_nta)
        finally show ?thesis .
      qed
      have selfloop: "\<And>v t. v \<in> D ! ?j \<Longrightarrow> t \<in> sn_intv (StI ! v)
          \<Longrightarrow> (map_pmf col (Tr_to_pmf t) = return_pmf (col u)) = (\<not> trans_leaves ?j t)"
      proof -
        fix v t assume vD: "v \<in> D ! ?j" and tsn: "t \<in> sn_intv (StI ! v)"
        have vN: "v < N" using vD jlt by auto
        then have mv: "mec_of v = ?j" using vD jlt by (simp add: in_D_iff_mec_of)
        then have "col v = col u" using vN u by (simp add: col_inj_iff)
        then show "(map_pmf col (Tr_to_pmf t) = return_pmf (col u)) = (\<not> trans_leaves ?j t)"
          using map_col_selfloop_iff[OF vN tsn] mv by simp
      qed
      have real: "\<And>v t. v \<in> D ! ?j \<Longrightarrow> t \<in> sn_intv (StI ! v) \<Longrightarrow> t < length Tr - Suc 0"
        using jlt mec_class_subs_N by (auto simp: sn_intv_def dest: Tr_in_bound_intvD)
      have cc: "col u \<in> computes (M_mec \<M>_\<alpha>)" using u NT NA by (rule col_computes)
      have "actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) \<noteq> {return_pmf (col u)}"
        using u NT NA NB by (simp add: selfloop_iff_tc)
      then have cb: "col u \<in> computes (M_mec \<M>_\<alpha>) - bots (M_mec \<M>_\<alpha>)" using cc by (auto simp: bots_def)
      have "actions (to_mdpc (to_index (M_mec \<M>_\<alpha>) D)) ?j
          = map_pmf (idx_of D) ` (actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) - {return_pmf (col u)})"
        using u cb by (simp add: actions_toindex actions_reduce_collapse)
      also have "\<dots> = (\<lambda>t. map_pmf mec_of (Tr_to_pmf t)) ` ltfull ?j"
      proof (intro Set.equalityI subsetI)
        fix p assume "p \<in> map_pmf (idx_of D) ` (actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) - {return_pmf (col u)})"
        then obtain a where a: "a \<in> actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u)" and ane: "a \<noteq> return_pmf (col u)"
          and pa: "p = map_pmf (idx_of D) a" by blast
        from a acts obtain v t where v: "v \<in> D ! ?j" and t: "t \<in> sn_intv (StI ! v)"
          and av: "a = map_pmf col (Tr_to_pmf t)" by blast
        have "trans_leaves ?j t" using ane av selfloop[OF v t] by simp
        then have "t \<in> lvt ?j v" using t by (simp add: lvt_def)
        then have "t \<in> ltfull ?j" using v ltfull_eq[OF jlt] by blast
        moreover have "p = map_pmf mec_of (Tr_to_pmf t)" using pa av map_idx_col[OF real[OF v t]] by simp
        ultimately show "p \<in> (\<lambda>t. map_pmf mec_of (Tr_to_pmf t)) ` ltfull ?j" by blast
      next
        fix p assume "p \<in> (\<lambda>t. map_pmf mec_of (Tr_to_pmf t)) ` ltfull ?j"
        then obtain t where t: "t \<in> ltfull ?j" and pt: "p = map_pmf mec_of (Tr_to_pmf t)" by blast
        from t ltfull_eq[OF jlt] obtain v where v: "v \<in> D ! ?j" and tv: "t \<in> lvt ?j v" by blast
        then have tsn: "t \<in> sn_intv (StI ! v)" and tl: "trans_leaves ?j t" by (auto simp: lvt_def)
        have "map_pmf col (Tr_to_pmf t) \<noteq> return_pmf (col u)" using tl selfloop[OF v tsn] by simp
        moreover have "map_pmf col (Tr_to_pmf t) \<in> actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u)"
          using v tsn acts by blast
        moreover have "p = map_pmf (idx_of D) (map_pmf col (Tr_to_pmf t))"
          using pt map_idx_col[OF real[OF v tsn]] by simp
        ultimately show "p \<in> map_pmf (idx_of D) ` (actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) - {return_pmf (col u)})"
          by blast
      qed
      finally show ?thesis .
    qed

    text \<open>A sink MEC's collapsed state is not a live compute state, so the reduction gives it a pure
      self-loop.\<close>
    lemma col_not_compute_bot:
      assumes u: "u < N" and S: "is_target_mec (mec_of u) \<or> out_avoid (mec_of u)"
      shows "col u \<notin> computes (M_mec \<M>_\<alpha>) - bots (M_mec \<M>_\<alpha>)"
    proof -
      consider (T) "is_target_mec (mec_of u)"
        | (A) "\<not> is_target_mec (mec_of u)" "is_avoid_mec (mec_of u)"
        | (B) "\<not> is_target_mec (mec_of u)" "\<not> is_avoid_mec (mec_of u)" "tc (mec_of u) = 0"
        using S by (auto simp: out_avoid_def)
      then show ?thesis
      proof cases
        case T
        then obtain w where w: "op_mec_index_of D w = mec_of u" "w \<in> Ta" by (auto simp: is_target_mec_def)
        have "w < N" using w(2) by (rule TaN)
        then have "col w = col u" using w(1) u by (simp add: mec_of_op_index col_inj_iff)
        then have "col u \<in> targets (M_mec \<M>_\<alpha>)" using w(2) by (metis targets_collapse imageI)
        then show ?thesis unfolding computes_def by blast
      next
        case A
        then obtain w where w: "op_mec_index_of D w = mec_of u" "w \<in> Av" by (auto simp: is_avoid_mec_def)
        have "w < N" using w(2) by (rule AvN)
        then have "col w = col u" using w(1) u by (simp add: mec_of_op_index col_inj_iff)
        then have "col u \<in> avoids (M_mec \<M>_\<alpha>)" using w(2) by (metis avoids_collapse imageI)
        then show ?thesis unfolding computes_def by blast
      next
        case B
        have "col u \<in> computes (M_mec \<M>_\<alpha>)" using u B(1,2) by (rule col_computes)
        moreover have "actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) = {return_pmf (col u)}"
          using u B by (simp add: selfloop_iff_tc)
        ultimately show ?thesis by (auto simp: bots_def)
      qed
    qed

    lemma toindex_actions_sink:
      assumes j: "j < length D" and S: "is_target_mec j \<or> out_avoid j"
      shows "actions (to_mdpc (to_index (M_mec \<M>_\<alpha>) D)) j = {return_pmf j}"
    proof -
      from j have "j \<in> mec_of ` {0..<N}" by (simp add: mec_of_onto)
      then obtain u where u: "u < N" and ju: "mec_of u = j" by auto
      have "col u \<notin> computes (M_mec \<M>_\<alpha>) - bots (M_mec \<M>_\<alpha>)" using u S ju by (metis col_not_compute_bot)
      then have "actions (to_mdpc (reduce (M_mec \<M>_\<alpha>))) (col u) = {return_pmf (col u)}"
        by (auto simp: actions_reduce_collapse[OF u])
      then have "actions (to_mdpc (to_index (M_mec \<M>_\<alpha>) D)) j = map_pmf (idx_of D) ` {return_pmf (col u)}"
        using ju actions_toindex[OF u] by simp
      also have "\<dots> = {return_pmf j}" using u ju by (simp add: idx_of_col)
      finally show ?thesis .
    qed

    lemma states_toindex: "states (to_mdpc (to_index (M_mec \<M>_\<alpha>) D)) = {0..<length D}"
    proof -
      have "states (to_mdpc (to_index (M_mec \<M>_\<alpha>) D)) = idx_of D ` (col ` {0..<N})"
        unfolding to_index_to_mdpc by (simp add: states_reduce states_collapse)
      also have "\<dots> = (\<lambda>u. idx_of D (col u)) ` {0..<N}" by (simp add: image_image)
      also have "\<dots> = mec_of ` {0..<N}" by (rule image_cong[OF refl]) (simp add: idx_of_col)
      also have "\<dots> = {0..<length D}" by (rule mec_of_onto)
      finally show ?thesis .
    qed

    text \<open>Membership of a collapsed state in the collapsed MDP's computes/avoids/targets, in terms of the
      MEC classification.\<close>
    lemma computes_iff:
      assumes u: "u < N"
      shows "(col u \<in> computes (M_mec \<M>_\<alpha>)) = (\<not> is_avoid_mec (mec_of u) \<and> \<not> is_target_mec (mec_of u))"
    proof -
      have st: "col u \<in> states (M_mec \<M>_\<alpha>)" using u by (auto simp: states_collapse)
      have av: "(col u \<in> avoids (M_mec \<M>_\<alpha>)) = is_avoid_mec (mec_of u)"
      proof
        assume "col u \<in> avoids (M_mec \<M>_\<alpha>)"
        then obtain w where "w \<in> Av" "col u = col w" by (auto simp: avoids_collapse)
        then show "is_avoid_mec (mec_of u)" using u AvN by (auto simp: col_inj_iff is_avoid_mec_def mec_of_op_index)
      next
        assume "is_avoid_mec (mec_of u)"
        then obtain w where w: "op_mec_index_of D w = mec_of u" "w \<in> Av" by (auto simp: is_avoid_mec_def)
        have "w < N" using w(2) by (rule AvN)
        then have "col w = col u" using w(1) u by (simp add: mec_of_op_index col_inj_iff)
        then show "col u \<in> avoids (M_mec \<M>_\<alpha>)" using w(2) by (metis avoids_collapse imageI)
      qed
      have ta: "(col u \<in> targets (M_mec \<M>_\<alpha>)) = is_target_mec (mec_of u)"
      proof
        assume "col u \<in> targets (M_mec \<M>_\<alpha>)"
        then obtain w where "w \<in> Ta" "col u = col w" by (auto simp: targets_collapse)
        then show "is_target_mec (mec_of u)" using u TaN by (auto simp: col_inj_iff is_target_mec_def mec_of_op_index)
      next
        assume "is_target_mec (mec_of u)"
        then obtain w where w: "op_mec_index_of D w = mec_of u" "w \<in> Ta" by (auto simp: is_target_mec_def)
        have "w < N" using w(2) by (rule TaN)
        then have "col w = col u" using w(1) u by (simp add: mec_of_op_index col_inj_iff)
        then show "col u \<in> targets (M_mec \<M>_\<alpha>)" using w(2) by (metis targets_collapse imageI)
      qed
      from st av ta show ?thesis unfolding computes_def by blast
    qed

    lemma idx_inj: "inj_on (idx_of D) (states (M_mec \<M>_\<alpha>))"
    proof (rule inj_onI)
      fix x y assume "x \<in> states (M_mec \<M>_\<alpha>)" "y \<in> states (M_mec \<M>_\<alpha>)" "idx_of D x = idx_of D y"
      then obtain u v where "u < N" "x = col u" "v < N" "y = col v" by (auto simp: states_collapse)
      then show "x = y" using \<open>idx_of D x = idx_of D y\<close> by (simp add: idx_of_col col_inj_iff)
    qed

    lemma idx_col_Ta: "idx_of D ` (col ` Ta) = {j. j < length D \<and> is_target_mec j}"
      using targets_reduce_collapse by (simp add: targets_reduce targets_collapse)

    lemma idx_col_Av: "idx_of D ` (col ` Av) = {j. j < length D \<and> is_avoid_mec j}"
    proof -
      have "idx_of D ` (col ` Av) = mec_of ` Av" by (auto simp: image_image idx_of_col AvN cong: image_cong)
      also have "\<dots> = {j. j < length D \<and> is_avoid_mec j}"
      proof (intro Set.equalityI subsetI)
        fix j assume "j \<in> mec_of ` Av"
        then obtain w where w: "w \<in> Av" "j = mec_of w" by auto
        then have "w < N" using AvN by simp
        then show "j \<in> {j. j < length D \<and> is_avoid_mec j}"
          using w mec_of_lt by (auto simp: is_avoid_mec_def mec_of_op_index)
      next
        fix j assume "j \<in> {j. j < length D \<and> is_avoid_mec j}"
        then obtain w where "w \<in> {0..<N}" "op_mec_index_of D w = j" "w \<in> Av" by (auto simp: is_avoid_mec_def)
        then show "j \<in> mec_of ` Av" by (auto simp: mec_of_op_index)
      qed
      finally show ?thesis .
    qed

    lemma idx_bots:
      "idx_of D ` bots (M_mec \<M>_\<alpha>) = {j. j < length D \<and> \<not> is_target_mec j \<and> \<not> is_avoid_mec j \<and> tc j = 0}"
    proof (intro Set.equalityI subsetI)
      fix j assume "j \<in> idx_of D ` bots (M_mec \<M>_\<alpha>)"
      then obtain m where m: "m \<in> bots (M_mec \<M>_\<alpha>)" and jm: "j = idx_of D m" by blast
      from m have "m \<in> states (M_mec \<M>_\<alpha>)" unfolding bots_def computes_def by blast
      then obtain u where u: "u < N" and mu: "m = col u" by (auto simp: states_collapse)
      have ju: "j = mec_of u" using jm mu u by (simp add: idx_of_col)
      have NTA: "\<not> is_avoid_mec (mec_of u) \<and> \<not> is_target_mec (mec_of u)"
        using m mu u by (auto simp: bots_def computes_iff)
      have "actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) = {return_pmf (col u)}" using m mu by (simp add: bots_def)
      then have "tc (mec_of u) = 0" using u NTA by (simp add: selfloop_iff_tc)
      then show "j \<in> {j. j < length D \<and> \<not> is_target_mec j \<and> \<not> is_avoid_mec j \<and> tc j = 0}"
        using ju u mec_of_lt NTA by auto
    next
      fix j assume "j \<in> {j. j < length D \<and> \<not> is_target_mec j \<and> \<not> is_avoid_mec j \<and> tc j = 0}"
      then have jlt: "j < length D" and NT: "\<not> is_target_mec j" and NA: "\<not> is_avoid_mec j" and tc0: "tc j = 0"
        by auto
      from jlt have "j \<in> mec_of ` {0..<N}" by (simp add: mec_of_onto)
      then obtain u where u: "u < N" and ju: "mec_of u = j" by auto
      have "col u \<in> computes (M_mec \<M>_\<alpha>)" using u NT NA ju by (simp add: col_computes)
      moreover have "actions (to_mdpc (M_mec \<M>_\<alpha>)) (col u) = {return_pmf (col u)}"
        using u NT NA tc0 ju by (simp add: selfloop_iff_tc)
      ultimately have "col u \<in> bots (M_mec \<M>_\<alpha>)" by (auto simp: bots_def)
      then show "j \<in> idx_of D ` bots (M_mec \<M>_\<alpha>)" using u ju by (auto simp: idx_of_col rev_image_eqI)
    qed

    text \<open>The avoid index set of the reduction: avoid MECs plus bottom (leaving-free) MECs, minus target
      MECs --- exactly @{const out_avoid}.\<close>
    lemma avoids_reduce_collapse: "idx_of D ` avoids (reduce (M_mec \<M>_\<alpha>)) = {j. j < length D \<and> out_avoid j}"
    proof -
      have sAv: "col ` Av \<subseteq> states (M_mec \<M>_\<alpha>)" using AN by (auto simp: states_collapse)
      have sTa: "col ` Ta \<subseteq> states (M_mec \<M>_\<alpha>)" using TN by (auto simp: states_collapse)
      have sB: "bots (M_mec \<M>_\<alpha>) \<subseteq> states (M_mec \<M>_\<alpha>)" unfolding bots_def computes_def by blast
      have avr: "avoids (reduce (M_mec \<M>_\<alpha>)) = (col ` Av \<union> bots (M_mec \<M>_\<alpha>)) - col ` Ta"
        by (simp add: avoids_reduce avoids_collapse targets_collapse)
      have sub: "(col ` Av \<union> bots (M_mec \<M>_\<alpha>)) \<subseteq> states (M_mec \<M>_\<alpha>)" using sAv sB by (rule Un_least)
      have sub2: "(col ` Av \<union> bots (M_mec \<M>_\<alpha>)) - col ` Ta \<subseteq> states (M_mec \<M>_\<alpha>)" using sub by auto
      have "idx_of D ` avoids (reduce (M_mec \<M>_\<alpha>))
          = idx_of D ` (col ` Av \<union> bots (M_mec \<M>_\<alpha>)) - idx_of D ` (col ` Ta)"
        unfolding avr by (rule inj_on_image_set_diff[OF idx_inj sub2 sTa])
      also have "\<dots> = (idx_of D ` (col ` Av) \<union> idx_of D ` bots (M_mec \<M>_\<alpha>)) - idx_of D ` (col ` Ta)"
        by (simp add: image_Un)
      also have "\<dots> = {j. j < length D \<and> out_avoid j}"
        by (auto simp: idx_col_Av idx_bots idx_col_Ta out_avoid_def)
      finally show ?thesis .
    qed

    text \<open>O2 (semantics): the built MDP is exactly the indexed max reduction of the collapsed MDP. Component
      by component (@{thm mdptc_eqI}): targets/avoids match the target/avoid-MEC index sets, and the
      inner MDP matches state-for-state --- a compute MEC's actions are the relabelled leaving
      transitions (@{thm [source] built_actions_compute} = @{thm [source] toindex_actions_compute}), a sink MEC's is a
      pure self-loop.\<close>
    lemma build_semantics:
      assumes P: "built_post St' Tr' Br' Pr' Av' Ta'"
      shows "modest_mdp_input_def.\<M>_\<alpha> (length D) St' Tr' Br' Av' Ta' Pr' = to_index (M_mec \<M>_\<alpha>) D"
    proof -
      interpret B: modest_mdp_input_invar "length D" St' Tr' Br' Pr' Av' Ta'
        using built_input_invar[OF P] .
      from P have AvE: "Av' = {j. j < length D \<and> out_avoid j}"
        and TaE: "Ta' = {j. j < length D \<and> is_target_mec j}" by (simp_all add: built_post_def)
      show ?thesis
      proof (rule mdptc_eqI)
        have "targets B.\<M>_\<alpha> = Ta'" by simp
        also have "\<dots> = idx_of D ` targets (reduce (M_mec \<M>_\<alpha>))"
          unfolding TaE by (rule targets_reduce_collapse[symmetric])
        also have "\<dots> = targets (to_index (M_mec \<M>_\<alpha>) D)" by (rule to_index_targets[symmetric])
        finally show "targets B.\<M>_\<alpha> = targets (to_index (M_mec \<M>_\<alpha>) D)" .
        have "avoids B.\<M>_\<alpha> = Av'" by simp
        also have "\<dots> = idx_of D ` avoids (reduce (M_mec \<M>_\<alpha>))"
          unfolding AvE by (rule avoids_reduce_collapse[symmetric])
        also have "\<dots> = avoids (to_index (M_mec \<M>_\<alpha>) D)" by (rule to_index_avoids[symmetric])
        finally show "avoids B.\<M>_\<alpha> = avoids (to_index (M_mec \<M>_\<alpha>) D)" .
        show "to_mdpc B.\<M>_\<alpha> = to_mdpc (to_index (M_mec \<M>_\<alpha>) D)"
        proof (rule mdpc_eqI)
          show "states (to_mdpc B.\<M>_\<alpha>) = states (to_mdpc (to_index (M_mec \<M>_\<alpha>) D))"
            by (simp add: B.states_M\<^sub>0_\<alpha> states_toindex)
        next
          fix j assume "j \<in> states (to_mdpc B.\<M>_\<alpha>)"
          then have j: "j < length D" by (simp add: B.states_M\<^sub>0_\<alpha>)
          have Bact: "actions (to_mdpc B.\<M>_\<alpha>) j = B.St_to_pmfs j" using j by (simp add: B.actions_M\<^sub>0_\<alpha>)
          show "actions (to_mdpc B.\<M>_\<alpha>) j = actions (to_mdpc (to_index (M_mec \<M>_\<alpha>) D)) j"
          proof (cases "is_target_mec j \<or> out_avoid j")
            case True
            then have "j \<in> Av' \<or> j \<in> Ta'" using j AvE TaE by auto
            then have "j \<notin> B.Cm" by (auto simp: B.Cm_mem)
            then have "B.St_to_pmfs j = {return_pmf j}" by (simp add: B.St_to_pmfs_def)
            moreover have "actions (to_mdpc (to_index (M_mec \<M>_\<alpha>) D)) j = {return_pmf j}"
              using j True by (rule toindex_actions_sink)
            ultimately show ?thesis using Bact by simp
          next
            case False
            then have NT: "\<not> is_target_mec j" and NOA: "\<not> out_avoid j" by auto
            from j have "j \<in> mec_of ` {0..<N}" by (simp add: mec_of_onto)
            then obtain u where u: "u < N" and ju: "mec_of u = j" by auto
            have "B.St_to_pmfs j = (\<lambda>t. map_pmf mec_of (Tr_to_pmf t)) ` ltfull j"
              using P j NT NOA by (rule built_actions_compute)
            moreover have "actions (to_mdpc (to_index (M_mec \<M>_\<alpha>) D)) j = (\<lambda>t. map_pmf mec_of (Tr_to_pmf t)) ` ltfull j"
              using u NT NOA ju toindex_actions_compute by (metis out_avoid_def)
            ultimately show ?thesis using Bact by simp
          qed
        qed
      qed
    qed

  end

  section \<open>The builder: five array passes (step 6)\<close>

  text \<open>An array-based (counting-sort / CSR-construction) state-space builder. Every pass is either a
    single sweep over the states \<^term>\<open>[0..<N]\<close> or an \<open>O(|D|)\<close> pass over \<^term>\<open>[0..<length D]\<close> ---
    never nested --- giving \<open>O(N + E + |D|)\<close> overall, as against the \<open>O(N \<cdot> |D|)\<close> of the obvious
    formulation that re-scans the whole state space once per MEC.

    All count / offset / cursor state is \<^typ>\<open>nat list\<close> (array-shaped, hence refinable to flat LLVM
    arrays); no \<^typ>\<open>nat \<Rightarrow> _\<close> function accumulators.

    The output is engineered to satisfy \<^const>\<open>modest_collapse_invar.built_post\<close> above, so the whole
    step-7 chain (@{thm [source] modest_collapse_invar.build_valid},
    @{thm [source] modest_collapse_invar.build_semantics}) applies to it verbatim: the only proof
    obligation specific to the builder is \<open>build_statespace'_post\<close> below.\<close>
  context modest_collapse_invar
  begin

    subsection \<open>The five passes\<close>

    text \<open>Pass 1 -- counting (single sweep over \<^term>\<open>[0..<N]\<close>). For each state \<^term>\<open>u\<close> with MEC index
      \<^term>\<open>c\<close>, accumulate its leaving transitions / branches into \<open>cntT!c\<close> / \<open>cntB!c\<close>, and record
      \<^term>\<open>c\<close> as a target / avoid MEC if \<^term>\<open>u\<close> is a target / avoid state. Matches \<^const>\<open>tc\<close> /
      \<^const>\<open>bc\<close> and \<^const>\<open>is_target_mec\<close> / \<^const>\<open>is_avoid_mec\<close>.\<close>
    definition "count_pass = do {
      let cntT = replicate (length D) 0;
      let cntB = replicate (length D) 0;
      (cntT, cntB, Ta', avm) \<leftarrow> FOREACH {0..<N}
        (\<lambda>u (cntT, cntB, Ta', avm). do {
           ASSERT (u < N);
           let c = op_mec_index_of D u;
           let Ta' = (if u \<in> Ta then insert c Ta' else Ta');
           let avm = (if u \<in> Av then insert c avm else avm);
           (cntT, cntB) \<leftarrow> FOREACH (sn_intv (StI ! u))
              (\<lambda>t (cntT, cntB). do {
                 ASSERT (t < length Tr - Suc 0);
                 if trans_leaves c t
                 then do {
                   ASSERT (c < length cntT \<and> c < length cntB
                           \<and> cntT ! c < length Tr \<and> cntB ! c + length (ls_intv (TrI ! t)) \<le> length Br);
                   RETURN (cntT[c := cntT ! c + 1], cntB[c := cntB ! c + length (ls_intv (TrI ! t))]) }
                 else RETURN (cntT, cntB) })
              (cntT, cntB);
           RETURN (cntT, cntB, Ta', avm) })
        (cntT, cntB, {}, {});
      RETURN (cntT, cntB, Ta', avm) }"


    text \<open>Pass 2 -- empty-EC (pass over \<^term>\<open>[0..<length D]\<close>). A MEC that produced no leaving
      transition (\<open>cntT!c = 0\<close>), or is an avoid MEC, but is not a target MEC, is an out-avoid MEC.
      Yields the output avoid set \<^term>\<open>Av' = {c. c < length D \<and> out_avoid c}\<close>; the sink set is then
      exactly \<^term>\<open>Ta' \<union> Av'\<close>.\<close>
    definition "empty_ec_pass cntT Ta' avm = FOREACH {0..<length D}
        (\<lambda>c Av'. if c \<notin> Ta' \<and> (c \<in> avm \<or> cntT ! c = 0) then RETURN (insert c Av') else RETURN Av') {}"

    text \<open>Pass 3 -- offset / prefix sum (ordered \<^const>\<open>nfoldli\<close> over \<^term>\<open>[0..<length D]\<close>). Turns the
      counts into CSR block offsets: \<open>St'!c = ctA c\<close>, \<open>boff!c = cbA c\<close>. A sink contributes one
      self-loop slot; any other MEC contributes its \<open>cntT!c\<close> / \<open>cntB!c\<close>. Returns the totals
      \<open>T = cnt_T\<close>, \<open>B = cnt_B\<close>.\<close>
    definition "offset_pass cntT cntB Ta' Av' = do {
      let St' = replicate (length D + 1) 0;
      let boff = replicate (length D + 1) 0;
      (St', boff, ct, cb) \<leftarrow> nfoldli [0..<length D] (\<lambda>_. True)
        (\<lambda>c (St', boff, ct, cb). do {
           let St' = St'[c := ct];
           let boff = boff[c := cb];
           let dT = (if c \<in> Ta' \<or> c \<in> Av' then 1 else cntT ! c);
           let dB = (if c \<in> Ta' \<or> c \<in> Av' then 1 else cntB ! c);
           RETURN (St', boff, ct + dT, cb + dB) })
        (St', boff, 0, 0);
      RETURN (St'[length D := ct], boff[length D := cb], ct, cb) }"

    text \<open>Pass 4 -- copy / scatter (single sweep over \<^term>\<open>[0..<N]\<close>, with per-MEC cursors). The
      cursor arrays \<open>curT\<close> / \<open>curB\<close> start at the block offsets (\<open>St'\<close> / \<open>boff\<close>). Each non-sink state's
      leaving transitions are scattered into their MEC's block, advancing that MEC's cursor; sink MECs
      are skipped (their self-loop is written in pass 5). The inner branch fill is the one verified
      by @{thm [source] fill_inner}.\<close>
    definition "copy_pass St' boff Ta' Av' nT nB = do {
      ASSERT (nT < length Tr);
      let Tr' = replicate (nT + 1) 0;
      let Br' = replicate nB 0;
      let Pr' = replicate nB 1;
      Tr' \<leftarrow> FOREACH {0..<length D} (\<lambda>c Tr'. RETURN (Tr'[St' ! c := boff ! c])) Tr';
      let curT = St';
      let curB = boff;
      (Tr', Br', Pr', curT, curB) \<leftarrow> FOREACH {0..<N}
        (\<lambda>u (Tr', Br', Pr', curT, curB). do {
           let c = op_mec_index_of D u;
           if c \<in> Ta' \<or> c \<in> Av' then RETURN (Tr', Br', Pr', curT, curB)
           else FOREACH (sn_intv (StI ! u))
              (\<lambda>t (Tr', Br', Pr', curT, curB).
                 if trans_leaves c t then do {
                   ASSERT (c < length curT \<and> c < length curB
                           \<and> curT ! c < length Tr' \<and> curT ! c + 1 < length Tr'
                           \<and> curT ! c < length Tr
                           \<and> curB ! c + cnt (TrI ! t) \<le> length Br'
                           \<and> length Pr' = length Br' \<and> length Br' \<le> length Br);
                   let Tr' = Tr'[curT ! c := curB ! c];
                   (Br', Pr', cbc) \<leftarrow> FOREACH (sn_intv (TrI ! t))
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

    text \<open>Pass 5 -- self-loops (pass over \<^term>\<open>[0..<length D]\<close>). Each sink MEC \<^term>\<open>c\<close> owns a
      one-slot block; fill it with the self-loop \<open>{#(c, 1)#}\<close> (branch target \<^term>\<open>c\<close>, probability
      \<open>1\<close>) at its offsets \<open>St'!c\<close> / \<open>boff!c\<close>.\<close>
    definition "selfloop_pass Tr' Br' Pr' St' boff Ta' Av' = FOREACH {0..<length D}
        (\<lambda>c (Tr', Br', Pr').
           if c \<in> Ta' \<or> c \<in> Av' then
             RETURN (Tr'[St' ! c := boff ! c, St' ! c + 1 := boff ! c + 1],
                     Br'[boff ! c := c], Pr'[boff ! c := 1])
           else RETURN (Tr', Br', Pr'))
        (Tr', Br', Pr')"

    subsection \<open>Correctness of the individual passes\<close>

    lemma mec_lt_lenD: "u < N \<Longrightarrow> op_mec_index_of D u < length D"
    proof -
      assume "u < N"
      then have "mec_of u \<in> mec_of ` {0..<N}" by simp
      also note mec_of_onto
      finally show ?thesis by (simp add: mec_of_eq_op)
    qed

    subsubsection \<open>Pass 1: counting\<close>

    text \<open>Inner loop: accumulating one member state's leaving transitions / branches into the count
      arrays at index \<^term>\<open>c\<close> (only that entry changes).\<close>
    text \<open>Per-MEC count bounds: the leaving transitions / branches of MEC \<open>i\<close> fit inside the input
      arrays (they are a subset of the transition / branch index space). Used to discharge the
      overflow \<open>ASSERT\<close>s propagated onto the count pass.\<close>
    lemma tc_le_length_Tr: "tc i \<le> length Tr - Suc 0"
    proof -
      have "ltdone i {} \<subseteq> {0..<length Tr - Suc 0}"
        unfolding ltdone_def using lvt_real_trans by fastforce
      from card_mono[OF _ this] have "card (ltdone i {}) \<le> length Tr - Suc 0" by simp
      thus ?thesis by (simp add: tc_card)
    qed

    lemma bc_le_length_Br: "bc i \<le> length Br"
    proof -
      have bcc: "bc i = (\<Sum>t \<in> ltdone i {}. cnt (TrI ! t))"
      proof -
        have "bc i = (\<Sum>u \<in> {u \<in> {0..<N}. op_mec_index_of D u = i}. \<Sum>t \<in> lvt i u. cnt (TrI ! t))"
          unfolding bc_def by (simp add: length_ls_intv)
        also have "\<dots> = (\<Sum>t \<in> (\<Union>u \<in> {u \<in> {0..<N}. op_mec_index_of D u = i}. lvt i u). cnt (TrI ! t))"
          by (subst sum.UNION_disjoint) (auto simp: lvt_disj_states)
        finally show ?thesis by (simp add: ltdone_def)
      qed
      have finlt: "finite (ltdone i {})" by simp
      have realt: "t < length Tr - Suc 0" if "t \<in> ltdone i {}" for t
        using that unfolding ltdone_def using lvt_real_trans by fastforce
      have disjTr: "sn_intv (TrI ! s) \<inter> sn_intv (TrI ! t) = {}"
          if "s \<noteq> t" "s \<in> ltdone i {}" "t \<in> ltdone i {}" for s t
        using that realt by (metis Tr_intv_disj inf_commute nat_neq_iff)
      have sub: "(\<Union>t \<in> ltdone i {}. sn_intv (TrI ! t)) \<subseteq> {0..<length Br}"
        using realt by (fastforce simp: sn_intv_member intro: Br_in_bound_intvD)
      have "bc i = card (\<Union>t \<in> ltdone i {}. sn_intv (TrI ! t))"
        unfolding bcc using finlt
        by (subst card_UN_disjoint) (auto simp: card_sn_intv realt disjTr)
      also have "\<dots> \<le> length Br"
        using card_mono[OF finite_atLeastLessThan sub] by simp
      finally show ?thesis .
    qed

    lemma count_inner_arr:
      assumes UB: "u < N"
      assumes cT: "c < length cntT0" and cB: "c < length cntB0"
      assumes Tbnd: "cntT0 ! c + card (lvt c u) \<le> length Tr - Suc 0"
      assumes Bbnd: "cntB0 ! c + (\<Sum>t \<in> lvt c u. length (ls_intv (TrI ! t))) \<le> length Br"
      shows "FOREACH (sn_intv (StI ! u))
         (\<lambda>t (cntT, cntB). do {
            ASSERT (t < length Tr - Suc 0);
            if trans_leaves c t
            then do {
              ASSERT (c < length cntT \<and> c < length cntB
                      \<and> cntT ! c < length Tr \<and> cntB ! c + length (ls_intv (TrI ! t)) \<le> length Br);
              RETURN (cntT[c := cntT ! c + 1], cntB[c := cntB ! c + length (ls_intv (TrI ! t))]) }
            else RETURN (cntT, cntB) })
         (cntT0, cntB0)
       \<le> SPEC (\<lambda>(cntT, cntB). length cntT = length cntT0 \<and> length cntB = length cntB0 \<and>
           cntT ! c = cntT0 ! c + card (lvt c u) \<and>
           cntB ! c = cntB0 ! c + (\<Sum>t \<in> lvt c u. length (ls_intv (TrI ! t))) \<and>
           (\<forall>c'. c' \<noteq> c \<longrightarrow> cntT ! c' = cntT0 ! c' \<and> cntB ! c' = cntB0 ! c'))"
    proof -
      have Tb: "cntT0 ! c + card (lvt c u - it) \<le> length Tr - Suc 0" for it
        using Tbnd card_mono[OF finite_lvt Diff_subset, of c u it] by simp
      have Bb: "cntB0 ! c + (\<Sum>t \<in> lvt c u - it. length (ls_intv (TrI ! t))) + length (ls_intv (TrI ! x)) \<le> length Br"
        if xit: "x \<in> it" and xsub: "it \<subseteq> sn_intv (StI ! u)" and xtl: "trans_leaves c x" for x it
      proof -
        have xtl': "x \<in> lvt c u" using xit xsub xtl by (auto simp: lvt_def)
        have "(\<Sum>t \<in> lvt c u - it. length (ls_intv (TrI ! t))) + length (ls_intv (TrI ! x))
              = (\<Sum>t \<in> insert x (lvt c u - it). length (ls_intv (TrI ! t)))"
          using xit finite_lvt by simp
        also have "\<dots> \<le> (\<Sum>t \<in> lvt c u. length (ls_intv (TrI ! t)))"
          using xtl' finite_lvt by (intro sum_mono2) auto
        finally show ?thesis using Bbnd by simp
      qed
      show ?thesis
        apply (refine_vcg FOREACH_rule[where I="\<lambda>it (cntT, cntB).
             length cntT = length cntT0 \<and> length cntB = length cntB0 \<and>
             cntT ! c = cntT0 ! c + card (lvt c u - it) \<and>
             cntB ! c = cntB0 ! c + (\<Sum>t \<in> lvt c u - it. length (ls_intv (TrI ! t))) \<and>
             (\<forall>c'. c' \<noteq> c \<longrightarrow> cntT ! c' = cntT0 ! c' \<and> cntB ! c' = cntB0 ! c')"])

        apply clarsimp_all
        subgoal
          using Tr_in_bound_intvD assms(1) in_subset_sn_intv by presburger
        subgoal 
          using assms(2) by fastforce
        subgoal
          using assms(3) by blast
        subgoal for x it aa ba using Tb[of it] by linarith
        subgoal premises p for x it aa ba using Bb[OF p(1) p(2) p(4)] by simp
        subgoal by (auto simp: lvt_diff_it card_insert_if split: if_splits)
        subgoal by (auto simp: lvt_diff_it sum.insert_remove split: if_splits)
        subgoal by (simp add: lvt_diff_skip)
        subgoal by (simp add: lvt_diff_skip)
        done
    qed

    text \<open>Adding one just-processed state \<^term>\<open>u\<close> to the processed set, split by whether it belongs
      to MEC \<^term>\<open>c'\<close>.\<close>
    lemma proc_insert:
      "u \<in> it \<Longrightarrow> it \<subseteq> {0..<N} \<Longrightarrow>
       {v \<in> {0..<N} - (it - {u}). op_mec_index_of D v = c'}
         = (if op_mec_index_of D u = c' then insert u {v \<in> {0..<N} - it. op_mec_index_of D v = c'}
            else {v \<in> {0..<N} - it. op_mec_index_of D v = c'})"
      by (auto split: if_splits)

    text \<open>Reindexing a per-MEC count sum when one processed state \<^term>\<open>x\<close> is added.\<close>
    lemma sum_proc_insert:
      fixes f :: "nat \<Rightarrow> nat"
      assumes xit: "x \<in> it" and itN: "it \<subseteq> {0..<N}"
      shows "(\<Sum>u \<in> {u \<in> {0..<N} - (it - {x}). op_mec_index_of D u = c}. f u)
           = (if op_mec_index_of D x = c then f x else 0)
             + (\<Sum>u \<in> {u \<in> {0..<N} - it. op_mec_index_of D u = c}. f u)"
    proof (cases "op_mec_index_of D x = c")
      case True
      have "{u \<in> {0..<N} - (it - {x}). op_mec_index_of D u = c}
              = insert x {u \<in> {0..<N} - it. op_mec_index_of D u = c}"
        using xit itN True by auto
      moreover have "x \<notin> {u \<in> {0..<N} - it. op_mec_index_of D u = c}" using xit by simp
      ultimately show ?thesis using True by simp
    next
      case False
      have "{u \<in> {0..<N} - (it - {x}). op_mec_index_of D u = c}
              = {u \<in> {0..<N} - it. op_mec_index_of D u = c}"
        using False by auto
      with False show ?thesis by simp
    qed

    text \<open>The accumulated invariant of the counting sweep.\<close>
    definition "count_inv it cntT cntB Ta' avm \<longleftrightarrow>
      length cntT = length D \<and> length cntB = length D \<and>
      (\<forall>c<length D. cntT ! c = (\<Sum>u \<in> {u \<in> {0..<N} - it. op_mec_index_of D u = c}. card (lvt c u))) \<and>
      (\<forall>c<length D. cntB ! c = (\<Sum>u \<in> {u \<in> {0..<N} - it. op_mec_index_of D u = c}. (\<Sum>t \<in> lvt c u. length (ls_intv (TrI ! t))))) \<and>
      Ta' = {c. c < length D \<and> (\<exists>u \<in> {0..<N} - it. op_mec_index_of D u = c \<and> u \<in> Ta)} \<and>
      avm = {c. c < length D \<and> (\<exists>u \<in> {0..<N} - it. op_mec_index_of D u = c \<and> u \<in> Av)}"

    lemma count_inv_start:
      "count_inv {0..<N} (replicate (length D) 0) (replicate (length D) 0) {} {}"
      by (auto simp: count_inv_def)

    lemma count_inv_lenT: "count_inv it cntT cntB Ta' avm \<Longrightarrow> length cntT = length D"
      and count_inv_lenB: "count_inv it cntT cntB Ta' avm \<Longrightarrow> length cntB = length D"
      by (simp_all add: count_inv_def)

    lemma count_inv_step:
      assumes xit: "x \<in> it" and itN: "it \<subseteq> {0..<N}"
      assumes INV: "count_inv it cntT cntB Ta' avm"
      assumes lenT': "length cntT' = length cntT" and lenB': "length cntB' = length cntB"
      assumes T: "cntT' ! (op_mec_index_of D x) = cntT ! (op_mec_index_of D x) + card (lvt (op_mec_index_of D x) x)"
      assumes B: "cntB' ! (op_mec_index_of D x) = cntB ! (op_mec_index_of D x) + (\<Sum>t \<in> lvt (op_mec_index_of D x) x. length (ls_intv (TrI ! t)))"
      assumes oth: "\<forall>c'. c' \<noteq> op_mec_index_of D x \<longrightarrow> cntT' ! c' = cntT ! c' \<and> cntB' ! c' = cntB ! c'"
      shows "count_inv (it - {x}) cntT' cntB'
               (if x \<in> Ta then insert (op_mec_index_of D x) Ta' else Ta')
               (if x \<in> Av then insert (op_mec_index_of D x) avm else avm)"
    proof -
      from INV have
        lenTD: "length cntT = length D" and lenBD: "length cntB = length D" and
        iT: "\<And>c. c < length D \<Longrightarrow> cntT ! c = (\<Sum>u \<in> {u \<in> {0..<N} - it. op_mec_index_of D u = c}. card (lvt c u))" and
        iB: "\<And>c. c < length D \<Longrightarrow> cntB ! c = (\<Sum>u \<in> {u \<in> {0..<N} - it. op_mec_index_of D u = c}. (\<Sum>t \<in> lvt c u. length (ls_intv (TrI ! t))))" and
        iTa: "Ta' = {c. c < length D \<and> (\<exists>u \<in> {0..<N} - it. op_mec_index_of D u = c \<and> u \<in> Ta)}" and
        iAv: "avm = {c. c < length D \<and> (\<exists>u \<in> {0..<N} - it. op_mec_index_of D u = c \<and> u \<in> Av)}"
        by (auto simp: count_inv_def)
      have cT: "cntT' ! c = (\<Sum>u \<in> {u \<in> {0..<N} - (it-{x}). op_mec_index_of D u = c}. card (lvt c u))"
        if c: "c < length D" for c
        using T oth iT[OF c] sum_proc_insert[OF xit itN, of "\<lambda>u. card (lvt c u)" c]
        by (cases "op_mec_index_of D x = c") auto
      have cB: "cntB' ! c = (\<Sum>u \<in> {u \<in> {0..<N} - (it-{x}). op_mec_index_of D u = c}. (\<Sum>t \<in> lvt c u. length (ls_intv (TrI ! t))))"
        if c: "c < length D" for c
        using B oth iB[OF c] sum_proc_insert[OF xit itN, of "\<lambda>u. \<Sum>t \<in> lvt c u. length (ls_intv (TrI ! t))" c]
        by (cases "op_mec_index_of D x = c") auto
      have cTa: "(if x \<in> Ta then insert (op_mec_index_of D x) Ta' else Ta')
                 = {c. c < length D \<and> (\<exists>u \<in> {0..<N} - (it-{x}). op_mec_index_of D u = c \<and> u \<in> Ta)}"
        using iTa xit itN mec_lt_lenD[of x] by auto
      have cAv: "(if x \<in> Av then insert (op_mec_index_of D x) avm else avm)
                 = {c. c < length D \<and> (\<exists>u \<in> {0..<N} - (it-{x}). op_mec_index_of D u = c \<and> u \<in> Av)}"
        using iAv xit itN mec_lt_lenD[of x] by auto
      show ?thesis using lenT' lenB' lenTD lenBD cT cB cTa cAv by (auto simp: count_inv_def)
    qed

    lemma count_inv_final:
      "count_inv {} cntT cntB Ta' avm \<Longrightarrow>
        length cntT = length D \<and> length cntB = length D \<and>
        (\<forall>c<length D. cntT ! c = tc c) \<and> (\<forall>c<length D. cntB ! c = bc c) \<and>
        Ta' = {c. c < length D \<and> is_target_mec c} \<and> avm = {c. c < length D \<and> is_avoid_mec c}"
      by (auto simp: count_inv_def tc_def bc_def is_target_mec_def is_avoid_mec_def)

    text \<open>The running count for MEC \<open>c = mec u\<close> plus \<open>u\<close>'s own contribution never exceeds the total
      \<^const>\<open>tc\<close>/\<^const>\<open>bc\<close> for that MEC (a sum over a superset), hence stays within \<open>length Tr/Br\<close> --
      this discharges the overflow \<open>ASSERT\<close>s of the count pass (\<open>count_inner_arr\<close>'s \<open>Tbnd\<close>/\<open>Bbnd\<close>).\<close>
    lemma count_inv_Tbnd:
      assumes INV: "count_inv it cntT cntB Ta' avm" and uit: "u \<in> it" and itN: "it \<subseteq> {0..<N}"
      shows "cntT ! (op_mec_index_of D u) + card (lvt (op_mec_index_of D u) u) \<le> length Tr - Suc 0"
    proof -
      define c where "c = op_mec_index_of D u"
      define S where "S = {v \<in> {0..<N} - it. op_mec_index_of D v = c}"
      have uN: "u < N" using uit itN by auto
      have cD: "c < length D" unfolding c_def using uN by (rule mec_lt_lenD)
      have uS: "u \<notin> S" using uit unfolding S_def by simp
      have finS: "finite S" unfolding S_def by simp
      have cntTc: "cntT ! c = (\<Sum>v \<in> S. card (lvt c v))"
        using INV cD unfolding count_inv_def S_def by blast
      have "cntT ! c + card (lvt c u) = (\<Sum>v \<in> insert u S. card (lvt c v))"
        using cntTc by (simp add: sum.insert[OF finS uS])
      also have "\<dots> \<le> (\<Sum>v \<in> {v \<in> {0..<N}. op_mec_index_of D v = c}. card (lvt c v))"
        using uN by (intro sum_mono2) (auto simp: S_def c_def)
      also have "\<dots> = tc c" by (simp add: tc_def)
      also have "\<dots> \<le> length Tr - Suc 0" by (rule tc_le_length_Tr)
      finally show ?thesis by (simp add: c_def)
    qed

    lemma count_inv_Bbnd:
      assumes INV: "count_inv it cntT cntB Ta' avm" and uit: "u \<in> it" and itN: "it \<subseteq> {0..<N}"
      shows "cntB ! (op_mec_index_of D u) + (\<Sum>t \<in> lvt (op_mec_index_of D u) u. length (ls_intv (TrI ! t))) \<le> length Br"
    proof -
      define c where "c = op_mec_index_of D u"
      define S where "S = {v \<in> {0..<N} - it. op_mec_index_of D v = c}"
      have uN: "u < N" using uit itN by auto
      have cD: "c < length D" unfolding c_def using uN by (rule mec_lt_lenD)
      have uS: "u \<notin> S" using uit unfolding S_def by simp
      have finS: "finite S" unfolding S_def by simp
      have cntBc: "cntB ! c = (\<Sum>v \<in> S. \<Sum>t \<in> lvt c v. length (ls_intv (TrI ! t)))"
        using INV cD unfolding count_inv_def S_def by blast
      have "cntB ! c + (\<Sum>t \<in> lvt c u. length (ls_intv (TrI ! t)))
            = (\<Sum>v \<in> insert u S. \<Sum>t \<in> lvt c v. length (ls_intv (TrI ! t)))"
        using cntBc by (simp add: sum.insert[OF finS uS])
      also have "\<dots> \<le> (\<Sum>v \<in> {v \<in> {0..<N}. op_mec_index_of D v = c}. \<Sum>t \<in> lvt c v. length (ls_intv (TrI ! t)))"
        using uN by (intro sum_mono2) (auto simp: S_def c_def)
      also have "\<dots> = bc c" by (simp add: bc_def)
      also have "\<dots> \<le> length Br" by (rule bc_le_length_Br)
      finally show ?thesis by (simp add: c_def)
    qed

    lemma count_pass_correct:
      "count_pass \<le> SPEC (\<lambda>(cntT, cntB, Ta', avm).
          length cntT = length D \<and> length cntB = length D \<and>
          (\<forall>c<length D. cntT ! c = tc c) \<and> (\<forall>c<length D. cntB ! c = bc c) \<and>
          Ta' = {c. c < length D \<and> is_target_mec c} \<and> avm = {c. c < length D \<and> is_avoid_mec c})"
      unfolding count_pass_def
      apply (refine_vcg count_inner_arr[THEN order_trans]
         FOREACH_rule[where I="\<lambda>it (cntT, cntB, Ta', avm). count_inv it cntT cntB Ta' avm"])
      subgoal by simp                                    \<comment> \<open>finite\<close>
      subgoal by (auto simp: count_inv_def)              \<comment> \<open>init\<close>
      subgoal by auto                                    \<comment> \<open>u < N\<close>
      subgoal by (auto simp: count_inv_lenT count_inv_lenB mec_lt_lenD)   \<comment> \<open>c < length cntT\<close>
      subgoal by (auto simp: count_inv_lenT count_inv_lenB mec_lt_lenD)   \<comment> \<open>c < length cntB\<close>
      subgoal by (rule count_inv_Tbnd) auto              \<comment> \<open>Tbnd\<close>
      subgoal by (rule count_inv_Bbnd) auto              \<comment> \<open>Bbnd\<close>
      subgoal                                            \<comment> \<open>step\<close>
        apply (clarsimp split del: if_split)
        apply (rule count_inv_step)
        apply (assumption | simp)+
        done
      subgoal by (auto dest!: count_inv_final)           \<comment> \<open>final: length cntT\<close>
      subgoal by (auto dest!: count_inv_final)           \<comment> \<open>final: length cntB\<close>
      subgoal by (auto dest!: count_inv_final)           \<comment> \<open>final: cntT = tc\<close>
      subgoal by (auto dest!: count_inv_final)           \<comment> \<open>final: cntB = bc\<close>
      subgoal by (auto dest!: count_inv_final)           \<comment> \<open>final: Ta'\<close>
      subgoal by (auto dest!: count_inv_final)           \<comment> \<open>final: avm\<close>
      done

    subsubsection \<open>Pass 2: empty-EC\<close>

    lemma empty_ec_pass_correct:
      assumes cntT: "\<forall>c<length D. cntT ! c = tc c"
      assumes Ta': "Ta' = {c. c < length D \<and> is_target_mec c}"
      assumes avm: "avm = {c. c < length D \<and> is_avoid_mec c}"
      shows "empty_ec_pass cntT Ta' avm \<le> SPEC (\<lambda>Av'. Av' = {c. c < length D \<and> out_avoid c})"
      unfolding empty_ec_pass_def
      apply (refine_vcg FOREACH_rule[where I="\<lambda>it Av'.
          Av' = {c \<in> {0..<length D} - it. c \<notin> Ta' \<and> (c \<in> avm \<or> cntT ! c = 0)}"])
      subgoal by simp
      subgoal by simp
      subgoal by (auto simp: it_step_insert_iff)
      subgoal by (auto simp: it_step_insert_iff)
      subgoal using cntT by (auto simp: out_avoid_def Ta' avm)
      done

    subsubsection \<open>Pass 3: offset / prefix sum\<close>

    lemma contrib_T_alt: "contrib_T c = (if is_target_mec c \<or> out_avoid c then 1 else tc c)"
      by (auto simp: contrib_T_def out_avoid_def)
    lemma contrib_B_alt: "contrib_B c = (if is_target_mec c \<or> out_avoid c then 1 else bc c)"
      by (auto simp: contrib_B_def out_avoid_def)

    lemma upt_split_elem:
      assumes "[0..<n] = l1 @ x # l2" shows "x = length l1 \<and> length l1 < n"
    proof -
      have lt: "length l1 < n" using assms by (auto dest!: arg_cong[where f = length])
      have "x = (l1 @ x # l2) ! length l1" by simp
      also have "\<dots> = [0..<n] ! length l1" using assms by simp
      also have "\<dots> = length l1" using lt by simp
      finally show ?thesis using lt by simp
    qed

    text \<open>The whole built transition array fits inside the input one. This is the relative form of
      the builder's capacity bound; combined with the machine-word bound that the input MDP's
      \<^emph>\<open>assertion\<close> carries, it is what discharges the snat overflow side conditions of the
      implementation --- see @{thm [source] cnt_B_le_length_Br} for the branch counterpart.\<close>
    lemma cnt_T_le_length_Tr: "cnt_T \<le> length Tr"
      by (rule Suc_leD[OF Suc_cnt_T_le_length_Tr])

    lemma cnt_T_lt_length_Tr: "cnt_T < length Tr"
      using Suc_cnt_T_le_length_Tr by simp

    lemma offset_pass_correct:
      assumes cntT: "\<forall>c<length D. cntT ! c = tc c"
      assumes cntB: "\<forall>c<length D. cntB ! c = bc c"
      assumes Ta': "Ta' = {c. c < length D \<and> is_target_mec c}"
      assumes Av': "Av' = {c. c < length D \<and> out_avoid c}"
      shows "offset_pass cntT cntB Ta' Av'
         \<le> SPEC (\<lambda>(St', boff, nT, nB).
             length St' = length D + 1 \<and> length boff = length D + 1 \<and>
             (\<forall>c\<le>length D. St' ! c = ctA c) \<and> (\<forall>c\<le>length D. boff ! c = cbA c) \<and>
             nT = cnt_T \<and> nB = cnt_B)"
      unfolding offset_pass_def
      apply (refine_vcg nfoldli_rule[where I="\<lambda>l1 l2 (St', boff, ct, cb).
          length St' = length D + 1 \<and> length boff = length D + 1 \<and>
          ct = ctA (length l1) \<and> cb = cbA (length l1) \<and>
          (\<forall>c<length l1. St' ! c = ctA c \<and> boff ! c = cbA c)"])
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (auto dest!: upt_split_elem)
      subgoal by (auto dest!: upt_split_elem)
      subgoal by (auto dest!: upt_split_elem simp: ctA_Suc contrib_T_alt Ta' Av' cntT)
      subgoal by (auto dest!: upt_split_elem simp: cbA_Suc contrib_B_alt Ta' Av' cntB)
      subgoal by (auto dest!: upt_split_elem simp: nth_list_update)
      subgoal by (auto dest!: upt_split_elem simp: nth_list_update)
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by auto
      subgoal by auto
      subgoal by (auto simp: nth_list_update cnt_T_ctA)
      subgoal by (auto simp: nth_list_update cnt_B_cbA)
      subgoal by (auto simp: cnt_T_ctA)
      subgoal by (auto simp: cnt_B_cbA)
      done

    subsubsection \<open>Pass 4: copy / scatter\<close>

    text \<open>The output of the copy pass: sizes, all block openings pinned, the global pointer bound, and
      -- for the non-sink MECs -- the CSR row content read back as \<^term>\<open>rmt ` ltfull c\<close>. Sink blocks
      keep only their (pre-written) opening; they are completed by the self-loop pass.\<close>
    definition "copy_post Tr' Br' Pr' \<longleftrightarrow>
      length Tr' = cnt_T + 1 \<and> length Br' = cnt_B \<and> length Pr' = cnt_B \<and>
      Tr' ! 0 = 0 \<and> (\<forall>s\<le>cnt_T. Tr' ! s \<le> cnt_B) \<and>
      (\<forall>c<length D. Tr' ! ctA c = cbA c) \<and>
      (\<forall>c<length D. \<not> (is_target_mec c \<or> out_avoid c) \<longrightarrow>
          Tr' ! ctA (Suc c) = cbA (Suc c) \<and>
          (\<forall>s. ctA c \<le> s \<and> s \<le> ctA (Suc c) \<longrightarrow> cbA c \<le> Tr' ! s \<and> Tr' ! s \<le> cbA (Suc c)) \<and>
          seg Tr' Br' Pr' ` {ctA c..<ctA (Suc c)} = rmt ` ltfull c)"

    lemma ctA_le_iff: "ctA a \<le> ctA b \<longleftrightarrow> a \<le> b"
      using ctA_strict_mono ctA_mono by (metis leD leI)
    lemma cbA_le_iff: "cbA a \<le> cbA b \<longleftrightarrow> a \<le> b"
      using cbA_strict_mono cbA_mono by (metis leD leI)
    lemma ctA_eq_iff: "ctA a = ctA b \<longleftrightarrow> a = b"
      by (metis ctA_le_iff le_antisym order_refl)
    lemma cbA_eq_iff: "cbA a = cbA b \<longleftrightarrow> a = b"
      by (metis cbA_le_iff le_antisym order_refl)
    lemma ctA_less_iff: "ctA a < ctA b \<longleftrightarrow> a < b"
      using ctA_le_iff by (metis linorder_not_le)
    lemma cbA_less_iff: "cbA a < cbA b \<longleftrightarrow> a < b"
      using cbA_le_iff by (metis linorder_not_le)

    text \<open>Pre-write pass: pin every block opening \<open>Tr'[ctA c := cbA c]\<close>.\<close>
    lemma copy_prewrite_correct:
      assumes StA: "\<forall>c\<le>length D. St' ! c = ctA c"
      assumes bA: "\<forall>c\<le>length D. boff ! c = cbA c"
      shows "FOREACH {0..<length D} (\<lambda>c T. RETURN (T[St' ! c := boff ! c])) (replicate (cnt_T + 1) 0)
         \<le> SPEC (\<lambda>T. length T = cnt_T + 1 \<and> (\<forall>c<length D. T ! ctA c = cbA c) \<and>
             (\<forall>s\<le>cnt_T. T ! s \<le> cnt_B) \<and> T ! 0 = 0)"
      apply (refine_vcg FOREACH_rule[where I="\<lambda>it T.
          length T = cnt_T + 1 \<and> (\<forall>c<length D. c \<notin> it \<longrightarrow> T ! ctA c = cbA c) \<and>
          (\<forall>s\<le>cnt_T. T ! s \<le> cnt_B)"])
      subgoal by simp                     \<comment> \<open>finite\<close>
      subgoal by simp                     \<comment> \<open>init: length\<close>
      subgoal by simp                     \<comment> \<open>init: opening (vacuous)\<close>
      subgoal by (simp add: nth_Cons')    \<comment> \<open>init: bound\<close>
      subgoal by simp                     \<comment> \<open>step: length\<close>
      subgoal premises p for x it \<sigma> c    \<comment> \<open>step: opening\<close>
      proof -
        have xD: "x < length D" using p by auto
        have Sx: "St' ! x = ctA x" and bx: "boff ! x = cbA x" using StA bA xD by auto
        have ctxlt: "ctA x < length \<sigma>" using p ctA_mono[of x "length D"] xD by (simp add: cnt_T_ctA)
        show ?thesis
        proof (cases "c = x")
          case True thus ?thesis using Sx bx ctxlt by (simp add: nth_list_update)
        next
          case False
          then have "\<sigma> ! ctA c = cbA c" using p by auto
          then show ?thesis using Sx bx False by (simp add: nth_list_update ctA_eq_iff)
        qed
      qed
      subgoal premises p for x it \<sigma> s    \<comment> \<open>step: bound\<close>
      proof -
        have xD: "x < length D" using p by auto
        have Sx: "St' ! x = ctA x" and bx: "boff ! x = cbA x" using StA bA xD by auto
        have "cbA x \<le> cnt_B" using cbA_le_cnt_B[of x] xD by simp
        moreover have "\<sigma> ! s \<le> cnt_B" using p by auto
        ultimately show ?thesis using Sx bx
          by (simp add: nth_list_update')
      qed
      subgoal by simp                     \<comment> \<open>final: length\<close>
      subgoal by simp                     \<comment> \<open>final: opening\<close>
      subgoal by simp                     \<comment> \<open>final: bound\<close>
      subgoal premises p for \<sigma>            \<comment> \<open>final: T ! 0 = 0\<close>
      proof -
        from p have opn: "\<And>c. c < length D \<Longrightarrow> \<sigma> ! ctA c = cbA c"
          and bnd: "\<And>s. s \<le> cnt_T \<Longrightarrow> \<sigma> ! s \<le> cnt_B" by auto
        show "\<sigma> ! 0 = 0"
        proof (cases "length D = 0")
          case True then have "cnt_B = 0" by (metis cnt_B_cbA cbA_0)
          then show ?thesis using bnd[of 0] by simp
        next
          case False then show ?thesis using opn[of 0] by (metis ctA_0 cbA_0 gr0I)
        qed
      qed
      done

    text \<open>Per-state emit for member \<open>u\<close> of MEC \<open>c\<close>: the cursor lives in \<open>curT!c\<close> / \<open>curB!c\<close> and
      only entry \<open>c\<close> of the cursor arrays changes; the effect on \<open>Tr'\<close>/\<open>Br'\<close>/\<open>Pr'\<close> is exactly
      \<^const>\<open>fill_state_inv\<close>'s, with \<open>em\<close> fixed to \<open>True\<close>.\<close>
    definition "copy_state_inv u c TR BR PR curT0 curB0 it Tr' Br' Pr' curT curB \<longleftrightarrow>
      (\<forall>c'. c' \<noteq> c \<longrightarrow> curT ! c' = curT0 ! c' \<and> curB ! c' = curB0 ! c') \<and>
      length curT = length curT0 \<and> length curB = length curB0 \<and>
      fill_state_inv u c TR BR PR (curT0 ! c) (curB0 ! c) True it Tr' Br' Pr' (curT ! c) (curB ! c) True"

    lemma copy_state_emit_pres:
      assumes cc: "c < length curT" and ccB: "c < length curB"
      assumes op0: "TR ! (curT0 ! c) = curB0 ! c"
      assumes roomT: "curT0 ! c + card (lvt c u) < length TR"
      assumes xit: "x \<in> it" and xlvt: "x \<in> lvt c u"
      assumes INV: "copy_state_inv u c TR BR PR curT0 curB0 it Tr' Br' Pr' curT curB"
      assumes FI: "fill_inv x Br' Pr' (curB ! c) {} Br2 Pr2 cbc"
      shows "copy_state_inv u c TR BR PR curT0 curB0 (it - {x})
               (Tr'[curT ! c := curB ! c, curT ! c + 1 := curB[c := cbc] ! c]) Br2 Pr2
               (curT[c := curT ! c + 1]) (curB[c := cbc])"
    proof -
      from INV[unfolded copy_state_inv_def] have
        H1: "\<forall>c'. c' \<noteq> c \<longrightarrow> curT ! c' = curT0 ! c' \<and> curB ! c' = curB0 ! c'" and
        H2: "length curT = length curT0" and H3: "length curB = length curB0" and
        FSI: "fill_state_inv u c TR BR PR (curT0 ! c) (curB0 ! c) True it Tr' Br' Pr' (curT ! c) (curB ! c) True"
        by auto
      have step: "fill_state_inv u c TR BR PR (curT0 ! c) (curB0 ! c) True (it - {x})
          (Tr'[curT ! c := curB ! c, Suc (curT ! c) := cbc]) Br2 Pr2 (Suc (curT ! c)) cbc True"
        using fill_state_emit_step[OF xlvt xit op0 roomT FSI FI] .
      show ?thesis
        unfolding copy_state_inv_def
      proof (intro conjI)
        show "\<forall>c'. c' \<noteq> c \<longrightarrow> curT[c := curT ! c + 1] ! c' = curT0 ! c' \<and> curB[c := cbc] ! c' = curB0 ! c'"
          using H1 by (simp add: nth_list_update)
        show "length (curT[c := curT ! c + 1]) = length curT0" using H2 by simp
        show "length (curB[c := cbc]) = length curB0" using H3 by simp
        show "fill_state_inv u c TR BR PR (curT0 ! c) (curB0 ! c) True (it - {x})
                (Tr'[curT ! c := curB ! c, curT ! c + 1 := curB[c := cbc] ! c]) Br2 Pr2
                (curT[c := curT ! c + 1] ! c) (curB[c := cbc] ! c) True"
          using step cc ccB by (simp add: nth_list_update Suc_eq_plus1[symmetric])
      qed
    qed

    lemma copy_state:
      assumes cT: "c < length curT0" and cB: "c < length curB0"
      assumes op0: "TR ! (curT0 ! c) = curB0 ! c"
      assumes lenBR: "length PR = length BR"
      assumes roomB: "curB0 ! c + (\<Sum>t\<in>lvt c u. cnt (TrI ! t)) \<le> length BR"
      assumes roomT: "curT0 ! c + card (lvt c u) < length TR"
      assumes capT: "length TR \<le> length Tr" and capB: "length BR \<le> length Br"
      shows "FOREACH (sn_intv (StI ! u))
          (\<lambda>t (Tr', Br', Pr', curT, curB).
            if trans_leaves c t then do {
              ASSERT (c < length curT \<and> c < length curB
                      \<and> curT ! c < length Tr' \<and> curT ! c + 1 < length Tr'
                      \<and> curT ! c < length Tr
                      \<and> curB ! c + cnt (TrI ! t) \<le> length Br'
                      \<and> length Pr' = length Br' \<and> length Br' \<le> length Br);
              let Tr' = Tr'[curT ! c := curB ! c];
              (Br', Pr', cbc) \<leftarrow> FOREACH (sn_intv (TrI ! t))
                  (\<lambda>b (Br', Pr', cbc). RETURN (Br'[cbc := op_mec_index_of D (Br ! b)], Pr'[cbc := Pr ! b], cbc + 1))
                  (Br', Pr', curB ! c);
              let curB = curB[c := cbc];
              let Tr' = Tr'[curT ! c + 1 := curB ! c];
              RETURN (Tr', Br', Pr', curT[c := curT ! c + 1], curB)
            } else RETURN (Tr', Br', Pr', curT, curB))
          (TR, BR, PR, curT0, curB0)
        \<le> SPEC (\<lambda>(Tr', Br', Pr', curT, curB).
            copy_state_inv u c TR BR PR curT0 curB0 {} Tr' Br' Pr' curT curB)"
    proof -
      \<comment> \<open>The whole transition-body \<open>ASSERT\<close> follows from the loop invariant: the cursors have advanced
        by exactly the already-emitted leaving transitions (\<open>lvt c u - it\<close>), so \<open>roomT\<close>/\<open>roomB\<close> bound
        them, and \<open>t \<in> it \<inter> lvt c u\<close> makes that advance strictly smaller than the whole block, which is
        the \<open>+ 1\<close> headroom the impl writes into.\<close>
      have ASRT: "c < length curT \<and> c < length curB
              \<and> curT ! c < length Tr' \<and> curT ! c + 1 < length Tr'
              \<and> curT ! c < length Tr
              \<and> curB ! c + cnt (TrI ! t) \<le> length Br'
              \<and> length Pr' = length Br' \<and> length Br' \<le> length Br"
        if INV: "copy_state_inv u c TR BR PR curT0 curB0 it Tr' Br' Pr' curT curB"
          and tit: "t \<in> it" and itsub: "it \<subseteq> sn_intv (StI ! u)" and tl: "trans_leaves c t"
        for it Tr' Br' Pr' curT curB t
      proof -
        from INV[unfolded copy_state_inv_def fill_state_inv_def] have
          LcT: "length curT = length curT0" and LcB: "length curB = length curB0" and
          cTv: "curT ! c = curT0 ! c + card (lvt c u - it)" and
          cBv: "curB ! c = curB0 ! c + (\<Sum>t'\<in>lvt c u - it. cnt (TrI ! t'))" and
          LT: "length Tr' = length TR" and LB: "length Br' = length BR" and
          LP: "length Pr' = length PR"
          by auto
        have tlvt: "t \<in> lvt c u" using tit itsub tl by (auto simp: lvt_mem)
        have c1: "c < length curT" using cT LcT by simp
        have c2: "c < length curB" using cB LcB by simp
        have cl: "card (lvt c u - it) < card (lvt c u)"
          using tit tlvt by (intro psubset_card_mono[OF finite_lvt]) blast
        have t1: "curT ! c + 1 < length Tr'"
        proof -
          have "curT ! c + 1 \<le> curT0 ! c + card (lvt c u)" using cTv cl by simp
          also have "\<dots> < length TR" by (rule roomT)
          finally show ?thesis using LT by simp
        qed
        have t0: "curT ! c < length Tr'" using t1 by simp
        have t2: "curT ! c < length Tr" using t1 LT capT by simp
        have b1: "curB ! c + cnt (TrI ! t) \<le> length Br'"
        proof -
          have "(\<Sum>t'\<in>lvt c u - it. cnt (TrI ! t')) + cnt (TrI ! t)
                  \<le> (\<Sum>t'\<in>lvt c u. cnt (TrI ! t'))"
            using lvt_sum_room[OF tlvt _ Diff_subset] tit by blast
          then have "curB ! c + cnt (TrI ! t) \<le> curB0 ! c + (\<Sum>t'\<in>lvt c u. cnt (TrI ! t'))"
            using cBv by simp
          with roomB show ?thesis using LB by simp
        qed
        have p1: "length Pr' = length Br'" using LP LB lenBR by simp
        have b2: "length Br' \<le> length Br" using LB capB by simp
        show ?thesis using c1 c2 t0 t1 t2 b1 p1 b2 by blast
      qed
      show ?thesis
        apply (refine_vcg fill_inner[THEN order_trans]
            FOREACH_rule[where I="\<lambda>it (Tr', Br', Pr', curT, curB).
              copy_state_inv u c TR BR PR curT0 curB0 it Tr' Br' Pr' curT curB"])
        subgoal by simp                                                        \<comment> \<open>finite\<close>
        subgoal using op0 by (auto simp: copy_state_inv_def fill_state_inv_def lvt_sub)  \<comment> \<open>init\<close>
        \<comment> \<open>The eight conjuncts of the transition-body \<open>ASSERT\<close> (mirroring the sepref impl), each
          discharged from \<open>ASRT\<close> above. The last of each pair is the \<^emph>\<open>relative\<close> capacity bound
          against the input arrays, which is what the code layer turns into a machine-word bound.\<close>
        subgoal by (auto dest!: ASRT)                          \<comment> \<open>c < length curT\<close>
        subgoal by (auto dest!: ASRT)                          \<comment> \<open>c < length curB\<close>
        subgoal by (auto dest!: ASRT)                          \<comment> \<open>curT ! c < length Tr'\<close>
        subgoal by (auto dest!: ASRT)                          \<comment> \<open>curT ! c + 1 < length Tr'\<close>
        subgoal by (auto dest!: ASRT)                          \<comment> \<open>curT ! c < length Tr\<close>
        subgoal by (auto dest!: ASRT)                          \<comment> \<open>branch block has room\<close>
        subgoal by (auto dest!: ASRT)                          \<comment> \<open>length Pr' = length Br'\<close>
        subgoal by (auto dest!: ASRT)                          \<comment> \<open>length Br' \<le> length Br\<close>
        \<comment> \<open>\<open>fill_inner\<close>'s own room premises are now literally two conjuncts of the \<open>ASSERT\<close> just
          established (\<open>shared_left\<close> is an abbreviation for \<^const>\<open>cnt\<close>), so they come for free.\<close>
        subgoal by auto                                                        \<comment> \<open>fill_inner room: branch space\<close>
        subgoal by auto                                                        \<comment> \<open>fill_inner room: lengths\<close>
        subgoal                                                                \<comment> \<open>emit step\<close>
          apply clarify
          apply (rule copy_state_emit_pres[OF _ _ op0 roomT])
          subgoal using cT by (auto simp: copy_state_inv_def)   \<comment> \<open>c < length curT\<close>
          subgoal using cB by (auto simp: copy_state_inv_def)   \<comment> \<open>c < length curB\<close>
          subgoal by assumption                                  \<comment> \<open>x \<in> it\<close>
          subgoal by (auto simp: lvt_mem sn_intv_def)            \<comment> \<open>x \<in> lvt c u\<close>
          apply assumption                                       \<comment> \<open>copy_state_inv (before): instantiates ?Br'/?Pr'\<close>
          apply assumption                                       \<comment> \<open>fill_inv result\<close>
          done
        subgoal by (clarsimp simp: copy_state_inv_def fill_state_inv_def lvt_diff_skip)  \<comment> \<open>skip step\<close>
        done
    qed

    text \<open>A segment reads back the same when the pointer cells and the branch cells it touches are
      unchanged in value.\<close>
    lemma seg_eq_on:
      assumes "Tr2 ! s = Tr' ! s" and "Tr2 ! Suc s = Tr' ! Suc s"
        and "\<And>x. x \<in> {Tr' ! s..<Tr' ! Suc s} \<Longrightarrow> Br2 ! x = Br' ! x \<and> Pr2 ! x = Pr' ! x"
      shows "seg Tr2 Br2 Pr2 s = seg Tr' Br' Pr' s"
      unfolding seg_def using assms by (auto intro!: image_mset_cong)

    text \<open>A non-sink block reads back monotone: since every emitted transition row @{term \<open>rmt t\<close>} is
      nonempty, consecutive CSR pointers strictly increase across the block, so every pointer is at
      least the opening @{term \<open>cbA c\<close>}.\<close>
    lemma block_lower_bound:
      assumes seg: "seg Tr' Br' Pr' ` {ctA c..<ctA (Suc c)} = rmt ` ltfull c"
      assumes op: "Tr' ! ctA c = cbA c"
      assumes s1: "ctA c \<le> s" and s2: "s \<le> ctA (Suc c)"
      shows "cbA c \<le> Tr' ! s"
    proof -
      have inc: "Tr' ! s' \<le> Tr' ! Suc s'" if "ctA c \<le> s'" "s' < ctA (Suc c)" for s'
      proof -
        have "seg Tr' Br' Pr' s' \<in> rmt ` ltfull c" using seg that by auto
        then obtain t where "t \<in> ltfull c" and e: "seg Tr' Br' Pr' s' = rmt t" by auto
        then have "seg Tr' Br' Pr' s' \<noteq> {#}" using rmt_nonempty by fastforce
        then have "{Tr' ! s'..<Tr' ! Suc s'} \<noteq> {}"
          by (auto simp: seg_def image_mset_is_empty_iff mset_set_empty_iff)
        then show ?thesis by simp
      qed
      have "Tr' ! ctA c \<le> Tr' ! s" using s1 s2
      proof (induction s)
        case 0 then show ?case by simp
      next
        case (Suc s)
        show ?case
        proof (cases "ctA c = Suc s")
          case True then show ?thesis by simp
        next
          case False
          with Suc.prems(1) have le: "ctA c \<le> s" by simp
          from Suc.prems(2) have lt: "s < ctA (Suc c)" and le2: "s \<le> ctA (Suc c)" by simp_all
          have "Tr' ! ctA c \<le> Tr' ! s" using Suc.IH[OF le le2] .
          also have "Tr' ! s \<le> Tr' ! Suc s" using inc[OF le lt] .
          finally show ?thesis .
        qed
      qed
      then show ?thesis using op by simp
    qed

    text \<open>Generalised monotonicity: on any range whose segments read back as nonempty rows, the CSR
      pointers are nondecreasing (used both for the final lower bound and to maintain the sweep's
      per-block lower bound across an emit).\<close>
    lemma seg_mono_lb:
      assumes seg: "seg Tr' Br' Pr' ` {a..<b} = rmt ` S"
      assumes ne: "\<And>t. t \<in> S \<Longrightarrow> rmt t \<noteq> {#}"
      assumes s1: "a \<le> s" and s2: "s \<le> b"
      shows "Tr' ! a \<le> Tr' ! s"
    proof -
      have inc: "Tr' ! s' \<le> Tr' ! Suc s'" if "a \<le> s'" "s' < b" for s'
      proof -
        have "seg Tr' Br' Pr' s' \<in> rmt ` S" using seg that by auto
        then obtain t where "t \<in> S" and "seg Tr' Br' Pr' s' = rmt t" by auto
        then have "seg Tr' Br' Pr' s' \<noteq> {#}" using ne by fastforce
        then have "{Tr' ! s'..<Tr' ! Suc s'} \<noteq> {}"
          by (auto simp: seg_def image_mset_is_empty_iff mset_set_empty_iff)
        then show ?thesis by simp
      qed
      show ?thesis using s1 s2
      proof (induction s)
        case 0 then show ?case by simp
      next
        case (Suc s)
        show ?case
        proof (cases "a = Suc s")
          case True then show ?thesis by simp
        next
          case False
          with Suc.prems(1) have le: "a \<le> s" by simp
          from Suc.prems(2) have lt: "s < b" and le2: "s \<le> b" by simp_all
          have "Tr' ! a \<le> Tr' ! s" using Suc.IH[OF le le2] .
          also have "Tr' ! s \<le> Tr' ! Suc s" using inc[OF le lt] .
          finally show ?thesis .
        qed
      qed
    qed

    text \<open>Invariant of the copy sweep. Over the already-processed states @{term \<open>{0..<N} - it\<close>}: sizes
      and global bounds are pinned, every block opening @{term \<open>Tr' ! ctA c = cbA c\<close>} holds, sinks keep
      their (untouched) cursor and opening, and each non-sink MEC @{term c} has its cursor advanced by
      its processed leaving transitions @{term \<open>ltdone c it\<close>}, its live pointer @{term \<open>Tr' ! (curT ! c)\<close>}
      pinned, its written pointers bounded in @{term \<open>[cbA c, curB ! c]\<close>}, and its written prefix reading
      back as @{term \<open>rmt ` (ltdone c it)\<close>}.\<close>
    definition "copy_sweep_inv it Tr' Br' Pr' curT curB \<longleftrightarrow>
      length Tr' = cnt_T + 1 \<and> length Br' = cnt_B \<and> length Pr' = cnt_B \<and>
      length curT = length D + 1 \<and> length curB = length D + 1 \<and>
      Tr' ! 0 = 0 \<and> (\<forall>s\<le>cnt_T. Tr' ! s \<le> cnt_B) \<and>
      (\<forall>c<length D. Tr' ! ctA c = cbA c) \<and>
      (\<forall>c<length D. (is_target_mec c \<or> out_avoid c) \<longrightarrow> curT ! c = ctA c \<and> curB ! c = cbA c) \<and>
      (\<forall>c<length D. \<not> (is_target_mec c \<or> out_avoid c) \<longrightarrow>
          curT ! c = ctA c + card (ltdone c it) \<and>
          curB ! c = cbA c + (\<Sum>t\<in>ltdone c it. cnt (TrI ! t)) \<and>
          Tr' ! (curT ! c) = curB ! c \<and>
          (\<forall>s. ctA c \<le> s \<and> s \<le> curT ! c \<longrightarrow> cbA c \<le> Tr' ! s \<and> Tr' ! s \<le> curB ! c) \<and>
          seg Tr' Br' Pr' ` {ctA c..<curT ! c} = rmt ` (ltdone c it))"

    lemma copy_sweep_final:
      assumes INV: "copy_sweep_inv {} Tr' Br' Pr' curT curB"
      shows "copy_post Tr' Br' Pr'"
    proof -
      note IC = INV[unfolded copy_sweep_inv_def]
      have LT: "length Tr' = cnt_T + 1" using IC by blast
      have LB: "length Br' = cnt_B" using IC by blast
      have LP: "length Pr' = cnt_B" using IC by blast
      have T0: "Tr' ! 0 = 0" using IC by blast
      have UP: "\<forall>s\<le>cnt_T. Tr' ! s \<le> cnt_B" using IC by blast
      have OP: "\<forall>c<length D. Tr' ! ctA c = cbA c" using IC by blast
      have NS: "\<forall>c<length D. \<not> (is_target_mec c \<or> out_avoid c) \<longrightarrow>
              curT ! c = ctA c + card (ltdone c {}) \<and> curB ! c = cbA c + (\<Sum>t\<in>ltdone c {}. cnt (TrI ! t)) \<and>
              Tr' ! (curT ! c) = curB ! c \<and> (\<forall>s. ctA c \<le> s \<and> s \<le> curT ! c \<longrightarrow> Tr' ! s \<le> curB ! c) \<and>
              seg Tr' Br' Pr' ` {ctA c..<curT ! c} = rmt ` (ltdone c {})" using IC by blast
      have block: "Tr' ! ctA (Suc c) = cbA (Suc c) \<and>
          (\<forall>s. ctA c \<le> s \<and> s \<le> ctA (Suc c) \<longrightarrow> cbA c \<le> Tr' ! s \<and> Tr' ! s \<le> cbA (Suc c)) \<and>
          seg Tr' Br' Pr' ` {ctA c..<ctA (Suc c)} = rmt ` ltfull c"
        if cD: "c < length D" and nsc: "\<not> (is_target_mec c \<or> out_avoid c)" for c
      proof -
        have cT: "curT ! c = ctA c + card (ltdone c {})" using NS cD nsc by blast
        have cB: "curB ! c = cbA c + (\<Sum>t\<in>ltdone c {}. cnt (TrI ! t))" using NS cD nsc by blast
        have op': "Tr' ! (curT ! c) = curB ! c" using NS cD nsc by blast
        have bnd: "\<forall>s. ctA c \<le> s \<and> s \<le> curT ! c \<longrightarrow> Tr' ! s \<le> curB ! c" using NS cD nsc by blast
        have seg': "seg Tr' Br' Pr' ` {ctA c..<curT ! c} = rmt ` (ltdone c {})" using NS cD nsc by blast
        have ctc: "curT ! c = ctA (Suc c)" using cT nsc by (simp add: ctA_Suc contrib_T_alt tc_card)
        have cbc: "curB ! c = cbA (Suc c)" using cB nsc by (simp add: cbA_Suc contrib_B_alt bc_sum)
        have opc: "Tr' ! ctA c = cbA c" using OP cD by blast
        have segf: "seg Tr' Br' Pr' ` {ctA c..<ctA (Suc c)} = rmt ` ltfull c"
          using seg' ctc by (simp add: ltfull_def)
        have "Tr' ! ctA (Suc c) = cbA (Suc c)" using op' ctc cbc by simp
        moreover have "\<forall>s. ctA c \<le> s \<and> s \<le> ctA (Suc c) \<longrightarrow> cbA c \<le> Tr' ! s \<and> Tr' ! s \<le> cbA (Suc c)"
        proof (intro allI impI conjI)
          fix s assume s: "ctA c \<le> s \<and> s \<le> ctA (Suc c)"
          show "cbA c \<le> Tr' ! s" using block_lower_bound[OF segf opc] s by simp
          show "Tr' ! s \<le> cbA (Suc c)" using bnd ctc cbc s by simp
        qed
        ultimately show ?thesis using segf by blast
      qed
      have blockA: "\<forall>c<length D. \<not> (is_target_mec c \<or> out_avoid c) \<longrightarrow>
          Tr' ! ctA (Suc c) = cbA (Suc c) \<and>
          (\<forall>s. ctA c \<le> s \<and> s \<le> ctA (Suc c) \<longrightarrow> cbA c \<le> Tr' ! s \<and> Tr' ! s \<le> cbA (Suc c)) \<and>
          seg Tr' Br' Pr' ` {ctA c..<ctA (Suc c)} = rmt ` ltfull c"
        using block by blast
      show ?thesis unfolding copy_post_def using LT LB LP T0 UP OP blockA by blast
    qed

    text \<open>Processing a sink state changes nothing and leaves the invariant.\<close>
    lemma copy_sweep_skip:
      assumes uit: "u \<in> it" and uN: "u < N"
      assumes sink: "is_target_mec (op_mec_index_of D u) \<or> out_avoid (op_mec_index_of D u)"
      assumes INV: "copy_sweep_inv it Tr' Br' Pr' curT curB"
      shows "copy_sweep_inv (it - {u}) Tr' Br' Pr' curT curB"
    proof -
      have key: "ltdone c (it - {u}) = ltdone c it"
        if "c < length D" "\<not> (is_target_mec c \<or> out_avoid c)" for c
      proof -
        have "c \<noteq> op_mec_index_of D u" using that sink by auto
        then show ?thesis using uit by (simp add: ltdone_skip)
      qed
      note IC = INV[unfolded copy_sweep_inv_def]
      have NS': "\<forall>c<length D. \<not> (is_target_mec c \<or> out_avoid c) \<longrightarrow>
          curT ! c = ctA c + card (ltdone c (it - {u})) \<and>
          curB ! c = cbA c + (\<Sum>t\<in>ltdone c (it - {u}). cnt (TrI ! t)) \<and>
          Tr' ! (curT ! c) = curB ! c \<and>
          (\<forall>s. ctA c \<le> s \<and> s \<le> curT ! c \<longrightarrow> cbA c \<le> Tr' ! s \<and> Tr' ! s \<le> curB ! c) \<and>
          seg Tr' Br' Pr' ` {ctA c..<curT ! c} = rmt ` (ltdone c (it - {u}))"
      proof (intro allI impI)
        fix c assume c: "c < length D" and ns: "\<not> (is_target_mec c \<or> out_avoid c)"
        have k: "ltdone c (it - {u}) = ltdone c it" using key[OF c ns] .
        show "curT ! c = ctA c + card (ltdone c (it - {u})) \<and>
              curB ! c = cbA c + (\<Sum>t\<in>ltdone c (it - {u}). cnt (TrI ! t)) \<and>
              Tr' ! (curT ! c) = curB ! c \<and>
              (\<forall>s. ctA c \<le> s \<and> s \<le> curT ! c \<longrightarrow> cbA c \<le> Tr' ! s \<and> Tr' ! s \<le> curB ! c) \<and>
              seg Tr' Br' Pr' ` {ctA c..<curT ! c} = rmt ` (ltdone c (it - {u}))"
          unfolding k using IC c ns by blast
      qed
      show ?thesis unfolding copy_sweep_inv_def using IC NS' by blast
    qed

    text \<open>Processing a non-sink state @{term u} (of MEC @{term \<open>op_mec_index_of D u\<close>}): its
      \<open>copy_state\<close> emit advances only that MEC's block; all other blocks are frozen (disjoint),
      so the invariant is preserved.\<close>
    lemma copy_sweep_step:
      assumes uit: "u \<in> it" and uN: "u < N" and mecu: "op_mec_index_of D u = c"
      assumes nonsink: "\<not> (is_target_mec c \<or> out_avoid c)"
      assumes INV: "copy_sweep_inv it Tr' Br' Pr' curT curB"
      assumes CS: "copy_state_inv u c Tr' Br' Pr' curT curB {} Tr'2 Br'2 Pr'2 curT2 curB2"
      shows "copy_sweep_inv (it - {u}) Tr'2 Br'2 Pr'2 curT2 curB2"
    proof -
      have cD: "c < length D" using uN mecu by (metis mec_lt_lenD)
      from CS[unfolded copy_state_inv_def] have
        OTH: "\<forall>c'. c' \<noteq> c \<longrightarrow> curT2 ! c' = curT ! c' \<and> curB2 ! c' = curB ! c'" and
        lenT2: "length curT2 = length curT" and lenB2: "length curB2 = length curB" and
        FSI: "fill_state_inv u c Tr' Br' Pr' (curT ! c) (curB ! c) True {} Tr'2 Br'2 Pr'2 (curT2 ! c) (curB2 ! c) True"
        by blast+
      from fill_state_emptyD[OF FSI] have
        fcT: "curT2 ! c = curT ! c + card (lvt c u)" and
        fcB: "curB2 ! c = curB ! c + (\<Sum>t\<in>lvt c u. cnt (TrI ! t))" and
        fct0: "curT ! c \<le> curT2 ! c" and fop: "Tr'2 ! (curT2 ! c) = curB2 ! c" and
        flenT: "length Tr'2 = length Tr'" and flenB: "length Br'2 = length Br'" and flenP: "length Pr'2 = length Pr'" and
        fbnd: "\<forall>s. curT ! c \<le> s \<and> s \<le> curT2 ! c \<longrightarrow> Tr'2 ! s \<le> curB2 ! c" and
        ffrzT: "\<forall>s. (s \<le> curT ! c \<or> curT2 ! c < s) \<longrightarrow> Tr'2 ! s = Tr' ! s" and
        ffrzB: "\<forall>y. (y < curB ! c \<or> curB2 ! c \<le> y) \<longrightarrow> Br'2 ! y = Br' ! y \<and> Pr'2 ! y = Pr' ! y" and
        fseg: "seg Tr'2 Br'2 Pr'2 ` {curT ! c..<curT2 ! c} = rmt ` (lvt c u)"
        by auto
      note IC = INV[unfolded copy_sweep_inv_def]
      have LT: "length Tr' = cnt_T + 1" using IC by blast
      have LB: "length Br' = cnt_B" using IC by blast
      have LP: "length Pr' = cnt_B" using IC by blast
      have LcT: "length curT = length D + 1" using IC by blast
      have LcB: "length curB = length D + 1" using IC by blast
      have T0: "Tr' ! 0 = 0" using IC by blast
      have UP: "\<forall>s\<le>cnt_T. Tr' ! s \<le> cnt_B" using IC by blast
      have OP: "\<forall>c'<length D. Tr' ! ctA c' = cbA c'" using IC by blast
      have SK: "\<forall>c'<length D. (is_target_mec c' \<or> out_avoid c') \<longrightarrow> curT ! c' = ctA c' \<and> curB ! c' = cbA c'"
        using IC by blast
      have NS: "\<forall>c'<length D. \<not> (is_target_mec c' \<or> out_avoid c') \<longrightarrow>
            curT ! c' = ctA c' + card (ltdone c' it) \<and> curB ! c' = cbA c' + (\<Sum>t\<in>ltdone c' it. cnt (TrI ! t)) \<and>
            Tr' ! (curT ! c') = curB ! c' \<and>
            (\<forall>s. ctA c' \<le> s \<and> s \<le> curT ! c' \<longrightarrow> cbA c' \<le> Tr' ! s \<and> Tr' ! s \<le> curB ! c') \<and>
            seg Tr' Br' Pr' ` {ctA c'..<curT ! c'} = rmt ` (ltdone c' it)" using IC by blast
      have cTb: "curT ! c = ctA c + card (ltdone c it)" using NS cD nonsink by blast
      have cBb: "curB ! c = cbA c + (\<Sum>t\<in>ltdone c it. cnt (TrI ! t))" using NS cD nonsink by blast
      have opb: "Tr' ! (curT ! c) = curB ! c" using NS cD nonsink by blast
      have bndb: "\<forall>s. ctA c \<le> s \<and> s \<le> curT ! c \<longrightarrow> cbA c \<le> Tr' ! s \<and> Tr' ! s \<le> curB ! c" using NS cD nonsink by blast
      have segb: "seg Tr' Br' Pr' ` {ctA c..<curT ! c} = rmt ` (ltdone c it)" using NS cD nonsink by blast
      have ctac: "ctA c \<le> curT ! c" using cTb by simp
      have cbb_le: "curB ! c \<le> curB2 ! c" using fcB by simp
      have step_lt: "ltdone c (it - {u}) = ltdone c it \<union> lvt c u" using uit uN mecu by (metis ltdone_step)
      have disj: "lvt c u \<inter> ltdone c it = {}" using uit uN by (rule lvt_ltdone_disj)
      have NcT: "curT2 ! c = ctA c + card (ltdone c (it - {u}))"
        using fcT cTb step_lt disj by (simp add: card_Un_disjoint Int_commute)
      have NcB: "curB2 ! c = cbA c + (\<Sum>t\<in>ltdone c (it - {u}). cnt (TrI ! t))"
        using fcB cBb step_lt disj by (simp add: sum.union_disjoint Int_commute)
      have sub: "ltdone c (it - {u}) \<subseteq> ltdone c {}" by (rule ltdone_sub_full)
      have curT2_le: "curT2 ! c \<le> ctA (Suc c)"
      proof -
        have "card (ltdone c (it - {u})) \<le> card (ltdone c {})" by (rule card_mono[OF finite_ltdone sub])
        then have "curT2 ! c \<le> ctA c + card (ltdone c {})" using NcT by simp
        also have "\<dots> = ctA c + tc c" by (simp add: tc_card)
        also have "\<dots> = ctA (Suc c)" using nonsink by (simp add: ctA_Suc contrib_T_alt)
        finally show ?thesis .
      qed
      have curB2_le: "curB2 ! c \<le> cbA (Suc c)"
      proof -
        have "(\<Sum>t\<in>ltdone c (it - {u}). cnt (TrI ! t)) \<le> (\<Sum>t\<in>ltdone c {}. cnt (TrI ! t))"
          by (rule sum_mono2[OF finite_ltdone sub]) auto
        then have "curB2 ! c \<le> cbA c + (\<Sum>t\<in>ltdone c {}. cnt (TrI ! t))" using NcB by simp
        also have "\<dots> = cbA c + bc c" by (simp add: bc_sum)
        also have "\<dots> = cbA (Suc c)" using nonsink by (simp add: cbA_Suc contrib_B_alt)
        finally show ?thesis .
      qed
      have bnd_close: "curB2 ! c = cbA (Suc c)" if cc2: "curT2 ! c = ctA (Suc c)"
      proof -
        have "ctA c + card (ltdone c (it - {u})) = ctA (Suc c)" using cc2 NcT by simp
        also have "ctA (Suc c) = ctA c + tc c" using nonsink by (simp add: ctA_Suc contrib_T_alt)
        finally have "card (ltdone c (it - {u})) = card (ltdone c {})" by (simp add: tc_card)
        then have eq: "ltdone c (it - {u}) = ltdone c {}"
          using card_subset_eq[OF finite_ltdone sub] by blast
        show ?thesis using NcB eq nonsink by (simp add: cbA_Suc contrib_B_alt bc_sum)
      qed
      \<comment> \<open>every other block is frozen (disjoint from the region this emit touches)\<close>
      have Tfrz: "Tr'2 ! s = Tr' ! s" if c'D: "c' < length D" and c'c: "c' \<noteq> c"
          and sr1: "ctA c' \<le> s" and sr2: "s \<le> ctA (Suc c')" for c' s
      proof (cases "c' < c")
        case True
        have "ctA (Suc c') \<le> ctA c" using True by (simp add: ctA_le_iff)
        then have "s \<le> curT ! c" using sr2 ctac by simp
        then show ?thesis using ffrzT by simp
      next
        case False
        with c'c have cc': "c < c'" by simp
        have le1: "ctA (Suc c) \<le> ctA c'" using cc' by (simp add: ctA_le_iff)
        show ?thesis
        proof (cases "curT2 ! c < s")
          case True then show ?thesis using ffrzT by simp
        next
          case False
          have "curT2 ! c \<le> ctA c'" using curT2_le le1 by simp
          then have "curT2 ! c \<le> s" using sr1 by simp
          with False have seq: "s = curT2 ! c" by simp
          have "s \<le> ctA c'" using seq \<open>curT2 ! c \<le> ctA c'\<close> by simp
          with sr1 have sc': "s = ctA c'" by simp
          have suceq: "curT2 ! c = ctA (Suc c)" using seq sc' le1 curT2_le by (metis le_antisym)
          have "Tr'2 ! s = curB2 ! c" using fop seq by simp
          also have "\<dots> = cbA (Suc c)" using bnd_close suceq by simp
          also have "\<dots> = cbA c'" using sc' seq suceq by (metis ctA_eq_iff)
          also have "\<dots> = Tr' ! ctA c'" using OP c'D by auto
          also have "ctA c' = s" using sc' by simp
          finally show ?thesis .
        qed
      qed
      have Bfrz: "Br'2 ! y = Br' ! y \<and> Pr'2 ! y = Pr' ! y"
          if c'D: "c' < length D" and c'c: "c' \<noteq> c" and yr1: "cbA c' \<le> y" and yr2: "y < cbA (Suc c')" for c' y
      proof (cases "c' < c")
        case True
        have "cbA (Suc c') \<le> cbA c" using True by (simp add: cbA_le_iff)
        then have "y < curB ! c" using yr2 cBb by simp
        then show ?thesis using ffrzB by simp
      next
        case False
        with c'c have cc': "c < c'" by simp
        have "cbA (Suc c) \<le> cbA c'" using cc' by (simp add: cbA_le_iff)
        then have "curB2 ! c \<le> y" using curB2_le yr1 by simp
        then show ?thesis using ffrzB by simp
      qed
      \<comment> \<open>the six invariant clauses for the updated arrays\<close>
      have L1: "length Tr'2 = cnt_T + 1" using flenT LT by simp
      have L2: "length Br'2 = cnt_B" using flenB LB by simp
      have L3: "length Pr'2 = cnt_B" using flenP LP by simp
      have L4: "length curT2 = length D + 1" using lenT2 LcT by simp
      have L5: "length curB2 = length D + 1" using lenB2 LcB by simp
      have TT0: "Tr'2 ! 0 = 0" using ffrzT T0 by simp
      have UUP: "\<forall>s\<le>cnt_T. Tr'2 ! s \<le> cnt_B"
      proof (intro allI impI)
        fix s assume s: "s \<le> cnt_T"
        show "Tr'2 ! s \<le> cnt_B"
        proof (cases "curT ! c < s \<and> s \<le> curT2 ! c")
          case True
          then have "Tr'2 ! s \<le> curB2 ! c" using fbnd by simp
          also have "curB2 ! c \<le> cbA (Suc c)" using curB2_le .
          also have "\<dots> \<le> cnt_B" using cbA_le_cnt_B[of "Suc c"] cD by simp
          finally show ?thesis .
        next
          case False
          then have "Tr'2 ! s = Tr' ! s" using ffrzT by auto
          then show ?thesis using UP s by simp
        qed
      qed
      have OOP: "\<forall>c'<length D. Tr'2 ! ctA c' = cbA c'"
      proof (intro allI impI)
        fix c' assume c'D: "c' < length D"
        show "Tr'2 ! ctA c' = cbA c'"
        proof (cases "c' = c")
          case True
          then have "Tr'2 ! ctA c' = Tr' ! ctA c'" using ffrzT ctac by simp
          then show ?thesis using OP c'D by simp
        next
          case False
          have "Tr'2 ! ctA c' = Tr' ! ctA c'" using Tfrz[OF c'D False, of "ctA c'"] by (simp add: ctA_le_iff)
          then show ?thesis using OP c'D by simp
        qed
      qed
      have SSK: "\<forall>c'<length D. (is_target_mec c' \<or> out_avoid c') \<longrightarrow> curT2 ! c' = ctA c' \<and> curB2 ! c' = cbA c'"
      proof (intro allI impI)
        fix c' assume c'D: "c' < length D" and sk': "is_target_mec c' \<or> out_avoid c'"
        have "c' \<noteq> c" using sk' nonsink by auto
        then have "curT2 ! c' = curT ! c'" "curB2 ! c' = curB ! c'" using OTH by auto
        moreover have "curT ! c' = ctA c'" "curB ! c' = cbA c'" using SK c'D sk' by auto
        ultimately show "curT2 ! c' = ctA c' \<and> curB2 ! c' = cbA c'" by simp
      qed
      have NNS: "\<forall>c'<length D. \<not> (is_target_mec c' \<or> out_avoid c') \<longrightarrow>
          curT2 ! c' = ctA c' + card (ltdone c' (it - {u})) \<and>
          curB2 ! c' = cbA c' + (\<Sum>t\<in>ltdone c' (it - {u}). cnt (TrI ! t)) \<and>
          Tr'2 ! (curT2 ! c') = curB2 ! c' \<and>
          (\<forall>s. ctA c' \<le> s \<and> s \<le> curT2 ! c' \<longrightarrow> cbA c' \<le> Tr'2 ! s \<and> Tr'2 ! s \<le> curB2 ! c') \<and>
          seg Tr'2 Br'2 Pr'2 ` {ctA c'..<curT2 ! c'} = rmt ` (ltdone c' (it - {u}))"
      proof (intro allI impI)
        fix c' assume c'D: "c' < length D" and ns': "\<not> (is_target_mec c' \<or> out_avoid c')"
        show "curT2 ! c' = ctA c' + card (ltdone c' (it - {u})) \<and>
              curB2 ! c' = cbA c' + (\<Sum>t\<in>ltdone c' (it - {u}). cnt (TrI ! t)) \<and>
              Tr'2 ! (curT2 ! c') = curB2 ! c' \<and>
              (\<forall>s. ctA c' \<le> s \<and> s \<le> curT2 ! c' \<longrightarrow> cbA c' \<le> Tr'2 ! s \<and> Tr'2 ! s \<le> curB2 ! c') \<and>
              seg Tr'2 Br'2 Pr'2 ` {ctA c'..<curT2 ! c'} = rmt ` (ltdone c' (it - {u}))"
        proof (cases "c' = c")
          case True
          have ltsub: "rmt t \<noteq> {#}" if "t \<in> lvt c u" for t
          proof -
            have "lvt c u \<subseteq> ltfull c" using uN mecu lvt_sub_full[of u c] by (simp add: ltfull_def)
            then show ?thesis using that rmt_nonempty by auto
          qed
          have Topen: "Tr'2 ! (curT ! c) = curB ! c" using ffrzT opb by simp
          have newlb: "curB ! c \<le> Tr'2 ! s" if "curT ! c \<le> s" "s \<le> curT2 ! c" for s
            using seg_mono_lb[OF fseg ltsub that] Topen by simp
          have bnd2: "\<forall>s. ctA c \<le> s \<and> s \<le> curT2 ! c \<longrightarrow> cbA c \<le> Tr'2 ! s \<and> Tr'2 ! s \<le> curB2 ! c"
          proof (intro allI impI)
            fix s assume s: "ctA c \<le> s \<and> s \<le> curT2 ! c"
            show "cbA c \<le> Tr'2 ! s \<and> Tr'2 ! s \<le> curB2 ! c"
            proof (cases "s \<le> curT ! c")
              case True
              have "Tr'2 ! s = Tr' ! s" using ffrzT True by simp
              moreover have "cbA c \<le> Tr' ! s \<and> Tr' ! s \<le> curB ! c" using bndb s True by simp
              ultimately show ?thesis using cbb_le by simp
            next
              case False
              then have s': "curT ! c \<le> s" by simp
              have "cbA c \<le> curB ! c" using cBb by simp
              also have "curB ! c \<le> Tr'2 ! s" using newlb s' s by simp
              finally have "cbA c \<le> Tr'2 ! s" .
              moreover have "Tr'2 ! s \<le> curB2 ! c" using fbnd s' s by simp
              ultimately show ?thesis by simp
            qed
          qed
          have seg_old_c: "seg Tr'2 Br'2 Pr'2 s = seg Tr' Br' Pr' s" if sm: "s \<in> {ctA c..<curT ! c}" for s
          proof (rule seg_eq_on)
            from sm have s0: "ctA c \<le> s" and slt: "s < curT ! c" by auto
            show "Tr'2 ! s = Tr' ! s" using ffrzT slt by simp
            show "Tr'2 ! Suc s = Tr' ! Suc s" using ffrzT slt by simp
            fix x assume x: "x \<in> {Tr' ! s..<Tr' ! Suc s}"
            have "Tr' ! Suc s \<le> curB ! c" using bndb s0 slt by simp
            then have "x < curB ! c" using x by simp
            then show "Br'2 ! x = Br' ! x \<and> Pr'2 ! x = Pr' ! x" using ffrzB by simp
          qed
          have seg2: "seg Tr'2 Br'2 Pr'2 ` {ctA c..<curT2 ! c} = rmt ` (ltdone c (it - {u}))"
          proof -
            have "{ctA c..<curT2 ! c} = {ctA c..<curT ! c} \<union> {curT ! c..<curT2 ! c}"
              using ctac fct0 by auto
            then have "seg Tr'2 Br'2 Pr'2 ` {ctA c..<curT2 ! c}
                = seg Tr'2 Br'2 Pr'2 ` {ctA c..<curT ! c} \<union> rmt ` (lvt c u)"
              by (simp add: image_Un fseg)
            also have "seg Tr'2 Br'2 Pr'2 ` {ctA c..<curT ! c} = seg Tr' Br' Pr' ` {ctA c..<curT ! c}"
              by (rule image_cong[OF refl seg_old_c])
            also have "\<dots> = rmt ` (ltdone c it)" using segb .
            also have "rmt ` (ltdone c it) \<union> rmt ` (lvt c u) = rmt ` (ltdone c (it - {u}))"
              using step_lt by (simp add: image_Un)
            finally show ?thesis .
          qed
          show ?thesis unfolding True using NcT NcB fop bnd2 seg2 by blast
        next
          case False
          have skip': "ltdone c' (it - {u}) = ltdone c' it" using uit mecu False by (metis ltdone_skip)
          have oT: "curT2 ! c' = curT ! c'" and oB: "curB2 ! c' = curB ! c'" using OTH False by auto
          have cT': "curT ! c' = ctA c' + card (ltdone c' it)" using NS c'D ns' by blast
          have cB': "curB ! c' = cbA c' + (\<Sum>t\<in>ltdone c' it. cnt (TrI ! t))" using NS c'D ns' by blast
          have op': "Tr' ! (curT ! c') = curB ! c'" using NS c'D ns' by blast
          have bnd': "\<forall>s. ctA c' \<le> s \<and> s \<le> curT ! c' \<longrightarrow> cbA c' \<le> Tr' ! s \<and> Tr' ! s \<le> curB ! c'" using NS c'D ns' by blast
          have seg': "seg Tr' Br' Pr' ` {ctA c'..<curT ! c'} = rmt ` (ltdone c' it)" using NS c'D ns' by blast
          have curTc'_le: "curT ! c' \<le> ctA (Suc c')"
          proof -
            have "card (ltdone c' it) \<le> card (ltdone c' {})" by (rule card_mono[OF finite_ltdone ltdone_sub_full])
            then have "curT ! c' \<le> ctA c' + card (ltdone c' {})" using cT' by simp
            also have "\<dots> = ctA c' + tc c'" by (simp add: tc_card)
            also have "\<dots> = ctA (Suc c')" using ns' by (simp add: ctA_Suc contrib_T_alt)
            finally show ?thesis .
          qed
          have curBc'_le: "curB ! c' \<le> cbA (Suc c')"
          proof -
            have "(\<Sum>t\<in>ltdone c' it. cnt (TrI ! t)) \<le> (\<Sum>t\<in>ltdone c' {}. cnt (TrI ! t))"
              by (rule sum_mono2[OF finite_ltdone ltdone_sub_full]) auto
            then have "curB ! c' \<le> cbA c' + (\<Sum>t\<in>ltdone c' {}. cnt (TrI ! t))" using cB' by simp
            also have "\<dots> = cbA c' + bc c'" by (simp add: bc_sum)
            also have "\<dots> = cbA (Suc c')" using ns' by (simp add: cbA_Suc contrib_B_alt)
            finally show ?thesis .
          qed
          have Tfrz': "Tr'2 ! s = Tr' ! s" if "ctA c' \<le> s" "s \<le> curT ! c'" for s
            using Tfrz[OF c'D False that(1)] that(2) curTc'_le by simp
          have op2': "Tr'2 ! (curT2 ! c') = curB2 ! c'"
          proof -
            have "Tr'2 ! (curT2 ! c') = Tr' ! (curT ! c')" using oT Tfrz'[of "curT ! c'"] cT' by simp
            then show ?thesis using op' oB by simp
          qed
          have bnd2': "\<forall>s. ctA c' \<le> s \<and> s \<le> curT2 ! c' \<longrightarrow> cbA c' \<le> Tr'2 ! s \<and> Tr'2 ! s \<le> curB2 ! c'"
          proof (intro allI impI)
            fix s assume s: "ctA c' \<le> s \<and> s \<le> curT2 ! c'"
            then have s1: "ctA c' \<le> s" and s2: "s \<le> curT ! c'" using oT by auto
            have "Tr'2 ! s = Tr' ! s" using Tfrz' s1 s2 by simp
            moreover have "cbA c' \<le> Tr' ! s \<and> Tr' ! s \<le> curB ! c'" using bnd' s1 s2 by simp
            ultimately show "cbA c' \<le> Tr'2 ! s \<and> Tr'2 ! s \<le> curB2 ! c'" using oB by simp
          qed
          have seg_pres': "seg Tr'2 Br'2 Pr'2 s = seg Tr' Br' Pr' s" if sm: "s \<in> {ctA c'..<curT ! c'}" for s
          proof (rule seg_eq_on)
            from sm have s0: "ctA c' \<le> s" and slt: "s < curT ! c'" by auto
            have s0S: "ctA c' \<le> Suc s" using s0 by simp
            have sSle: "Suc s \<le> curT ! c'" using slt by simp
            show "Tr'2 ! s = Tr' ! s" using Tfrz' s0 slt by simp
            show "Tr'2 ! Suc s = Tr' ! Suc s" using Tfrz' s0S sSle by simp
            fix x assume x: "x \<in> {Tr' ! s..<Tr' ! Suc s}"
            have "cbA c' \<le> Tr' ! s" using bnd' s0 slt by simp
            moreover have "Tr' ! Suc s \<le> curB ! c'" using bnd' s0S sSle by simp
            ultimately have "x \<in> {cbA c'..<cbA (Suc c')}" using x curBc'_le by simp
            then show "Br'2 ! x = Br' ! x \<and> Pr'2 ! x = Pr' ! x" using Bfrz[OF c'D False] by simp
          qed
          have seg2': "seg Tr'2 Br'2 Pr'2 ` {ctA c'..<curT2 ! c'} = rmt ` (ltdone c' (it - {u}))"
          proof -
            have "seg Tr'2 Br'2 Pr'2 ` {ctA c'..<curT2 ! c'} = seg Tr' Br' Pr' ` {ctA c'..<curT ! c'}"
              unfolding oT by (rule image_cong[OF refl seg_pres'])
            also have "\<dots> = rmt ` (ltdone c' it)" using seg' .
            also have "ltdone c' it = ltdone c' (it - {u})" using skip' by simp
            finally show ?thesis .
          qed
          have NcT': "curT2 ! c' = ctA c' + card (ltdone c' (it - {u}))" using oT cT' skip' by simp
          have NcB': "curB2 ! c' = cbA c' + (\<Sum>t\<in>ltdone c' (it - {u}). cnt (TrI ! t))" using oB cB' skip' by simp
          show ?thesis using NcT' NcB' op2' bnd2' seg2' by blast
        qed
      qed
      show ?thesis unfolding copy_sweep_inv_def
        using L1 L2 L3 L4 L5 TT0 UUP OOP SSK NNS by blast
    qed

    lemma copy_sweep_body:
      assumes uit: "u \<in> it" and itN: "it \<subseteq> {0..<N}"
      assumes Ta': "Ta' = {c. c < length D \<and> is_target_mec c}"
      assumes Av': "Av' = {c. c < length D \<and> out_avoid c}"
      assumes INV: "copy_sweep_inv it Tr' Br' Pr' curT curB"
      shows "(let c = op_mec_index_of D u in
                if c \<in> Ta' \<or> c \<in> Av' then RETURN (Tr', Br', Pr', curT, curB)
                else FOREACH (sn_intv (StI ! u))
                  (\<lambda>t (Tr', Br', Pr', curT, curB).
                     if trans_leaves c t then do {
                       ASSERT (c < length curT \<and> c < length curB
                               \<and> curT ! c < length Tr' \<and> curT ! c + 1 < length Tr'
                               \<and> curT ! c < length Tr
                               \<and> curB ! c + cnt (TrI ! t) \<le> length Br'
                               \<and> length Pr' = length Br' \<and> length Br' \<le> length Br);
                       let Tr' = Tr'[curT ! c := curB ! c];
                       (Br', Pr', cbc) \<leftarrow> FOREACH (sn_intv (TrI ! t))
                          (\<lambda>b (Br', Pr', cbc). RETURN (Br'[cbc := op_mec_index_of D (Br ! b)], Pr'[cbc := Pr ! b], cbc + 1))
                          (Br', Pr', curB ! c);
                       let curB = curB[c := cbc];
                       let Tr' = Tr'[curT ! c + 1 := curB ! c];
                       RETURN (Tr', Br', Pr', curT[c := curT ! c + 1], curB)
                     } else RETURN (Tr', Br', Pr', curT, curB))
                  (Tr', Br', Pr', curT, curB))
        \<le> SPEC (\<lambda>(Tr'2, Br'2, Pr'2, curT2, curB2). copy_sweep_inv (it - {u}) Tr'2 Br'2 Pr'2 curT2 curB2)"
    proof -
      have uN: "u < N" using uit itN by auto
      have cD: "op_mec_index_of D u < length D" using uN by (rule mec_lt_lenD)
      show ?thesis
      proof (cases "op_mec_index_of D u \<in> Ta' \<or> op_mec_index_of D u \<in> Av'")
        case True
        then have "is_target_mec (op_mec_index_of D u) \<or> out_avoid (op_mec_index_of D u)"
          using Ta' Av' cD by auto
        then have "copy_sweep_inv (it - {u}) Tr' Br' Pr' curT curB"
          using copy_sweep_skip[OF uit uN _ INV] by blast
        then show ?thesis using True by (simp add: Let_def)
      next
        case False
        define c where "c = op_mec_index_of D u"
        have notc: "c \<notin> Ta' \<and> c \<notin> Av'" using False c_def by simp
        have ns: "\<not> (is_target_mec c \<or> out_avoid c)" using False Ta' Av' cD by (auto simp: c_def)
        from INV[unfolded copy_sweep_inv_def] have
          LB: "length Br' = cnt_B" and LP: "length Pr' = cnt_B" and LT: "length Tr' = cnt_T + 1" and
          LcT: "length curT = length D + 1" and LcB: "length curB = length D + 1" and
          NSc: "curT ! c = ctA c + card (ltdone c it) \<and> curB ! c = cbA c + (\<Sum>t\<in>ltdone c it. cnt (TrI ! t)) \<and>
                Tr' ! (curT ! c) = curB ! c \<and> (\<forall>s. ctA c \<le> s \<and> s \<le> curT ! c \<longrightarrow> Tr' ! s \<le> curB ! c) \<and>
                seg Tr' Br' Pr' ` {ctA c..<curT ! c} = rmt ` (ltdone c it)"
          using cD ns c_def by blast+
        have cDc: "c < length D" using cD c_def by simp
        have op0: "Tr' ! (curT ! c) = curB ! c" using NSc by blast
        have lenBR: "length Pr' = length Br'" using LB LP by simp
        have cT: "c < length curT" using cDc LcT by simp
        have cB: "c < length curB" using cDc LcB by simp
        have cTval: "curT ! c = ctA c + card (ltdone c it)" using NSc by blast
        have cBval: "curB ! c = cbA c + (\<Sum>t\<in>ltdone c it. cnt (TrI ! t))" using NSc by blast
        have roomB: "curB ! c + (\<Sum>t\<in>lvt c u. cnt (TrI ! t)) \<le> length Br'"
        proof -
          have "curB ! c + (\<Sum>t\<in>lvt c u. cnt (TrI ! t)) = cbA c + ((\<Sum>t\<in>ltdone c it. cnt (TrI ! t)) + (\<Sum>t\<in>lvt c u. cnt (TrI ! t)))"
            using cBval by simp
          also have "\<dots> \<le> cbA c + bc c" using room_sum[OF uit uN c_def[symmetric]] by simp
          also have "\<dots> = cbA (Suc c)" using ns by (simp add: cbA_Suc contrib_B_alt)
          also have "\<dots> \<le> cnt_B" using cbA_le_cnt_B[of "Suc c"] cDc by simp
          finally show ?thesis using LB by simp
        qed
        have capT: "length Tr' \<le> length Tr" using LT Suc_cnt_T_le_length_Tr by simp
        have capB: "length Br' \<le> length Br" using LB cnt_B_le_length_Br by simp
        have roomT: "curT ! c + card (lvt c u) < length Tr'"
        proof -
          have "curT ! c + card (lvt c u) = ctA c + (card (ltdone c it) + card (lvt c u))"
            using cTval by simp
          also have "\<dots> \<le> ctA c + tc c" using room_card[OF uit uN c_def[symmetric]] by simp
          also have "\<dots> = ctA (Suc c)" using ns by (simp add: ctA_Suc contrib_T_alt)
          also have "\<dots> \<le> cnt_T" using ctA_le_cnt_T[of "Suc c"] cDc by simp
          finally show ?thesis using LT by simp
        qed
        have "FOREACH (sn_intv (StI ! u))
              (\<lambda>t (Tr', Br', Pr', curT, curB).
                 if trans_leaves c t then do {
                   ASSERT (c < length curT \<and> c < length curB
                           \<and> curT ! c < length Tr' \<and> curT ! c + 1 < length Tr'
                           \<and> curT ! c < length Tr
                           \<and> curB ! c + cnt (TrI ! t) \<le> length Br'
                           \<and> length Pr' = length Br' \<and> length Br' \<le> length Br);
                   let Tr' = Tr'[curT ! c := curB ! c];
                   (Br', Pr', cbc) \<leftarrow> FOREACH (sn_intv (TrI ! t))
                      (\<lambda>b (Br', Pr', cbc). RETURN (Br'[cbc := op_mec_index_of D (Br ! b)], Pr'[cbc := Pr ! b], cbc + 1))
                      (Br', Pr', curB ! c);
                   let curB = curB[c := cbc];
                   let Tr' = Tr'[curT ! c + 1 := curB ! c];
                   RETURN (Tr', Br', Pr', curT[c := curT ! c + 1], curB)
                 } else RETURN (Tr', Br', Pr', curT, curB))
              (Tr', Br', Pr', curT, curB)
            \<le> SPEC (\<lambda>(Tr'2, Br'2, Pr'2, curT2, curB2).
                copy_state_inv u c Tr' Br' Pr' curT curB {} Tr'2 Br'2 Pr'2 curT2 curB2)"
          by (rule copy_state[OF cT cB op0 lenBR roomB roomT capT capB])
        also have "SPEC (\<lambda>(Tr'2, Br'2, Pr'2, curT2, curB2).
                copy_state_inv u c Tr' Br' Pr' curT curB {} Tr'2 Br'2 Pr'2 curT2 curB2)
            \<le> SPEC (\<lambda>(Tr'2, Br'2, Pr'2, curT2, curB2). copy_sweep_inv (it - {u}) Tr'2 Br'2 Pr'2 curT2 curB2)"
          by (rule SPEC_rule) (auto intro: copy_sweep_step[OF uit uN c_def[symmetric] ns INV])
        finally show ?thesis
          using notc unfolding c_def[symmetric] by (simp add: Let_def cong: if_weak_cong)
      qed
    qed

    lemma copy_sweep_correct:
      assumes StA: "\<forall>c\<le>length D. St' ! c = ctA c"
      assumes bA: "\<forall>c\<le>length D. boff ! c = cbA c"
      assumes lenSt: "length St' = length D + 1" and lenboff: "length boff = length D + 1"
      assumes Ta': "Ta' = {c. c < length D \<and> is_target_mec c}"
      assumes Av': "Av' = {c. c < length D \<and> out_avoid c}"
      assumes nB: "nB = cnt_B"
      assumes pw1: "length Tr'0 = cnt_T + 1" and pw2: "\<forall>c<length D. Tr'0 ! ctA c = cbA c"
      assumes pw3: "\<forall>s\<le>cnt_T. Tr'0 ! s \<le> cnt_B" and pw4: "Tr'0 ! 0 = 0"
      shows "FOREACH {0..<N}
          (\<lambda>u (Tr', Br', Pr', curT, curB). do {
             let c = op_mec_index_of D u;
             if c \<in> Ta' \<or> c \<in> Av' then RETURN (Tr', Br', Pr', curT, curB)
             else FOREACH (sn_intv (StI ! u))
                (\<lambda>t (Tr', Br', Pr', curT, curB).
                   if trans_leaves c t then do {
                     ASSERT (c < length curT \<and> c < length curB
                             \<and> curT ! c < length Tr' \<and> curT ! c + 1 < length Tr'
                             \<and> curT ! c < length Tr
                             \<and> curB ! c + cnt (TrI ! t) \<le> length Br'
                             \<and> length Pr' = length Br' \<and> length Br' \<le> length Br);
                     let Tr' = Tr'[curT ! c := curB ! c];
                     (Br', Pr', cbc) \<leftarrow> FOREACH (sn_intv (TrI ! t))
                        (\<lambda>b (Br', Pr', cbc). RETURN (Br'[cbc := op_mec_index_of D (Br ! b)], Pr'[cbc := Pr ! b], cbc + 1))
                        (Br', Pr', curB ! c);
                     let curB = curB[c := cbc];
                     let Tr' = Tr'[curT ! c + 1 := curB ! c];
                     RETURN (Tr', Br', Pr', curT[c := curT ! c + 1], curB)
                   } else RETURN (Tr', Br', Pr', curT, curB))
                (Tr', Br', Pr', curT, curB) })
          (Tr'0, replicate nB 0, replicate nB 1, St', boff)
        \<le> SPEC (\<lambda>(Tr', Br', Pr', curT, curB). copy_post Tr' Br' Pr')"
      apply (rule FOREACH_rule[where I="\<lambda>it (Tr', Br', Pr', curT, curB). copy_sweep_inv it Tr' Br' Pr' curT curB"])
      subgoal by simp
      subgoal
        unfolding copy_sweep_inv_def
        using StA bA pw1 pw2 pw3 pw4 lenSt lenboff nB by (auto simp: ltdone_def)
      subgoal for u it \<sigma>
        apply (cases \<sigma>)
        apply (simp only: prod.case)
        by (rule copy_sweep_body[OF _ _ Ta' Av']; assumption)
      subgoal for \<sigma> by (cases \<sigma>) (auto dest: copy_sweep_final)
      done

    lemma copy_pass_correct:
      assumes StA: "\<forall>c\<le>length D. St' ! c = ctA c"
      assumes bA: "\<forall>c\<le>length D. boff ! c = cbA c"
      assumes lenSt: "length St' = length D + 1" and lenboff: "length boff = length D + 1"
      assumes Ta': "Ta' = {c. c < length D \<and> is_target_mec c}"
      assumes Av': "Av' = {c. c < length D \<and> out_avoid c}"
      assumes nT: "nT = cnt_T" and nB: "nB = cnt_B"
      shows "copy_pass St' boff Ta' Av' nT nB
         \<le> SPEC (\<lambda>(Tr', Br', Pr', curT, curB). copy_post Tr' Br' Pr')"
      unfolding copy_pass_def
      apply (simp only: nT)
      apply (refine_vcg copy_prewrite_correct[THEN order_trans, OF StA bA]
          copy_sweep_correct[THEN order_trans, OF StA bA lenSt lenboff Ta' Av' nB])
      apply (simp_all add: nB)
      by (rule cnt_T_lt_length_Tr)

    text \<open>The same statement for the pass \<^emph>\<open>projected\<close> to the three built arrays --- the shape in which
      the LLVM implementation refines it (\<open>copy_ll_impl\<close> drops the spent cursors), so that the combined
      builder's refinement can chain the two first-order.\<close>
    lemma copy_pass_correct3:
      assumes StA: "\<forall>c\<le>length D. St' ! c = ctA c"
      assumes bA: "\<forall>c\<le>length D. boff ! c = cbA c"
      assumes lenSt: "length St' = length D + 1" and lenboff: "length boff = length D + 1"
      assumes Ta': "Ta' = {c. c < length D \<and> is_target_mec c}"
      assumes Av': "Av' = {c. c < length D \<and> out_avoid c}"
      assumes nT: "nT = cnt_T" and nB: "nB = cnt_B"
      shows "copy_pass St' boff Ta' Av' nT nB \<bind> (\<lambda>(Tr', Br', Pr', curT, curB). RETURN (Tr', Br', Pr'))
         \<le> SPEC (\<lambda>(Tr', Br', Pr'). copy_post Tr' Br' Pr')"
      using copy_pass_correct[OF StA bA lenSt lenboff Ta' Av' nT nB]
      by (auto simp: pw_le_iff refine_pw_simps)

    subsubsection \<open>Pass 5: self-loops\<close>

    lemma sink_contrib1: "is_target_mec c \<or> out_avoid c \<Longrightarrow> contrib_T c = 1 \<and> contrib_B c = 1"
      by (auto simp: contrib_T_def contrib_B_def out_avoid_def)

    text \<open>The array-index bounds the self-loop pass's \<^emph>\<open>implementation\<close> needs, read off the copy
      postcondition and the offset semantics: MEC \<^term>\<open>c\<close>'s block start
      \<^term>\<open>ctA c\<close> / \<^term>\<open>cbA c\<close> lies strictly inside the built arrays (strictly, because every MEC
      contributes at least one slot --- @{thm [source] contrib_T_pos}). All bounds are \<^emph>\<open>relative\<close> to
      the built arrays; the machine-word bounds on the cursor increments are recovered at the
      \<open>sepref\<close> layer from the array assertions themselves.\<close>
    lemma selfloop_sink_bounds:
      assumes cp: "copy_post Tr' Br' Pr'"
      assumes StA: "\<forall>c\<le>length D. St' ! c = ctA c"
      assumes bA: "\<forall>c\<le>length D. boff ! c = cbA c"
      assumes lenSt: "length St' = length D + 1" and lenboff: "length boff = length D + 1"
      shows "\<forall>c<length D. c < length St' \<and> c < length boff
          \<and> St' ! c < length Tr' \<and> St' ! c + 1 < length Tr'
          \<and> boff ! c < length Br' \<and> boff ! c < length Pr'
          \<and> St' ! c < length Tr \<and> boff ! c < length Br"
    proof (intro allI impI)
      fix c assume c: "c < length D"
      have Sc: "St' ! c = ctA c" using StA c by simp
      have bc: "boff ! c = cbA c" using bA c by simp
      have LT: "length Tr' = cnt_T + 1" and LB: "length Br' = cnt_B" and LP: "length Pr' = cnt_B"
        using cp by (auto simp: copy_post_def)
      have ct: "ctA c < cnt_T" unfolding cnt_T_ctA using c by (rule ctA_strict_mono)
      have cb: "cbA c < cnt_B" unfolding cnt_B_cbA using c by (rule cbA_strict_mono)
      have ctTr: "ctA c < length Tr" using ct Suc_cnt_T_le_length_Tr by simp
      have cbBr: "cbA c < length Br" using cb cnt_B_le_length_Br by simp
      show "c < length St' \<and> c < length boff
          \<and> St' ! c < length Tr' \<and> St' ! c + 1 < length Tr'
          \<and> boff ! c < length Br' \<and> boff ! c < length Pr'
          \<and> St' ! c < length Tr \<and> boff ! c < length Br"
        using c ct cb ctTr cbBr by (simp add: Sc bc LT LB LP lenSt lenboff)
    qed

    text \<open>A sink MEC's one-slot block reads back as the self-loop \<open>{#(c,1)#}\<close>.\<close>
    lemma seg_sink_block:
      assumes op: "Tr' ! ctA c = cbA c" and cl: "Tr' ! (ctA c + 1) = cbA c + 1"
        and brc: "Br' ! cbA c = c" and prc: "Pr' ! cbA c = 1"
        and sink: "is_target_mec c \<or> out_avoid c"
      shows "seg Tr' Br' Pr' ` {ctA c..<ctA (Suc c)} = {{#(c, 1::real)#}}"
    proof -
      have "ctA (Suc c) = ctA c + 1" using sink by (simp add: ctA_Suc sink_contrib1)
      moreover have "seg Tr' Br' Pr' (ctA c) = {#(c, 1::real)#}"
        unfolding seg_def using op cl brc prc by simp
      ultimately show ?thesis by simp
    qed

    definition "selfloop_inv it Tr' Br' Pr' \<longleftrightarrow>
      length Tr' = cnt_T + 1 \<and> length Br' = cnt_B \<and> length Pr' = cnt_B \<and>
      Tr' ! 0 = 0 \<and> (\<forall>s\<le>cnt_T. Tr' ! s \<le> cnt_B) \<and>
      (\<forall>c<length D. Tr' ! ctA c = cbA c) \<and>
      (\<forall>c<length D. \<not> (is_target_mec c \<or> out_avoid c) \<longrightarrow>
          Tr' ! ctA (Suc c) = cbA (Suc c) \<and>
          (\<forall>s. ctA c \<le> s \<and> s \<le> ctA (Suc c) \<longrightarrow> cbA c \<le> Tr' ! s \<and> Tr' ! s \<le> cbA (Suc c)) \<and>
          seg Tr' Br' Pr' ` {ctA c..<ctA (Suc c)} = rmt ` ltfull c) \<and>
      (\<forall>c<length D. (is_target_mec c \<or> out_avoid c) \<and> c \<notin> it \<longrightarrow>
          Tr' ! ctA (Suc c) = cbA (Suc c) \<and> Br' ! cbA c = c \<and> Pr' ! cbA c = 1)"

    lemma selfloop_inv_start: "copy_post Tr' Br' Pr' \<Longrightarrow> selfloop_inv {0..<length D} Tr' Br' Pr'"
      by (auto simp: selfloop_inv_def copy_post_def)

    lemma selfloop_inv_final:
      assumes INV: "selfloop_inv {} Tr' Br' Pr'"
      shows "length Tr' = cnt_T + 1 \<and> length Br' = cnt_B \<and> length Pr' = cnt_B \<and>
             Tr' ! 0 = 0 \<and> Tr' ! cnt_T = cnt_B \<and> (\<forall>s\<le>cnt_T. Tr' ! s \<le> cnt_B) \<and>
             (\<forall>j<length D. seg Tr' Br' Pr' ` {ctA j..<ctA (Suc j)} = rowset j)"
    proof -
      from INV have L: "length Tr' = cnt_T + 1" and Tr0: "Tr' ! 0 = 0"
        and mono: "\<forall>s\<le>cnt_T. Tr' ! s \<le> cnt_B"
        and op: "\<And>c. c<length D \<Longrightarrow> Tr' ! ctA c = cbA c"
        and ns: "\<And>c. c<length D \<Longrightarrow> \<not> (is_target_mec c \<or> out_avoid c) \<Longrightarrow>
              Tr' ! ctA (Suc c) = cbA (Suc c) \<and> seg Tr' Br' Pr' ` {ctA c..<ctA (Suc c)} = rmt ` ltfull c"
        and sk: "\<And>c. c<length D \<Longrightarrow> is_target_mec c \<or> out_avoid c \<Longrightarrow>
              Tr' ! ctA (Suc c) = cbA (Suc c) \<and> Br' ! cbA c = c \<and> Pr' ! cbA c = 1"
        by (auto simp: selfloop_inv_def)
      have rows: "seg Tr' Br' Pr' ` {ctA j..<ctA (Suc j)} = rowset j" if j: "j < length D" for j
      proof (cases "is_target_mec j \<or> out_avoid j")
        case True
        have cl: "Tr' ! (ctA j + 1) = cbA j + 1"
          using sk[OF j True] True by (simp add: ctA_Suc cbA_Suc sink_contrib1)
        from sk[OF j True] have "Br' ! cbA j = j" "Pr' ! cbA j = 1" by auto
        then have "seg Tr' Br' Pr' ` {ctA j..<ctA (Suc j)} = {{#(j, 1)#}}"
          by (rule_tac seg_sink_block[OF op[OF j] cl]) (auto simp: True)
        then show ?thesis using True by (simp add: rowset_def)
      next
        case False
        then show ?thesis using ns[OF j] by (simp add: rowset_def)
      qed
      have last: "Tr' ! cnt_T = cnt_B"
      proof (cases "length D = 0")
        case True
        then have "cnt_T = 0" by (metis cnt_T_ctA ctA_0)
        moreover have "cnt_B = 0" using True by (metis cnt_B_cbA cbA_0)
        ultimately show ?thesis using Tr0 by simp
      next
        case False
        then have j: "length D - 1 < length D" by simp
        have "Tr' ! ctA (Suc (length D - 1)) = cbA (Suc (length D - 1))"
          using ns[OF j] sk[OF j] by (cases "is_target_mec (length D - 1) \<or> out_avoid (length D - 1)") auto
        then show ?thesis using False by (simp add: cnt_T_ctA cnt_B_cbA)
      qed
      show ?thesis using L mono Tr0 last rows INV by (simp add: selfloop_inv_def)
    qed

    lemma selfloop_inv_step:
      assumes cit: "c \<in> it" and itD: "it \<subseteq> {0..<length D}"
      assumes INV: "selfloop_inv it Tr' Br' Pr'"
      assumes sink: "is_target_mec c \<or> out_avoid c"
      shows "selfloop_inv (it - {c})
               (Tr'[ctA c := cbA c, ctA c + 1 := cbA c + 1]) (Br'[cbA c := c]) (Pr'[cbA c := 1])"
    proof -
      have cD: "c < length D" using cit itD by auto
      have sucT: "ctA (Suc c) = ctA c + 1" and sucB: "cbA (Suc c) = cbA c + 1"
        using sink by (simp_all add: ctA_Suc cbA_Suc sink_contrib1)
      from INV have L: "length Tr' = cnt_T + 1" and LB: "length Br' = cnt_B" and LP: "length Pr' = cnt_B"
        and Tr0: "Tr' ! 0 = 0" and mono: "\<And>s. s \<le> cnt_T \<Longrightarrow> Tr' ! s \<le> cnt_B"
        and op: "\<And>c'. c' < length D \<Longrightarrow> Tr' ! ctA c' = cbA c'"
        and ns: "\<And>c'. c' < length D \<Longrightarrow> \<not> (is_target_mec c' \<or> out_avoid c') \<Longrightarrow>
              Tr' ! ctA (Suc c') = cbA (Suc c') \<and>
              (\<forall>s. ctA c' \<le> s \<and> s \<le> ctA (Suc c') \<longrightarrow> cbA c' \<le> Tr' ! s \<and> Tr' ! s \<le> cbA (Suc c')) \<and>
              seg Tr' Br' Pr' ` {ctA c'..<ctA (Suc c')} = rmt ` ltfull c'"
        and sk: "\<And>c'. c' < length D \<Longrightarrow> is_target_mec c' \<or> out_avoid c' \<Longrightarrow> c' \<notin> it \<Longrightarrow>
              Tr' ! ctA (Suc c') = cbA (Suc c') \<and> Br' ! cbA c' = c' \<and> Pr' ! cbA c' = 1"
        by (auto simp: selfloop_inv_def)
      have sucD: "Suc c \<le> length D" using cD by simp
      have suc_le: "ctA (Suc c) \<le> cnt_T" using ctA_mono[OF sucD] by (simp add: cnt_T_ctA)
      have cbsuc_le: "cbA (Suc c) \<le> cnt_B" using cbA_mono[OF sucD] by (simp add: cnt_B_cbA)
      have ctc_lt: "ctA c + 1 < length Tr'" using suc_le sucT L by simp
      have cbc_lt: "cbA c < length Br'" using cbsuc_le sucB LB by simp
      define Trs where "Trs = Tr'[ctA c + 1 := cbA c + 1]"
      have Trs_eq: "Tr'[ctA c := cbA c, ctA c + 1 := cbA c + 1] = Trs"
        unfolding Trs_def using op[OF cD] by (metis list_update_id)
      have Trs_nth: "\<And>s. s \<noteq> ctA c + 1 \<Longrightarrow> Trs ! s = Tr' ! s"
        unfolding Trs_def by (simp add: nth_list_update)
      have Trs_at: "Trs ! (ctA c + 1) = cbA c + 1"
        unfolding Trs_def using ctc_lt by simp
      define Br2 where "Br2 = Br'[cbA c := c]"
      define Pr2 where "Pr2 = Pr'[cbA c := 1]"
      have Br2_nth: "\<And>x. x \<noteq> cbA c \<Longrightarrow> Br2 ! x = Br' ! x" unfolding Br2_def by (simp add: nth_list_update)
      have Pr2_nth: "\<And>x. x \<noteq> cbA c \<Longrightarrow> Pr2 ! x = Pr' ! x" unfolding Pr2_def by (simp add: nth_list_update)
      \<comment> \<open>Values at cells any block reads are unchanged, for c' \<noteq> c.\<close>
      have TE: "Trs ! s = Tr' ! s" if c': "c' < length D" "c' \<noteq> c" and sr: "ctA c' \<le> s \<and> s \<le> ctA (Suc c')" for c' s
      proof (cases "s = ctA c + 1")
        case False thus ?thesis by (simp add: Trs_nth)
      next
        case True
        have "ctA (Suc c) \<le> ctA (Suc c')" using sr sucT True by simp
        then have "Suc c \<le> Suc c'" by (simp add: ctA_le_iff)
        moreover have "ctA c' \<le> ctA (Suc c)" using sr sucT True by simp
        then have "c' \<le> Suc c" by (simp add: ctA_le_iff)
        ultimately have "c = c' - 1 \<and> 0 < c'" using c'(2) by auto
        then have "Suc c = c'" by simp
        then have "Trs ! s = cbA c'" using Trs_at True sucB sucT by simp
        also have "\<dots> = Tr' ! s" using op[OF c'(1)] True \<open>Suc c = c'\<close> sucT by simp
        finally show ?thesis .
      qed
      show ?thesis unfolding Trs_eq Br2_def[symmetric] Pr2_def[symmetric] selfloop_inv_def
      proof (intro conjI)
        show "length Trs = cnt_T + 1" unfolding Trs_def using L by simp
        show "length Br2 = cnt_B" unfolding Br2_def using LB by simp
        show "length Pr2 = cnt_B" unfolding Pr2_def using LP by simp
        show "Trs ! 0 = 0" using Tr0 by (simp add: Trs_nth)
        show "\<forall>s\<le>cnt_T. Trs ! s \<le> cnt_B"
        proof (intro allI impI)
          fix s assume s: "s \<le> cnt_T"
          show "Trs ! s \<le> cnt_B"
          proof (cases "s = ctA c + 1")
            case True thus ?thesis using Trs_at cbsuc_le sucB by simp
          next
            case False thus ?thesis using s mono by (simp add: Trs_nth)
          qed
        qed
        show "\<forall>c'<length D. Trs ! ctA c' = cbA c'"
        proof (intro allI impI)
          fix c' assume c': "c' < length D"
          show "Trs ! ctA c' = cbA c'"
          proof (cases "ctA c' = ctA c + 1")
            case True
            then have "ctA c' = ctA (Suc c)" using sucT by simp
            then have "c' = Suc c" by (simp add: ctA_eq_iff)
            then show ?thesis using Trs_at True sucB by simp
          next
            case False then show ?thesis using op[OF c'] by (simp add: Trs_nth)
          qed
        qed
        show "\<forall>c'<length D. \<not> (is_target_mec c' \<or> out_avoid c') \<longrightarrow>
                Trs ! ctA (Suc c') = cbA (Suc c') \<and>
                (\<forall>s. ctA c' \<le> s \<and> s \<le> ctA (Suc c') \<longrightarrow> cbA c' \<le> Trs ! s \<and> Trs ! s \<le> cbA (Suc c')) \<and>
                seg Trs Br2 Pr2 ` {ctA c'..<ctA (Suc c')} = rmt ` ltfull c'"
        proof (intro allI impI)
          fix c' assume c': "c' < length D" and nsc': "\<not> (is_target_mec c' \<or> out_avoid c')"
          have cc': "c' \<noteq> c" using nsc' sink by auto
          from ns[OF c' nsc'] have cl: "Tr' ! ctA (Suc c') = cbA (Suc c')"
            and bnd: "\<And>s. ctA c' \<le> s \<Longrightarrow> s \<le> ctA (Suc c') \<Longrightarrow> cbA c' \<le> Tr' ! s \<and> Tr' ! s \<le> cbA (Suc c')"
            and segc': "seg Tr' Br' Pr' ` {ctA c'..<ctA (Suc c')} = rmt ` ltfull c'" by auto
          have TEc: "\<And>s. ctA c' \<le> s \<Longrightarrow> s \<le> ctA (Suc c') \<Longrightarrow> Trs ! s = Tr' ! s"
            using TE[OF c' cc'] by blast
          have le1: "ctA c' \<le> ctA (Suc c')" by (simp add: ctA_le_iff)
          have "Trs ! ctA (Suc c') = cbA (Suc c')" using TEc[of "ctA (Suc c')"] le1 cl by simp
          moreover have "\<forall>s. ctA c' \<le> s \<and> s \<le> ctA (Suc c') \<longrightarrow> cbA c' \<le> Trs ! s \<and> Trs ! s \<le> cbA (Suc c')"
            using TEc bnd by auto
          moreover have "seg Trs Br2 Pr2 ` {ctA c'..<ctA (Suc c')} = rmt ` ltfull c'"
          proof -
            have "seg Trs Br2 Pr2 s = seg Tr' Br' Pr' s" if s: "s \<in> {ctA c'..<ctA (Suc c')}" for s
            proof (rule seg_eq_on)
              show "Trs ! s = Tr' ! s" using TEc s by simp
              show "Trs ! Suc s = Tr' ! Suc s" using TEc s by simp
              fix x assume x: "x \<in> {Tr' ! s..<Tr' ! Suc s}"
              have "cbA c' \<le> Tr' ! s" using bnd[of s] s by simp
              moreover have "Tr' ! Suc s \<le> cbA (Suc c')" using bnd[of "Suc s"] s by simp
              ultimately have "x \<in> {cbA c'..<cbA (Suc c')}" using x by simp
              then have "x \<noteq> cbA c" using cc' by (auto simp: cbA_le_iff cbA_less_iff)
              then show "Br2 ! x = Br' ! x \<and> Pr2 ! x = Pr' ! x" by (simp add: Br2_nth Pr2_nth)
            qed
            then have "seg Trs Br2 Pr2 ` {ctA c'..<ctA (Suc c')}
                = seg Tr' Br' Pr' ` {ctA c'..<ctA (Suc c')}" by (rule image_cong[OF refl])
            then show ?thesis using segc' by simp
          qed
          ultimately show "Trs ! ctA (Suc c') = cbA (Suc c') \<and>
                (\<forall>s. ctA c' \<le> s \<and> s \<le> ctA (Suc c') \<longrightarrow> cbA c' \<le> Trs ! s \<and> Trs ! s \<le> cbA (Suc c')) \<and>
                seg Trs Br2 Pr2 ` {ctA c'..<ctA (Suc c')} = rmt ` ltfull c'" by blast
        qed
        show "\<forall>c'<length D. (is_target_mec c' \<or> out_avoid c') \<and> c' \<notin> it - {c} \<longrightarrow>
                Trs ! ctA (Suc c') = cbA (Suc c') \<and> Br2 ! cbA c' = c' \<and> Pr2 ! cbA c' = 1"
        proof (intro allI impI)
          fix c' assume c': "c' < length D" and P: "(is_target_mec c' \<or> out_avoid c') \<and> c' \<notin> it - {c}"
          show "Trs ! ctA (Suc c') = cbA (Suc c') \<and> Br2 ! cbA c' = c' \<and> Pr2 ! cbA c' = 1"
          proof (cases "c' = c")
            case True
            have "Trs ! ctA (Suc c) = cbA (Suc c)" using Trs_at sucT sucB by simp
            moreover have "Br2 ! cbA c = c" unfolding Br2_def using cbc_lt by simp
            moreover have "Pr2 ! cbA c = 1" unfolding Pr2_def using cbc_lt LP LB by simp
            ultimately show ?thesis using True by simp
          next
            case False
            then have "c' \<notin> it" using P by simp
            from sk[OF c' _ this] P have cl: "Tr' ! ctA (Suc c') = cbA (Suc c')"
              and br: "Br' ! cbA c' = c'" and pr: "Pr' ! cbA c' = 1" by auto
            have "ctA (Suc c') \<noteq> ctA c + 1" using False sucT ctA_eq_iff by (metis Suc_inject)
            then have "Trs ! ctA (Suc c') = cbA (Suc c')" using cl by (simp add: Trs_nth)
            moreover have "cbA c' \<noteq> cbA c" using False by (simp add: cbA_eq_iff)
            then have "Br2 ! cbA c' = c'" "Pr2 ! cbA c' = 1" using br pr by (simp_all add: Br2_nth Pr2_nth)
            ultimately show ?thesis by simp
          qed
        qed
      qed
    qed

    lemma selfloop_pass_correct:
      assumes cp: "copy_post Tr' Br' Pr'"
      assumes StA: "\<forall>c\<le>length D. St' ! c = ctA c"
      assumes bA: "\<forall>c\<le>length D. boff ! c = cbA c"
      assumes Ta': "Ta' = {c. c < length D \<and> is_target_mec c}"
      assumes Av': "Av' = {c. c < length D \<and> out_avoid c}"
      shows "selfloop_pass Tr' Br' Pr' St' boff Ta' Av'
         \<le> SPEC (\<lambda>(Tr', Br', Pr').
             length Tr' = cnt_T + 1 \<and> length Br' = cnt_B \<and> length Pr' = cnt_B \<and>
             Tr' ! 0 = 0 \<and> Tr' ! cnt_T = cnt_B \<and> (\<forall>s\<le>cnt_T. Tr' ! s \<le> cnt_B) \<and>
             (\<forall>j<length D. seg Tr' Br' Pr' ` {ctA j..<ctA (Suc j)} = rowset j))"
      unfolding selfloop_pass_def
      apply (refine_vcg FOREACH_rule[where I="\<lambda>it (Tr', Br', Pr'). selfloop_inv it Tr' Br' Pr'"])
      subgoal by simp
      subgoal using selfloop_inv_start[OF cp] by simp
      subgoal premises p for x it \<sigma> a b aa ba x1 x2 x1a x2a
      proof -
        have xD: "x < length D" using p by auto
        have "St' ! x = ctA x" "boff ! x = cbA x" using StA bA xD by auto
        moreover have "is_target_mec x \<or> out_avoid x" using p Ta' Av' xD by auto
        ultimately show ?thesis using selfloop_inv_step[of x it a aa ba] p by auto
      qed
      subgoal premises p for x it \<sigma> a b aa ba x1 x2 x1a x2a
      proof -
        have xD: "x < length D" using p by auto
        have "\<not> (is_target_mec x \<or> out_avoid x)" using p Ta' Av' xD by auto
        then show ?thesis using p by (auto simp: selfloop_inv_def)
      qed
      subgoal by (auto dest!: selfloop_inv_final)
      subgoal by (auto dest!: selfloop_inv_final)
      subgoal by (auto dest!: selfloop_inv_final)
      subgoal by (auto dest!: selfloop_inv_final)
      subgoal by (auto dest!: selfloop_inv_final)
      subgoal by (auto dest!: selfloop_inv_final)
      subgoal by (auto dest!: selfloop_inv_final)
      done

    subsection \<open>The sequenced builder\<close>

    definition "build_statespace' = do {
      (cntT, cntB, Ta', avm) \<leftarrow> count_pass;
      Av' \<leftarrow> empty_ec_pass cntT Ta' avm;
      (St', boff, nT, nB) \<leftarrow> offset_pass cntT cntB Ta' Av';
      (Tr', Br', Pr', curT, curB) \<leftarrow> copy_pass St' boff Ta' Av' nT nB;
      (Tr', Br', Pr') \<leftarrow> selfloop_pass Tr' Br' Pr' St' boff Ta' Av';
      ASSERT (nT < length Tr');
      RETURN (St', Tr'[nT := nB], Br', Pr', Av', Ta') }"

    subsection \<open>Correctness (definitions first: the postcondition is deferred)\<close>

    text \<open>The builder's own proof obligation: the five passes together establish
      \<^const>\<open>built_post\<close>. Everything else (O1 validity, O2 semantics) follows from that alone,
      by the step-7 chain above.\<close>
    lemma build_statespace'_post:
      "build_statespace' \<le> SPEC (\<lambda>(St', Tr', Br', Pr', Av', Ta'). built_post St' Tr' Br' Pr' Av' Ta')"
      unfolding build_statespace'_def
      apply (refine_vcg count_pass_correct[THEN order_trans]
         empty_ec_pass_correct[THEN order_trans]
         offset_pass_correct[THEN order_trans]
         copy_pass_correct[THEN order_trans]
         selfloop_pass_correct[THEN order_trans])
      apply (simp_all add: built_post_def)
      subgoal premises prems for x a b aa ba ab xa xb ac bc ad bd xc af bf ag bg ah bh ai bi xd aj
      proof -
        from prems have "aj[cnt_T := cnt_B] = aj" by (metis list_update_id)
        with prems show ?thesis by simp
      qed
      done

    text \<open>Internal stepping stone used to discharge the
      step-7 refinement \<open>build_statespace'_correct\<close> below: with @{const built_post}
      established, the built data is a well-formed Sup interval-iteration state space
      (@{thm [source] build_valid}) whose abstract semantics is the indexed max reduction
      (@{thm [source] build_semantics}). The concrete argument \<^term>\<open>M_mec \<M>_\<alpha>\<close> occurs only here,
      inside the locale; at the interface it is abstracted away by @{const modest_collapse_rel}.\<close>
    lemma build_statespace'_spec:
      "build_statespace' \<le> SPEC (\<lambda>(St', Tr', Br', Pr', Av', Ta').
          modest_mdp_ii_invar_sup (length D) St' Tr' Br' Pr' Av' Ta'
          \<and> length Tr' \<le> length Tr \<and> length Br' \<le> length Br
          \<and> modest_mdp_input_def.\<M>_\<alpha> (length D) St' Tr' Br' Av' Ta' Pr' = to_index (M_mec \<M>_\<alpha>) D)"
      apply (rule order_trans[OF build_statespace'_post])
      apply (rule SPEC_rule)
      apply clarify
      apply (intro conjI)
      subgoal by (rule build_valid)
      subgoal using Suc_cnt_T_le_length_Tr by (simp add: built_post_def)
      subgoal using cnt_B_le_length_Br by (simp add: built_post_def)
      subgoal by (rule build_semantics)
      done

  end

  text \<open>Step-7 packaging for the builder: bundle the
    preserved input MDP, the freshly built state space, and the decomposition, and show the result
    refines @{const op_to_index} over @{const modest_collapse_rel}. The abstract MDP argument is
    supplied by the relation -- no \<^const>\<open>M_mec\<close> (collapse) in the interface; the \<^const>\<open>to_index\<close>
    semantics enters only internally, via @{thm [source] modest_collapse_invar.build_statespace'_spec}.\<close>
  definition op_build_statespace' ::
    "nat \<Rightarrow> (modest_input_mdp \<times> nat set list)
         \<Rightarrow> ((modest_input_mdp \<times> modest_input_mdp) \<times> nat set list) nres" where
    "op_build_statespace' N = (\<lambda>((St,Tr,Br,Pr,Av,Ta), D). do {
        out \<leftarrow> modest_collapse_invar.build_statespace' N St Tr Br Pr Av Ta D;
        RETURN (((St,Tr,Br,Pr,Av,Ta), out), D) })"

  lemma build_statespace'_refine:
    assumes REL: "(((St,Tr,Br,Pr,Av,Ta), D), (\<M>c, D2)) \<in> modest_collapse_rel N"
    shows "op_build_statespace' N ((St,Tr,Br,Pr,Av,Ta), D)
             \<le> \<Down>(modest_build_rel N) (RETURN (op_to_index (\<M>c, D2)))"
  proof -
    interpret L: modest_collapse_invar N St Tr Br Pr Av Ta D
      using REL by (simp add: modest_collapse_rel_iff)
    have MC: "\<M>c = M_mec (modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr)" and DD: "D2 = D"
      using REL by (simp_all add: modest_collapse_rel_iff)
    show ?thesis
      unfolding op_build_statespace'_def prod.case op_to_index_def MC DD
      apply (refine_vcg L.build_statespace'_spec[THEN order_trans])
      apply (clarsimp simp: modest_build_rel_def in_br_conv)
      by (simp add: modest_build_invar_def modest_build_invar_axioms_def
                    L.modest_collapse_invar_axioms)
  qed

  lemma build_statespace'_correct:
    "(op_build_statespace' N, RETURN o op_to_index) \<in> modest_collapse_rel N \<rightarrow> \<langle>modest_build_rel N\<rangle>nres_rel"
  proof (intro fun_relI)
    fix c a assume "(c, a) \<in> modest_collapse_rel N"
    then obtain St Tr Br Pr Av Ta D \<M>c D2 where
      c: "c = ((St,Tr,Br,Pr,Av,Ta), D)" and a: "a = (\<M>c, D2)"
      and REL: "(((St,Tr,Br,Pr,Av,Ta), D), (\<M>c, D2)) \<in> modest_collapse_rel N"
      by (auto simp: modest_collapse_rel_def in_br_conv)
    show "(op_build_statespace' N c, (RETURN o op_to_index) a) \<in> \<langle>modest_build_rel N\<rangle>nres_rel"
      unfolding c a o_apply by (rule nres_relI[OF build_statespace'_refine[OF REL]])
  qed
end