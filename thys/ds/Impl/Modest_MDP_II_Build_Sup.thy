theory Modest_MDP_II_Build_Sup
  imports "Modest_MDP_II_Maxred_Build_Impl" "../../fpii/Interval_Iteration_Max_Code"
    "Modest_MDP_II_Minred_Impl"
begin

no_notation Finite_Cartesian_Product.matrix_matrix_mult (infixl "**" 70)

text \<open>Bridging the \<^emph>\<open>built\<close> state space to a \<open>Sup\<close> interval-iteration input.

  The collapse builder allocates its own arrays, so it delivers \<^const>\<open>built_mdp_assn\<close> ---
  \<^const>\<open>IICF_Array.array_assn\<close> plus owned bitsets. Interval iteration consumes
  \<^const>\<open>Modest_mdp_sup_assn\<close>, whose raw part \<^const>\<open>modest_init_mdp_env_defs.Modest_mdp_assn_aux\<close>
  is built from caller-owned \<^emph>\<open>slices\<close>. This theory closes that gap.

  The conversion is not a coercion but an \<^emph>\<open>equality\<close>: a full array is a slice of itself together
  with its malloc tag. That is @{thm [source] array_assn_split} at the raw level, and it lifts to the
  IICF level for free because \<^const>\<open>IICF_Array.array_assn\<close> and
  \<^const>\<open>IICF_Array.array_slice_assn\<close> are the same \<^const>\<open>hr_comp\<close> over
  \<open>\<langle>the_pure A\<rangle>list_rel\<close> (which preserves length) of the two raw assertions.

  Kept in its own theory: the builder's \<open>Impl\<close> costs a ~15 min reprocess per edit, whereas this
  one re-checks in seconds.\<close>


section \<open>Array \<open>\<leftrightarrow>\<close> slice at the IICF level\<close>

text \<open>The IICF-level counterpart of @{thm [source] array_assn_split}. The malloc tag
  \<^term>\<open>\<upharpoonleft>array_base_assn (length xs) p\<close> is not pure, so it cannot be dropped --- but it never has to
  be threaded by hand either: across a \<^emph>\<open>kept\<close> inner call it simply stays in the \<open>vcg\<close> frame. This
  is the same shape as \<open>wo_array_sort_adapt\<close> in Isabelle_LLVM's sorting examples.\<close>
lemma iicf_array_assn_split:
  "IICF_Array.array_assn A xs p
     = (IICF_Array.array_slice_assn A xs p ** \<upharpoonleft>array_base_assn (length xs) p)"
  unfolding IICF_Array.array_assn_def IICF_Array.array_slice_assn_def hr_comp_def
  by (auto simp: array_assn_split sep_algebra_simps fun_eq_iff list_rel_imp_same_length)

text \<open>The owned bitset is an \<^const>\<open>IICF_Array.array_assn\<close> under one further \<^const>\<open>hr_comp\<close>
  (\<^const>\<open>bitset_rel\<close>), so it splits the same way --- which is what relates it to the input MDP's
  slice-backed \<^const>\<open>bitset_assn\<close>.\<close>
lemma bitset_own_assn_split:
  "bitset_own_assn n s q
     = (EXS bs. \<up>((bs, s) \<in> bitset_rel n)
                ** IICF_Array.array_slice_assn (id_assn::size_t \<Rightarrow> _) bs q
                ** \<upharpoonleft>array_base_assn (length bs) q)"
  unfolding bitset_own_assn_def bitset_own_assn_raw_def hr_comp_def
  by (auto simp: iicf_array_assn_split sep_algebra_simps fun_eq_iff pred_lift_extract_simps)


section \<open>DS-pinned \<open>Sup\<close> assertion\<close>

text \<open>Recovering the concrete tuple \<^emph>\<open>after\<close> an inner call needs the \<^const>\<open>hr_comp\<close> witness to be
  determined, so --- exactly as on the min side (\<^const>\<open>modest_mdp_inf_DS_rel\<close> /
  \<^const>\<open>Modest_mdp_inf_DS_assn\<close>) --- syntheses are stated at a \<open>DS\<close>-pinned assertion and un-pinned
  afterwards by hand. These live here rather than next to
  \<^const>\<open>modest_mdp_sup_rel\<close>/\<^const>\<open>Modest_mdp_sup_assn\<close> only to keep the edit out of the bottom of
  the import chain; nothing about them is builder-specific.\<close>

abbreviation "\<M>_sup_inv_DS N DS \<equiv>
  (\<lambda>(St,Tr,Br,Pr,Av,Ta). modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta \<and> DS = (St,Tr,Br,Pr,Av,Ta))"

definition modest_mdp_sup_DS_rel :: "nat \<Rightarrow> modest_mdp \<Rightarrow> (modest_mdp \<times> (nat mdptc)) set" where
  "modest_mdp_sup_DS_rel N DS = br (\<M>_\<alpha>_sup' N) (\<M>_sup_inv_DS N DS)"

definition "Modest_mdp_sup_DS_assn N DS =
  hr_comp (modest_init_mdp_env_defs.Modest_mdp_assn_aux N) (modest_mdp_sup_DS_rel N DS)"

lemma Modest_mdp_sup_assn_DS:
  "Modest_mdp_sup_assn N M Ei = (EXS DS. Modest_mdp_sup_DS_assn N DS M Ei)"
  unfolding Modest_mdp_sup_assn_def Modest_mdp_sup_DS_assn_def
    modest_mdp_sup_DS_rel_def modest_mdp_sup_rel_def
  apply (cases M)
  by (auto simp: in_br_conv fun_eq_iff hr_comp_def sep_algebra_simps)


section \<open>Per-component array \<open>\<longrightarrow>\<close> slice entailments\<close>

text \<open>The three shapes \<^const>\<open>modest_init_mdp_env_defs.Modest_mdp_assn_aux\<close> is built from. Each is
  @{thm [source] iicf_array_assn_split} plus the \<^const>\<open>b_assn\<close> side condition, which is pure and so
  simply gets discharged from the hypothesis.\<close>

lemma array_to_slice_ent:
  "IICF_Array.array_assn A xs p
     \<turnstile> IICF_Array.array_slice_assn A xs p ** \<upharpoonleft>array_base_assn (length xs) p"
  by (simp add: iicf_array_assn_split)

lemma array_to_small_slice_ent:
  assumes "length xs < max_size_t"
  shows "IICF_Array.array_assn A xs p
           \<turnstile> small_array_slice_assn A xs p ** \<upharpoonleft>array_base_assn (length xs) p"
  using assms by (simp add: iicf_array_assn_split sep_algebra_simps)

lemma array_to_node_slice_ent:
  assumes "length xs = N'"
  shows "IICF_Array.array_assn A xs p
           \<turnstile> node_array_slice_assn N' A xs p ** \<upharpoonleft>array_base_assn (length xs) p"
  using assms by (simp add: iicf_array_assn_split sep_algebra_simps)

text \<open>The branch array additionally narrows its \<^emph>\<open>element\<close> assertion, from \<^const>\<open>size_assn\<close> to the
  bounded \<^term>\<open>node_assn' M\<close>: the built branch targets are MEC indices, hence \<open>< M\<close>. Both are the
  same \<^const>\<open>hr_comp\<close> over a \<open>list_rel\<close>, so this is elementwise.\<close>

lemma the_pure_node_assn: "the_pure (node_assn' M) = b_rel (snat_rel' TYPE(node_T)) (\<lambda>x. x < M)"
  by (simp add: b_assn_pure_conv)

lemma array_slice_to_node_elem:
  assumes "\<forall>x\<in>set xs. x < M"
  shows "IICF_Array.array_slice_assn size_assn xs p
           \<turnstile> IICF_Array.array_slice_assn (node_assn' M) xs p"
  unfolding IICF_Array.array_slice_assn_def hr_comp_def the_pure_node_assn
  using assms
  by (auto simp: sep_algebra_simps list_rel_def list_all2_conv_all_nth entails_def)

text \<open>The bitsets differ only in the same array-vs-slice way, under a common
  \<^const>\<open>hr_comp\<close> with \<^const>\<open>bitset_rel\<close>. \<^const>\<open>bitset_invar\<close> only \<^emph>\<open>lower\<close>-bounds the raw word
  list (\<open>n \<le> LENGTH(size_T) * length bs\<close>), so the malloc tag's size stays existentially bound ---
  which is harmless, since the tag is only parked and handed back.\<close>
lemma bitset_own_to_bitset_ent:
  "bitset_own_assn M s q \<turnstile> bitset_assn M s q ** (EXS n. \<upharpoonleft>array_base_assn n q)"
  unfolding bitset_own_assn_def bitset_own_assn_raw_def bitset_assn_def bitset_assn_raw_def
    hr_comp_def
  by (auto simp: iicf_array_assn_split sep_algebra_simps entails_def pred_lift_extract_simps)


section \<open>The built state space as a \<open>Sup\<close> interval-iteration input\<close>

text \<open>The composite entailment: the builder's owned-array assertion implies the input MDP's
  slice-based one, plus the six malloc tags. The tags are \<^emph>\<open>interleaved\<close> with the components rather
  than bundled at the end, so the proof is a straight \<open>conj_entails_mono\<close> chain with no
  reassociation; separation conjunction is commutative, so the grouping is immaterial to callers.

  The two machine-word bounds are hypotheses, discharged at the use site from the \<^emph>\<open>input\<close> MDP's own
  assertion (\<open>interval_iteration_env.Modest_mdp_assn_boundsD\<close>) chained through
  @{thm [source] modest_build_invar.Tr'_cap} / @{thm [source] modest_build_invar.Br'_cap}. That is
  the sanctioned way to obtain a \<open>max_size_t\<close> fact --- it is read off an assertion, never assumed in
  an invariant.\<close>
lemma built_to_aux_ent:
  assumes INV: "modest_mdp_input_invar M St' Tr' Br' Pr' Av' Ta'"
  assumes TrM: "length Tr' < max_size_t" and BrM: "length Br' < max_size_t"
  shows "built_mdp_assn M (St',Tr',Br',Pr',Av',Ta') (Sti,Tri,Bri,Pri,Avi,Tai)
    \<turnstile> (node_array_slice_assn (Suc M) size_assn St' Sti ** \<upharpoonleft>array_base_assn (length St') Sti)
    ** (small_array_slice_assn size_assn Tr' Tri ** \<upharpoonleft>array_base_assn (length Tr') Tri)
    ** (small_array_slice_assn (node_assn' M) Br' Bri ** \<upharpoonleft>array_base_assn (length Br') Bri)
    ** (small_array_slice_assn pfin_real_intv_assn Pr' Pri ** \<upharpoonleft>array_base_assn (length Pr') Pri)
    ** (bitset_assn M Av' Avi ** (EXS n. \<upharpoonleft>array_base_assn n Avi))
    ** (bitset_assn M Ta' Tai ** (EXS n. \<upharpoonleft>array_base_assn n Tai))"
proof -
  interpret I: modest_mdp_input_invar M St' Tr' Br' Pr' Av' Ta' by (rule INV)
  have LSt: "length St' = Suc M" using I.N_DEF I.N0 by simp
  have LPr: "length Pr' < max_size_t" using BrM by (simp add: I.Len_Pr_Br)
  have BrN: "\<forall>x\<in>set Br'. x < M" using I.Br_dom by auto
  show ?thesis
    unfolding built_mdp_assn_def prod_assn_def
    apply (simp only: prod.case)
    apply (intro conj_entails_mono)
    subgoal by (rule array_to_node_slice_ent[OF LSt])
    subgoal by (rule array_to_small_slice_ent[OF TrM])
    subgoal
      apply (rule entails_trans[OF array_to_small_slice_ent[OF BrM]])
      apply (rule conj_entails_mono[OF _ entails_refl])
      apply (simp only: b_assn_simp)
      apply (rule conj_entails_mono[OF entails_refl])
      by (rule array_slice_to_node_elem[OF BrN])
    subgoal by (rule array_to_small_slice_ent[OF LPr])
    subgoal by (rule bitset_own_to_bitset_ent)
    subgoal by (rule bitset_own_to_bitset_ent)
    done
qed

text \<open>The six malloc tags the builder still owns after its arrays have been viewed as slices. They
  are what makes the built state space \<^emph>\<open>freeable\<close>, so they must be carried, not dropped; across a
  \<^emph>\<open>kept\<close> inner call they are inert and simply travel in the frame.\<close>
definition built_tags :: "modest_input_mdp \<Rightarrow> modest_input_mdpi \<Rightarrow> assn" where
  "built_tags \<equiv> (\<lambda>(St',Tr',Br',Pr',Av',Ta') (Sti,Tri,Bri,Pri,Avi,Tai).
       \<upharpoonleft>array_base_assn (length St') Sti
    ** \<upharpoonleft>array_base_assn (length Tr') Tri
    ** \<upharpoonleft>array_base_assn (length Br') Bri
    ** \<upharpoonleft>array_base_assn (length Pr') Pri
    ** (EXS n. \<upharpoonleft>array_base_assn n Avi)
    ** (EXS n. \<upharpoonleft>array_base_assn n Tai))"

text \<open>The same statement with the six components grouped into
  \<^const>\<open>modest_init_mdp_env_defs.Modest_mdp_assn_aux\<close> and the six tags grouped into
  \<^const>\<open>built_tags\<close>. This is a pure permutation of a twelve-fold separation conjunction, so it is
  closed by \<open>**\<close>'s associativity/commutativity.\<close>
lemma built_to_aux_grouped:
  assumes INV: "modest_mdp_input_invar M St' Tr' Br' Pr' Av' Ta'"
  assumes TrM: "length Tr' < max_size_t" and BrM: "length Br' < max_size_t"
  shows "built_mdp_assn M (St',Tr',Br',Pr',Av',Ta') (Sti,Tri,Bri,Pri,Avi,Tai)
    \<turnstile> modest_init_mdp_env_defs.Modest_mdp_assn_aux M
         (St',Tr',Br',Pr',Av',Ta') (Sti,Tri,Bri,Pri,Avi,Tai)
      ** built_tags (St',Tr',Br',Pr',Av',Ta') (Sti,Tri,Bri,Pri,Avi,Tai)"
  apply (rule entails_trans[OF built_to_aux_ent[OF INV TrM BrM]])
  unfolding modest_init_mdp_env_defs.Modest_mdp_assn_aux_def built_tags_def prod_assn_def
  apply (simp only: prod.case)
  by (simp add: sep_conj_ac)

text \<open>Introducing the \<^const>\<open>hr_comp\<close>: the built tuple is its own witness, and the relation's
  invariant is exactly \<^const>\<open>modest_mdp_ii_invar_sup\<close> at \<^term>\<open>M\<close> --- which is what
  \<^locale>\<open>modest_build_invar\<close> carries for the built space. No singleton domain is needed in this
  direction.\<close>
lemma aux_to_sup_ent:
  assumes INV: "modest_mdp_ii_invar_sup M St' Tr' Br' Pr' Av' Ta'"
  shows "modest_init_mdp_env_defs.Modest_mdp_assn_aux M (St',Tr',Br',Pr',Av',Ta') q
           \<turnstile> Modest_mdp_sup_assn M (\<M>_\<alpha>_sup' M (St',Tr',Br',Pr',Av',Ta')) q"
  unfolding Modest_mdp_sup_assn_def modest_mdp_sup_rel_def hr_comp_def
  apply (clarsimp simp: in_br_conv sep_algebra_simps entails_def)
  apply (rule exI[of _ St'], rule exI[of _ Tr'], rule exI[of _ Br'],
         rule exI[of _ Pr'], rule exI[of _ Av'], rule exI[of _ Ta'])
  using INV by simp

text \<open>The \<^emph>\<open>pinned\<close> \<^const>\<open>hr_comp\<close> introduction. Identical to the un-pinned one except that the
  relation additionally records \<open>DS = B\<close> --- which the witness satisfies by construction, since the
  witness \<^emph>\<open>is\<close> \<open>B\<close>. This is the form the bridge needs, because only here is the tuple determined
  on the way back out.\<close>
lemma aux_to_sup_DS_ent:
  assumes INV: "modest_mdp_ii_invar_sup M St' Tr' Br' Pr' Av' Ta'"
  shows "modest_init_mdp_env_defs.Modest_mdp_assn_aux M (St',Tr',Br',Pr',Av',Ta') q
           \<turnstile> Modest_mdp_sup_DS_assn M (St',Tr',Br',Pr',Av',Ta')
                (\<M>_\<alpha>_sup' M (St',Tr',Br',Pr',Av',Ta')) q"
  unfolding Modest_mdp_sup_DS_assn_def modest_mdp_sup_DS_rel_def hr_comp_def
  using INV by (auto simp: in_br_conv sep_algebra_simps entails_def)

text \<open>The forward direction, end to end: the builder's output assertion implies a \<open>Sup\<close>
  interval-iteration input at the \<^emph>\<open>same\<close> abstract MDP, with the malloc tags parked alongside.

  The two \<open>max_size_t\<close> hypotheses are about the \<^emph>\<open>input\<close> arrays, so at the use site they come from
  the input MDP's own assertion (\<open>Modest_mdp_assn_boundsD\<close>) --- which lives in the same
  \<open>modest_build_rel\<close> tuple --- and Phase-0's relative caps carry them over to the built arrays. This
  is the whole reason the caps had to exist.\<close>
lemma built_to_sup_ent:
  assumes INV: "modest_build_invar N St Tr Br Pr Av Ta D St' Tr' Br' Pr' Av' Ta'"
  assumes MD: "M = length D"
  assumes TrM: "length Tr < max_size_t" and BrM: "length Br < max_size_t"
  shows "built_mdp_assn M (St',Tr',Br',Pr',Av',Ta') q
           \<turnstile> Modest_mdp_sup_assn M (\<M>_\<alpha>_sup' M (St',Tr',Br',Pr',Av',Ta')) q
             ** built_tags (St',Tr',Br',Pr',Av',Ta') q"
proof -
  interpret B: modest_build_invar N St Tr Br Pr Av Ta D St' Tr' Br' Pr' Av' Ta' by (rule INV)
  have IIS: "modest_mdp_ii_invar_sup M St' Tr' Br' Pr' Av' Ta'"
    using INV MD by (simp add: modest_build_invar_def)
  have IN: "modest_mdp_input_invar M St' Tr' Br' Pr' Av' Ta'"
    using IIS by (simp add: modest_mdp_ii_invar_sup_def)
  have TrM': "length Tr' < max_size_t" using B.Tr'_cap TrM by simp
  have BrM': "length Br' < max_size_t" using B.Br'_cap BrM by simp
  obtain Sti Tri Bri Pri Avi Tai where Q: "q = (Sti,Tri,Bri,Pri,Avi,Tai)" by (cases q)
  show ?thesis
    unfolding Q
    apply (rule entails_trans[OF built_to_aux_grouped[OF IN TrM' BrM']])
    apply (rule conj_entails_mono[OF _ entails_refl])
    by (rule aux_to_sup_ent[OF IIS])
qed


section \<open>Reading the input MDP's machine-word bounds off its assertion\<close>

text \<open>The \<open>max_size_t\<close> facts \<open>built_to_sup_ent\<close> needs are about the \<^emph>\<open>input\<close> arrays, and the input
  MDP sits inside \<^const>\<open>Modest_build_assn\<close> at \<^const>\<open>modest_init_mdp_env_defs.Modest_mdp_assn_aux\<close>,
  whose \<^const>\<open>small_array_slice_assn\<close> components carry exactly those bounds as \<^const>\<open>b_assn\<close> side
  conditions. This is the standalone (locale-free) counterpart of
  \<open>interval_iteration_env.Modest_mdp_assn_boundsD\<close>.\<close>
lemma Modest_mdp_assn_aux_boundsD:
  assumes "rdomp (modest_init_mdp_env_defs.Modest_mdp_assn_aux N') (St,Tr,Br,Pr,Av,Ta)"
  shows "length Tr < max_size_t" and "length Br < max_size_t"
  using assms unfolding modest_init_mdp_env_defs.Modest_mdp_assn_aux_def by auto


section \<open>Recovering the pinned representation\<close>

text \<open>The obstacle to a round trip is that \<^const>\<open>Modest_mdp_sup_assn\<close> binds the concrete tuple
  existentially: going \<^emph>\<open>in\<close> is fine, but coming back out one only learns that \<^emph>\<open>some\<close> valid tuple
  sits at the pointer, so anything parked outside that names it (a malloc tag mentioning
  \<open>length St'\<close>) can no longer be re-paired.

  @{thm [source] hr_comp_entails_unique_dom} is the standard remedy, and its own comment in
  \<open>Modest_MDP_MEC\<close> describes exactly this situation. It recovers the pinned representation from the
  un-pinned one, not from any invariant but from \<^emph>\<open>precision\<close>: the memory determines the tuple. It
  needs two things --- \<open>pure_part\<close> of the pinned assertion (available from the block's precondition
  via \<open>htriple_pure_preI\<close>), and a singleton domain for the pinned relation, which is this lemma.

  Because the recovery happens inside the block, the block's \<open>Pair\<close>/\<open>FR2\<close> premises can be stated at
  the \<^emph>\<open>un-pinned\<close> \<^const>\<open>Modest_mdp_sup_assn\<close> --- so the existing interval-iteration rule applies
  verbatim and its interface is untouched. (The MEC precedent
  \<open>hn_collapse_to_mec_block\<close> pins both sides instead, which is why its inner rule had to be restated
  at \<open>Modest_MDP_DS_assn\<close>; we do not need to copy that.)\<close>

lemma Domain_modest_mdp_sup_DS_rel: "Domain (modest_mdp_sup_DS_rel N DS) \<subseteq> {DS}"
  unfolding modest_mdp_sup_DS_rel_def by (auto simp: in_br_conv split: prod.splits)

lemma modest_mdp_sup_DS_rel_dom_eq:
  "\<lbrakk>a \<in> Domain (modest_mdp_sup_DS_rel N DS); b \<in> Domain (modest_mdp_sup_DS_rel N DS)\<rbrakk> \<Longrightarrow> a = b"
  using Domain_modest_mdp_sup_DS_rel by blast


section \<open>The builder's output, viewed as a borrowed MDP with its tags parked\<close>

text \<open>This is the resolution of the ownership mismatch, and it is deliberately blunt. A malloc tag
  cannot be dropped --- Isabelle_LLVM's assertions are precise, so \<open>A ** B \<turnstile> A\<close> is false --- but it
  never has to be \<^emph>\<open>re-paired\<close> either, and re-pairing was the only real difficulty: coming back out
  of \<^const>\<open>bitset_assn\<close> one learns only that \<^emph>\<open>some\<close> word list sits at the pointer, so a tag naming
  \<open>length bs\<close> can no longer be matched up with it.

  So we stop trying. The built state space is exported as an ordinary \<^emph>\<open>borrowed\<close> MDP --- exactly the
  \<^const>\<open>modest_init_mdp_env_defs.Modest_mdp_assn_aux\<close> the interval iteration already consumes ---
  with the six malloc tags parked beside it in \<^const>\<open>built_tags\<close>, where the two bitset tags are
  existentially bound and therefore tied to nothing. Splitting and rejoining are then both
  \<^emph>\<open>definitional\<close>, and across a \<^emph>\<open>kept\<close> inner call \<^const>\<open>built_tags\<close> is never even opened: it
  travels in the frame verbatim.

  The conversion is one-way, as intended. Nothing downstream ever needs an owned bitset again, so
  nothing ever goes back.\<close>

definition built_mdp_assn' :: "nat \<Rightarrow> modest_input_mdp \<Rightarrow> modest_input_mdpi \<Rightarrow> assn" where
  "built_mdp_assn' M c ci =
     (modest_init_mdp_env_defs.Modest_mdp_assn_aux M c ci ** built_tags c ci)"

lemma built_to_built'_ent:
  assumes INV: "modest_mdp_input_invar M St' Tr' Br' Pr' Av' Ta'"
  assumes TrM: "length Tr' < max_size_t" and BrM: "length Br' < max_size_t"
  shows "built_mdp_assn M (St',Tr',Br',Pr',Av',Ta') q
           \<turnstile> built_mdp_assn' M (St',Tr',Br',Pr',Av',Ta') q"
proof -
  obtain Sti Tri Bri Pri Avi Tai where Q: "q = (Sti,Tri,Bri,Pri,Avi,Tai)" by (cases q)
  show ?thesis
    unfolding Q built_mdp_assn'_def
    by (rule built_to_aux_grouped[OF INV TrM BrM])
qed


subsection \<open>Two generic tools\<close>

text \<open>A pure fact that holds of every state of an assertion may simply be assumed while proving an
  entailment out of it. This is what lets a \<open>max_size_t\<close> bound be read off one component of a
  separating conjunction and used on another inside a plain entailment --- the same move \<open>sepref\<close>
  makes with \<open>rdomp\<close>, but available outside a synthesis proof.\<close>
lemma entails_pure_pre_extract:
  assumes EX: "\<And>s. A s \<Longrightarrow> P"
  assumes ENT: "P \<Longrightarrow> A \<turnstile> B"
  shows "A \<turnstile> B"
  using assms unfolding entails_def by blast

text \<open>\<^const>\<open>hr_comp\<close> is monotone in its assertion, and --- crucially --- the witness's membership in
  the relation is available while proving the inner entailment. That is where the built space's
  invariant comes from.\<close>
lemma hr_comp_ent_mono:
  assumes "\<And>c. (c,a) \<in> R \<Longrightarrow> A c ci \<turnstile> A' c ci"
  shows "hr_comp A R a ci \<turnstile> hr_comp A' R a ci"
  using assms by (auto simp: hr_comp_def entails_def sep_algebra_simps pred_lift_extract_simps)

text \<open>Weakening an \<^const>\<open>hfref\<close>'s \<^emph>\<open>result\<close> assertion. Note this cannot see the precondition ---
  the result is universally quantified --- which is the whole reason \<open>modest_build_M_rel\<close> exists.\<close>
lemma hfref_cons_res:
  assumes "(f,g) \<in> hfref P C RS T CP"
  assumes "\<And>a x y. T a x y \<turnstile> T' a x y"
  shows "(f,g) \<in> hfref P C RS T' CP"
  using assms unfolding hfref_def by (blast intro: hn_refine_cons_res)

text \<open>Strengthening an \<^const>\<open>nres_rel\<close> by a property of the \<^emph>\<open>concrete\<close> results only.\<close>
lemma nres_rel_restrict_conc:
  assumes A: "(m,n) \<in> \<langle>R\<rangle>nres_rel"
  assumes B: "\<And>r. nofail m \<Longrightarrow> inres m r \<Longrightarrow> \<Phi> r"
  shows "(m,n) \<in> \<langle>{(c,a). (c,a) \<in> R \<and> \<Phi> c}\<rangle>nres_rel"
  using assms by (auto simp: pw_nres_rel_iff pw_le_iff refine_pw_simps)

text \<open>Turning a \<^emph>\<open>locale parameter\<close> into an \<^emph>\<open>input parameter\<close>. If a rule holds for every value of
  a parameter whose refinement assertion is \<^emph>\<open>pure\<close>, then it lifts to a rule that takes that
  parameter as an ordinary kept argument. The result assertion may mention it, which is why the
  conclusion needs the dependent arrow \<open>\<rightarrow>\<^sub>d\<close> --- \<^const>\<open>hfref\<close>'s result slot is already a function
  of the abstract argument, so no new machinery is required.

  This is what lets a size that is only known at \<^emph>\<open>run time\<close> be fed to a synthesis whose assertions
  were set up against a fixed locale parameter.\<close>

lemma hfref_add_kept_pure_arg_aux:
  assumes RULE: "(f vi, g v) \<in> [P v]\<^sub>a RS \<rightarrow> T v"
  assumes PP: "P v x"
  shows "hn_refine (pure R v vi ** fst RS x xi) (f vi xi)
           (pure R v vi ** snd RS x xi) (T v) (\<lambda>_. True) (g v x)"
proof -
  note RR = RULE[THEN hfrefD, where c = xi and a = x, simplified, OF PP]
  show ?thesis
    apply (rule hn_refine_cons[OF _ hn_refine_frame'[where F = "pure R v vi", OF RR]])
    subgoal by (simp add: sep_algebra_simps sep_conj_ac)
    subgoal by (simp add: sep_algebra_simps sep_conj_ac)
    subgoal by simp
    done
qed

lemma hfref_add_kept_pure_arg:
  assumes RULE: "\<And>v vi. (vi,v) \<in> R \<Longrightarrow> Q v \<Longrightarrow> (f vi, g v) \<in> [P v]\<^sub>a RS \<rightarrow> T v"
  shows "(uncurry f, uncurry g)
           \<in> [\<lambda>(v,x). Q v \<and> P v x]\<^sub>a (pure R)\<^sup>k *\<^sub>a RS \<rightarrow>\<^sub>d (\<lambda>(v,_). T v)"
  apply (rule hfrefI)
  apply (clarsimp split: prod.splits)
  apply (rule hn_refine_preI)
  apply (rule hfref_add_kept_pure_arg_aux)
   apply (rule RULE)
     apply (auto simp: sep_conj_def pure_def pred_lift_extract_simps)
  done


subsection \<open>Pinning the decomposition's length into the builder's output relation\<close>

text \<open>\<^const>\<open>modest_build_rel\<close> sizes the built space by \<^term>\<open>length D\<close>, while \<^const>\<open>built_mdp_assn\<close>
  is stated at the code locale's \<^term>\<open>M\<close>. The builder's \<open>hnr\<close> ties the two by a \<^emph>\<open>precondition\<close>
  (\<open>M = length D\<close>), which is exactly the wrong place for the weakening below: a result assertion is
  universally quantified over the result, so a precondition on the argument cannot reach it.

  Recording \<open>M = length D\<close> in the relation instead fixes that, and costs nothing --- it is a
  statement about a list the builder receives and returns unchanged, not a machine-word bound.\<close>

definition modest_build_M_rel ::
  "nat \<Rightarrow> nat \<Rightarrow> (((modest_input_mdp \<times> modest_input_mdp) \<times> nat set list) \<times> nat mdptc) set" where
  "modest_build_M_rel N M = br build_\<alpha> (\<lambda>x. build_inv N x \<and> M = length (snd x))"

lemma modest_build_M_rel_alt:
  "modest_build_M_rel N M = {(c,a). (c,a) \<in> modest_build_rel N \<and> M = length (snd c)}"
  unfolding modest_build_M_rel_def modest_build_rel_def by (auto simp: in_br_conv)

lemma modest_build_M_rel_sub: "modest_build_M_rel N M \<subseteq> modest_build_rel N"
  by (auto simp: modest_build_M_rel_alt)

lemma modest_build_M_rel_sv[simp, intro!]: "single_valued (modest_build_M_rel N M)"
  unfolding modest_build_M_rel_def by (rule br_sv)

text \<open>The builder's output assertion at that relation --- what the re-run \<open>FCOMP\<close> produces --- and
  the borrowed view of it, which is what callers see.\<close>

definition "Modest_build_M_assn N M =
  hr_comp ((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn M)
           \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N)
          (modest_build_M_rel N M)"

definition "Modest_build_assn' N M =
  hr_comp ((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn' M)
           \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N)
          (modest_build_M_rel N M)"

text \<open>The \<open>max_size_t\<close> bounds for the \<^emph>\<open>input\<close> MDP, read off the very assertion the weakening starts
  from. This is the sanctioned source (see the hard rule in \<open>CLAUDE.md\<close>): a \<^const>\<open>b_assn\<close> side
  condition inside \<^const>\<open>modest_init_mdp_env_defs.Modest_mdp_assn_aux\<close>, never an assumption.\<close>
lemma build_prod_boundsD:
  assumes "(modest_init_mdp_env_defs.Modest_mdp_assn_aux N (St,Tr,Br,Pr,Av,Ta) ici ** X) s"
  shows "length Tr < max_size_t" and "length Br < max_size_t"
proof -
  have PP: "pure_part (modest_init_mdp_env_defs.Modest_mdp_assn_aux N (St,Tr,Br,Pr,Av,Ta) ici ** X)"
    unfolding pure_part_def using assms by blast
  from pure_part_split_conj[OF PP]
  have "pure_part (modest_init_mdp_env_defs.Modest_mdp_assn_aux N (St,Tr,Br,Pr,Av,Ta) ici)"
    by simp
  hence "rdomp (modest_init_mdp_env_defs.Modest_mdp_assn_aux N) (St,Tr,Br,Pr,Av,Ta)"
    unfolding rdomp_def pure_part_def by blast
  from Modest_mdp_assn_aux_boundsD[OF this]
  show "length Tr < max_size_t" and "length Br < max_size_t" by simp_all
qed

text \<open>The weakening itself: the builder's owned output becomes the borrowed view. Every hypothesis
  \<open>built_to_built'_ent\<close> needs is supplied by the relation (the built space's own invariant, at
  \<^term>\<open>M\<close> because the relation now pins \<open>M = length D\<close>) or by the assertion (the two machine-word
  bounds, chained onto the built arrays by \<^locale>\<open>modest_build_invar\<close>'s relative caps). So it holds
  unconditionally --- which is what makes it usable as a result weakening.\<close>
lemma build_M_to_build'_ent:
  "Modest_build_M_assn N M a ai \<turnstile> Modest_build_assn' N M a ai"
  unfolding Modest_build_M_assn_def Modest_build_assn'_def
proof (rule hr_comp_ent_mono)
  fix c :: "(modest_input_mdp \<times> modest_input_mdp) \<times> nat set list"
  assume REL: "(c, a) \<in> modest_build_M_rel N M"
  obtain ic bc D where C: "c = ((ic,bc),D)" by (cases c; cases "fst c") auto
  obtain St Tr Br Pr Av Ta where IC: "ic = (St,Tr,Br,Pr,Av,Ta)" by (cases ic)
  obtain St' Tr' Br' Pr' Av' Ta' where BC: "bc = (St',Tr',Br',Pr',Av',Ta')" by (cases bc)
  from REL have INV: "modest_build_invar N St Tr Br Pr Av Ta D St' Tr' Br' Pr' Av' Ta'"
    and MD: "M = length D"
    unfolding C IC BC modest_build_M_rel_def by (auto simp: in_br_conv)
  interpret B: modest_build_invar N St Tr Br Pr Av Ta D St' Tr' Br' Pr' Av' Ta' by (rule INV)
  have IIS: "modest_mdp_ii_invar_sup M St' Tr' Br' Pr' Av' Ta'"
    using INV MD by (simp add: modest_build_invar_def)
  have IN: "modest_mdp_input_invar M St' Tr' Br' Pr' Av' Ta'"
    using IIS by (simp add: modest_mdp_ii_invar_sup_def)
  show "((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn M)
         \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N) c ai
        \<turnstile> ((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn' M)
           \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N) c ai"
  proof -
    obtain qi Di where CI: "ai = (qi,Di)" by (cases ai)
    obtain ici bci where QI: "qi = (ici,bci)" by (cases qi)
    show ?thesis
      unfolding C IC BC CI QI
      apply (rule entails_pure_pre_extract[where
               P = "length Tr < max_size_t \<and> length Br < max_size_t"])
      subgoal by (auto dest: build_prod_boundsD)
      subgoal premises bnds
      proof -
        have TrM': "length Tr' < max_size_t" using B.Tr'_cap bnds by simp
        have BrM': "length Br' < max_size_t" using B.Br'_cap bnds by simp
        show ?thesis
          unfolding prod_assn_def
          apply (simp only: prod.case)
          apply (intro conj_entails_mono entails_refl)
          by (rule built_to_built'_ent[OF IN TrM' BrM'])
      qed
      done
  qed
qed


subsection \<open>The builder's \<open>hnr\<close> at the borrowed view\<close>

context collapse_build_env
begin

  text \<open>The builder hands its \<open>D\<close> argument straight back, so every result it can produce has
    \<open>snd r = D\<close>. That is all \<open>build_statespace_correct_M\<close> adds: the precondition's \<open>M = length D\<close>
    is moved from the argument side, where a result assertion cannot see it, into the output
    relation, where it can.\<close>

  lemma op_build_statespace_impl_shape:
    "nofail (op_build_statespace_impl (MDP,D)) \<Longrightarrow> inres (op_build_statespace_impl (MDP,D)) res
       \<Longrightarrow> \<exists>out. res = ((MDP,out),D)"
    unfolding op_build_statespace_impl_def by (auto simp: refine_pw_simps)

  lemma build_statespace_correct_M:
    "(PR_CONST op_build_statespace_impl, op_build_index)
     \<in> [\<lambda>x. M = length (snd x)]\<^sub>f modest_collapse_rel N \<rightarrow> \<langle>modest_build_M_rel N M\<rangle>nres_rel"
  proof (rule frefI)
    fix x y
    assume P: "M = length (snd y)" and REL: "(x,y) \<in> modest_collapse_rel N"
    obtain MDP D where X: "x = (MDP,D)" by (cases x)
    have SND: "D = snd y"
      using REL unfolding X
      by (cases MDP; cases y) (auto simp: modest_collapse_rel_iff)
    have UNF: "\<And>x y. M = length (snd y) \<Longrightarrow> (x,y) \<in> modest_collapse_rel N
                 \<Longrightarrow> (PR_CONST op_build_statespace_impl x, op_build_index y)
                       \<in> \<langle>modest_build_rel N\<rangle>nres_rel"
      using build_statespace_correct unfolding fref_def by blast
    note BASE = UNF[OF P REL, unfolded PR_CONST_def]
    show "(PR_CONST op_build_statespace_impl x, op_build_index y)
            \<in> \<langle>modest_build_M_rel N M\<rangle>nres_rel"
      unfolding modest_build_M_rel_alt PR_CONST_def
      apply (rule nres_rel_restrict_conc[OF BASE])
      unfolding X using op_build_statespace_impl_shape P SND by fastforce
  qed

  context
    notes [fcomp_norm_unfold] = f_triple_aux Modest_collapse_assn_def[symmetric]
      Modest_build_M_assn_def[symmetric]
  begin
    lemmas build_statespace_hnr_M = build_statespace_ll.refine[FCOMP build_statespace_correct_M]
  end

  text \<open>And the deliverable of this section: the builder, stated at the borrowed view. This is the
    rule the pipeline registers; the owned one stays where it is, unchanged.\<close>
  lemmas build_statespace_hnr' =
    hfref_cons_res[OF build_statespace_hnr_M build_M_to_build'_ent]

end


section \<open>Splitting the borrowed view for a kept inner call\<close>

text \<open>With the builder's output at \<^const>\<open>Modest_build_assn'\<close> the rest is bookkeeping: hand the
  built MDP to the interval iteration and keep everything else in the frame. The only subtlety is
  that \<^const>\<open>Modest_build_assn'\<close> binds its concrete tuple existentially, so the frame --- which
  names \<open>length St'\<close> and friends --- must be split off \<^emph>\<open>under\<close> that binder and rejoined under the
  same witness. That is what \<^const>\<open>Modest_mdp_sup_DS_assn\<close>'s pinning buys.\<close>

text \<open>Recovering the raw assertion from the pinned one. No precision argument is needed, and no
  appeal to \<open>hr_comp_entails_unique_dom\<close>: the relation's own invariant says the concrete tuple
  \<^emph>\<open>is\<close> \<open>DS\<close>, so the existential is a singleton by construction.\<close>
lemma sup_DS_to_aux_ent:
  "Modest_mdp_sup_DS_assn M DS a q \<turnstile> modest_init_mdp_env_defs.Modest_mdp_assn_aux M DS q"
  unfolding Modest_mdp_sup_DS_assn_def modest_mdp_sup_DS_rel_def hr_comp_def
  by (auto simp: in_br_conv entails_def sep_algebra_simps pred_lift_extract_simps
           split: prod.splits)

text \<open>Everything in the builder's output \<^emph>\<open>except\<close> the built MDP: the preserved input MDP, the six
  malloc tags, the decomposition, and the relation membership (pure, and needed to rebuild the
  \<^const>\<open>hr_comp\<close> afterwards). Across the inner call this is inert --- it is never opened.\<close>
definition "build'_frame N\<^sub>0 M w a ai =
  (modest_init_mdp_env_defs.Modest_mdp_assn_aux N\<^sub>0 (fst (fst w)) (fst (fst ai))
   ** built_tags (snd (fst w)) (snd (fst ai))
   ** disj_set_list_tuple_defs.mec_map_assn N\<^sub>0 N\<^sub>0 (snd w) (snd ai)
   ** \<up>((w,a) \<in> modest_build_M_rel N\<^sub>0 M))"

lemma build_M_relD:
  assumes "(((inp,(St',Tr',Br',Pr',Av',Ta')),D), a) \<in> modest_build_M_rel N\<^sub>0 M"
  shows "modest_mdp_ii_invar_sup M St' Tr' Br' Pr' Av' Ta'"
    and "a = \<M>_\<alpha>_sup' M (St',Tr',Br',Pr',Av',Ta')"
  using assms unfolding modest_build_M_rel_def
  by (auto simp: in_br_conv modest_build_invar_def split: prod.splits)

lemma build'_split:
  "Modest_build_assn' N\<^sub>0 M a ai
     \<turnstile> (EXS w. Modest_mdp_sup_DS_assn M (snd (fst w)) a (snd (fst ai))
               ** build'_frame N\<^sub>0 M w a ai)"
  unfolding Modest_build_assn'_def hr_comp_def
  apply (rule entails_exE2)
  subgoal for w
    apply (rule entails_exI[where x = w])
    apply (rule entails_pure_pre_extract[where P = "(w,a) \<in> modest_build_M_rel N\<^sub>0 M"])
    subgoal by (auto simp: sep_conj_def pred_lift_extract_simps)
    subgoal premises REL
    proof -
      obtain inp bt D where W: "w = ((inp,bt),D)" by (cases w; cases "fst w") auto
      obtain St' Tr' Br' Pr' Av' Ta' where BT: "bt = (St',Tr',Br',Pr',Av',Ta')" by (cases bt)
      obtain qi Di where AI: "ai = (qi,Di)" by (cases ai)
      obtain inpi bti where QI: "qi = (inpi,bti)" by (cases qi)
      note D = build_M_relD[OF REL[unfolded W BT]]
      show ?thesis
        unfolding W BT AI QI build'_frame_def prod_assn_def built_mdp_assn'_def
        apply (simp only: prod.case fst_conv snd_conv)
        apply (simp add: sep_conj_ac)
        apply (intro conj_entails_mono entails_refl)
        by (rule aux_to_sup_DS_ent[OF D(1), simplified D(2)[symmetric]])
    qed
    done
  done

lemma build'_join:
  "Modest_mdp_sup_DS_assn M (snd (fst w)) a (snd (fst ai)) ** build'_frame N\<^sub>0 M w a ai
     \<turnstile> Modest_build_assn' N\<^sub>0 M a ai"
  unfolding Modest_build_assn'_def hr_comp_def
  apply (rule entails_exI[where x = w])
  apply (rule entails_pure_pre_extract[where P = "(w,a) \<in> modest_build_M_rel N\<^sub>0 M"])
  subgoal by (auto simp: build'_frame_def sep_conj_def pred_lift_extract_simps)
  subgoal premises REL
  proof -
    obtain inp bt D where W: "w = ((inp,bt),D)" by (cases w; cases "fst w") auto
    obtain St' Tr' Br' Pr' Av' Ta' where BT: "bt = (St',Tr',Br',Pr',Av',Ta')" by (cases bt)
    obtain qi Di where AI: "ai = (qi,Di)" by (cases ai)
    obtain inpi bti where QI: "qi = (inpi,bti)" by (cases qi)
    show ?thesis
      unfolding W BT AI QI build'_frame_def prod_assn_def built_mdp_assn'_def
      apply (simp only: prod.case fst_conv snd_conv)
      apply (simp add: sep_conj_ac)
      apply (intro conj_entails_mono entails_refl)
      by (rule sup_DS_to_aux_ent)
  qed
  done

text \<open>The generic move this enables: an inner rule that holds at \<^emph>\<open>every\<close> witness lifts to an outer
  assertion that splits into it plus a frame, provided the frame can be rejoined at the same
  witness. The witness is bound inside the \<open>hn_refine\<close>, so it never escapes --- which is exactly why
  the tags do not have to be re-paired at the outer level.\<close>
lemma hn_refine_kept_adapt:
  assumes RULE: "\<And>w. hn_refine (A w ** B) cc (A w ** B) R CP aa"
  assumes FWD: "A' \<turnstile> (EXS w. A w ** F w)"
  assumes BWD: "\<And>w. A w ** F w \<turnstile> A'"
  shows "hn_refine (A' ** B) cc (A' ** B) R CP aa"
proof -
  have PRE: "A' ** B \<turnstile> (EXS w. (A w ** B) ** F w)"
    apply (rule entails_trans[OF conj_entails_mono[OF FWD entails_refl]])
    by (auto simp: entails_def sep_algebra_simps sep_conj_ac)
  show ?thesis
    apply (rule hn_refine_cons_pre[OF PRE])
    apply (subst hnr_pre_ex_conv)
    apply (intro allI)
    subgoal for w
      apply (rule hn_refine_cons_post[OF hn_refine_frame'[OF RULE]])
      apply (rule entails_trans[OF _ conj_entails_mono[OF BWD entails_refl]])
      by (auto simp: entails_def sep_algebra_simps sep_conj_ac)
    done
qed


section \<open>Interval iteration at the pinned assertion\<close>

text \<open>The bridge needs the interval-iteration rule at a \<open>DS\<close>-pinned assertion: only then is the
  concrete tuple determined on the way out, so the malloc tags can be re-paired with their arrays.
  It cannot be \<^emph>\<open>derived\<close> from the un-pinned rule (that direction needs a precision property the
  framework does not have), but it can be \<^emph>\<open>re-synthesised\<close> cheaply: every sub-op refinement lemma
  takes \<open>(DS, M) \<in> modest_mdp_sup_rel N\<close> as a hypothesis, and the pinned relation is a subset of
  it, so plain relation restriction plus a re-run of the existing \<open>FCOMP\<close>s suffices.

  All of this is \<^emph>\<open>additive\<close>: \<open>ii_max_impl_ll\<close> and \<open>ii_max_impl_hnr_raw\<close> keep their statements, so
  the reduction-free export is unaffected. The emitted code is the same loop under a second name ---
  the pinning is purely logical and costs nothing at runtime.\<close>

lemma fun_rel_restrict: "R' \<subseteq> R \<Longrightarrow> (f,g) \<in> R \<rightarrow> S \<Longrightarrow> (f,g) \<in> R' \<rightarrow> S"
  by (auto dest: fun_relD intro: fun_relI)

lemma fref_restrict: "R' \<subseteq> R \<Longrightarrow> (f,g) \<in> [P]\<^sub>f R \<rightarrow> S \<Longrightarrow> (f,g) \<in> [P]\<^sub>f R' \<rightarrow> S"
  by (auto simp: fref_def)

context interval_iteration_sup_env
begin

  lemma sup_DS_rel_subset: "modest_mdp_sup_DS_rel N DS \<subseteq> modest_mdp_sup_rel N"
    unfolding modest_mdp_sup_DS_rel_def modest_mdp_sup_rel_def by (auto simp: in_br_conv)

  lemma sup_DS_prod_subset:
    "((modest_mdp_sup_DS_rel N DS \<times>\<^sub>r A) \<times>\<^sub>r B) \<subseteq> ((modest_mdp_sup_rel N \<times>\<^sub>r A) \<times>\<^sub>r B)"
    by (auto simp: prod_rel_def dest!: sup_DS_rel_subset[THEN subsetD])

  lemmas init_lb_impl_correct_DS = fun_rel_restrict[OF sup_DS_rel_subset init_lb_impl_correct]
  lemmas init_ub_impl_correct_DS = fun_rel_restrict[OF sup_DS_rel_subset init_ub_impl_correct]
  lemmas isA_correct_DS = fun_rel_restrict[OF sup_DS_rel_subset isA_correct]
  lemmas isT_correct_DS = fun_rel_restrict[OF sup_DS_rel_subset isT_correct]
  lemmas updated_state_val_gs_impl_correct_DS =
    fref_restrict[OF sup_DS_prod_subset updated_state_val_gs_impl_correct]
  lemmas next_iter_correct_DS = fref_restrict[OF sup_DS_prod_subset next_iter_correct]

  context
    notes [fcomp_norm_unfold] = f_triple_aux Modest_mdp_sup_DS_assn_def[symmetric]
      output_ub_assn_alt[symmetric] output_lb_assn_alt[symmetric]
  begin

    lemmas mop_init_lb_hnr_DS = init_lb_ll_hnr[FCOMP init_lb_impl_correct_DS]
    lemmas mop_init_ub_hnr_DS = init_ub_ll_hnr[FCOMP init_ub_impl_correct_DS]
    lemmas mop_state_vals_gs_hnr_DS =
      updated_state_val_gs_impl_ll_hnr[FCOMP updated_state_val_gs_impl_correct_DS,
                                       folded mop_state_vals_gs_sup_def]
    lemmas op_is_avoid_hnr_DS = isA_ll_hnr[FCOMP isA_correct_DS]
    lemmas op_is_target_hnr_DS = isT_ll_hnr[FCOMP isT_correct_DS]
    lemmas next_iter_impl_ll_hnr_DS =
      next_iter_impl_ll.refine[FCOMP next_iter_correct_DS,
        unfolded next_iter_impl_max_ll'.refine[OF interval_iteration_sup_env_axioms]]

  end

  text \<open>The \<open>DS\<close>-pinned rules are \<^emph>\<open>supplied\<close> to the one synthesis that needs them rather than
    declared \<^theory_text>\<open>[sepref_fr_rules]\<close>. Declaring them would leak them into every downstream synthesis in
    this locale, and \<open>mop_state_vals_gs_hnr_DS\<close> --- whose argument assertion still carries a
    \<^emph>\<open>schematic\<close> \<open>?DS\<close> and whose result is a product --- then breaks \<open>sepref\<close>'s translation of plain
    \<^const>\<open>Pair\<close> construction (\<open>RETURN (a,b)\<close> stops synthesising, with \<open>Apply rule\<close> failing). The
    un-pinned rules from \<open>Modest_MDP_II_Maxred_Impl\<close> stay registered and are unaffected.\<close>

  sepref_definition ii_max_impl_DS_ll is "uncurry ii_max_impl"
    :: "(Modest_mdp_sup_DS_assn N DS)\<^sup>k *\<^sub>a size_assn\<^sup>k
        \<rightarrow>\<^sub>a (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn)"
    unfolding ii_max_impl_def PR_CONST_def
    supply [sepref_fr_rules] = mop_init_lb_hnr_DS mop_init_ub_hnr_DS mop_state_vals_gs_hnr_DS
      op_is_avoid_hnr_DS op_is_target_hnr_DS next_iter_impl_ll_hnr_DS
    supply [iff del] = length_greater_0_conv
    supply [simp] = upd_state_val_pre_def next_iter_pre_def
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done


  subsection \<open>\<dots> and at the builder's output\<close>

  text \<open>The builder's concrete side is a triple --- input MDP, built MDP, decomposition --- while the
    interval iteration takes the built MDP alone, so the rule needs a projection. At LLVM level that
    is two \<open>extractvalue\<close>s, which \<^const>\<open>prod_extract_fst\<close>/\<^const>\<open>prod_extract_snd\<close> provide; on a
    concrete pair they reduce away, so the wrapper \<^emph>\<open>is\<close> the inner loop.\<close>

  definition ii_max_built_ll where
    "ii_max_built_ll x L = doM {
       q \<leftarrow> prod_extract_fst x;
       bi \<leftarrow> prod_extract_snd q;
       ii_max_impl_DS_ll bi L }"

  lemma ii_max_built_ll_alt: "ii_max_built_ll ((inpi,bti),Di) Li = ii_max_impl_DS_ll bti Li"
    unfolding ii_max_built_ll_def by (simp add: prod_ops_simp)

  lemma ii_max_built_hnr_aux:
    "hn_refine (Modest_build_assn' N\<^sub>0 N m mi ** snat_assn L Li)
       (ii_max_built_ll mi Li)
       (Modest_build_assn' N\<^sub>0 N m mi ** snat_assn L Li)
       (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a snat_assn) (\<lambda>_. True)
       (ii_max_impl m L)"
  proof -
    obtain qi Di where MI: "mi = (qi,Di)" by (cases mi)
    obtain inpi bti where QI: "qi = (inpi,bti)" by (cases qi)
    have CC: "ii_max_built_ll mi Li = ii_max_impl_DS_ll bti Li"
      unfolding MI QI by (rule ii_max_built_ll_alt)
    have BTI: "snd (fst mi) = bti" unfolding MI QI by simp
    show ?thesis
      unfolding CC
      apply (rule hn_refine_kept_adapt[where
               A = "\<lambda>w. Modest_mdp_sup_DS_assn N (snd (fst w)) m bti"
               and F = "\<lambda>w. build'_frame N\<^sub>0 N w m mi"])
      subgoal for w
        using ii_max_impl_DS_ll.refine[where DS = "snd (fst w)", THEN hfrefD,
                of "(m,L)" "(bti,Li)", simplified] .
      subgoal using build'_split[of N\<^sub>0 N m mi] unfolding BTI .
      subgoal for w using build'_join[where M = N and w = w and a = m and ai = mi] unfolding BTI .
      done
  qed

  text \<open>Interval iteration on the freshly built state space, at the assertion the builder delivers.
    The built MDP is \<^emph>\<open>kept\<close>: nothing is destroyed, and the caller gets the whole triple back.\<close>
  lemma ii_max_built_hnr:
    "(uncurry ii_max_built_ll, uncurry ii_max_impl)
       \<in> (Modest_build_assn' N\<^sub>0 N)\<^sup>k *\<^sub>a size_assn\<^sup>k
         \<rightarrow>\<^sub>a (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn)"
    apply (rule hfrefI)
    subgoal for c a
      apply (cases a; cases c)
      apply (simp only: keep_drop_sels hfprod_fst_snd prod_assn_def prod.case uncurry_def)
      by (rule ii_max_built_hnr_aux)
    done

end


section \<open>A sorted MEC decomposition for the \<open>Sup\<close> case\<close>

text \<open>The MEC computation itself is mode-agnostic --- \<^const>\<open>modest_init_mdp_env_defs.collapse_to_mec_block\<close>
  throws the mode away by \<^const>\<open>to_mdpc\<close>, and \<^const>\<open>modest_init_mdp_env_defs.compute_mecs_mat\<close>,
  \<^const>\<open>modest_init_mdp_env_defs.compute_mecs_pre\<close> and their refinement are already stated in the
  mode-neutral \<^locale>\<open>modest_init_mdp_env_defs\<close>. All that is mode-specific is the block rule's
  \<^emph>\<open>source\<close> assertion, so only that is mirrored here. The min side is untouched.\<close>

context modest_init_mdp_env_defs
begin

  text \<open>The two sides of the block, at \<open>Sup\<close>. Both are the same \<^const>\<open>hr_comp\<close> over
    \<^const>\<open>modest_init_mdp_env_defs.Modest_mdp_assn_aux\<close>, so the concrete pointer never moves;
    only the abstraction changes, from the \<open>Sup\<close> \<^type>\<open>mdptc\<close> to the bare \<^type>\<open>mdpc\<close> the MEC
    algorithm wants.\<close>

  lemma Modest_mdp_sup_ent_MDP:
    "Modest_mdp_sup_DS_assn N DS \<M> ss \<turnstile> Modest_MDP_DS_assn DS (to_mdpc \<M>) ss"
    unfolding Modest_mdp_sup_DS_assn_def Modest_MDP_DS_assn_def
    apply (rule hr_comp_alt_rel)
    unfolding modest_mdp_sup_DS_rel_def modest_mdp_input_DS_rel_def modest_mdp_input_def.\<M>_\<alpha>_def
    by (auto simp: in_br_conv to_mdpc.abs_eq modest_mdp_ii_invar_sup_def modest_mdp_input_invar_def)

  lemma Modest_MDP_ent_mdp_sup:
    "pure_part (Modest_mdp_sup_DS_assn N DS \<M> ss)
       \<Longrightarrow> Modest_MDP_DS_assn DS M ss \<turnstile> Modest_mdp_sup_DS_assn N DS \<M> ss"
    unfolding Modest_MDP_DS_assn_def Modest_mdp_sup_DS_assn_def
    apply (erule hr_comp_entails_unique_dom)
    unfolding modest_mdp_sup_DS_rel_def modest_mdp_input_DS_rel_def
    by auto

  text \<open>The block rule itself. Structurally identical to the min one --- only the outer assertion
    differs --- so the proof is the same script.\<close>
  lemma hn_collapse_to_mec_block_sup:
    assumes FR: "\<Gamma> \<turnstile> hn_ctxt (Modest_mdp_sup_DS_assn N DS) p' p ** \<Gamma>1"
    assumes Pair: "\<And>a1' a1. hn_refine (hn_ctxt (Modest_MDP_DS_assn DS) a1' a1 \<and>* \<Gamma>1) (f a1)
                               (\<Gamma>1' a1' a1) R CP (f' a1')"
    assumes FR2: "\<And>a1' a1. \<Gamma>1' a1' a1 \<turnstile> hn_ctxt (Modest_MDP_DS_assn DS) a1' a1 ** \<Gamma>2'"
    shows "hn_refine \<Gamma> (f p) (hn_ctxt (Modest_mdp_sup_DS_assn N DS) p' p ** \<Gamma>2')
      R CP (collapse_to_mec_block$p'$(\<lambda>\<^sub>2 x. f' x))"
    apply (rule hn_refine_cons_pre[OF FR])
    unfolding autoref_tag_defs PROTECT2_def hr_comp_def
    apply (cases p')
    apply (clarsimp simp: collapse_to_mec_block_def hn_ctxt_def sep_conj_exists hnr_pre_ex_conv)
    apply (sepref_to_hoare)
    apply (rule htriple_pure_preI)
    apply (drule pure_part_split_conj, clarify)+
    supply [vcg_rules] = Pair[THEN hn_refineD, unfolded hn_ctxt_def,
                              THEN htriple_ent_pre[OF conj_entails_mono2[OF Modest_mdp_sup_ent_MDP]]]
    apply vcg
    apply (rule ENTAILS_trans_pre)
    apply (sep_drule FR2)
    unfolding hn_ctxt_def
    apply (erule conj_entails_mono2[OF conj_entails_mono2[OF Modest_MDP_ent_mdp_sup]])
    apply vcg'
    done

end


context modest_init_mdp_env
begin

  interpretation disj_set_list_tuple_defs N N ni ni .

  context
    notes [sepref_comb_rules] = hn_collapse_to_mec_block_sup
    and [sepref_monadify_arity] = collapse_to_mec_block_arity
    and [sepref_monadify_comb] = collapse_to_mec_block_comb
  begin

    sepref_definition compute_mecs_mat_sup_ll is "compute_mecs_mat"
      :: "[compute_mecs_pre]\<^sub>a (Modest_mdp_sup_DS_assn N DS)\<^sup>k \<rightarrow> mec_map_assn"
      unfolding compute_mecs_mat_def compute_mecs_pre_def
      apply sepref
      done

  end

  text \<open>Un-pinning \<open>DS\<close>: mandatory, and the step most easily forgotten. Same proof as the min side.\<close>
  lemma compute_mecs_mat_sup_hnr:
    "(compute_mecs_mat_sup_ll, op_compute_mecs)
       \<in> [compute_mecs_pre]\<^sub>a (Modest_mdp_sup_assn N)\<^sup>k \<rightarrow> mec_map_assn"
  proof -
    note REF = compute_mecs_mat_sup_ll.refine[FCOMP compute_mecs_mat_refine, to_hnr]
    show ?thesis
      apply (rule hfrefI)
      apply simp
      unfolding Modest_mdp_sup_assn_DS hnr_pre_ex_conv
      apply (rule allI)
      apply (sepref_to_hoare)
      supply [vcg_rules] = REF[THEN hn_refineD, unfolded hn_ctxt_def, simplified]
      by vcg
  qed

end

text \<open>Disambiguated from the min side's \<open>compute_mecs_mat_impl_ll'\<close>, so both load in one session.\<close>
concrete_definition (in -) compute_mecs_mat_sup_ll' [llvm_code] is
  modest_init_mdp_env.compute_mecs_mat_sup_ll_def

context modest_init_mdp_env
begin

  lemmas compute_mecs_mat_sup_hnr'[sepref_fr_rules] =
    compute_mecs_mat_sup_hnr[unfolded compute_mecs_mat_sup_ll'.refine[OF modest_init_mdp_env_axioms]]

  interpretation disj_set_list_tuple_defs N N ni ni .
  interpretation disj_set_list_tuple_env N N ni ni
    unfolding disj_set_list_tuple_env_def using n_impl by satx

  text \<open>The deliverable: a \<^emph>\<open>sorted\<close> MEC decomposition of a \<open>Sup\<close> Modest MDP. \<^const>\<open>compute_MEC_sorted\<close>
    is \<^const>\<open>op_compute_mecs\<close> followed by \<^const>\<open>op_sort_by_inf\<close>, both already registered, so the
    synthesis is bare.\<close>
  sepref_definition compute_MEC_sorted_sup_ll is "compute_MEC_sorted"
    :: "[\<lambda>M. compute_mecs_pre M]\<^sub>a (Modest_mdp_sup_assn N)\<^sup>k \<rightarrow> mec_map_assn"
    unfolding compute_MEC_sorted_def
    by sepref

end


section \<open>Reinterpretation folded into the builder (step 3 + step 5)\<close>

text \<open>\<^const>\<open>reinterpret\<close> is concretely the identity --- the collapsed MDP is the same bytes --- so
  instead of synthesising an identity program and registering \<^const>\<open>op_reinterpret\<close> on its own, the
  two abstract steps are composed at the \<open>nres\<close> level and the builder's existing LLVM function is
  \<open>FCOMP\<close>'d against the composite. That is also the shape \<open>tool_pmax\<close> uses: there
  \<^term>\<open>op_to_index (op_reinterpret (\<M>, D))\<close> is a single \<open>let\<close>.\<close>

definition op_build_reindex :: "(nat mdptc \<times> nat set list) \<Rightarrow> nat mdptc nres" where
  "op_build_reindex x = op_build_index (op_reinterpret x)"

sepref_register op_build_reindex

text \<open>\<^const>\<open>modest_mdp_sup_rel\<close> is \<^const>\<open>modest_mdp_rel\<close> with the stronger \<open>Sup\<close>
  interval-iteration invariant in place of the plain input one, so it is a subrelation and the
  reinterpretation refinement restricts to it unchanged.\<close>

lemma modest_mdp_sup_rel_subset: "modest_mdp_sup_rel N \<subseteq> modest_mdp_rel N"
  unfolding modest_mdp_sup_rel_def modest_mdp_rel_def
  by (auto simp: in_br_conv modest_mdp_ii_invar_sup_def split: prod.splits)

lemma modest_mdp_sup_prod_subset:
  "(modest_mdp_sup_rel N \<times>\<^sub>r Id) \<subseteq> (modest_mdp_rel N \<times>\<^sub>r Id)"
  by (auto simp: prod_rel_def dest!: modest_mdp_sup_rel_subset[THEN subsetD])

lemmas reinterpret_correct_sup = fref_restrict[OF modest_mdp_sup_prod_subset reinterpret_correct]

context collapse_build_env
begin

  lemma build_reindex_correct_M:
    "(PR_CONST op_build_statespace_impl, op_build_reindex)
     \<in> [\<lambda>x. reinterpret_pre x \<and> M = length (snd x)]\<^sub>f (modest_mdp_sup_rel N \<times>\<^sub>r Id)
       \<rightarrow> \<langle>modest_build_M_rel N M\<rangle>nres_rel"
  proof (rule frefI)
    fix x y
    assume P: "reinterpret_pre y \<and> M = length (snd y)"
      and REL: "(x,y) \<in> modest_mdp_sup_rel N \<times>\<^sub>r Id"
    have UNF1: "\<And>u v. reinterpret_pre v \<Longrightarrow> (u,v) \<in> modest_mdp_sup_rel N \<times>\<^sub>r Id
                  \<Longrightarrow> (reinterpret u, op_reinterpret v) \<in> modest_collapse_rel N"
      using reinterpret_correct_sup unfolding fref_def by blast
    have COL: "(x, op_reinterpret y) \<in> modest_collapse_rel N"
      using UNF1[OF _ REL] P by (simp add: reinterpret_def)
    have SND: "snd (op_reinterpret y) = snd y"
      by (cases y) (simp add: op_reinterpret_def)
    have MD: "M = length (snd (op_reinterpret y))" using P SND by simp
    have UNF2: "\<And>u v. M = length (snd v) \<Longrightarrow> (u,v) \<in> modest_collapse_rel N
                  \<Longrightarrow> (PR_CONST op_build_statespace_impl u, op_build_index v)
                        \<in> \<langle>modest_build_M_rel N M\<rangle>nres_rel"
      using build_statespace_correct_M unfolding fref_def by blast
    show "(PR_CONST op_build_statespace_impl x, op_build_reindex y)
            \<in> \<langle>modest_build_M_rel N M\<rangle>nres_rel"
      unfolding op_build_reindex_def by (rule UNF2[OF MD COL])
  qed

  context
    notes [fcomp_norm_unfold] = f_triple_aux Modest_mdp_sup_assn_def[symmetric]
      Modest_build_M_assn_def[symmetric]
  begin
    lemmas build_reindex_hnr_M = build_statespace_ll.refine[FCOMP build_reindex_correct_M]
  end

  text \<open>The pipeline's build step, end to end: a \<open>Sup\<close> Modest MDP plus its MEC decomposition in,
    the re-indexed max reduction out, at the borrowed view.\<close>
  lemmas build_reindex_hnr =
    hfref_cons_res[OF build_reindex_hnr_M build_M_to_build'_ent]

end


section \<open>The MEC count as an input parameter\<close>

text \<open>\<^term>\<open>M\<close> stays fixed \<^emph>\<open>inside\<close> \<^locale>\<open>collapse_build_env\<close> --- the builder's arrays and bitsets
  are sized by it, so it has to be. What changes here is the \<^emph>\<open>rule\<close>: \<^const>\<open>build_statespace_ll'\<close>
  already takes \<open>Mi\<close> as an LLVM argument, and \<open>build_reindex_hnr\<close> holds for \<^emph>\<open>every\<close> \<open>M\<close>/\<open>Mi\<close>
  satisfying \<open>M_impl\<close>, so @{thm [source] hfref_add_kept_pure_arg} turns it into an ordinary argument.

  That is what makes the pipeline possible: the MEC count is only known once
  \<open>compute_MEC_sorted_sup_ll\<close> has run (it is \<^const>\<open>op_mec_map_length\<close> of the decomposition), so it
  cannot be a locale parameter of the caller.\<close>

definition op_build_reindex' :: "nat \<Rightarrow> (nat mdptc \<times> nat set list) \<Rightarrow> nat mdptc nres" where
  "op_build_reindex' M x = op_build_reindex x"

sepref_register op_build_reindex'

lemma build_reindex_hnr_arg:
  assumes ENV: "interval_iteration_env N \<epsilon> ni \<epsilon>i"
  shows "(uncurry (build_statespace_ll' ni), uncurry op_build_reindex')
    \<in> [\<lambda>(M,x). Suc M < max_size_t \<and> (case x of (a,b) \<Rightarrow> reinterpret_pre (a,b) \<and> M = length b)]\<^sub>a
        size_assn\<^sup>k *\<^sub>a (Modest_mdp_sup_assn N \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N)\<^sup>d
      \<rightarrow>\<^sub>d (\<lambda>(M,_). Modest_build_assn' N M)"
  apply (rule hfref_add_kept_pure_arg[where R = snat_rel])
  subgoal premises p for v vi
  proof -
    have CBE: "collapse_build_env N \<epsilon> ni \<epsilon>i v vi"
      unfolding collapse_build_env_def collapse_build_env_axioms_def
      using ENV p by (auto simp: b_rel_def in_br_conv)
    show ?thesis
      unfolding op_build_reindex'_def[abs_def]
      using collapse_build_env.build_reindex_hnr[OF CBE]
      unfolding build_statespace_ll'.refine[OF CBE]
      by simp
  qed
  done


section \<open>An \<open>M\<close>-free view of the built state space\<close>

text \<open>\<open>M\<close> must not appear in any assertion that reaches the outside world. It need not: it is
  \<^emph>\<open>recovered\<close> from the concrete data, because \<^const>\<open>modest_mdp_input_invar\<close> forces
  \<open>length St' = Suc M\<close>. A raw assertion may depend on the concrete value --- that is exactly what
  makes this legal, and it is also why \<^const>\<open>output_lb_assn\<close>'s \<^const>\<open>raw_array_assn\<close> side is
  already parameterless.\<close>

definition built_mdp_assn_x :: "modest_input_mdp \<Rightarrow> modest_input_mdpi \<Rightarrow> assn" where
  "built_mdp_assn_x c ci =
     (modest_init_mdp_env_defs.Modest_mdp_assn_aux (length (fst c) - 1) c ci ** built_tags c ci)"

lemma built_mdp_assn_x_eq:
  assumes "length St' = Suc M"
  shows "built_mdp_assn_x (St',Tr',Br',Pr',Av',Ta') q = built_mdp_assn' M (St',Tr',Br',Pr',Av',Ta') q"
  unfolding built_mdp_assn_x_def built_mdp_assn'_def using assms by simp

lemma built_to_built_x_ent:
  assumes INV: "modest_mdp_input_invar M St' Tr' Br' Pr' Av' Ta'"
  assumes TrM: "length Tr' < max_size_t" and BrM: "length Br' < max_size_t"
  shows "built_mdp_assn M (St',Tr',Br',Pr',Av',Ta') q
           \<turnstile> built_mdp_assn_x (St',Tr',Br',Pr',Av',Ta') q"
proof -
  interpret I: modest_mdp_input_invar M St' Tr' Br' Pr' Av' Ta' by (rule INV)
  have LSt: "length St' = Suc M" using I.N_DEF I.N0 by simp
  show ?thesis
    unfolding built_mdp_assn_x_eq[OF LSt]
    by (rule built_to_built'_ent[OF INV TrM BrM])
qed

text \<open>\<^const>\<open>hr_comp\<close> monotone in \<^emph>\<open>both\<close> arguments at once, with the witness's membership available
  for the inner entailment.\<close>
lemma hr_comp_ent_mono2:
  assumes REL: "\<And>c. (c,a) \<in> R \<Longrightarrow> (c,a) \<in> R'"
  assumes ASSN: "\<And>c. (c,a) \<in> R \<Longrightarrow> A c ci \<turnstile> A' c ci"
  shows "hr_comp A R a ci \<turnstile> hr_comp A' R' a ci"
  using assms by (auto simp: hr_comp_def entails_def sep_algebra_simps pred_lift_extract_simps)

text \<open>The builder's output with no \<open>M\<close> anywhere. Note the relation is the plain
  \<^const>\<open>modest_build_rel\<close> again --- \<^const>\<open>modest_build_M_rel\<close> exists only to pin \<open>M\<close>, which the
  data now determines, so it is no longer needed past this point.\<close>
definition "Modest_build_assn_x N =
  hr_comp ((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn_x)
           \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N)
          (modest_build_rel N)"

lemma build_M_to_build_x_ent:
  "Modest_build_M_assn N M a ai \<turnstile> Modest_build_assn_x N a ai"
  unfolding Modest_build_M_assn_def Modest_build_assn_x_def
proof (rule hr_comp_ent_mono2)
  fix c
  assume REL: "(c, a) \<in> modest_build_M_rel N M"
  thus "(c,a) \<in> modest_build_rel N" using modest_build_M_rel_sub by blast
next
  fix c
  assume REL: "(c, a) \<in> modest_build_M_rel N M"
  obtain ic bc D where C: "c = ((ic,bc),D)" by (cases c; cases "fst c") auto
  obtain St Tr Br Pr Av Ta where IC: "ic = (St,Tr,Br,Pr,Av,Ta)" by (cases ic)
  obtain St' Tr' Br' Pr' Av' Ta' where BC: "bc = (St',Tr',Br',Pr',Av',Ta')" by (cases bc)
  from REL have INV: "modest_build_invar N St Tr Br Pr Av Ta D St' Tr' Br' Pr' Av' Ta'"
    and MD: "M = length D"
    unfolding C IC BC modest_build_M_rel_def by (auto simp: in_br_conv)
  interpret B: modest_build_invar N St Tr Br Pr Av Ta D St' Tr' Br' Pr' Av' Ta' by (rule INV)
  have IIS: "modest_mdp_ii_invar_sup M St' Tr' Br' Pr' Av' Ta'"
    using INV MD by (simp add: modest_build_invar_def)
  have IN: "modest_mdp_input_invar M St' Tr' Br' Pr' Av' Ta'"
    using IIS by (simp add: modest_mdp_ii_invar_sup_def)
  show "((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn M)
         \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N) c ai
        \<turnstile> ((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn_x)
           \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N) c ai"
  proof -
    obtain qi Di where CI: "ai = (qi,Di)" by (cases ai)
    obtain ici bci where QI: "qi = (ici,bci)" by (cases qi)
    show ?thesis
      unfolding C IC BC CI QI
      apply (rule entails_pure_pre_extract[where
               P = "length Tr < max_size_t \<and> length Br < max_size_t"])
      subgoal by (auto dest: build_prod_boundsD)
      subgoal premises bnds
      proof -
        have TrM': "length Tr' < max_size_t" using B.Tr'_cap bnds by simp
        have BrM': "length Br' < max_size_t" using B.Br'_cap bnds by simp
        show ?thesis
          unfolding prod_assn_def
          apply (simp only: prod.case)
          apply (intro conj_entails_mono entails_refl)
          by (rule built_to_built_x_ent[OF IN TrM' BrM'])
      qed
      done
  qed
qed

text \<open>Everything the relation determines about a witness. The third part is what makes
  \<^const>\<open>built_mdp_assn_x\<close> agree with \<^const>\<open>built_mdp_assn'\<close> at the right \<open>M\<close>; the fourth is the
  \<^emph>\<open>abstract\<close> handle on \<open>M\<close>, which is how a caller states the tie without mentioning the witness.\<close>
lemma build_relD:
  assumes "(((inp,(St',Tr',Br',Pr',Av',Ta')),D), a) \<in> modest_build_rel N\<^sub>0"
  shows "modest_mdp_ii_invar_sup (length D) St' Tr' Br' Pr' Av' Ta'"
    and "a = \<M>_\<alpha>_sup' (length D) (St',Tr',Br',Pr',Av',Ta')"
    and "length St' = Suc (length D)"
    and "states (to_mdpc a) = {0..<length D}"
proof -
  show IIS: "modest_mdp_ii_invar_sup (length D) St' Tr' Br' Pr' Av' Ta'"
    and AA: "a = \<M>_\<alpha>_sup' (length D) (St',Tr',Br',Pr',Av',Ta')"
    using assms unfolding modest_build_rel_def
    by (auto simp: in_br_conv modest_build_invar_def split: prod.splits)
  interpret I: modest_mdp_input_invar "length D" St' Tr' Br' Pr' Av' Ta'
    using IIS by (simp add: modest_mdp_ii_invar_sup_def)
  show "length St' = Suc (length D)" using I.N_DEF I.N0 by simp
  show "states (to_mdpc a) = {0..<length D}" unfolding AA by (simp add: I.states_M\<^sub>0_\<alpha>)
qed

definition "build_x_frame N\<^sub>0 w a ai =
  (modest_init_mdp_env_defs.Modest_mdp_assn_aux N\<^sub>0 (fst (fst w)) (fst (fst ai))
   ** built_tags (snd (fst w)) (snd (fst ai))
   ** disj_set_list_tuple_defs.mec_map_assn N\<^sub>0 N\<^sub>0 (snd w) (snd ai)
   ** \<up>((w,a) \<in> modest_build_rel N\<^sub>0))"

text \<open>The two halves at a \<^emph>\<open>named\<close> witness. Everything downstream --- the \<open>M\<close>-free view and the
  richer view of the next subsection --- is an instance of these, so the case analysis is done once.\<close>

abbreviation "build_raw_assn N\<^sub>0 \<equiv>
  ((modest_init_mdp_env_defs.Modest_mdp_assn_aux N\<^sub>0 \<times>\<^sub>a built_mdp_assn_x)
   \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N\<^sub>0 N\<^sub>0)"

lemma build_x_split_w:
  assumes REL: "(w,a) \<in> modest_build_rel N\<^sub>0"
  shows "build_raw_assn N\<^sub>0 w ai
     \<turnstile> Modest_mdp_sup_DS_assn (length (snd w)) (snd (fst w)) a (snd (fst ai))
       ** build_x_frame N\<^sub>0 w a ai"
proof -
  obtain inp bt D where W: "w = ((inp,bt),D)" by (cases w; cases "fst w") auto
  obtain St' Tr' Br' Pr' Av' Ta' where BT: "bt = (St',Tr',Br',Pr',Av',Ta')" by (cases bt)
  obtain qi Di where AI: "ai = (qi,Di)" by (cases ai)
  obtain inpi bti where QI: "qi = (inpi,bti)" by (cases qi)
  note D = build_relD[OF REL[unfolded W BT]]
  have R': "(((inp,(St',Tr',Br',Pr',Av',Ta')),D), a) \<in> modest_build_rel N\<^sub>0"
    using REL unfolding W BT .
  show ?thesis
    unfolding W BT AI QI build_x_frame_def prod_assn_def built_mdp_assn_x_def
    apply (simp only: prod.case fst_conv snd_conv D(3) diff_Suc_1)
    apply (simp add: sep_conj_ac R' sep_algebra_simps)
    apply (intro conj_entails_mono entails_refl)
    by (rule aux_to_sup_DS_ent[OF D(1), simplified D(2)[symmetric]])
qed

lemma build_x_join_w:
  assumes REL: "(w,a) \<in> modest_build_rel N\<^sub>0"
  shows "Modest_mdp_sup_DS_assn (length (snd w)) (snd (fst w)) a (snd (fst ai))
         ** build_x_frame N\<^sub>0 w a ai
     \<turnstile> build_raw_assn N\<^sub>0 w ai"
proof -
  obtain inp bt D where W: "w = ((inp,bt),D)" by (cases w; cases "fst w") auto
  obtain St' Tr' Br' Pr' Av' Ta' where BT: "bt = (St',Tr',Br',Pr',Av',Ta')" by (cases bt)
  obtain qi Di where AI: "ai = (qi,Di)" by (cases ai)
  obtain inpi bti where QI: "qi = (inpi,bti)" by (cases qi)
  note D = build_relD[OF REL[unfolded W BT]]
  have R': "(((inp,(St',Tr',Br',Pr',Av',Ta')),D), a) \<in> modest_build_rel N\<^sub>0"
    using REL unfolding W BT .
  show ?thesis
    unfolding W BT AI QI build_x_frame_def prod_assn_def built_mdp_assn_x_def
    apply (simp only: prod.case fst_conv snd_conv D(3) diff_Suc_1)
    apply (simp add: sep_conj_ac R' sep_algebra_simps)
    apply (intro conj_entails_mono entails_refl)
    by (rule sup_DS_to_aux_ent)
qed

lemma build_x_split:
  "Modest_build_assn_x N\<^sub>0 a ai
     \<turnstile> (EXS w. Modest_mdp_sup_DS_assn (length (snd w)) (snd (fst w)) a (snd (fst ai))
               ** build_x_frame N\<^sub>0 w a ai)"
  unfolding Modest_build_assn_x_def hr_comp_def
  apply (rule entails_exE2)
  subgoal for w
    apply (rule entails_exI[where x = w])
    apply (rule entails_pure_pre_extract[where P = "(w,a) \<in> modest_build_rel N\<^sub>0"])
    subgoal by (auto simp: sep_conj_def pred_lift_extract_simps)
    subgoal premises REL
      apply (rule entails_trans[OF _ build_x_split_w[OF REL]])
      by (auto simp: entails_def sep_conj_def pred_lift_extract_simps)
    done
  done

lemma build_x_join:
  "Modest_mdp_sup_DS_assn (length (snd w)) (snd (fst w)) a (snd (fst ai))
   ** build_x_frame N\<^sub>0 w a ai
     \<turnstile> Modest_build_assn_x N\<^sub>0 a ai"
  unfolding Modest_build_assn_x_def hr_comp_def
  apply (rule entails_exI[where x = w])
  apply (rule entails_pure_pre_extract[where P = "(w,a) \<in> modest_build_rel N\<^sub>0"])
  subgoal by (auto simp: build_x_frame_def sep_conj_def pred_lift_extract_simps)
  subgoal premises REL
    apply (rule entails_trans[OF build_x_join_w[OF REL]])
    using REL by (auto simp: entails_def sep_conj_def pred_lift_extract_simps)
  done


subsection \<open>The richer view: input state space and decomposition kept in the abstraction\<close>

text \<open>\<^const>\<open>Modest_build_assn_x\<close> abstracts the builder's concrete triple --- input MDP, built MDP,
  MEC decomposition --- to the built MDP \<^emph>\<open>alone\<close>. That is enough to run interval iteration, but it
  makes the other two components invisible to any specification: a caller physically gets them back,
  yet nothing is claimed about them. Here the abstraction is widened to the triple
  \<^term>\<open>(a\<^sub>0, D, a)\<close>, so the pipeline's specification can say what the returned input state space and
  decomposition are, and that \<open>a\<close> is the max reduction of \<open>a\<^sub>0\<close>.

  Nothing is added to the \<^emph>\<open>concrete\<close> side, so this costs no code: \<^const>\<open>build_raw_assn\<close> is the
  same raw assertion, only composed with a wider relation.\<close>

definition modest_build_rel_t ::
  "nat \<Rightarrow> (((modest_input_mdp \<times> modest_input_mdp) \<times> nat set list)
           \<times> (nat mdptc \<times> nat set list \<times> nat mdptc)) set" where
  "modest_build_rel_t N = br (\<lambda>w. (\<M>_\<alpha>_sup' N (fst (fst w)), snd w, build_\<alpha> w)) (build_inv N)"

lemma modest_build_rel_tD:
  assumes "(w,t) \<in> modest_build_rel_t N"
  shows "(w, snd (snd t)) \<in> modest_build_rel N"
    and "fst t = \<M>_\<alpha>_sup' N (fst (fst w))"
    and "fst (snd t) = snd w"
  using assms unfolding modest_build_rel_t_def modest_build_rel_def by (auto simp: in_br_conv)

lemma modest_build_rel_tI:
  assumes "(w,a) \<in> modest_build_rel N"
  shows "(w, (\<M>_\<alpha>_sup' N (fst (fst w)), snd w, a)) \<in> modest_build_rel_t N"
  using assms unfolding modest_build_rel_t_def modest_build_rel_def by (auto simp: in_br_conv)

definition "Modest_build_assn_t N = hr_comp (build_raw_assn N) (modest_build_rel_t N)"

definition "build_t_frame N\<^sub>0 w t ai =
  (build_x_frame N\<^sub>0 w (snd (snd t)) ai
   ** \<up>(fst t = \<M>_\<alpha>_sup' N\<^sub>0 (fst (fst w)) \<and> fst (snd t) = snd w))"

lemma build_t_split:
  "Modest_build_assn_t N\<^sub>0 t ai
     \<turnstile> (EXS w. Modest_mdp_sup_DS_assn (length (snd w)) (snd (fst w)) (snd (snd t)) (snd (fst ai))
               ** build_t_frame N\<^sub>0 w t ai)"
  unfolding Modest_build_assn_t_def hr_comp_def
  apply (rule entails_exE2)
  subgoal for w
    apply (rule entails_exI[where x = w])
    apply (rule entails_pure_pre_extract[where P = "(w,t) \<in> modest_build_rel_t N\<^sub>0"])
    subgoal by (auto simp: sep_conj_def pred_lift_extract_simps)
    subgoal premises REL
      using modest_build_rel_tD(2,3)[OF REL] build_x_split_w[OF modest_build_rel_tD(1)[OF REL]]
      unfolding build_t_frame_def
      by (auto simp: entails_def sep_conj_def pred_lift_extract_simps)
    done
  done

lemma build_t_join:
  "Modest_mdp_sup_DS_assn (length (snd w)) (snd (fst w)) (snd (snd t)) (snd (fst ai))
   ** build_t_frame N\<^sub>0 w t ai
     \<turnstile> Modest_build_assn_t N\<^sub>0 t ai"
  unfolding Modest_build_assn_t_def hr_comp_def
  apply (rule entails_exI[where x = w])
  apply (rule entails_pure_pre_extract[where
           P = "(w, snd (snd t)) \<in> modest_build_rel N\<^sub>0
                \<and> fst t = \<M>_\<alpha>_sup' N\<^sub>0 (fst (fst w)) \<and> fst (snd t) = snd w"])
  subgoal by (auto simp: build_t_frame_def build_x_frame_def sep_conj_def pred_lift_extract_simps)
  subgoal premises REL
  proof -
    have T: "t = (fst t, fst (snd t), snd (snd t))" by simp
    have REL': "(w,t) \<in> modest_build_rel_t N\<^sub>0"
      apply (subst T)
      using modest_build_rel_tI[OF conjunct1[OF REL]] REL by simp
    show ?thesis
      using build_x_join_w[OF conjunct1[OF REL]] REL'
      unfolding build_t_frame_def
      by (auto simp: entails_def sep_conj_def pred_lift_extract_simps)
  qed
  done



subsection \<open>Interval iteration at the \<open>M\<close>-free assertion\<close>

text \<open>The tie between a caller's \<open>M\<close> and the witness, stated \<^emph>\<open>abstractly\<close>: a caller can say
  \<open>states (to_mdpc a) = {0..<M}\<close> without mentioning the concrete data at all. This is the same
  condition \<^locale>\<open>interval_iteration_sup_code\<close> already assumes of its MDP, so it costs nothing.\<close>
lemma build_x_tie:
  assumes REL: "(w,a) \<in> modest_build_rel N\<^sub>0"
  assumes ST: "states (to_mdpc a) = {0..<M}"
  shows "length (snd w) = M"
proof -
  obtain inp bt D where W: "w = ((inp,bt),D)" by (cases w; cases "fst w") auto
  obtain St' Tr' Br' Pr' Av' Ta' where BT: "bt = (St',Tr',Br',Pr',Av',Ta')" by (cases bt)
  from build_relD(4)[OF REL[unfolded W BT]] ST
  have "{0..<length D} = {0..<M}" by simp
  thus ?thesis unfolding W by (metis card_atLeastLessThan diff_zero snd_conv)
qed

lemma build_x_split_M:
  assumes ST: "states (to_mdpc a) = {0..<M}"
  shows "Modest_build_assn_x N\<^sub>0 a ai
    \<turnstile> (EXS w. Modest_mdp_sup_DS_assn M (snd (fst w)) a (snd (fst ai))
              ** build_x_frame N\<^sub>0 w a ai)"
  apply (rule entails_trans[OF build_x_split])
  apply (rule entails_exE2)
  subgoal for w
    apply (rule entails_exI[where x = w])
    apply (rule entails_pure_pre_extract[where P = "(w,a) \<in> modest_build_rel N\<^sub>0"])
    subgoal by (auto simp: build_x_frame_def sep_conj_def pred_lift_extract_simps)
    subgoal premises REL using build_x_tie[OF REL ST] by simp
    done
  done

lemma build_x_join_M:
  assumes ST: "states (to_mdpc a) = {0..<M}"
  shows "Modest_mdp_sup_DS_assn M (snd (fst w)) a (snd (fst ai)) ** build_x_frame N\<^sub>0 w a ai
    \<turnstile> Modest_build_assn_x N\<^sub>0 a ai"
  apply (rule entails_trans[OF _ build_x_join[where w = w]])
  apply (rule entails_pure_pre_extract[where P = "(w,a) \<in> modest_build_rel N\<^sub>0"])
  subgoal by (auto simp: build_x_frame_def sep_conj_def pred_lift_extract_simps)
  subgoal premises REL using build_x_tie[OF REL ST] by simp
  done

lemma build_t_tie:
  assumes REL: "(w,t) \<in> modest_build_rel_t N\<^sub>0"
  assumes ST: "states (to_mdpc (snd (snd t))) = {0..<M}"
  shows "length (snd w) = M"
  by (rule build_x_tie[OF modest_build_rel_tD(1)[OF REL] ST])

lemma build_t_split_M:
  assumes ST: "states (to_mdpc (snd (snd t))) = {0..<M}"
  shows "Modest_build_assn_t N\<^sub>0 t ai
    \<turnstile> (EXS w. Modest_mdp_sup_DS_assn M (snd (fst w)) (snd (snd t)) (snd (fst ai))
              ** build_t_frame N\<^sub>0 w t ai)"
  apply (rule entails_trans[OF build_t_split])
  apply (rule entails_exE2)
  subgoal for w
    apply (rule entails_exI[where x = w])
    apply (rule entails_pure_pre_extract[where
             P = "(w, snd (snd t)) \<in> modest_build_rel N\<^sub>0"])
    subgoal by (auto simp: build_t_frame_def build_x_frame_def sep_conj_def
                           pred_lift_extract_simps)
    subgoal premises REL using build_x_tie[OF REL ST] by simp
    done
  done

lemma build_t_join_M:
  assumes ST: "states (to_mdpc (snd (snd t))) = {0..<M}"
  shows "Modest_mdp_sup_DS_assn M (snd (fst w)) (snd (snd t)) (snd (fst ai))
         ** build_t_frame N\<^sub>0 w t ai
    \<turnstile> Modest_build_assn_t N\<^sub>0 t ai"
  apply (rule entails_trans[OF _ build_t_join[where w = w]])
  apply (rule entails_pure_pre_extract[where P = "(w, snd (snd t)) \<in> modest_build_rel N\<^sub>0"])
  subgoal by (auto simp: build_t_frame_def build_x_frame_def sep_conj_def
                         pred_lift_extract_simps)
  subgoal premises REL using build_x_tie[OF REL ST] by simp
  done

text \<open>Interval iteration on the built state space, with the argument assertion free of \<open>M\<close>. \<open>M\<close> now
  enters only through the locale instance --- hence through \<open>Mi\<close>, which is already an argument of the
  emitted function --- and through the \<^emph>\<open>result\<close> assertion, where the dependent arrow can carry it.\<close>
lemma ii_max_built_x_hnr_aux:
  assumes ENV: "interval_iteration_sup_env M \<epsilon> Mi \<epsilon>i"
  assumes ST: "states (to_mdpc m) = {0..<M}"
  shows "hn_refine (Modest_build_assn_x N\<^sub>0 m mi ** snat_assn L Li)
           (interval_iteration_sup_env.ii_max_built_ll Mi \<epsilon>i mi Li)
           (Modest_build_assn_x N\<^sub>0 m mi ** snat_assn L Li)
           (output_lb_assn M \<times>\<^sub>a output_ub_assn M \<times>\<^sub>a snat_assn) (\<lambda>_. True)
           (interval_iteration_sup_env_defs.ii_max_impl m L)"
proof -
  obtain qi Di where MI: "mi = (qi,Di)" by (cases mi)
  obtain inpi bti where QI: "qi = (inpi,bti)" by (cases qi)
  have CC: "interval_iteration_sup_env.ii_max_built_ll Mi \<epsilon>i mi Li
              = interval_iteration_sup_env.ii_max_impl_DS_ll Mi \<epsilon>i bti Li"
    unfolding MI QI by (rule interval_iteration_sup_env.ii_max_built_ll_alt[OF ENV])
  have BTI: "snd (fst mi) = bti" unfolding MI QI by simp
  show ?thesis
    unfolding CC
    apply (rule hn_refine_kept_adapt[where
             A = "\<lambda>w. Modest_mdp_sup_DS_assn M (snd (fst w)) m bti"
             and F = "\<lambda>w. build_x_frame N\<^sub>0 w m mi"])
    subgoal for w
      using interval_iteration_sup_env.ii_max_impl_DS_ll.refine[OF ENV,
              where DS = "snd (fst w)", THEN hfrefD, where c = "(bti,Li)" and a = "(m,L)",
              simplified] .
    subgoal using build_x_split_M[OF ST, where N\<^sub>0 = N\<^sub>0 and ai = mi, unfolded BTI] .
    subgoal for w
      using build_x_join_M[OF ST, where N\<^sub>0 = N\<^sub>0 and ai = mi and w = w, unfolded BTI] .
    done
qed


text \<open>The same, at the richer view. Only the abstraction differs --- the emitted loop and the
  concrete data are literally the same --- so the proof is the \<open>t\<close>-instance of the same adapter.\<close>
lemma ii_max_built_t_hnr_aux:
  assumes ENV: "interval_iteration_sup_env M \<epsilon> Mi \<epsilon>i"
  assumes ST: "states (to_mdpc (snd (snd t))) = {0..<M}"
  shows "hn_refine (Modest_build_assn_t N\<^sub>0 t mi ** snat_assn L Li)
           (interval_iteration_sup_env.ii_max_built_ll Mi \<epsilon>i mi Li)
           (Modest_build_assn_t N\<^sub>0 t mi ** snat_assn L Li)
           (output_lb_assn M \<times>\<^sub>a output_ub_assn M \<times>\<^sub>a snat_assn) (\<lambda>_. True)
           (interval_iteration_sup_env_defs.ii_max_impl (snd (snd t)) L)"
proof -
  obtain qi Di where MI: "mi = (qi,Di)" by (cases mi)
  obtain inpi bti where QI: "qi = (inpi,bti)" by (cases qi)
  have CC: "interval_iteration_sup_env.ii_max_built_ll Mi \<epsilon>i mi Li
              = interval_iteration_sup_env.ii_max_impl_DS_ll Mi \<epsilon>i bti Li"
    unfolding MI QI by (rule interval_iteration_sup_env.ii_max_built_ll_alt[OF ENV])
  have BTI: "snd (fst mi) = bti" unfolding MI QI by simp
  show ?thesis
    unfolding CC
    apply (rule hn_refine_kept_adapt[where
             A = "\<lambda>w. Modest_mdp_sup_DS_assn M (snd (fst w)) (snd (snd t)) bti"
             and F = "\<lambda>w. build_t_frame N\<^sub>0 w t mi"])
    subgoal for w
      using interval_iteration_sup_env.ii_max_impl_DS_ll.refine[OF ENV,
              where DS = "snd (fst w)", THEN hfrefD,
              where c = "(bti,Li)" and a = "(snd (snd t),L)", simplified] .
    subgoal using build_t_split_M[OF ST, where N\<^sub>0 = N\<^sub>0 and ai = mi, unfolded BTI] .
    subgoal for w
      using build_t_join_M[OF ST, where N\<^sub>0 = N\<^sub>0 and ai = mi and w = w, unfolded BTI] .
    done
qed

section \<open>The exposed result: value arrays bundled with the built MDP\<close>

text \<open>The value arrays depend on \<open>M\<close> too, and unlike the MDP they cannot shed it on their own:
  \<^const>\<open>output_lb_assn\<close> is \<^term>\<open>hr_comp raw_array_assn (\<langle>node_rel' M, nn_real_lb_double_rel\<rangle>list_fun_rel M)\<close>,
  whose abstract side is a \<^emph>\<open>total function\<close> constrained only on \<open>{0..<M}\<close>. That relation is not
  single-valued in the function direction, so \<open>M\<close> is not recoverable from the abstract value --- for
  the built MDP it is (\<open>length St' = Suc M\<close>), for these it is not.

  So the arrays cannot each carry their own \<open>M\<close>-free assertion; they must \<^emph>\<open>share\<close> one. Bundling the
  whole result tuple under a single \<^const>\<open>hr_comp\<close> does exactly that: \<open>M\<close> is read off the build
  witness once and then constrains both array lengths. It occurs nowhere a caller can see.

  This works because the raw sides are already parameterless --- \<^const>\<open>raw_array_assn\<close> takes no
  size, and \<^const>\<open>built_mdp_assn_x\<close> recovers its own.\<close>

lemma hr_comp_bundle3_pure:
  assumes REL: "\<And>c1 c2 c3. (c1,a1) \<in> R1 \<Longrightarrow> (c2,a2) \<in> R2 \<Longrightarrow> (c3,a3) \<in> R3
             \<Longrightarrow> ((c1,c2,c3,a4),(a1,a2,a3,a4)) \<in> R"
  shows "hr_comp A1 R1 a1 ci1 ** hr_comp A2 R2 a2 ci2 ** hr_comp A3 R3 a3 ci3 ** A4 a4 ci4
         \<turnstile> hr_comp (A1 \<times>\<^sub>a A2 \<times>\<^sub>a A3 \<times>\<^sub>a A4) R (a1,a2,a3,a4) (ci1,ci2,ci3,ci4)"
  unfolding hr_comp_def prod_assn_def
  apply (clarsimp simp: entails_def sep_conj_def pred_lift_extract_simps)
  subgoal for s c1 s1 c2 s2 c3 s3
    apply (rule exI[of _ c1], rule exI[of _ c2], rule exI[of _ s3], rule exI[of _ a4])
    apply (rule conjI)
    subgoal
      apply (rule exI[of _ s], rule exI[of _ "s1 + (s2 + c3)"])
      apply (simp add: sep_algebra_simps)
      apply (rule exI[of _ s1], rule exI[of _ "s2 + c3"])
      apply (simp add: sep_algebra_simps)
      apply (rule exI[of _ s2], rule exI[of _ c3])
      by (simp add: sep_algebra_simps)
    subgoal using REL by simp
    done
  done

text \<open>The abstract side is the \<^emph>\<open>triple\<close> \<^term>\<open>(a\<^sub>0,D,a)\<close> of \<^const>\<open>modest_build_rel_t\<close> together with
  the two value functions and the iteration count. So a specification written against this assertion
  can talk about all three state-space components the caller physically receives --- the input MDP,
  its MEC decomposition, and the reduced MDP --- not just the last.\<close>

definition "build_out_rel N =
  {((c,xs,ys,i),(t,x,y,j)) | c xs ys i t x y j.
     (c,t) \<in> modest_build_rel_t N \<and> j = i
     \<and> (xs,x) \<in> \<langle>node_rel' (length (snd c)), nn_real_lb_double_rel\<rangle>list_fun_rel (length (snd c))
     \<and> (ys,y) \<in> \<langle>node_rel' (length (snd c)), nn_real_ub_double_rel\<rangle>list_fun_rel (length (snd c))}"

definition "Modest_build_out_assn N =
  hr_comp ((build_raw_assn N) \<times>\<^sub>a raw_array_assn \<times>\<^sub>a raw_array_assn \<times>\<^sub>a size_assn)
          (build_out_rel N)"

lemma build_out_bundle:
  assumes ST: "states (to_mdpc (snd (snd t))) = {0..<M}"
  shows "Modest_build_assn_t N t mi ** output_lb_assn M lb lbi ** output_ub_assn M ub ubi
           ** size_assn i ii
         \<turnstile> Modest_build_out_assn N (t,lb,ub,i) (mi,lbi,ubi,ii)"
proof -
  obtain a\<^sub>0 D a where T: "t = (a\<^sub>0,D,a)" by (cases t; cases "snd t") auto
  show ?thesis
    unfolding Modest_build_out_assn_def Modest_build_assn_t_def
              output_lb_assn_def output_ub_assn_def
    apply (rule hr_comp_bundle3_pure)
    using build_t_tie[OF _ ST] by (auto simp: build_out_rel_def T)
qed


section \<open>The pipeline's two rules, both at the \<open>M\<close>-free assertion\<close>

text \<open>The emitted constants. \<^const>\<open>interval_iteration_sup_env.ii_max_built_ll\<close> is a plain
  \<^theory_text>\<open>definition\<close> in the locale, so it gets a hand-written global counterpart in terms of the
  \<open>concrete_definition\<close> for the loop.\<close>

concrete_definition (in -) ii_max_impl_DS_ll' [llvm_code] is
  interval_iteration_sup_env.ii_max_impl_DS_ll_def

definition ii_max_built_ll' where [llvm_code]:
  "ii_max_built_ll' ni \<epsilon>i x L = doM {
     q \<leftarrow> prod_extract_fst x;
     bi \<leftarrow> prod_extract_snd q;
     ii_max_impl_DS_ll' ni \<epsilon>i bi L }"

lemma ii_max_built_ll'_eq:
  assumes ENV: "interval_iteration_sup_env N \<epsilon> ni \<epsilon>i"
  shows "interval_iteration_sup_env.ii_max_built_ll ni \<epsilon>i x L = ii_max_built_ll' ni \<epsilon>i x L"
  unfolding ii_max_built_ll'_def
            interval_iteration_sup_env.ii_max_built_ll_def[OF ENV]
            ii_max_impl_DS_ll'.refine[OF ENV]
  by (rule refl)

text \<open>\<^const>\<open>interval_iteration_sup_env_defs.ii_max_impl\<close> has no locale parameters, so the abstract
  program is literally the same at every \<open>M\<close>; this wrapper only threads \<open>M\<close> so the arities match.\<close>
definition ii_max_impl_x :: "nat \<Rightarrow> nat mdptc \<Rightarrow> nat \<Rightarrow> _ nres" where
  "ii_max_impl_x M m L = interval_iteration_sup_env_defs.ii_max_impl m L"

lemma ii_max_built_x_hnr_aux2:
  assumes EPS: "(\<epsilon>i,\<epsilon>) \<in> nn_real_lb_double_rel"
  assumes MREL: "(Mi,M) \<in> snat_rel"
  assumes MB: "2*M < max_size_t"
  assumes ST: "states (to_mdpc m) = {0..<M}"
  shows "hn_refine (snat_assn M Mi ** Modest_build_assn_x N\<^sub>0 m mi ** snat_assn L Li)
           (ii_max_built_ll' Mi \<epsilon>i mi Li)
           (snat_assn M Mi ** Modest_build_assn_x N\<^sub>0 m mi ** snat_assn L Li)
           (output_lb_assn M \<times>\<^sub>a output_ub_assn M \<times>\<^sub>a snat_assn) (\<lambda>_. True)
           (ii_max_impl_x M m L)"
proof -
  have ENV: "interval_iteration_sup_env M \<epsilon> Mi \<epsilon>i"
    using MREL MB EPS by unfold_locales (auto simp: b_rel_def in_br_conv)
  show ?thesis
    unfolding ii_max_impl_x_def ii_max_built_ll'_eq[OF ENV, symmetric]
    apply (rule hn_refine_cons[OF _ hn_refine_frame'[where F = "snat_assn M Mi",
             OF ii_max_built_x_hnr_aux[OF ENV ST, where N\<^sub>0 = N\<^sub>0]]])
    subgoal by (simp add: sep_algebra_simps sep_conj_ac entails_refl)
    subgoal by (simp add: sep_algebra_simps sep_conj_ac entails_refl)
    subgoal by simp
    done
qed

lemma ii_max_built_t_hnr_aux2:
  assumes EPS: "(\<epsilon>i,\<epsilon>) \<in> nn_real_lb_double_rel"
  assumes MREL: "(Mi,M) \<in> snat_rel"
  assumes MB: "2*M < max_size_t"
  assumes ST: "states (to_mdpc (snd (snd t))) = {0..<M}"
  shows "hn_refine (snat_assn M Mi ** Modest_build_assn_t N\<^sub>0 t mi ** snat_assn L Li)
           (ii_max_built_ll' Mi \<epsilon>i mi Li)
           (snat_assn M Mi ** Modest_build_assn_t N\<^sub>0 t mi ** snat_assn L Li)
           (output_lb_assn M \<times>\<^sub>a output_ub_assn M \<times>\<^sub>a snat_assn) (\<lambda>_. True)
           (ii_max_impl_x M (snd (snd t)) L)"
proof -
  have ENV: "interval_iteration_sup_env M \<epsilon> Mi \<epsilon>i"
    using MREL MB EPS by unfold_locales (auto simp: b_rel_def in_br_conv)
  show ?thesis
    unfolding ii_max_impl_x_def ii_max_built_ll'_eq[OF ENV, symmetric]
    apply (rule hn_refine_cons[OF _ hn_refine_frame'[where F = "snat_assn M Mi",
             OF ii_max_built_t_hnr_aux[OF ENV ST, where N\<^sub>0 = N\<^sub>0]]])
    subgoal by (simp add: sep_algebra_simps sep_conj_ac entails_refl)
    subgoal by (simp add: sep_algebra_simps sep_conj_ac entails_refl)
    subgoal by simp
    done
qed

text \<open>Interval iteration with the MEC count as an input parameter. Every argument assertion is
  \<open>M\<close>-free; only the result mentions \<open>M\<close>, which the dependent arrow carries.\<close>
lemma ii_max_built_x_hnr:
  assumes EPS: "(\<epsilon>i,\<epsilon>) \<in> nn_real_lb_double_rel"
  shows "(uncurry2 (\<lambda>Mi m L. ii_max_built_ll' Mi \<epsilon>i m L), uncurry2 ii_max_impl_x)
    \<in> [\<lambda>((M,m),L). 2*M < max_size_t \<and> states (to_mdpc m) = {0..<M}]\<^sub>a
        size_assn\<^sup>k *\<^sub>a (Modest_build_assn_x N\<^sub>0)\<^sup>k *\<^sub>a size_assn\<^sup>k
      \<rightarrow>\<^sub>d (\<lambda>((M,_),_). output_lb_assn M \<times>\<^sub>a output_ub_assn M \<times>\<^sub>a snat_assn)"
  apply (rule hfrefI)
  apply (clarsimp split: prod.splits)
  apply (rule hn_refine_preI)
  apply (rule ii_max_built_x_hnr_aux2[OF EPS])
    apply (auto simp: sep_conj_def pure_def pred_lift_extract_simps)
  done

text \<open>And the builder at the same assertion. Because its result no longer mentions \<open>M\<close>, the
  dependent arrow disappears here --- a plain \<open>\<rightarrow>\<close> suffices.\<close>

lemma build'_to_build_x_ent:
  "Modest_build_assn' N M a ai \<turnstile> Modest_build_assn_x N a ai"
  unfolding Modest_build_assn'_def Modest_build_assn_x_def
proof (rule hr_comp_ent_mono2)
  fix c
  assume REL: "(c, a) \<in> modest_build_M_rel N M"
  thus "(c,a) \<in> modest_build_rel N" using modest_build_M_rel_sub by blast
next
  fix c
  assume REL: "(c, a) \<in> modest_build_M_rel N M"
  obtain ic bc D where C: "c = ((ic,bc),D)" by (cases c; cases "fst c") auto
  obtain St' Tr' Br' Pr' Av' Ta' where BC: "bc = (St',Tr',Br',Pr',Av',Ta')" by (cases bc)
  from REL have RELp: "(c,a) \<in> modest_build_rel N" using modest_build_M_rel_sub by blast
  from REL have MD: "M = length D"
    unfolding C modest_build_M_rel_def by (auto simp: in_br_conv)
  have LSt: "length St' = Suc M"
    using build_relD(3)[OF RELp[unfolded C BC]] MD by simp
  show "((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn' M)
         \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N) c ai
        \<turnstile> ((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn_x)
           \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N) c ai"
  proof -
    obtain qi Di where CI: "ai = (qi,Di)" by (cases ai)
    obtain ici bci where QI: "qi = (ici,bci)" by (cases qi)
    show ?thesis
      unfolding C BC CI QI prod_assn_def
      apply (simp only: prod.case)
      apply (intro conj_entails_mono entails_refl)
      by (simp add: built_mdp_assn_x_eq[OF LSt] entails_refl)
  qed
qed

lemma build_reindex_hnr_arg_x:
  assumes ENV: "interval_iteration_env N \<epsilon> ni \<epsilon>i"
  shows "(uncurry (build_statespace_ll' ni), uncurry op_build_reindex')
    \<in> [\<lambda>(M,x). Suc M < max_size_t \<and> (case x of (a,b) \<Rightarrow> reinterpret_pre (a,b) \<and> M = length b)]\<^sub>a
        size_assn\<^sup>k *\<^sub>a (Modest_mdp_sup_assn N \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N)\<^sup>d
      \<rightarrow> Modest_build_assn_x N"
  apply (rule hfref_cons_res[OF build_reindex_hnr_arg[OF ENV]])
  apply (clarsimp split: prod.splits)
  by (rule build'_to_build_x_ent)


section \<open>The two abstract facts the pipeline's preconditions need\<close>

text \<open>Both are lifted out of \<^locale>\<open>modest_collapse_invar\<close> and both are \<^emph>\<open>relative\<close> --- no
  machine-word bound in sight, as the hard rule in \<open>CLAUDE.md\<close> requires. \<open>length D \<le> N\<close> is what lets
  the sepref layer cash \<open>Suc M < max_size_t\<close> and \<open>2 * M < max_size_t\<close> from the locale's own \<open>n_impl\<close>;
  \<open>states \<dots> = {0..<length D}\<close> is the abstract handle @{thm [source] build_x_tie} consumes.\<close>

lemma to_index_states:
  assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
  shows "states (to_mdpc (op_to_index (op_reinterpret
             (modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr, D)))) = {0..<length D}"
  unfolding op_to_index_def op_reinterpret_def
  by (simp add: modest_collapse_invar.states_toindex[OF LOC])

lemma to_index_card:
  assumes LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
  shows "length D \<le> N"
proof -
  have "length D = card {0..<length D}" by simp
  also have "\<dots> = card (modest_collapse_invar.mec_of D ` {0..<N})"
    using modest_collapse_invar.mec_of_onto[OF LOC] by simp
  also have "\<dots> \<le> N"
    using card_image_le[where A = "{0..<N}" and f = "modest_collapse_invar.mec_of D"] by simp
  finally show ?thesis .
qed


section \<open>The builder at the richer view\<close>

text \<open>The same LLVM function, \<open>FCOMP\<close>'d against an abstract step that hands back what the concrete
  triple actually contains: the input state space, its MEC decomposition, and the re-indexed max
  reduction. Nothing about the emitted code changes --- the builder returns its own argument's two
  components unchanged, which is what makes the wider relation provable.\<close>

definition op_build_reindex_tp ::
  "(nat mdptc \<times> nat set list) \<Rightarrow> (nat mdptc \<times> nat set list \<times> nat mdptc) nres" where
  "op_build_reindex_tp x = do { r \<leftarrow> op_build_reindex x; Refine_Basic.RETURN (fst x, snd x, r) }"

definition op_build_reindex_t ::
  "nat \<Rightarrow> (nat mdptc \<times> nat set list) \<Rightarrow> (nat mdptc \<times> nat set list \<times> nat mdptc) nres" where
  "op_build_reindex_t M x = op_build_reindex_tp x"

sepref_register op_build_reindex_t

text \<open>As on the \<open>M\<close>-indexed path, the count has to sit \<^emph>\<open>in the relation\<close> for a result assertion to
  see it: the raw assertion the synthesis delivers is \<^const>\<open>built_mdp_assn\<close> at \<open>M\<close>, and weakening it
  to the \<open>M\<close>-free \<^const>\<open>built_mdp_assn_x\<close> needs \<open>length St' = Suc M\<close>.\<close>

definition "modest_build_rel_tM N M =
  {(c,t). (c,t) \<in> modest_build_rel_t N \<and> M = length (snd c)}"

lemma modest_build_rel_tM_sub: "modest_build_rel_tM N M \<subseteq> modest_build_rel_t N"
  unfolding modest_build_rel_tM_def by blast

definition "Modest_build_tM_assn N M =
  hr_comp ((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn M)
           \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N)
          (modest_build_rel_tM N M)"

lemma build_tM_to_build_t_ent:
  "Modest_build_tM_assn N M t ai \<turnstile> Modest_build_assn_t N t ai"
  unfolding Modest_build_tM_assn_def Modest_build_assn_t_def
proof (rule hr_comp_ent_mono2)
  fix c assume "(c,t) \<in> modest_build_rel_tM N M"
  thus "(c,t) \<in> modest_build_rel_t N" using modest_build_rel_tM_sub by blast
next
  fix c :: "(modest_input_mdp \<times> modest_input_mdp) \<times> nat set list"
  assume REL: "(c,t) \<in> modest_build_rel_tM N M"
  obtain ic bc D where C: "c = ((ic,bc),D)" by (cases c; cases "fst c") auto
  obtain St Tr Br Pr Av Ta where IC: "ic = (St,Tr,Br,Pr,Av,Ta)" by (cases ic)
  obtain St' Tr' Br' Pr' Av' Ta' where BC: "bc = (St',Tr',Br',Pr',Av',Ta')" by (cases bc)
  from REL have RT: "(c,t) \<in> modest_build_rel_t N" and MD: "M = length D"
    unfolding C modest_build_rel_tM_def by auto
  from modest_build_rel_tD(1)[OF RT] have RELp: "(c, snd (snd t)) \<in> modest_build_rel N" .
  from RELp have INV: "modest_build_invar N St Tr Br Pr Av Ta D St' Tr' Br' Pr' Av' Ta'"
    unfolding C IC BC modest_build_rel_def by (auto simp: in_br_conv)
  interpret B: modest_build_invar N St Tr Br Pr Av Ta D St' Tr' Br' Pr' Av' Ta' by (rule INV)
  have IIS: "modest_mdp_ii_invar_sup M St' Tr' Br' Pr' Av' Ta'"
    using INV MD by (simp add: modest_build_invar_def)
  have IN: "modest_mdp_input_invar M St' Tr' Br' Pr' Av' Ta'"
    using IIS by (simp add: modest_mdp_ii_invar_sup_def)
  have LSt: "length St' = Suc M"
    using build_relD(3)[OF RELp[unfolded C BC]] MD by simp
  show "((modest_init_mdp_env_defs.Modest_mdp_assn_aux N \<times>\<^sub>a built_mdp_assn M)
         \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N) c ai
        \<turnstile> build_raw_assn N c ai"
  proof -
    obtain qi Di where CI: "ai = (qi,Di)" by (cases ai)
    obtain ici bci where QI: "qi = (ici,bci)" by (cases qi)
    show ?thesis
      unfolding C IC BC CI QI
      apply (rule entails_pure_pre_extract[where
               P = "length Tr < max_size_t \<and> length Br < max_size_t"])
      subgoal by (auto dest: build_prod_boundsD)
      subgoal premises bnds
      proof -
        have TrM': "length Tr' < max_size_t" using B.Tr'_cap bnds by simp
        have BrM': "length Br' < max_size_t" using B.Br'_cap bnds by simp
        show ?thesis
          unfolding prod_assn_def
          apply (simp only: prod.case)
          apply (intro conj_entails_mono entails_refl)
          apply (rule entails_trans[OF built_to_built'_ent[OF IN TrM' BrM']])
          by (simp add: built_mdp_assn_x_eq[OF LSt] entails_refl)
      qed
      done
  qed
qed

context collapse_build_env
begin

  lemma build_reindex_correct_t:
    "(PR_CONST op_build_statespace_impl, op_build_reindex_tp)
     \<in> [\<lambda>x. reinterpret_pre x \<and> M = length (snd x)]\<^sub>f (modest_mdp_sup_rel N \<times>\<^sub>r Id)
       \<rightarrow> \<langle>modest_build_rel_tM N M\<rangle>nres_rel"
  proof (rule frefI)
    fix x y
    assume P: "reinterpret_pre y \<and> M = length (snd y)"
      and REL: "(x,y) \<in> modest_mdp_sup_rel N \<times>\<^sub>r Id"
    obtain MDP D where X: "x = (MDP,D)" by (cases x)
    have YEQ: "y = (\<M>_\<alpha>_sup' N MDP, D)"
      using REL unfolding X modest_mdp_sup_rel_def by (cases y) (auto simp: in_br_conv)
    have FY: "fst y = \<M>_\<alpha>_sup' N MDP" and SY: "snd y = D" unfolding YEQ by simp_all
    have BASE: "(PR_CONST op_build_statespace_impl x, op_build_reindex y)
                  \<in> \<langle>modest_build_M_rel N M\<rangle>nres_rel"
      using build_reindex_correct_M unfolding fref_def using P REL by blast
    have LE: "op_build_statespace_impl x
                \<le> \<Down> (modest_build_M_rel N M)
                     (Refine_Basic.RETURN (op_to_index (op_reinterpret y)))"
      using BASE unfolding PR_CONST_def op_build_reindex_def op_build_index_def
      by (simp add: nres_relD)
    have NF: "nofail (op_build_statespace_impl x)"
      using LE by (auto simp: pw_le_iff refine_pw_simps)
    have KEY: "(res, (fst y, snd y, op_to_index (op_reinterpret y))) \<in> modest_build_rel_tM N M"
      if IR: "inres (op_build_statespace_impl x) res" for res
    proof -
      obtain out where RES: "res = ((MDP,out),D)"
        using op_build_statespace_impl_shape[of MDP D res] IR NF unfolding X by auto
      have R1: "(res, op_to_index (op_reinterpret y)) \<in> modest_build_M_rel N M"
        using LE IR NF
        by (auto simp add: pw_le_iff refine_pw_simps simp del: split_paired_All)
      hence R2: "(res, op_to_index (op_reinterpret y)) \<in> modest_build_rel N"
        using modest_build_M_rel_sub by blast
      have MD: "M = length (snd res)" using R1 unfolding RES modest_build_M_rel_def
        by (auto simp: in_br_conv)
      show ?thesis
        unfolding modest_build_rel_tM_def
        using modest_build_rel_tI[OF R2] MD unfolding RES FY SY by simp
    qed
    show "(PR_CONST op_build_statespace_impl x, op_build_reindex_tp y)
            \<in> \<langle>modest_build_rel_tM N M\<rangle>nres_rel"
      unfolding PR_CONST_def op_build_reindex_tp_def op_build_reindex_def op_build_index_def
      apply (rule nres_relI)
      using NF KEY by (auto simp: pw_le_iff refine_pw_simps)
  qed

  context
    notes [fcomp_norm_unfold] = f_triple_aux Modest_mdp_sup_assn_def[symmetric]
      Modest_build_tM_assn_def[symmetric]
  begin
    lemmas build_reindex_hnr_tM = build_statespace_ll.refine[FCOMP build_reindex_correct_t]
  end

  lemmas build_reindex_hnr_t = hfref_cons_res[OF build_reindex_hnr_tM build_tM_to_build_t_ent]

end

text \<open>\<dots> and with the MEC count as an ordinary input parameter. The result assertion does not mention
  \<open>M\<close>, so the dependent arrow that @{thm [source] hfref_add_kept_pure_arg} produces collapses to a
  plain one.\<close>

lemma build_reindex_hnr_arg_t_d:
  assumes ENV: "interval_iteration_env N \<epsilon> ni \<epsilon>i"
  shows "(uncurry (build_statespace_ll' ni), uncurry op_build_reindex_t)
    \<in> [\<lambda>(M,x). Suc M < max_size_t \<and> (case x of (a,b) \<Rightarrow> reinterpret_pre (a,b) \<and> M = length b)]\<^sub>a
        size_assn\<^sup>k *\<^sub>a (Modest_mdp_sup_assn N \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N)\<^sup>d
      \<rightarrow>\<^sub>d (\<lambda>(M,_). Modest_build_assn_t N)"
  apply (rule hfref_add_kept_pure_arg[where R = snat_rel])
  subgoal premises p for v vi
  proof -
    have CBE: "collapse_build_env N \<epsilon> ni \<epsilon>i v vi"
      unfolding collapse_build_env_def collapse_build_env_axioms_def
      using ENV p by (auto simp: b_rel_def in_br_conv)
    show ?thesis
      unfolding op_build_reindex_t_def[abs_def]
      using collapse_build_env.build_reindex_hnr_t[OF CBE]
      unfolding build_statespace_ll'.refine[OF CBE]
      by simp
  qed
  done

lemma build_reindex_hnr_arg_t:
  assumes ENV: "interval_iteration_env N \<epsilon> ni \<epsilon>i"
  shows "(uncurry (build_statespace_ll' ni), uncurry op_build_reindex_t)
    \<in> [\<lambda>(M,x). Suc M < max_size_t \<and> (case x of (a,b) \<Rightarrow> reinterpret_pre (a,b) \<and> M = length b)]\<^sub>a
        size_assn\<^sup>k *\<^sub>a (Modest_mdp_sup_assn N \<times>\<^sub>a disj_set_list_tuple_defs.mec_map_assn N N)\<^sup>d
      \<rightarrow> Modest_build_assn_t N"
proof -
  have D: "(\<lambda>(M::nat,_::nat mdptc \<times> nat set list). Modest_build_assn_t N)
             = (\<lambda>_. Modest_build_assn_t N)" by auto
  show ?thesis using build_reindex_hnr_arg_t_d[OF ENV] unfolding D .
qed

end
