theory Interval_Iteration_Max_Code
  imports "../ds/Impl/Modest_MDP_II_Maxred_Impl"
begin

text \<open>LLVM code for MAXIMAL reach-avoid probabilities via interval iteration (Gauss-Seidel),
  \<^emph>\<open>without\<close> the MEC max-reduction — i.e. interval iteration run directly on the input Modest MDP in
  the \<open>Sup\<close> mode. This mirrors the interval-iteration part of the min-side
  \<^file>\<open>Interval_Iteration_Tool_GS_Minred_Code.thy\<close> (drop the reduction, keep the loop), using the Sup
  Bellman-sweep \<^const>\<open>interval_iteration_sup_env_defs.mop_state_vals_gs_sup\<close> (\<open>mop_state_vals_gs_hnr\<close>).\<close>

  section \<open>Interval Iteration Gauss-Seidel (Sup)\<close>

  text \<open>The convergence flag is left abstractly nondeterministic; the LLVM implements it with the
    \<open>\<epsilon>\<close>-stopping test.\<close>
  definition next_iter_max :: "nat mdptc \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> bool nres" where
    "next_iter_max M x y = SPEC (\<lambda>_. True)"

  context modest_mdp_ii_sup_def
  begin
    definition "next_iter_impl' \<epsilon> MDP xs ys = do{
      ASSERT((\<forall>u < N. xs ! u \<le> ys ! u) \<and> N > 0 \<and> length xs = N \<and> length ys = N);
      mop_leq_cmplt_nn \<epsilon> (op_sub_ub (ys ! 0) (xs ! 0))
    }"
  end

  context modest_mdp_ii_invar_sup
  begin
    lemma next_iter'_refine:
      assumes XSX: "(xs,x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes YSY: "(ys,y) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes XY: "\<forall>u \<in> states M\<^sub>0_\<alpha>. x u \<le> y u"
      shows "next_iter_impl' \<epsilon> (St, Tr, Br, Pr, Av, Ta) xs ys \<le> next_iter_max \<M>_\<alpha> x y"
    proof -
      have AUX: "u < N \<Longrightarrow> x u \<le> y u" for u
        using XY AT by(auto simp: states_M\<^sub>0_\<alpha>)
      from XSX YSY have [simp]: "length xs = N" "length ys = N"
        using list_fun_relD1 by blast+
      show ?thesis
        using N0 XSX YSY
        unfolding next_iter_impl'_def next_iter_max_def mop_leq_cmplt_nn_def
        apply refine_vcg
        by (auto simp: br_id_list_fun_rel dest!: list_fun_relD2 intro: AUX)
    qed
  end

  context interval_iteration_sup_env_defs
  begin

    definition next_iter_impl :: "modest_mdp \<Rightarrow> real list \<Rightarrow> real list \<Rightarrow> bool nres" where
      "next_iter_impl MDP xs ys = do{
        ASSERT((\<forall>u < N. xs ! u \<le> ys ! u) \<and> N > 0 \<and> length xs = N \<and> length ys = N);
        mop_leq_cmplt_nn \<epsilon> (op_sub_ub (ys ! 0) (xs ! 0))
      }"
    sepref_register next_iter_impl

    lemma next_iter_impl_alt: "next_iter_impl MDP xs ys = modest_mdp_ii_sup_def.next_iter_impl' N \<epsilon> MDP xs ys"
      unfolding next_iter_impl_def modest_mdp_ii_sup_def.next_iter_impl'_def ..

    definition "ii_max_impl = (\<lambda>\<M> L. do{
      x \<leftarrow> mop_init_lb \<M>;
      y \<leftarrow> mop_init_ub \<M>;
      (x,y,i,flag) \<leftarrow> WHILET (\<lambda> (x,y,i,flag). i < L \<and> flag) (\<lambda> (x,y,i,flag). do {
        ASSERT (\<forall>u \<in> states (to_mdpc \<M>). (x u \<ge> 0 \<and> y u \<ge> 0 \<and> x u \<le> 1 \<and> y u \<le> 1));
        (x,y) \<leftarrow> mop_state_vals_gs_sup \<M> x y;
        ASSERT (\<forall>u \<in> states (to_mdpc \<M>). x u \<le> y u);
        flag \<leftarrow> next_iter_max \<M> x y;
        ASSERT(Suc i \<le> L);
        RETURN (x,y,Suc i,flag)
      }) (x,y,0,True);
      RETURN (x,y,i)
    })"
    sepref_register ii_max_impl

    definition "next_iter_pre = (\<lambda> ((\<M>,x),y). \<forall>u \<in> states (to_mdpc \<M>). x u \<le> y u)"

    lemma next_iter_refine:
      assumes REL: "(DS, \<M>) \<in> modest_mdp_sup_rel N"
      assumes XSX: "(xs,x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes YSY: "(ys,y) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes XY: "\<forall>u \<in> states (to_mdpc \<M>). x u \<le> y u"
      shows "next_iter_impl DS xs ys \<le> next_iter_max \<M> x y"
    proof -
      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)" by (cases DS) blast
      from REL have INV: "modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta"
        unfolding modest_mdp_sup_rel_def by(auto simp: DDEF in_br_conv)
      from INV interpret modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta .
      from REL have [simp]: "to_mdpc \<M> = M\<^sub>0_\<alpha>" "\<M> = \<M>_\<alpha>"
        unfolding DDEF modest_mdp_sup_rel_def by(auto simp: in_br_conv)
      show ?thesis
        unfolding next_iter_impl_alt
        using assms by(auto simp: DDEF states_M\<^sub>0_\<alpha> intro!: next_iter'_refine)
    qed

    lemma next_iter_correct: "(uncurry2 next_iter_impl, uncurry2 next_iter_max) \<in> [next_iter_pre]\<^sub>f
      (modest_mdp_sup_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
      unfolding next_iter_pre_def
      apply(rule frefI)
      apply(refine_vcg)
      by(auto intro!: next_iter_refine)

  end

  section \<open>The code locale: interval iteration correctness\<close>

  locale interval_iteration_sup_code = MDPC_Reach_Avoid_Sup \<M> for \<M>::"nat mdptc" +
    fixes N::nat and ni::"64 Word.word" and \<epsilon>::real and \<epsilon>i::double
    assumes n_impl: "(ni,N) \<in> b_rel size_rel (\<lambda>i. 2 * i < max_size_t)"
    assumes \<epsilon>_impl: "(\<epsilon>i,\<epsilon>) \<in> nn_real_lb_double_rel"
    assumes states_M: "states (to_mdpc \<M>) = {0..<N}"
  begin

    sublocale interval_iteration_sup_env
      where N=N and ni=ni
      apply(unfold_locales)
      subgoal using n_impl .
      subgoal using \<epsilon>_impl .
      done

    lemma ii_max_impl_correct:
      shows "ii_max_impl \<M> L \<le> mop_interval_iteration_sup \<M> L"
    proof -
      have "ii_max_impl \<M> L = mop_interval_iteration_gs L"
        unfolding ii_max_impl_def mop_interval_iteration_gs_def mop_state_vals_gs_sup_def next_iter_max_def
        by blast
      also note mop_interval_iteration_gs_correct
      also have "interval_iteration_pspec = mop_interval_iteration_sup \<M> L"
        unfolding mop_interval_iteration_sup_def by presburger
      finally show ?thesis .
    qed

  end


  section \<open>LLVM synthesis of the loop\<close>

  context interval_iteration_sup_env
  begin

    sepref_definition next_iter_impl_ll is "uncurry2 next_iter_impl"
      :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a lb_reach_assn\<^sup>k *\<^sub>a ub_reach_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding next_iter_impl_def
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
    concrete_definition(in -) next_iter_impl_max_ll' [llvm_code] is interval_iteration_sup_env.next_iter_impl_ll_def

    context
      notes [fcomp_norm_unfold] = f_triple_aux Modest_mdp_sup_assn_def[symmetric]
        output_ub_assn_alt[symmetric] output_lb_assn_alt[symmetric]
    begin
      lemmas next_iter_impl_ll_hnr' = next_iter_impl_ll.refine[FCOMP next_iter_correct]
      lemmas next_iter_impl_ll_hnr [sepref_fr_rules] =
        next_iter_impl_ll_hnr'[unfolded next_iter_impl_max_ll'.refine[OF interval_iteration_sup_env_axioms]]
    end

    sepref_definition ii_max_impl_ll is "uncurry ii_max_impl"
      :: "(Modest_mdp_sup_assn N)\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn)"
      unfolding ii_max_impl_def PR_CONST_def
      supply[iff del] = length_greater_0_conv
      supply[simp] = upd_state_val_pre_def next_iter_pre_def
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
    concrete_definition(in -) ii_max_impl_ll' [llvm_code] is interval_iteration_sup_env.ii_max_impl_ll_def
    lemmas ii_max_impl_hnr_raw[sepref_fr_rules] =
      ii_max_impl_ll.refine[unfolded ii_max_impl_ll'.refine[OF interval_iteration_sup_env_axioms]]

  end

  definition Modest_compute_ii_max_ll ::
    "size_t \<Rightarrow> size_t \<Rightarrow> double \<Rightarrow> modest_mdpi ptr \<Rightarrow> (double ptr \<times> double ptr \<times> size_t) ptr \<Rightarrow> unit llM"
  where [llvm_code, llvm_inline]: "Modest_compute_ii_max_ll Li ni \<epsilon>i Mip resp \<equiv> doM {
    Mi \<leftarrow> ll_load Mip;
    res \<leftarrow> ii_max_impl_ll' ni \<epsilon>i Mi Li;
    ll_store res resp
  }"

  export_llvm Modest_compute_ii_max_ll
    is "void compute_II_max(modest_size_t, modest_size_t, modest_dec_t, modest_mdp_t *, modest_ii_vals_t *)"
  defines \<open>
    typedef double modest_dec_t;
    typedef int64_t modest_size_t;
    typedef modest_size_t node_t;

    typedef struct {
      modest_dec_t lb;
      modest_dec_t ub;
    } modest_interval_t;

    typedef struct {
      node_t *states;
      struct {
        node_t *transitions;
        struct {
          node_t *branches;
          struct {
            modest_interval_t *probabilities;
            struct {
              modest_size_t *avoid;
              modest_size_t *target;
            };
          };
        };
      };
    } modest_mdp_t;

    typedef struct {
      modest_dec_t *lbs;
      struct{
        modest_dec_t *ubs;
        modest_size_t iterations;
      };
    } modest_ii_vals_t;
  \<close>
    file "modest_ii_max_gs.ll"

end
