theory Modest_MDP_II_Ops
  imports "II_Modest_Base.More_B_Assn" "II_Modest_Base.Nat_Interval" "../../II/II_Def" "../../mec/MaxEndComponent"
begin

  text \<open>This theory contains all of the abstract operations necessary for min-reduction and interval
    iteration. This theory acts as an interface between the refinement of the algorithm and the
    refinement of the data structure. For modularity purposes, these refinements are separated.\<close>

  section \<open>General Theory\<close>

  lemma Squnion_dom_eqI: "(\<And>x. x \<in> X \<Longrightarrow> f x = g x) \<Longrightarrow> (\<Squnion>x\<in>X. f x) = (\<Squnion>x\<in>X. g x)"
    by auto

  lemma Sqinter_dom_eqI: "(\<And>x. x \<in> X \<Longrightarrow> f x = g x) \<Longrightarrow> (\<Sqinter>x\<in>X. f x) = (\<Sqinter>x\<in>X. g x)"
    by auto

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

  lemma less_minus_Suc_zero: "i < j - Suc 0 \<longleftrightarrow> Suc i < j"
    by linarith

  lemma Min_le_ub:
    assumes "finite A" and "(\<And>x. x \<in> A \<Longrightarrow> x \<le> y)" and "A \<noteq> {}"
    shows "Min A \<le> y"
    by (simp add: assms)

  lemma forall_ex_conc_fun_univ: "(\<And> x. \<exists>y. (x,y) \<in> R) \<Longrightarrow> \<Down> R (RES UNIV) = RES UNIV"
    by (metis UNIV_I UNIV_eq_I conc_fun_RES inres_simps(2) pw_conc_inres)

  lemma conc_fun_univ_eq: "\<Down> R (RES UNIV) = RES UNIV \<longleftrightarrow> (\<forall> x. \<exists>y. (x,y) \<in> R)"
    by (metis UNIV_I inres_simps(2) nofail_simps(2) pw_conc_inres forall_ex_conc_fun_univ)

  lemma forall_ex_conc_fun_univ_Domain: "(\<And> x. x \<in> Domain R \<Longrightarrow> \<exists>y. (x,y) \<in> R) \<Longrightarrow> RES (Domain R) \<le> \<Down> R (RES UNIV)"
    by (simp add: RES_refine)

  lemma sum_in_sum_over_contr: "finite X \<Longrightarrow> (\<And> x. finite {y. P x y \<and> x = g y}) \<Longrightarrow> (\<Sum>x\<in>X. (\<Sum>y | P x y \<and> x = g y. f x y)) = (\<Sum>y | P (g y) y \<and> g y \<in> X. f (g y) y)"
    proof(induction X rule: finite_induct)
      case empty
      then show ?case by simp
    next
      case (insert x F)
      note IH = insert.IH[OF insert.prems]

      have "{y. P (g y) y \<and> g y \<in> F} \<subseteq> (\<Union>x\<in>F. {y. P x y \<and> x = g y})"
        by blast
      hence "finite {y. P (g y) y \<and> g y \<in> F}"
        using insert.hyps(1) insert.prems finite_subset by blast

      moreover have "finite {y. P x y \<and> x = g y}"
        using insert.prems by simp

      moreover have C: "{y. P (g y) y \<and> g y \<in> F} \<union> {y. P x y \<and> x = g y} = {y. P (g y) y \<and> g y \<in> insert x F}"
        by blast
      ultimately have D: "finite {y. P (g y) y \<and> g y \<in> insert x F}"
        by (metis (no_types, lifting) finite_UnI)
      have "(\<Sum>x\<in>insert x F. sum (f x) {y. P x y \<and> x = g y}) = (\<Sum>x\<in>F. sum (f x) {y. P x y \<and> x = g y}) + sum (f x) {y. P x y \<and> x = g y}"
        by (simp add: cross3_simps(8) insert.hyps(1) insert.hyps(2))
      also have "... = sum (\<lambda>y. f (g y) y) {y. P (g y) y \<and> g y \<in> F} + sum (\<lambda>y. f (g y) y) {y. P x y \<and> x = g y}"
        using IH by auto
      also have "... = (\<Sum>y | P (g y) y \<and> g y \<in> insert x F. f (g y) y)"
        using local.insert(2) sum_Un_eq[OF _ C D] by blast
      finally show ?case by blast
    qed

  
  section \<open>Optimization mode for reachability\<close>

  locale reachability_opt_mode_defs = 
    fixes Opt::"real set \<Rightarrow> real" \<comment> \<open>Optimal value in a set\<close>
    and opt::"real \<Rightarrow> real \<Rightarrow> real" \<comment> \<open>Optimal value out of two\<close>
    and nw::"real \<Rightarrow> real \<Rightarrow> bool" \<comment> \<open>Not-worse relation\<close>
    and vopt::"real" \<comment> \<open>Optimal value\<close>
    and vsub::"real" \<comment> \<open>Anti-optimal value\<close>
  begin


    definition "in_vDom x \<equiv> nw x vsub \<and> nw vopt x"

    definition "sub_vDom A \<equiv> \<forall>x \<in> A. in_vDom x"

    definition "vDom = Collect in_vDom"

    lemma in_vDom_alt: "in_vDom x \<longleftrightarrow> x \<in> vDom"
      unfolding vDom_def by blast

    lemma in_vDomI: "nw vopt x \<Longrightarrow> nw x vsub \<Longrightarrow> in_vDom x"
      unfolding in_vDom_def by presburger

    lemma sub_vDom_alt: "sub_vDom A \<longleftrightarrow> A \<subseteq> vDom"
      unfolding vDom_def sub_vDom_def by blast

    lemma sub_vDom_empty[simp]: "sub_vDom {}"
      unfolding sub_vDom_def by blast

    lemma sub_vDom_insert[intro!]: "sub_vDom A \<Longrightarrow> in_vDom x \<Longrightarrow> sub_vDom (insert x A)"
      unfolding sub_vDom_def by auto

    lemma sub_vDom_union: "sub_vDom A \<Longrightarrow> sub_vDom B \<Longrightarrow> sub_vDom (A \<union> B)"
      unfolding sub_vDom_def by blast

    lemma sub_vDom_inter: "sub_vDom A \<Longrightarrow> sub_vDom B \<Longrightarrow> sub_vDom (A \<inter> B)"
      unfolding sub_vDom_def by blast

    lemma sub_vDom_mono: "A \<subseteq> B \<Longrightarrow> sub_vDom B \<Longrightarrow> sub_vDom A"
      unfolding sub_vDom_def by blast

    
  end


  locale reachability_opt_mode = reachability_opt_mode_defs +
    assumes refl[iff]: "nw x x"
    assumes trans: "nw x y \<Longrightarrow> nw y z \<Longrightarrow> nw x z"
    assumes antisym: "nw x y \<Longrightarrow> nw y x \<Longrightarrow> x = y"
    assumes linear: "nw x y \<or> nw y x"
    assumes opt_nw1: "in_vDom x \<Longrightarrow> in_vDom y \<Longrightarrow> nw (opt x y) x"
    assumes opt_nw2: "in_vDom x \<Longrightarrow> in_vDom y \<Longrightarrow> nw (opt x y) y"
    assumes nw_opt: "in_vDom x \<Longrightarrow> in_vDom y \<Longrightarrow> in_vDom z \<Longrightarrow> nw x y \<Longrightarrow> nw x z \<Longrightarrow> nw x (opt y z)"
    assumes Opt_nw: "sub_vDom A \<Longrightarrow> x \<in> A \<Longrightarrow> nw (Opt A) x"
    assumes nw_Opt: "in_vDom z \<Longrightarrow> sub_vDom A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> nw z x) \<Longrightarrow> nw z (Opt A)"
    assumes Opt_vDom: "sub_vDom A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> in_vDom (Opt A)"
    assumes opt_vDom: "in_vDom x \<Longrightarrow> in_vDom y \<Longrightarrow> in_vDom (opt x y)"
    assumes vopt_nw: "in_vDom x \<Longrightarrow> nw vopt x"
    assumes nw_vsub: "in_vDom x \<Longrightarrow> nw x vsub"
    assumes vopt_nw_vsub[simp,intro!]: "nw vopt vsub"
  begin

    lemmas opt_intros = opt_nw1 opt_nw2 vopt_nw nw_vsub

    lemma in_vDom_vopt[simp,intro!]: "in_vDom vopt"
      unfolding in_vDom_def by blast

    lemma in_vDom_vsub[simp,intro!]: "in_vDom vsub"
      unfolding in_vDom_def by blast

    lemma opt_vopt1[simp]: "in_vDom x \<Longrightarrow> opt vopt x = vopt"
      by (simp add: antisym opt_nw1 opt_vDom vopt_nw)

    lemma opt_vopt2[simp]: "in_vDom x \<Longrightarrow> opt x vopt = vopt"
      by (simp add: antisym opt_nw2 opt_vDom vopt_nw)


    lemma opt_vsub1[simp]: "in_vDom x \<Longrightarrow> opt vsub x = x"
      by (simp add: antisym nw_opt nw_vsub opt_nw2)

    lemma opt_vsub2[simp]: "in_vDom x \<Longrightarrow> opt x vsub = x"
      by (simp add: antisym nw_opt nw_vsub opt_nw1)  

    lemma nw_optI1: "in_vDom a \<Longrightarrow> in_vDom b \<Longrightarrow> nw a x \<Longrightarrow> nw (opt a b) x"
      by (rule trans) (auto intro: opt_intros)

    lemma nw_optI2: "in_vDom a \<Longrightarrow> in_vDom b \<Longrightarrow> nw b x \<Longrightarrow> nw (opt a b) x"
      by (rule trans) (auto intro: opt_intros)

    lemma Opt_mono: "A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> sub_vDom B \<Longrightarrow> nw (Opt B) (Opt A)"
      by(auto intro!: nw_Opt Opt_vDom intro: Opt_nw elim: sub_vDom_mono)

    lemma opt_comm: "in_vDom a \<Longrightarrow> in_vDom b \<Longrightarrow> opt a b = opt b a"
      by (simp add: antisym nw_opt opt_nw1 opt_nw2 opt_vDom)

    lemma Opt_insert1: "sub_vDom A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> in_vDom x \<Longrightarrow> Opt (insert x A) = opt (Opt A) x"
      by (auto intro: Opt_nw Opt_mono opt_vDom nw_optI1 opt_nw2 intro!: antisym nw_opt nw_Opt Opt_vDom)

    lemma Opt_insert2: "sub_vDom A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> in_vDom x \<Longrightarrow> Opt (insert x A) = opt x (Opt A)"
      by (auto simp: Opt_vDom Opt_insert1 opt_comm)

    lemma Opt_singleton[simp]: "in_vDom x \<Longrightarrow> Opt {x} = x"
      by(auto intro!: antisym Opt_nw nw_Opt)

    lemma opt_in[simp]: "sub_vDom A \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A  \<Longrightarrow> opt a b \<in> A"
      using linear[of a b] by (metis antisym refl nw_opt opt_nw1 opt_nw2 sub_vDom_def)

    lemma Opt_in: "finite A \<Longrightarrow> sub_vDom A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> Opt A \<in> A"
      unfolding sub_vDom_alt
      apply (induction A rule: finite_subset_induct')
      subgoal by simp
      subgoal for a F
        apply(cases "F = {}")
        subgoal by (simp add: in_vDom_alt Opt_singleton)
        subgoal
          apply(subst Opt_insert1)
          apply (auto simp flip: sub_vDom_alt in_vDom_alt)[3]
          apply(rule opt_in) 
          apply (auto simp: in_vDom_alt sub_vDom_def)
          done
        done
      done
  end

  context 
    notes [simp] = reachability_opt_mode_defs.sub_vDom_def reachability_opt_mode_defs.in_vDom_def
  begin 

    lemma reachability_opt_mode_inf: "reachability_opt_mode Inf inf (\<le>) 0 1"
      apply(unfold_locales) apply clarsimp_all
      subgoal for A x 
        by(rule bounded_has_Inf(1)[of A,THEN ballE[where?x=x]]) (auto simp: bounded_real)
      subgoal for z A
        by(rule bounded_has_Inf(2)[of A,THEN allE[where?x=z]]) (auto simp: bounded_real)
      subgoal
        by (meson bdd_belowI cInf_greatest cInf_lower2 set_notEmptyE)
      subgoal
        using le_infI1 by blast
     done
  
    lemma reachability_opt_mode_sup: "reachability_opt_mode Sup sup (\<ge>) 1 0"
      apply(unfold_locales) apply clarsimp_all
      subgoal for A x
        by(rule bounded_has_Sup(1)[of A,THEN ballE[where?x=x]]) (auto simp: bounded_real)
      subgoal for z A
        by(rule bounded_has_Sup(2)[of A,THEN allE[where?x=z]]) (auto simp: bounded_real)
      subgoal
        by (meson bdd_aboveI cSup_least cSup_upper dual_order.trans set_notEmptyE)
      subgoal
        using le_supI1 by blast
      done

  end

  section \<open>Operations\<close>

  subsection \<open>Abstract Operations\<close>

  definition op_is_avoid :: "'v mdptc \<Rightarrow> 'v \<Rightarrow> bool" where
    "op_is_avoid \<M> u \<longleftrightarrow> u \<in> avoids \<M>"

  definition op_is_target :: "'v mdptc \<Rightarrow> 'v \<Rightarrow> bool" where
    "op_is_target \<M> u \<longleftrightarrow> u \<in> targets \<M>"

  subsubsection \<open>Interval Iteration\<close>

  definition mop_init_ub :: "'v mdptc \<Rightarrow> ('v \<Rightarrow> real) nres" where
    "mop_init_ub \<M> =  SPEC (\<lambda> x. \<forall>u \<in> states \<M>. (if op_is_avoid \<M> u then x u = 0 else x u = 1))"

  definition mop_init_lb :: "'v mdptc \<Rightarrow> ('v \<Rightarrow> real) nres" where 
    "mop_init_lb \<M> =  SPEC (\<lambda> x. \<forall>u \<in> states \<M>. (if op_is_target \<M> u then x u = 1 else x u = 0))"

  definition "op_trans_val \<equiv> (\<lambda>\<M> x p. \<Sum> v \<in> states \<M>. x v * pmf p v)"

  subsubsection \<open>Reduction\<close>

  abbreviation "mec_decomp' \<equiv> Finite_MDP_defs.mec_decomp"

  definition op_is_trivial :: "'a mdptc \<Rightarrow> 'a set list \<Rightarrow> 'a \<Rightarrow> bool" where
    "op_is_trivial \<M> D u \<longleftrightarrow> (\<forall>a \<in> actions \<M> u. \<exists> v \<in> set_pmf a. (\<exists> i j. i < length D \<and> j < length D \<and> i \<noteq> j \<and> u \<in> D ! i \<and> v \<in> D ! j))"

  definition op_make_avd_sink :: "'v mdptc \<Rightarrow> 'v \<Rightarrow> 'v mdptc" where "op_make_avd_sink \<M> v = 
    Abs_mdptc (fix_loop v \<M>, insert v (avoids \<M>), targets \<M>)"

  definition op_compute_mecs :: "'a mdptc \<Rightarrow> 'a set list nres" where
    "op_compute_mecs = (\<lambda>\<M>. mec_algo_defs.compute_MEC_spec \<M>)"


  subsubsection \<open>Other\<close>

  definition(in reachability_opt_mode_defs) op_state_val :: "'a mdptc \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
    "op_state_val \<M> x u = (Opt {\<Sum> v \<in> states \<M>. x v * pmf p v | p. p \<in> actions \<M> u})"


  definition(in reachability_opt_mode_defs) 
  mop_state_vals_gs :: "'v mdptc \<Rightarrow> ('v \<Rightarrow> real) \<Rightarrow> ('v \<Rightarrow> real) \<Rightarrow> (('v \<Rightarrow> real) \<times> ('v \<Rightarrow> real)) nres" where
  "mop_state_vals_gs = (\<lambda> \<M> x y. do {
    (x,y) \<leftarrow> FOREACH (states (to_mdpc \<M>)) (\<lambda> u (x,y). do{ 
    ASSERT (\<forall>u \<in> states \<M>. (x u \<ge> 0 \<and> y u \<ge> 0 \<and> x u \<le> 1 \<and> y u \<le> 1));
    if op_is_avoid \<M> u then RETURN (x,y) 
    else 
      if op_is_target \<M> u then RETURN (x,y) 
      else do {
        ASSERT (u \<in> states \<M>);
        let xmin = op_state_val \<M> x u;
        let ymin = op_state_val \<M> y u;
        RETURN (x(u:=xmin),y(u:=ymin))
      }}) (x,y);
      RETURN (x,y)
    })"


  subsection \<open>\<close>

  context Finite_MDP
  begin 

    lemma integrable_K: "u \<in> states M \<Longrightarrow> p \<in> actions M u \<Longrightarrow> integrable (measure_pmf p) (x::_\<Rightarrow>real)"
      by (auto simp: actions'_def set_pmf_finite intro!: integrable_measure_pmf_finite)
  
    lemma AE_pmf_leq_1: "u \<in> states M \<Longrightarrow> p \<in> actions M u \<Longrightarrow> (\<And>v. v \<in> states M \<Longrightarrow> x v \<le> 1) \<Longrightarrow> AE xa in measure_pmf p. x xa \<le> 1"
      apply(rule AE_pmfI) 
      by (simp add: closed_M closed_mdpcD)
  
    lemma AE_pmf_geq_0: "u \<in> states M \<Longrightarrow> p \<in> actions M u \<Longrightarrow> (\<And>v. v \<in> states M \<Longrightarrow> 0 \<le> x v) \<Longrightarrow> AE xa in measure_pmf p. x xa \<ge> 0"
      apply(rule AE_pmfI) 
      by (simp add: closed_M closed_mdpcD)
  
    lemma pmf_expectation_le_one: "u \<in> states M \<Longrightarrow> p \<in> actions M u \<Longrightarrow> (\<And>v. v \<in> states M \<Longrightarrow> x v \<le> (1::real)) \<Longrightarrow> measure_pmf.expectation p x \<le> 1"
      by(auto intro!: measure_pmf.integral_le_const integrable_K AE_pmf_leq_1)
  
    lemma pmf_expectation_ge_zero: "u \<in> states M \<Longrightarrow> p \<in> actions M u \<Longrightarrow> (\<And>v. v \<in> states M \<Longrightarrow> (0::real) \<le> x v) \<Longrightarrow> measure_pmf.expectation p x \<ge> 0"
      by(auto intro!: measure_pmf.integral_ge_const integrable_K AE_pmf_geq_0)

  end

  context MDPC_Reach_Avoid
  begin

    lemma expectation_trans_val: "u \<in> states \<M> \<Longrightarrow> p \<in> actions \<M> u \<Longrightarrow> measure_pmf.expectation p x = op_trans_val \<M> x p"
      by(auto simp: closed_M closed_mdpcD op_trans_val_def intro!: integral_measure_pmf_real )

    corollary op_trans_val_le_one: "u \<in> states \<M> \<Longrightarrow> p \<in> actions \<M> u \<Longrightarrow> (\<And>v. v \<in> states \<M> \<Longrightarrow> x v \<le> (1::real)) \<Longrightarrow> op_trans_val \<M> x p \<le> 1"
      using expectation_trans_val pmf_expectation_le_one by metis
  
    corollary op_trans_val_ge_zero: "u \<in> states \<M> \<Longrightarrow> p \<in> actions \<M> u \<Longrightarrow> (\<And>v. v \<in> states \<M> \<Longrightarrow> (0::real) \<le> x v) \<Longrightarrow> 0 \<le> op_trans_val \<M> x p"
      using expectation_trans_val pmf_expectation_ge_zero by metis

  end

  locale MDPC_Reach_Avoid_Prob = MDPC_Reach_Avoid + reachability_opt_mode +
    assumes vDom_alt: "vDom = {0..1}"
  begin

    lemma in_vDom_01: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> in_vDom x"
      using in_vDom_alt vDom_alt by presburger
 
    lemma sub_vDom_op_trans_val:  "u \<in> states \<M> \<Longrightarrow> (\<And>v. v \<in> states \<M> \<Longrightarrow> in_vDom (x v)) \<Longrightarrow> sub_vDom {op_trans_val \<M> x p |p. p \<in> actions \<M> u}"
      unfolding sub_vDom_alt vDom_alt
      by (auto intro!: op_trans_val_ge_zero[of u] op_trans_val_le_one[of u]  simp: in_vDom_alt vDom_alt)

    lemma in_vDom_op_trans_val:  "u \<in> states \<M> \<Longrightarrow> (\<And>v. v \<in> states \<M> \<Longrightarrow> in_vDom (x v)) \<Longrightarrow> p \<in> actions \<M> u \<Longrightarrow> in_vDom (op_trans_val \<M> x p)"
      unfolding sub_vDom_alt vDom_alt
      by (auto intro!: op_trans_val_ge_zero[of u] op_trans_val_le_one[of u]  simp: in_vDom_alt vDom_alt)

    lemma op_state_val_in_vDom:
      "u \<in> states \<M> \<Longrightarrow> (\<And>v. v \<in> states \<M> \<Longrightarrow> in_vDom (x v)) \<Longrightarrow> in_vDom (op_state_val \<M> x u)"
      unfolding op_state_val_def
      by (auto intro!: sub_vDom_op_trans_val[unfolded op_trans_val_def, simplified] Opt_vDom 
        simp: actions_neq_empty_M) 

  end


  section \<open>Interval Iteration\<close>


  locale MDPC_Reach_Avoid_opt = MDPC_Reach_Avoid + reachability_opt_mode (*TODO does this even make sense still?*)
  begin  
  
    subsection \<open>Specification\<close>
  
    definition(in MDPC_Reach_Avoid) "iin_gs_it_spec = SPEC (\<lambda> (x', y'). \<forall> u \<in> states \<M>. x' u \<le> n_real u \<and> n_real u \<le> y' u \<and> x' u \<ge> 0 \<and> y' u \<le> 1)"
  
    definition(in MDPC_Reach_Avoid) "iip_gs_it_spec = SPEC (\<lambda> (x', y'). \<forall> u \<in> states \<M>. x' u \<le> p_real u \<and> p_real u \<le> y' u \<and> x' u \<ge> 0 \<and> y' u \<le> 1)"
  
  
    subsection \<open>Algorithm\<close>
  
    definition(in MDPC_Reach_Avoid) "mop_state_vals_gs_ninvar 
      = (\<lambda> it (x', y'). \<forall> u \<in> states \<M>. x' u \<le> n_real u \<and> n_real u \<le> y' u \<and> x' u \<ge> 0 \<and> y' u \<le> 1)"

    definition(in MDPC_Reach_Avoid) "mop_state_vals_gs_pinvar 
      = (\<lambda> it (x', y'). \<forall> u \<in> states \<M>. x' u \<le> p_real u \<and> p_real u \<le> y' u \<and> x' u \<ge> 0 \<and> y' u \<le> 1)"
  end


  context MDPC_Reach_Avoid
  begin

    corollary op_trans_val_le_one_\<M>: "u \<in> states \<M> \<Longrightarrow> a \<in> actions \<M> u \<Longrightarrow> (\<And>v. v \<in> states \<M> \<Longrightarrow> x v \<le> (1::real)) \<Longrightarrow> op_trans_val \<M> x a \<le> 1"
      by(auto intro: op_trans_val_le_one)

    corollary op_trans_val_ge_zero_\<M>: "u \<in> states \<M> \<Longrightarrow> a \<in> actions \<M> u \<Longrightarrow> (\<And>v. v \<in> states \<M> \<Longrightarrow> (0::real) \<le> x v) \<Longrightarrow> 0 \<le> op_trans_val \<M> x a"
      by(auto intro: op_trans_val_ge_zero)
    
    lemma F_inf_real_op_state_val_True: 
      assumes "op_is_target \<M> u"
      shows "R.F_inf_real f u = 1"
      using assms
      unfolding op_is_target_def 
      by (simp add: R.F_inf_def R.F_inf_real_def)
    
    lemma F_inf_real_op_state_val_False: 
      assumes "op_is_avoid \<M> u"
      shows "R.F_inf_real f u = 0"
      using assms AT_disj
      unfolding op_is_avoid_def 
      by (auto simp add: R.F_inf_def R.F_inf_real_def)

    
    lemma F_sup_real_op_state_val_True: 
      assumes "op_is_target \<M> u"
      shows "R.F_sup_real f u = 1"
      using assms
      unfolding op_is_target_def
      by (simp add: R.F_sup_def R.F_sup_real_def)
    
    lemma F_sup_real_op_state_val_False: 
      assumes "op_is_avoid \<M> u"
      shows "R.F_sup_real f u = 0"
      using assms AT_disj
      unfolding op_is_avoid_def
      by (auto simp add: R.F_sup_def R.F_sup_real_def)

  end


  locale MDPC_Reach_Avoid_Sup = MDPC_Reach_Avoid
  begin

    lemma MDPC_Reach_Avoid_opt_sup: "MDPC_Reach_Avoid_opt \<M> Sup sup (\<ge>) 1 0"
      unfolding MDPC_Reach_Avoid_opt_def using reachability_opt_mode_sup MDPC_Reach_Avoid_axioms by auto

    sublocale MDPC_Reach_Avoid_opt \<M> Sup sup "(\<ge>)" 1 0
      using MDPC_Reach_Avoid_opt_sup .

    lemma vDom_alt: "vDom = {0..1}"
      by (auto simp: vDom_def in_vDom_def)

    sublocale MDPC_Reach_Avoid_Prob \<M> Sup sup "(\<ge>)" 1 0
      apply(unfold_locales)
      by (auto simp add: vDom_alt)

    lemma in_vDom_01[simp]: "in_vDom x \<longleftrightarrow> x \<in> {0..1}"
      by(simp flip: vDom_alt in_vDom_alt) 

    lemma op_state_val_in_bound:
      assumes "u \<in> states \<M> "
      and "(\<And>v. v \<in> states \<M> \<Longrightarrow> 0 \<le> x v)"
      and "(\<And>v. v \<in> states \<M> \<Longrightarrow> x v \<le> 1)"
      shows "0 \<le> op_state_val \<M> x u" and "op_state_val \<M> x u \<le> 1"
      using op_state_val_in_vDom assms 
      by(simp_all add: in_vDom_01)


    lemma F_sup_real_op_state_val: 
      assumes "u \<in> states \<M>" 
      assumes "\<not> op_is_avoid \<M> u"
      assumes "\<not> op_is_target \<M> u"
      assumes LE1: \<open>\<And>u. u \<in> states \<M> \<Longrightarrow> f u \<le> 1\<close>
      assumes GE0: \<open>\<And>u. u \<in> states \<M> \<Longrightarrow> f u \<ge> 0\<close>
      shows "R.F_sup_real f u = op_state_val \<M> f u"
      apply (subst R.F_sup_real)
      subgoal using GE0 by presburger
      subgoal using LE1 by presburger
      unfolding op_state_val_def
      using assms actions_finite'
      by (auto dest: computesI intro!: Squnion_dom_eqI
        simp: op_is_target_def op_is_avoid_def op_trans_val_def expectation_trans_val Setcompr_eq_image actions'_states )

    lemma p_le_op_state_val: 
      assumes "u \<in> states \<M>" 
      assumes "\<not> op_is_avoid \<M> u"
      assumes "\<not> op_is_target \<M> u"
      assumes "(\<And>u. u \<in> states \<M> \<Longrightarrow> x u \<le> 1)"
      assumes "(\<And>u. u \<in> states \<M> \<Longrightarrow> 0 \<le> x u)"
      assumes "(\<And>t. t \<in> states \<M> \<Longrightarrow> p_real t \<le> x t)"
      shows "p_real u \<le> op_state_val \<M> x u"
      apply(rule order_trans[OF  F_sup_ge_iter'_state[OF _ assms(1)], of x])
      using F_sup_real_op_state_val[OF assms(1-3)] assms(4-6) by auto
      

    lemma p_ge_op_state_val: 
      assumes "u \<in> states \<M>" 
      assumes "\<not> op_is_avoid \<M> u"
      assumes "\<not> op_is_target \<M> u"
      assumes "(\<And>u. u \<in> states \<M> \<Longrightarrow> x u \<le> 1)"
      assumes "(\<And>u. u \<in> states \<M> \<Longrightarrow> 0 \<le> x u)"
      assumes "(\<And>t. t \<in> states \<M> \<Longrightarrow> x t \<le> p_real t)"
      shows "p_real u \<ge> op_state_val \<M> x u"
      apply(rule order_trans[OF _ F_sup_le_iter'_state[OF _ assms(1)], of _ x])
      using F_sup_real_op_state_val[OF assms(1-3)] assms(4-6) by auto

    lemma le_op_state_val:
      assumes US: "u \<in> states \<M>"
      assumes XY: \<open>\<And>u. u \<in> states \<M> \<Longrightarrow> x u \<le> y u\<close>
      shows "op_state_val \<M> x u \<le> op_state_val \<M> y u"
      unfolding op_state_val_def Setcompr_eq_image 
      using finite_actions_M 
      by(auto simp: assms actions_neq_empty_M landau_o.R_mult_right_mono sum_mono 
        intro!: cSUP_subset_mono)

    lemma lb_0_val: "u \<in> states \<M> \<Longrightarrow> R.lb_0 u = (if op_is_target \<M> u then 1 else 0)"
      unfolding R.lb_0_def op_is_target_def
      by auto
  
    lemma ub_0_val: "u \<in> states \<M> \<Longrightarrow> R.ub_0 u = (if op_is_avoid \<M> u then 0 else 1)"
      unfolding R.ub_0_def op_is_avoid_def
      using AT_disj
      by (auto dest: computesI) 

    lemma mop_state_vals_gs_correct:
      assumes "\<forall> u \<in> states \<M>. x u \<le> p_real u \<and> p_real u \<le> y u \<and> x u \<ge> 0 \<and> y u \<le> 1"
      shows "mop_state_vals_gs \<M> x y \<le> iip_gs_it_spec"
      unfolding mop_state_vals_gs_def iip_gs_it_spec_def 
      apply(refine_vcg FOREACH_rule[where ?I=mop_state_vals_gs_pinvar])
      subgoal by blast
      subgoal using assms unfolding mop_state_vals_gs_pinvar_def by auto
      subgoal unfolding mop_state_vals_gs_pinvar_def by force
      subgoal unfolding mop_state_vals_gs_pinvar_def by fastforce
      subgoal unfolding mop_state_vals_gs_pinvar_def by fastforce
      subgoal unfolding mop_state_vals_gs_pinvar_def by fastforce
      subgoal
        unfolding mop_state_vals_gs_pinvar_def 
        using p_ge_op_state_val p_le_op_state_val op_state_val_in_bound 
        by simp
      subgoal unfolding mop_state_vals_gs_pinvar_def by fastforce
      done

  end

  locale MDPC_Reach_Avoid_Inf = MDPC_Reach_Avoid
  begin

    lemma MDPC_Reach_Avoid_opt_inf: "MDPC_Reach_Avoid_opt \<M> Inf inf (\<le>) 0 1"
      unfolding MDPC_Reach_Avoid_opt_def using reachability_opt_mode_inf MDPC_Reach_Avoid_axioms by auto

    sublocale MDPC_Reach_Avoid_opt \<M> Inf inf "(\<le>)" 0 1
      using MDPC_Reach_Avoid_opt_inf .

    lemma vDom_alt: "vDom = {0..1}"
      by (auto simp: vDom_def in_vDom_def)

    sublocale MDPC_Reach_Avoid_Prob \<M> Inf inf "(\<le>)" 0 1
      apply unfold_locales
      by (auto simp:  vDom_alt)

    lemma in_vDom_01: "in_vDom x \<longleftrightarrow> x \<in> {0..1}"
      by(simp flip: vDom_alt in_vDom_alt) 

    lemma op_state_val_in_bound:
      assumes "u \<in> states \<M> "
      and "(\<And>v. v \<in> states \<M> \<Longrightarrow> 0 \<le> x v)"
      and "(\<And>v. v \<in> states \<M> \<Longrightarrow> x v \<le> 1)"
      shows "0 \<le> op_state_val \<M> x u" and "op_state_val \<M> x u \<le> 1"
      using op_state_val_in_vDom[of _ _] assms 
      by(simp_all add: in_vDom_01)

    lemma F_inf_real_op_state_val: 
      assumes "u \<in> states \<M>" 
      assumes "\<not> op_is_avoid \<M> u"
      assumes "\<not> op_is_target \<M> u"
      assumes LE1: \<open>\<And>u. u \<in> states \<M> \<Longrightarrow> f u \<le> 1\<close>
      assumes GE0: \<open>\<And>u. u \<in> states \<M> \<Longrightarrow> f u \<ge> 0\<close>
      shows "R.F_inf_real f u = op_state_val \<M> f u"
      apply (subst R.F_inf_real)
      subgoal using GE0 by presburger
      subgoal using LE1 by presburger
      unfolding op_state_val_def
      using assms actions_finite'
      by (auto dest: computesI intro!: Squnion_dom_eqI
        simp: op_is_avoid_def op_is_target_def op_trans_val_def expectation_trans_val Setcompr_eq_image actions'_states)


    lemma n_le_op_state_val: 
      assumes "u \<in> states \<M>" 
      assumes "\<not> op_is_avoid \<M> u"
      assumes "\<not> op_is_target \<M> u"
      assumes "(\<And>u. u \<in> states \<M> \<Longrightarrow> x u \<le> 1)"
      assumes "(\<And>u. u \<in> states \<M> \<Longrightarrow> 0 \<le> x u)"
      assumes "(\<And>t. t \<in> states \<M> \<Longrightarrow> n_real t \<le> x t)"
      shows "n_real u \<le> op_state_val \<M> x u"
      apply(rule order_trans[OF F_inf_ge_iter'_state[OF _ assms(1)], of x])
      using F_inf_real_op_state_val[OF assms(1-3)] assms(4-6) by auto


    lemma n_ge_op_state_val: 
      assumes "u \<in> states \<M>" 
      assumes "\<not> op_is_avoid \<M> u"
      assumes "\<not> op_is_target \<M> u"
      assumes "(\<And>u. u \<in> states \<M> \<Longrightarrow> x u \<le> 1)"
      assumes "(\<And>u. u \<in> states \<M> \<Longrightarrow> 0 \<le> x u)"
      assumes "(\<And>t. t \<in> states \<M> \<Longrightarrow> x t \<le> n_real t)"
      shows "n_real u \<ge> op_state_val \<M> x u"
      apply(rule order_trans[OF _ F_inf_le_iter'_state[OF _ assms(1)], of _ x])
      using F_inf_real_op_state_val[OF assms(1-3)] assms(4-6) by auto

    lemma le_op_state_val:
      assumes US: "u \<in> states \<M>"
      assumes XY: \<open>\<And>u. u \<in> states \<M> \<Longrightarrow> x u \<le> y u\<close>
      shows "op_state_val \<M> x u \<le> op_state_val \<M> y u"
      unfolding op_state_val_def Setcompr_eq_image 
      using finite_actions_M 
      by (auto simp: XY landau_omega.R_mult_right_mono sum_mono US actions_neq_empty_M 
          intro!: cINF_superset_mono)

    lemma lb_0_val: "u \<in> states \<M> \<Longrightarrow> R.lb_0 u = (if op_is_target \<M> u then 1 else 0)"
      unfolding R.lb_0_def op_is_target_def
      by auto
  
    lemma ub_0_val: "u \<in> states \<M> \<Longrightarrow> R.ub_0 u = (if op_is_avoid \<M> u then 0 else 1)"
      unfolding R.ub_0_def op_is_avoid_def
      using AT_disj by (auto dest: computesI)

    lemma mop_state_vals_gs_correct:
      assumes "\<forall> u \<in> states \<M>. x u \<le> n_real u \<and> n_real u \<le> y u \<and> x u \<ge> 0 \<and> y u \<le> 1"
      shows "mop_state_vals_gs \<M> x y \<le> iin_gs_it_spec"
      unfolding mop_state_vals_gs_def iin_gs_it_spec_def mop_state_vals_gs_ninvar_def
      apply(refine_vcg FOREACH_rule[where ?I=mop_state_vals_gs_ninvar])
      subgoal by blast
      subgoal unfolding mop_state_vals_gs_ninvar_def using assms by auto
      subgoal unfolding mop_state_vals_gs_ninvar_def by force
      subgoal unfolding mop_state_vals_gs_ninvar_def by fastforce
      subgoal unfolding mop_state_vals_gs_ninvar_def by fastforce
      subgoal unfolding mop_state_vals_gs_ninvar_def by fastforce
      subgoal
        unfolding mop_state_vals_gs_ninvar_def
        using n_le_op_state_val n_ge_op_state_val op_state_val_in_bound
        by force
      subgoal unfolding mop_state_vals_gs_ninvar_def by fastforce
      done

  end

end
