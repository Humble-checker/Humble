theory Util
  imports "HOL-Probability.Probability"
begin

section \<open>Util\<close>

lemma nat_descent: 
  assumes \<open>P i\<close> \<open>\<And>i. P i \<Longrightarrow> i > 0 \<Longrightarrow> \<exists>j < i. P j\<close>
  shows \<open>P (0 :: nat)\<close>
  using assms
  by (induction i rule: less_induct) auto

lemma emeasure_prob_space_compl:  \<open>prob_space M \<Longrightarrow> A \<in> sets M \<Longrightarrow> emeasure M (space M - A) = 1 - emeasure M A\<close>
  by (simp add: emeasure_compl finite_measure.emeasure_finite prob_space.emeasure_space_1 prob_space_def)

lemma enn2real_e2ennreal:
  assumes \<open>x \<ge> 0\<close>
  shows \<open>enn2real (e2ennreal x) = real_of_ereal x\<close>
  by (simp add: assms enn2ereal_e2ennreal enn2real_def)

lemma power_of_ceil_nat_log_le: 
  \<open>j > 0 \<Longrightarrow> i < 1 \<Longrightarrow> 0 < i \<Longrightarrow> i ^ nat \<lceil>log i j\<rceil> \<le> j\<close>
  using powr_log_cancel[of i j] powr_realpow[of i] of_nat_ceiling powr_mono'
  by (smt (verit))

subsection \<open>Continuity\<close>

lemma sup_continuous_min1[order_continuous_intros]: 
  \<open>sup_continuous f \<Longrightarrow> sup_continuous (\<lambda>x. min (y :: _ :: complete_linorder) (f x))\<close>
  unfolding sup_continuous_def
  by (auto intro!: antisym SUP_least simp: less_Sup_iff le_SUP_iff)

lemma inf_continuous_min1[order_continuous_intros]: 
  \<open>inf_continuous f \<Longrightarrow> inf_continuous (\<lambda>x. min (y :: _ :: complete_linorder) (f x))\<close>
  unfolding inf_continuous_def
  apply (auto intro!: )
  subgoal for M
    apply (auto intro!: antisym SUP_least INF_greatest)
    apply (cases \<open>y \<le> (\<Squnion>i. f (M i))\<close>)
    subgoal by (meson INF_lower UNIV_I linorder_not_le min_less_iff_conj)
    subgoal by (meson INF_lower UNIV_I linorder_not_le min_less_iff_conj)
    apply (auto simp add: INF_lower2)
    by (meson INF_lower2 UNIV_I linorder_not_less min_less_iff_conj order_less_le) 
  done

lemma inf_continuous_applyD: \<open>inf_continuous f \<Longrightarrow> inf_continuous (\<lambda>x. f x h)\<close>
  unfolding inf_continuous_def
  by (metis INF_apply)

lemma inf_continuous_If': 
  \<open>(C \<Longrightarrow> inf_continuous F) \<Longrightarrow> (\<not> C \<Longrightarrow> inf_continuous G) \<Longrightarrow> inf_continuous (\<lambda>f. if C then F f else G f)\<close>
  unfolding inf_continuous_def
  by auto

lemmas inf_continuous_If[order_continuous_intros del]
lemmas inf_continuous_If'[order_continuous_intros]

lemma inf_continuous_INF[order_continuous_intros]:
  fixes M :: "_ \<Rightarrow> _ \<Rightarrow> 'a::complete_lattice"
  assumes M: "\<And>i. i \<in> I \<Longrightarrow> inf_continuous (M i)"
  shows  "inf_continuous (INF i\<in>I. M i)"
  unfolding inf_continuous_def by (auto simp add: inf_continuousD [OF M] image_comp intro: INF_commute)

lemma inf_continuous_apply_INF[order_continuous_intros]:
  fixes M :: "_ \<Rightarrow> _ \<Rightarrow> 'a::complete_lattice"
  shows "(\<And>i. i \<in> I \<Longrightarrow> inf_continuous (M i)) \<Longrightarrow> inf_continuous (\<lambda>x. INF i\<in>I. M i x)"
  unfolding INF_apply[symmetric] by (rule inf_continuous_INF)

lemma cINF_lower3: \<open>X \<noteq> {} \<Longrightarrow> \<forall>x \<in> X. x \<le> c \<Longrightarrow> bdd_below X \<Longrightarrow> \<Sqinter>(X :: real set) \<le> c\<close>
  using cInf_lower2 by blast

subsection \<open>Sup + Inf\<close>
lemma SUP_mono'':
  assumes \<open>\<And>i. (f i :: _ :: complete_lattice) \<le> g (h i)\<close>
  shows \<open>(\<Squnion>i. f i) \<le> (\<Squnion>i. g i)\<close>
  using assms
  by (auto intro!: SUP_mono)

lemma Sup_Suc_mono:
  assumes \<open>mono (f :: nat \<Rightarrow> _ :: complete_lattice)\<close>
  shows \<open>(\<Squnion>i. f (Suc i)) = (\<Squnion>i. f i)\<close>  
  using monoD[OF assms]
  by (auto intro!: SUP_least antisym intro: SUP_upper2)

lemma enn2real_Inf: 
  assumes \<open>X \<noteq> {}\<close> and X_fin: \<open>\<And>x. x \<in> X \<Longrightarrow> x < \<infinity>\<close>
  shows \<open>enn2real (\<Sqinter>X) = \<Sqinter>(enn2real ` X)\<close>
proof  -
  obtain x where \<open>x \<in> X\<close> \<open>x < \<infinity>\<close>
    using assms less_top
    by auto

  hence Inf_ninfty: \<open>(\<Sqinter>X) < \<infinity>\<close>
    using Inf_less_iff by blast

  have \<open>enn2real (\<Sqinter> X) \<le> \<Sqinter> (enn2real ` X)\<close>
    using assms
    by (auto simp add: Inf_lower intro!: cINF_greatest[OF \<open>X \<noteq> {}\<close>] enn2real_mono)

  have \<open>\<And>x. x \<in> X \<Longrightarrow>  (\<Sqinter> (enn2real ` X)) \<le> enn2real x\<close>
    by (auto intro!: cINF_lower bdd_belowI[of _ 0])

  hence \<open>ennreal (\<Sqinter> (enn2real ` X)) \<le> (\<Sqinter> X)\<close>
    by (metis Inf_greatest enn2real_less_iff ennreal_le_epsilon not_le)

  thus ?thesis
    by (metis Inf_ninfty \<open>enn2real (\<Sqinter> X) \<le> \<Sqinter> (enn2real ` X)\<close> enn2real_less infinity_ennreal_def linorder_not_le order_less_le)
qed

lemma enn2real_Sup: 
  assumes \<open>X \<noteq> {}\<close> and Sup_fin: \<open>(\<Squnion>X) \<noteq> \<infinity>\<close>
  shows \<open>enn2real (\<Squnion>X) = \<Squnion>(enn2real ` X)\<close>
proof (cases \<open>(\<Squnion>X) = 0\<close>)
  case True
  hence "X = {0}"
    using assms Sup_le_iff[of X 0]
    by auto
  then show ?thesis
    by auto
next
  case False
  have X_fin: \<open>x\<in>X \<Longrightarrow> x < \<top>\<close> for x
    using assms less_top
    by auto

  hence [simp]: \<open>x\<in>X \<Longrightarrow> ennreal (enn2real x) = x\<close> for x
    using assms less_top
    by auto

  from False have \<open>\<not>(\<Squnion>X)\<le> 0\<close>
    by auto

  hence \<open>(\<Squnion>X)> 0\<close>
    by order

  moreover have \<open>(\<Squnion>X) = \<Squnion>(enn2real ` X)\<close>
    using assms by (subst ennreal_Sup) (auto simp add: image_image )
  ultimately show ?thesis
    by (subst enn2real_eq_posreal_iff) auto
qed

subsection \<open>Argmax and Argmin\<close>
lemma ex_max_if_finite:
  "\<lbrakk> finite S; S \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>m\<in>S. \<not>(\<exists>x\<in>S. x > (m::'a::order))"
by(induction rule: finite.induct) (auto intro: order.strict_trans)

lemma ex_is_arg_max_if_finite: fixes f :: "'a \<Rightarrow> 'b :: order"
shows "\<lbrakk> finite S; S \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>x. is_arg_max f (\<lambda>x. x \<in> S) x"
unfolding is_arg_max_def
using ex_max_if_finite[of "f ` S"]
by auto

lemma arg_max_if_finite: fixes f :: "'a \<Rightarrow> 'b :: order"
assumes "finite S" "S \<noteq> {}"
shows  "arg_max_on f S \<in> S" and "\<not>(\<exists>x\<in>S. f x > f (arg_max_on f S))"
using ex_is_arg_max_if_finite[OF assms, of f]
unfolding arg_max_on_def arg_max_def is_arg_max_def
by(auto dest!: someI_ex)

lemma (in -) arg_max_SOME_Max:
  "finite S \<Longrightarrow> arg_max_on f S = (SOME y. y \<in> S \<and> f y = Max(f ` S))"
  unfolding arg_max_on_def arg_max_def is_arg_max_linorder
  by (rule arg_cong[where f = Eps]) (auto simp: fun_eq_iff intro: Max_eqI[symmetric])

lemma (in -) arg_max_on_Max:
  assumes \<open>X \<noteq> {}\<close> \<open>finite X\<close>
  shows \<open>f (arg_max_on f X) = (MAX x \<in> X. f x :: _ :: order)\<close>
  using assms
  apply (auto simp: arg_max_SOME_Max)
  by (smt (verit, del_insts) Max_in assms(1) finite_imageI imageE image_is_empty someI_ex)

lemma arg_min_on_Min:
  assumes \<open>X \<noteq> {}\<close> \<open>finite X\<close>
  shows \<open>f (arg_min_on f X) = (MIN x \<in> X. f x :: _ :: order)\<close>
  using assms
  by (smt (verit) Min_eqI arg_min_if_finite(1) arg_min_least finite_imageI imageE imageI)

subsection \<open>Integrals\<close>

lemma measure_pmf_integral_leI:
  assumes \<open>\<And>x. x \<in> set_pmf P \<Longrightarrow> \<bar>f x\<bar> \<le> b\<close>
  shows \<open>measure_pmf.expectation P f \<le> (b :: real)\<close>
    using assms
    by (fastforce simp: AE_measure_pmf_iff intro: measure_pmf.integral_le_const measure_pmf.integrable_const_bound)

lemma sup_continuous_nn_integral_pmf: 
  \<open>sup_continuous (nn_integral (measure_pmf (P :: 's pmf)))\<close>
proof -
  {
    fix M :: \<open>nat \<Rightarrow> 's \<Rightarrow> ennreal\<close>
    assume M: \<open>incseq M\<close>

    have \<open>(\<integral>\<^sup>+ x. ((\<Squnion>x. (M x)) x) \<partial>measure_pmf P) = (\<Squnion>i. \<integral>\<^sup>+ x. (M i x) \<partial>measure_pmf P)\<close>
      using M
      by (simp add: nn_integral_monotone_convergence_SUP image_image incseq_def le_funI)
  }
  thus ?thesis
    unfolding sup_continuous_def
    by blast
qed

lemma nn_integral_topI:
  assumes \<open>X \<in> sets M\<close> \<open>\<And>x. x \<in> X \<Longrightarrow> f x = \<top>\<close> \<open>X \<notin> null_sets M\<close> \<open>f \<in> borel_measurable M\<close>
  shows \<open>nn_integral M f = \<top>\<close>
  using assms
proof -
  have \<open>set_nn_integral M X f = set_nn_integral M X (\<lambda>_. \<top>)\<close>
    using assms by (auto intro: set_nn_integral_cong)
  also have \<open>\<dots> = \<top>\<close>
    using assms
    by (auto simp: nn_integral_cmult_indicator null_sets_def)
  moreover have \<open>nn_integral M f = set_nn_integral M X f + set_nn_integral M (-X) f\<close>
    using assms
    by (subst nn_integral_add[symmetric]) (auto intro!: nn_integral_cong simp: indicator_def)
  ultimately show ?thesis
    by fastforce
qed

lemma measure_pmf_nn_integral_topI:
  assumes \<open>s \<in> set_pmf P\<close> \<open>f s = \<top>\<close>
  shows \<open>nn_integral P f = \<top>\<close>
  using assms
  by (intro nn_integral_topI[of \<open>{s}\<close>]) (auto simp: null_sets_def emeasure_pmf_single_eq_zero_iff)

lemma finite_nn_integral_lt_topI:
  assumes \<open>\<And>s. s \<in> set_pmf P \<Longrightarrow> f s \<noteq> \<top>\<close> \<open>finite (set_pmf P)\<close>
  shows \<open>nn_integral P f \<noteq> \<top>\<close>
proof -
  have \<open>nn_integral P f \<le> Max (f ` set_pmf P)\<close>
    using assms
    by (auto simp: AE_measure_pmf_iff intro!: measure_pmf.nn_integral_le_const)
  moreover have \<open>Max (f ` set_pmf P) < \<top>\<close>
    using assms less_top
    by (auto simp: set_pmf_not_empty)
  ultimately show ?thesis
    using less_top 
    by auto
qed


lemma finite_nn_integral_lt_topI':
  assumes \<open>\<And>s. s \<in> set_pmf P \<Longrightarrow> f s \<noteq> \<top>\<close> \<open>finite (set_pmf P)\<close>
  shows \<open>nn_integral P f < \<top>\<close>
  using assms(1) assms(2) finite_nn_integral_lt_topI less_top by blast

lemma inf_continuous_nn_integral_pmf:
  assumes \<open>finite (set_pmf P)\<close>
  shows \<open>inf_continuous (nn_integral (measure_pmf (P :: 's pmf)))\<close>
proof -
  {
    fix M :: \<open>nat \<Rightarrow> 's \<Rightarrow> ennreal\<close>
    assume M: \<open>decseq M\<close>

    have \<open>(\<integral>\<^sup>+ x. ((\<Sqinter>i. (M i x))) \<partial>measure_pmf P) = (\<Sqinter>i. \<integral>\<^sup>+ x. (M i x) \<partial>measure_pmf P)\<close>
    proof (cases \<open>\<exists>j \<in> set_pmf P. \<forall>i. M i j = \<infinity>\<close>)
      case True
      hence \<open>(\<integral>\<^sup>+ x. ((\<Sqinter>i. (M i) x)) \<partial>measure_pmf P) = \<top>\<close>
        using measure_pmf_nn_integral_topI 
        by fastforce
      also have \<open>\<dots> = (\<Sqinter>i. \<integral>\<^sup>+ x. (M i x) \<partial>measure_pmf P)\<close>
        using True
        by (auto simp add: measure_pmf_nn_integral_topI)
      finally show ?thesis .
    next
      case False
      hence \<open>\<forall>j \<in> set_pmf P. \<exists>i. \<forall>j' \<ge> i. M j' j \<noteq> \<infinity>\<close>
        using M le_funD
        by (metis decseqD infinity_ennreal_def top_le)
      hence \<open>\<forall>j \<in> set_pmf P. \<exists>\<^sub>\<infinity>i. M i j \<noteq> \<infinity>\<close>
        by (metis (mono_tags, lifting) INFM_nat_le nat_le_linear)
      hence \<open>\<exists>i. \<forall>j \<in> set_pmf P. M i j \<noteq> \<infinity>\<close>
        by (smt (verit, ccfv_threshold) INFM_EX M assms decseqD finite_indexed_bound infinity_ennreal_def le_funD top_le)
      then obtain i where \<open>(\<forall>j\<in>set_pmf P. M i j \<noteq> \<infinity>)\<close>
        using assms
        by auto
      then show ?thesis
        using M finite_nn_integral_lt_topI assms
        by (auto intro!: finite_nn_integral_lt_topI' nn_integral_monotone_convergence_INF_decseq[of _ _ i])
    qed
  }
  thus ?thesis
    unfolding inf_continuous_def INF_apply
    by blast
qed


end
