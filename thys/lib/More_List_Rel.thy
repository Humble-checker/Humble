theory More_List_Rel
  imports "II_Modest_Base.Base_MEC"
begin

  section \<open>Lemmas for list_rel\<close>

  lemma bounded_list_rel_eq: "(xs, ys) \<in> \<langle>b_rel A P\<rangle>list_rel \<longleftrightarrow>(xs, ys) \<in> \<langle>A\<rangle>list_rel \<and> (\<forall> y \<in> set ys. P y)"
    apply(induction xs arbitrary: ys)
    apply auto[]
    apply clarsimp
    subgoal for x xs ys 
      apply(cases ys) 
      by auto
    done

  lemma bounded_set_rel_eq: "(xs, ys) \<in> \<langle>b_rel A P\<rangle>set_rel \<longleftrightarrow> (xs, ys) \<in> \<langle>A\<rangle>set_rel \<and> (\<forall> y \<in> ys. P y)"
    apply (auto simp: set_rel_def)
    done

  lemma br_distinct_set_to_list: "br set distinct O \<langle>b_rel Id P\<rangle>set_rel = \<langle>b_rel Id P\<rangle>list_rel O br set distinct"
    apply (auto simp: in_br_conv bounded_list_rel_eq bounded_set_rel_eq)
    done

  lemma b_rel_list_rel: "\<langle>b_rel Id P\<rangle>list_rel = b_rel Id (list_all P)"
  proof -
    have "list_all2 (eq_onp P) a b \<Longrightarrow> list_all P b" for a b 
      unfolding list.rel_eq_onp 
      by(auto simp add: eq_onp_def)
    moreover have "(\<lambda>x y. P x \<and> x = y) = (\<lambda>x x'. x = x' \<and> P x')" 
      by fast
    moreover have "list_all P b \<Longrightarrow> list_all2 (\<lambda>x x'. x = x' \<and> P x') b b" for b using eq_onp_def list.pred_rel list_all2_same
      by (simp add: eq_onp_def list.pred_rel list_all2_same)
    moreover have "list_all2 (\<lambda>x x'. x = x' \<and> P x') a b \<Longrightarrow> a = b" for a b 
      using list_all2_eq list_all2_mono by fastforce
    ultimately show ?thesis unfolding list_rel_def b_rel_def eq_onp_def by auto
  qed

  lemma list_to_set_b_relI: "list_all P xs \<Longrightarrow> distinct xs \<Longrightarrow> X = set xs \<Longrightarrow> (xs, X) \<in> \<langle>b_rel Id P\<rangle>list_set_rel"
    unfolding list_set_rel_def
    apply(auto simp: br_def b_rel_list_rel)
    done


  lemma list_to_set_b_rel'_setI: "list_all P xs \<Longrightarrow> distinct xs \<Longrightarrow> (xs, set xs) \<in> \<langle>b_rel Id P\<rangle>list_set_rel"
    unfolding list_set_rel_def
    apply(auto simp: br_def b_rel_list_rel)
    done

  lemma list_to_set_b_rel: "\<langle>b_rel Id P\<rangle>list_set_rel = {(xs, set xs) | xs. list_all P xs \<and> distinct xs }"
    unfolding list_set_rel_def
    apply(auto simp: br_def b_rel_list_rel)
    done

  lemma Id_list_set_rel: "\<langle>Id\<rangle>list_set_rel = {(xs, set xs) | xs. distinct xs}"
    unfolding list_set_rel_def
    apply(auto simp: br_def )
    done

  lemma Id_list_set_relI: "distinct xs \<Longrightarrow> X = set xs \<Longrightarrow> (xs, X) \<in> \<langle>Id\<rangle>list_set_rel"
    unfolding list_set_rel_def
    apply(auto simp: br_def )
    done

  lemma upt_list_set_rel: "([N..<M],{N..<M}) \<in> \<langle>Id\<rangle>list_set_rel"
    apply(rule Id_list_set_relI)
    apply auto
    done

  lemma zero_upt_list_set_rel: "([0..<M],{..<M}) \<in> \<langle>Id\<rangle>list_set_rel"
    apply(rule Id_list_set_relI)
    apply auto
    done

  lemma rev_upt_list_set_rel: "(rev [N..<M],{N..<M}) \<in> \<langle>Id\<rangle>list_set_rel"
    apply(rule Id_list_set_relI)
    apply auto
    done

  lemma rev_zero_upt_list_set_rel: "(rev [0..<M],{..<M}) \<in> \<langle>Id\<rangle>list_set_rel"
    apply(rule Id_list_set_relI)
    apply auto
    done

  lemma nth_to_list_all: "(\<And>i. i < length xs \<Longrightarrow> P (xs!i)) \<Longrightarrow> list_all P xs" 
    apply(induction xs rule: rev_induct)
    subgoal
      by auto
    subgoal
      apply clarsimp
      apply(rule conjI)
      subgoal
        by (metis less_SucI nth_append_first)
      subgoal
        by (metis lessI nth_append_length)
      done
    done

  lemma list_all_to_nth: "list_all P xs \<Longrightarrow> i < length xs \<Longrightarrow> P (xs!i)" 
    apply(induction xs rule: rev_induct)
    subgoal
      by simp
    subgoal
      apply clarsimp
      by (metis less_Suc_eq nth_append_first nth_append_length)
    done

  lemma sum_list_butlast_last: "xs \<noteq> [] \<Longrightarrow> sum_list (butlast xs) + last xs = sum_list xs"
    apply(induction xs rule: rev_induct)
    by auto

  section \<open>Test\<close>

  definition "right_Id R = (\<exists>f. {(x,f y) | x y . (x,y) \<in> R} \<subseteq> Id)"

  lemma right_Id_alt_aux1: "right_Id R \<Longrightarrow> \<forall>(x1,y1) \<in> R. \<forall> (x2,y2) \<in> R. y1 = y2 \<longrightarrow> x1 = x2"
    unfolding right_Id_def by (auto split: prod.splits) 

  lemma right_Id_alt_aux2:
    assumes "\<forall>(x1,y1) \<in> R. \<forall> (x2,y2) \<in> R. y1 = y2 \<longrightarrow> x1 = x2"
    shows "right_Id R"
  proof -
    obtain f where A: "(\<forall> x y. (x,y) \<in> R \<longrightarrow> f y = x)"
      using assms apply (clarsimp split: prod.splits) 
      by (metis img_snd in_snd_imageE)
    show ?thesis
      unfolding right_Id_def
      apply(rule exI[where?x=f])
      using A by blast
  qed

  lemma right_Id_alt: "right_Id R \<longleftrightarrow> (\<forall>(x1,y1) \<in> R. \<forall> (x2,y2) \<in> R. y1 = y2 \<longrightarrow> x1 = x2)"
    using right_Id_alt_aux1[of R] right_Id_alt_aux2[of R] by satx


  section \<open>Function to List Relation\<close>

  definition list_fun_rel where
    list_fun_rel_internal: "list_fun_rel n Ri Ro = {(xs,f) | xs f. n = length xs \<and> (\<forall> (i,j) \<in> Ri. i < n \<longrightarrow> (xs ! i, f j) \<in> Ro)}"

  lemma list_fun_rel_def: "\<langle>Ri,Ro\<rangle>list_fun_rel n = {(xs,f) | xs f. n = length xs \<and> (\<forall> (i,j) \<in> Ri. i < n \<longrightarrow> (xs ! i, f j) \<in> Ro)}"
    by (simp add: list_fun_rel_internal relAPP_def)

  lemma list_fun_rel_mem: "(xs,f) \<in> \<langle>Ri,Ro\<rangle>list_fun_rel n \<longleftrightarrow> n = length xs \<and> (\<forall> (i,j) \<in> Ri. i < n \<longrightarrow> (xs ! i, f j) \<in> Ro)"
    unfolding list_fun_rel_def by blast

  lemma list_fun_relI: "n = length xs \<Longrightarrow> (\<And>i j. (i,j) \<in> Ri \<Longrightarrow> i < n \<Longrightarrow> (xs ! i, f j) \<in> Ro) \<Longrightarrow> (xs,f) \<in> \<langle>Ri,Ro\<rangle>list_fun_rel n"
    unfolding list_fun_rel_def by blast

  lemma list_fun_relD1: "(xs,f) \<in> \<langle>Ri,Ro\<rangle>list_fun_rel n \<Longrightarrow> n = length xs"
    unfolding list_fun_rel_def by blast

  lemma list_fun_relD2: "(xs,f) \<in> \<langle>Ri,Ro\<rangle>list_fun_rel n \<Longrightarrow> (\<forall> i j. (i,j) \<in> Ri \<longrightarrow> i < n \<longrightarrow> (xs ! i, f j) \<in> Ro)"
    unfolding list_fun_rel_def by blast

  lemma list_fun_relE: "(xs,f) \<in> \<langle>Ri,Ro\<rangle>list_fun_rel n \<Longrightarrow> (n = length xs \<Longrightarrow> (\<And>i j. (i,j) \<in> Ri \<Longrightarrow> i < n \<Longrightarrow> (xs ! i, f j) \<in> Ro) \<Longrightarrow> P) \<Longrightarrow> P"
    unfolding list_fun_rel_def by blast

  lemma nth_list_fun_rel: "(xs,(!) xs) \<in> \<langle>Id,Id\<rangle>list_fun_rel (length xs)"
    unfolding list_fun_rel_def by blast

  lemma br_id_list_fun_rel: "(xs,f) \<in> \<langle>br \<alpha> I,Ro\<rangle>list_fun_rel n \<longleftrightarrow> n = length xs \<and> (\<forall>i<length xs. I i \<longrightarrow> (xs ! i, f (\<alpha> i)) \<in> Ro)"
    unfolding list_fun_rel_def by (auto simp: br_def)

  lemma Domain_list_fun_rel_sub_len: "Domain (\<langle>Ri,Ro\<rangle>list_fun_rel n) \<subseteq> {xs. length xs = n}"
    unfolding list_fun_rel_def
    by blast

  lemma Ex_fun_list_fun_rel:
    assumes NLEN: "n = length xs"
    assumes RII: "(\<And> i1 j1 i2 j2. (i1,j1) \<in> Ri \<Longrightarrow> (i2,j2) \<in> Ri \<Longrightarrow> j1 = j2 \<Longrightarrow> i1 = i2)"
    assumes RI: "(\<And>j. \<exists> i. i < length xs \<and> (i,j) \<in> Ri)"
    assumes RO: "(\<And> x. \<exists> y. (x,y) \<in> Ro)"
    shows "\<exists> f. (xs,f) \<in> \<langle>Ri,Ro\<rangle>list_fun_rel n"
  proof -

    obtain f where FD: "(\<And>i j. f j = i \<Longrightarrow> i < length xs \<and> (i,j) \<in> Ri)"
      using RI by metis

    obtain g where GD: "(\<And>x y. g x = y \<Longrightarrow> (x,y) \<in> Ro)"
      using RO by metis

    {
      fix a b
      assume RI': "(a, b) \<in> Ri" and AL: "a < length xs"
      
      have AUX:"(xs ! f b, g (xs ! f b)) \<in> Ro"
        using GD by blast

      have "(f b, b) \<in> Ri" and "f b < length xs"
        using FD by blast+
      with RII RI' have "a = f b"
        by presburger

      with AUX have "(xs ! a, g (xs ! f b)) \<in> Ro"
        by blast
    }

    thus ?thesis
      unfolding list_fun_rel_def apply (clarsimp simp: NLEN)
      by(auto intro: exI[where ?x="(\<lambda>j. g (xs ! (f j)))"])
  qed

  (*TODO this lemma is iteratively constructed from my needs, rather than a concrete idea, see if there is some idea behind it*)
  lemma Ex_fun_eq_list_fun_rel:
    assumes NLEN: "n = length xs"
    assumes RII: "(\<And> i1 i2 j. (i1,j) \<in> Ri \<Longrightarrow> (i2,j) \<in> Ri \<Longrightarrow> xs ! i1 = xs ! i2)"
    assumes FD: "(\<And>i j. j \<in> Range Ri \<Longrightarrow> f j = i \<Longrightarrow> i < length xs \<and> (i,j) \<in> Ri)"
    assumes GD: "(\<And>x y. x \<in> set xs \<Longrightarrow>  g x = y \<Longrightarrow> (x,y) \<in> Ro)"
    assumes PH: "P (\<lambda>j. g (xs ! (f j)))"
    shows "\<exists> h. (xs,h) \<in> \<langle>Ri,Ro\<rangle>list_fun_rel n \<and> P h"
  proof -

    {
      fix a b
      assume RI': "(a, b) \<in> Ri" and AL: "a < length xs"
      

      have "(f b, b) \<in> Ri" and AUX: "f b < length xs"
        using RI' FD by blast+
      with RII RI' have "xs ! a = xs ! (f b)"
        by blast

      moreover have "(xs ! f b, g (xs ! f b)) \<in> Ro"
        using AUX GD by auto

      ultimately have "(xs ! a, g (xs ! f b)) \<in> Ro"
        by argo
    }

    thus ?thesis
      unfolding list_fun_rel_def using PH by (fastforce simp: NLEN) 
  qed

  lemma Domain_list_fun_rel:
    assumes NLEN: "n = length xs"
    assumes RII: "(\<And> i1 j1 i2 j2. (i1,j1) \<in> Ri \<Longrightarrow> (i2,j2) \<in> Ri \<Longrightarrow> j1 = j2 \<Longrightarrow> i1 = i2)"
    assumes RI: "(\<And>j. \<exists> i. i < length (xs ::'a list) \<and> (i,j) \<in> Ri)"
    assumes RO: "(\<And> x. \<exists> y. (x,y) \<in> Ro)"
    shows "Domain (\<langle>Ri,Ro\<rangle>list_fun_rel n) = {xs :: 'a list. length xs = n}"
    apply safe
    subgoal using Ex_fun_list_fun_rel[OF NLEN] RII RI RO  by (auto simp: NLEN list_fun_rel_mem)
    subgoal for x
      using Ex_fun_list_fun_rel[OF NLEN] RII RI RO 
      by (simp add: Domain_iff Ex_fun_list_fun_rel assms(1))
    done

  lemma list_fun_rel_upd: "(\<And> i' j'. (i',j') \<in> Ri \<Longrightarrow> i' = i \<longleftrightarrow> j' = j) \<Longrightarrow> (xs,f) \<in> \<langle>Ri,Ro\<rangle>list_fun_rel n \<Longrightarrow> (i,j) \<in> Ri \<Longrightarrow> i < n \<Longrightarrow> (x,y) \<in> Ro \<Longrightarrow> (xs[i:=x],f(j:=y)) \<in> \<langle>Ri,Ro\<rangle>list_fun_rel n"
    unfolding list_fun_rel_def apply clarsimp by fastforce


  lemma list_fun_rel_Zero: "\<langle>Ri,Ro\<rangle>list_fun_rel 0 = Collect (\<lambda> (xs,f). xs = [])"
    unfolding list_fun_rel_def by auto

  lemma list_rel_comp_list_fun_rel_dist: "\<langle>R1\<rangle>list_rel O \<langle>Ri,R2\<rangle>list_fun_rel N \<subseteq> \<langle>Ri, R1 O R2\<rangle>list_fun_rel N"
    unfolding list_rel_def list_fun_rel_def 
    apply (clarsimp simp: list_all2_iff split: prod.splits) 
    by (metis length_zip min.idem nth_mem nth_zip relcomp.simps)

  lemma list_fun_rel_comp_fun_rel_dist: "\<langle>Ri1,Ro1\<rangle>list_fun_rel N O (Ri2 \<rightarrow> Ro2) \<subseteq> \<langle>Ri1 O Ri2, Ro1 O Ro2\<rangle>list_fun_rel N"
    unfolding list_rel_def list_fun_rel_def 
    apply (clarsimp simp: list_all2_iff split: prod.splits) 
    by (metis relcomp.relcompI tagged_fun_relD_rhs)

  lemma list_rel_comp_list_fun_rel: "\<langle>R1\<rangle>list_rel O \<langle>Id,R2\<rangle>list_fun_rel N = \<langle>Id, R1 O R2\<rangle>list_fun_rel N"
  proof(safe)
    fix x y z
    assume "(x, y) \<in> \<langle>R1\<rangle>list_rel" "(y, z) \<in> \<langle>Id,R2\<rangle>list_fun_rel N"
    then show "(x, z) \<in> \<langle>Id, R1 O R2\<rangle>list_fun_rel N"
      unfolding list_fun_rel_def list_rel_def 
      by (auto simp: Id_def dest: list_all2_lengthD list_all2_nthD2)
  next
    fix x z
    assume A: "(x, z) \<in> \<langle>Id, R1 O R2\<rangle>list_fun_rel N"
    hence "\<forall>i < length x. (\<exists> y'. (x ! i, y') \<in> R1 \<and> (y', z i) \<in> R2)" 
      unfolding list_fun_rel_def by auto
    then obtain y where "length y = length x" and "\<forall>i<length x. (\<forall>j. (x ! i, y ! i) \<in> R1 \<and> (y ! i, z i) \<in> R2)"
      unfolding Skolem_list_nth by fast
    hence "(x, y) \<in> \<langle>R1\<rangle>list_rel" and "(y, z) \<in> \<langle>Id,R2\<rangle>list_fun_rel N"
      unfolding list_fun_rel_def list_rel_def using A 
      by (auto simp add: list_all2_all_nthI list_fun_rel_mem) 
    thus "(x,z) \<in> \<langle>R1\<rangle>list_rel O \<langle>Id,R2\<rangle>list_fun_rel N"
      by blast
  qed

  lemma list_rel_comp_b_rel_eq: "(\<And>i. i < N \<Longrightarrow> P i) \<Longrightarrow> \<langle>b_rel Id P,R\<rangle>list_fun_rel N = \<langle>Id,R\<rangle>list_fun_rel N"
    unfolding list_fun_rel_def by (auto simp: b_rel_def)



  lemma Ex_list_of_nat_fun: "\<exists>xs. i = length xs \<and> (\<forall>j < i. xs ! j = f j)"
  proof (induction i)
    case 0
    then show ?case by simp
  next
    case (Suc i)
    then obtain xs where "i = length xs" and "(\<forall>j<i. xs ! j = f j)" by blast
    then show ?case apply clarsimp
      apply(rule exI[where ?x="xs@[f (length xs)]"])
      apply clarsimp
      subgoal for j
        by(cases "j = length xs";  auto)
      done
  qed

  (* TODO: This lemma is still quite specific and can definitely be made more general*)
  lemma list_rel_comp_list_fun_rel_br: "(\<And>i. i < N \<Longrightarrow> I i) \<Longrightarrow> \<langle>R1\<rangle>list_rel O \<langle>br \<alpha> I,Id\<rangle>list_fun_rel N = \<langle>br \<alpha> I, R1\<rangle>list_fun_rel N"
  proof(safe)
    fix x y z
    assume "(x, y) \<in> \<langle>R1\<rangle>list_rel" "(y, z) \<in> \<langle>br \<alpha> I,Id\<rangle>list_fun_rel N"
    then show "(x, z) \<in> \<langle>br \<alpha> I, R1\<rangle>list_fun_rel N"
      unfolding list_fun_rel_def list_rel_def 
      by (auto simp: br_def list_all2_conv_all_nth Id_def dest: list_all2_lengthD list_all2_nthD2) 
  next
    fix x z
    assume A: "(x, z) \<in> \<langle>br \<alpha> I, R1\<rangle>list_fun_rel N" and B: "(\<And>i. i < N \<Longrightarrow> I i)"
    hence "\<forall>i < length x. (x ! i, z (\<alpha> i)) \<in> R1 \<and> (z (\<alpha> i), z (\<alpha> i)) \<in> Id" and "length x = N"
      by (auto simp: br_id_list_fun_rel)

    moreover obtain y where "length y = N" and "(\<And>i. i<length y \<Longrightarrow> y ! i = z (\<alpha> i))"
      using Ex_list_of_nat_fun[of "N" "z o \<alpha>"] by force

    ultimately have "(x, y) \<in> \<langle>R1\<rangle>list_rel" and "(y, z) \<in> \<langle>br \<alpha> I,Id\<rangle>list_fun_rel N"
      unfolding list_fun_rel_def list_rel_def 
      by (auto simp add: in_br_conv list_fun_rel_mem intro!: list_all2_all_nthI) 

    thus "(x,z) \<in> \<langle>R1\<rangle>list_rel O \<langle>br \<alpha> I, Id\<rangle>list_fun_rel N"
      by blast
  qed

end
