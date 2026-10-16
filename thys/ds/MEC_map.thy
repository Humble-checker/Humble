theory MEC_map
  imports "Array_Nat_Tuple_Partition"
begin

  lemma inj_on_nat_Inf:
    fixes A::"nat set set"
    assumes NE: "{} \<notin> A"
    assumes DISJ: "(\<And> A\<^sub>1 A\<^sub>2 a. A\<^sub>1 \<in> A \<Longrightarrow> A\<^sub>2 \<in> A \<Longrightarrow> a \<in> A\<^sub>1 \<Longrightarrow> a \<in> A\<^sub>2 \<Longrightarrow> A\<^sub>1 = A\<^sub>2)"
    shows "inj_on Inf A"
  proof(rule inj_onI)
    fix B\<^sub>1 B\<^sub>2
    assume A: "B\<^sub>1 \<in> A " "B\<^sub>2 \<in> A" "\<Sqinter> B\<^sub>1 = \<Sqinter> B\<^sub>2"
    with NE have "B\<^sub>1 \<noteq> {}" and "B\<^sub>2 \<noteq> {}"
      by blast+
    hence "\<Sqinter> B\<^sub>1 \<in> B\<^sub>1" and "\<Sqinter> B\<^sub>2 \<in> B\<^sub>2"
      using Inf_nat_def1 by force+
    with A DISJ show "B\<^sub>1 = B\<^sub>2"
      by presburger
  qed

  lemma inj_on_enat_Inf:
    fixes A::"enat set set"
    assumes NINF: "{\<infinity>} \<in> A \<Longrightarrow> {} \<in> A \<Longrightarrow> False"
    assumes DISJ: "(\<And> A\<^sub>1 A\<^sub>2 a. A\<^sub>1 \<in> A \<Longrightarrow> A\<^sub>2 \<in> A \<Longrightarrow> a \<in> A\<^sub>1 \<Longrightarrow> a \<in> A\<^sub>2 \<Longrightarrow> A\<^sub>1 = A\<^sub>2)"
    shows "inj_on Inf A"
  proof(rule inj_onI)
    fix B\<^sub>1 B\<^sub>2
    assume A: "B\<^sub>1 \<in> A " "B\<^sub>2 \<in> A" "\<Sqinter> B\<^sub>1 = \<Sqinter> B\<^sub>2"

    show "B\<^sub>1=B\<^sub>2"
    proof(cases "B\<^sub>1 = {}")
      case True
      hence 1: "{\<infinity>} \<notin> A"
        using NINF A(1) by blast
      from True have "\<Sqinter> B\<^sub>1 = \<infinity>" 
        using Inf_enat_def by auto
      with A(3) have "\<Sqinter> B\<^sub>2 = \<infinity>"
        by presburger
      hence "B\<^sub>2 = {}"
        using 1 A True
        by (metis Inf_top_conv(1) cInf_singleton is_singletonE is_singletonI' top_enat_def)
      with True show ?thesis 
        by presburger
    next
      case False
      hence 1: "\<Sqinter> B\<^sub>1 \<in> B\<^sub>1"
        using wellorder_InfI by fastforce
      moreover have "\<Sqinter> B\<^sub>2 \<in> B\<^sub>2"
      proof -
        have "B\<^sub>2 \<noteq> {}"
        proof(rule notI)
          assume B: "B\<^sub>2 = {}"
          hence "\<Sqinter> B\<^sub>2 = \<infinity>"
            by (simp add: Inf_enat_def)
          moreover from 1 have "B\<^sub>1={\<infinity>}"
            using A(3) \<open>B\<^sub>2 = {}\<close> calculation by auto
          with A B NINF show False
            by blast
        qed
        thus ?thesis 
          using wellorder_InfI by auto
      qed
      with DISJ A 1 show ?thesis
        by presburger
    qed
  qed

  lemma bij_betw_eq_dom: "bij_betw f A B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> bij_betw g A B"
    by(drule bij_betw_cong; blast) 

  lemma fin_eq_image_bij_betw: assumes "finite A" and "f ` A = A"
    shows "bij_betw f A A"
    by (auto simp: assms bij_betw_def intro!: eq_card_imp_inj_on)

  section\<open>Correctness Proofs\<close>


text \<open>
  This theory implements the output type of the algorithm. It is based on the 
    Disj_Nat_Set_List_Tuple from which it is derived in the MEC algorithm.
\<close>

  type_synonym mec_map = "nat set list"
  type_synonym mec_mapc = "nat \<times> nat dsmt"
  type_synonym mec_mapc' = "nat \<times> ((nat, tuple_list_id) i_map)"
  type_synonym mec_mapi = "64 Word.word \<times> 64 Word.word ptr"


  definition op_antpar_to_mec_map :: "antpar \<Rightarrow> mec_map" where "op_antpar_to_mec_map = (\<lambda> (XS,YS). XS)"
  definition op_mec_map_length :: "mec_map \<Rightarrow> nat" where "op_mec_map_length XS = length XS"
  definition op_in_eq_mec :: "mec_map \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "op_in_eq_mec XS v w = (\<exists> i < length XS. v \<in> XS ! i \<and> w \<in> XS ! i)"
  definition op_mec_index_of :: "mec_map \<Rightarrow> nat \<Rightarrow> nat" where "op_mec_index_of XS v = (THE i. i < length XS \<and> v \<in> XS ! i)"
  definition op_sort_by_inf :: "mec_map \<Rightarrow> mec_map" where "op_sort_by_inf XS = sort_key Inf XS"


  definition mec_map_\<alpha> :: "mec_mapc \<Rightarrow> mec_map" where "mec_map_\<alpha> = (\<lambda> (n\<^sub>1,M). (map (\<lambda> i. {v. M v = Some (LIST1 i)}) [0..<n\<^sub>1]))"


  context disj_set_list_tuple_defs
  begin
  
    definition mec_map_invar :: "mec_mapc \<Rightarrow> bool" where "mec_map_invar = (\<lambda> (n\<^sub>1,M). n\<^sub>1 \<le> L\<^sub>1 \<and> (\<forall> v. case M v of Some lv \<Rightarrow> (case lv of LIST1 i \<Rightarrow> i < n\<^sub>1 \<and> v < N | LIST2 j \<Rightarrow> False) | None \<Rightarrow> v \<ge> N) \<and> (\<forall>i < n\<^sub>1. \<exists> v < N. M v = Some (LIST1 i)))"
    
    definition "mec_map_rel = br mec_map_\<alpha> mec_map_invar" 
  

    definition "mec_map_eq_mec_mem_pre = (\<lambda> XS v. (\<exists> i < length XS. v \<in> XS ! i))"

    lemma mec_map_invarD1: "mec_map_invar (n\<^sub>1,M) \<Longrightarrow> n\<^sub>1 \<le> L\<^sub>1"
      unfolding mec_map_invar_def by blast

    lemma mec_map_invarD2: "mec_map_invar (n\<^sub>1,M) \<Longrightarrow> (\<forall> v. case M v of Some lv \<Rightarrow> (case lv of LIST1 i \<Rightarrow> i < n\<^sub>1 \<and> v < N | LIST2 j \<Rightarrow> False) | None \<Rightarrow> v \<ge> N)"
      unfolding mec_map_invar_def by blast

    lemma mec_map_invarD3: "mec_map_invar (n\<^sub>1,M) \<Longrightarrow> (\<forall>i < n\<^sub>1. \<exists> v < N. M v = Some (LIST1 i))"
      unfolding mec_map_invar_def by blast

    lemma mec_map_invar_Some: "mec_map_invar (n, M) \<Longrightarrow> M v = Some i' \<Longrightarrow> v < N \<and> (\<exists>i. i' = LIST1 i \<and> i < n)"
      unfolding mec_map_invar_def
      apply(cases i') 
      by(auto split: option.splits tuple_list_id.splits) 

    lemma mec_map_invar_card:
      assumes INV: "mec_map_invar (n, M)"
      shows "n = card {i. \<exists>v::nat < N. M v = Some (LIST1 i)}"
    proof -
      have "{i. \<exists>v::nat < N. M v = Some (LIST1 i)} = {..<n}"
        apply(rule equalityI)
        subgoal by (auto dest: mec_map_invar_Some[OF INV])
        subgoal using mec_map_invarD3[OF INV] by blast
        done
      thus ?thesis
        by auto
    qed


    definition t_to_mec_map :: "antparc \<Rightarrow> mec_mapc" where "t_to_mec_map= (\<lambda> (n\<^sub>1,n\<^sub>2,M). (n\<^sub>1,M))"
    sepref_register t_to_mec_map :: "antparc'\<Rightarrow> mec_mapc'" (*TODO: I think we do not need the special type mec_mapc' and antparc' anymore*)

    definition mec_map_len :: "mec_mapc \<Rightarrow> nat" where "mec_map_len = (\<lambda>(n,M). n)"
    sepref_register mec_map_len :: "mec_mapc' \<Rightarrow> nat"

    definition eq_mec_member :: "mec_mapc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "eq_mec_member = (\<lambda> (n,M) v w. the (op_map_lookup v M) = the (op_map_lookup w M))"
    sepref_register eq_mec_member :: "mec_mapc' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"

    text \<open>The MEC index of state \<^term>\<open>v\<close>: a single array lookup \<^term>\<open>M v\<close> decoded to its index.\<close>
    definition mec_index_of :: "mec_mapc \<Rightarrow> nat \<Rightarrow> nat" where "mec_index_of = (\<lambda> (n,M) v. of_LIST1 (the (op_map_lookup v M)))"
    sepref_register mec_index_of :: "mec_mapc' \<Rightarrow> nat \<Rightarrow> nat"

    text \<open>Because a MEC partition contains all numbers from 0 to N, we can sort partitions in linear
      time. We iterate over the range {0..<N} and greedily assign the first number that we encounter 
      of each partition to the lowest possible index. For subsequent states in that partition, we 
      add them to the same index. To this end, we use a partial function \<open>xs\<close> that maps indices of
      the input partitions to their new index, or to None if no state of that partition has been 
      iterated over.\<close>
    definition sort_by_inf :: "mec_mapc \<Rightarrow> mec_mapc nres" where "sort_by_inf = (\<lambda>(n,M). do{
      let xs = Map.empty;
      (_,c,xs,M) \<leftarrow> WHILET (\<lambda> (u,c,xs,M). u < N) (\<lambda> (u,c,xs,M). do{
        ASSERT(\<exists>i. M u = Some (LIST1 i) \<and> Suc u \<le> N);
        let x = id1 (the (M u));
        ASSERT(x < n);
        if(xs x = None) then do{
          ASSERT(c < L\<^sub>1 \<and> u < N \<and> x < n);
          RETURN (Suc u,Suc c,xs(x\<mapsto>c),M(u\<mapsto>LIST1 c))
        } else do{
          ASSERT (u < N \<and> (\<exists>j. xs x = Some j \<and> j < L\<^sub>1) \<and> x < n);
          RETURN (Suc u,c,xs,M(u\<mapsto>LIST1 (the (xs x))))
        }
      }) (0,0,xs,M);
      RETURN (n,M)
    })"
    sepref_register sort_by_inf :: "mec_mapc' \<Rightarrow> mec_mapc' nres"
  

    lemma t_to_mec_map_\<alpha>: "disj_set_list_tuple_invar (n\<^sub>1,n\<^sub>2,M) \<Longrightarrow>
       mec_map_\<alpha> (t_to_mec_map (n\<^sub>1,n\<^sub>2,M)) = op_antpar_to_mec_map (disj_set_list_tuple_\<alpha> (n\<^sub>1,n\<^sub>2,M))"
      unfolding t_to_mec_map_def op_antpar_to_mec_map_def mec_map_\<alpha>_def disj_set_list_tuple_\<alpha>_def
      by auto

    lemma t_to_mec_map_invar: 
      assumes INV: "disj_set_list_tuple_invar (n\<^sub>1,n\<^sub>2,M)"
      assumes EMP: "\<Union> (set (fst (disj_set_list_tuple_\<alpha> (n\<^sub>1,n\<^sub>2,M)))) = {0..<N}"
      assumes NEMP: "{} \<notin> set (fst (disj_set_list_tuple_\<alpha> (n\<^sub>1,n\<^sub>2,M)))"
      shows "mec_map_invar (t_to_mec_map (n\<^sub>1,n\<^sub>2,M))"
    proof -

      from INV have N1_BOUND: "n\<^sub>1 \<le> L\<^sub>1"
        unfolding disj_set_list_tuple_invar_def by auto

      have NN: "M u \<noteq> None" if "u < N" for u
        using EMP that unfolding disj_set_list_tuple_\<alpha>_def
        by auto

      {
        fix u i
        assume A: "M u = Some i"
        hence UN: "u < N"
          using INV unfolding disj_set_list_tuple_invar_def
          by(auto split: option.splits)
        have "\<forall> j. i \<noteq> LIST2 j"
        proof(rule ccontr)
          assume "\<not>(\<forall>j. i \<noteq> LIST2 j)"
          then obtain j where "i = LIST2 j"
            by presburger
          moreover from A EMP UN obtain k where "i = LIST1 k"
            apply (clarsimp simp: disj_set_list_tuple_\<alpha>_def ) 
            by (metis (mono_tags, lifting) UN_E atLeastLessThan_iff mem_Collect_eq option.inject
                zero_le)
          ultimately show False by blast
        qed
      } note AUX = this

      have AUX1: "i < n\<^sub>1 \<Longrightarrow> \<exists>v<N. M v = Some (LIST1 i)" for i
      proof(rule ccontr)
        assume IN: "i < n\<^sub>1" and "\<not>(\<exists>v<N. M v = Some (LIST1 i))"
        with INV have  "{v. M v = Some (LIST1 i)} = {}"
          by (auto simp: disj_set_list_tuple_invar_def split: option.splits)
        with IN have "{} \<in> (\<lambda>x. {v. M v = Some (LIST1 x)}) ` {0..<n\<^sub>1}"
          by force
        thus False
          using NEMP 
          by(auto simp: disj_set_list_tuple_\<alpha>_def)
      qed

      have AUX2: "M v = None \<Longrightarrow> N \<le> v" for v
        using NN leI by blast
      have AUX3: "M v = Some (LIST1 i) \<Longrightarrow> i < n\<^sub>1" for v i
        using assms(1) disj_set_list_tuple_defs.disj_set_list_tuple_invarD1 by blast
      have AUX4: "M v = Some (LIST1 i) \<Longrightarrow> v < N" for v i 
        using EMP \<open>\<And>v i. M v = Some (LIST1 i) \<Longrightarrow> i < n\<^sub>1\<close>
        unfolding disj_set_list_tuple_\<alpha>_def by auto
      have AUX5: "M v = Some (LIST2 i) \<Longrightarrow> False" for v i
        using AUX by blast

      show ?thesis
        unfolding t_to_mec_map_def mec_map_invar_def 
        by(auto split: option.splits tuple_list_id.splits simp: N1_BOUND NN AUX1 AUX2 AUX3 AUX4 dest: AUX5) 
    qed

    lemma eq_mec_member_\<alpha>:  "mec_map_invar (n, M) \<Longrightarrow> i < length (mec_map_\<alpha> (n, M)) \<Longrightarrow> v \<in> mec_map_\<alpha> (n, M) ! i \<Longrightarrow>
        j < length (mec_map_\<alpha> (n, M)) \<Longrightarrow> w \<in> mec_map_\<alpha> (n, M) ! j \<Longrightarrow> eq_mec_member (n, M) v w \<longleftrightarrow> op_in_eq_mec (mec_map_\<alpha> (n, M)) v w"
      unfolding eq_mec_member_def op_in_eq_mec_def mec_map_\<alpha>_def
      by auto

    lemma mec_index_of_\<alpha>:
      assumes PRE: "mec_map_eq_mec_mem_pre (mec_map_\<alpha> (n, M)) v"
      shows "mec_index_of (n, M) v = op_mec_index_of (mec_map_\<alpha> (n, M)) v"
    proof -
      from PRE obtain i where i: "i < n" "M v = Some (LIST1 i)"
        unfolding mec_map_eq_mec_mem_pre_def mec_map_\<alpha>_def by auto
      have "(THE i'. i' < length (mec_map_\<alpha> (n, M)) \<and> v \<in> mec_map_\<alpha> (n, M) ! i') = i"
      proof (rule the_equality)
        show "i < length (mec_map_\<alpha> (n, M)) \<and> v \<in> mec_map_\<alpha> (n, M) ! i"
          using i unfolding mec_map_\<alpha>_def by auto
      next
        fix i' assume "i' < length (mec_map_\<alpha> (n, M)) \<and> v \<in> mec_map_\<alpha> (n, M) ! i'"
        then have "M v = Some (LIST1 i')" unfolding mec_map_\<alpha>_def by auto
        with i show "i' = i" by simp
      qed
      then show ?thesis
        unfolding mec_index_of_def op_mec_index_of_def
        using i by (simp add: op_map_lookup_def of_LIST1_def)
    qed


    definition(in -) "op_antpar_to_mec_map_pre N = (\<lambda>(XS,YS). {} \<notin> set XS \<and> \<Union>(set XS)={0..<N})"
    lemma t_to_mec_map_correct: "(t_to_mec_map, op_antpar_to_mec_map) \<in> [op_antpar_to_mec_map_pre N]\<^sub>f disj_set_list_tuple_rel \<rightarrow> mec_map_rel"
      unfolding disj_set_list_tuple_rel_def mec_map_rel_def op_antpar_to_mec_map_pre_def using t_to_mec_map_invar
      by(auto intro!: t_to_mec_map_invar frefI simp: in_br_conv t_to_mec_map_\<alpha> disj_set_list_tuple_\<alpha>_def)

    lemma mec_map_len_correct: "(mec_map_len, op_mec_map_length) \<in> mec_map_rel \<rightarrow> nat_rel"
      unfolding mec_map_rel_def mec_map_len_def op_mec_map_length_def mec_map_\<alpha>_def
      by(auto simp: in_br_conv)

    lemma eq_mec_member_correct: "(uncurry2 eq_mec_member, uncurry2 op_in_eq_mec) \<in> [\<lambda> ((XS,v),w). mec_map_eq_mec_mem_pre XS v \<and> mec_map_eq_mec_mem_pre XS w]\<^sub>f ((mec_map_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel) \<rightarrow> bool_rel"
      unfolding mec_map_rel_def mec_map_eq_mec_mem_pre_def
      by(auto intro!: frefI simp: in_br_conv eq_mec_member_\<alpha>)

    lemma mec_index_of_correct: "(uncurry mec_index_of, uncurry op_mec_index_of) \<in> [\<lambda> (XS,v). mec_map_eq_mec_mem_pre XS v]\<^sub>f (mec_map_rel \<times>\<^sub>r nat_rel) \<rightarrow> nat_rel"
      unfolding mec_map_rel_def
      by(auto intro!: frefI simp: in_br_conv mec_index_of_\<alpha>)

    lemma sort_by_inf_correct: "(sort_by_inf, RETURN o op_sort_by_inf) \<in> mec_map_rel \<rightarrow> \<langle>mec_map_rel\<rangle>nres_rel"
    proof -

      have forall_Suc_AUX: "\<forall>u<v. P u \<Longrightarrow> Q v \<Longrightarrow> (\<And>u. u < v \<Longrightarrow> P u \<Longrightarrow> Q u) \<Longrightarrow> \<forall>u<Suc v. Q u" for P Q v
        apply clarsimp
        subgoal for u
          apply(cases "u=v")
          by auto
        done

      have leq_Suc_AUX: "b < Suc a \<Longrightarrow> a \<le> b \<Longrightarrow> b = a" for a b
        by linarith

      {
        fix n\<^sub>0 M\<^sub>0 XS
        assume REL: "((n\<^sub>0,M\<^sub>0), XS) \<in> mec_map_rel" 
        hence XS: "XS = mec_map_\<alpha> (n\<^sub>0, M\<^sub>0)" and INV: "mec_map_invar (n\<^sub>0, M\<^sub>0)"
          unfolding mec_map_rel_def
          by(auto simp: in_br_conv)
        hence N0: "n\<^sub>0 = length XS"
          unfolding mec_map_\<alpha>_def by auto

        from INV have M\<^sub>0_Ex_i: "(\<And>i. M\<^sub>0 v = Some (LIST1 i) \<Longrightarrow> i < n\<^sub>0 \<Longrightarrow> P) \<Longrightarrow> P" if "v < N" for P v
          unfolding mec_map_invar_def using that
          apply clarsimp
          apply(erule allE[where ?x=v])
          by (auto split: option.splits tuple_list_id.splits) 

        define inf_sorts_M :: "(nat \<Rightarrow> tuple_list_id option) \<Rightarrow> bool" where 
          "inf_sorts_M = (\<lambda> M. (\<forall> i j. i \<le> j \<longrightarrow> j < n\<^sub>0 \<longrightarrow>
            (\<exists> u < N. M u = Some (LIST1 i) \<and> (\<forall> v < N. M v = Some (LIST1 j) \<longrightarrow> u \<le> v))))"

        define eq_mset_M where
          "eq_mset_M = (\<lambda> M xs. \<forall>v < N. M v = Some (LIST1 (the (xs (id1 (the (M\<^sub>0 v)))))))"

        define xs_welldef where 
          "xs_welldef = (\<lambda>xs::(nat \<Rightarrow> nat option). (\<forall>i < n\<^sub>0. \<exists> j < n\<^sub>0. xs j = Some i) 
            \<and> (\<forall>i < n\<^sub>0. \<exists> j < n\<^sub>0. xs i = Some j) \<and> (\<forall>i1 i2 j. xs i1 = Some j \<longrightarrow> xs i2 = Some j \<longrightarrow> i1 = i2))"

        have xs_welldef_bij: "xs_welldef xs \<Longrightarrow> bij_betw (the o xs) {0..<n\<^sub>0} {0..<n\<^sub>0}" for xs
          unfolding xs_welldef_def by(force intro!: fin_eq_image_bij_betw)

        have M_M\<^sub>0_eq_part: "M v = Some (LIST1 (the (xs i))) \<longleftrightarrow> M\<^sub>0 v = Some (LIST1 i)"
          if EM: "eq_mset_M M xs" and WD: "xs_welldef xs" and VN: "v < N" and IN: "i < n\<^sub>0" for v i M xs
        proof(cases "i = id1 (the (M\<^sub>0 v))")
          case True
          hence "M\<^sub>0 v = Some (LIST1 i)"
            using VN by(auto elim: M\<^sub>0_Ex_i)
          moreover from EM VN True have "M v = Some (LIST1 (the (xs i)))"
            unfolding eq_mset_M_def by presburger
          ultimately show ?thesis 
            by presburger
        next
          case False
          obtain i' where 1: "M\<^sub>0 v = Some (LIST1 i')" and IN': "i' < n\<^sub>0"
            using M\<^sub>0_Ex_i VN by blast
          with False have NEQ: "i' \<noteq> i"
            by fastforce
          moreover have "M v \<noteq> Some (LIST1 (the (xs i)))"
          proof(rule notI)
            assume "M v = Some (LIST1 (the (xs i)))"
            moreover obtain j where C1: "xs i = Some j"
              using WD IN unfolding xs_welldef_def by blast
            ultimately have M: "M v = Some (LIST1 j)" 
              by simp

            from EM have "M v = Some (LIST1 (the (xs i')))"
              unfolding eq_mset_M_def using VN 1 by simp
            moreover obtain j' where C2: "xs i' = Some j'" 
              using WD IN' unfolding xs_welldef_def by blast
            ultimately have "j' = j" using M by auto
            with WD C1 C2 have "i' = i"
              unfolding xs_welldef_def by presburger
            thus False using NEQ by presburger
          qed
          moreover from False have "M\<^sub>0 v \<noteq> Some (LIST1 i)"
            using VN by(auto elim: M\<^sub>0_Ex_i)
              
          ultimately show ?thesis by presburger
        qed 

        define xs_full where
          "xs_full = (\<lambda> xs i. if i < n\<^sub>0 then the (xs i) else i)"

        have xs_full_upt_nth: "xs_welldef xs \<Longrightarrow> i < length XS \<Longrightarrow> [0..<length XS] ! xs_full xs i = the (xs i)" for xs i
          unfolding xs_full_def xs_welldef_def
          by (auto simp: N0)

        have xs_full_permutes: "xs_welldef xs \<Longrightarrow> (xs_full xs) permutes {..<length XS}" for xs
          apply(rule bij_imp_permutes)
          subgoal by(auto simp: atLeast0LessThan xs_full_def simp flip: N0 
            dest!: xs_welldef_bij elim!: bij_betw_eq_dom) 
          subgoal unfolding xs_full_def by(auto simp: N0) 
          done

        have "sort_by_inf (n\<^sub>0,M\<^sub>0) \<le> SPEC (\<lambda>(n,M). n = n\<^sub>0 \<and> mec_map_invar (n\<^sub>0, M) \<and> inf_sorts_M M \<and> (\<exists> xs. eq_mset_M M xs \<and> xs_welldef xs))"
        proof -

          define inf_sorts_M_inv :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> tuple_list_id option) \<Rightarrow> bool" where 
            "inf_sorts_M_inv = (\<lambda> u c M. (\<forall> i j. i \<le> j \<longrightarrow> j < c \<longrightarrow>
              (\<exists> v < u. M v = Some (LIST1 i) \<and> (\<forall> w < u. M w = Some (LIST1 j) \<longrightarrow> v \<le> w))))"

          define eq_mset_M_inv where
            "eq_mset_M_inv = (\<lambda> u M xs. \<forall>v < N. if v < u 
              then (case (xs (id1 (the (M\<^sub>0 v)))) of Some j \<Rightarrow> M v =  Some (LIST1 j) | None \<Rightarrow> False)
              else M v = M\<^sub>0 v)"

          define xs_welldef_inv where 
            "xs_welldef_inv = (\<lambda> u c xs::(nat \<Rightarrow> nat option). 
              (\<forall>j. if j < c then \<exists> i < n\<^sub>0. xs i = Some j else \<forall>i. xs i \<noteq> Some j) \<comment> \<open>\<close>
              \<and> (\<forall>v < u. let i = id1 (the (M\<^sub>0 v)) in \<exists> j < c. xs i = Some j)
              \<and> (\<forall>i1 i2 j. xs i1 = Some j \<longrightarrow> xs i2 = Some j \<longrightarrow> i1 = i2))"

          define mec_map_inv where 
            "mec_map_inv = (\<lambda> c M. n\<^sub>0 \<le> L\<^sub>1 \<and> (\<forall> v. case M v of Some lv \<Rightarrow> (case lv of LIST1 i \<Rightarrow> i < n\<^sub>0 \<and> v < N | LIST2 j \<Rightarrow> False) | None \<Rightarrow> v \<ge> N) \<and> (\<forall>i < c. \<exists> v < N. M v = Some (LIST1 i)))"

          define c_eq where
            "c_eq = (\<lambda> u c. c = card {i. \<exists>v::nat < u. M\<^sub>0 v = Some (LIST1 i)})"

          have xs_welldef_invD1: "xs_welldef_inv u c xs \<Longrightarrow> if j < c then \<exists> i < n\<^sub>0. xs i = Some j else \<forall>i. xs i \<noteq> Some j" for j u c xs
            unfolding xs_welldef_inv_def by presburger

          have xs_welldef_invD2: "xs_welldef_inv u c xs \<Longrightarrow> v < u \<Longrightarrow> \<exists> j < c. xs (id1 (the (M\<^sub>0 v))) = Some j" for v u c xs
            unfolding xs_welldef_inv_def by presburger

          have c_leq_n: "c \<le> n\<^sub>0" if "u \<le> N" and "c_eq u c" for u c
          proof -
            have "{i. \<exists>v<u. M\<^sub>0 v = Some (LIST1 i)} \<subseteq> {i. \<exists>v<N. M\<^sub>0 v = Some (LIST1 i)}"
              using that(1) by force

            show ?thesis
              using mec_map_invar_card[OF INV] that not_finite_existsD unfolding c_eq_def 
              by(fastforce intro!: card_mono) 
          qed

          have c_eq_N: "c = n\<^sub>0" if C: "c_eq N c" for c
            using C INV unfolding c_eq_def mec_map_invar_def
            apply (clarsimp split: option.splits tuple_list_id.splits) 
            by (smt (verit, ccfv_threshold) Collect_cong card_Collect_less_nat order_refl)

          have ran_xs: "ran xs = {..<c}" if "xs_welldef_inv u c xs" for u c xs
            using that unfolding ran_def xs_welldef_inv_def by (auto split: if_splits)

          have xs_uniq: "i1 = i2" if WD: "xs_welldef_inv u c xs"
            and X1: "xs i1 = Some j" and X2: "xs i2 = Some j" for i1 i2 j u c xs
            using that unfolding xs_welldef_inv_def by presburger

          have dom_xs: "dom xs \<subseteq> {..<n\<^sub>0}" if WD: "xs_welldef_inv u c xs" for u c xs
            using WD unfolding xs_welldef_inv_def by (clarsimp; metis)

          have M_Ex_v: "inf_sorts_M_inv u c M \<Longrightarrow> i < c \<Longrightarrow> (\<And>v. v < u \<Longrightarrow> M v = Some (LIST1 i) \<Longrightarrow> P) \<Longrightarrow> P" for i u c M P
            using ran_xs unfolding inf_sorts_M_inv_def by blast

          have M\<^sub>0_Ex_v: "(\<And>v. v < u \<Longrightarrow> M\<^sub>0 v = Some (LIST1 i) \<Longrightarrow> P) \<Longrightarrow> P" if WD: "xs_welldef_inv u c xs" 
            and IS:"inf_sorts_M_inv u c M" and EM: "eq_mset_M_inv u M xs" and XSJ: "xs i = Some j" and UN: "u < N" for P xs i j u c M
          proof(rule M_Ex_v[OF IS, of j])
            from XSJ show "j < c" using ran_xs[OF WD]
              unfolding ran_def by blast
          next
            fix v
            assume VU: "v < u" and MV: "M v = Some (LIST1 j)" and A: "(\<And>v. v < u \<Longrightarrow> M\<^sub>0 v = Some (LIST1 i) \<Longrightarrow> P)"
            have "j < c" 
              by (metis WD that(4) xs_welldef_inv_def)
            with WD XSJ have "i < n\<^sub>0" unfolding xs_welldef_inv_def
              using xs_uniq[OF WD] by metis
            with VU MV have "M\<^sub>0 v = Some (LIST1 i)"
              using WD EM XSJ UN unfolding eq_mset_M_inv_def xs_welldef_inv_def
              by (force split: option.splits if_splits intro: M\<^sub>0_Ex_i[of v]) 
            thus P
              by(auto intro!: VU A)
          qed

          have c_card_dom_xs: "c = card (dom xs)" if C: "c_eq u c" and WD: "xs_welldef_inv u c xs" 
            and IS:"inf_sorts_M_inv u c M" and EM: "eq_mset_M_inv u M xs" and UN: "u < N"  for u c xs M
          proof -
            have "dom xs = {i. \<exists>v::nat < u. M\<^sub>0 v = Some (LIST1 i)}"
              using WD unfolding xs_welldef_inv_def 
              by (auto elim: M\<^sub>0_Ex_v[OF WD IS EM _ UN])

            with C show ?thesis
              unfolding c_eq_def by presburger
          qed

          have c_lt_n\<^sub>0: "c < n\<^sub>0" if C: "c_eq u c" and I: "xs i = None" "i < n\<^sub>0" and WD: "xs_welldef_inv u c xs" 
            and IS:"inf_sorts_M_inv u c M" and EM: "eq_mset_M_inv u M xs" and UN: "u < N" for u c i xs M 
          proof -
            have "dom xs \<subseteq> {..<n\<^sub>0} - {i}"
              using dom_xs[OF WD] I by blast
            hence "card (dom xs) \<le> card {..<n\<^sub>0} - card {i}"
              by(subst card_Diff_subset[symmetric]; fastforce simp: I intro: card_mono)+
            thus ?thesis using c_card_dom_xs[OF C WD IS EM UN]
              using I(2) by auto
          qed

          have xs_Ex_i: "(\<And>i. xs i = Some j \<Longrightarrow> P) \<Longrightarrow> P" if VU: "v < u" and UN: "u < N" and MVJ: "M v = Some (LIST1 j)"
            and WD: "xs_welldef_inv u c xs" and EM: "eq_mset_M_inv u M xs" for P u v j c xs M (*Sledgehammer timeout inconsistency example*)
          proof-
            assume A: "(\<And>i. xs i = Some j \<Longrightarrow> P)"

            obtain j' where "M\<^sub>0 v = Some (LIST1 j')" 
              using INV VU UN unfolding mec_map_invar_def 
              by (clarsimp split: option.splits tuple_list_id.splits; metis not_le order_trans_rules(19) tuple_list_id.exhaust_sel)

            with WD VU EM UN have "M v = Some (LIST1 (the (xs j')))"
              using mec_map_invar_Some[OF INV] unfolding eq_mset_M_inv_def xs_welldef_inv_def 
              by (force split: option.splits if_splits) 

            with MVJ have "xs j' = Some j" 
              using \<open>M\<^sub>0 v = Some (LIST1 j')\<close> that(1,4) xs_welldef_inv_def by fastforce

            with A show P
              by blast
          qed

          have M_not_eq_v: "M v \<noteq> Some (LIST1 c)" if VU: "v < u" and UN: "u < N"
            and WD: "xs_welldef_inv u c xs" and EM: "eq_mset_M_inv u M xs" for u v c xs M
          proof(rule notI)
            assume "M v = Some (LIST1 c)"
            then obtain i where "xs i = Some c"
              using xs_Ex_i[OF VU UN _ WD EM] by blast
            thus False 
              using WD[unfolded xs_welldef_inv_def] by force
          qed

          have xs_welldef_inv_prog: "xs_welldef_inv u\<^sub>1 c\<^sub>1 xs\<^sub>1" if WD: "xs_welldef_inv u\<^sub>0 c\<^sub>0 xs\<^sub>0" and UL: "u\<^sub>0 \<le> u\<^sub>1" and CL: "c\<^sub>0 \<le> c\<^sub>1" 
            and DL: "(\<And>i. i \<in> dom xs\<^sub>0 \<Longrightarrow> xs\<^sub>0 i = xs\<^sub>1 i)" and P1a: "(\<And>j. c\<^sub>0 \<le> j \<Longrightarrow> j < c\<^sub>1 \<Longrightarrow> \<exists>i<n\<^sub>0. xs\<^sub>1 i = Some j)"
            and P1b: "(\<And>i j. c\<^sub>1 \<le> j \<Longrightarrow> xs\<^sub>1 i = Some j \<Longrightarrow> False)"
            and P2: "(\<And>v. v < u\<^sub>1 \<Longrightarrow> u\<^sub>0 \<le> v \<Longrightarrow> \<exists>j<c\<^sub>1. xs\<^sub>1 (id1 (the (M\<^sub>0 v))) = Some j)"
            and P3a: "(\<And>i j. i \<notin> dom xs\<^sub>0 \<Longrightarrow> xs\<^sub>1 i = Some j \<Longrightarrow> j \<ge> c\<^sub>0)"
            and P3b: "(\<And>i1 i2 j. xs\<^sub>1 i1 = Some j \<Longrightarrow> xs\<^sub>1 i2 = Some j \<Longrightarrow> i1 \<notin> dom xs\<^sub>0 \<Longrightarrow> i2 \<notin> dom xs\<^sub>0 \<Longrightarrow> i1 = i2)"
            for u\<^sub>0 c\<^sub>0 xs\<^sub>0 u\<^sub>1 c\<^sub>1 xs\<^sub>1
            unfolding xs_welldef_inv_def
            apply(intro conjI)
            subgoal 
              apply(rule allI)
              subgoal for j
                apply(cases "j < c\<^sub>0")
                subgoal
                  using CL xs_welldef_invD1[OF WD, of j] DL 
                  by (force simp: xs_welldef_inv_def split: if_splits)
                subgoal
                  by (auto simp: not_less intro: P1a elim: P1b) 
                done
              done
            subgoal
              apply(rule allI; rule impI)
              subgoal for v
                apply(cases "v < u\<^sub>0")
                subgoal
                  using CL DL by (force dest!: xs_welldef_invD2[OF WD])
                subgoal
                  by (auto simp: not_less P2) 
                done
              done
            subgoal
              apply(intro allI; intro impI)
              subgoal for i1 i2 j
                apply(cases "i1 \<in> dom xs\<^sub>0"; cases "i2 \<in> dom xs\<^sub>0")
                subgoal
                  using DL xs_uniq[OF WD] by presburger
                subgoal
                  using P3a[of i2 j] 
                  by (metis le_def WD DL xs_welldef_invD1)
                subgoal
                  using P3a[of i1 j]
                  by (metis le_def WD DL xs_welldef_invD1)
                subgoal using P3b .
                done
              done
            done

          have c_eq_prog: "c_eq (Suc u) c'" 
          if C: "c_eq u c" and EM: "eq_mset_M_inv u M xs" and UN: "u < N" and MU: "M u = Some (LIST1 i)" 
          and C': "c' = (if \<exists>v<u. M\<^sub>0 v = Some (LIST1 i) then c else Suc c)"for u c c' xs M i
          proof -

            from INV have *: "finite {i. \<exists>v<u. M\<^sub>0 v = Some (LIST1 i)}"
              unfolding mec_map_invar_def by (auto 5 0 split: option.splits tuple_list_id.splits simp: finite_nat_set_iff_bounded)

            have "{i'. \<exists>v<Suc u. M\<^sub>0 v = Some (LIST1 i')} = insert i {i'. \<exists>v<u. M\<^sub>0 v = Some (LIST1 i')}"
            proof safe 
              fix i' v
              assume ASM: "i' \<noteq> i" "v < Suc u" "M\<^sub>0 v = Some (LIST1 i')"

              moreover from MU EM have "M\<^sub>0 u = Some (LIST1 i)"
                unfolding eq_mset_M_inv_def
                by(auto simp: UN split: if_splits option.splits tuple_list_id.splits) 
              ultimately have "v \<noteq> u" by force
              thus "\<exists>v<u. M\<^sub>0 v = Some (LIST1 i')"
                using ASM by force
            next
              from MU EM have "M\<^sub>0 u = Some (LIST1 i)"
                unfolding eq_mset_M_inv_def
                by(auto simp: UN split: if_splits option.splits tuple_list_id.splits)
              thus "\<exists>v<Suc u. M\<^sub>0 v = Some (LIST1 i)"
                by blast
            next
              fix v i'
              assume "v < u" "M\<^sub>0 v = Some (LIST1 i')"
              thus "\<exists>v<Suc u. M\<^sub>0 v = Some (LIST1 i')"
                by(auto intro!: exI[where ?x=v])
            qed

            with C C' show ?thesis
              unfolding c_eq_def
              by (auto split: if_splits simp: card_insert_if *)
          qed

          have I1: "inf_sorts_M_inv 0 0 M\<^sub>0"
            unfolding inf_sorts_M_inv_def by blast
          have I2: "eq_mset_M_inv 0 M\<^sub>0 (\<lambda>x. None)"
            unfolding eq_mset_M_inv_def by presburger
          have I3: "xs_welldef_inv 0 0 (\<lambda>x. None)"
            unfolding xs_welldef_inv_def by fastforce
          have I4: "mec_map_inv 0 M\<^sub>0"
            using INV unfolding mec_map_invar_def mec_map_inv_def
            by fast
          have I5: "c_eq 0 0"
            unfolding c_eq_def by simp

          have A1: "u < N \<Longrightarrow> mec_map_inv c M \<Longrightarrow> \<exists>y. M u = Some (LIST1 y)" for u c M
            unfolding mec_map_inv_def 
            by (clarsimp split: option.splits tuple_list_id.splits; metis le_def tuple_list_id.exhaust)

          have A2: "u < N \<Longrightarrow> xs i = None \<Longrightarrow> M u = Some (LIST1 i) \<Longrightarrow> inf_sorts_M_inv u c M \<Longrightarrow> mec_map_inv c M \<Longrightarrow>
            eq_mset_M_inv u M xs \<Longrightarrow> xs_welldef_inv u c xs \<Longrightarrow> c_eq u c \<Longrightarrow> c < L\<^sub>1" for u c M xs i
            apply(rule less_le_trans[of _ n\<^sub>0])
            subgoal using M\<^sub>0_Ex_i by(force simp: eq_mset_M_inv_def intro!: Suc_leI elim!: c_lt_n\<^sub>0)
            subgoal unfolding mec_map_inv_def by presburger
            done

          have A3: "M u = Some (LIST1 i) \<Longrightarrow> mec_map_inv c M \<Longrightarrow> i < n\<^sub>0" for u c i M
            unfolding mec_map_inv_def by(auto split: option.splits tuple_list_id.splits)

          have A4: "u < N \<Longrightarrow> xs i = Some y \<Longrightarrow> mec_map_inv c M \<Longrightarrow> xs_welldef_inv u c xs \<Longrightarrow> c_eq u c \<Longrightarrow> y < L\<^sub>1" for u c i xs M y
            unfolding mec_map_inv_def xs_welldef_inv_def
            apply(rule dual_order.strict_trans1[of n\<^sub>0])
            subgoal by(auto split: option.splits tuple_list_id.splits if_splits) 
            subgoal apply(rule c_leq_n[of u c, THEN order.strict_trans2[rotated]])
              subgoal by linarith
              subgoal by argo
              subgoal by metis
              done
            done


          have S11: "u < N \<Longrightarrow>
            xs i = None \<Longrightarrow>
            M u = Some (LIST1 i) \<Longrightarrow>
            mec_map_inv c M \<Longrightarrow>
            inf_sorts_M_inv u c M \<Longrightarrow>
            eq_mset_M_inv u M xs \<Longrightarrow>
            xs_welldef_inv u c xs \<Longrightarrow>
            c_eq u c \<Longrightarrow> mec_map_inv (Suc c) (M(u \<mapsto> LIST1 c))" for u c xs M i
            unfolding mec_map_inv_def
            apply clarsimp
            apply(intro conjI)
            subgoal
              apply(auto split: option.splits tuple_list_id.splits intro: c_lt_n\<^sub>0)
              done
            subgoal 
              apply(erule forall_Suc_AUX)
              subgoal 
                by(auto intro: exI[where ?x=u])
              subgoal for i 
                apply(erule M_Ex_v)
                apply assumption
                subgoal for v
                  apply(rule exI[where ?x=v])
                  by linarith
                done
              done
            done

          have S12: "u < N \<Longrightarrow>
            xs i = None \<Longrightarrow>
            M u = Some (LIST1 i) \<Longrightarrow>
            mec_map_inv c M \<Longrightarrow>
            eq_mset_M_inv u M xs \<Longrightarrow>
            xs_welldef_inv u c xs \<Longrightarrow>
            c_eq u c \<Longrightarrow> inf_sorts_M_inv (Suc u) (Suc c) (M(u \<mapsto> LIST1 c))" if IS: "inf_sorts_M_inv u c M" for u c xs M i
            using IS unfolding inf_sorts_M_inv_def apply -
            apply (rule allI)+
            subgoal for i1 j1
              apply(erule allE[where ?x=i1]; erule allE[where ?x=j1])
              apply(cases "j1 = c")
              subgoal 
                apply(cases "i1 = c")
                subgoal 
                  apply clarsimp
                  apply(rule exI[where ?x=u])
                  using M_not_eq_v not_less_less_Suc_eq by blast
                subgoal
                  apply clarsimp
                  apply(rule M_Ex_v[OF IS, of i1])
                  subgoal by presburger
                  subgoal for v
                    apply(rule exI[where ?x=v]) 
                    apply clarsimp
                    using M_not_eq_v not_less_less_Suc_eq by blast
                done
              done
              subgoal 
                apply clarsimp
                subgoal for v
                  by(auto intro: exI[where ?x=v])
                done
              done
            done

          have S13: "xs i = None \<Longrightarrow> M u = Some (LIST1 i) \<Longrightarrow>
            eq_mset_M_inv u M xs \<Longrightarrow> eq_mset_M_inv (Suc u) (M(u \<mapsto> LIST1 c)) (xs(i \<mapsto> c))" for u c xs M i
            unfolding eq_mset_M_inv_def
            by(erule all_forward; auto split: option.splits)

          have S14: "u < N \<Longrightarrow>
            xs i = None \<Longrightarrow>
            M u = Some (LIST1 i) \<Longrightarrow>
            mec_map_inv c M \<Longrightarrow>
            eq_mset_M_inv u M xs \<Longrightarrow>
            xs_welldef_inv (Suc u) (Suc c) (xs(i \<mapsto> c))" if WD: "xs_welldef_inv u c xs" for u c xs M i
            apply(rule xs_welldef_inv_prog[OF WD])
            subgoal by linarith
            subgoal by linarith
            subgoal by auto
            subgoal for j 
              by(auto simp: mec_map_inv_def intro!: exI[where ?x=i] split: option.splits tuple_list_id.splits)
            subgoal for i2 j using xs_welldef_invD1[OF WD] by (auto split: if_splits)
            subgoal for v
              using eq_mset_M_inv_def by (force dest: leq_Suc_AUX[of v u])
            subgoal for i2 j by (auto split: if_splits) 
            subgoal for i2 j
              by (metis domI map_upd_Some_unfold)
            done

          have S15: "u < N \<Longrightarrow> M u = Some (LIST1 i) \<Longrightarrow> xs i = None \<Longrightarrow>
            xs_welldef_inv u c xs \<Longrightarrow> 
            c_eq u c \<Longrightarrow>
            eq_mset_M_inv u M xs \<Longrightarrow> 
            c_eq (Suc u) (Suc c)" for u c xs M i
            by(fastforce dest: xs_welldef_invD2 elim: c_eq_prog) 

          have S21: "u < N \<Longrightarrow>
            M u = Some (LIST1 i) \<Longrightarrow>
            xs i = Some j \<Longrightarrow>
            mec_map_inv c M \<Longrightarrow>
            inf_sorts_M_inv u c M \<Longrightarrow>
            eq_mset_M_inv u M xs \<Longrightarrow>
            xs_welldef_inv u c xs \<Longrightarrow> c_eq u c \<Longrightarrow> mec_map_inv c (M(u \<mapsto> LIST1 j))" for u c xs M i j
            unfolding mec_map_inv_def
            apply(intro conjI)
            subgoal by presburger
            subgoal
              using xs_welldef_invD1[of u c xs j]
              apply(auto split: option.splits tuple_list_id.splits if_splits intro:)
              done
            subgoal (*TODO: Clean up!*)
              by (simp; smt (verit, ccfv_SIG) M_Ex_v ex_least_nat_le less_or_eq_imp_le order.strict_trans2)
            done
            
          have S22: "inf_sorts_M_inv u c M \<Longrightarrow>
            inf_sorts_M_inv (Suc u) c (M(u \<mapsto> LIST1 j))" for u c M j
            unfolding inf_sorts_M_inv_def
            apply safe
            subgoal for i1 j1
              apply(erule allE[where ?x=i1]; erule allE[where ?x=j1])
              apply safe
              subgoal for v
                apply(rule exI[where ?x=v])
                apply safe
                subgoal by linarith
                subgoal by simp
                subgoal for w 
                  by (metis array_rules(2) le_antisym le_def le_simps(2) order_less_not_sym)
                done
              done
            done

          have S23: "u < N \<Longrightarrow>
            M u = Some (LIST1 i) \<Longrightarrow>
            xs i = Some j \<Longrightarrow>
            mec_map_inv c M \<Longrightarrow>
            inf_sorts_M_inv u c M \<Longrightarrow>
            eq_mset_M_inv u M xs \<Longrightarrow>
            xs_welldef_inv u c xs \<Longrightarrow>
            c_eq u c \<Longrightarrow> eq_mset_M_inv (Suc u) (M(u \<mapsto> LIST1 j)) xs" for u c xs M i j
            unfolding eq_mset_M_inv_def
            by(erule all_forward; auto split: option.splits)
          
          have S24: "u < N \<Longrightarrow>
            M u = Some (LIST1 i) \<Longrightarrow>
            xs i = Some j \<Longrightarrow>
            mec_map_inv c M \<Longrightarrow>
            inf_sorts_M_inv u c M \<Longrightarrow>
            eq_mset_M_inv u M xs \<Longrightarrow>
            c_eq u c \<Longrightarrow> xs_welldef_inv (Suc u) c xs" if WD: "xs_welldef_inv u c xs" for u c xs M i j
            apply(rule xs_welldef_inv_prog[OF WD])
            subgoal by linarith
            subgoal by linarith
            subgoal by auto
            subgoal for j by presburger
            subgoal for i2 j using xs_welldef_invD1[OF WD] by auto
            subgoal for v
              using eq_mset_M_inv_def  xs_welldef_invD1[OF WD, of j]
              by(force split: option.splits tuple_list_id.splits if_splits dest: leq_Suc_AUX[of v u])
            subgoal for i2 j by blast 
            subgoal for i2 j by blast
            done

          have S25: "u < N \<Longrightarrow>
            M u = Some (LIST1 i) \<Longrightarrow>
            xs i = Some j \<Longrightarrow>
            mec_map_inv c M \<Longrightarrow>
            inf_sorts_M_inv u c M \<Longrightarrow>
            eq_mset_M_inv u M xs \<Longrightarrow>
            xs_welldef_inv u c xs \<Longrightarrow> c_eq u c \<Longrightarrow> c_eq (Suc u) c" for u c xs M i j 
            by(auto elim!: c_eq_prog M\<^sub>0_Ex_v)

          have F1: "mec_map_inv c M \<Longrightarrow>
            inf_sorts_M_inv N c M \<Longrightarrow> eq_mset_M_inv N M xs \<Longrightarrow> xs_welldef_inv N c xs \<Longrightarrow> c_eq N c \<Longrightarrow> mec_map_invar (n\<^sub>0, M)" for c xs M
            unfolding mec_map_inv_def mec_map_invar_def
            by(auto dest: c_eq_N)

          have F2: "inf_sorts_M_inv N n\<^sub>0 M \<Longrightarrow> inf_sorts_M M" for M
            unfolding inf_sorts_M_inv_def inf_sorts_M_def by blast
          
          have F3: "eq_mset_M_inv N M xs \<Longrightarrow> eq_mset_M M xs" for xs M
            unfolding eq_mset_M_inv_def eq_mset_M_def
            by(auto split: option.splits) 

          have F4: "xs_welldef_inv N n\<^sub>0 xs \<Longrightarrow> xs_welldef xs" for xs
            unfolding xs_welldef_inv_def xs_welldef_def 
            using mec_map_invarD3[OF INV] 
            by fastforce

          show ?thesis 
            unfolding sort_by_inf_def
            apply(refine_vcg WHILET_rule[where ?I="\<lambda>(u, c, xs, M). u \<le> N
              \<and> mec_map_inv c M
              \<and> inf_sorts_M_inv u c M
              \<and> eq_mset_M_inv u M xs
              \<and> xs_welldef_inv u c xs
              \<and> c_eq u c"
              and ?R="measure(\<lambda>(u,_). N-u)"])
            apply (vc_solve solve: INV I1 I2 I3 I4 I5 A1 )
            subgoal using A3 by blast
            subgoal using A2 by blast
            subgoal using S11 by blast 
            subgoal using S12 by blast
            subgoal using S13 by blast
            subgoal using S14 by blast
            subgoal using S15 by blast
            subgoal by linarith
            subgoal using A4 by blast
            subgoal using S21 by blast
            subgoal using S22 by blast
            subgoal using S23 by blast
            subgoal using S24 by blast
            subgoal using S25 by blast
            subgoal by linarith
            subgoal by(auto intro: F1)
            subgoal by(auto dest: c_eq_N intro: F2)
            subgoal by(auto dest: c_eq_N intro: F3 F4)
            done
  
        qed

        also have "... \<le> \<Down> mec_map_rel (RETURN (op_sort_by_inf XS))"
        proof -

          have AUX1: "inj_on Inf (set (map ((`) enat) XS)) \<Longrightarrow> inj_on ((Inf \<circ>\<circ> (`)) enat) (set XS)"
            unfolding inj_on_def
            apply clarsimp 
            by (meson inj_enat inj_image_eq_iff)

          have mec_map_permute: "XS = permute_list (xs_full xs) (mec_map_\<alpha> (n\<^sub>0, M))" 
            if MMI: "mec_map_invar (n\<^sub>0, M)" and WD: "xs_welldef xs" and EM: "eq_mset_M M xs" for M xs
            unfolding mec_map_\<alpha>_def XS using mec_map_invar_Some[OF MMI]
            by (force simp: M_M\<^sub>0_eq_part[OF EM WD] N0 xs_full_permutes[OF WD] 
              permute_list_map permute_list_nth xs_full_upt_nth[OF WD]  mec_map_invar_Some[OF INV] 
              intro!: nth_equalityI) 

          have F1: "mec_map_invar (n\<^sub>0, M) \<Longrightarrow> eq_mset_M M xs \<Longrightarrow> xs_welldef xs \<Longrightarrow> mset XS = mset (mec_map_\<alpha> (n\<^sub>0, M))" for M xs
            apply(clarsimp simp: mec_map_permute)
            apply(rule mset_permute_list)
            apply(auto simp: mec_map_\<alpha>_def elim: xs_full_permutes[folded N0])
            done

          have F2: "inj_on Inf (set XS)"
            using mec_map_invarD3[OF INV]
            by(auto simp: XS mec_map_\<alpha>_def intro!: inj_on_nat_Inf) 

          have F3: "sorted (map Inf (mec_map_\<alpha> (n\<^sub>0, M)))" if MMI: "mec_map_invar (n\<^sub>0, M)" and ISM: "inf_sorts_M M" for M
            apply(clarsimp simp: sorted_iff_nth_mono mec_map_\<alpha>_def inf_sorts_M_def eq_mset_M_def intro!: Inf_mono)
            apply(rule cInf_mono)
            subgoal using inf_sorts_M_def that(2) by blast
            subgoal by force
            subgoal for i j u
              apply(rule mec_map_invarD3[OF MMI, THEN allE[where ?x=i]])
              apply clarsimp
              subgoal for v
                using ISM[unfolded inf_sorts_M_def] mec_map_invar_Some[OF MMI] by fast
              done
            done

          show ?thesis
            unfolding conc_fun_RETURN mec_map_rel_def op_sort_by_inf_def
            by(auto simp: F1 F2 F3 in_br_conv intro!: sort_key_inj_key_eq)
        qed

        finally have "sort_by_inf (n\<^sub>0, M\<^sub>0) \<le> \<Down> mec_map_rel (RETURN (op_sort_by_inf XS))" .
      } note AUX=this


      thus ?thesis
        apply(refine_vcg)
        by auto
    qed

  end

    
  section \<open>Code Generation\<close>

  context disj_set_list_tuple_defs
  begin


    definition "mec_map_assn_raw = size_assn \<times>\<^sub>a disj_set_list_tuple_defs.tuple_list_id_am_assn L\<^sub>1 N"

    definition "mec_map_assn = hr_comp mec_map_assn_raw mec_map_rel"

    schematic_goal[sepref_frame_free_rules]: "MK_FREE mec_map_assn ?A"
      unfolding mec_map_assn_def mec_map_assn_raw_def tuple_list_id_am_assn_def
      by(rule sepref_frame_free_rules | rule mk_free_pair)+


    abbreviation size_am_assn :: "nat \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> 64 Word.word ptr \<Rightarrow> llvm_amemory \<Rightarrow> bool" where "size_am_assn n \<equiv> snat.am_assn n"

    definition "sbi_assn n = size_assn \<times>\<^sub>a size_assn \<times>\<^sub>a size_am_assn n \<times>\<^sub>a tuple_list_id_am_assn"



    definition open_mec_map :: "mec_mapc \<Rightarrow> nat \<times> (nat \<rightharpoonup> tuple_list_id)" where "open_mec_map = (\<lambda>(n,M). (n,M))"
    sepref_register open_mec_map :: "mec_mapc \<Rightarrow> nat \<times> (nat, tuple_list_id) i_map"

    definition close_mec_map :: "nat \<Rightarrow> (nat \<rightharpoonup> tuple_list_id) \<Rightarrow> mec_mapc" where"close_mec_map = (\<lambda>n M. (n,M))"
    sepref_register close_mec_map :: "nat \<Rightarrow> (nat, tuple_list_id) i_map \<Rightarrow> mec_mapc"

    type_synonym sbi_state = "nat \<times> nat \<times> (nat \<rightharpoonup> nat) \<times> (nat \<rightharpoonup> tuple_list_id)"

    definition[simp]: "sbi_u = (\<lambda>(u,c,xs,M). u)"
    definition[simp]: "sbi_c = (\<lambda>(u,c,xs,M). c)"
    definition[simp]: "sbi_xs = (\<lambda>(u,c,xs,M). xs)"
    definition[simp]: "sbi_M = (\<lambda>(u,c,xs,M). M)"




    definition sbi_close_state :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<rightharpoonup> nat) \<Rightarrow> (nat \<rightharpoonup> tuple_list_id) \<Rightarrow> sbi_state" where
      "sbi_close_state u c xs M = (u,c,xs,M)"
    sepref_register sbi_close_state :: "nat \<Rightarrow> nat \<Rightarrow> (nat, nat) i_map \<Rightarrow> (nat, tuple_list_id) i_map => sbi_state"

    definition sbi_open_state :: "sbi_state \<Rightarrow> (nat \<times> nat \<times> (nat \<rightharpoonup> nat) \<times> (nat \<rightharpoonup> tuple_list_id))" where
      "sbi_open_state = (\<lambda>(u,c,xs,M). (u,c,xs,M))"
    sepref_register sbi_open_state :: "sbi_state \<Rightarrow> (nat \<times> nat \<times> (nat, nat) i_map \<times> (nat, tuple_list_id) i_map)"

    definition sbi_upd_new :: "sbi_state \<Rightarrow> nat \<Rightarrow> sbi_state nres" where
      "sbi_upd_new = (\<lambda>(u,c,xs,M) x. do{
        RETURN((Suc u), (Suc c), (xs(x\<mapsto>c)), (M(u\<mapsto>to_LIST1 c)))
      })"
    sepref_register sbi_upd_new

    definition sbi_upd_ex :: "sbi_state \<Rightarrow> nat \<Rightarrow> sbi_state nres" where
      "sbi_upd_ex = (\<lambda>(u,c,xs,M) x . do{
        RETURN (Suc u,c,xs,M(u\<mapsto>to_LIST1 (the (xs x))))
      })"
    sepref_register sbi_upd_ex

    definition sbi_is_new :: "sbi_state \<Rightarrow> nat \<Rightarrow> bool" where
      "sbi_is_new = (\<lambda>(u,c,xs,M) x. is_None (xs x))"
    sepref_register sbi_is_new

    definition sbi_get_x :: "sbi_state \<Rightarrow> nat" where
      "sbi_get_x = (\<lambda>(u,c,xs,M). let u' = op_bound_val (\<lambda>u. u < N) u in of_LIST1 (the (M u')))"
    sepref_register sbi_get_x

    definition sbi_has_next :: "sbi_state \<Rightarrow> bool" where
      "sbi_has_next = (\<lambda>(u,c,xs,M). u < N)"
    sepref_register sbi_has_next

    definition sort_by_inf' :: "mec_mapc \<Rightarrow> mec_mapc nres" where "sort_by_inf' = (\<lambda>nM. do{
      let (n,M) = open_mec_map nM;
      let xs = op_am_custom_empty n;
      sbi \<leftarrow> WHILET (\<lambda> sbi. sbi_has_next sbi) (\<lambda> sbi. do{
        ASSERT(\<exists>i. (sbi_M sbi) (sbi_u sbi) = Some (LIST1 i) \<and> Suc (sbi_u sbi) \<le> N);
        let x = sbi_get_x sbi;
        ASSERT(x < n);
        if sbi_is_new sbi x then do{
          ASSERT((sbi_c sbi) < L\<^sub>1 \<and> (sbi_u sbi) < N \<and> x < n);
          sbi_upd_new sbi x
        } else do{
          ASSERT ((sbi_u sbi) < N \<and> (\<exists>j. (sbi_xs sbi) x = Some j \<and> j < L\<^sub>1) \<and> x < n);
          sbi_upd_ex sbi x
        }
      }) (sbi_close_state 0 0 xs M);
      RETURN (let (u,c,xs,M) = sbi_open_state sbi in close_mec_map n M)
    })"

    lemma sort_by_inf_alt: "sort_by_inf = sort_by_inf'"
      unfolding sort_by_inf_def sort_by_inf'_def open_mec_map_def close_mec_map_def
        sbi_get_x_def sbi_is_new_def sbi_upd_new_def sbi_upd_ex_def sbi_close_state_def sbi_open_state_def
        sbi_u_def sbi_c_def sbi_M_def to_LIST1_def of_LIST1_def Let_def sbi_has_next_def op_bound_val_def
      apply(rule ext)
      subgoal for nM
        apply(cases nM)
        apply(clarsimp) 
        apply(rule arg_cong2[where ?f = Refine_Basic.bind])
        subgoal 
          apply(rule arg_cong3[where ?f=WHILET])
          by (auto intro!:arg_cong2[where ?f = Refine_Basic.bind] intro!: ext)
        subgoal by fast
        done
      done




  end

  context disj_set_list_tuple_env
  begin



    lemma N_max_size: "a \<le> N \<Longrightarrow> a < max_snat 64"
      using n_impl in_snat_rel_boundsD by fastforce

    lemma L\<^sub>1_max_size: "a \<le> L\<^sub>1 \<Longrightarrow> a < max_snat 64"
      using l_impl in_snat_rel_boundsD by fastforce

    sepref_definition open_mec_map_ll is "RETURN o open_mec_map" :: "mec_map_assn_raw\<^sup>d \<rightarrow>\<^sub>a size_assn \<times>\<^sub>a tuple_list_id_am_assn"
      unfolding open_mec_map_def mec_map_assn_raw_def
      by sepref
    concrete_definition (in -) open_mec_map_ll' [llvm_code] is disj_set_list_tuple_env.open_mec_map_ll_def
    lemmas [sepref_fr_rules] = open_mec_map_ll.refine[unfolded open_mec_map_ll'.refine[OF disj_set_list_tuple_env_axioms]]

    sepref_definition close_mec_map_ll is "uncurry (RETURN oo close_mec_map)" :: "size_assn\<^sup>d *\<^sub>a tuple_list_id_am_assn\<^sup>d \<rightarrow>\<^sub>a mec_map_assn_raw"
      unfolding close_mec_map_def mec_map_assn_raw_def                                 
      by sepref
    concrete_definition (in -) close_mec_map_ll' [llvm_code] is disj_set_list_tuple_env.close_mec_map_ll_def
    lemmas [sepref_fr_rules] = close_mec_map_ll.refine[unfolded close_mec_map_ll'.refine[OF disj_set_list_tuple_env_axioms]]


    sepref_definition sbi_close_state_ll is "uncurry3 (RETURN oooo sbi_close_state)" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (size_am_assn n)\<^sup>d *\<^sub>a tuple_list_id_am_assn\<^sup>d \<rightarrow>\<^sub>a sbi_assn n" 
      unfolding sbi_close_state_def sbi_assn_def
      apply sepref
      done
    concrete_definition (in -) sbi_close_state_ll' [llvm_code] is disj_set_list_tuple_env.sbi_close_state_ll_def
    lemmas [sepref_fr_rules] = sbi_close_state_ll.refine[unfolded sbi_close_state_ll'.refine[OF disj_set_list_tuple_env_axioms]]

    sepref_definition sbi_open_state_ll is "(RETURN o sbi_open_state)" :: "(sbi_assn n)\<^sup>d \<rightarrow>\<^sub>a size_assn \<times>\<^sub>a size_assn \<times>\<^sub>a (size_am_assn n) \<times>\<^sub>a tuple_list_id_am_assn" 
      unfolding sbi_open_state_def sbi_assn_def
      apply sepref
      done
    concrete_definition (in -) sbi_open_state_ll' [llvm_code] is disj_set_list_tuple_env.sbi_open_state_ll_def
    lemmas [sepref_fr_rules] = sbi_open_state_ll.refine[unfolded sbi_open_state_ll'.refine[OF disj_set_list_tuple_env_axioms]]

    sepref_definition sbi_upd_new_ll is "uncurry sbi_upd_new" :: "[\<lambda>((u,c,xs,M), x). u < N \<and> c < L\<^sub>1 \<and> x < n]\<^sub>a (sbi_assn n)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> sbi_assn n"
      unfolding sbi_upd_new_def sbi_assn_def tuple_list_id_am_assn_def
      supply[simp] = N_max_size L\<^sub>1_max_size 
      apply sepref
      done
    concrete_definition (in -) sbi_upd_new_ll' [llvm_code] is disj_set_list_tuple_env.sbi_upd_new_ll_def
    lemmas [sepref_fr_rules] = sbi_upd_new_ll.refine[unfolded sbi_upd_new_ll'.refine[OF disj_set_list_tuple_env_axioms]]

    sepref_definition sbi_upd_ex_ll is "uncurry sbi_upd_ex" :: "[\<lambda>((u,c,xs,M), x). u < N \<and> (\<exists>j. xs x = Some j \<and> j < L\<^sub>1) \<and> x < n]\<^sub>a (sbi_assn n)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> sbi_assn n"
      unfolding sbi_upd_ex_def sbi_assn_def tuple_list_id_am_assn_def
      supply[simp] = N_max_size L\<^sub>1_max_size 
      apply sepref
      done
    concrete_definition (in -) sbi_upd_ex_ll' [llvm_code] is disj_set_list_tuple_env.sbi_upd_ex_ll_def
    lemmas [sepref_fr_rules] = sbi_upd_ex_ll.refine[unfolded sbi_upd_ex_ll'.refine[OF disj_set_list_tuple_env_axioms]]

    sepref_definition sbi_is_new_ll is "uncurry (RETURN oo sbi_is_new)" :: "[\<lambda>((u,c,xs,M), x). x < n]\<^sub>a (sbi_assn n)\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> bool1_assn"
      unfolding sbi_is_new_def sbi_assn_def
      apply sepref
      done
    concrete_definition (in -) sbi_is_new_ll' [llvm_code] is disj_set_list_tuple_env.sbi_is_new_ll_def
    lemmas [sepref_fr_rules] = sbi_is_new_ll.refine[unfolded sbi_is_new_ll'.refine[OF disj_set_list_tuple_env_axioms]]

    sepref_definition sbi_get_x_ll is "RETURN o (PR_CONST sbi_get_x)" :: "[\<lambda>(u,c,xs,M). u < N \<and> (\<exists>i. M u = Some (LIST1 i))]\<^sub>a (sbi_assn n)\<^sup>k \<rightarrow> size_assn"
      unfolding sbi_get_x_def sbi_assn_def tuple_list_id_am_assn_def PR_CONST_def
      apply sepref
      done
    concrete_definition (in -) sbi_get_x_ll' [llvm_code] is disj_set_list_tuple_env.sbi_get_x_ll_def
    lemmas [sepref_fr_rules] = sbi_get_x_ll.refine[unfolded sbi_get_x_ll'.refine[OF disj_set_list_tuple_env_axioms]]

    sepref_definition sbi_has_next_ll is "RETURN o (PR_CONST sbi_has_next)" :: "(sbi_assn n)\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding sbi_has_next_def sbi_assn_def tuple_list_id_am_assn_def PR_CONST_def
      apply sepref
      done
    concrete_definition (in -) sbi_has_next_ll' [llvm_code] is disj_set_list_tuple_env.sbi_has_next_ll_def
    lemmas [sepref_fr_rules] = sbi_has_next_ll.refine[unfolded sbi_has_next_ll'.refine[OF disj_set_list_tuple_env_axioms]]


    interpretation disj_set_list_defs N .


    sepref_definition t_to_mec_map_ll is "RETURN o t_to_mec_map" :: "disj_set_list_tuple_assn_raw\<^sup>d \<rightarrow>\<^sub>a mec_map_assn_raw"
      unfolding t_to_mec_map_def disj_set_list_tuple_assn_raw_def mec_map_assn_raw_def
      apply sepref
      done
    concrete_definition(in -) t_to_mec_map_ll' [llvm_code] is disj_set_list_tuple_env.t_to_mec_map_ll_def


    sepref_definition mec_map_len_ll is "RETURN o mec_map_len" :: "mec_map_assn_raw\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding mec_map_len_def mec_map_assn_raw_def
      apply sepref
      done
    concrete_definition(in -) mec_map_len_ll' [llvm_code] is disj_set_list_tuple_env.mec_map_len_ll_def


    sepref_definition eq_mec_member_ll is "uncurry2 (RETURN ooo eq_mec_member)" :: "[\<lambda> (((n,M),v),w). M v \<noteq> None \<and> M w \<noteq> None]\<^sub>a mec_map_assn_raw\<^sup>k *\<^sub>a elemt_assn\<^sup>k *\<^sub>a elemt_assn\<^sup>k \<rightarrow> bool1_assn"
      unfolding eq_mec_member_def mec_map_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def
      apply sepref
      done
    concrete_definition(in -) eq_mec_member_ll' [llvm_code] is disj_set_list_tuple_env.eq_mec_member_ll_def

    sepref_definition mec_index_of_ll is "uncurry (RETURN oo mec_index_of)" :: "[\<lambda> ((n,M),v). \<exists>j. M v = Some (LIST1 j)]\<^sub>a mec_map_assn_raw\<^sup>k *\<^sub>a elemt_assn\<^sup>k \<rightarrow> size_assn"
      unfolding mec_index_of_def mec_map_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def
      apply sepref
      done
    concrete_definition(in -) mec_index_of_ll' [llvm_code] is disj_set_list_tuple_env.mec_index_of_ll_def

find_in_thms open_mec_map in sepref_fr_rules
lemma test_AUX: "INDEP (sbi_assn a1')" by simp
find_theorems monadic_WHILEIT
    sepref_definition sort_by_inf_ll is "sort_by_inf'" :: "mec_map_assn_raw\<^sup>d \<rightarrow>\<^sub>a mec_map_assn_raw"
      unfolding sort_by_inf'_def  
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
    concrete_definition(in -) sort_by_inf_ll' [llvm_code] is disj_set_list_tuple_env.sort_by_inf_ll_def
(*
      (*apply sepref_dbg_trans_keep*)
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
apply(rule test_AUX)
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
apply(rule test_AUX)
subgoal 
apply argo
apply blast
find_theorems "_ \<turnstile> _"
thm frame_rem1[of "hn_ctxt (sbi_assn _) _ _"]
      apply sepref_dbg_trans_step_keep
*)

    lemma disj_set_list_tuple_rel_ex_mem: "((n, M), Mm) \<in> mec_map_rel \<Longrightarrow> mec_map_eq_mec_mem_pre Mm b \<Longrightarrow> (\<exists>y. M b = Some y)"
      unfolding mec_map_eq_mec_mem_pre_def mec_map_rel_def mec_map_\<alpha>_def
      by(auto simp: in_br_conv)

    lemma disj_set_list_tuple_rel_ex_mem_LIST1: "((n, M), Mm) \<in> mec_map_rel \<Longrightarrow> mec_map_eq_mec_mem_pre Mm b \<Longrightarrow> (\<exists>j. M b = Some (LIST1 j))"
      unfolding mec_map_eq_mec_mem_pre_def mec_map_rel_def mec_map_\<alpha>_def
      by(auto simp: in_br_conv)

    context
      notes [fcomp_norm_unfold] = mec_map_assn_def[symmetric] disj_set_list_tuple_assn_def[symmetric]
      notes [simp] = disj_set_list_tuple_rel_ex_mem disj_set_list_tuple_rel_ex_mem_LIST1
    begin

      lemmas t_to_mec_map_hnr[sepref_fr_rules] = t_to_mec_map_ll.refine[FCOMP t_to_mec_map_correct, unfolded t_to_mec_map_ll'.refine[OF disj_set_list_tuple_env_axioms]]
      lemmas mec_map_len_hnr[sepref_fr_rules] = mec_map_len_ll.refine[FCOMP mec_map_len_correct, unfolded mec_map_len_ll'.refine[OF disj_set_list_tuple_env_axioms]]
      lemmas eq_mec_member_hnr[sepref_fr_rules] = eq_mec_member_ll.refine[FCOMP eq_mec_member_correct, unfolded eq_mec_member_ll'.refine[OF disj_set_list_tuple_env_axioms]]
      lemmas mec_index_of_hnr[sepref_fr_rules] = mec_index_of_ll.refine[FCOMP mec_index_of_correct, unfolded mec_index_of_ll'.refine[OF disj_set_list_tuple_env_axioms]]
      lemmas sort_by_inf_ll_hnr[sepref_fr_rules] = sort_by_inf_ll.refine[folded sort_by_inf_alt, FCOMP sort_by_inf_correct, unfolded sort_by_inf_ll'.refine[OF disj_set_list_tuple_env_axioms]]

    end

  end

end