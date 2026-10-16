theory Nat_Interval
  imports "./More_List_Rel"
begin 

section \<open>SharedNat Intervals\<close>

text \<open>
  This sections represents an extension of the tuple representation as an interval.
  I.e. the tuple (n,i) represents the natural numbers ranging from i to n+i.
  There are three representations: as a predicate \<open>in_intv\<close>, as a set \<open>sn_intv\<close> and as a list
  \<open>ls_intv\<close>.
\<close>


(*left*)definition cnt :: "nat \<times> nat \<Rightarrow> nat" where "cnt = fst" \<comment> \<open>Number of natural numbers in the interval\<close>

(*right*)definition lid :: "nat \<times> nat \<Rightarrow> nat" where "lid = snd" \<comment> \<open>Lowest list index, inclusive\<close>

(*sum*)definition uid :: "nat \<times> nat \<Rightarrow> nat" where "uid = (\<lambda> (l,r). l + r)" \<comment> \<open>Highest list index, exclusive\<close>


section \<open>Nat_Interval basic lemmas\<close>

lemma cnt_eq[simp]: "cnt (l,r) = l"
  unfolding cnt_def by simp

lemma lid_eq[simp]: "lid (l,r) = r"
  unfolding lid_def by simp

lemma shared_sum_eq[simp]: "uid (l,r) = l + r"
  unfolding uid_def by simp


lemma uid_as_cnt_plus_lid: "uid x = cnt x + lid x"
  unfolding uid_def cnt_def lid_def
  apply (cases x) 
  by simp

lemma cnt_leq_uid[simp]: "cnt x \<le> uid x"
  unfolding cnt_def uid_def
  by(cases x ; simp)

lemma lid_leq_uid[simp]: "lid x \<le> uid x"
  unfolding lid_def uid_def
  by(cases x ; simp)

lemma cnt_lt_uid[simp, intro!]: "lid x > 0 \<Longrightarrow> cnt x < uid x"
  unfolding uid_def cnt_def lid_def
  by(cases x ; auto)

lemma lid_lt_uid[simp, intro!]: "cnt x > 0 \<Longrightarrow> lid x < uid x"
  unfolding uid_def cnt_def lid_def
  by(cases x ; simp)

lemma uid_sub_lid_eq_cnt[simp]: "uid x - lid x = cnt x"
  unfolding uid_def cnt_def lid_def
  apply (cases x) 
  by simp

lemma uid_sub_cnt_eq_lid[simp]: "uid x - cnt x = lid x"
  unfolding uid_def cnt_def lid_def
  apply (cases x) 
  by simp

lemma uid_neq_cnt_lt: "uid x \<noteq> cnt x \<Longrightarrow> cnt x < uid x"
  unfolding uid_as_cnt_plus_lid by simp

lemma cnt_neq_uid_lt: "cnt x \<noteq> uid x \<Longrightarrow> cnt x < uid x"
  unfolding uid_as_cnt_plus_lid by simp

lemma uid_neq_lid_lt: "uid x \<noteq> lid x \<Longrightarrow> lid x < uid x"
  unfolding uid_as_cnt_plus_lid by simp

lemma lid_neq_uid_lt: "lid x \<noteq> uid x \<Longrightarrow> lid x < uid x"
  unfolding uid_as_cnt_plus_lid by simp



section \<open>Interval evaluation\<close>

definition "in_intv sn i = (lid sn \<le> i \<and> i < uid sn)"
definition "sn_intv sn = Collect (in_intv sn)"
definition "ls_intv sn = [lid sn..<uid sn]"

lemma lid_in_intv [simp,intro!]: "cnt sn > 0 \<Longrightarrow> in_intv sn (lid sn)"
  by(auto simp: in_intv_def)

lemma uid_not_in_intv [simp]: "\<not>in_intv sn (uid sn)" 
  by(auto simp: in_intv_def)

lemma sn_intv_alt: "sn_intv sn = {lid sn..<uid sn}"
  unfolding sn_intv_def in_intv_def
  by auto

lemma in_intv_lbD[intro]: "in_intv sn i \<Longrightarrow> lid sn \<le> i"
  unfolding in_intv_def
  by blast

lemma in_intv_ubD[intro]: "in_intv sn i \<Longrightarrow> i < uid sn"
  unfolding in_intv_def
  by blast

lemma in_intv_bounds: "in_intv sn i \<Longrightarrow> lid sn \<le> i \<and> i < uid sn"
  unfolding in_intv_def
  by blast

lemma sn_intv_member[simp]: "i \<in> sn_intv sn \<longleftrightarrow> in_intv sn i"
  by (auto simp: in_intv_def sn_intv_def)

lemma in_intvI: "lid sn \<le> i \<Longrightarrow> i < uid sn \<Longrightarrow> in_intv sn i" 
  apply(fold sn_intv_member) 
  unfolding sn_intv_alt
  by simp

lemma finite_sn_intv[simp]: "finite (sn_intv sn)"
  unfolding sn_intv_alt
  by simp

lemma set_ls_intv[simp]: "set (ls_intv sn) = sn_intv sn"
  unfolding ls_intv_def sn_intv_alt by simp

lemma distinct_ls_intv[simp]: "distinct (ls_intv sn)"
  unfolding ls_intv_def
  by simp

lemma sorted_ls_intv[simp]: "sorted (ls_intv sn)"
  unfolding ls_intv_def by simp

lemma sorted_lt_ls_intv[simp]: "sorted_wrt (<) (ls_intv sn)"
  unfolding ls_intv_def by simp

lemma length_ls_intv[simp]: "length (ls_intv sn) = cnt sn"
  unfolding ls_intv_def by simp

lemma last_intv: "cnt sn > 0 \<Longrightarrow> last (ls_intv sn) = uid sn - Suc 0"
  unfolding ls_intv_def by fastforce

lemma hd_intv: "cnt sn > 0 \<Longrightarrow> hd (ls_intv sn) = lid sn"
  unfolding ls_intv_def by force

lemma butlast_intv: "butlast (ls_intv sn) = [lid sn..<uid sn - Suc 0]" 
  using One_nat_def butlast_upt ls_intv_def by presburger

lemma tl_intv: "tl (ls_intv sn) = [Suc (lid sn)..<uid sn]"
  by (simp add: ls_intv_def)

lemma ls_intv_emp [simp]: "ls_intv sn = [] \<longleftrightarrow> cnt sn = 0"
  unfolding ls_intv_def uid_as_cnt_plus_lid by force

lemma ls_intv_nemp [simp]: "ls_intv sn \<noteq> [] \<longleftrightarrow> cnt sn > 0"
  unfolding ls_intv_def uid_as_cnt_plus_lid by force

lemma sn_intv_emp [simp]: "sn_intv sn = {} \<longleftrightarrow> cnt sn = 0"
  unfolding sn_intv_def uid_as_cnt_plus_lid in_intv_def by auto

lemma sn_intv_nemp [simp]: "sn_intv sn \<noteq> {} \<longleftrightarrow> cnt sn > 0"
  unfolding sn_intv_def uid_as_cnt_plus_lid in_intv_def by force  

lemma ls_intv_butlast_last: "cnt sn > 0 \<Longrightarrow> ls_intv sn = [lid sn..<uid sn - Suc 0] @ [uid sn - Suc 0]"
  apply(simp flip: butlast_intv)
  by(simp flip: last_intv )

lemma in_intv_nth: "in_intv sn i \<Longrightarrow> ls_intv sn ! (i - lid sn) = i"
  unfolding ls_intv_def
  apply(subst nth_upt)
  subgoal
    apply(subst add_diff_inverse_nat)
    apply(subst not_less) 
    by auto
  subgoal
    apply(subst add_diff_inverse_nat)
    apply(subst not_less) 
    by auto
  done

lemma ls_intv_nth[simp]: "i < cnt sn \<Longrightarrow> ls_intv sn ! i = i + lid sn"
  unfolding ls_intv_def
  apply(subst nth_upt) 
  using uid_as_cnt_plus_lid 
  by auto

lemma ls_intv_nth_lt[simp]:  "i < cnt sn \<Longrightarrow> j < cnt sn \<Longrightarrow> ls_intv sn ! i < ls_intv sn ! j \<longleftrightarrow> i < j"
  by auto

lemma i_lt_cnt_in_intv: "i < cnt sn \<Longrightarrow> in_intv sn (i + lid sn)"
  unfolding in_intv_def uid_as_cnt_plus_lid by simp

lemma i_lt_cnt_ls_intv_in_intv: "i < cnt sn \<Longrightarrow> in_intv sn (ls_intv sn ! i)"
  by(auto simp: ls_intv_nth i_lt_cnt_in_intv)

lemma take_ls_intv: "i < uid sn \<Longrightarrow> take (i - lid sn) (ls_intv sn) = [lid sn..<i]"
  apply(cases "i \<le> lid sn")
  using in_intv_lbD in_intv_ubD ls_intv_def nat_less_le by auto

lemma drop_ls_intv: "lid sn \<le> i \<Longrightarrow> drop (i - lid sn) (ls_intv sn) = [i..<uid sn]"
  using ls_intv_def by auto

lemma in_intv_gt: "in_intv sn x \<Longrightarrow> x < x' \<Longrightarrow> x' < uid sn \<Longrightarrow> in_intv sn x'"
  by (auto simp: in_intv_def)

lemma in_intv_lt: "in_intv sn x \<Longrightarrow> x' < x \<Longrightarrow> lid sn \<le> x' \<Longrightarrow> in_intv sn x'"
  by (auto simp: in_intv_def)

lemma intv_list_set_rel: "(ls_intv sn, sn_intv sn) \<in> \<langle>nat_rel\<rangle>list_set_rel"
  unfolding ls_intv_def sn_intv_alt using upt_list_set_rel by presburger

lemma in_subset_sn_intv: "x \<in> X \<Longrightarrow> X \<subseteq> sn_intv sn \<Longrightarrow> in_intv sn x"
  unfolding sn_intv_def in_intv_def by blast

lemma ex_in_intv: "cnt sn > 0 \<Longrightarrow> \<exists>x. in_intv sn x"
    unfolding in_intv_def by blast

lemma in_intv_set: "{x. in_intv sn x} = sn_intv sn"
  unfolding in_intv_def sn_intv_def by blast

lemma image_sn_intv: "in_intv sn x \<Longrightarrow> f x \<in> f ` sn_intv sn"
  by auto


section \<open>Sorted list as intervals\<close>

definition "sorted_intvs xs = map (\<lambda> i. (xs ! (Suc i) - xs ! i, xs ! i)) [0..<length xs - Suc 0]"

lemma length_sorted_intvs: "xs \<noteq> [] \<Longrightarrow> length (sorted_intvs xs) = length xs - Suc 0"
  unfolding sorted_intvs_def by simp

lemma lid_sorted_intvs[simp, intro!]: "sorted xs \<Longrightarrow> i < length xs - Suc 0 \<Longrightarrow> lid (sorted_intvs xs ! i) = xs ! i"
  unfolding sorted_intvs_def by auto

lemma uid_sorted_intvs[simp, intro!]: "sorted xs \<Longrightarrow> i < length xs - Suc 0 \<Longrightarrow> uid (sorted_intvs xs ! i) = xs ! (Suc i)"
  unfolding sorted_intvs_def
  by (simp add: sorted_wrt_nth_less)

lemma cnt_sorted_intvs[simp, intro!]: "sorted xs \<Longrightarrow> i < length xs - Suc 0 \<Longrightarrow> cnt (sorted_intvs xs ! i) = xs ! (Suc i) - xs ! i"
  unfolding sorted_intvs_def by auto

lemma in_intv_sorted_intvs: "sorted xs \<Longrightarrow> i < length xs - Suc 0 \<Longrightarrow> in_intv (sorted_intvs xs ! i) x \<longleftrightarrow> xs ! i \<le> x \<and> x < xs ! Suc i"
  unfolding sorted_intvs_def 
  by (auto dest!: in_intv_bounds intro!: in_intvI) 

lemma sn_intv_sorted_intvs: "sorted xs \<Longrightarrow> i < length xs - Suc 0 \<Longrightarrow> sn_intv (sorted_intvs xs ! i) = {xs ! i ..< xs ! Suc i}"
  using in_intv_sorted_intvs by auto

lemma ls_intv_sorted_intvs: "sorted xs \<Longrightarrow> i < length xs - Suc 0 \<Longrightarrow> ls_intv (sorted_intvs xs ! i) = [xs ! i ..< xs ! Suc i]"
  by (simp add: lid_sorted_intvs ls_intv_def uid_sorted_intvs)

lemma sorted_intvs_disj: "sorted xs \<Longrightarrow> i < j \<Longrightarrow> j < length xs - Suc 0 \<Longrightarrow> sn_intv (sorted_intvs xs ! i) \<inter> sn_intv (sorted_intvs xs ! j) = {}"
  by(fastforce simp: less_eq_Suc_le sn_intv_sorted_intvs dest: sorted_nth_mono)

lemma sorted_intvs_disj_ext: "sorted xs \<Longrightarrow> i \<noteq> j \<Longrightarrow> i < length xs - Suc 0 \<Longrightarrow> j < length xs - Suc 0 \<Longrightarrow> sn_intv (sorted_intvs xs ! i) \<inter> sn_intv (sorted_intvs xs ! j) = {}"
  using sorted_intvs_disj 
  by(auto simp: nat_neq_iff)

lemma strict_sorted_intvs_cnt_gt_0: "sorted_wrt (<) xs \<Longrightarrow> i < length xs - Suc 0 \<Longrightarrow> cnt (sorted_intvs xs ! i) > 0"
  unfolding strict_sorted_iff 
  using cnt_sorted_intvs[of xs i]
  by (auto intro: distinct_sorted_mono)

lemma nth_in_intv_sorted_intvs[simp,intro!]: "sorted_wrt (<) xs \<Longrightarrow> i < length xs - Suc 0 \<Longrightarrow> in_intv (sorted_intvs xs ! i) (xs ! i)"
  unfolding sorted_intvs_def in_intv_def by (auto simp: map_nth sorted_wrt_less_idx sorted_wrt_nth_less)

section \<open>Set Interval\<close>

definition set_lid :: "nat \<times> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where "set_lid = (\<lambda> (c,l') l. (c+l'-l,l))"

definition set_uid :: "nat \<times> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where "set_uid = (\<lambda> (_,l) u. (u-l,l))"

lemma lid_set_lid[simp]:"lid (set_lid sn l) = l"
  unfolding set_lid_def by (auto split: prod.split)

lemma uid_set_lid[simp]:"l \<le> uid sn \<Longrightarrow> uid (set_lid sn l) = uid sn"
  unfolding set_lid_def by (auto split: prod.split)

lemma lid_set_uid[simp]: "lid (set_uid sn u) = lid sn"
  unfolding set_uid_def by (auto split: prod.split)

lemma uid_set_uid[simp]: "u \<ge> lid sn \<Longrightarrow> uid (set_uid sn u) = u"
  unfolding set_uid_def by (auto split: prod.split)

lemma cnt_set_lid: "cnt (set_lid sn l) = cnt sn + lid sn - l"
  unfolding set_lid_def cnt_def lid_def apply(cases sn) by auto

lemma cnt_set_uid: "cnt (set_uid sn l) = l - lid sn"
  unfolding set_uid_def cnt_def uid_def apply(cases sn) by auto

lemma set_lid_to_lid[simp]: "(set_lid sn (lid sn)) = sn"
  unfolding set_lid_def apply(cases sn) by auto

lemma set_uid_to_uid[simp]: "(set_uid sn (uid sn)) = sn"
  unfolding set_uid_def apply(cases sn) by auto


lemma sn_intv_set_lid[simp]: "l \<le> uid sn \<Longrightarrow> sn_intv (set_lid sn l) = {l..<uid sn}"
  unfolding set_lid_def by (auto simp: in_intv_def split: prod.split)

lemma sn_intv_set_uid[simp]: "u \<ge> lid sn \<Longrightarrow> sn_intv (set_uid sn u) = {lid sn..<u}"
  unfolding set_uid_def by (auto simp: in_intv_def split: prod.split)

lemma ls_intv_set_lid[simp]: "l \<le> uid sn \<Longrightarrow> ls_intv (set_lid sn l) = [l..<uid sn]"
  unfolding set_lid_def by (auto simp: ls_intv_def split: prod.split)

lemma ls_intv_set_uid[simp]: "u \<ge> lid sn \<Longrightarrow> ls_intv (set_uid sn u) = [lid sn..<u]"
  unfolding set_uid_def by (auto simp: ls_intv_def split: prod.split)

lemma in_intv_le_set_lid: "in_intv sn i \<Longrightarrow> l \<le> i \<Longrightarrow> in_intv (set_lid sn l) i"
  unfolding in_intv_def by auto

lemma in_intv_bigger_set_lid: "in_intv sn i \<Longrightarrow> l \<le> lid sn \<Longrightarrow> in_intv (set_lid sn l) i"
  unfolding in_intv_def by auto

lemma in_intv_smaller_set_lid: "in_intv (set_lid sn l) i \<Longrightarrow> lid sn \<le> l \<Longrightarrow> l \<le> uid sn \<Longrightarrow> in_intv sn i"
  unfolding in_intv_def by auto

lemma in_intv_ge_set_uid: "in_intv sn i \<Longrightarrow> i < u \<Longrightarrow> in_intv (set_uid sn u) i"
  unfolding in_intv_def by auto

lemma in_intv_bigger_set_uid: "in_intv sn i \<Longrightarrow> u \<ge> uid sn \<Longrightarrow> in_intv (set_uid sn u) i"
  unfolding in_intv_def by auto

lemma in_intv_smaller_set_uid: "in_intv (set_uid sn u) i \<Longrightarrow> lid sn \<le> u \<Longrightarrow> u \<le> uid sn \<Longrightarrow> in_intv sn i"
  unfolding in_intv_def by auto

lemma pos_cnt_set_lid[simp]: "0 < cnt (set_lid sn l) \<longleftrightarrow> l < uid sn"
  unfolding set_lid_def cnt_def uid_def by (auto split: prod.split)

lemma pos_cnt_set_uid[simp]: "0 < cnt (set_uid sn u) \<longleftrightarrow> u > lid sn"
  unfolding set_uid_def cnt_def lid_def by (auto split: prod.split)

lemma hd_ls_intv_set_lid[simp, intro!]:  "l < uid sn \<Longrightarrow> hd (ls_intv (set_lid sn l)) = l"
  by(auto)

lemma hd_ls_intv_set_uid[simp, intro!]:  "u > lid sn \<Longrightarrow> hd (ls_intv (set_uid sn u)) = lid sn"
  by(auto)

lemma last_ls_intv_set_lid[simp, intro!]:  "l < uid sn \<Longrightarrow> last (ls_intv (set_lid sn l)) = uid sn - Suc 0"
  by(auto)

lemma last_ls_intv_set_uid[simp, intro!]:  "u > lid sn \<Longrightarrow> last (ls_intv (set_uid sn u)) = u - Suc 0"
  by(auto)

end
