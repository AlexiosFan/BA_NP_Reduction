theory SS_Part_KS_aux
  imports "../XC_To_SS/XC_To_SS_aux"
begin


definition "part \<equiv> {as::nat list. \<exists>xs. (\<forall>i < length xs. xs!i \<in> {0, 1}) \<and> length as = length xs 
  \<and> 2 * (\<Sum>i < length as. as ! i * xs ! i) =( \<Sum>i < length as. as ! i)}"

definition ss_to_part :: "nat list * nat \<Rightarrow> nat list" where
"ss_to_part \<equiv> \<lambda>(as, s). (if s \<le> (\<Sum> i < length as. as ! i) then ((\<Sum>i < length as. as ! i) + 1 - s) # (s + 1) # as else [1])"

definition "subset_sum_int_list \<equiv> {(as,s). (\<exists>xs::int list. 
    (\<forall>i<length xs. xs!i \<in> {0,1}) \<and> (\<Sum>i<length as. as!i * xs!i) = s \<and> length xs = length as)}"

lemma subset_sum_nat_to_int_sound:
assumes "(as, s) \<in> subset_sum_list"
shows "(map int as, int s) \<in> subset_sum_int_list"
proof -
  from assms obtain xs where 
  "(\<forall>i<length xs. xs!i \<in> {0,1}) \<and> (\<Sum>i<length as. as!i * xs!i) = s \<and> length xs = length as"
    unfolding subset_sum_list_def
    by blast 
  hence "(\<forall>i<length (map int xs).(map int xs)! i \<in> {0,1}) 
    \<and> (\<Sum>i<length (map int as). (map int as)! i * (map int xs) ! i) = int s 
    \<and> length (map int xs) = length (map int as)"
    by force
  then show ?thesis
    unfolding subset_sum_int_list_def
    by blast
qed 

lemma subset_sum_nat_to_int_complete:
assumes "(map int as, int s) \<in> subset_sum_int_list"
shows "(as, s) \<in> subset_sum_list"
proof -
  from assms obtain xs where xs_def:
  "(\<forall>i<length xs. xs ! i \<in> {0,1})"
    "(\<Sum>i<length (map int as). (map int as)! i * xs ! i) = int s"
    "length xs = length (map int as)"
    unfolding subset_sum_int_list_def
    by fast 
  from this(1) have "\<exists>ys. map int ys = xs"
    proof (induction xs)
      case (Cons a xs)
      then obtain ys where "map int ys = xs"
        by fastforce 
      moreover from Cons(2) have "a = 1 \<or> a = 0"
        by auto
      ultimately have "map int ((if a = 1 then 1 :: nat else 0 )# ys) = a # xs"
        by fastforce
      then show ?case
        by metis
    qed simp
  then obtain ys where "map int ys = xs"
    by blast
  with xs_def have "(\<forall>i<length ys. ys! i \<in> {0,1}) 
    \<and> (\<Sum>i<length as. as! i * ys ! i) = s 
    \<and> length ys = length as"
    by (auto, smt (verit) of_nat_eq_iff of_nat_mult of_nat_sum sum.cong)
  then show ?thesis 
    unfolding subset_sum_list_def
    by blast
qed 

lemma is_reduction_subset_sum_nat_to_int:
"is_reduction (\<lambda>(as, s). (map int as, int s)) subset_sum_list subset_sum_int_list"
  unfolding is_reduction_def 
  using subset_sum_nat_to_int_sound subset_sum_nat_to_int_complete
  by fast


end 