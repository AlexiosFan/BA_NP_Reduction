theory XC_To_Subset_Sum
  imports XC_To_Subset_Sum_aux

begin

abbreviation "sum_of_power S A \<equiv> \<Sum> ((\<lambda>x. x ^ (card S)) ` A)"

definition "xc_to_subset_sum XC \<equiv> 
  (case XC of (X, S) \<Rightarrow> 
    (if X = {} then (S, 0, 0)
    else 
    (S, 
    sum_of_power S, 
    sum_of_power S {0..card S - 1}))
  )"

lemma xc_to_subset_sum_sound:
assumes "cover X S"
shows "is_subset_sum S (sum_of_power S) ( sum_of_power S {0..card S - 1})"
using assms unfolding cover_def
sorry

end 