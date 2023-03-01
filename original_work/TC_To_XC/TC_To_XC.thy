theory TC_To_XC
imports  "Karp21.Polynomial_Reductions" 
         "Karp21.TC_To_ChrN"
         "HOL-Library.Disjoint_Sets"

begin

subsection "Exact cover definitions"

definition "exactCover \<equiv> {(X, S). \<forall>S' \<in> S. (S' \<subseteq> X \<and> (\<forall>x \<in> X. \<forall>S'' \<in> S. x \<in> S' \<and> S' \<noteq> S'' \<longrightarrow> x \<notin> S''))}"

definition "exactCover' \<equiv> {(X, S). \<forall>S' \<in> S. S' \<subseteq> X \<and> disjoint S}"

lemma "exactCover = exactCover'"
unfolding exactCover_def exactCover'_def 
apply auto 
apply (rule disjointI, blast)
using disjointD apply blast+
done 



end 