theory TC_To_XC
imports  "Karp21.Polynomial_Reductions" 
         "Karp21.TC_To_ChrN"
         "HOL-Library.Disjoint_Sets"

begin

subsection "Exact cover definitions"

definition "exactCover \<equiv> 
   {(X, S). \<Union>S \<subseteq> X \<and>
    (\<exists>S' \<subseteq> S. \<forall>x \<in> X. \<exists>s \<in> S'. x \<in> s \<and> (\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t))}"

definition "exactCover' \<equiv> {(X, S). \<Union>S \<subseteq> X \<and> (\<exists>S' \<subseteq> S. \<Union>S' = X \<and> disjoint S')}"

lemma "(X, S) \<in> exactCover \<longleftrightarrow> (X, S) \<in> exactCover'"
proof (standard, goal_cases)
  assume 1: "(X, S) \<in> exactCover"
  hence "\<Union>S \<subseteq> X" unfolding exactCover_def by blast
  from 1 obtain S' where s_def: "S' \<subseteq> S" "\<forall>x \<in> X. \<exists>s \<in> S'. x \<in> s \<and> (\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t)"
  unfolding exactCover_def by blast 

  hence "\<forall>x \<in> X. \<exists>s \<in> S'. x \<in> s" by blast   
  then have "X \<subseteq> \<Union>S'" by blast 
  moreover have "\<Union>S' \<subseteq> X" using \<open>S' \<subseteq> S\<close> \<open>\<Union>S \<subseteq> X\<close> by blast 
  ultimately have "X = \<Union>S'" by simp 

  have "disjoint S'"
  proof (rule disjointI)
    fix a b 
    assume ab_def: "a \<in> S'" "b \<in> S'" "a \<noteq> b"

    with s_def have 
      "\<forall>x \<in> X. x \<in> a \<longrightarrow> x \<notin> b" 
      "\<forall>x \<in> X. x \<in> b \<longrightarrow> x \<notin> a"
       by metis+ 
    hence "\<forall>x\<in>X. x \<notin> a \<inter> b" by blast 

    moreover from \<open>\<Union>S' \<subseteq> X\<close> have "\<forall>x \<in> a \<inter> b. x \<in> X"
    using ab_def by blast

    ultimately show "a \<inter> b = {}" by blast
  qed

  from \<open>X = \<Union>S'\<close> \<open>disjoint S'\<close> \<open>S' \<subseteq> S\<close> \<open>\<Union>S \<subseteq> X\<close> show "(X, S) \<in> exactCover'"
  unfolding exactCover'_def by blast
next
  assume 2:"(X, S) \<in> exactCover'"
  then have "\<Union>S \<subseteq> X" unfolding exactCover'_def by blast

  from 2 obtain S' where S'_def: "S' \<subseteq> S" "\<Union>S' = X" "disjoint S'"
    unfolding exactCover'_def by blast 
  
  have "\<forall>x \<in> X. \<exists>s \<in> S'. x \<in> s \<and> (\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t)"
  proof 
    fix x 
    assume "x \<in> X"
    then obtain s where "s \<in> S'" "x \<in> s" using S'_def by blast
    moreover then have "\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t"
      using disjointD[OF \<open>disjoint S'\<close>] by blast

    ultimately show "\<exists>s \<in> S'. x \<in> s \<and> (\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t)"
    by blast
  qed 
  
  then show "(X, S) \<in> exactCover" using \<open>\<Union>S \<subseteq> X\<close> \<open>S' \<subseteq> S\<close>
    unfolding exactCover_def by blast 
qed



end 