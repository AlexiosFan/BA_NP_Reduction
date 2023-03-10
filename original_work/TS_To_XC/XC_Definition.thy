theory XC_Definition
  imports "Karp21.Polynomial_Reductions"
          "HOL-Library.Disjoint_Sets"

begin

subsection "Exact cover definitions"

definition "exact_cover \<equiv> 
   {(X, S). \<Union>S \<subseteq> X \<and>
    (\<exists>S' \<subseteq> S. \<forall>x \<in> X. \<exists>s \<in> S'. x \<in> s \<and> (\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t))}"

definition "exact_cover' \<equiv> {(X, S). \<Union>S \<subseteq> X \<and> (\<exists>S' \<subseteq> S. \<Union>S' = X \<and> disjoint S')}"
(*for a collection S of subsets of a set X, there exists a subset S' of S s.t. 
S' covers all elements of X exactly, i.e. the each element of X is contained in
exactly one element of S'*)

lemma aux: "(X, S) \<in> exact_cover \<longleftrightarrow> (X, S) \<in> exact_cover'"
proof (standard, goal_cases)
  assume 1: "(X, S) \<in> exact_cover"
  hence "\<Union>S \<subseteq> X" unfolding exact_cover_def by blast
  from 1 obtain S' where s_def: "S' \<subseteq> S" "\<forall>x \<in> X. \<exists>s \<in> S'. x \<in> s \<and> (\<forall>t \<in> S'. s \<noteq> t \<longrightarrow> x \<notin> t)"
  unfolding exact_cover_def by blast 

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

  from \<open>X = \<Union>S'\<close> \<open>disjoint S'\<close> \<open>S' \<subseteq> S\<close> \<open>\<Union>S \<subseteq> X\<close> show "(X, S) \<in> exact_cover'"
  unfolding exact_cover'_def by blast
next
  assume 2:"(X, S) \<in> exact_cover'"
  then have "\<Union>S \<subseteq> X" unfolding exact_cover'_def by blast

  from 2 obtain S' where S'_def: "S' \<subseteq> S" "\<Union>S' = X" "disjoint S'"
    unfolding exact_cover'_def by blast 
  
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
  
  then show "(X, S) \<in> exact_cover" using \<open>\<Union>S \<subseteq> X\<close> \<open>S' \<subseteq> S\<close>
    unfolding exact_cover_def by blast 
qed

corollary "exact_cover = exact_cover'"
   using aux by auto

lemma exact_coverI: "\<lbrakk>S' \<subseteq> S; \<Union>S \<subseteq> X; disjoint S'; \<Union>S' = X\<rbrakk> \<Longrightarrow> (X, S) \<in> exact_cover'"
  unfolding exact_cover'_def by blast

end 