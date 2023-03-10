theory TC_To_XC
imports  "Karp21.Polynomial_Reductions" 
         "Karp21.TC_To_ChrN"
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

(*2 different definitions, which is better?
  Possibility to reuse the Disjoint_Sets*)

lemma exact_coverI: "\<lbrakk>S' \<subseteq> S; \<Union>S = X; disjoint S'; \<Union>S' = X\<rbrakk> \<Longrightarrow> (X, S) \<in> exact_cover'"
  unfolding exact_cover'_def by blast

definition "TC_XC E \<equiv> (if ugraph E 
  then (let X = {(v, opt, c). v \<in> \<Union>E 
                \<and> (opt = None \<or> (\<exists>u. {v, u} \<in> E \<longrightarrow> opt = Some u) \<or> opt = Some v) 
                \<and> (\<exists>c_sets. disjoint c_sets \<and> c \<in> c_sets \<and> card c = 3)};
            S = {}
             in (X,S))
  else ({}, {}))"
(*refinement necessary
{{u_trip, p} | u_trip p. u_trip \<noteq> p \<and> u_trip \<in> X \<and> (\<exists>u c. u_trip = (u, Some u, 3) \<and> p = (u, None, c))}
                \<union> {{p1, p2} | p1 p2. p1 \<noteq> p2 \<and> p1 \<in> X \<and> p2 \<in> X \<and> (\<exists>u v c1 c2. p1 = (v, Some u, c1) \<and> p2 = (u, Some v, c2) \<and> c1 \<noteq> c2)}
                \<union> {{(v, opt, c). opt = None \<or> (\<exists>u. {v, u} \<in> E \<longrightarrow> opt = Some u) \<and> c \<in> {0, 1, 2}} | v. v \<in> \<Union>E}
*)

lemma "({}, {}) \<in> exact_cover"
unfolding exact_cover_def by blast

lemma TC_XC_sound: "E \<in> three_colorability \<Longrightarrow> (TC_XC E) \<in> exact_cover'"
unfolding TC_XC_def apply (auto split: prod.splits)
sorry

(*proof of soundness understood, problem and refinement goal: 
the definition of \<chi> does not involve a set of colors, but a direct partition of vertexes*)

lemma TC_XC_complete: "(TC_XC E) \<in> exact_cover' \<Longrightarrow> E \<in> three_colorability"
sorry

lemma "is_reduction TC_XC three_colorability exact_cover'"
using TC_XC_sound TC_XC_complete unfolding is_reduction_def by blast

(*proof of completeness understood, problem: the proof far away from the definition of
the three coloarbility, a formalisation and abstraction is necessary*)

end 