theory XC_To_SS
  imports XC_To_SS_aux

begin

definition "map_to_nat X \<equiv> (SOME f. (if X = {} then bij_betw f X {} else bij_betw f X {1..card X}))"
definition "weight p X \<equiv> (sum (\<lambda>x. x ^ p)  X)"


lemma map_to_nat_unfold:
assumes "finite X"
shows  "(map_to_nat X) ` X = (if X = {} then {} else {1..card X}) \<and> inj_on (map_to_nat X) X"
proof -
  have "(if X = {} then bij_betw (map_to_nat X) X {} else bij_betw (map_to_nat X) X {1..card X})"
    unfolding map_to_nat_def
    apply (rule someI_ex[of "\<lambda>f. (if X = {} then bij_betw f X {} else bij_betw f X {1..card X})"])
    using bij_exist[OF assms] .
  thus ?thesis 
    unfolding bij_betw_def
    by presburger
qed 

lemma weight_eq_poly:
fixes X:: "nat set"
assumes "p \<ge> 2"
shows  "weight p X = \<Sum>{x ^ p | x . x \<in> X}"
  proof -
    from assms have "inj_on (\<lambda>x. x ^ p) X"
      proof (induction p)
        case (Suc p)
        then show ?case
        proof (cases "p = 1")
          case True
          then show ?thesis
            unfolding inj_on_def
            using power_inject_base 
            by blast 
        next
          case False
          with Suc have "\<forall>x\<in>X. \<forall>y\<in>X. x ^ p = y ^ p \<longrightarrow> x = y"
            unfolding inj_on_def
            by linarith
          then show ?thesis
            unfolding inj_on_def
            using power_eq_iff_eq_base 
            by fastforce
        qed
      qed auto

    moreover have "{x ^ p | x . x \<in> X} = ((\<lambda>x. x ^ p) ` X)"
      by blast
    ultimately show ?thesis
      unfolding weight_def
      using sum.image_eq[of "(\<lambda>x. x ^ p)" "X"]
      by presburger
  qed 


definition 
"xc_to_ss XC \<equiv> 
  (case XC of (X, S) \<Rightarrow> 
    (if infinite X \<or> (\<not> \<Union>S \<subseteq> X) then ({}, card, 1::nat)
    else 
      (let f = map_to_nat X;
           p = max 2 (card S + 1) 
        in
      (S, 
      (\<lambda>A. weight p (f ` A)), 
      weight p (f ` X))
      )
    )
  )"

lemma infinite_not_in_ss:
  "\<not> is_subset_sum ({}, card , 1::nat)"
unfolding is_subset_sum_def
by force

lemma xc_to_subset_sum_sound:
assumes "cover S X" "finite X"
shows "is_subset_sum (xc_to_ss (X, S))"
proof (cases "finite X")  
  let ?f = "(map_to_nat X)"
  let ?p = "max 2 (card S + 1)"
  case True
  from assms have prems: "disjoint S" "\<Union>S = X"
    unfolding cover_def 
    by blast+

  from assms have "finite (\<Union>S)"
    using prems 
    by blast
  hence *:"finite S"
    using finite_UnionD
    by blast

  have "\<forall>i \<in> S. finite i"
    using \<open>finite (\<Union>S)\<close>
    by (metis Sup_upper finite_subset)
  hence **:"\<forall>i\<in>S. finite (?f ` i)"
    by blast

  have "inj_on ?f X"
    using map_to_nat_unfold[OF assms(2)]
    by blast
  with prems have "disjoint ((`) ?f ` S)"
    by (simp add: disjoint_image)
  hence ***:"\<forall>i\<in>S. \<forall>j\<in>S. i \<noteq> j \<longrightarrow> map_to_nat X ` i \<inter> map_to_nat X ` j = {}"
    unfolding disjoint_def 
    by (metis True Union_upper assms(1) cover_def disjointD image_empty 
    inj_on_image_Int map_to_nat_unfold)

  from * ** *** have 
  "(\<Sum>x\<in>\<Union> ((`) ?f ` S). x ^ ?p) = (\<Sum>x\<in>S. \<Sum>x\<in>?f ` x. x ^ ?p)"
    using sum.UNION_disjoint[of S "(`) ?f" "(\<lambda>x. x ^ ?p)"]
    by blast
  moreover have "\<Union> ((`) ?f ` S) = ?f ` X"
    using prems
    by blast
  ultimately have "(\<Sum>x\<in>S. \<Sum>x\<in>?f` x. x ^ ?p) = (\<Sum>x\<in>?f ` X. x ^ ?p)"
    by argo

  with assms(2) * prems show ?thesis
    unfolding is_subset_sum_def xc_to_ss_def Let_def weight_def 
    by simp 
next
  case False
  then show ?thesis
    unfolding is_subset_sum_def xc_to_ss_def
    by (simp add: assms)
qed


lemma ss_leads_disjoint:
assumes "is_subset_sum (xc_to_ss (X, S))"
shows "disjoint S"
proof (cases "infinite X \<or> (\<not> \<Union>S \<subseteq> X)")
  case True
  then show ?thesis
    using assms(1)
    unfolding xc_to_ss_def is_subset_sum_def
    by simp
next
  let ?f = "(map_to_nat X)"
  let ?p = "max 2 (card S + 1)"
  have "?p \<ge> 2"
    by auto 
  hence 
  "weight ?p (?f ` X) = \<Sum>{x ^ ?p | x . x \<in> (?f ` X)}"
  "\<forall>A\<in>S. weight ?p (?f ` A) = \<Sum>{x ^ ?p | x . x \<in> (?f ` A)}"
    using weight_eq_poly[of ?p] 
    by blast+
(*(\<Sum>x\<in>S. \<Sum>x\<in>?f ` x. x ^ ?p)*)
  case False
  then have "finite S" "(\<Sum>A\<in>S. weight ?p (?f ` A)) = weight ?p (?f ` X)"
      using assms 
      unfolding xc_to_ss_def is_subset_sum_def Let_def
      by simp+
  then show ?thesis sorry
qed

lemma disjoint_unfold:
"disjoint S \<Longrightarrow> a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<inter> b = {}"
unfolding disjoint_def 
by fast


lemma xc_to_subset_sum_complete:
assumes "is_subset_sum (xc_to_ss (X, S))"
shows "cover S X" 
proof (cases "infinite X \<or> (\<not> \<Union>S \<subseteq> X)")
  case True
  then show ?thesis
    using assms(1)
    unfolding xc_to_ss_def is_subset_sum_def
    by simp
next
  let ?f = "map_to_nat X"
  let ?p = "max 2 (card S + 1)"
  case False
  then have S_prop: "finite S" "(\<Sum>A\<in>S. weight ?p (?f ` A)) = weight ?p (?f ` X)"
      using assms 
      unfolding xc_to_ss_def is_subset_sum_def Let_def
      by simp+
  have f_unfold:
    "?f ` X = (if X = {} then {} else {1..card X})" 
    "inj_on ?f X"
      using map_to_nat_unfold False
      by blast+

  have "?p \<ge> 2"
    by auto 
  hence weight_unfold:
  "weight ?p (?f ` X) = \<Sum>{x ^ ?p | x . x \<in> (?f ` X)}"
  "\<forall>A\<in>S. weight ?p (?f ` A) = \<Sum>{x ^ ?p | x . x \<in> (?f ` A)}"
    using weight_eq_poly[of ?p] 
    by blast+
  hence "(\<Sum>A\<in>S. weight ?p (?f ` A)) = \<Sum>{x ^ ?p | x . x \<in> (?f ` X)}"
    using S_prop(2)
    by argo
  moreover from weight_unfold(2) have 
  "(\<Sum>A\<in>S. weight ?p (?f ` A)) = (\<Sum>A\<in>S. \<Sum>{x ^ ?p | x . x \<in> (?f ` A)})"
    by simp
  ultimately have Sum_eq: "(\<Sum>A\<in>S. \<Sum>{x ^ ?p | x . x \<in> (?f ` A)}) = \<Sum>{x ^ ?p | x . x \<in> (?f ` X)}"
    by argo

  from False have "finite X" "\<Union>S \<subseteq> X"
    by blast+
  from S_prop(1) Sum_eq have "disjoint S"
   proof (induction S arbitrary: X rule: finite_induct)
    case empty
    then show ?case
      unfolding disjoint_def 
      by blast
  next
    case (insert x F)
    then show ?case
    
      sorry
    
  qed

thm disjoint_def
  
  moreover have "\<Union>S = X"
  proof (rule ccontr)
    assume "\<Union>S \<noteq> X"
    with False have prems: "\<Union>S \<subset> X" "finite (\<Union> S)"
      by (auto simp add: finite_subset)
    with S_prop have "\<forall>i \<in> S. finite i"
      by (metis Sup_upper finite_subset)
    hence *: "\<forall>i\<in>S. finite (?f ` i)"
      by blast

    with f_unfold prems have "inj_on ?f (\<Union>S)"
      unfolding inj_on_def 
      by blast
    with \<open>disjoint S\<close> have "disjoint ((`) ?f ` S)"
      by (simp add: disjoint_image)
    hence **:"\<forall>i\<in>S. \<forall>j\<in>S. i \<noteq> j \<longrightarrow> map_to_nat X ` i \<inter> map_to_nat X ` j = {}"
      unfolding disjoint_def 
      by (metis Sup_upper \<open>disjoint S\<close> \<open>inj_on ?f (\<Union> S)\<close> disjointD 
         image_empty inj_on_image_Int)
    
    have strict_subset: "\<Union> ((`) ?f ` S) \<subset> ?f ` X"
      using prems(1)
      by (metis \<open>inj_on ?f X\<close> image_Union inj_on_strict_subset)
    hence "(\<Sum>x\<in>\<Union> ((`) ?f ` S). x ^ ?p) < (\<Sum>x\<in>?f ` X. x ^ ?p)"
      proof-
        from strict_subset obtain b where b_def: "b \<in> ?f ` X - \<Union> ((`) ?f ` S)" 
          by blast
        hence "b \<in> ?f ` X"
          by blast
        moreover hence "\<forall>b \<in> ?f ` X. b > 0"
          using f_unfold
          by auto
        ultimately have "0 < b ^ max 2 (card S + 1)" "\<forall>b \<in> ?f ` X. b \<ge> 0"
          by force+

        moreover have "finite (?f ` X)"
          using False
          by blast
        thm sum_strict_mono2[of "?f ` X" "\<Union> ((`) ?f ` S)" b "(\<lambda>x. x ^ ?p)"]
        ultimately show ?thesis
          using b_def strict_subset 
            sum_strict_mono2[of "?f ` X" "\<Union> ((`) ?f ` S)" b "(\<lambda>x. x ^ ?p)"]
          by fast
      qed 
    moreover from \<open>finite S\<close> * ** have 
      "(\<Sum>x\<in>\<Union> ((`) ?f ` S). x ^ ?p) = (\<Sum>x\<in>S. \<Sum>x\<in>?f ` x. x ^ ?p)"
      using sum.UNION_disjoint[of S "(`) ?f" "(\<lambda>x. x ^ ?p)"]
      by blast
    ultimately have "(\<Sum>x\<in>S. \<Sum>x\<in>?f` x. x ^ ?p) < (\<Sum>x\<in>?f ` X. x ^ ?p)"
      by argo
    with S_prop
    show "False"
      unfolding weight_def
      by linarith
  qed 
    
  ultimately show ?thesis
    unfolding cover_def 
    by blast
qed
  
end 