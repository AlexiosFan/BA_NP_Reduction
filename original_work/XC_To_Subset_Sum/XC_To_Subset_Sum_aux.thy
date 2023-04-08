theory  XC_To_Subset_Sum_aux
  imports "../TS_To_XC/XC_Definition"
begin

definition is_subset_sum :: "'a set \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
"is_subset_sum S w B \<equiv> (\<exists>S'\<subseteq>S. \<Sum>(w`S') = B)"

definition "subset_sum \<equiv> {(S, w, B) | S w B. is_subset_sum S w B}"

(*construction via a bijective function, a preliminary lemma that 
there is a bijective function from a finite set to a finite natural number interval
from 0 to the cardinality of the set*)

lemma bij_exist: 
  "finite S \<Longrightarrow> \<exists>f. (if S = {} then bij_betw f S {} else bij_betw f S {0..card S-1})"
proof (induction S rule: finite_induct)
  case (insert x F)
  then obtain f where 
    f_def: "if F = {} then bij_betw f F {} else bij_betw f F {0..card F - 1}"
    by blast
  then show ?case
  proof (cases "F = {}")
  case True
    then have "insert x F = {x}"
      by argo
    moreover with True have "card (insert x F) = 1"
      using card_insert_if[OF insert(1), of x]
      by fastforce
    ultimately have "bij_betw (f (x:=0)) (insert x F) {0..card (insert x F) - 1}"
      unfolding bij_betw_def inj_on_def 
      by auto

    moreover from True f_def have "bij_betw f F {}"
      by argo
    ultimately show ?thesis 
      by auto
  next
    case False
    with f_def have "bij_betw f F {0..card F - 1}"
      by argo
    hence "inj_on f F" "f ` F = {0..card F - 1}"
      unfolding bij_betw_def 
      by blast+
    moreover from insert have "card (insert x F) - 1 = card F"
      using card_insert_if[OF insert(1), of x]
      by force 
    ultimately have "f(x := card F) ` insert x F = {0..card (insert x F) - 1}"
      using insert(2) 
      by (auto, force)
    
    moreover have "inj_on (f(x := card F)) (insert x F)"
      using \<open>inj_on f F\<close> unfolding inj_on_def
      proof (safe, goal_cases)
        case (1 a b)
        from 1(3) insert(2) \<open>f ` F = {0..card F - 1}\<close> 
        have "(f(x := card F)) b \<in> {0..card F - 1}"
          by auto
        with False have "(f(x := card F)) b \<noteq> card F"
          using card_0_eq[OF insert(1)]
          by auto 
        
        with 1(2) have "False"
          by force
        then show ?case
          by blast
      next
        case (2 a b)
        from 2(3) insert(2) \<open>f ` F = {0..card F - 1}\<close> 
        have "(f(x := card F)) a \<in> {0..card F - 1}"
          by auto
        with False have "(f(x := card F)) a \<noteq> card F"
          using card_0_eq[OF insert(1)]
          by auto 
        
        with 2(2) have "False"
          by force
        then show ?case
          by blast
      next
        case (3 a b)
        from 3(3) 3(4) insert(2) have 
        "(f(x := card F)) a = f a" "(f(x := card F)) b = f b"
          by auto
        with 3 show ?case
          by metis
      qed

    ultimately have "bij_betw (f(x := card F)) (insert x F) {0..card (insert x F) - 1}"
      unfolding bij_betw_def
      by blast

    moreover from insert have "insert x F \<noteq> {}"
      by blast
    ultimately show ?thesis 
      by metis
  qed
qed (simp add: bij_betw_def inj_on_def)


end 