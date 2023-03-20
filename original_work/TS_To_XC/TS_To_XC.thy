theory TS_To_XC
  imports TS_To_XC_aux
begin

section "useful definitions and the reduction function"

definition literal_sets
  :: "'a three_sat  \<Rightarrow> 'a xc_element set set" where
"literal_sets F = {{l}| l. l \<in> (literals_of_sat F)}"

definition clauses_with_literals 
  :: "'a three_sat \<Rightarrow> 'a xc_element set set" where
"clauses_with_literals F = {{C c, l} |c l. C c \<in> (clauses_of_sat F) \<and> l \<in> (literals_of_sat F) 
        \<and> l \<in> {L a c | a. a \<in> c}}"

definition var_true_literals
  :: "'a three_sat \<Rightarrow> 'a xc_element set set" where 
"var_true_literals F = 
  {{V v} \<union> {l. l \<in> (literals_of_sat F) 
  \<and> (\<exists>c. C c\<in> (clauses_of_sat F) \<and> L (Neg v) c = l)} |v. V v \<in> (vars_of_sat F)}"

definition var_false_literals
    :: "'a three_sat \<Rightarrow> 'a xc_element set set" where 
"var_false_literals F = 
  {{V v} \<union> {l. l \<in> (literals_of_sat F) 
  \<and> (\<exists>c. C c\<in> (clauses_of_sat F) \<and> L (Pos v) c = l)} |v. V v \<in> (vars_of_sat F)}"

abbreviation "comp_X F \<equiv> 
  vars_of_sat F \<union> clauses_of_sat F \<union> literals_of_sat F"
abbreviation "comp_S F \<equiv> 
    literal_sets F \<union> clauses_with_literals F 
  \<union> var_true_literals F \<union> var_false_literals F"

definition ts_xc :: "'a three_sat \<Rightarrow> 'a xc_element set * 'a xc_element set set" where 
"ts_xc F = (comp_X F, comp_S F)"

lemma ts_xc_is_collection:
  assumes "F \<in> three_cnf_sat" 
  shows "\<Union> (comp_S F) \<subseteq> (comp_X F)"
proof -
  let ?vars = "vars_of_sat F"
  let ?clauses = "clauses_of_sat F"
  let ?literals = "literals_of_sat F"

  let ?ls = "literal_sets F"
  let ?cs = "clauses_with_literals F"
  let ?vt = "var_true_literals F"
  let ?vf = "var_false_literals F"

  have x_part: "(comp_X F) = ?vars \<union> ?clauses \<union> ?literals"
  using assms ts_xc_def[of F] by (auto simp: Let_def)
    
  have s_part: "(comp_S F) = ?ls \<union> ?cs \<union> ?vt \<union> ?vf"
  using assms ts_xc_def[of F] by (auto simp: Let_def)

  have "\<Union>?ls = ?literals" 
    unfolding literal_sets_def by blast 

  moreover have "\<Union>?cs \<subseteq> ?literals \<union> ?clauses" 
    unfolding clauses_with_literals_def by blast

  moreover have "\<Union>?vt \<subseteq> ?literals \<union> ?vars"
    unfolding var_true_literals_def by blast

  moreover have "\<Union>?vf \<subseteq> ?literals \<union> ?vars" 
    unfolding var_false_literals_def by blast

  ultimately have "\<Union> (?ls \<union> ?cs \<union> ?vt \<union> ?vf) \<subseteq> ?vars \<union> ?clauses \<union> ?literals"
  by blast

  with x_part s_part show ?thesis by force
qed 

section "the proof for the soundness"

subsection "the construction of the cover"

definition constr_cover_clause
  :: "'a lit set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a xc_element set set" where 
"constr_cover_clause c \<sigma> = 
  (SOME s. \<exists>p \<in> c. (\<sigma>\<up>) p \<and> s = {{C c, L p c}} \<union> {{L q c} | q. q \<in> c \<and> q \<noteq> p \<and> (\<sigma>\<up>) q})" 

lemma constr_cover_clause_unfold:
assumes "\<sigma> \<Turnstile> F" "c \<in> set F"
shows "\<exists>p\<in>c. (\<sigma>\<up>) p \<and> constr_cover_clause c \<sigma> = {{C c, L p c}} \<union> {{L q c} | q. q \<in> c \<and> q \<noteq> p \<and> (\<sigma>\<up>) q}"
proof- 
  from assms have "\<exists>p \<in>c. (\<sigma>\<up>) p"
  unfolding models_def lift_def by blast

  thus "\<exists>p\<in>c. (\<sigma>\<up>) p \<and> constr_cover_clause c \<sigma> = {{C c, L p c}} \<union> {{L q c} | q. q \<in> c \<and> q \<noteq> p \<and> (\<sigma>\<up>) q}"
   unfolding constr_cover_clause_def
   apply auto
   apply (rule someI_ex)
   by blast
qed 
  
definition vars_sets 
  :: "'a three_sat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a xc_element set set" where 
"vars_sets F \<sigma> =
  {x_set | x_set. \<exists>x \<in> vars F.
       (if (\<sigma>\<up>) (Pos x) then (V x) \<in> x_set \<and> x_set \<in> var_true_literals F
        else (V x) \<in> x_set \<and> x_set \<in> var_false_literals F)}"

definition clause_sets
  :: "'a three_sat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a xc_element set set set" where 
  "clause_sets F \<sigma> = 
      {constr_cover_clause c \<sigma> |c. c \<in> set F}"

definition constr_cover 
  :: "'a three_sat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a xc_element set set" where 
"constr_cover F \<sigma> \<equiv> 
  (if F \<in> three_cnf_sat 
  then vars_sets F \<sigma> \<union> \<Union> (clause_sets F \<sigma>)
  else {})"

subsubsection "The constructed set is a collection"

lemma constr_cover_clause_is_collection:
assumes "\<sigma> \<Turnstile> F" "c \<in> set F"
 shows "constr_cover_clause c \<sigma> \<subseteq> (comp_S F)"
proof standard
  fix x   
  let ?s = "constr_cover_clause c \<sigma>"
  assume prem: "x \<in> ?s"

  from assms have "\<exists>p \<in>c. (\<sigma>\<up>) p"
    unfolding models_def lift_def by blast

  from assms have  "\<exists>p\<in>c. (\<sigma>\<up>) p \<and> ?s = {{C c, L p c}} \<union> {{L q c} | q. q \<in> c \<and> q \<noteq> p \<and> (\<sigma>\<up>) q}"
   using constr_cover_clause_unfold by blast

  then obtain p where 
    p_def: "?s = {{C c, L p c}} \<union> {{L q c} | q. q \<in> c \<and> q \<noteq> p \<and> (\<sigma>\<up>) q}" 
      "(\<sigma>\<up>) p" "p \<in> c"
     using \<open>\<exists>p \<in>c. (\<sigma>\<up>) p\<close> by blast

  with assms(2) have "\<forall>p \<in> c. {L p c} \<in> literal_sets F"
    unfolding literal_sets_def literals_of_sat_def 
    by fastforce

  hence "\<forall>p \<in> c. {{L q c} | q. q \<in> c \<and> q \<noteq> p \<and> (\<sigma>\<up>) q} \<subseteq> literal_sets F"
    by blast

  moreover from assms(2) have "\<forall>p \<in> c. {C c, L p c} \<in> clauses_with_literals F"
    unfolding clauses_with_literals_def literals_of_sat_def
    by force 

  ultimately have "x \<in> (literal_sets F \<union> clauses_with_literals F)"
    using prem p_def
  by auto

  then show "x \<in> comp_S F" 
    by blast
qed

lemma constr_cover_is_collection:
  "\<sigma> \<Turnstile> F \<Longrightarrow> constr_cover F \<sigma> \<subseteq> (comp_S F)"
  unfolding constr_cover_def vars_sets_def clause_sets_def
  apply auto
  using constr_cover_clause_is_collection 
  by blast

subsubsection "The constructed set is a cover"

paragraph "covers all variables"
lemma vars_in_vars_set_aux1:
  "\<forall>x\<in>vars_sets F \<sigma>. \<exists>v \<in> vars F. V v \<in> x"
  unfolding vars_sets_def by auto

lemma vars_in_vars_set_aux2:
  "\<forall>v\<in> vars F. \<exists>x \<in> var_true_literals F. V v \<in> x"
  unfolding var_true_literals_def vars_of_sat_def
  by auto

lemma vars_in_vars_set_aux3:
  "\<forall>v\<in> vars F. \<exists>x \<in> var_false_literals F. V v \<in> x"
  unfolding var_false_literals_def vars_of_sat_def
  by auto

lemmas vars_in_vars_set_aux=
vars_in_vars_set_aux1 vars_in_vars_set_aux2 vars_in_vars_set_aux3

lemma vars_in_vars_set:
  "vars_of_sat F \<subseteq> \<Union> (vars_sets F \<sigma>)"
  unfolding vars_of_sat_def vars_sets_def 
  using vars_in_vars_set_aux by (auto, meson)

paragraph "covers all clauses"

lemma clause_in_clause_set_aux:
assumes "\<sigma> \<Turnstile> F" "c \<in> set F"
shows  "C c \<in> \<Union>(constr_cover_clause c \<sigma>)" 
using constr_cover_clause_unfold [OF assms]
by fastforce

lemma clause_in_clause_set:
assumes "\<sigma> \<Turnstile> F"
shows "clauses_of_sat F \<subseteq> \<Union> (\<Union>(clause_sets F \<sigma>))"
unfolding clause_sets_def  clauses_of_sat_def
using clause_in_clause_set_aux[OF assms] 
by (auto, fastforce)

paragraph "covers all false literals"

lemma double_neg_id: 
  "\<not> (\<sigma>\<up>) (Neg a) \<longleftrightarrow> (\<sigma>\<up>) (Pos a)"
unfolding models_def lift_def
by simp

lemma false_literal_in_vars_sets_aux:
assumes "\<not> (\<sigma>\<up>) x" "x \<in> c" "c \<in> set F"
shows " \<exists>s \<in> vars_sets F \<sigma>. L x c \<in> s"
proof (cases x) 
  case (Pos a)
  then show ?thesis
  proof -
    let ?s = "{V a} \<union> {l \<in> literals_of_sat F. \<exists>c. C c \<in> clauses_of_sat F \<and> L (Pos a) c = l}"
    
    have "a \<in> vars F"
      using assms(2-3) Pos by (force simp add: vars_correct)

    moreover then have "?s \<in> var_false_literals F"
      unfolding var_false_literals_def vars_of_sat_def
      by blast

    moreover have "\<not> (\<sigma>\<up>) (Pos a)"
      using Pos assms(1) by blast

    ultimately have "?s \<in> vars_sets F \<sigma>" 
      unfolding vars_sets_def 
      by force

    moreover have "L x c \<in> ?s"
      using Pos assms(2-3) by simp

    ultimately show ?thesis 
      by meson
  qed 
next
  case (Neg b)
  then show ?thesis
  proof -
    let ?s = "{V b} \<union> {l \<in> literals_of_sat F. \<exists>c. C c \<in> clauses_of_sat F \<and> L (Neg b) c = l}"
    
    have "b \<in> vars F"
      using assms(2-3) Neg by (force simp add: vars_correct)

    moreover then have "?s \<in> var_true_literals F"
      unfolding var_true_literals_def vars_of_sat_def
      by blast

    moreover have "(\<sigma>\<up>) (Pos b)"
      using Neg assms(1) 
      by (force simp add: double_neg_id)

    ultimately have "?s \<in> vars_sets F \<sigma>" 
      unfolding vars_sets_def 
      by force

    moreover have "L x c \<in> ?s"
      using Neg assms(2-3) by simp

    ultimately show ?thesis 
      by meson
  qed 
qed

lemma false_literal_in_vars_sets:
"\<lbrakk>\<not> (\<sigma>\<up>) x; x \<in> c; c \<in> set F\<rbrakk> \<Longrightarrow> L x c \<in> \<Union>(vars_sets F \<sigma>)"
  using false_literal_in_vars_sets_aux 
  by fast

paragraph "covers all true literals"

lemma true_literals_in_clause_sets_aux:
assumes "\<sigma> \<Turnstile> F" "(\<sigma>\<up>) x" "x \<in> c" "c \<in> set F"
shows "L x c \<in> \<Union>(constr_cover_clause c \<sigma>)"
proof -
let ?s = "constr_cover_clause c \<sigma>"

from constr_cover_clause_unfold[OF assms(1) assms(4)]
have "\<exists>p\<in>c. (\<sigma>\<up>) p \<and> ?s = {{C c, L p c}} \<union> {{L q c} |q. q \<in> c \<and> q \<noteq> p \<and> (\<sigma>\<up>) q}"
  by blast

then obtain p where p_def:
"p \<in> c" "(\<sigma>\<up>) p" "?s = {{C c, L p c}} \<union> {{L q c} |q. q \<in> c \<and> q \<noteq> p \<and> (\<sigma>\<up>) q}"
  by blast 

hence "\<Union>?s = {C c} \<union> {L q c|q. q \<in> c \<and> (\<sigma>\<up>) q}"
  by blast

then show ?thesis 
  using assms(2-3) by blast
qed

lemma true_literals_in_clause_sets:
"\<lbrakk>\<sigma> \<Turnstile> F;(\<sigma>\<up>) x; x \<in> c; c \<in> set F\<rbrakk> \<Longrightarrow> L x c \<in> \<Union> (\<Union>(clause_sets F \<sigma>))"
  unfolding clause_sets_def
  using true_literals_in_clause_sets_aux 
  by fast

paragraph "Integration of all true and false literals"

lemma literals_in_construction_aux:
assumes "\<sigma> \<Turnstile> F" "x \<in> c" "c \<in> set F" "F \<in> three_cnf_sat"
shows "L x c \<in> \<Union>(constr_cover F \<sigma>)"
proof (cases "(\<sigma>\<up>) x")
  case True
  with assms have "L x c \<in> \<Union> (\<Union>(clause_sets F \<sigma>))"
    using true_literals_in_clause_sets by blast
  then show ?thesis
    unfolding constr_cover_def 
    using assms(4) by simp
next
  case False
  with assms have "L x c \<in> \<Union>(vars_sets F \<sigma>)"
    using false_literal_in_vars_sets by blast
  then show ?thesis
    unfolding constr_cover_def 
    using assms(4) by simp
qed


corollary literals_in_construction: 
"\<lbrakk>\<sigma> \<Turnstile> F; \<forall>cls\<in>set F. card cls = 3\<rbrakk> \<Longrightarrow> literals_of_sat F \<subseteq> \<Union>(constr_cover F \<sigma>)"
proof - 
  assume "\<sigma> \<Turnstile> F" "\<forall>cls\<in>set F. card cls = 3"
  hence "F \<in> three_cnf_sat" 
    unfolding three_cnf_sat_def sat_def by blast

  with \<open>\<sigma> \<Turnstile> F\<close> have "\<forall>c\<in>set F. \<forall>x\<in>c.  L x c \<in> \<Union> (constr_cover F \<sigma>)"
    using literals_in_construction_aux by blast

  then show "literals_of_sat F \<subseteq> \<Union>(constr_cover F \<sigma>)"
    unfolding literals_of_sat_def 
    by fastforce
qed 

subsubsection "The constructed sets are pairwise disjoint"

lemma clause_sets_disj:
assumes "\<sigma> \<Turnstile> F" 
shows  "disjoint (\<Union> (clause_sets F \<sigma>))"
  unfolding clause_sets_def 
  apply (rule disjointI)
  apply (auto)
  using constr_cover_clause_unfold[OF assms] 
  apply (smt (z3) Un_iff empty_iff insertE mem_Collect_eq 
    xc_element.simps(2) xc_element.simps(3) xc_element.simps(9))+
  done 

lemma vars_sets_disj:
assumes "\<sigma> \<Turnstile> F" 
shows "disjoint (vars_sets F \<sigma>)"
  unfolding vars_sets_def
  apply (rule disjointI)
  apply auto 
  sorry

subsection "The soundness lemma"
  
lemma ts_xc_sound:
  "\<lbrakk>\<sigma> \<Turnstile> F; \<forall>cls \<in> set F. card cls = 3\<rbrakk> \<Longrightarrow> cover (constr_cover F \<sigma>) (comp_X F)"
  unfolding cover_def
  proof
    assume prems: "\<sigma> \<Turnstile> F" "\<forall>cls \<in> set F. card cls = 3"
    show "\<Union> (constr_cover F \<sigma>) = comp_X F"
    proof (standard, goal_cases)
      case 1

      have "constr_cover F \<sigma> \<subseteq> comp_S F"
        using constr_cover_is_collection prems by blast 

      moreover have "F \<in> three_cnf_sat"
        unfolding three_cnf_sat_def sat_def
        using prems by blast

      ultimately show ?case
        using ts_xc_is_collection by blast
    next
      case 2
      have "F \<in> three_cnf_sat"
        unfolding three_cnf_sat_def sat_def
        using prems by blast

      have "vars_of_sat F \<subseteq> \<Union> (constr_cover F \<sigma>)"
        unfolding constr_cover_def
        using vars_in_vars_set \<open>F \<in> three_cnf_sat\<close>
        by auto
        
      moreover have "clauses_of_sat F \<subseteq> \<Union> (constr_cover F \<sigma>)"
        unfolding constr_cover_def 
        using clause_in_clause_set[OF prems(1)] \<open>F \<in> three_cnf_sat\<close>
        by auto

      moreover have "literals_of_sat F \<subseteq> \<Union> (constr_cover F \<sigma>)"  
        using prems literals_in_construction 
        by blast

      ultimately show ?case 
        by blast
    qed
  next
    assume prems: "\<sigma> \<Turnstile> F" "\<forall>cls \<in> set F. card cls = 3"
    have "F \<in> three_cnf_sat"
      unfolding three_cnf_sat_def sat_def
      using prems by blast

    show "disjoint (constr_cover F \<sigma>)"
    sorry
  qed 

end