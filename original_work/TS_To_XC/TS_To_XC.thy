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

lemma ts_xc_is_collection: "\<Union> (comp_S F) \<subseteq> (comp_X F)"
proof -
  let ?vars = "vars_of_sat F"
  let ?clauses = "clauses_of_sat F"
  let ?literals = "literals_of_sat F"

  let ?ls = "literal_sets F"
  let ?cs = "clauses_with_literals F"
  let ?vt = "var_true_literals F"
  let ?vf = "var_false_literals F"

  have x_part: "(comp_X F) = ?vars \<union> ?clauses \<union> ?literals"
  using ts_xc_def[of F] by (auto simp: Let_def)
    
  have s_part: "(comp_S F) = ?ls \<union> ?cs \<union> ?vt \<union> ?vf"
  using ts_xc_def[of F] by (auto simp: Let_def)

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
  (if F \<in> cnf_sat 
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
assumes "\<sigma> \<Turnstile> F" "x \<in> c" "c \<in> set F" "F \<in> cnf_sat"
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
"\<sigma> \<Turnstile> F \<Longrightarrow> literals_of_sat F \<subseteq> \<Union>(constr_cover F \<sigma>)"
proof - 
  assume "\<sigma> \<Turnstile> F" 
  hence "F \<in> cnf_sat" 
    unfolding cnf_sat_def sat_def by blast

  with \<open>\<sigma> \<Turnstile> F\<close> have "\<forall>c\<in>set F. \<forall>x\<in>c.  L x c \<in> \<Union> (constr_cover F \<sigma>)"
    using literals_in_construction_aux by blast

  then show "literals_of_sat F \<subseteq> \<Union>(constr_cover F \<sigma>)"
    unfolding literals_of_sat_def 
    by fastforce
qed 

subsubsection "The constructed sets are pairwise disjoint"

paragraph "clause_sets are disjoint"

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

paragraph "vars_sets are disjoint"

abbreviation "true_literals v F \<equiv> {V v} \<union> {l. l \<in> (literals_of_sat F) 
  \<and> (\<exists>c. C c\<in> (clauses_of_sat F) \<and> L (Neg v) c = l)}"
abbreviation "false_literals v F \<equiv> {V v} \<union> {l. l \<in> (literals_of_sat F) 
  \<and> (\<exists>c. C c\<in> (clauses_of_sat F) \<and> L (Pos v) c = l)}"

lemma true_false_literals_noteq: 
  "v \<in> vars F \<Longrightarrow> true_literals v F \<noteq> false_literals v F"
proof -
  assume "v \<in> vars F"
  then have "(v \<in> var ` \<Union> (set F))"
    using vars_correct[of v F] by blast 
  then have "\<exists>c\<in> set F. v \<in> var ` c"
    by blast
  
  have "\<exists>c. C c \<in> (clauses_of_sat F) \<and>
    (L (Neg v) c \<in> (literals_of_sat F) \<or> L (Pos v) c \<in> (literals_of_sat F))"
    unfolding literals_of_sat_def clauses_of_sat_def
    using comp_literals_correct[of F "{}"] 
    apply auto
    using \<open>\<exists>c\<in> set F. v \<in> var ` c\<close> 
    by (metis imageE var.elims)

  then show  "true_literals v F \<noteq> false_literals v F" 
    by fast
qed 

lemma true_literals_not_in_false:
  "v \<in> vars F \<Longrightarrow> \<forall>u\<in> vars F. true_literals v F \<noteq> false_literals u F"
proof 
  fix u 
  assume  "v \<in> vars F" "u \<in> vars F"  

  have "\<forall>x\<in> true_literals v F. x = V v \<or> (\<exists>c. x = L (Neg v) c)"
    by blast
  moreover have "\<forall>x\<in> false_literals u F. x = V u \<or> (\<exists>c. x = L (Pos u) c)"
    by blast 

  ultimately show "true_literals v F \<noteq> false_literals u F" 
  apply (cases "v\<noteq>u")
  using true_false_literals_noteq[OF \<open>v \<in> vars F\<close>] by blast+ 
qed 
 

lemma false_literals_not_in_true:
  "v \<in> vars F \<Longrightarrow> \<forall>u\<in> vars F. false_literals v F \<noteq> true_literals u F"
proof 
  fix u 
  assume  "v \<in> vars F" "u \<in> vars F"  

  have "\<forall>x\<in> true_literals v F. x = V v \<or> (\<exists>c. x = L (Neg v) c)"
    by blast
  moreover have "\<forall>x\<in> false_literals u F. x = V u \<or> (\<exists>c. x = L (Pos u) c)"
    by blast 

  ultimately show "false_literals v F \<noteq> true_literals u F" 
  apply (cases "v\<noteq>u")
  using true_false_literals_noteq[OF \<open>v \<in> vars F\<close>] by blast+ 
qed 
 

lemma vars_sets_true_assignment:
"\<lbrakk>(\<sigma>\<up>) (Pos v); v \<in> vars F\<rbrakk> \<Longrightarrow> true_literals v F \<in> vars_sets F \<sigma> \<and> false_literals v F \<notin> vars_sets F \<sigma>"
proof standard
  assume "(\<sigma>\<up>) (Pos v)" "v \<in> vars F"

  have "true_literals v F \<in> var_true_literals F"
    unfolding var_true_literals_def vars_of_sat_def
    using \<open>v \<in> vars F\<close> by blast

  then show "true_literals v F \<in> vars_sets F \<sigma>"
    unfolding vars_sets_def
    using \<open>(\<sigma>\<up>) (Pos v)\<close> \<open>v \<in> vars F\<close> 
    by auto

  from \<open>v \<in> vars F\<close> have "false_literals v F \<notin> var_true_literals F"
    unfolding var_true_literals_def vars_of_sat_def
    using false_literals_not_in_true by force

  then show "false_literals v F \<notin> vars_sets F \<sigma>"
    unfolding vars_sets_def
    using \<open>(\<sigma>\<up>) (Pos v)\<close> \<open>v \<in> vars F\<close> 
    by auto
qed 

lemma vars_sets_false_assignment:
"\<lbrakk>\<not> (\<sigma>\<up>) (Pos v); v \<in> vars F\<rbrakk> \<Longrightarrow> true_literals v F \<notin> vars_sets F \<sigma> \<and> false_literals v F \<in> vars_sets F \<sigma>"
proof standard
  assume "\<not> (\<sigma>\<up>) (Pos v)" "v \<in> vars F"

  have "false_literals v F \<in> var_false_literals F"
    unfolding var_false_literals_def vars_of_sat_def
    using \<open>v \<in> vars F\<close> by blast

  then show "false_literals v F \<in> vars_sets F \<sigma>"
    unfolding vars_sets_def
    using \<open>\<not> (\<sigma>\<up>) (Pos v)\<close> \<open>v \<in> vars F\<close> 
    by fastforce 
    

  from \<open>v \<in> vars F\<close> have "true_literals v F \<notin> var_false_literals F"
    unfolding var_false_literals_def vars_of_sat_def
    using true_literals_not_in_false by force

  then show "true_literals v F \<notin> vars_sets F \<sigma>"
    unfolding vars_sets_def
    using \<open>\<not> (\<sigma>\<up>) (Pos v)\<close> \<open>v \<in> vars F\<close> 
    by auto
qed 

lemma vars_sets_bipartite:
  "v \<in> vars F 
    \<Longrightarrow> (true_literals v F \<notin> vars_sets F \<sigma> \<and> false_literals v F \<in> vars_sets F \<sigma>) 
        \<or> (true_literals v F \<in> vars_sets F \<sigma> \<and> false_literals v F \<notin> vars_sets F \<sigma>)"
  using vars_sets_false_assignment vars_sets_true_assignment 
  by fast

lemma vars_sets_subset:
  "vars_sets F \<sigma> \<subseteq> (var_true_literals F \<union> var_false_literals F)"
  unfolding vars_sets_def var_true_literals_def var_false_literals_def
  by auto

lemma var_true_literals_disj:
  "disjoint (var_true_literals F)"
  apply (rule disjointI)
  unfolding var_true_literals_def
  by auto

lemma var_false_literals_disj:
  "disjoint (var_false_literals F)"
  apply (rule disjointI)
  unfolding var_false_literals_def
  by auto


lemma vars_sets_disj_aux:
assumes "A \<in> vars_sets F \<sigma>"
shows "\<forall>s\<in>vars_sets F \<sigma>. s \<noteq> A \<longrightarrow> s \<inter> A = {}"
proof 
  fix s
  assume "s \<in> vars_sets F \<sigma>"
  show "s \<noteq> A \<longrightarrow> s \<inter> A = {}"
  proof 
    assume "s \<noteq> A"
    consider 
      "s \<in> var_false_literals F \<and> A \<in> var_false_literals F" |
      "s \<in> var_false_literals F \<and> A \<in> var_true_literals F \<or> 
        s \<in> var_true_literals F \<and> A \<in> var_false_literals F" |
      "s \<in> var_true_literals F \<and> A \<in> var_true_literals F"
        using vars_sets_subset assms \<open>s \<in> vars_sets F \<sigma>\<close> 
        by blast
    then show "s \<inter> A = {}"
    proof (cases)
      case 1
      then show ?thesis
      using disjointD var_false_literals_disj 
        \<open>s \<noteq> A\<close> by blast
    next
      case 2
      then show ?thesis
      unfolding var_false_literals_def var_true_literals_def vars_of_sat_def
      using assms \<open>s \<in> vars_sets F \<sigma>\<close> vars_sets_bipartite 
      by fast
    next
      case 3
      then show ?thesis 
      using disjointD var_true_literals_disj 
        \<open>s \<noteq> A\<close> by blast
    qed
  qed 
qed 

lemma vars_sets_disj:
"disjoint (vars_sets F \<sigma>)"
  apply (rule disjointI)
  using vars_sets_disj_aux 
  by blast

paragraph "clause sets and var sets are disjoint to each other"

lemma vars_sets_only_false_literals_aux:
"\<forall>s\<in>vars_sets F \<sigma>. \<forall>x \<in> s. x \<in> vars_of_sat F \<or> (x \<in> literals_of_sat F \<and> \<not>(\<sigma>\<Up>) x)"
unfolding vars_sets_def
apply auto 
unfolding var_false_literals_def var_true_literals_def
using double_neg_id by fastforce+

corollary vars_sets_only_false_literals:
"\<forall>x\<in>\<Union>(vars_sets F \<sigma>). x \<in> vars_of_sat F \<or> (x \<in> literals_of_sat F \<and> \<not>(\<sigma>\<Up>) x)"
using vars_sets_only_false_literals_aux by blast

lemma constr_cover_clause_only_true_literals_aux1:
assumes "\<sigma> \<Turnstile> F" "c \<in> set F"
shows "\<forall>s\<in> constr_cover_clause c \<sigma>. \<forall>x\<in>s. x \<in> clauses_of_sat F \<or> (x \<in> literals_of_sat F \<and> (\<sigma>\<Up>) x)"
proof  auto
  fix s x
  assume prems: "s \<in> constr_cover_clause c \<sigma>" "x \<in> s" "x \<notin> clauses_of_sat F"
  
  obtain p where p_def:"p \<in> c" "(\<sigma>\<up>) p"
  "constr_cover_clause c \<sigma> = {{C c, L p c}} \<union> {{L q c} |q. q \<in> c \<and> q \<noteq> p \<and> (\<sigma>\<up>) q}"
    using constr_cover_clause_unfold[OF assms] by blast 

  hence "x \<in> {L q c |q. q \<in> c \<and> (\<sigma>\<up>) q}"
    using prems assms unfolding clauses_of_sat_def 
    by blast

  with assms(2) show "(\<sigma>\<Up>) x" "x \<in> literals_of_sat F"
  unfolding literals_of_sat_def
  by fastforce+  
qed

corollary constr_cover_clause_only_true_literals_aux2:
assumes "\<sigma> \<Turnstile> F"
shows "\<forall>s\<in> \<Union>(clause_sets F \<sigma>). \<forall>x\<in>s. x \<in> clauses_of_sat F \<or> (x \<in> literals_of_sat F \<and> (\<sigma>\<Up>) x)"
unfolding clause_sets_def
using constr_cover_clause_only_true_literals_aux1[OF assms]
by blast

corollary constr_cover_clause_only_true_literals:
assumes "\<sigma> \<Turnstile> F"
shows "\<forall>x\<in> \<Union>(\<Union>(clause_sets F \<sigma>)). x \<in> clauses_of_sat F \<or> (x \<in> literals_of_sat F \<and> (\<sigma>\<Up>) x)"
using constr_cover_clause_only_true_literals_aux2[OF assms]
by blast

lemma vars_clauses_set_disj:
assumes "\<sigma> \<Turnstile> F" 
shows "\<Union>(vars_sets F \<sigma>) \<inter> \<Union> (\<Union> (clause_sets F \<sigma>)) = {}"
using assms constr_cover_clause_only_true_literals vars_sets_only_false_literals
unfolding vars_of_sat_def clauses_of_sat_def literals_of_sat_def
by fastforce

corollary constr_cover_disj:
"\<sigma> \<Turnstile> F \<Longrightarrow> disjoint ((vars_sets F \<sigma>) \<union> (\<Union> (clause_sets F \<sigma>)))"
using disjoint_union vars_sets_disj clause_sets_disj vars_clauses_set_disj
by blast  

subsection "The soundness lemma"
  
lemma ts_xc_sound_aux:
  "\<sigma> \<Turnstile> F \<Longrightarrow> cover (constr_cover F \<sigma>) (comp_X F)"
  unfolding cover_def
  proof
    assume prems: "\<sigma> \<Turnstile> F" 
    show "\<Union> (constr_cover F \<sigma>) = comp_X F"
    proof (standard, goal_cases)
      case 1
      have "constr_cover F \<sigma> \<subseteq> comp_S F"
        using constr_cover_is_collection prems by blast 
      moreover have "F \<in> cnf_sat"
        unfolding cnf_sat_def sat_def
        using prems by blast
      ultimately show ?case
        using ts_xc_is_collection by blast
    next
      case 2
      have "F \<in> cnf_sat"
        unfolding cnf_sat_def sat_def
        using prems by blast
      have "vars_of_sat F \<subseteq> \<Union> (constr_cover F \<sigma>)"
        unfolding constr_cover_def
        using vars_in_vars_set \<open>F \<in> cnf_sat\<close>
        by auto 
      moreover have "clauses_of_sat F \<subseteq> \<Union> (constr_cover F \<sigma>)"
        unfolding constr_cover_def 
        using clause_in_clause_set[OF prems(1)] \<open>F \<in> cnf_sat\<close>
        by auto
      moreover have "literals_of_sat F \<subseteq> \<Union> (constr_cover F \<sigma>)"  
        using prems literals_in_construction 
        by blast
      ultimately show ?case 
        by blast
    qed
  next
    assume prems: "\<sigma> \<Turnstile> F" 
    have "F \<in> cnf_sat"
      unfolding cnf_sat_def sat_def
      using prems by blast
    show "disjoint (constr_cover F \<sigma>)"
      unfolding constr_cover_def 
      using prems constr_cover_disj 
      by auto
  qed 

lemma ts_xc_sound:
  "F \<in> cnf_sat \<Longrightarrow> ts_xc F \<in> exact_cover"
  proof (goal_cases) 
    let ?X = "comp_X F"
    let ?S = "comp_S F"
  case 1
    hence prems: "\<exists>\<sigma>. \<sigma> \<Turnstile> F" 
      unfolding cnf_sat_def sat_def
      by blast
    then obtain \<sigma> where sig_def: "\<sigma> \<Turnstile> F"
      by blast
    have "(?X, ?S) \<in> exact_cover"
      apply (rule exact_cover_I)
      apply (rule constr_cover_is_collection[OF sig_def])
      apply (rule ts_xc_is_collection)
      apply (rule ts_xc_sound_aux[OF sig_def])
      done 
    then show ?case 
      unfolding ts_xc_def 
      by simp
  qed

section "The proof of the completeness"

definition "constr_model S' F = 
(\<lambda>x. 
    if (\<exists>s \<in> S'. \<exists>c \<in> set F. s = {C c, L (Pos x) c} \<and> (Pos x) \<in> c) 
    then True
    else if (\<exists>s \<in> S'. \<exists>c \<in> set F. s = {C c, L (Neg x) c} \<and> (Neg x) \<in> c)
    then False
    else False)"

lemma clause_only_binary:
  "\<forall>c \<in> clauses_of_sat F. \<forall>s\<in>(comp_S F). c \<in> s \<longrightarrow> s \<in> clauses_with_literals F"
proof standard
  fix c 
  assume prems: "c \<in> clauses_of_sat F"

  hence "\<forall>s \<in> literal_sets F. c \<notin> s"
        "\<forall>s \<in> var_true_literals F. c \<notin> s"
        "\<forall>s \<in> var_false_literals F. c \<notin> s"
    unfolding literal_sets_def var_true_literals_def var_false_literals_def
      clauses_of_sat_def literals_of_sat_def
    by fastforce+

  then show "\<forall>s\<in>(comp_S F). c \<in> s \<longrightarrow> s \<in> clauses_with_literals F"
  by blast
qed 


lemma clauses_with_literals_satisfiability:
  "s \<in> clauses_with_literals F \<Longrightarrow> C c \<in> s \<Longrightarrow> (\<exists>l \<in> c. s = {C c, L l c})"
  unfolding clauses_with_literals_def
  by blast

lemma constr_model_exists:
  "\<lbrakk>S' \<subseteq> S; cover S' X; ts_xc F = (X, S)\<rbrakk> 
    \<Longrightarrow> (\<forall>c\<in> set F. \<exists>s\<in> S'. \<exists>l \<in> c. s = {C c, L l c})"
proof
  fix c 
  assume "S' \<subseteq> S" "cover S' X" "ts_xc F = (X, S)" 
  "c \<in> set F"

  from \<open>c \<in> set F\<close> have "C c \<in> clauses_of_sat F"
    unfolding clauses_of_sat_def 
    by simp 
  moreover from \<open>ts_xc F = (X, S)\<close> 
  have "S = comp_S F" "X = comp_X F"
    unfolding ts_xc_def 
    by force+
  ultimately 
  have prem: "\<forall>s\<in>S. C c \<in> s \<longrightarrow> s \<in> clauses_with_literals F"
    using clause_only_binary 
    by blast

  from \<open>C c \<in> clauses_of_sat F\<close> \<open>X = comp_X F\<close>
  have "C c \<in> X" 
    by fastforce
  with \<open>cover S' X\<close> have "\<exists>s \<in> S'. C c \<in> s"
    unfolding cover_def 
    by blast
  moreover from \<open>S' \<subseteq> S\<close>
  have "\<forall>s \<in> S'. C c \<in> s \<longrightarrow> s \<in> clauses_with_literals F"
    using prem
    by blast
  ultimately obtain s where "s \<in> S'" "C c \<in> s" "s \<in> clauses_with_literals F"
    by blast
  hence "(\<exists>l \<in> c. s = {C c, L l c})"
    using clauses_with_literals_satisfiability
    by blast
  with \<open>s \<in> S'\<close> show "\<exists>s \<in> S'. \<exists>l\<in>c. s = {C c, L l c}"
    by blast
qed 

lemma vars_only_in_true_false_literals:
assumes "s \<in> comp_S F" "V x \<in> s"
shows "s = true_literals x F \<or> s = false_literals x F"
proof -
have "V x \<notin> \<Union>(literal_sets F)"
  unfolding literal_sets_def literals_of_sat_def
  by force 
with assms(2) have limit1: "s \<notin> literal_sets F"
  by fastforce 

have "V x \<notin> \<Union>(clauses_with_literals F)"
  unfolding clauses_with_literals_def clauses_of_sat_def
  by blast
with assms(2) have limit2: "s \<notin> clauses_with_literals F"
  by fastforce

from limit1 limit2 assms(1)
have "s \<in> var_true_literals F \<or> s \<in> var_false_literals F"
  by blast
then consider "s \<in> var_true_literals F" | "s \<in> var_false_literals F"
  by blast
then show ?thesis
  proof (cases)
    case 1
    with assms(2) have "s = true_literals x F"
      unfolding var_true_literals_def
      by fastforce
    then show ?thesis 
      by blast
  next
    case 2
    with assms(2) have "s = false_literals x F"
      unfolding var_false_literals_def
      by fastforce
    then show ?thesis
      by blast
  qed
qed 

lemma constr_model_disj_aux:
assumes  "cover S' (comp_X F)" "S' \<subseteq> (comp_S F)" "{C c, L (Pos x) c} \<in> S'"
shows "\<not>(\<exists>c'. {C c', L (Neg x) c'} \<in> S')"
proof 
  assume "\<exists>c'. {C c', L (Neg x) c'} \<in> S'"
  then obtain c' where c'_def: "{C c', L (Neg x) c'} \<in> S'"
    by blast
  show "False"
  proof (cases "c = c'")
    case True
    from assms(1) have "disjoint S'"
      unfolding cover_def
      by blast
    with c'_def assms(3) disjointD True 
    show ?thesis
      by blast
  next
    case False
    from assms(1) assms(3) c'_def 
    have "C c \<in> comp_X F" "C c' \<in> comp_X F"
      unfolding cover_def
      by blast+
    hence "C c \<in> clauses_of_sat F" "C c' \<in> clauses_of_sat F"
      unfolding vars_of_sat_def literals_of_sat_def
      by simp+

    moreover from assms(2-3) c'_def
    have "{C c, L (Pos x) c} \<in> comp_S F" "{C c', L (Neg x) c'} \<in> comp_S F"
      by blast+
    ultimately have
    "{C c, L (Pos x) c} \<in> clauses_with_literals F"
    "{C c', L (Neg x) c'} \<in> clauses_with_literals F"
      using clause_only_binary
      by blast+
    hence c_x_unfold:
    "C c \<in> clauses_of_sat F" "C c' \<in> clauses_of_sat F"
    "Pos x \<in> c" "Neg x \<in> c'"
      unfolding clauses_with_literals_def
      by (simp add: doubleton_eq_iff)+
    with \<open>C c \<in> clauses_of_sat F\<close> have "x \<in> vars F"
      unfolding clauses_of_sat_def vars_correct 
      by force
    hence "V x \<in> vars_of_sat F"
      unfolding vars_of_sat_def
      by simp
    then have "V x \<in> comp_X F"
      by simp
    with assms(1) have "\<exists>s \<in> S'. V x \<in> s"
      unfolding cover_def 
      by blast
    then obtain s where s_def: "s \<in> S'" "V x \<in> s"
      by blast
    hence "s \<in> comp_S F"
      using assms(2) 
      by blast
    with \<open>V x \<in> s\<close> have 
    "s = true_literals x F \<or> s = false_literals x F"
      using vars_only_in_true_false_literals[of s F x]
      by fastforce
    then consider "s = true_literals x F" | "s = false_literals x F"
      by blast
    then show ?thesis
    proof (cases)
      case 1
      have "L (Neg x) c' \<in> comp_literals F {}"
        using c_x_unfold 
        unfolding clauses_of_sat_def
        by auto
      hence "L (Neg x) c' \<in> true_literals x F"
        by simp
      moreover have "L (Neg x) c' \<in> {C c', L (Neg x) c'}"
        by blast
      moreover from assms(1)
      have "disjoint S'"
        unfolding cover_def 
        by blast
      ultimately show ?thesis
        using disjointD[of S', OF _ c'_def s_def(1)] 1
        by blast
    next
      case 2
      have "L (Pos x) c \<in> comp_literals F {}"
        using c_x_unfold 
        unfolding clauses_of_sat_def
        by auto
      hence "L (Pos x) c \<in> false_literals x F"
        by simp
      moreover have "L (Pos x) c \<in> {C c, L (Pos x) c}"
        by blast
      moreover from assms(1)
      have "disjoint S'"
        unfolding cover_def 
        by blast
      ultimately show ?thesis
        using disjointD[of S', OF _ assms(3) s_def(1)] 2
        by blast
    qed
  qed
qed 

lemma ts_xc_complete:
  "ts_xc F \<in> exact_cover \<Longrightarrow> F \<in> cnf_sat"
proof -
  let ?X = "comp_X F"
  let ?S = "comp_S F"

  assume "ts_xc F \<in> exact_cover"
  then have "ts_xc F = (?X, ?S)"
    unfolding ts_xc_def 
    by simp 
  with \<open>ts_xc F \<in> exact_cover\<close> 
  have "\<exists>S' \<subseteq> ?S. cover S' ?X"
    using exact_cover_D ts_xc_is_collection
    by metis 
  then obtain S' where S'_def: "cover S' ?X" "S' \<subseteq> ?S" 
    by blast
  with \<open>ts_xc F = (?X, ?S)\<close> 
  have prem: "\<forall>c\<in> set F. \<exists>s\<in> S'. \<exists>l \<in> c. s = {C c, L l c}"
   using constr_model_exists[of S' ?S ?X]
   by presburger

   let ?\<sigma> = "constr_model S' F"
   have "\<forall>c\<in> set F. \<exists>s\<in> S'. \<exists>l \<in> c. s = {C c, L l c} \<and> (?\<sigma> \<up>) l"
   proof 
     fix c 
     assume "c \<in> set F"
     then have "\<exists>s\<in> S'. \<exists>l \<in> c. s = {C c, L l c}"
       using prem 
       by blast
     then obtain s l where s_def: "s \<in> S'" "l \<in> c" "s = {C c, L l c}"
       by blast
     
     have "(?\<sigma>\<up>) l"
      unfolding constr_model_def lift_def
      apply (cases l)
      using s_def \<open>c \<in> set F\<close> apply force 
      apply auto 
      using constr_model_disj_aux[OF S'_def] s_def
      by blast
     with s_def \<open>c \<in> set F\<close> 
     show "\<exists>s\<in>S'. \<exists>l\<in>c. s = {C c, L l c} \<and> (?\<sigma>\<up>) l"
       by blast
   qed 
   then have "?\<sigma> \<Turnstile> F"
     unfolding models_def 
     by blast
   then show ?thesis
     unfolding cnf_sat_def sat_def
     by blast
qed

theorem is_reduction_ts_xc:
"is_reduction ts_xc cnf_sat exact_cover"
  unfolding is_reduction_def 
  using ts_xc_sound ts_xc_complete
  by blast

end