theory TS_To_XC
  imports TS_To_XC_aux
begin

definition vars_of_sat :: "'a three_sat \<Rightarrow> 'a xc_element set" where
"vars_of_sat F = {V v |v. v \<in> vars F}"

definition clauses_of_sat :: "'a three_sat \<Rightarrow> 'a xc_element set" where 
"clauses_of_sat F = {C c| c. c\<in> set F}"

definition literals_of_sat :: "'a three_sat \<Rightarrow> 'a xc_element set" where
"literals_of_sat F = comp_literals F {}"

definition literal_sets
  :: "'a xc_element set \<Rightarrow> 'a xc_element set set" where
"literal_sets Li = {{l}| l. l \<in> Li}"

definition clauses_with_literals 
  :: "'a xc_element set \<Rightarrow> 'a xc_element set \<Rightarrow> 'a xc_element set set" where
"clauses_with_literals Cl Li = {{C c, l} |c l. C c \<in> Cl \<and> l \<in> Li 
        \<and> l \<in> {L a c | a. a \<in> c}}"

definition var_true_literals
  :: "'a xc_element set \<Rightarrow> 'a xc_element set \<Rightarrow> 'a xc_element set 
       \<Rightarrow> 'a xc_element set set" where 
"var_true_literals Va Cl Li = 
  {{V v} \<union> {l. l \<in> Li \<and> (\<exists>c. C c\<in> Cl \<and> L (Neg v) c = l)} |v. V v \<in> Va}"

definition var_false_literals
  :: "'a xc_element set \<Rightarrow> 'a xc_element set \<Rightarrow> 'a xc_element set 
       \<Rightarrow> 'a xc_element set set" where 
"var_false_literals Va Cl Li = 
  {{V v} \<union> {l. l \<in> Li \<and> (\<exists>c. C c\<in> Cl \<and> L (Pos v) c = l)} |v. V v \<in> Va}"

definition ts_xc :: "'a three_sat \<Rightarrow> 'a xc_element set * 'a xc_element set set" where 
"ts_xc F =(let
   vars = vars_of_sat F;
   clauses = clauses_of_sat F;
   literals = literals_of_sat F;
   literals_sets = literal_sets literals;
   clause_with_literal_sets = clauses_with_literals clauses literals;
   var_true_sets = 
    var_true_literals vars clauses literals;
   var_false_sets = 
    var_false_literals vars clauses literals
  in
   (vars \<union> clauses \<union> literals,
    literals_sets \<union> clause_with_literal_sets \<union> var_true_sets \<union> var_false_sets))"

lemma ts_xc_is_collection:
  assumes "ts_xc F = (X, S)" "F \<in> three_cnf_sat" 
  shows "\<Union>S \<subseteq> X"
proof -
  let ?vars = "vars_of_sat F"
  let ?clauses = "clauses_of_sat F"
  let ?literals = "literals_of_sat F"

  let ?ls = "literal_sets ?literals"
  let ?cs = "clauses_with_literals ?clauses ?literals"
  let ?vt = "var_true_literals ?vars ?clauses ?literals"
  let ?vf = "var_false_literals ?vars ?clauses ?literals"

  have x_part: "X = ?vars \<union> ?clauses \<union> ?literals"
  using assms ts_xc_def[of F] by (auto simp: Let_def)
    
  have s_part: "S = ?ls \<union> ?cs \<union> ?vt \<union> ?vf"
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

end