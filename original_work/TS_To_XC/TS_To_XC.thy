theory TS_To_XC
  imports TS_To_XC_aux
begin

definition ts_xc :: "'a three_sat \<Rightarrow> 'a xc_element set * 'a xc_element set set" where 
"ts_xc F = 
  (if F \<in> three_cnf_sat 
  then 
  (let
   vars = {V v |v. v \<in> vars F};
   clauses = {C c| c. c\<in> set F};
   literals = comp_literals F {};
   literals_sets = {{l}| l. l \<in> literals};
   clause_with_literal_sets = {{C c, l} |c l. C c \<in> clauses \<and> l \<in> literals 
        \<and> l \<in> {L a c | a. a \<in> c}};
   var_true_sets = 
    {{V v} \<union> {l. l \<in> literals \<and> (\<exists>c. C c\<in> clauses \<and> L (Neg v) c = l)} |v. V v \<in> vars};
   var_false_sets = 
    {{V v} \<union> {l. l \<in> literals \<and> (\<exists>c. C c\<in> clauses \<and> L (Pos v) c = l)} |v. V v \<in> vars}
  in
   (vars \<union> clauses \<union> literals,
    literals_sets \<union> clause_with_literal_sets \<union> var_true_sets \<union> var_false_sets))
  else ({}, {}))"

lemma ts_xc_is_collection:
  assumes "ts_xc F = (X, S)" "F \<in> three_cnf_sat" 
  shows "\<Union>S \<subseteq> X"
  proof -
  let ?vars = "{V v |v. v \<in> vars F}"
  let ?clauses = "{C c| c. c\<in> set F}"
  let ?literals = "comp_literals F {}"

  let ?ls = "{{l}| l. l \<in> ?literals}"
  let ?cs = "{{C c, l} 
    |c l. C c \<in> ?clauses \<and> l \<in> ?literals \<and> l \<in> {L a c | a. a \<in> c}}"
  let ?vt = "{{V v} 
   \<union> {l. l \<in> ?literals \<and> (\<exists>c. C c\<in> ?clauses \<and> L (Neg v) c = l)} |v. V v \<in> ?vars}"
  let ?vf = " {{V v} 
   \<union> {l. l \<in> ?literals \<and> (\<exists>c. C c\<in> ?clauses \<and> L (Pos v) c = l)} |v. V v \<in> ?vars}"

  have x_part: "X = ?vars \<union> ?clauses \<union> ?literals"
  using assms ts_xc_def[of F] by (auto simp: Let_def)
   
  have s_part: "S = ?ls \<union> ?cs \<union> ?vt \<union> ?vf"
  using assms ts_xc_def[of F] by (auto simp: Let_def)

  have "\<Union>?ls = ?literals" by blast 
  moreover have "\<Union>?cs \<subseteq> ?literals \<union> ?clauses" by blast
  moreover have "\<Union>?vt \<subseteq> ?literals \<union> ?vars" by blast
  moreover have "\<Union>?vf \<subseteq> ?literals \<union> ?vars" by blast

  ultimately have "\<Union> (?ls \<union> ?cs \<union> ?vt \<union> ?vf) \<subseteq> ?vars \<union> ?clauses \<union> ?literals"
  by blast
  
  with x_part s_part show ?thesis by force
  qed 

end