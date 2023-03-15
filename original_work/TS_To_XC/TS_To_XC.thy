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

definition ts_xc :: "'a three_sat \<Rightarrow> 'a xc_element set * 'a xc_element set set" where 
"ts_xc F =(let
   vars = vars_of_sat F;
   clauses = clauses_of_sat F;
   literals = literals_of_sat F;
   literals_sets = literal_sets F;
   clause_with_literal_sets = 
     clauses_with_literals F;
   var_true_sets = 
    var_true_literals F;
   var_false_sets = 
    var_false_literals F
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

  let ?ls = "literal_sets F"
  let ?cs = "clauses_with_literals F"
  let ?vt = "var_true_literals F"
  let ?vf = "var_false_literals F"

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

definition constr_cover 
  :: "'a three_sat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a xc_element set set" where 
"constr_cover F \<sigma> \<equiv> 
  (if F \<in> three_cnf_sat 
  then 
  (let
     vars_sets = 
       {x_set | x_set. \<exists>x \<in> vars F.
       (if (\<sigma>\<up>) (Pos x) then (V x) \<in> x_set \<and> x_set \<in> var_true_literals F
       else (V x) \<in> x_set \<and> x_set \<in> var_false_literals F)};
     clause_sets = 
       {{C c, p} | c p. c \<in> (set F) \<and> p \<in> c}
   in 
    S')
  else {})"

end