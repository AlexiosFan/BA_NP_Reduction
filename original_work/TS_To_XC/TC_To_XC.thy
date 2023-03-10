theory TC_To_XC
imports  "Karp21.TC_To_ChrN" XC_Definition
begin



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