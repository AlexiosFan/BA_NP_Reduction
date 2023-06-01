theory importing 
  imports "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar"
begin


definition "xc_to_ehs \<equiv> \<lambda>(X, S). (if finite X \<and> \<Union>S \<subseteq> X then {{s. u \<in> s \<and> s \<in> S} | u. u \<in> X} else {{}})"
lemma xc_to_ehs_sound: "(X, S) \<in> exact_cover \<Longrightarrow> xc_to_ehs (X, S) \<in> exact_hitting_set"
sorry
lemma xc_to_ehs_complete: "xc_to_ehs (X, S) \<in> exact_hitting_set \<Longrightarrow> (X, S) \<in> exact_cover"
sorry
theorem is_reduction_xc_to_ehs:
  "is_reduction xc_to_ehs exact_cover exact_hitting_set"
  sorry
end 