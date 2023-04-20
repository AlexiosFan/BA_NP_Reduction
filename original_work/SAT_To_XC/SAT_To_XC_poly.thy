theory SAT_To_XC_poly
  imports  "Karp21.TSTSC_Poly" "Poly_Reductions_Lib.Set_Auxiliaries" SAT_To_XC 
begin

section "the reduction from sat to xc is polynomial"

subsection "basics"

definition "mop_get_vars F \<equiv> SPEC (\<lambda>v. v = vars F) (\<lambda>_. 2 * (length F) + 3 * (card (\<Union> (set F))) + 1)"
definition "mop_get_cls F \<equiv> SPEC (\<lambda>c. c = set F) (\<lambda>_. 1)"
(*
1 for the set operator
2 * length for the big union
3 * card for the mapping
*)

abbreviation "Max_nat s \<equiv> (if s = {} then 0 else Max s)"

definition "sz_vars F \<equiv> card (vars F)"
definition "sz_cls \<equiv> size_SAT"
definition "sz_lit F \<equiv> length F * (Max_nat (card ` (set F)))"
definition "size_XC XC \<equiv> max (card (fst XC)) (card (snd XC))"
definition "size_SAT_max \<equiv> (\<lambda>x. max (max (sz_cls x) (sz_lit x)) (sz_vars x))"

(*
3 metrics are independent from each other, hence lift them to the maximum
*)

subsection "forging the X"

definition "mop_vars_of_sat F \<equiv> SPEC (\<lambda>v. v = vars_of_sat F) (\<lambda>_. 3 * sz_vars F)"
definition "mop_clauses_of_sat F \<equiv> SPEC (\<lambda>c. c = clauses_of_sat F) (\<lambda>_. 3 * sz_cls F)"
definition "mop_literals_of_sat F \<equiv> SPEC (\<lambda>l. l = literals_of_sat F) (\<lambda>_. sz_cls F + 3 * sz_lit F)"

(*
1 * x for checking the existence
3 * for checking the existence, type lifting and insertion
*)

subsection "forging the S"


definition "mop_literal_sets F \<equiv> SPEC (\<lambda>s. s = literal_sets F) (\<lambda>_. (3 + 1) * sz_lit F)"
definition "mop_clauses_with_literals F 
  \<equiv> SPEC (\<lambda>s. s = clauses_with_literals F) (\<lambda>_. (3 + 1 + 1) * sz_lit F + sz_cls F)"
definition "mop_var_true_literals F 
  \<equiv> SPEC (\<lambda>s. s = var_true_literals F) (\<lambda>_. (3 + 1) * sz_vars F + (3 + 1) * sz_lit F + (1 + 1) * sz_cls F + 1)"
definition "mop_var_false_literals F 
  \<equiv> SPEC (\<lambda>s. s = var_false_literals F) (\<lambda>_. (3 + 1) * sz_vars F + (3 + 1) * sz_lit F + (1 + 1) * sz_cls F + 1)"

subsection "algorithmic in NREST"

definition "mop_union_x a b c \<equiv> SPEC (\<lambda>s. s = a \<union> b \<union> c) (\<lambda>_. 2)"
definition "mop_union_s a b c d \<equiv> SPEC (\<lambda>s. s = a \<union> b \<union> c \<union> d) (\<lambda>_. 3)"
definition "sat_to_xc_alg \<equiv> (\<lambda>F.
 do 
    {
      VS \<leftarrow> mop_vars_of_sat F;
      CS \<leftarrow> mop_clauses_of_sat F;
      LS \<leftarrow> mop_literals_of_sat F;
      s1 \<leftarrow> mop_literal_sets F;
      s2 \<leftarrow> mop_clauses_with_literals F;
      s3 \<leftarrow> mop_var_true_literals F;
      s4 \<leftarrow> mop_var_false_literals F;
      X \<leftarrow> mop_union_x CS VS LS;
      S \<leftarrow> mop_union_s s1 s2 s3 s4;
      RETURNT (X, S)
    }
)"

definition "sat_to_xc_time_aux l m n = 
  2 * m + 3 * n + 1 + 1
+ 3 * l + 3 * m + m + 3 * n
+ (3 + 1) * n + (3 + 1 + 1) * n + m
+ (3 + 1) * l + (3 + 1 + 1) * n + (1 + 1) * m + 1
+ (3 + 1) * l + (3 + 1 + 1) * n + (1 + 1) * m + 1
+ 2 + 3"

definition "sat_to_xc_space_aux l m n = 
l + m + n
+ n + n
+ l + l"

lemma sat_to_xc_time_aux_mono1: 
"(a::nat) \<le> b \<Longrightarrow> sat_to_xc_time_aux a x y \<le> sat_to_xc_time_aux b x y"
 unfolding sat_to_xc_time_aux_def
 by auto

lemma sat_to_xc_time_aux_mono2: 
"(a::nat) \<le> b \<Longrightarrow> sat_to_xc_time_aux x a y \<le> sat_to_xc_time_aux x b y"
 unfolding sat_to_xc_time_aux_def
 by auto

lemma sat_to_xc_time_aux_mono3: 
"(a::nat) \<le> b \<Longrightarrow> sat_to_xc_time_aux x y a \<le> sat_to_xc_time_aux x y b"
 unfolding sat_to_xc_time_aux_def
 by fastforce

lemmas sat_to_xc_time_aux_mono = 
  sat_to_xc_time_aux_mono1 sat_to_xc_time_aux_mono2 sat_to_xc_time_aux_mono3

lemma sat_to_xc_space_aux_mono1: 
"(a::nat) \<le> b \<Longrightarrow> sat_to_xc_space_aux a x y \<le> sat_to_xc_space_aux b x y"
 unfolding sat_to_xc_space_aux_def
 by linarith

lemma sat_to_xc_space_aux_mono2: 
"(a::nat) \<le> b \<Longrightarrow> sat_to_xc_space_aux x a y \<le> sat_to_xc_space_aux x b y"
 unfolding sat_to_xc_space_aux_def
 by (simp add: add_mono) 

lemma sat_to_xc_space_aux_mono3: 
"(a::nat) \<le> b \<Longrightarrow> sat_to_xc_space_aux x y a \<le> sat_to_xc_space_aux x y b"
 unfolding sat_to_xc_space_aux_def
 by (simp add: add_mono) 

lemmas sat_to_xc_space_aux_mono=
 sat_to_xc_space_aux_mono1 sat_to_xc_space_aux_mono2 sat_to_xc_space_aux_mono3


definition "sat_to_xc_time n = sat_to_xc_time_aux n n n"
definition "sat_to_xc_space n = sat_to_xc_space_aux n n n"

subsubsection "auxiliary lemmas about the cardinality"

lemma card_Un_le_3:
"card (a \<union> b \<union> c) \<le> card a + card b + card c"
  using card_Un_le[of "a \<union> b" c] card_Un_le[of a b]
  by simp   

lemma card_Un_le_4:
"card (a \<union> b \<union> c \<union> d) \<le> card a + card b + card c + card d"
  using card_Un_le[of "a \<union> b \<union> c" d] card_Un_le_3[of a b c]
  by linarith

lemma card_Union_upper: 
  "\<forall>c \<in> s. card c \<le> a \<Longrightarrow> card (\<Union>s) \<le> card s * a"
  by (metis Orderings.order_eq_iff card.infinite 
  card_union_if_all_subsets_card_i finite_UnionD mult.commute mult_is_0)

lemma card_finite_sat:
"card (literals_of_sat F) \<le> length F * (Max_nat (card ` (set F)))"
proof (induction F)
  case (Cons a F)
  let ?m = "Max_nat (card ` set F)"
  let ?n = "Max_nat (card ` set (a # F))"

  have *: "Max_nat (card ` set F) \<le> ?n"
    by auto

  have "inj_on (\<lambda>l. L l a) a" "{L l a | l. l \<in> a} = (\<lambda>l. L l a) ` a"
    unfolding inj_on_def 
    by blast+
  then have "card {L l a | l. l \<in> a}  = card a"
    using card_image
    by metis
 then have **:"card {L l a | l. l \<in> a} \<le> ?n"
   by simp

  have "literals_of_sat (a#F) = {L l a | l. l \<in> a} \<union> literals_of_sat F"
    unfolding literals_of_sat_def 
    by fastforce
  then have "card (literals_of_sat (a#F)) = card ({L l a | l. l \<in> a} \<union> literals_of_sat F)"
    by argo
  also have "... \<le> card {L l a | l. l \<in> a} + card (literals_of_sat F)"
    using card_Un_le
    by blast
  also have "... \<le> card {L l a | l. l \<in> a} + length F * ?m"
    using Cons 
    by linarith
  also have "... \<le> ?n + length F * ?n"
    using * ** 
    by (simp add: add_mono)
  also have "... \<le> (1 + length F) * ?n"
    by simp
  finally show ?case
    by auto
qed (simp add: literals_of_sat_def)

lemma comp_X_Nil:
"comp_X [] = {}"
unfolding vars_of_sat_def _clauses_of_sat_def literals_of_sat_def vars_def 
by simp

lemma comp_S_Nil:
"comp_S [] = {}"
unfolding literal_sets_def clauses_with_literals_def 
  var_true_literals_def var_false_literals_def
  literals_of_sat_def clauses_of_sat_def
  vars_of_sat_def vars_def 
by simp 

lemma card_comp_X:
  "card (comp_X F) \<le> sz_vars F + sz_cls F + sz_lit F"
proof -
  have *: "inj_on V (vars F)" "V ` (vars F) = vars_of_sat F"
        unfolding inj_on_def vars_of_sat_def
        by blast+
  have **: "inj_on C (set F)" "C ` (set F) = clauses_of_sat F"
        unfolding inj_on_def clauses_of_sat_def
        by blast+

  have "card (comp_X F) \<le> card (vars_of_sat F) + card (clauses_of_sat F) + card (literals_of_sat F)"
    using card_Un_le_3 
    by blast
  also have "... = sz_vars F + card (clauses_of_sat F) + card (literals_of_sat F)"
    unfolding  sz_vars_def 
    using card_image * 
    by metis
  also have "... \<le> sz_vars F + sz_cls F + card (literals_of_sat F)"
    unfolding sz_cls_def size_SAT_def 
    using card_image ** card_length
    by fastforce
  finally show ?thesis
    unfolding sz_lit_def
    using card_finite_sat[of F] add_mono
    by linarith
qed

lemma card_comp_S:
  "card (comp_S F) \<le> (sz_lit F) + (sz_lit F) + (sz_vars F) + (sz_vars F)"
proof -
  have *: "inj_on 
  (\<lambda>v. {V v} \<union> {l. l \<in> (literals_of_sat F) \<and> (\<exists>c. C c\<in> (clauses_of_sat F) \<and> L (Neg v) c = l)}) (vars F)" 
  "var_true_literals F = 
    (\<lambda>v. {V v} \<union> {l. l \<in> (literals_of_sat F) \<and> (\<exists>c. C c\<in> (clauses_of_sat F) \<and> L (Neg v) c = l)}) ` (vars F)"
    unfolding inj_on_def var_true_literals_def vars_of_sat_def
    by fast+
  have **: "inj_on 
  (\<lambda>v. {V v} \<union> {l. l \<in> (literals_of_sat F) \<and> (\<exists>c. C c\<in> (clauses_of_sat F) \<and> L (Pos v) c = l)}) (vars F)" 
  "var_false_literals F = 
    (\<lambda>v. {V v} \<union> {l. l \<in> (literals_of_sat F) \<and> (\<exists>c. C c\<in> (clauses_of_sat F) \<and> L (Pos v) c = l)}) ` (vars F)"
    unfolding inj_on_def var_false_literals_def vars_of_sat_def
    by fast+
  have ***: "inj_on (\<lambda>l. {l}) (literals_of_sat F)" "literal_sets F = (\<lambda>l. {l}) ` (literals_of_sat F)"
    unfolding literals_of_sat_def literal_sets_def
    by auto
  have ****: "inj_on (\<lambda>c. {L l c| l. l \<in> c}) (set F)" 
       "{{L l c| l. l \<in> c} | c. c \<in> set F} = (\<lambda>c. {L l c| l. l \<in> c}) ` (set F)"
    unfolding inj_on_def
    by blast+
  hence card_eq:
    "card {{L l c| l. l \<in> c} | c. c \<in> set F} = card (set F)"
    "finite {{L l c| l. l \<in> c} | c. c \<in> set F}"
    using card_image 
    by fastforce+
  hence card_sum: "card (\<Union> {{L l c| l. l \<in> c} | c. c \<in> set F}) 
    \<le> sum card  {{L l c| l. l \<in> c} | c. c \<in> set F}"
     using card_Un 
     by blast
  
  have "\<forall>c\<in> set F. inj_on (\<lambda>l. L l c) c \<and> {L l c| l. l \<in> c} = (\<lambda>l. L l c) ` c"
    unfolding inj_on_def
    by blast
  hence "\<forall>c \<in> set F. card {L l c| l. l \<in> c} = card c"
    using card_image
    by fastforce
  moreover have "\<forall>c \<in> set F. card c \<le> Max_nat (card ` set F)"
    by force 
  ultimately have "\<forall>c \<in> set F. card {L l c| l. l \<in> c} \<le> Max_nat (card ` set F)"
    by simp
  hence "\<forall>s \<in> {{L l c| l. l \<in> c} | c. c \<in> set F}. card s \<le> Max_nat (card ` set F)"
    using ****(2)
    by blast 
  hence "sum card {{L l c| l. l \<in> c} | c. c \<in> set F} 
    \<le> sum (\<lambda>_. Max_nat (card ` set F)) {{L l c| l. l \<in> c} | c. c \<in> set F}"
    using sum_mono 
    by meson
  with card_sum have "card (\<Union> {{L l c| l. l \<in> c} | c. c \<in> set F}) 
    \<le> sum (\<lambda>_. Max_nat (card ` set F)) {{L l c| l. l \<in> c} | c. c \<in> set F}"
   by linarith 
  also have "... \<le> Max_nat (card ` set F) * card {{L l c| l. l \<in> c} | c. c \<in> set F}"
    by fastforce 
  finally have "card (\<Union> {{L l c| l. l \<in> c} | c. c \<in> set F}) 
    \<le> Max_nat (card ` set F) * card (set F)"
    using card_eq
    by simp
  moreover have "\<Union> {{L l c| l. l \<in> c} | c. c \<in> set F} = {L l c | l c. l \<in> c \<and> c \<in> set F}"
    unfolding clauses_with_literals_def 
    by blast 
  ultimately have card_max_le: "card {L l c | l c. l \<in> c \<and> c \<in> set F} 
    \<le> Max_nat (card ` set F) * card (set F)"
    by argo

  have "\<forall>x \<in> {L l c | l c. l \<in> c \<and> c \<in> set F}. \<exists> l c. x = L l c"
    by blast
  then have 
    "inj_on (\<lambda>x. case x of L l c => {C c, L l c}) {L l c | l c. l \<in> c \<and> c \<in> set F}"
    "(\<lambda>x. case x of L l c => {C c, L l c}) ` {L l c | l c. l \<in> c \<and> c \<in> set F}
      = clauses_with_literals F"
    unfolding clauses_with_literals_def inj_on_def clauses_of_sat_def literals_of_sat_def
    by (auto split: xc_element.splits, blast)
  hence "card (clauses_with_literals F) = card {L l c | l c. l \<in> c \<and> c \<in> set F}"
    using card_image
    by fastforce
  with card_max_le have 
    "card (clauses_with_literals F) \<le> Max_nat (card ` set F) * card (set F)"
    by presburger
  then have *****:
    "card (clauses_with_literals F) \<le> sz_lit F"
    unfolding sz_lit_def sz_cls_def size_SAT_def
    using card_length[of F] le_trans
    by fastforce
    

  have "card (comp_S F) \<le> card (literal_sets F) + card (clauses_with_literals F) 
     + card (var_true_literals F) + card (var_false_literals F)"
    using card_Un_le_4
    by blast
  also have "... = card (literal_sets F) + card (clauses_with_literals F) 
     + sz_vars F + card (var_false_literals F)"
     unfolding sz_vars_def
     using card_image *
     by fastforce
  also have "... = card (literal_sets F) + card (clauses_with_literals F) 
     + sz_vars F + sz_vars F"
     unfolding sz_vars_def
     using card_image **
     by fastforce
  also have "... = card (literals_of_sat F) + card (clauses_with_literals F) + sz_vars F + sz_vars F"
    using card_image ***
    by metis
  also have "... \<le> sz_lit F + card (clauses_with_literals F) + sz_vars F + sz_vars F"
    unfolding sz_lit_def
    using card_finite_sat[of F] add_mono
    by auto
  also have "... \<le> sz_lit F + sz_lit F + sz_vars F + sz_vars F"
    using *****
    by auto
  finally show ?thesis 
    by blast
qed


subsubsection "the main proof"

lemma sat_to_xc_size_aux:
"size_XC (sat_xc F) \<le> sat_to_xc_space_aux (sz_vars F) (sz_cls F) (sz_lit F)"
unfolding size_XC_def sat_xc_def
apply (cases " F = []")
apply (auto simp add: comp_X_Nil comp_S_Nil sat_to_xc_space_aux_def )
using add_mono[OF card_comp_X card_comp_S, of F F]
by auto

lemma sat_to_xc_size:
"size_XC (sat_xc F) \<le> sat_to_xc_space (size_SAT_max F)"
proof -
  have *: "sz_cls F \<le> size_SAT_max F" "sz_lit F \<le> size_SAT_max F" "sz_vars F \<le> size_SAT_max F"
    unfolding size_SAT_max_def max_def 
    by auto

  from sat_to_xc_size_aux have 
    "size_XC (sat_xc F) \<le> sat_to_xc_space_aux (sz_vars F) (sz_cls F) (sz_lit F)"
    by blast 
  also have "... \<le> sat_to_xc_space_aux (sz_vars F) (sz_cls F) (size_SAT_max F)"
    using * sat_to_xc_space_aux_mono
    by auto
  also have "... \<le> sat_to_xc_space_aux (sz_vars F) (size_SAT_max F) (size_SAT_max F)"
    using * sat_to_xc_space_aux_mono
    by auto
  also have "... \<le> sat_to_xc_space_aux (size_SAT_max F) (size_SAT_max F) (size_SAT_max F)"
    using * sat_to_xc_space_aux_mono
    by auto
  finally show ?thesis 
    unfolding sat_to_xc_space_def 
    by blast
qed 


lemma sat_to_xc_refines_aux1:
"sat_to_xc_alg F \<le> 
  SPEC (\<lambda>y. y = sat_xc F) (\<lambda>_. sat_to_xc_time_aux  (sz_vars F) (sz_cls F) (sz_lit F))"
unfolding SPEC_def
unfolding sat_to_xc_alg_def sat_xc_def
  mop_get_vars_def mop_get_cls_def mop_vars_of_sat_def
  mop_clauses_of_sat_def mop_literals_of_sat_def
  mop_literal_sets_def mop_clauses_with_literals_def 
  mop_var_true_literals_def mop_var_false_literals_def
  mop_union_x_def mop_union_s_def
apply(rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC)
apply (auto simp add: sat_to_xc_time_aux_def size_SAT_def sz_vars_def sz_lit_def sz_cls_def
  one_enat_def)
by (simp add: add.assoc eval_nat_numeral(3) numeral_Bit0 numeral_eq_enat)+
 
lemma sat_to_xc_refines_aux2:
"sat_to_xc_time_aux (sz_vars F) (sz_cls F) (sz_lit F) \<le> 
   sat_to_xc_time (size_SAT_max F)"
proof -
  have *: "sz_cls F \<le> size_SAT_max F" "sz_lit F \<le> size_SAT_max F" "sz_vars F \<le> size_SAT_max F"
    unfolding size_SAT_max_def max_def 
    by auto

  have "sat_to_xc_time_aux (sz_vars F) (sz_cls F) (sz_lit F) 
    \<le> sat_to_xc_time_aux (sz_vars F) (sz_cls F) (size_SAT_max F)"
    using * sat_to_xc_time_aux_mono
    by auto
  also have "... \<le> sat_to_xc_time_aux (sz_vars F) (size_SAT_max F) (size_SAT_max F)"
    using * sat_to_xc_time_aux_mono
    by auto
  also have "... \<le> sat_to_xc_time_aux (size_SAT_max F) (size_SAT_max F) (size_SAT_max F)"
    using * sat_to_xc_time_aux_mono
    by auto
  finally show ?thesis 
    unfolding sat_to_xc_time_def 
    by blast
qed 

corollary sat_to_xc_refines_aux3:
"SPEC (\<lambda>y. y = sat_xc F) (\<lambda>_. sat_to_xc_time_aux  (sz_vars F) (sz_cls F) (sz_lit F)) 
  \<le> SPEC (\<lambda>y. y = sat_xc F) (\<lambda>_. sat_to_xc_time (size_SAT_max F))"
using sat_to_xc_refines_aux2[of F]
unfolding SPEC_def 
by (simp add: le_funI)
  
lemma sat_to_xc_refines:
"sat_to_xc_alg F \<le> 
  SPEC (\<lambda>y. y = sat_xc F) (\<lambda>_. sat_to_xc_time (size_SAT_max F))"
using sat_to_xc_refines_aux1[of F] sat_to_xc_refines_aux3[of F] 
by simp

theorem sat_to_xc_ispolyred:
  "ispolyred sat_to_xc_alg cnf_sat exact_cover size_SAT_max size_XC"
  unfolding ispolyred_def
  apply(rule exI[where x=sat_xc])
  apply(rule exI[where x=sat_to_xc_time])
  apply(rule exI[where x=sat_to_xc_space])
  apply safe 
  subgoal 
    using sat_to_xc_refines 
    by blast 
  subgoal 
    using sat_to_xc_size 
    by blast
  subgoal 
    unfolding poly_def sat_to_xc_time_def sat_to_xc_time_aux_def 
    apply(intro exI[where x=2]) 
    by auto
  subgoal 
    unfolding poly_def sat_to_xc_space_def sat_to_xc_space_aux_def 
    apply(intro exI[where x=2]) 
    by auto
  subgoal using is_reduction_sat_xc
    by blast
  done 


end 