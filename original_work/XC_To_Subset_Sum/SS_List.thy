theory SS_List
  imports Main
begin

subsection "simulation of polynomials, a little endian implementation"

type_synonym Poly = "nat \<times> nat list"
(*
A base and the list of log base (N^k).
The length of the list should be fixed*)

subsubsection addition

fun handle_overflow :: "nat \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> nat list" where
"handle_overflow b [] _ = []" |
"handle_overflow b (x # xs) flag = 
  (let num = (if flag then 1 else 0) + b
  in
   (if num \<le> b 
   then x # (handle_overflow b xs False)
   else (x - b) # (handle_overflow b xs True)
   )
  )"

fun add_polys :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where 
"add_polys _ [] [] = []" |
"add_polys b (x # xs) (y # ys) = handle_overflow b ((x+y) # ys) False"

fun add_Poly :: "Poly \<Rightarrow> Poly \<Rightarrow> Poly option" where
"add_Poly (a, xs) (b, ys) = 
  (if a = b \<and> length xs = length ys
  then Some (a, add_polys a xs ys)
  else None)"

subsubsection mapping

fun polys_to_nat :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where 
"polys_to_nat _ [] = 0" |
"polys_to_nat b (x # xs) = x * (b ^ (length xs + 1)) + polys_to_nat b xs"

definition sum_to_polys :: "nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where 
"sum_to_polys S b len = 
 (if \<forall>n \<in> S. \<exists>k. b ^ k = n \<and> k \<le> len \<and> k > 0
 then THE xs. length xs = len \<and> (\<forall>k < len. if b ^ k \<in> S then xs ! k = 1 else xs ! k = 0)
 else [])"

definition Poly_to_nat :: "Poly \<Rightarrow> nat" where 
"Poly_to_nat p = polys_to_nat (fst p) (rev (snd p))"


declare handle_overflow.simps[[simp del]] 
        add_polys.simps[[simp del]] 
        add_Poly.simps[[simp del]]
        polys_to_nat.simps[[simp del]]

find_theorems "THE _. _"

lemma sum_to_polys_exists:
assumes "\<forall>n \<in> S. \<exists>k. b ^ k = n \<and> k \<le> len \<and> k > 0"
shows "\<exists>!xs. length xs = len \<and> (\<forall>k < len. if b ^ k \<in> S then xs ! k = 1 else xs ! k = 0)"
proof (safe, goal_cases)
  case 1
  then show ?case
  using assms sorry
next
  case (2 xs y)
  then show ?case sorry
qed

end