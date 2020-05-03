theory Section_1_1
  imports Main
begin

chapter \<open>Sets and Maps\<close>

section \<open>Notion of Sets\<close>

subsection \<open>A) Sets and Elements\<close>

subsection \<open>B) Notation of Sets\<close>

subsection \<open>C) Equality of Sets\<close>

subsection \<open>D) Subsets\<close>

proposition prop_1_1_3:
  shows "A = B \<longleftrightarrow> A \<subseteq> B \<and> A \<supseteq> B"
  by (fact set_eq_subset)

proposition prop_1_1_4:
  assumes "A \<subseteq> B"
    and "B \<subseteq> C"
  shows "A \<subseteq> C"
  using assms by simp

proposition prop_1_1_5:
  fixes A :: "'a set"
  shows "{} \<subseteq> A"
  by simp

proposition prop_1_1_6:
  assumes "x \<in> {}"
  shows "x \<in> A"
  using assms by (fact emptyE)

subsection \<open>Problems\<close>

proposition prob_1_1_1:
  shows "a \<in> A \<longleftrightarrow> {a} \<subseteq> A"
  by simp

proposition prob_1_1_2:
  shows "{1, 2, 3} = {n :: nat. 1 \<le> n \<and> n \<le> 3}"
  by auto

(* TODO: prob_1_1_3_a *)
(* TODO: prob_1_1_3_b *)
(* TODO: prob_1_1_3_c *)
(* TODO: prob_1_1_3_d *)
(* TODO: prob_1_1_3_e *)
(* TODO: prob_1_1_3_f *)
(* TODO: prob_1_1_4_a_i *)
(* TODO: prob_1_1_4_a_ii *)
(* TODO: prob_1_1_4_b *)
(* TODO: prob_1_1_5_a *)
(* TODO: prob_1_1_5_b *)

end
