theory Section_1_2
  imports Main
    "Section_1_1"
begin

section \<open>Operations among Sets\<close>

subsection \<open>A) Union\<close>

proposition prop_1_2_0_a:
  defines "A \<equiv> {1, 2, 3, 4, 5}"
    and "B \<equiv> {3, 5, 7, 9}"
  shows "A \<union> B = {1, 2, 3, 4, 5, 7, 9}"
  unfolding A_def and B_def by auto

proposition prop_1_2_0_b:
  defines "A \<equiv> {n :: nat. even n}"
    and "B \<equiv> {n :: nat. odd n}"
  shows "A \<union> B = UNIV"
  unfolding A_def and B_def by auto

proposition prop_1_2_1:
  shows "A \<union> B = {x. x \<in> A \<or> x \<in> B}"
  by (fact Un_def)

proposition prop_1_2_2_a:
  shows "A \<subseteq> A \<union> B"
  by (fact Un_upper1)

proposition prop_1_2_2_b:
  shows "B \<subseteq> A \<union> B"
  by (fact Un_upper2)

proposition prop_1_2_3:
  assumes "A \<subseteq> C"
    and "B \<subseteq> C"
  shows "A \<union> B \<subseteq> C"
  using assms by (fact Un_least)

proposition prop_1_2_4:
  shows "A \<union> A = A"
  by (fact Un_absorb)

proposition prop_1_2_5:
  shows "A \<union> B = B \<union> A"
  by auto

proposition prop_1_2_6:
  shows "(A \<union> B) \<union> C = A \<union> (B \<union> C)"
  by auto

proposition prop_1_2_6_b:
  shows "((A \<union> B) \<union> C) \<union> D = (A \<union> B) \<union> (C \<union> D)"
    and "(A \<union> B) \<union> (C \<union> D) = A \<union> (B \<union> (C \<union> D))"
    and "A \<union> (B \<union> (C \<union> D)) = A \<union> ((B \<union> C) \<union> D)"
    and "A \<union> ((B \<union> C) \<union> D) = (A \<union> (B \<union> C)) \<union> D"
  by auto

proposition prop_1_2_7:
  assumes "A \<subseteq> B"
  shows "A \<union> B = B"
  using assms by (fact Un_absorb1)

proposition prop_1_2_8:
  assumes "A \<subseteq> B"
  shows "A \<union> C \<subseteq> B \<union> C"
  using assms by auto

proposition prop_1_2_9:
  shows "{} \<union> A = A"
  using prop_1_1_5 by (rule prop_1_2_7)

subsection \<open>B) Intersection\<close>

proposition prop_1_2_0_c:
  defines "A :: nat set \<equiv> {1, 2, 3, 4, 5}"
    and "B \<equiv> {3, 5, 7, 9}"
  shows "A \<inter> B = {3, 5}"
  unfolding A_def and B_def by simp

proposition prop_1_2_0_d:
  defines "A \<equiv> {n :: nat. even n}"
    and "B \<equiv> {n :: nat. odd n}"
  shows "A \<inter> B = {}"
  unfolding A_def and B_def by auto

proposition prop_1_2_2'_a:
  shows "A \<inter> B \<subseteq> A"
  by (fact Int_lower1)

proposition prop_1_2_2'_b:
  shows "A \<inter> B \<subseteq> B"
  by (fact Int_lower2)

proposition prop_1_2_3':
  assumes "C \<subseteq> A"
    and "C \<subseteq> B"
  shows "C \<subseteq> A \<inter> B"
  using assms by (fact Int_greatest)

proposition prop_1_2_4':
  shows "A \<inter> A = A"
  by (fact Int_absorb)

proposition prop_1_2_5':
  shows "A \<inter> B = B \<inter> A"
  by auto

proposition prop_1_2_6':
  shows "(A \<inter> B) \<inter> C = A \<inter> (B \<inter> C)"
  by auto

proposition prop_1_2_7':
  assumes "A \<subseteq> B"
  shows "A \<inter> B = A"
  using assms by(fact Int_absorb2)

proposition prop_1_2_8':
  assumes "A \<subseteq> B"
  shows "A \<inter> C \<subseteq> B \<inter> C"
  using assms by auto

proposition prop_1_2_9':
  shows "{} \<inter> A = {}"
  using prop_1_1_5 by (rule prop_1_2_7')

proposition prop_1_2_10:
  shows "(A \<union> B) \<inter> C = A \<inter> C \<union> B \<inter> C"
  by (fact Int_Un_distrib2)

proposition prop_1_2_10':
  shows "(A \<inter> B) \<union> C = (A \<union> C) \<inter> (B \<union> C)"
  by (fact Un_Int_distrib2)

proposition prop_1_2_11:
  shows "(A \<union> B) \<inter> A = A"
  by auto

proposition prop_1_2_11':
  shows "(A \<inter> B) \<union> A = A"
  by auto

subsection \<open>C) Difference\<close>

proposition prop_1_2_0_e:
  defines "A :: nat set \<equiv> {1, 2, 3, 4, 5}"
    and "B \<equiv> {3, 5, 7, 9}"
  shows "A - B = {1, 2, 4}"
  unfolding A_def and B_def by auto

subsection \<open>D) Universal Set\<close>

proposition prop_1_2_12_a:
  assumes "A \<subseteq> X"
  shows "A \<union> (X - A) = X"
  using assms by auto

proposition prop_1_2_12_b:
  \<comment> \<open>The assumption @{prop "A \<subseteq> X"} is not necessary.\<close>
  shows "A \<inter> (X - A) = {}"
  by (fact Diff_disjoint)

proposition prop_1_2_13:
  assumes "A \<subseteq> X"
  shows "X - (X - A) = A"
  using assms by (simp only: double_diff)

proposition prop_1_2_14_a:
  shows "X - {} = X"
  by (fact Diff_empty)

proposition prop_1_2_14_b:
  shows "X - X = {}"
  by (fact Diff_cancel)

proposition prop_1_2_15:
  assumes "A \<subseteq> X"
    and "B \<subseteq> X"
  shows "A \<subseteq> B \<longleftrightarrow> X - A \<supseteq> X - B"
  using assms by auto

proposition prop_1_2_16:
  \<comment> \<open>The assumption @{prop "A \<subseteq> X"} is not necessary.\<close>
  \<comment> \<open>The assumption @{prop "B \<subseteq> X"} is not necessary.\<close>
  shows "X - (A \<union> B) = (X - A) \<inter> (X - B)"
  by (fact Diff_Un)

proposition prop_1_2_16':
  \<comment> \<open>The assumption @{prop "A \<subseteq> X"} is not necessary.\<close>
  \<comment> \<open>The assumption @{prop "B \<subseteq> X"} is not necessary.\<close>
  shows "X - (A \<inter> B) = (X - A) \<union> (X - B)"
  by (fact Diff_Int)

subsection \<open>E) Family of Sets, Power Set\<close>

proposition prop_1_2_0_f:
  fixes a and b and c
  defines "X \<equiv> {a, b, c}"
  shows "Pow X = {{}, {a}, {b}, {c}, {a, b}, {b, c}, {c, a}, {a, b, c}}"
  unfolding X_def by blast

proposition prop_1_2_0_g:
  shows "Pow {} = {{}}"
  by (fact Pow_empty)

proposition prop_1_2_0_h:
  assumes "finite X"
    and "card X = n"
  shows "card (Pow X) = 2 ^ n"
using assms proof (induct n arbitrary: X)
  case 0
  from 0 and assms(1) have "X = {}" by simp
  thus ?case by simp
next
  case (Suc n')
  from Suc.prems obtain x and X' where "card X' = n'" and "insert x X' = X" and "x \<notin> X'"
    by (blast dest: card_eq_SucD)
  from Suc.prems(1) and this(2) have "finite X'" by auto
  with \<open>card X' = n'\<close> have "card (Pow X') = 2 ^ n'" by (intro Suc.hyps)
  note \<open>finite X'\<close>
  moreover have "Pow (insert x X') = Pow X' \<union> insert x ` Pow X'" by (fact Pow_insert)
  moreover from \<open>x \<notin> X'\<close> have "Pow X' \<inter> insert x ` Pow X' = {}" by auto
  ultimately have "card (Pow (insert x X')) = card (Pow X') + card (insert x ` Pow X')"
    by (simp add: card_Un_disjoint)
  moreover have "card (insert x ` Pow X') = card (Pow X')"
  proof (rule card_image, rule inj_onI)
    fix A B
    assume "A \<in> Pow X'"
      and "B \<in> Pow X'"
      and "insert x A = insert x B"
    from this(1,2) and \<open>x \<notin> X'\<close> have "x \<notin> A" and "x \<notin> B" by auto
    with \<open>insert x A = insert x B\<close> show "A = B" by auto
  qed
  moreover note \<open>insert x X' = X\<close>
  ultimately have "card (Pow X) = card (Pow X') + card (Pow X')" by simp
  also from \<open>card (Pow X') = 2 ^ n'\<close> have "\<dots> = 2 ^ (Suc n')" by simp
  finally show ?case .
qed

subsection \<open>F) Union and Intersection of Family of Sets\<close>

proposition prop_1_2_17:
  shows "\<forall>A \<in> \<AA>. A \<subseteq> \<Union>\<AA>"
  by auto

proposition prop_1_2_18:
  assumes "\<forall>A \<in> \<AA>. A \<subseteq> C"
  shows "\<Union>\<AA> \<subseteq> C"
  using assms by auto

proposition prop_1_2_17':
  shows "\<forall>A \<in> \<AA>. \<Inter>\<AA> \<subseteq> A"
  by auto

proposition prop_1_2_18':
  assumes "\<forall>A \<in> \<AA>. C \<subseteq> A"
  shows "C \<subseteq> \<Inter>\<AA>"
  using assms by auto

subsection \<open>Problems\<close>

proposition prob_1_2_1_a:
  \<comment> \<open>The assumption @{prop "A \<subseteq> X"} is not necessary.\<close>
  \<comment> \<open>The assumption @{prop "B \<subseteq> X"} is not necessary.\<close>
  shows "(A \<union> B) \<inter> (A \<union> (X - B)) = A"
  by auto

proposition prob_1_2_1_b:
  \<comment> \<open>The assumption @{prop "A \<subseteq> X"} is not necessary.\<close>
  \<comment> \<open>The assumption @{prop "B \<subseteq> X"} is not necessary.\<close>
  shows "(A \<union> B) \<inter> ((X - A) \<union> B) \<inter> (A \<union> (X - B)) = A \<inter> B"
  by auto

proposition prob_1_2_2_a:
  assumes \<comment> \<open>The assumption @{prop "A \<subseteq> X"} is not necessary.\<close>
    "B \<subseteq> X"
  shows "A \<inter> B = {} \<longleftrightarrow> B \<subseteq> X - A"
  using assms by auto

proposition prob_1_2_2_b:
  assumes "A \<subseteq> X"
    \<comment> \<open>The assumption @{prop "B \<subseteq> X"} is not necessary.\<close>
  shows "A \<inter> B = {} \<longleftrightarrow> A \<subseteq> X - B"
  using assms by auto

proposition prob_1_2_3_a_a:
  shows "A - B = (A \<union> B) - B"
  by auto

proposition prob_1_2_3_a_b:
  shows "A - B = A - (A \<inter> B)"
  by auto

proposition prob_1_2_3_a_c:
  assumes "A \<subseteq> X"
    \<comment> \<open>The assumption @{prop "B \<subseteq> X"} is not necessary.\<close>
  shows "A - B = A \<inter> (X - B)"
  using assms by auto

proposition prob_1_2_3_b:
  shows "A - B = A \<longleftrightarrow> A \<inter> B = {}"
  by auto

proposition prob_1_2_3_c:
  shows "A - B = {} \<longleftrightarrow> A \<subseteq> B"
  by (fact Diff_eq_empty_iff)

proposition prob_1_2_4_a:
  shows "A - (B \<union> C) = (A - B) \<inter> (A - C)"
  by (fact prop_1_2_16)

proposition prob_1_2_4_b:
  shows "A - (B \<inter> C) = (A - B) \<union> (A - C)"
  by (fact prop_1_2_16')

proposition prob_1_2_4_c:
  shows "(A \<union> B) - C = (A - C) \<union> (B - C)"
  by (fact Un_Diff)

proposition prob_1_2_4_d:
  shows "(A \<inter> B) - C = (A - C) \<inter> (B - C)"
  by auto

proposition prob_1_2_4_e:
  shows "A \<inter> (B - C) = (A \<inter> B) - (A \<inter> C)"
  by (fact Diff_Int_distrib)

proposition prob_1_2_5_a:
  shows "(A - B) - C = A - (B \<union> C)"
  by auto

proposition prob_1_2_5_b:
  shows "A - (B - C) = (A - B) \<union> (A \<inter> C)"
  by auto

proposition prob_1_2_6:
  assumes "A \<subseteq> C"
  shows "A \<union> (B \<inter> C) = (A \<union> B) \<inter> C"
  using assms by auto

definition sym_diff :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<triangle>" 65)
  where "sym_diff A B = (A - B) \<union> (B - A)"

lemmas sym_diff_eq [iff] = sym_diff_def

proposition prob_1_2_7_a:
  shows "A \<triangle> B = B \<triangle> A"
  by auto

proposition prob_1_2_7_b:
  shows "A \<triangle> B = (A \<union> B) - (A \<inter> B)"
  by auto

proposition prob_1_2_7_c:
  shows "(A \<triangle> B) \<triangle> C = A \<triangle> (B \<triangle> C)"
  by auto

proposition prob_1_2_7_d:
  shows "A \<inter> (B \<triangle> C) = (A \<inter> B) \<triangle> (A \<inter> C)"
  by auto

proposition prob_1_2_8_a [simp]:
  shows "A \<triangle> {} = A"
  by simp

proposition prob_1_2_8_b:
  assumes "A \<subseteq> X"
  shows "A \<triangle> X = X - A"
  using assms by auto

proposition prob_1_2_8_c [simp]:
  shows "A \<triangle> A = {}"
  by simp

proposition prob_1_2_8_d:
  assumes "A \<subseteq> X"
  shows "A \<triangle> (X - A) = X"
  using assms by auto

proposition prob_1_2_9:
  assumes "A\<^sub>1 \<triangle> A\<^sub>2 = B\<^sub>1 \<triangle> B\<^sub>2"
  shows "A\<^sub>1 \<triangle> B\<^sub>1 = A\<^sub>2 \<triangle> B\<^sub>2"
  using assms by auto

end
