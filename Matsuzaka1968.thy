theory Matsuzaka1968
  imports Main "HOL-Cardinals.Cardinals"
begin

proposition prop_1_1_4:
  assumes "A \<subseteq> B" and "B \<subseteq> C"
  shows "A \<subseteq> C"
proof -
  {
    fix x
    assume "x \<in> A"
    with assms(1) have "x \<in> B" by (elim subsetD)
    with assms(2) have "x \<in> C" by (elim subsetD)
  }
  thus "?thesis" by (intro subsetI)
qed

proposition prop_1_1_5:
  fixes A :: "'a set"
  shows "{} \<subseteq> A"
proof -
  {
    fix x :: 'a
    assume "x \<in> {}"
    hence "False" by (elim emptyE)
    hence "x \<in> A" by (elim FalseE)
  }
  thus "?thesis" by (intro subsetI)
qed

proposition problem_1_1_1:
  shows "a \<in> A \<longleftrightarrow> {a} \<subseteq> A"
proof -
  have "{a} \<subseteq> A" if "a \<in> A"
  proof -
    {
      fix x
      assume "x \<in> {a}"
      hence "x = a" by (elim singletonD)
      with that have "x \<in> A" by (elim ssubst)
    }
    thus "?thesis" by (intro subsetI)
  qed
  moreover have "a \<in> A" if "{a} \<subseteq> A"
  proof -
    have "a \<in> {a}" by (intro singletonI)
    with that show "?thesis" by (elim subsetD)
  qed
  ultimately show "?thesis" by (intro iffI)
qed

lemma disj_implies_union:
  assumes "x \<in> A \<or> x \<in> B"
  shows "x \<in> A \<union> B"
proof -
  from assms have "x \<in> {x. x \<in> A \<or> x \<in> B}" by (intro CollectI)
  thus "?thesis" by (fold Un_def)
qed

lemma union_implies_disj:
  assumes "x \<in> A \<union> B"
  shows "x \<in> A \<or> x \<in> B"
proof -
  from assms have "x \<in> {x. x \<in> A \<or> x \<in> B}" by (unfold Un_def)
  thus "?thesis" by (elim CollectD)
qed

proposition prop_1_2_2_a:
  shows "A \<subseteq> A \<union> B"
proof -
  {
    fix x
    assume "x \<in> A"
    hence "x \<in> A \<or> x \<in> B" by (intro disjI1)
    hence "x \<in> A \<union> B" by (intro disj_implies_union)
  }
  thus "?thesis" by (intro subsetI)
qed

proposition prop_1_2_2_b:
  shows "B \<subseteq> A \<union> B"
proof -
  {
    fix x
    assume "x \<in> B"
    hence "x \<in> A \<or> x \<in> B" by (intro disjI2)
    hence "x \<in> A \<union> B" by (intro disj_implies_union)
  }
  thus "?thesis" by (intro subsetI)
qed

proposition prop_1_2_3:
  assumes "A \<subseteq> C" and "B \<subseteq> C"
  shows "A \<union> B \<subseteq> C"
proof -
  {
    fix x
    assume "x \<in> A \<union> B"
    hence "x \<in> A \<or> x \<in> B" by (elim union_implies_disj)
    moreover {
      assume "x \<in> A"
      with assms(1) have "x \<in> C" by (elim subsetD)
    }
    moreover {
      assume "x \<in> B"
      with assms(2) have "x \<in> C" by (elim subsetD)
    }
    ultimately have "x \<in> C" by (elim disjE)
  }
  thus "?thesis" by (intro subsetI)
qed

lemma
  shows "A \<subseteq> A"
proof -
  {
    fix x
    assume "x \<in> A"
    hence "x \<in> A" .
  }
  thus "?thesis" by (intro subsetI)
qed

(* From now on, we can use subset_refl. *)

proposition prop_1_2_4:
  shows "A \<union> A = A"
proof -
  have "A \<union> A \<subseteq> A"
  proof -
    have "A \<subseteq> A" by (intro subset_refl)
    with prop_1_2_3 show "?thesis" by (intro prop_1_2_3)
  qed
  moreover have "A \<subseteq> A \<union> A" by (intro prop_1_2_2_a)
  ultimately show "?thesis" by (intro equalityI)
qed

proposition prop_1_2_5:
  shows "A \<union> B = B \<union> A"
proof -
  have "A \<union> B \<subseteq> B \<union> A"
  proof -
    from prop_1_2_2_b have "A \<subseteq> B \<union> A" .
    moreover from prop_1_2_2_a have "B \<subseteq> B \<union> A" .
    ultimately show "?thesis" by (intro prop_1_2_3)
  qed
  moreover have "B \<union> A \<subseteq> A \<union> B"
  proof -
    from prop_1_2_2_b have "B \<subseteq> A \<union> B" .
    moreover from prop_1_2_2_a have "A \<subseteq> A \<union> B" .
    ultimately show "?thesis" by (intro prop_1_2_3)
  qed
  ultimately show "?thesis" by (intro equalityI)
qed

proposition prop_1_2_6:
  shows "(A \<union> B) \<union> C = A \<union> (B \<union> C)"
proof -
  have "(A \<union> B) \<union> C \<subseteq> A \<union> (B \<union> C)"
  proof -
    have "A \<union> B \<subseteq> A \<union> (B \<union> C)"
    proof -
      have "A \<subseteq> A \<union> (B \<union> C)" by (fact prop_1_2_2_a)
      moreover have "B \<subseteq> A \<union> (B \<union> C)"
      proof -
        have "B \<subseteq> B \<union> C" by (fact prop_1_2_2_a)
        also have "\<dots> \<subseteq> A \<union> (B \<union> C)" by (fact prop_1_2_2_b)
        finally show "?thesis" .
      qed
      ultimately show "?thesis" by (fact prop_1_2_3)
    qed
    moreover have "C \<subseteq> A \<union> (B \<union> C)"
    proof -
      have "C \<subseteq> B \<union> C" by (fact prop_1_2_2_b)
      moreover have "B \<union> C \<subseteq> A \<union> (B \<union> C)" by (fact prop_1_2_2_b)
      ultimately show "?thesis" by (fact prop_1_1_4)
    qed
    ultimately show "?thesis" by (fact prop_1_2_3)
  qed
  moreover have "A \<union> (B \<union> C) \<subseteq> (A \<union> B) \<union> C"
  proof -
    have "A \<subseteq> (A \<union> B) \<union> C"
    proof -
      have "A \<subseteq> A \<union> B" by (fact prop_1_2_2_a)
      also have "\<dots> \<subseteq> (A \<union> B) \<union> C" by (fact prop_1_2_2_a)
      finally show "?thesis" .
    qed
    moreover have "B \<union> C \<subseteq> (A \<union> B) \<union> C"
    proof -
      have "B \<subseteq> (A \<union> B) \<union> C"
      proof -
        have "B \<subseteq> A \<union> B" by (fact prop_1_2_2_b)
        also have "\<dots> \<subseteq> (A \<union> B) \<union> C" by (fact prop_1_2_2_a)
        finally show "?thesis" .
      qed
      moreover have "C \<subseteq> (A \<union> B) \<union> C" by (fact prop_1_2_2_b)
      ultimately show "?thesis" by (fact prop_1_2_3)
    qed
    ultimately show "?thesis" by (fact prop_1_2_3)
  qed
  ultimately show "?thesis" by (intro equalityI)
qed

proposition prop_1_2_7:
  assumes "A \<subseteq> B"
  shows "A \<union> B = B"
proof -
  have "A \<union> B \<subseteq> B"
  proof -
    have "B \<subseteq> B" by (fact subset_refl)
    with assms show "?thesis" by (fact prop_1_2_3)
  qed
  moreover have "B \<subseteq> A \<union> B" by (fact prop_1_2_2_b)
  ultimately show "?thesis" by (intro equalityI)
qed

proposition prop_1_2_8:
  assumes "A \<subseteq> B"
  shows "A \<union> C \<subseteq> B \<union> C"
proof -
  have "B \<subseteq> B \<union> C" by (fact prop_1_2_2_a)
  with assms have "A \<subseteq> B \<union> C" by (fact prop_1_1_4)
  moreover have "C \<subseteq> B \<union> C" by (fact prop_1_2_2_b)
  ultimately show "?thesis" by (fact prop_1_2_3)
qed

proposition prop_1_2_9:
  shows "{} \<union> A = A"
  using prop_1_1_5 by (intro prop_1_2_7)

lemma conj_implies_inter:
  assumes "x \<in> A \<and> x \<in> B"
  shows "x \<in> A \<inter> B"
proof -
  from assms have "x \<in> {x. x \<in> A \<and> x \<in> B}" by (intro CollectI)
  thus "?thesis" by (fold Int_def)
qed

lemma inter_implies_conj:
  assumes "x \<in> A \<inter> B"
  shows "x \<in> A \<and> x \<in> B"
proof -
  from assms have "x \<in> {x. x \<in> A \<and> x \<in> B}" by (unfold Int_def)
  thus "?thesis" by (elim CollectD)
qed

proposition prop_1_2_2'_a:
  shows "A \<supseteq> A \<inter> B"
proof -
  {
    fix x
    assume "x \<in> A \<inter> B"
    hence "x \<in> A \<and> x \<in> B" by (elim inter_implies_conj)
    hence "x \<in> A" by (elim conjunct1)
  }
  thus "?thesis" by (intro subsetI)
qed

proposition prop_1_2_2'_b:
  shows "B \<supseteq> A \<inter> B"
proof -
  {
    fix x
    assume "x \<in> A \<inter> B"
    hence "x \<in> A \<and> x \<in> B" by (elim inter_implies_conj)
    hence "x \<in> B" by (elim conjunct2)
  }
  thus "?thesis" by (intro subsetI)
qed

proposition prop_1_2_3':
  assumes "A \<supseteq> C" and "B \<supseteq> C"
  shows "A \<inter> B \<supseteq> C"
proof -
  {
    fix x
    assume "x \<in> C"
    with assms(1) have "x \<in> A" by (elim subsetD)
    moreover from \<open>x \<in> C\<close> assms(2) have "x \<in> B" by (elim subsetD)
    ultimately have "x \<in> A \<and> x \<in> B" by (intro conjI)
    hence "x \<in> A \<inter> B" by (intro conj_implies_inter)
  }
  thus "?thesis" by (intro subsetI)
qed

proposition prop_1_2_4':
  shows "A \<inter> A = A"
proof -
  have "A \<inter> A \<subseteq> A" by (fact prop_1_2_2'_a)
  moreover have "A \<subseteq> A \<inter> A"
  proof -
    have "A \<subseteq> A" by (fact subset_refl)
    thus "?thesis" by (intro prop_1_2_3')
  qed
  ultimately show "?thesis" by (intro equalityI)
qed

proposition prop_1_2_5':
  shows "A \<inter> B = B \<inter> A"
proof -
  have "A \<inter> B \<subseteq> B \<inter> A"
  proof -
    have "A \<inter> B \<subseteq> B" by (fact prop_1_2_2'_b)
    moreover have "A \<inter> B \<subseteq> A" by (fact prop_1_2_2'_a)
    ultimately show "?thesis" by (fact prop_1_2_3')
  qed
  moreover have "B \<inter> A \<subseteq> A \<inter> B"
  proof -
    have "B \<inter> A \<subseteq> A" by (fact prop_1_2_2'_b)
    moreover have "B \<inter> A \<subseteq> B" by (fact prop_1_2_2'_a)
    ultimately show "B \<inter> A \<subseteq> A \<inter> B" by (fact prop_1_2_3')
  qed
  ultimately show "?thesis" by (intro equalityI)
qed

proposition prop_1_2_6':
  shows "(A \<inter> B) \<inter> C = A \<inter> (B \<inter> C)"
proof -
  have "(A \<inter> B) \<inter> C \<subseteq> A \<inter> (B \<inter> C)"
  proof -
    have "(A \<inter> B) \<inter> C \<subseteq> A"
    proof -
      have "(A \<inter> B) \<inter> C \<subseteq> A \<inter> B" by (fact prop_1_2_2'_a)
      also have "\<dots> \<subseteq> A" by (fact prop_1_2_2'_a)
      finally show "?thesis" .
    qed
    moreover have "(A \<inter> B) \<inter> C \<subseteq> B \<inter> C"
    proof -
      have "(A \<inter> B) \<inter> C \<subseteq> B"
      proof -
        have "(A \<inter> B) \<inter> C \<subseteq> A \<inter> B" by (fact prop_1_2_2'_a)
        also have "\<dots> \<subseteq> B" by (fact prop_1_2_2'_b)
        finally show "?thesis" .
      qed
      moreover have "(A \<inter> B) \<inter> C \<subseteq> C" by (fact prop_1_2_2'_b)
      ultimately show "?thesis" by (fact prop_1_2_3')
    qed
    ultimately show "?thesis" by (fact prop_1_2_3')
  qed
  moreover have "A \<inter> (B \<inter> C) \<subseteq> (A \<inter> B) \<inter> C"
  proof -
    have "A \<inter> (B \<inter> C) \<subseteq> A \<inter> B"
    proof -
      have "A \<inter> (B \<inter> C) \<subseteq> A" by (fact prop_1_2_2'_a)
      moreover have "A \<inter> (B \<inter> C) \<subseteq> B"
      proof -
        have "A \<inter> (B \<inter> C) \<subseteq> B \<inter> C" by (fact prop_1_2_2'_b)
        also have "\<dots> \<subseteq> B" by (fact prop_1_2_2'_a)
        finally show "?thesis" .
      qed
      ultimately show "?thesis" by (fact prop_1_2_3')
    qed
    moreover have "A \<inter> (B \<inter> C) \<subseteq> C"
    proof -
      have "A \<inter> (B \<inter> C) \<subseteq> B \<inter> C" by (fact prop_1_2_2'_b)
      also have "\<dots> \<subseteq> C" by (fact prop_1_2_2'_b)
      finally show "?thesis" .
    qed
    ultimately show "?thesis" by (fact prop_1_2_3')
  qed
  ultimately show "?thesis" by (intro equalityI)
qed

proposition prop_1_2_7':
  assumes "A \<subseteq> B"
  shows "A \<inter> B = A"
proof -
  have "A \<inter> B \<subseteq> A" by (fact prop_1_2_2'_a)
  moreover have "A \<subseteq> A \<inter> B"
  proof -
    have "A \<subseteq> A" by (fact subset_refl)
    with assms show "?thesis" by (intro prop_1_2_3')
  qed
  ultimately show "?thesis" by (intro equalityI)
qed

proposition prop_1_2_8':
  assumes "A \<subseteq> B"
  shows "A \<inter> C \<subseteq> B \<inter> C"
proof -
  have "A \<inter> C \<subseteq> B"
  proof -
    have "A \<inter> C \<subseteq> A" by (fact prop_1_2_2'_a)
    with assms show "?thesis" by (fact prop_1_1_4[rotated])
  qed
  moreover have "A \<inter> C \<subseteq> C" by (fact prop_1_2_2'_b)
  ultimately show "?thesis" by (fact prop_1_2_3')
qed

proposition prop_1_2_9':
  shows "{} \<inter> A = {}"
  using prop_1_1_5 by (intro prop_1_2_7')

lemma
  shows "x \<in> A \<union> B \<longleftrightarrow> x \<in> A \<or> x \<in> B" (is "?LHS \<longleftrightarrow> ?RHS")
proof (intro iffI)
  assume "?LHS"
  thus "?RHS" by (fact union_implies_disj)
next
  assume "?RHS"
  thus "?LHS" by (fact disj_implies_union)
qed

(* From now on, we can use @thm{Un_iff}. *)

lemma
  shows "x \<in> A \<inter> B \<longleftrightarrow> x \<in> A \<and> x \<in> B" (is "?LHS \<longleftrightarrow> ?RHS")
proof (intro iffI)
  assume "?LHS"
  thus "?RHS" by (fact inter_implies_conj)
next
  assume "?RHS"
  thus "?LHS" by (fact conj_implies_inter)
qed

(* From now on, we can use @thm{Int_iff}. *)

proposition prop_1_2_10:
  shows "(A \<union> B) \<inter> C = A \<inter> C \<union> B \<inter> C" (is "?LHS = ?RHS")
proof -
  {
    fix x
    have "x \<in> (A \<union> B) \<inter> C \<longleftrightarrow> x \<in> A \<union> B \<and> x \<in> C" by (fact Int_iff)
    also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> B) \<and> x \<in> C" by (simp only: Un_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<in> C \<or> x \<in> B \<and> x \<in> C" by (fact conj_disj_distribR)
    also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> C \<or> x \<in> B \<inter> C" by (simp only: Int_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> C \<union> B \<inter> C" by (simp only: Un_iff)
    finally have "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" .
  }
  thus "?thesis" by (intro set_eqI)
qed

proposition prop_1_2_10':
  shows "(A \<inter> B) \<union> C = (A \<union> C) \<inter> (B \<union> C)" (is "?LHS = ?RHS")
proof -
  {
    fix x
    have "x \<in> (A \<inter> B) \<union> C \<longleftrightarrow> x \<in> (A \<inter> B) \<or> x \<in> C" by (fact Un_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<in> B \<or> x \<in> C" by (simp only: Int_iff)
    also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> C) \<and> (x \<in> B \<or> x \<in> C)" by (intro disj_conj_distribR)
    also have "\<dots> \<longleftrightarrow> x \<in> A \<union> C \<and> x \<in> B \<union> C" by (simp only: Un_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> (A \<union> C) \<inter> (B \<union> C)" by (simp only: Int_iff)
    finally have "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" .
  }
  thus "?thesis" by (intro set_eqI)
qed

proposition prop_1_2_11:
  shows "(A \<union> B) \<inter> A = A"
proof -
  have "A \<subseteq> A \<union> B" by (fact prop_1_2_2_a)
  hence "A \<inter> (A \<union> B) = A" by (intro prop_1_2_7')
  thus "?thesis" by (simp only: prop_1_2_5')
qed

proposition prop_1_2_11':
  shows "(A \<inter> B) \<union> A = A"
proof -
  have "A \<inter> B \<subseteq> A" by (fact prop_1_2_2'_a)
  thus "?thesis" by (intro prop_1_2_7)
qed

lemma
  shows "x \<in> X - A \<longleftrightarrow> x \<in> X \<and> x \<notin> A"
proof (intro iffI)
  assume "x \<in> X - A"
  hence "x \<in> {x. x \<in> X \<and> x \<notin> A}" by simp
  thus "x \<in> X \<and> x \<notin> A" by (elim CollectD)
next
  assume "x \<in> X \<and> x \<notin> A"
  hence "x \<in> {x. x \<in> X \<and> x \<notin> A}" by (intro CollectI)
  thus "x \<in> X- A" by simp
qed

(* From now on, we can use @{Diff_iff}. *)

lemma or_not_eq_true:
  shows "A \<or> \<not>A \<longleftrightarrow> True"
  by simp

lemma not_or_eq_true:
  shows "\<not>A \<or> A \<longleftrightarrow> True"
  by simp

lemma or_true_eq:
  shows "A \<and> True \<longleftrightarrow> A"
  by simp

lemma disj_absorb_iff:
  assumes "A \<subseteq> X"
  shows "x \<in> A \<or> x \<in> X \<longleftrightarrow> x \<in> X"
proof (intro iffI)
  assume "x \<in> A \<or> x \<in> X"
  moreover {
    assume "x \<in> A"
    with assms have "x \<in> X" by (elim subsetD)
  }
  ultimately show "x \<in> X" by (elim disjE)
next
  assume "x \<in> X"
  thus "x \<in> A \<or> x \<in> X" by (intro disjI2)
qed

proposition prop_1_2_12_a:
  assumes "A \<subseteq> X"
  shows "A \<union> (X - A) = X" (is "?LHS = ?RHS")
proof -
  {
    fix x
    have "x \<in> ?LHS \<longleftrightarrow> x \<in> A \<or> x \<in> X - A" by (fact Un_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> A \<or> (x \<in> X \<and> x \<notin> A)" by (simp only: Diff_iff)
    also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> X) \<and> (x \<in> A \<or> x \<notin> A)" by (fact disj_conj_distribL)
    also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> X) \<and> True" by (simp only: or_not_eq_true)
    also have "\<dots> \<longleftrightarrow> x \<in> A \<or> x \<in> X" by (simp only: or_true_eq)
    also from assms have "\<dots> \<longleftrightarrow> x \<in> X" by (simp only: disj_absorb_iff)
    finally have "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" .
  }
  thus "?thesis" by (intro set_eqI)
qed

proposition prop_1_2_12_b:
  shows "A \<inter> (X - A) = {}"
proof -
  {
    fix x
    assume "x \<in> A \<inter> (X - A)"
    hence "x \<in> A \<and> x \<in> X - A" by (simp cong: Un_iff)
    hence *: "x \<in> A \<and> (x \<in> X \<and> x \<notin> A)" by (subst (asm) Diff_iff)
    hence "x \<in> X \<and> x \<notin> A" by (elim conjunct2)
    hence "x \<notin> A" by (elim conjunct2)
    moreover from * have "x \<in> A" by (elim conjunct1)
    ultimately have "False" by (elim notE)
  }
  thus "?thesis" by (intro equals0I)
qed

lemma conj_contra:
  shows "P \<and> \<not>P \<longleftrightarrow> False"
proof (intro iffI)
  assume *: "P \<and> \<not>P"
  hence "P" by (elim conjunct1)
  moreover from * have "\<not>P" by (elim conjunct2)
  ultimately show "False" by (elim notE)
next
  assume "False"
  thus "P \<and> \<not>P" by (elim FalseE)
qed

proposition prop_1_2_13:
  assumes "A \<subseteq> X"
  shows "X - (X - A) = A" (is "?LHS = A")
proof -
  {
    fix x
    have "x \<in> X - (X - A) \<longleftrightarrow> x \<in> X \<and> x \<notin> X - A" by (fact Diff_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> X \<and> \<not>(x \<in> X \<and> x \<notin> A)" by (simp only: Diff_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> X \<and> (x \<notin> X \<or> \<not>(x \<notin> A))" by (simp only: de_Morgan_conj)
    also have "\<dots> \<longleftrightarrow> x \<in> X \<and> (x \<notin> X \<or> x \<in> A)" by (simp only: not_not)
    also have "\<dots> \<longleftrightarrow> x \<in> X \<and> x \<notin> X \<or> x \<in> X \<and> x \<in> A" by (simp only: conj_disj_distribL)
    also have "\<dots> \<longleftrightarrow> False \<or> x \<in> X \<and> x \<in> A" by (simp only: conj_contra)
    also have "\<dots> \<longleftrightarrow> x \<in> X \<and> x \<in> A" by (simp only: simp_thms(32))
    also have "\<dots> \<longleftrightarrow> x \<in> X \<inter> A" by (fact Int_iff[THEN sym])
    also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> X" by (simp only: prop_1_2_5')
    also from assms have "\<dots> \<longleftrightarrow> x \<in> A" by (simp only: prop_1_2_7')
    finally have "x \<in> ?LHS \<longleftrightarrow> x \<in> A" .
  }
  thus "?LHS = A" by (intro set_eqI)
qed

lemma notin_empty:
  shows "x \<notin> {}"
proof (intro notI)
  assume "x \<in> {}"
  thus "False" by (elim emptyE)
qed

proposition prop_1_2_14_a:
  shows "X - {} = X"
proof -
  {
    fix x
    have "x \<in> X - {} \<longleftrightarrow> x \<in> X \<and> x \<notin> {}" by (fact Diff_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> X \<and> True" by (simp only: notin_empty[THEN eqTrueI])
    also have "\<dots> \<longleftrightarrow> x \<in> X" by (simp only: simp_thms(21))
    finally have "x \<in> X - {} \<longleftrightarrow> x \<in> X" .
  }
  thus "?thesis" by (intro set_eqI)
qed

proposition prop_1_2_14_b:
  fixes X :: "'a set"
  shows "X - X = {}"
proof -
  {
    fix x
    assume "x \<in> X - X"
    hence "x \<in> X \<and> x \<notin> X" by (subst (asm) Diff_iff)
    hence "False" by (subst (asm) conj_contra)
  }
  thus "?thesis" by (intro equals0I)
qed

proposition prop_1_2_15_pre:
  assumes "A \<subseteq> B"
  shows "X - A \<supseteq> X - B"
proof -
  {
    fix x
    assume "x \<in> X - B"
    hence *: "x \<in> X \<and> x \<notin> B" by (unfold Diff_iff)
    {
      assume "x \<in> A"
      with assms have "x \<in> B" by (elim subsetD)
      moreover from * have "x \<notin> B" by (elim conjunct2)
      ultimately have "False" by (elim notE)
    }
    hence "x \<notin> A" by (intro notI)
    moreover with * have "x \<in> X" by (elim conjunct1)
    ultimately have "x \<in> X - A" by (intro DiffI)
  }
  thus "X - A \<supseteq> X - B" by (intro subsetI)
qed

proposition prop_1_2_15:
  assumes "A \<subseteq> X" and "B \<subseteq> X"
  shows "A \<subseteq> B \<longleftrightarrow> X - A \<supseteq> X - B"
proof (intro iffI)
  assume "A \<subseteq> B"
  thus "X - A \<supseteq> X - B" by (fact prop_1_2_15_pre)
next
  assume "X - A \<supseteq> X - B"
  hence "X - (X - A) \<subseteq> X - (X - B)" by (fact prop_1_2_15_pre)
  with assms(1) have "A \<subseteq> X - (X - B)" by (subst (asm) prop_1_2_13)
  with assms(2) show "A \<subseteq> B" by (subst (asm) prop_1_2_13)
qed

proposition prop_1_2_16:
  assumes "A \<subseteq> X" and "B \<subseteq> X"
  shows "X - (A \<union> B) = (X - A) \<inter> (X - B)" (is "?LHS = ?RHS")
proof -
  {
    fix x
    have "x \<in> X - (A \<union> B) \<longleftrightarrow> x \<in> X \<and> x \<notin> A \<union> B" by (fact Diff_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> X \<and> \<not>(x \<in> A \<or> x \<in> B)" by (simp only: Un_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> X \<and> x \<notin> A \<and> x \<notin> B" by (simp only: de_Morgan_disj)
    also have "\<dots> \<longleftrightarrow> (x \<in> X \<and> x \<in> X) \<and> x \<notin> A \<and> x \<notin> B" by (simp only: conj_absorb)
    also have "\<dots> \<longleftrightarrow> ((x \<in> X \<and> x \<in> X) \<and> x \<notin> A) \<and> x \<notin> B" by (fact conj_assoc[THEN sym])
    also have "\<dots> \<longleftrightarrow> (x \<in> X \<and> x \<in> X \<and> x \<notin> A) \<and> x \<notin> B" by (simp only: conj_assoc)
    also have "\<dots> \<longleftrightarrow> (x \<in> X \<and> x \<notin> A \<and> x \<in> X) \<and> x \<notin> B" by (simp only: conj_commute)
    also have "\<dots> \<longleftrightarrow> ((x \<in> X \<and> x \<notin> A) \<and> x \<in> X) \<and> x \<notin> B" by (simp only: conj_assoc)
    also have "\<dots> \<longleftrightarrow> (x \<in> X \<and> x \<notin> A) \<and> (x \<in> X \<and> x \<notin> B)" by (simp only: conj_assoc)
    also have "\<dots> \<longleftrightarrow> x \<in> X - A \<and> x \<in> X - B" by (simp only: Diff_iff)
    also have "\<dots> \<longleftrightarrow> x \<in> ?RHS" by (simp only: Int_iff)
    finally have "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" .
  }
  thus "?thesis" by (intro set_eqI)
qed

proposition prop_1_2_16':
  shows "X - (A \<inter> B) = (X - A) \<union> (X - B)" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix x
  have "x \<in> ?LHS \<longleftrightarrow> x \<in> X \<and> x \<notin> A \<inter> B" by (fact Diff_iff)
  also have "... \<longleftrightarrow> x \<in> X \<and> \<not>(x \<in> A \<and> x \<in> B)" by (simp cong: Int_iff)
  also have "... \<longleftrightarrow> x \<in> X \<and> (x \<notin> A \<or> x \<notin> B)" by (simp cong: de_Morgan_conj)
  also have "... \<longleftrightarrow> (x \<in> X \<and> x \<notin> A) \<or> (x \<in> X \<and> x \<notin> B)" by (intro conj_disj_distribL)
  also have "... \<longleftrightarrow> x \<in> X - A \<or> x \<in> X - B" by (simp cong: Diff_iff)
  also have "... \<longleftrightarrow> x \<in> ?RHS" by (simp only: Un_iff)
  finally show "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" .
qed

proposition prop_1_2_17:
  shows "\<forall>A \<in> \<AA>. A \<subseteq> \<Union>\<AA>"
proof (intro ballI)
  fix A
  assume "A \<in> \<AA>"
  show "A \<subseteq> \<Union>\<AA>"
  proof (intro subsetI)
    fix x
    assume "x \<in> A"
    with \<open>A \<in> \<AA>\<close> have "\<exists>A \<in> \<AA>. x \<in> A" by (intro bexI)
    thus "x \<in> \<Union>\<AA>" by (fold Union_iff)
  qed
qed

proposition prop_1_2_18:
  assumes "\<forall>A \<in> \<AA>. A \<subseteq> C"
  shows "\<Union>\<AA> \<subseteq> C"
proof (intro subsetI)
  fix x
  assume "x \<in> \<Union>\<AA>"
  hence "\<exists>A \<in> \<AA>. x \<in> A" by (unfold Union_iff)
  then obtain A where "A \<in> \<AA>" and "x \<in> A" ..
  from assms and \<open>A \<in> \<AA>\<close> have "A \<subseteq> C" by (elim bspec)
  with \<open>x \<in> A\<close> show "x \<in> C" by (elim subsetD)
qed

proposition prop_1_2_17':
  shows "\<forall>A \<in> \<AA>. A \<supseteq> \<Inter>\<AA>"
proof (intro ballI)
  fix A
  assume "A \<in> \<AA>"
  show "A \<supseteq> \<Inter>\<AA>"
  proof (intro subsetI)
    fix x
    assume "x \<in> \<Inter>\<AA>"
    hence "\<forall>A \<in> \<AA>. x \<in> A" by (unfold Inter_iff)
    with \<open>A \<in> \<AA>\<close> show "x \<in> A" by (elim bspec)
  qed
qed

proposition prop_1_2_18':
  assumes "\<forall>A \<in> \<AA>. A \<supseteq> C"
  shows "\<Inter>\<AA> \<supseteq> C"
proof (intro subsetI)
  fix x
  assume "x \<in> C"
  show "x \<in> \<Inter>\<AA>"
  proof (intro InterI)
    fix A
    assume "A \<in> \<AA>"
    with assms have "A \<supseteq> C" by (elim bspec)
    with \<open>x \<in> C\<close> show "x \<in> A" by (elim subsetD)
  qed
qed

proposition problem_1_2_1_a:
  assumes (*"A \<subseteq> X" and*) "B \<subseteq> X"
  shows "(A \<union> B) \<inter> (A \<union> (X - B)) = A"
  by auto

proposition problem_1_2_1_b:
  (*assumes "A \<subseteq> X" and "B \<subseteq> X"*)
  shows "(A \<union> B) \<inter> ((X - A) \<union> B) \<inter> (A \<union> (X - B)) = A \<inter> B"
  by auto

proposition problem_1_2_2_a:
  assumes (*"A \<subseteq> X" and*) "B \<subseteq> X"
  shows "A \<inter> B = {} \<longleftrightarrow> X - A \<supseteq> B"
proof (intro iffI)
  assume "A \<inter> B = {}"
  {
    fix x
    assume "x \<in> B"
    with assms have "x \<in> X" by (elim subsetD)
    moreover have "x \<notin> A"
    proof (intro notI)
      assume "x \<in> A"
      with \<open>x \<in> B\<close> have "x \<in> A \<inter> B" by (intro IntI)
      hence "x \<in> {}" by (subst (asm) \<open>A \<inter> B = {}\<close>)
      thus "False" by (elim emptyE)
    qed
    ultimately have "x \<in> X - A" by (intro DiffI)
  }
  thus "X - A \<supseteq> B" by (intro subsetI)
next
  assume "X - A \<supseteq> B"
  {
    fix x
    assume "x \<in> A" and "x \<in> B"
    from this(2) and \<open>X - A \<supseteq> B\<close> have "x \<in> X - A" by (elim subsetD)
    with \<open>x \<in> A\<close> have "False" by (elim DiffD2)
  }
  thus "A \<inter> B = {}" by (intro Int_emptyI)
qed

proposition problem_1_2_2_b:
  assumes "A \<subseteq> X" (*and "B \<subseteq> X"*)
  shows "A \<inter> B = {} \<longleftrightarrow> A \<subseteq> X - B"
proof -
  from assms have "B \<inter> A = {} \<longleftrightarrow> X - B \<supseteq> A" by (fact problem_1_2_2_a)
  thus "A \<inter> B = {} \<longleftrightarrow> A \<subseteq> X - B" by (subst (asm) Int_commute)
qed

proposition problem_1_2_3_a:
  shows "A - B = (A \<union> B) - B" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix x
  have "x \<in> ?RHS \<longleftrightarrow> x \<in> A \<union> B \<and> x \<notin> B" by (fact Diff_iff)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> B) \<and> x \<notin> B" by (simp only: Un_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> B \<or> x \<in> B \<and> x \<notin> B" by (fact conj_disj_distribR)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> B \<or> False" by (simp only: conj_contra)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> B" by (simp only: simp_thms(31))
  also have "\<dots> \<longleftrightarrow> x \<in> A - B" by (fact Diff_iff[THEN sym])
  finally have "x \<in> ?RHS \<longleftrightarrow> x \<in> ?LHS" .
  thus "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" by (fact sym)
qed

proposition problem_1_2_3_b:
  shows "A - B = A - (A \<inter> B)"
proof (intro set_eqI)
  fix x
  have "x \<in> A - (A \<inter> B) \<longleftrightarrow> x \<in> A \<and> x \<notin> A \<inter> B" by (fact Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> \<not>(x \<in> A \<and> x \<in> B)" by (simp only: Int_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> (x \<notin> A \<or> x \<notin> B)" by (simp only: de_Morgan_conj)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> A \<or> x \<in> A \<and> x \<notin> B" by (simp only: conj_disj_distribL)
  also have "\<dots> \<longleftrightarrow> False \<or> x \<in> A \<and> x \<notin> B" by (simp only: conj_contra)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> B" by (simp only: simp_thms(32))
  also have "\<dots> \<longleftrightarrow> x \<in> A - B" by (fact Diff_iff[THEN sym])
  finally have "x \<in> A - (A \<inter> B) \<longleftrightarrow> x \<in> A - B" .
  thus "x \<in> A - B \<longleftrightarrow> x \<in> A - (A \<inter> B)" by (fact sym)
qed

proposition problem_1_2_3_c:
  assumes "A \<subseteq> X"
  shows "A - B = A \<inter> (X - B)"
proof (intro set_eqI)
  fix x
  have "x \<in> A \<inter> (X - B) \<longleftrightarrow> x \<in> A \<and> x \<in> X - B" by (fact Int_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<in> X \<and> x \<notin> B" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<in> X) \<and> x \<notin> B" by (fact conj_assoc[THEN sym])
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> X \<and> x \<notin> B" by (simp only: Int_iff)
  also from assms have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> B" by (simp only: prop_1_2_7')
  also have "\<dots> \<longleftrightarrow> x \<in> A - B" by (fact Diff_iff[THEN sym])
  finally have "x \<in> A \<inter> (X - B) \<longleftrightarrow> x \<in> A - B" .
  thus "x \<in> A - B \<longleftrightarrow> x \<in> A \<inter> (X - B)" by (fact sym)
qed

proposition problem_1_2_4_a:
  shows "A - (B \<union> C) = (A - B) \<inter> (A - C)"
proof (intro set_eqI)
  fix x
  have "x \<in> A - (B \<union> C) \<longleftrightarrow> x \<in> A \<and> x \<notin> B \<union> C" by (fact Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> \<not>(x \<in> B \<or> x \<in> C)" by (simp only: Un_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> B \<and> x \<notin> C" by (simp only: de_Morgan_disj)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<in> A) \<and> x \<notin> B \<and> x \<notin> C" by (simp only: conj_absorb)
  also have "\<dots> \<longleftrightarrow> ((x \<in> A \<and> x \<in> A) \<and> x \<notin> B) \<and> x \<notin> C" by (fact conj_assoc[THEN sym])
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<in> A \<and> x \<notin> B) \<and> x \<notin> C" by (simp only: conj_assoc)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<notin> B \<and> x \<in> A) \<and> x \<notin> C" by (simp only: conj_commute)
  also have "\<dots> \<longleftrightarrow> ((x \<in> A \<and> x \<notin> B) \<and> x \<in> A) \<and> x \<notin> C" by (simp only: conj_assoc)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<notin> B) \<and> x \<in> A \<and> x \<notin> C" by (fact conj_assoc)
  also have "\<dots> \<longleftrightarrow> x \<in> A - B \<and> x \<in> A - C" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> (A - B) \<inter> (A - C)" by (fact Int_iff[THEN sym])
  finally show "x \<in> A - (B \<union> C) \<longleftrightarrow> x \<in> (A - B) \<inter> (A - C)" .
qed

proposition problem_1_2_4_b:
  shows "A - (B \<inter> C) = (A - B) \<union> (A - C)"
proof (intro set_eqI)
  fix x
  have "x \<in> A - (B \<inter> C) \<longleftrightarrow> x \<in> A \<and> x \<notin> (B \<inter> C)" by (fact Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> \<not>(x \<in> B \<and> x \<in> C)" by (simp only: Int_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> (x \<notin> B \<or> x \<notin> C)" by (simp only: de_Morgan_conj)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> B \<or> x \<in> A \<and> x \<notin> C" by (fact conj_disj_distribL)
  also have "\<dots> \<longleftrightarrow> x \<in> A - B \<or> x \<in> A - C" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> (A - B) \<union> (A - C)" by (fact Un_iff[THEN sym])
  finally show "x \<in> A - (B \<inter> C) \<longleftrightarrow> x \<in> (A - B) \<union> (A - C)" .
qed

proposition problem_1_2_4_c:
  shows "(A \<union> B) - C = (A - C) \<union> (B - C)" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix x
  have "x \<in> ?RHS \<longleftrightarrow> x \<in> A - C \<or> x \<in> B - C" by (fact Un_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> C \<or> x \<in> B \<and> x \<notin> C" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> B) \<and> x \<notin> C" by (fact conj_disj_distribR[THEN sym])
  also have "\<dots> \<longleftrightarrow> x \<in> A \<union> B \<and> x \<notin> C" by (simp only: Un_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> (A \<union> B) - C" by (fact Diff_iff[THEN sym])
  finally have "x \<in> ?RHS \<longleftrightarrow> x \<in> ?LHS" .
  thus "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" by (fact sym)
qed

proposition problem_1_2_4_d:
  shows "(A \<inter> B) - C = (A - C) \<inter> (B - C)" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix x
  have "x \<in> ?RHS \<longleftrightarrow> x \<in> A - C \<and> x \<in> B - C" by (fact Int_iff)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<notin> C) \<and> x \<in> B \<and> x \<notin> C" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> ((x \<in> A \<and> x \<notin> C) \<and> x \<in> B) \<and> x \<notin> C" by (fact conj_assoc[THEN sym])
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<notin> C \<and> x \<in> B) \<and> x \<notin> C" by (simp only: conj_assoc)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<in> B \<and> x \<notin> C) \<and> x \<notin> C" by (simp only: conj_commute)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> (x \<in> B \<and> x \<notin> C) \<and> x \<notin> C" by (fact conj_assoc)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<in> B \<and> x \<notin> C \<and> x \<notin> C" by (simp only: conj_assoc)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<in> B \<and> x \<notin> C" by (simp only: conj_absorb)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<in> B) \<and> x \<notin> C" by (fact conj_assoc[THEN sym])
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> B \<and> x \<notin> C" by (simp only: Int_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> ?LHS" by (fact Diff_iff[THEN sym])
  finally have "x \<in> ?RHS \<longleftrightarrow> x \<in> ?LHS" .
  thus "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" by (fact sym)
qed

proposition problem_1_2_4_e:
  shows "A \<inter> (B - C) = (A \<inter> B) - (A \<inter> C)" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix x
  have "x \<in> ?RHS \<longleftrightarrow> x \<in> A \<inter> B \<and> x \<notin> A \<inter> C" by (fact Diff_iff)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<in> B) \<and> \<not>(x \<in> A \<and> x \<in> C)" by (simp only: Int_iff)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<in> B) \<and> (x \<notin> A \<or> x \<notin> C)" by (simp only: de_Morgan_conj)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<in> B) \<and> x \<notin> A \<or> (x \<in> A \<and> x \<in> B) \<and> x \<notin> C" by (fact conj_disj_distribL)
  also have "\<dots> \<longleftrightarrow> (x \<in> B \<and> x \<in> A) \<and> x \<notin> A \<or> (x \<in> A \<and> x \<in> B) \<and> x \<notin> C" by (simp only: conj_commute)
  also have "\<dots> \<longleftrightarrow> x \<in> B \<and> x \<in> A \<and> x \<notin> A \<or> (x \<in> A \<and> x \<in> B) \<and> x \<notin> C" by (simp only: conj_assoc)
  also have "\<dots> \<longleftrightarrow> x \<in> B \<and> False \<or> (x \<in> A \<and> x \<in> B) \<and> x \<notin> C" by (simp only: conj_contra)
  also have "\<dots> \<longleftrightarrow> False \<or> (x \<in> A \<and> x \<in> B) \<and> x \<notin> C" by (simp only: simp_thms(23))
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<in> B) \<and> x \<notin> C" by (simp only: simp_thms(32))
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<in> B \<and> x \<notin> C" by (fact conj_assoc)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<in> B - C" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> ?LHS" by (fact Int_iff[THEN sym])
  finally have "x \<in> ?RHS \<longleftrightarrow> x \<in> ?LHS" .
  thus "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" by (fact sym)
qed

proposition problem_1_2_5_a:
  shows "(A - B) - C = A - (B \<union> C)" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix x
  have "x \<in> ?RHS \<longleftrightarrow> x \<in> A \<and> x \<notin> B \<union> C" by (fact Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> \<not>(x \<in> B \<or> x \<in> C)" by (simp only: Un_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> B \<and> x \<notin> C" by (simp only: de_Morgan_disj)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<and> x \<notin> B) \<and> x \<notin> C" by (fact conj_assoc[THEN sym])
  also have "\<dots> \<longleftrightarrow> (x \<in> A - B) \<and> x \<notin> C" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> ?LHS" by (fact Diff_iff[THEN sym])
  finally have "x \<in> ?RHS \<longleftrightarrow> x \<in> ?LHS" .
  thus "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" by (fact sym)
qed

proposition problem_1_2_5_b:
  shows "A - (B - C) = (A - B) \<union> (A \<inter> C)" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix x
  have "x \<in> ?LHS \<longleftrightarrow> x \<in> A \<and> x \<notin> B - C" by (fact Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> \<not>(x \<in> B \<and> x \<notin> C)" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> (x \<notin> B \<or> \<not>(x \<notin> C))" by (simp only: de_Morgan_conj)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> (x \<notin> B \<or> x \<in> C)" by (simp only: not_not)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> B \<or> x \<in> A \<and> x \<in> C" by (fact conj_disj_distribL)
  also have "\<dots> \<longleftrightarrow> x \<in> A - B \<or> x \<in> A \<and> x \<in> C" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A - B \<or> x \<in> A \<inter> C" by (simp only: Int_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> ?RHS" by (simp only: Un_iff)
  finally show "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" .
qed

proposition problem_1_2_6:
  assumes "A \<subseteq> C"
  shows "A \<union> (B \<inter> C) = (A \<union> B) \<inter> C"
proof (intro set_eqI)
  fix x
  have "x \<in> A \<union> (B \<inter> C) \<longleftrightarrow> x \<in> A \<or> x \<in> B \<inter> C" by (fact Un_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<or> (x \<in> B \<and> x \<in> C)" by (simp only: Int_iff)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> B) \<and> (x \<in> A \<or> x \<in> C)" by (simp only: disj_conj_distribL)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> B) \<and> x \<in> A \<union> C" by (simp only: Un_iff)
  also from assms have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> B) \<and> x \<in> C" by (simp only: prop_1_2_7)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<union> B) \<and> x \<in> C" by (simp only: Un_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> (A \<union> B) \<inter> C" by (simp only: Int_iff)
  finally show "x \<in> A \<union> (B \<inter> C) \<longleftrightarrow> x \<in> (A \<union> B) \<inter> C" .
qed

definition sym_diff :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "sym_diff A B = (A - B) \<union> (B - A)"

proposition problem_1_2_7_a:
  shows "sym_diff A B = sym_diff B A"
proof (intro set_eqI)
  fix x
  have "x \<in> sym_diff A B \<longleftrightarrow> x \<in> (A - B) \<union> (B - A)" by (simp only: sym_diff_def)
  also have "\<dots> \<longleftrightarrow> x \<in> A - B \<or> x \<in> B - A" by (simp only: Un_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> B \<or> x \<in> B \<and> x \<notin> A" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> B \<and> x \<notin> A \<or> x \<in> A \<and> x \<notin> B" by (fact disj_commute)
  also have "\<dots> \<longleftrightarrow> x \<in> B - A \<or> x \<in> A - B" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> (B - A) \<union> (A - B)" by (fact Un_iff[THEN sym])
  also have "\<dots> \<longleftrightarrow> x \<in> sym_diff B A" by (simp only: sym_diff_def)
  finally show "x \<in> sym_diff A B \<longleftrightarrow> x \<in> sym_diff B A" .
qed

proposition problem_1_2_7_b:
  shows "sym_diff A B = (A \<union> B) - (A \<inter> B)"
proof (intro set_eqI)
  fix x
  have "x \<in> sym_diff A B \<longleftrightarrow> x \<in> (A - B) \<union> (B - A)" by (simp only: sym_diff_def)
  also have "\<dots> \<longleftrightarrow> x \<in> A - B \<or> x \<in> B - A" by (fact Un_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> B \<or> x \<in> B \<and> x \<notin> A" by (simp only: Diff_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> B \<and> x \<notin> A \<or> x \<in> A \<and> x \<notin> B" by (fact disj_commute)
  also have "\<dots> \<longleftrightarrow> False \<or> x \<in> B \<and> x \<notin> A \<or> x \<in> A \<and> x \<notin> B" by (simp only: simp_thms(32))
  also have "\<dots> \<longleftrightarrow> False \<or> x \<in> B \<and> x \<notin> A \<or> x \<in> A \<and> x \<notin> B \<or> False" by (simp only: simp_thms(31))
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<notin> A \<or> x \<in> B \<and> x \<notin> A \<or> x \<in> A \<and> x \<notin> B \<or> x \<in> B \<and> x \<notin> B"
    by (simp only: conj_contra)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> B) \<and> x \<notin> A \<or> (x \<in> A \<or> x \<in> B) \<and> x \<notin> B" by auto
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> B) \<and> (x \<notin> A \<or> x \<notin> B)" by (fact conj_disj_distribL[THEN sym])
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> B) \<and> \<not>(x \<in> A \<and> x \<in> B)" by (simp only: de_Morgan_conj)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<or> x \<in> B) \<and> x \<notin> A \<inter> B" by (simp only: Int_iff)
  also have "\<dots> \<longleftrightarrow> (x \<in> A \<union> B) \<and> x \<notin> A \<inter> B" by (simp only: Un_iff)
  also have "\<dots> \<longleftrightarrow> x \<in> (A \<union> B) - (A \<inter> B)" by (fact Diff_iff[THEN sym])
  finally show "x \<in> sym_diff A B \<longleftrightarrow> x \<in> (A \<union> B) - (A \<inter> B)" .
qed

proposition problem_1_2_7_c:
  shows "sym_diff (sym_diff A B) C = sym_diff A (sym_diff B C)" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix x
  have "x \<in> ?LHS \<longleftrightarrow> x \<in> (((A - B) \<union> (B - A)) - C) \<union> (C - ((A - B) \<union> (B - A)))"
    by (simp add:sym_diff_def)
  also have "\<dots> \<longleftrightarrow> x \<in> ((A - B) - C) \<union> ((B - C) - A) \<union> (C - ((A - B) \<union> (B - A)))"
    (is "_ \<longleftrightarrow> x \<in> ?ABC \<union> ?BCA \<union> _") by auto
  also have "\<dots> \<longleftrightarrow> x \<in> ?ABC \<union> ?BCA \<union> C \<inter> -((A - B) \<union> (B - A))" by simp
  also have "\<dots> \<longleftrightarrow> x \<in> ?ABC \<union> ?BCA \<union> C \<inter> -(A - B) \<inter> -(B - A)" by simp
  also have "\<dots> \<longleftrightarrow> x \<in> ?ABC \<union> ?BCA \<union> C \<inter> (-A \<union> B) \<inter> (-B \<union> A)" by simp
  also have "\<dots> \<longleftrightarrow> x \<in> ?ABC \<union> ?BCA \<union> ((C - A) - B) \<union> A \<inter> B \<inter> C" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> B \<inter> C \<union> ?ABC \<union> ?BCA \<union> ((C - A) - B)"
    (is "_ \<longleftrightarrow> x \<in> _ \<union> _ \<union> _ \<union> ?CAB") by auto
  finally have *: "x \<in> ?LHS \<longleftrightarrow> x \<in> A \<inter> B \<inter> C \<union> ?ABC \<union> ?BCA \<union> ?CAB" (is "_ \<longleftrightarrow> x \<in> ?X") .
  have "x \<in> sym_diff A (sym_diff B C) \<longleftrightarrow> x \<in> (A - ((B - C) \<union> (C - B))) \<union> (((B - C) \<union> (C - B)) - A)"
    (is "_ \<longleftrightarrow> x \<in> ?L1 \<union> _") by (simp add: sym_diff_def)
  also have "\<dots> \<longleftrightarrow> x \<in> ?L1 \<union> (((B \<union> C) \<inter> (-B \<union> -C)) - A)" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> ?L1 \<union> (((B - C) \<union> (C - B)) - A)" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> ?L1 \<union> ?BCA \<union> ?CAB" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> (-(B - C) \<inter> -(C - B)) \<union> ?BCA \<union> ?CAB" by simp
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> ((-B \<union> C) \<inter> (-C \<union> B)) \<union> ?BCA \<union> ?CAB" by simp
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> (-B \<inter> -C \<union> B \<inter> C) \<union> ?BCA \<union> ?CAB" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> ((A - B) - C) \<union> A \<inter> B \<inter> C \<union> ?BCA \<union> ?CAB" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> B \<inter> C \<union> ?ABC \<union> ?BCA \<union> ?CAB" by auto
  finally have "x \<in> ?RHS \<longleftrightarrow> x \<in> ?X" .
  with * show "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" ..
qed

proposition problem_1_2_7_d:
  shows "A \<inter> (sym_diff B C) = sym_diff (A \<inter> B) (A \<inter> C)" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix x
  have "x \<in> ?LHS \<longleftrightarrow> x \<in> A \<inter> ((B - C) \<union> (C - B))" by (simp only: sym_diff_def)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> (B \<union> C) \<inter> (-B \<union> -C)" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> B \<inter> -C \<union> A \<inter> -B \<inter> C" (is "_ \<longleftrightarrow> x \<in> ?DNF") by auto
  finally have *: "x \<in> ?LHS \<longleftrightarrow> x \<in> ?DNF" .
  have "x \<in> ?RHS \<longleftrightarrow> x \<in> ((A \<inter> B) - (A \<inter> C)) \<union> ((A \<inter> C) - (A \<inter> B))" by (simp only: sym_diff_def)
  also have "\<dots> \<longleftrightarrow> x \<in> ((A \<inter> B) \<inter> (-A \<union> -C)) \<union> ((A \<inter> C) \<inter> (-A \<union> -B))" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> B \<inter> -C \<union> A \<inter> -B \<inter> C" by auto
  finally have "x \<in> ?RHS \<longleftrightarrow> x \<in> ?DNF" .
  with * show "x \<in> ?LHS \<longleftrightarrow> x \<in> ?RHS" ..
qed

proposition problem_1_2_8_a:
  shows "sym_diff A {} = A"
proof (intro set_eqI)
  fix x
  have "x \<in> sym_diff A {} \<longleftrightarrow> x \<in> (A - {}) \<union> ({} - A)" by (simp only: sym_diff_def)
  also have "\<dots> \<longleftrightarrow> x \<in> A" by auto
  finally show "x \<in> sym_diff A {} \<longleftrightarrow> x \<in> A" .
qed

proposition problem_1_2_8_b:
  assumes "A \<subseteq> X"
  shows "sym_diff A X = X - A"
proof (intro set_eqI)
  fix x
  have "x \<in> sym_diff A X \<longleftrightarrow> x \<in> (A - X) \<union> (X - A)" by (simp only: sym_diff_def)
  also from assms have "\<dots> \<longleftrightarrow> x \<in> {} \<union> (X - A)" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> X - A" by simp
  finally show "x \<in> sym_diff A X \<longleftrightarrow> x \<in> X - A" .
qed

proposition problem_1_2_8_c:
  shows "sym_diff A A = {}"
proof (intro set_eqI)
  fix x
  have "x \<in> sym_diff A A \<longleftrightarrow> x \<in> (A - A) \<union> (A - A)" by (simp only: sym_diff_def)
  also have "\<dots> \<longleftrightarrow> x \<in> {}" by simp
  finally show "x \<in> sym_diff A A \<longleftrightarrow> x \<in> {}" .
qed

proposition problem_1_2_8_d:
  assumes "A \<subseteq> X"
  shows "sym_diff A (X - A) = X"
proof (intro set_eqI)
  fix x
  have "x \<in> sym_diff A (X - A) \<longleftrightarrow> x \<in> (A - (X - A)) \<union> ((X - A) - A)" by (simp only: sym_diff_def)
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> -(X - A) \<union> (X - A) \<inter> -A" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> -(X \<inter> -A) \<union> X \<inter> -A \<inter> -A" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> (-X \<union> A) \<union> X \<inter> -A" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> -X \<union> A \<inter> A \<union> X \<inter> -A" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> A \<union> X \<inter> -A" by auto
  also from assms have "\<dots> \<longleftrightarrow> x \<in> X \<inter> A \<union> X \<inter> -A" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> X \<inter> (A \<union> -A)" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> X" by simp
  finally show "x \<in> sym_diff A (X - A) \<longleftrightarrow> x \<in> X" .
qed

proposition problem_1_2_9:
  assumes "sym_diff A\<^sub>1 A\<^sub>2 = sym_diff B\<^sub>1 B\<^sub>2"
  shows "sym_diff A\<^sub>1 B\<^sub>1 = sym_diff A\<^sub>2 B\<^sub>2"
proof -
  from assms have "sym_diff B\<^sub>1 (sym_diff A\<^sub>1 A\<^sub>2) = sym_diff B\<^sub>1 (sym_diff B\<^sub>1 B\<^sub>2)" by simp
  hence "sym_diff (sym_diff B\<^sub>1 A\<^sub>1) A\<^sub>2 = sym_diff (sym_diff B\<^sub>1 B\<^sub>1) B\<^sub>2" by (simp only: problem_1_2_7_c)
  hence "sym_diff (sym_diff B\<^sub>1 A\<^sub>1) A\<^sub>2 = sym_diff {} B\<^sub>2" by (simp only: problem_1_2_8_c)
  hence "sym_diff (sym_diff B\<^sub>1 A\<^sub>1) A\<^sub>2 = sym_diff B\<^sub>2 {}" by (simp only: problem_1_2_7_a)
  hence "sym_diff (sym_diff B\<^sub>1 A\<^sub>1) A\<^sub>2 = B\<^sub>2" by (simp only: problem_1_2_8_a)
  hence "sym_diff (sym_diff (sym_diff B\<^sub>1 A\<^sub>1) A\<^sub>2) A\<^sub>2 = sym_diff B\<^sub>2 A\<^sub>2" by simp
  hence "sym_diff (sym_diff B\<^sub>1 A\<^sub>1) (sym_diff A\<^sub>2 A\<^sub>2) = sym_diff B\<^sub>2 A\<^sub>2" by (simp only: problem_1_2_7_c)
  hence "sym_diff (sym_diff B\<^sub>1 A\<^sub>1) {} = sym_diff B\<^sub>2 A\<^sub>2" by (simp only: problem_1_2_8_c)
  hence "sym_diff B\<^sub>1 A\<^sub>1 = sym_diff B\<^sub>2 A\<^sub>2" by (simp only: problem_1_2_8_a)
  thus "sym_diff A\<^sub>1 B\<^sub>1 = sym_diff A\<^sub>2 B\<^sub>2" by (simp only: problem_1_2_7_a)
qed

section "Correspondences, Functions"

definition corr_graph :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<times> 'b) set"
  where "corr_graph \<Gamma> = {p. snd p \<in> \<Gamma> (fst p)}"

proposition prop_1_3_1:
  shows "\<Gamma> a = {b. (a, b) \<in> corr_graph \<Gamma>}" (is "_ = ?RHS")
proof (intro set_eqI)
  fix b
  have "b \<in> ?RHS \<longleftrightarrow> (a, b) \<in> corr_graph \<Gamma>" by (fact mem_Collect_eq)
  also have "\<dots> \<longleftrightarrow> (a, b) \<in> {p. snd p \<in> \<Gamma> (fst p)}" by (simp only: corr_graph_def)
  also have "\<dots> \<longleftrightarrow> b \<in> \<Gamma> a" by simp
  finally show "b \<in> \<Gamma> a \<longleftrightarrow> b \<in> ?RHS" ..
qed

theorem th_1_1:
  shows "\<exists>!\<Gamma>. corr_graph \<Gamma> = G"
proof (intro ex1I)
  define \<Gamma> where Gamma: "\<Gamma> a = {b. (a, b) \<in> G}" for a
  show "corr_graph \<Gamma> = G"
  proof (intro set_eqI)
    fix g :: "'a \<times> 'b"
    let ?a = "fst g" and ?b = "snd g"
    have "g \<in> corr_graph \<Gamma> \<longleftrightarrow> ?b \<in> \<Gamma> ?a" by (simp add: corr_graph_def)
    also have "\<dots> \<longleftrightarrow> ?b \<in> {b. (?a, b) \<in> G}" by (simp only: Gamma)
    also have "\<dots> \<longleftrightarrow> (?a, ?b) \<in> G" by simp
    also have "\<dots> \<longleftrightarrow> g \<in> G" by simp
    finally show "g \<in> corr_graph \<Gamma> \<longleftrightarrow> g \<in> G" .
  qed
next
  fix \<Gamma>
  assume "corr_graph \<Gamma> = G"
  {
    fix a
    have "\<Gamma> a = {b. (a, b) \<in> corr_graph \<Gamma>}" by (fact prop_1_3_1)
    hence "\<Gamma> a = {b. (a, b) \<in> G}" by (simp only: \<open>corr_graph \<Gamma> = G\<close>)
  }
  thus "\<Gamma> = (\<lambda>a. {b. (a, b) \<in> G})" by auto
qed

definition corr_dom :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set"
  where "corr_dom \<Gamma> = {a. \<exists>b. (a, b) \<in> corr_graph \<Gamma>}"

definition corr_range :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set"
  where "corr_range \<Gamma> = {b. \<exists>a. (a, b) \<in> corr_graph \<Gamma>}"

definition corr_inv :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b \<Rightarrow> 'a set"
  where "corr_inv \<Gamma> b = {a. b \<in> \<Gamma> a}"

proposition prop_1_3_2:
  shows "b \<in> \<Gamma> a \<longleftrightarrow> a \<in> corr_inv \<Gamma> b"
proof -
  have "b \<in> \<Gamma> a \<longleftrightarrow> a \<in> {a. b \<in> \<Gamma> a}" by simp
  also have "\<dots> \<longleftrightarrow> a \<in> corr_inv \<Gamma> b" by (simp only: corr_inv_def)
  finally show "?thesis" .
qed

proposition prop_1_3_3_a:
  shows "corr_dom (corr_inv \<Gamma>) = corr_range \<Gamma>"
proof (intro set_eqI)
  fix b
  have "b \<in> corr_dom (corr_inv \<Gamma>) \<longleftrightarrow> (\<exists>a. (b, a) \<in> corr_graph (corr_inv \<Gamma>))"
    by (simp add: corr_dom_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>a. a \<in> corr_inv \<Gamma> b)" by (simp add: corr_graph_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>a. b \<in> \<Gamma> a)" by (simp add: corr_inv_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>a. (a, b) \<in> corr_graph \<Gamma>)" by (simp add: corr_graph_def)
  also have "... \<longleftrightarrow> b \<in> corr_range \<Gamma>" by (simp add: corr_range_def)
  finally show "b \<in> corr_dom (corr_inv \<Gamma>) \<longleftrightarrow> b \<in> corr_range \<Gamma>" .
qed

proposition prop_1_3_3_b:
  shows "corr_range (corr_inv \<Gamma>) = corr_dom \<Gamma>" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix a
  have "a \<in> ?LHS \<longleftrightarrow> (\<exists>b. (b, a) \<in> corr_graph (corr_inv \<Gamma>))" by (simp add: corr_range_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>b. a \<in> (corr_inv \<Gamma> b))" by (simp add: corr_graph_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>b. b \<in> \<Gamma> a)" by (simp add: corr_inv_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>b. (a, b) \<in> corr_graph \<Gamma>)" by (simp add: corr_graph_def)
  also have "\<dots> \<longleftrightarrow> a \<in> corr_dom \<Gamma>" by (simp add: corr_dom_def)
  finally show "a \<in> ?LHS \<longleftrightarrow> a \<in> ?RHS" .
qed

proposition prop_1_3_4:
  shows "corr_inv (corr_inv \<Gamma>) = \<Gamma>"
proof (intro ext)
  fix a
  show "corr_inv (corr_inv \<Gamma>) a = \<Gamma> a" (is "?LHS = ?RHS")
  proof (intro set_eqI)
    fix b
    have "b \<in> ?LHS \<longleftrightarrow> a \<in> corr_inv \<Gamma> b" by (simp add: corr_inv_def)
    also have "\<dots> \<longleftrightarrow> b \<in> \<Gamma> a" by (simp add: corr_inv_def)
    finally show "b \<in> ?LHS \<longleftrightarrow> b \<in> ?RHS" .
  qed
qed

definition as_corr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b set"
  where "as_corr f a = {f a}"

definition corr_functional :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "corr_functional \<Gamma> A B = (\<forall>a \<in> A. \<exists>!b \<in> B. b \<in> \<Gamma> a)"

section "Various Concepts on Functions"

proposition prop_1_4_1:
  assumes "P\<^sub>1 \<subseteq> P\<^sub>2"
  shows "f ` P\<^sub>1 \<subseteq> f ` P\<^sub>2"
proof (intro subsetI)
  fix b
  assume "b \<in> f ` P\<^sub>1"
  hence "\<exists>a \<in> P\<^sub>1. b = f a" by (simp add: image_def)
  then obtain a where "a \<in> P\<^sub>1" and "b = f a" ..
  from this(1) and assms have "a \<in> P\<^sub>2" by auto
  with \<open>b = f a\<close> have "\<exists>a \<in> P\<^sub>2. b = f a" by auto
  thus "b \<in> f ` P\<^sub>2" by (simp add: image_def)
qed

lemma
  shows "(\<exists>x. P x \<or> Q x) \<longleftrightarrow> (\<exists>x. P x) \<or> (\<exists>x. Q x)"
proof (intro iffI)
  assume "\<exists>x. P x \<or> Q x"
  then obtain x where "P x \<or> Q x" ..
  moreover {
    assume "P x"
    hence "\<exists>x. P x" ..
    hence "(\<exists>x. P x) \<or> (\<exists>x. Q x)" ..
  }
  moreover {
    assume "Q x"
    hence "\<exists>x. Q x" ..
    hence "(\<exists>x. P x) \<or> (\<exists>x. Q x)" ..
  }
  ultimately show "(\<exists>x. P x) \<or> (\<exists>x. Q x)" ..
next
  assume "(\<exists>x. P x) \<or> (\<exists>x. Q x)"
  moreover {
    assume "\<exists>x. P x"
    then obtain x where "P x" ..
    hence "P x \<or> Q x" ..
    hence "\<exists>x. P x \<or> Q x" ..
  }
  moreover {
    assume "\<exists>x. Q x"
    then obtain x where "Q x" ..
    hence "P x \<or> Q x" ..
    hence "\<exists>x. P x \<or> Q x" ..
  }
  ultimately show "\<exists>x. P x \<or> Q x" ..
qed

(* From now on, we can use @{thm ex_disj_distrib}. *)

proposition prop_1_4_2:
  shows "f ` (P\<^sub>1 \<union> P\<^sub>2) = f ` P\<^sub>1 \<union> f ` P\<^sub>2" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix b
  have "b \<in> ?LHS \<longleftrightarrow> (\<exists>a \<in> P\<^sub>1 \<union> P\<^sub>2. b = f a)" by (simp add: image_iff)
  also have "\<dots> \<longleftrightarrow> (\<exists>a. a \<in> P\<^sub>1 \<union> P\<^sub>2 \<and> b = f a)" by (simp only: Bex_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>a. a \<in> P\<^sub>1 \<and> b = f a \<or> a \<in> P\<^sub>2 \<and> b = f a)" by auto
  also have "\<dots> \<longleftrightarrow> (\<exists>a. a \<in> P\<^sub>1 \<and> b = f a) \<or> (\<exists>a. a \<in> P\<^sub>2 \<and> b = f a)" by (fact ex_disj_distrib)
  also have "\<dots> \<longleftrightarrow> (\<exists>a \<in> P\<^sub>1. b = f a) \<or> (\<exists>a \<in> P\<^sub>2. b = f a)" by (simp only: Bex_def)
  also have "\<dots> \<longleftrightarrow> b \<in> f ` P\<^sub>1 \<or> b \<in> f ` P\<^sub>2" by (simp only: image_iff)
  also have "\<dots> \<longleftrightarrow> b \<in> ?RHS" by simp
  finally show "b \<in> ?LHS \<longleftrightarrow> b \<in> ?RHS" .
qed

proposition prop_1_4_3:
  shows "f ` (P\<^sub>1 \<inter> P\<^sub>2) \<subseteq> f ` P\<^sub>1 \<inter> f ` P\<^sub>2"
proof (intro subsetI)
  fix b
  assume "b \<in> f ` (P\<^sub>1 \<inter> P\<^sub>2)"
  then obtain a where "a \<in> P\<^sub>1 \<inter> P\<^sub>2" and "b = f a" by auto
  from \<open>a \<in> P\<^sub>1 \<inter> P\<^sub>2\<close> have "a \<in> P\<^sub>1" ..
  with \<open>b = f a\<close> have "b \<in> f ` P\<^sub>1" by auto
  from \<open>a \<in> P\<^sub>1 \<inter> P\<^sub>2\<close> have "a \<in> P\<^sub>2" ..
  with \<open>b = f a\<close> have "b \<in> f ` P\<^sub>2" by auto
  with \<open>b \<in> f ` P\<^sub>1\<close> show "b \<in> f ` P\<^sub>1 \<inter> f ` P\<^sub>2" ..
qed

proposition prop_1_4_4:
  shows "f ` (A - P) \<supseteq> f ` A - f ` P"
proof (intro subsetI)
  fix b
  assume "b \<in> f ` A - f ` P"
  hence "b \<in> f ` A" and "b \<notin> f ` P" by auto
  from this(1) obtain a where "a \<in> A" and "b = f a" ..
  {
    assume "a \<in> P"
    with \<open>b = f a\<close> have "b \<in> f ` P" by auto
    with \<open>b \<notin> f ` P\<close> have "False" ..
  }
  hence "a \<notin> P" ..
  with \<open>a \<in> A\<close> have "a \<in> A - P" ..
  with \<open>b = f a\<close> show "b \<in> f ` (A - P)" ..
qed

proposition prop_1_4_1':
  assumes "Q\<^sub>1 \<subseteq> Q\<^sub>2"
  shows "f -` Q\<^sub>1 \<subseteq> f -` Q\<^sub>2"
proof (intro subsetI)
  fix a
  assume "a \<in> f -` Q\<^sub>1"
  then obtain b where "b \<in> Q\<^sub>1" and "b = f a" by simp
  from this(1) and assms have "b \<in> Q\<^sub>2" ..
  with \<open>b = f a\<close> show "a \<in> f -` Q\<^sub>2" by simp
qed

lemma
  shows "(\<exists>x \<in> A \<union> B. P x) \<longleftrightarrow> (\<exists>x \<in> A. P x) \<or> (\<exists>x \<in> B. P x)" (is "?LHS \<longleftrightarrow> ?RHS")
proof -
  have "?LHS \<longleftrightarrow> (\<exists>x. x \<in> A \<union> B \<and> P x)" by (fact Bex_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>x. x \<in> A \<and> P x \<or> x \<in> B \<and> P x)" by auto
  also have "\<dots> \<longleftrightarrow> (\<exists>x. x \<in> A \<and> P x) \<or> (\<exists>x. x \<in> B \<and> P x)" by (fact ex_disj_distrib)
  also have "\<dots> \<longleftrightarrow> ?RHS" by (simp only: Bex_def)
  finally show "?LHS \<longleftrightarrow> ?RHS" .
qed

(* From now on, we can use @{thm bex_Un}. *)

lemma
  shows "a \<in> f -` B \<longleftrightarrow> f a \<in> B"
proof -
  have "a \<in> f -` B \<longleftrightarrow> a \<in> {a. f a \<in> B}" by (simp only: vimage_def)
  also have "\<dots> \<longleftrightarrow> f a \<in> B" by (fact mem_Collect_eq)
  finally show "a \<in> f -` B \<longleftrightarrow> f a \<in> B" .
qed

(* From now on, we can use @{viamge_eq}. *)

proposition prop_1_4_2':
  shows "f -` (Q\<^sub>1 \<union> Q\<^sub>2) = f -` Q\<^sub>1 \<union> f -` Q\<^sub>2" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix a
  have "a \<in> ?LHS \<longleftrightarrow> f a \<in> Q\<^sub>1 \<union> Q\<^sub>2" by (fact vimage_eq)
  also have "\<dots> \<longleftrightarrow> f a \<in> Q\<^sub>1 \<or> f a \<in> Q\<^sub>2" by simp
  also have "\<dots> \<longleftrightarrow> a \<in> f -` Q\<^sub>1 \<or> a \<in> f -` Q\<^sub>2" by (simp only: vimage_eq)
  also have "\<dots> \<longleftrightarrow> a \<in> ?RHS" by simp
  finally show "a \<in> ?LHS \<longleftrightarrow> a \<in> ?RHS" .
qed

proposition prop_1_4_3':
  shows "f -` (Q\<^sub>1 \<inter> Q\<^sub>2) = f -` Q\<^sub>1 \<inter> f -` Q\<^sub>2" (is "?LHS = ?RHS")
proof (intro set_eqI)
  fix a
  have "a \<in> ?LHS \<longleftrightarrow> f a \<in> Q\<^sub>1 \<inter> Q\<^sub>2" by (fact vimage_eq)
  also have "\<dots> \<longleftrightarrow> f a \<in> Q\<^sub>1 \<and> f a \<in> Q\<^sub>2" by simp
  also have "\<dots> \<longleftrightarrow> a \<in> f -` Q\<^sub>1 \<and> a \<in> f -` Q\<^sub>2" by (simp only: vimage_eq)
  also have "\<dots> \<longleftrightarrow> a \<in> ?RHS" by simp
  finally show "a \<in> ?LHS \<longleftrightarrow> a \<in> ?RHS" .
qed

lemma
  assumes "a \<in> A"
  shows "f a \<in> f ` A"
proof -
  let ?b = "f a"
  from assms have "\<exists>a \<in> A. ?b = f a" by auto
  hence "?b \<in> {b. \<exists>a \<in> A. b = f a}" by (intro CollectI)
  thus "?b \<in> f ` A" by (unfold image_def)
qed

(* From now on, we can use @{thm imageI}. *)

lemma
  shows "f ` A \<subseteq> B \<longleftrightarrow> (\<forall>a \<in> A. f a \<in> B)"
proof (intro iffI)
  assume "f ` A \<subseteq> B"
  show "(\<forall>a \<in> A. f a \<in> B)"
  proof (intro ballI)
    fix a
    assume "a \<in> A"
    hence "f a \<in> f ` A" by (fact imageI)
    with \<open>f ` A \<subseteq> B\<close> show "f a \<in> B" ..
  qed
next
  assume "\<forall>a \<in> A. f a \<in> B"
  show "f ` A \<subseteq> B"
  proof (intro subsetI)
    fix b
    assume "b \<in> f ` A"
    then obtain a where "a \<in> A" and "b = f a" by auto
    from this(1) and \<open>\<forall>a \<in> A. f a \<in> B\<close> have "f a \<in> B" by simp
    with \<open>b = f a\<close> show "b \<in> B" by simp
  qed
qed

(* From now on, we can use @{thm image_subset_iff}. *)

lemma image_subsetD:
  assumes "f ` A \<subseteq> B" and "a \<in> A"
  shows "f a \<in> B"
proof -
  from assms(1) have "\<forall>a \<in> A. f a \<in> B" by (subst (asm) image_subset_iff)
  with assms(2) show "f a \<in> B" by simp
qed

(* Modified because functions in Isabelle/HOL are total while ones in mathematics are not *)
proposition prop_1_4_4':
  assumes "f ` A \<subseteq> B"
  shows "f -` (B - Q) \<inter> A = A - f -` Q" (is "?LHS = ?RHS")
proof (intro equalityI)
  show "?LHS \<subseteq> ?RHS"
  proof (intro subsetI)
    fix a
    assume "a \<in> ?LHS"
    hence *: "f a \<in> B - Q \<and> a \<in> A" by simp
    hence "a \<in> A" by simp
    moreover have "a \<notin> f -` Q"
    proof -
      from * have "f a \<notin> Q" by simp
      thus "?thesis" by simp
    qed
    ultimately show "a \<in> ?RHS" ..
  qed
next
  show "?RHS \<subseteq> ?LHS"
  proof (intro subsetI)
    fix a
    assume "a \<in> ?RHS"
    hence "a \<in> A" and "a \<notin> f -` Q" by auto
    from this(1) and assms have "f a \<in> B" by (elim image_subsetD)
    moreover from \<open>a \<notin> f -` Q\<close> have "f a \<notin> Q" by simp
    ultimately have "f a \<in> B - Q" ..
    hence "a \<in> f -` (B - Q)" by simp
    with \<open>a \<in> A\<close> show "a \<in> ?LHS" by simp
  qed
qed

proposition prop_1_4_5:
  shows "f -` (f ` P) \<supseteq> P"
proof (intro subsetI)
  fix a
  assume "a \<in> P"
  hence "f a \<in> f ` P" by (fact imageI)
  thus "a \<in> f -` (f ` P)" by (subst (asm) vimage_eq[THEN sym])
qed

proposition prop_1_4_5':
  shows "f ` (f -` Q) \<subseteq> Q"
proof (intro subsetI)
  fix b
  assume "b \<in> f ` (f -` Q)"
  then obtain a where "a \<in> f -` Q" and "b = f a" ..
  from this(1) have "f a \<in> Q" by (subst (asm) vimage_eq)
  thus "b \<in> Q" by (subst \<open>b = f a\<close>)
qed

lemma mem_corr_inv_iff:
  shows "a \<in> corr_inv \<Gamma> b \<longleftrightarrow> b \<in> \<Gamma> a"
proof -
  have "a \<in> corr_inv \<Gamma> b \<longleftrightarrow> a \<in> {a. b \<in> \<Gamma> a}" by (simp only: corr_inv_def)
  also have "\<dots> \<longleftrightarrow> b \<in> \<Gamma> a" by (fact mem_Collect_eq)
  finally show "?thesis" .
qed

lemma bex1D:
  assumes "\<exists>!x \<in> X. P x" and "a \<in> X" and "P a" and "b \<in> X" and "P b"
  shows "a = b"
proof -
  from assms(1) have "\<forall>x \<in> X. \<forall>y \<in> X. P x \<longrightarrow> P y \<longrightarrow> x = y" by auto
  with assms(2-5) show "a = b" by fast
qed

theorem th_1_4:
  assumes "f ` A \<subseteq> B"
  shows "corr_functional (corr_inv (as_corr f)) B A \<longleftrightarrow> bij_betw f A B"
proof (intro iffI)
  assume "corr_functional (corr_inv (as_corr f)) B A"
  hence *: "\<forall>b \<in> B. \<exists>!a \<in> A. a \<in> corr_inv (as_corr f) b" by (simp only: corr_functional_def)
  show "bij_betw f A B" find_theorems intro
  proof (intro bij_betw_imageI)
    show "inj_on f A"
    proof (intro inj_onI)
      fix a a'
      assume "a \<in> A" and "a' \<in> A" and "f a = f a'"
      from \<open>a \<in> A\<close> and assms have "f a \<in> B" by (elim image_subsetD)
      with * have "\<exists>!a'' \<in> A. a'' \<in> corr_inv (as_corr f) (f a)" by (elim bspec)
      hence "\<exists>!a'' \<in> A. f a \<in> (as_corr f) a''" by (simp only: mem_corr_inv_iff)
      hence "\<exists>!a'' \<in> A. f a \<in> {f a''}" by (simp only: as_corr_def)
      hence "\<exists>!a'' \<in> A. f a = f a''" by (simp only: singleton_iff)
      moreover have "f a = f a" ..
      moreover note \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and \<open>f a = f a'\<close>
      ultimately show "a = a'" by (elim bex1D)
    qed
  next
    show "f ` A = B"
    proof (intro equalityI)
      from assms show "f ` A \<subseteq> B" .
    next
      show "B \<subseteq> f ` A"
      proof (intro subsetI)
        fix b
        assume "b \<in> B"
        with * have "\<exists>!a \<in> A. a \<in> corr_inv (as_corr f) b" by (elim bspec)
        then obtain a'' where "a'' \<in> A" and "a'' \<in> corr_inv (as_corr f) b" by auto
        from this(2) have "b \<in> (as_corr f) a''" by (simp only: mem_corr_inv_iff)
        hence "b \<in> {f a''}" by (simp only: as_corr_def)
        hence "b = f a''" by (elim singletonD)
        with \<open>a'' \<in> A\<close> have "\<exists>a \<in> A. b = f a" ..
        thus "b \<in> f ` A" by auto
      qed
    qed
  qed
next
  assume "bij_betw f A B"
  hence "f ` A = B" by (fact bij_betw_imp_surj_on)
  {
    fix b
    assume "b \<in> B"
    with \<open>f ` A = B\<close> obtain a where "a \<in> A" and "b = f a" by auto
    from this(2) have "b \<in> as_corr f a" by (simp add: as_corr_def)
    hence "a \<in> corr_inv (as_corr f) b" unfolding corr_inv_def by simp
    with \<open>a \<in> A\<close> have "a \<in> A \<and> a \<in> corr_inv (as_corr f) b" ..
    moreover {
      fix a'
      assume **: "a' \<in> A \<and> a' \<in> corr_inv (as_corr f) b"
      hence "b \<in> as_corr f a'" by (simp only: mem_corr_inv_iff)
      hence "b = f a'" by (simp add: as_corr_def)
      with \<open>b = f a\<close> have "f a' = f a" by simp
      moreover from \<open>bij_betw f A B\<close> have "inj_on f A" by (fact bij_betw_imp_inj_on)
      moreover note \<open>a \<in> A\<close>
      moreover from ** have "a' \<in> A" ..
      ultimately have "a' = a" by (elim inj_onD)
    }
    ultimately have "\<exists>!a \<in> A. a \<in> (corr_inv (as_corr f)) b" by (intro ex1I)
  }
  hence "\<forall>b \<in> B. \<exists>!a \<in> A. a \<in> (corr_inv (as_corr f)) b" by (intro ballI)
  thus "corr_functional (corr_inv (as_corr f)) B A" by (fold corr_functional_def)
qed

theorem th_1_5_a:
  assumes "f ` A = B" and "g ` B = C"
  shows "(g \<circ> f) ` A = C"
proof (intro equalityI)
  {
    fix c
    assume "c \<in> (g \<circ> f) ` A"
    then obtain a where "a \<in> A" and "c = (g \<circ> f) a" by auto
    from this(2) have "c = g(f a)" by simp
    moreover from \<open>a \<in> A\<close> and assms(1) have "f a \<in> B" by auto
    moreover note assms(2)
    ultimately have "c \<in> C" by auto
  }
  thus "(g \<circ> f) ` A \<subseteq> C" ..
next
  {
    fix c
    assume "c \<in> C"
    with assms(2) obtain b where "b \<in> B" and "c = g b" by auto
    from this(1) and assms(1) obtain a where "a \<in> A" and "b = f a" by auto
    from \<open>c = g b\<close> and \<open>b = f a\<close> have "c = (g \<circ> f) a" by simp
    with \<open>a \<in> A\<close> have "c \<in> (g \<circ> f) ` A" by auto
  }
  thus "C \<subseteq> (g \<circ> f) ` A" ..
qed

theorem th_1_5_b:
  assumes "f ` A \<subseteq> B" and "inj_on f A" and "inj_on g B"
  shows "inj_on (g \<circ> f) A"
proof (intro inj_onI)
  fix a a'
  assume "a \<in> A" and "a' \<in> A" and "(g \<circ> f) a = (g \<circ> f) a'"
  from this(3) have "g(f a) = g(f a')" by simp
  moreover from \<open>a \<in> A\<close> and assms(1) have "f a \<in> B" by auto
  moreover from \<open>a' \<in> A\<close> and assms(1) have "f a' \<in> B" by auto
  moreover note assms(3)
  ultimately have "f a = f a'" by (elim inj_onD)
  with assms(2) and \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> show "a = a'"by (elim inj_onD)
qed

theorem th_1_5_c:
  assumes "bij_betw f A B" and "bij_betw g B C"
  shows "bij_betw (g \<circ> f) A C"
proof (intro bij_betw_imageI)
  from assms(1) have "f ` A = B" by (fact bij_betw_imp_surj_on)
  moreover from assms(2) have "g ` B = C" by (fact bij_betw_imp_surj_on)
  ultimately show "(g \<circ> f) ` A = C" by (fact th_1_5_a)
  from assms(1) have "inj_on f A" by (fact bij_betw_imp_inj_on)
  moreover from assms(2) have "inj_on g B" by (fact bij_betw_imp_inj_on)
  moreover from \<open>f ` A = B\<close> have "f ` A \<subseteq> B" by simp
  ultimately show "inj_on (g \<circ> f) A" by (intro th_1_5_b)
qed

theorem th_1_6_1:
  shows "(h \<circ> g) \<circ> f = h \<circ> (g \<circ> f)"
proof -
  {
    fix a
    have "((h \<circ> g) \<circ> f) a = (h \<circ> g) (f a)" by (simp only: comp_def)
    also have "\<dots> = h(g(f a))" by (simp only: comp_def)
    also have "\<dots> = h((g \<circ> f) a)" by (simp only: comp_def)
    also have "\<dots> = (h \<circ> (g \<circ> f)) a" by (simp only: comp_def)
    finally have "((h \<circ> g) \<circ> f) a = (h \<circ> (g \<circ> f)) a" .
  }
  thus "?thesis" ..
qed

theorem th_1_6_2_a:
  shows "f \<circ> id = f"
proof (intro ext)
  fix a
  have "(f \<circ> id) a = f(id a)" by (simp only: comp_def)
  also have "\<dots> = f a" by (simp only: id_def)
  finally show "(f \<circ> id) a = f a" .
qed

theorem th_1_6_2_b:
  shows "id \<circ> f = f"
proof (intro ext)
  fix a
  have "(id \<circ> f) a = id(f a)" by (simp only: comp_def)
  also have "\<dots> = f a" by (simp only: id_def)
  finally show "(id \<circ> f) a = f a" .
qed

theorem th_1_6_3_a:
  assumes "bij_betw f A B" and "a \<in> A"
  shows "((the_inv_into A f) \<circ> f) a = a"
proof -
  have "((the_inv_into A f) \<circ> f) a = (the_inv_into A f) (f a)" by (simp only: comp_def)
  also have "\<dots> = (THE a'. a' \<in> A \<and> f a' = f a)" by (simp only: the_inv_into_def)
  also have "\<dots> = a"
  proof (intro the1_equality)
    from assms(2) show "a \<in> A \<and> f a = f a" by simp
    moreover {
      fix a'
      assume *: "a' \<in> A \<and> f a' = f a"
      hence "f a' = f a" ..
      moreover from assms(1) have "inj_on f A" by (fact bij_betw_imp_inj_on)
      moreover note \<open>a \<in> A\<close>
      moreover from * have "a' \<in> A" ..
      ultimately have "a' = a" by (elim inj_onD)
    }
    ultimately show "\<exists>!a'. a' \<in> A \<and> f a' = f a" by (intro ex1I)
  qed
  finally show "?thesis" .
qed

theorem th_1_6_3_b:
  assumes "bij_betw f A B" and "b \<in> B"
  shows "(f \<circ> (the_inv_into A f)) b = b"
proof -
  from assms(1) have "f ` A = B" by (fact bij_betw_imp_surj_on)
  with assms(2) obtain a where "a \<in> A" and "b = f a" by auto
  from assms(1) and this(1) and th_1_6_3_a have "((the_inv_into A f) \<circ> f) a = a" by simp
  hence "f (((the_inv_into A f) \<circ> f) a) = f a" by simp
  hence "(f \<circ> (the_inv_into A f)) (f a) = f a" by simp
  with \<open>b = f a\<close> show "(f \<circ> (the_inv_into A f)) b = b" by simp
qed

proposition problem_1_4_3_a:
  assumes "inj_on f A" and "P \<subseteq> A"
  shows "(f -` (f ` P)) \<inter> A = P"
proof (intro equalityI)
  {
    fix p
    assume *: "p \<in> (f -` (f ` P)) \<inter> A"
    hence "f p \<in> f ` P" by auto
    then obtain p' where "p' \<in> P" and "f p = f p'" by auto
    from * have "p \<in> A" ..
    moreover from assms(2) and \<open>p' \<in> P\<close> have "p' \<in> A" ..
    moreover note assms(1)
    moreover note \<open>f p = f p'\<close>
    ultimately have "p = p'" by (elim inj_onD)
    with \<open>p' \<in> P\<close> have "p \<in> P" by simp
  }
  thus "(f -` (f ` P)) \<inter> A \<subseteq> P" ..
next
  {
    fix p
    assume "p \<in> P"
    hence "f p \<in> f ` P" by simp
    hence "p \<in> f -` (f ` P)" by auto
    moreover from \<open>p \<in> P\<close> and assms(2) have "p \<in> A" ..
    ultimately have "p \<in> (f -` (f ` P)) \<inter> A" ..
  }
  thus "P \<subseteq> (f -` (f ` P)) \<inter> A" ..
qed

proposition problem_1_4_3_b:
  assumes "Q \<subseteq> B" and "f ` A = B"
  shows "f ` (f -` Q) = Q"
proof (intro equalityI)
  show "f ` (f -` Q) \<subseteq> Q"
  proof (intro subsetI)
    fix b
    assume "b \<in> f ` (f -` Q)"
    hence "\<exists>a \<in> f -` Q. b = f a" by auto
    then obtain a where "a \<in> f -` Q" and "b = f a" ..
    from this(1) have "f a \<in> Q" by auto
    with \<open>b = f a\<close> show "b \<in> Q" by auto
  qed
next
  show "Q \<subseteq> f ` (f -` Q)"
  proof (intro subsetI)
    fix b
    assume "b \<in> Q"
    with assms(1) have "b \<in> B" ..
    with assms(2) have "\<exists>a \<in> A. b = f a" by auto
    then obtain a where "a \<in> A" and "b = f a" by auto
    from \<open>b = f a\<close> and \<open>b \<in> Q\<close> have "f a \<in> Q" by simp
    hence "a \<in> f -` Q" by auto
    with \<open>b = f a\<close> have "\<exists>a \<in> f -` Q. b = f a" by auto
    thus "b \<in> f ` (f -` Q)" by auto
  qed
qed

proposition problem_1_4_4:
  assumes "inj_on f A" and "P\<^sub>1 \<subseteq> A" and "P\<^sub>2 \<subseteq> A"
  shows "f ` (P\<^sub>1 \<inter> P\<^sub>2) = f ` P\<^sub>1 \<inter> f ` P\<^sub>2"
proof (intro equalityI)
  show "f ` (P\<^sub>1 \<inter> P\<^sub>2) \<subseteq> f ` P\<^sub>1 \<inter> f ` P\<^sub>2" by (fact prop_1_4_3)
next
  show "f ` P\<^sub>1 \<inter> f ` P\<^sub>2 \<subseteq> f ` (P\<^sub>1 \<inter> P\<^sub>2)"
  proof (intro subsetI)
    fix b
    assume "b \<in> f ` P\<^sub>1 \<inter> f ` P\<^sub>2"
    hence "b \<in> f ` P\<^sub>1" and "b \<in> f ` P\<^sub>2" by auto
    from \<open>b \<in> f ` P\<^sub>1\<close> have "\<exists>a \<in> P\<^sub>1. b = f a" by auto
    then obtain a where "a \<in> P\<^sub>1" and "b = f a" by auto
    from \<open>b \<in> f ` P\<^sub>2\<close> have "\<exists>a \<in> P\<^sub>2. b = f a" by auto
    then obtain a' where "a' \<in> P\<^sub>2" and "b = f a'" by auto
    from \<open>b = f a\<close> and \<open>b = f a'\<close> have "f a = f a'" by simp
    moreover from \<open>a \<in> P\<^sub>1\<close> and assms(2) have "a \<in> A" ..
    moreover from \<open>a' \<in> P\<^sub>2\<close> and assms(3) have "a' \<in> A" ..
    moreover note assms(1)
    ultimately have "a = a'" by (elim inj_onD)
    with \<open>a' \<in> P\<^sub>2\<close> have "a \<in> P\<^sub>2" by simp
    with \<open>a \<in> P\<^sub>1\<close> and \<open>b = f a\<close> have "\<exists>a \<in> P\<^sub>1 \<inter> P\<^sub>2. b = f a" by auto
    thus "b \<in> f ` (P\<^sub>1 \<inter> P\<^sub>2)" by auto
  qed
qed

proposition problem_1_4_5:
  assumes "P \<subseteq> A" and "inj_on f A"
  shows "f ` (A - P) = f ` A - f ` P"
proof (intro equalityI)
  show "f ` (A - P) \<subseteq> f ` A - f ` P"
  proof (intro subsetI)
    fix b
    assume "b \<in> f ` (A - P)"
    then obtain a where "a \<in> A - P" and "b = f a" by auto
    from \<open>a \<in> A - P\<close> have "a \<in> A" and "a \<notin> P" by auto
    from \<open>b = f a\<close> and \<open>a \<in> A\<close> have "b \<in> f ` A" by auto
    moreover have "b \<notin> f ` P"
    proof (intro notI)
      assume "b \<in> f ` P"
      then obtain a' where "a' \<in> P" and "b = f a'" by auto
      from \<open>b = f a'\<close> and \<open>b = f a\<close> have "f a = f a'" by simp
      moreover from \<open>a' \<in> P\<close> assms(1) have "a' \<in> A" ..
      moreover note \<open>a \<in> A\<close>
      moreover note assms(2)
      ultimately have "a = a'" by (elim inj_onD)
      with \<open>a \<notin> P\<close> and \<open>a' \<in> P\<close> show "False" by simp
    qed
    ultimately show "b \<in> f ` A - f ` P" ..
  qed
next
  show "f ` A - f ` P \<subseteq> f ` (A - P)" by (fact prop_1_4_4)
qed

proposition problem_1_4_8:
  assumes "bij_betw f A B" and "bij_betw g B C" and "c \<in> C"
  shows "the_inv_into A (g \<circ> f) c = ((the_inv_into A f) \<circ> (the_inv_into B g)) c" (is "?LHS = ?RHS")
proof -
  from assms(2) have "g ` B = C" by (fact bij_betw_imp_surj_on)
  with assms(3) obtain b where "b \<in> B" and "c = g b" by auto
  from assms(1) have "f ` A = B" by (fact bij_betw_imp_surj_on)
  with \<open>b \<in> B\<close> obtain a where "a \<in> A" and "b = f a" by auto
  have "the_inv_into A (g \<circ> f) c = (THE a. a \<in> A \<and> (g \<circ> f) a = c)" by (simp add: the_inv_into_def)
  also have "\<dots> = a"
  proof (intro the_equality)
    from \<open>c = g b\<close> and \<open>b = f a\<close> have "c = (g \<circ> f) a" by simp
    with \<open>a \<in> A\<close> show "a \<in> A \<and> (g \<circ> f) a = c" by simp
    fix a'
    assume *: "a' \<in> A \<and> (g \<circ> f) a' = c"
    hence "(g \<circ> f) a' = c" ..
    with \<open>c = (g \<circ> f) a\<close> have "(g \<circ> f) a = (g \<circ> f) a'" by simp
    moreover have "inj_on (g \<circ> f) A"
    proof (intro th_1_5_b)
      from assms(1) have "f ` A = B" by (fact bij_betw_imp_surj_on)
      thus "f ` A \<subseteq> B" by simp
    next
      from assms(1) show "inj_on f A" by (fact bij_betw_imp_inj_on)
    next
      from assms(2) show "inj_on g B" by (fact bij_betw_imp_inj_on)
    qed
    moreover note \<open>a \<in> A\<close>
    moreover from * have "a' \<in> A" ..
    ultimately have "a = a'" by (elim inj_onD)
    thus "a' = a" ..
  qed
  finally have *: "the_inv_into A (g \<circ> f) c = a" .
  have "((the_inv_into A f) \<circ> (the_inv_into B g)) c = (the_inv_into A f) ((the_inv_into B g) c)"
    by (simp only: comp_def)
  also have "\<dots> = (the_inv_into A f) (THE b. b \<in> B \<and> g b = c)" by (simp add: the_inv_into_def)
  also have "\<dots> = (the_inv_into A f) b"
  proof -
    from \<open>b \<in> B\<close> and \<open>c = g b\<close> have **: "b \<in> B \<and> g b = c" by simp
    moreover {
      fix b'
      assume ***: "b' \<in> B \<and> g b' = c"
      moreover from ** have "g b = c" ..
      ultimately have "g b' = g b" by simp
      moreover from assms(2) have "inj_on g B" by (fact bij_betw_imp_inj_on)
      moreover note \<open>b \<in> B\<close>
      moreover from *** have "b' \<in> B" ..
      ultimately have "b' = b" by (elim inj_onD)
    }
    ultimately have "(THE b. b \<in> B \<and> g b = c) = b" by (intro the_equality)
    thus "?thesis" by simp
  qed
  also have "\<dots> = (THE a. a \<in> A \<and> f a = b)" by (simp add: the_inv_into_def)
  also have "\<dots> = a"
  proof (intro the_equality)
    from \<open>a \<in> A\<close> and \<open>b = f a\<close> show "a \<in> A \<and> f a = b" by simp
  next
    fix a'
    assume ****: "a' \<in> A \<and> f a' = b"
    with \<open>b = f a\<close> have "f a' = f a" by simp
    moreover from assms(1) have "inj_on f A" by (fact bij_betw_imp_inj_on)
    moreover note \<open>a \<in> A\<close>
    moreover from **** have "a' \<in> A" ..
    ultimately show "a' = a" by (elim inj_onD)
  qed
  finally have "?RHS = a" .
  with * show "?LHS = ?RHS" by simp
qed

proposition problem_1_4_9_a:
  (*assumes "P \<subseteq> A"*)
  shows "(g \<circ> f) ` P = g ` (f ` P)"
proof (intro equalityI)
  {
    fix c
    assume "c \<in> (g \<circ> f) ` P"
    then obtain a where "a \<in> P" and "c = (g \<circ> f) a" by auto
    from this(2) have "c = g (f a)" by simp
    moreover from \<open>a \<in> P\<close> have "f a \<in> f ` P" by simp
    ultimately have "c \<in> g ` (f ` P)" by auto
  }
  thus "(g \<circ> f) ` P \<subseteq> g ` (f ` P)" by (intro subsetI)
next
  {
    fix c
    assume "c \<in> g ` (f ` P)"
    then obtain b where "b \<in> f ` P" and "c = g b" by auto
    from \<open>b \<in> f ` P\<close> obtain a where "a \<in> P" and "b = f a" by auto
    from \<open>c = g b\<close> and \<open>b = f a\<close> have "c = (g \<circ> f) a" by simp
    with \<open>a \<in> P\<close> have "c \<in> (g \<circ> f) ` P" by auto
  }
  thus "g ` (f ` P) \<subseteq> (g \<circ> f) ` P" by (intro subsetI)
qed

proposition problem_1_4_9_b:
  (*assumes "R \<subseteq> C"*)
  shows "(g \<circ> f) -` R = f -` (g -` R)"
proof (intro equalityI)
  {
    fix a
    assume "a \<in> (g \<circ> f) -` R"
    then obtain c where "c \<in> R" and "c = (g \<circ> f) a" by auto
    from \<open>c = (g \<circ> f) a\<close> have "c = g (f a)" by simp
    with \<open>c \<in> R\<close> have "f a \<in> g -` R" by auto
    hence "a \<in> f -` (g -` R)" by auto
  }
  thus "(g \<circ> f) -` R \<subseteq> f -` (g -` R)" by (intro subsetI)
next
  {
    fix a
    assume "a \<in> f -` (g -` R)"
    then obtain b where "b \<in> g -` R" and "b = f a" by auto
    from \<open>b \<in> g -` R\<close> obtain c where "c \<in> R" and "c = g b" by auto
    with \<open>b = f a\<close> have "c = (g \<circ> f) a" by simp
    with \<open>c \<in> R\<close> have "a \<in> (g \<circ> f) -` R" by auto
  }
  thus "f -` (g -` R) \<subseteq> (g \<circ> f) -` R" by (intro subsetI)
qed

proposition problem_1_4_10_a:
  assumes "f ` A \<subseteq> B" and "g ` B \<subseteq> C" and "(g \<circ> f) ` A = C"
  shows "g ` B = C"
proof (intro equalityI)
  show "g ` B \<subseteq> C" by (fact assms(2))
next
  {
    fix c
    assume "c \<in> C"
    with assms(3) obtain a where "a \<in> A" and "c = (g \<circ> f) a" by auto
    from \<open>a \<in> A\<close> and assms(1) have "f a \<in> B" by auto
    from \<open>c = (g \<circ> f) a\<close> have "c = g (f a)" by auto
    with \<open>f a \<in> B\<close> have "c \<in> g ` B" by auto
  }
  thus "C \<subseteq> g ` B" by (intro subsetI)
qed

proposition problem_1_4_10_b:
  assumes "inj_on (g \<circ> f) A"
  shows "inj_on f A"
proof (intro inj_onI)
  fix a a'
  assume "a \<in> A" and "a' \<in> A" and "f a = f a'"
  from this(3) have "g (f a) = g (f a')" by simp
  hence "(g \<circ> f) a = (g \<circ> f) a'" by simp
  with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and assms show "a = a'" by (elim inj_onD)
qed

proposition problem_1_4_11:
  assumes "f ` A = B" and "\<And>a. a \<in> A \<Longrightarrow> (g \<circ> f) a = (g' \<circ> f) a" and "b \<in> B"
  shows "g b = g' b"
proof -
  from assms(1) and assms(3) obtain a where "a \<in> A" and "b = f a" by auto
  from \<open>a \<in> A\<close> and assms(2) have "(g \<circ> f) a = (g' \<circ> f) a" by simp
  with \<open>b = f a\<close> show "g b = g' b" by auto
qed

proposition problem_1_4_12:
  assumes "f ` A \<subseteq> B"
    and "f' ` A \<subseteq> B"
    and "inj_on g B"
    and "\<And>a. a \<in> A \<Longrightarrow> (g \<circ> f) a = (g \<circ> f') a"
    and "a \<in> A"
  shows "f a = f' a"
proof -
  from assms(4,5) have "g (f a) = g (f' a)" by simp
  moreover from assms(1) and assms(5) have "f a \<in> B" by auto
  moreover from assms(2) and assms(5) have "f' a \<in> B" by auto
  moreover note assms(3)
  ultimately show "f a = f' a" by (elim inj_onD)
qed

proposition problem_1_4_13_a:
  assumes "f ` A \<subseteq> B" and "g ` B \<subseteq> C" and "(g \<circ> f) ` A = C" and "inj_on g B"
  shows "f ` A = B"
proof (intro equalityI)
  show "f ` A \<subseteq> B" by (fact assms(1))
next
  {
    fix b
    assume "b \<in> B"
    with assms(2) have "g b \<in> C" by auto
    with assms(3) obtain a where "a \<in> A" and "g b = (g \<circ> f) a" by auto
    from this(2) have "g b = g (f a)" by simp
    moreover note \<open>b \<in> B\<close>
    moreover from assms(1) and \<open>a \<in> A\<close> have "f a \<in> B" by auto
    moreover note assms(4)
    ultimately have "b = f a" by (elim inj_onD)
    with \<open>a \<in> A\<close> have "b \<in> f ` A" by auto
  }
  thus "B \<subseteq> f ` A" by (intro subsetI)
qed

proposition problem_1_4_13_b:
  assumes "inj_on (g \<circ> f) A" and "f ` A = B"
  shows "inj_on g B"
proof (intro inj_onI)
  fix b b'
  assume "b \<in> B" and "b' \<in> B" and "g b = g b'"
  from this(1) and assms(2) obtain a where "a \<in> A" and "b = f a" by auto
  from \<open>b' \<in> B\<close> and assms(2) obtain a' where "a' \<in> A" and "b' = f a'" by auto
  from \<open>g b = g b'\<close> and \<open>b = f a\<close> and \<open>b' = f a'\<close> have "(g \<circ> f) a = (g \<circ> f) a'" by simp
  with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and assms(1) have "a = a'" by (elim inj_onD)
  with \<open>b = f a\<close> and \<open>b' = f a'\<close> show "b = b'" by simp
qed

proposition problem_1_4_14:
  assumes "f ` A \<subseteq> B" and "g ` B \<subseteq> A" and "g' ` B \<subseteq> A"
    and "\<And>a. a \<in> A \<Longrightarrow> (g \<circ> f) a = a" and "\<And>b. b \<in> B \<Longrightarrow> (f \<circ> g') b = b" and "b \<in> B"
  shows "bij_betw f A B" and "g b = g' b" and "g b = the_inv_into A f b"
proof -
  have "inj_on f A"
  proof (intro inj_onI)
    fix a a'
    assume "a \<in> A" and "a' \<in> A" and "f a = f a'"
    from this(3) have "(g \<circ> f) a = (g \<circ> f) a'" by simp
    moreover from assms(4) and \<open>a \<in> A\<close> have "(g \<circ> f) a = a" by simp
    moreover from assms(4) and \<open>a' \<in> A\<close> have "(g \<circ> f) a' = a'" by simp
    ultimately show "a = a'" by simp
  qed
  moreover have "f ` A = B"
  proof (intro equalityI)
    show "f ` A \<subseteq> B" by (fact assms(1))
  next
    {
      fix b'
      assume "b' \<in> B"
      with assms(5) have "(f \<circ> g') b' = b'" by simp
      hence "b' = f (g' b')" by simp
      moreover from \<open>b' \<in> B\<close> and assms(3) have "g' b' \<in> A" by auto
      ultimately have "b' \<in> f ` A" by auto
    }
    thus "B \<subseteq> f ` A" by (intro subsetI)
  qed
  ultimately show "bij_betw f A B" by (intro bij_betw_imageI)
  have "g ` B \<subseteq> A" by (fact assms(2))
  moreover note assms(3)
  moreover note \<open>inj_on f A\<close>
  moreover have "(f \<circ> g) b = (f \<circ> g') b" if "b \<in> B" for b
  proof -
    from that have "(f \<circ> g') b = b" by (fact assms(5))
    from \<open>f ` A = B\<close> and \<open>b \<in> B\<close> obtain a where "a \<in> A" and "b = f a" by auto
    from \<open>a \<in> A\<close> and assms(4) have "(g \<circ> f) a = a" by simp
    with \<open>b = f a\<close> have "g b = a" by simp
    with \<open>b = f a\<close> have "(f \<circ> g) b = b" by simp
    with \<open>(f \<circ> g') b = b\<close> show "?thesis" by simp
  qed
  moreover note assms(6)
  ultimately show "g b = g' b" by (intro problem_1_4_12[where f = g])
  show "g b = the_inv_into A f b"
  proof (intro the_inv_into_f_eq[THEN sym])
    show "inj_on f A" by (fact \<open>inj_on f A\<close>)
    show "f (g b) = b"
    proof -
      from \<open>g b = g' b\<close> have "f (g b) = (f \<circ> g') b" by simp
      also from \<open>b \<in> B\<close> have "\<dots> = b" by (fact assms(5))
      finally show "?thesis" .
    qed
    from \<open>b \<in> B\<close> and assms(2) show "g b \<in> A" by auto
  qed
qed

definition \<chi> :: "'a set \<Rightarrow> 'a \<Rightarrow> int"
  where "\<chi> A a = (if a \<in> A then 1 else 0)"

lemma chi_0_1:
  shows "\<chi> A a \<in> {0, 1}"
  by (simp add: \<chi>_def)

lemma zero_leq_chi:
  shows "0 \<le> \<chi> A a"
  by (simp add: \<chi>_def)

lemma chi_leq_1:
  shows "\<chi> A a \<le> 1"
  by (simp add: \<chi>_def)

lemma chi_eq_0I:
  assumes "a \<notin> A"
  shows "\<chi> A a = 0"
  using assms \<chi>_def by metis

lemma chi_eq_1I:
  assumes "a \<in> A"
  shows "\<chi> A a = 1"
  using assms \<chi>_def by metis

lemma chi_eq_0D:
  assumes "\<chi> A a = 0"
  shows "a \<notin> A"
  using assms \<chi>_def zero_neq_one by metis

lemma chi_eq_1D:
  assumes "\<chi> A a = 1"
  shows "a \<in> A"
  using assms \<chi>_def one_neq_zero by metis

lemma one_leq_chi_imp_chi_eq_1:
  assumes "1 \<le> \<chi> A a"
  shows "\<chi> A a = 1"
  using assms chi_0_1 by force

proposition problem_1_4_15:
  assumes "A \<subseteq> X" and "B \<subseteq> X"
  shows "(\<forall>x \<in> X. \<chi> A x \<le> \<chi> B x) \<longleftrightarrow> A \<subseteq> B"
proof (intro iffI)
  assume "\<forall>x \<in> X. \<chi> A x \<le> \<chi> B x"
  {
    fix a
    assume "a \<in> A"
    with assms(1) and \<open>\<forall>x \<in> X. \<chi> A x \<le> \<chi> B x\<close> have "\<chi> A a \<le> \<chi> B a" by auto
    moreover from \<open>a \<in> A\<close> and \<chi>_def have "\<chi> A a = 1" by metis
    ultimately have "1 \<le> \<chi> B a" by simp
    hence "\<chi> B a = 1" by (fact one_leq_chi_imp_chi_eq_1)
    hence "a \<in> B" by (fact chi_eq_1D)
  }
  thus "A \<subseteq> B" by (intro subsetI)
next
  assume "A \<subseteq> B"
  {
    fix x
    assume "x \<in> X"
    {
      assume "x \<in> A"
      with \<open>A \<subseteq> B\<close> have "x \<in> B" by auto
      hence "\<chi> B x = 1" by (fact chi_eq_1I)
      with chi_leq_1 have "\<chi> A x \<le> \<chi> B x" by metis
    }
    moreover {
      assume "x \<notin> A"
      hence "\<chi> A x = 0" by (fact chi_eq_0I)
      with zero_leq_chi have "\<chi> A x \<le> \<chi> B x" by simp
    }
    ultimately have "\<chi> A x \<le> \<chi> B x" by auto
  }
  thus "\<forall>x \<in> X. \<chi> A x \<le> \<chi> B x" by auto
qed

proposition problem_1_4_15_a:
  shows "\<chi> (A \<inter> B) a = \<chi> A a * \<chi> B a"
proof -
  consider (a) "a \<notin> A" | (b) "a \<notin> B" | (c) "a \<in> A \<inter> B" by blast
  thus "?thesis"
  proof cases
    case a
    from a have "a \<notin> A \<inter> B" by auto
    hence "\<chi> (A \<inter> B) a = 0" by (fact chi_eq_0I)
    moreover have "\<chi> A a * \<chi> B a = 0"
    proof -
      from a have "\<chi> A a = 0" by (fact chi_eq_0I)
      thus "?thesis" by simp
    qed
    ultimately show "?thesis" by simp
  next
    case b
    from b have "a \<notin> A \<inter> B" by auto
    hence "\<chi> (A \<inter> B) a = 0" by (fact chi_eq_0I)
    moreover have "\<chi> A a * \<chi> B a = 0"
    proof -
      from b have "\<chi> B a = 0" by (fact chi_eq_0I)
      thus "?thesis" by simp
    qed
    ultimately show "?thesis" by simp
  next
    case c
    hence "\<chi> (A \<inter> B) a = 1" by (fact chi_eq_1I)
    moreover have "\<chi> A a * \<chi> B a = 1"
    proof -
      from c have "a \<in> A" by simp
      hence "\<chi> A a = 1" by (fact chi_eq_1I)
      moreover have "\<chi> B a = 1"
      proof (intro chi_eq_1I)
        from c show "a \<in> B" ..
      qed
      ultimately show "?thesis" by simp
    qed
    ultimately show "?thesis" by simp
  qed
qed

proposition problem_1_4_15_b:
  shows "\<chi> (A \<union> B) a = \<chi> A a + \<chi> B a - \<chi> (A \<inter> B) a"
proof -
  consider (a) "a \<in> A \<union> B" | (b) "a \<notin> A \<union> B" by auto
  thus "?thesis"
  proof cases
    case a
    from a have "\<chi> (A \<union> B) a = 1" by (fact chi_eq_1I)
    consider (aa) "a \<in> A" and "a \<in> B" | (bb) "a \<in> A" and "a \<notin> B"
      | (cc) "a \<notin> A" and "a \<in> B" | (dd) "a \<notin> A" and "a \<notin> B" by auto
    hence "\<chi> A a + \<chi> B a - \<chi> (A \<inter> B) a = 1"
    proof cases
      case aa
      thus "?thesis" by (simp add: chi_eq_1I)
    next
      case bb
      thus "?thesis" by (simp add: chi_eq_0I chi_eq_1I)
    next
      case cc
      thus "?thesis" by (simp add: chi_eq_0I chi_eq_1I)
    next
      case dd
      with a show "?thesis" by simp
    qed
    with \<open>\<chi> (A \<union> B) a = 1\<close> show "?thesis" by simp
  next
    case b
    hence "\<chi> (A \<union> B) a = 0" by (fact chi_eq_0I)
    moreover have "\<chi> A a + \<chi> B a - \<chi> (A \<inter> B) a = 0"
    proof -
      from b have "a \<notin> A" and "a \<notin> B" by auto
      from \<open>a \<notin> A\<close> have "\<chi> A a = 0" by (fact chi_eq_0I)
      moreover from \<open>a \<notin> B\<close> have "\<chi> B a = 0" by (fact chi_eq_0I)
      moreover have "\<chi> (A \<inter> B) a = 0"
      proof -
        from \<open>a \<notin> A\<close> have "a \<notin> A \<inter> B" by simp
        thus "?thesis" by (fact chi_eq_0I)
      qed
      ultimately show "?thesis" by simp
    qed
    ultimately show "?thesis" by simp
  qed
qed

proposition problem_1_4_15_c:
  assumes (*"A \<subseteq> X" and*) "x \<in> X"
  shows "\<chi> (X - A) x = 1 - \<chi> A x"
proof -
  consider (a) "x \<in> A" | (b) "x \<notin> A" by auto
  thus "?thesis"
  proof cases
    case a
    from a and assms have "x \<notin> X - A" by auto
    hence "\<chi> (X - A) x = 0" by (fact chi_eq_0I)
    moreover from a have "1 - \<chi> A x = 0" by (simp add: chi_eq_1I)
    ultimately show "?thesis" by simp
  next
    case b
    with assms have "x \<in> X - A" by auto
    hence "\<chi> (X - A) x = 1" by (fact chi_eq_1I)
    moreover from b have "1 - \<chi> A x = 1" by (simp add: chi_eq_0I)
    ultimately show "?thesis" by simp
  qed
qed

lemma
  shows "-A = UNIV - A"
proof (intro set_eqI)
  fix x
  have "x \<in> -A \<longleftrightarrow> x \<in> UNIV \<and> x \<notin> A" by simp
  also have "\<dots> \<longleftrightarrow> x \<in> UNIV - A" by auto
  finally show "x \<in> -A \<longleftrightarrow> x \<in> UNIV - A" .
qed

(* From now on, we can use @{thm Compl_eq_Diff_UNIV}. *)

lemma
  shows "A - B = A \<inter> -B"
proof (intro set_eqI)
  fix x
  have "x \<in> A - B \<longleftrightarrow> x \<in> A \<and> x \<notin> B" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> A \<and> x \<in> -B" by simp
  also have "\<dots> \<longleftrightarrow> x \<in> A \<inter> -B" by auto
  finally show "x \<in> A - B \<longleftrightarrow> x \<in> A \<inter> -B" .
qed

(* From now on, we can use @{thm Diff_eq}. *)

proposition problem_1_4_15_c':
  shows "\<chi> (-A) x = 1 - \<chi> A x"
proof -
  consider (a) "x \<in> A" | (b) "x \<notin> A" by auto
  thus "?thesis"
  proof cases
    case a
    hence "x \<notin> -A" by simp
    hence "\<chi> (-A) x = 0" by (fact chi_eq_0I)
    moreover from a have "1 - \<chi> A x = 0" by (simp add: chi_eq_1I)
    ultimately show "?thesis" by simp
  next
    case b
    hence "x \<in> -A" by simp
    hence "\<chi> (-A) x = 1" by (fact chi_eq_1I)
    moreover from b have "1 - \<chi> A x = 1" by (simp add: chi_eq_0I)
    ultimately show "?thesis" by simp
  qed
qed

proposition problem_1_4_15_d:
  shows "\<chi> (A - B) x = \<chi> A x * (1 - (\<chi> B x))"
proof -
  have "\<chi> (A - B) x = \<chi> (A \<inter> -B) x" by (simp add: Diff_eq)
  also have "\<dots> = \<chi> A x * \<chi> (-B) x" by (fact problem_1_4_15_a)
  also have "\<dots> = \<chi> A x * (1 - \<chi> B x)" by (simp add: problem_1_4_15_c')
  finally show "?thesis" .
qed

proposition problem_1_4_15_e:
  shows "\<chi> (sym_diff A B) x = \<bar>\<chi> A x - \<chi> B x\<bar>"
proof -
  consider (a) "x \<in> A" and "x \<in> B"
    | (b) "x \<in> A" and "x \<notin> B"
    | (c) "x \<notin> A" and "x \<in> B"
    | (d) "x \<notin> A" and "x \<notin> B"
    by auto
  thus "?thesis"
  proof cases
    case a
    hence "x \<notin> sym_diff A B" by (simp add: sym_diff_def)
    hence "\<chi> (sym_diff A B) x = 0" by (fact chi_eq_0I)
    moreover from a have "\<bar>\<chi> A x - \<chi> B x\<bar> = 0" by (simp add: chi_eq_1I)
    ultimately show "?thesis" by simp
  next
    case b
    hence "x \<in> sym_diff A B" by (simp add: sym_diff_def)
    hence "\<chi> (sym_diff A B) x = 1" by (fact chi_eq_1I)
    moreover from b have "\<bar>\<chi> A x - \<chi> B x\<bar> = 1" by (simp add: chi_eq_0I chi_eq_1I)
    ultimately show "?thesis" by simp
  next
    case c
    hence "x \<in> sym_diff A B" by (simp add: sym_diff_def)
    hence "\<chi> (sym_diff A B) x = 1" by (fact chi_eq_1I)
    moreover from c have "\<bar>\<chi> A x - \<chi> B x\<bar> = 1" by (simp add: chi_eq_0I chi_eq_1I)
    ultimately show "?thesis" by simp
  next
    case d
    hence "x \<notin> sym_diff A B" by (simp add: sym_diff_def)
    hence "\<chi> (sym_diff A B) x = 0" by (fact chi_eq_0I)
    moreover from d have "\<bar>\<chi> A x - \<chi> B x\<bar> = 0" by (simp add: chi_eq_0I)
    ultimately show "?thesis" by simp
  qed
qed

(* TODO: problem_1_4_16 *)
(* TODO: problem_1_4_17 *)
(* TODO: problem_1_4_18 *)
(* TODO: problem_1_4_19 *)

section "Indexed Families, General Products"

end
