theory Section_1_2
  imports Main
    "Section_1_1"
begin

section \<open>Operations among Sets\<close>

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

proposition prop_1_2_1:
  shows "A \<union> B = {x. x \<in> A \<or> x \<in> B}"
  by (fact Un_def)

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

end
