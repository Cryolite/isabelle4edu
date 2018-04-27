theory Section_1_1
  imports Main
begin

section {* Notion of Sets *}

subsection {* A) Sets and Elements *}

subsection {* B) Notation of Sets *}

text {*
  In the proofs of the propositions in this subsection, I pretend to be a novice learner of set
  theory and even how to prove a proposition. I begin with a core set of inference rules of natural
  deduction, i.e.,

    - @{thm conjI} as @{text \<and>}-I,
    - @{thm conjunct1} as @{text \<and>}-E1 and @{thm conjunct2} as @{text \<and>}-E2,
    - @{thm disjI1} as @{text \<or>}-I1 and @{thm disjI2} as @{text \<or>}-I2,
    - @{thm disjE} as @{text \<or>}-E,
    - @{thm impI} as @{text \<longrightarrow>}-I,
    - @{thm mp} as @{text \<longrightarrow>}-E,
    - @{thm notI} as @{text \<not>}-I,
    - @{thm notE} as @{text \<not>}-E,
    - @{thm ccontr} and @{thm notnotD} as equivalences of the law of exclusive middle,
    - @{thm allI} as @{text \<forall>}-I,
    - @{thm spec} as @{text \<forall>}-E,
    - @{thm exI} as @{text \<exists>}-I, and
    - obtain as the improved usage of @{text \<exists>}-E.

  In addition, I use some method (subst, subst (asm), unfold, and fold) and some facts (@{thm refl}
  and @{thm arg_cong}) to rewrite (simplify) terms.
*}

lemma
  assumes "P \<Longrightarrow> Q" and
    "Q \<Longrightarrow> P"
  shows "P \<longleftrightarrow> Q"
proof -
  from assms(1) have "P \<longrightarrow> Q" ..
  moreover from assms(2) have "Q \<longrightarrow> P" ..
  ultimately have "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P)" by (fact conjI)
  thus "?thesis" by (fold iff_conv_conj_imp)
qed

text {* From now on, @{thm iffI} can be used. *}

lemma
  assumes "\<And>x. x \<in> A \<Longrightarrow> x \<in> B"
  shows "A \<subseteq> B"
proof -
  {
    fix x
    {
      assume "x \<in> A"
      hence "x \<in> B" by (fact assms)
    }
    hence "x \<in> A \<longrightarrow> x \<in> B" by (fact impI)
  }
  hence "\<forall>x. x \<in> A \<longrightarrow> x \<in> B" by (fact allI)
  thus "?thesis" by (fold subset_iff)
qed

text {* From now on, @{thm subsetI} can be used. *}

lemma
  assumes "A \<subseteq> B" and
    "x \<in> A"
  shows "x \<in> B"
proof -
  from assms(1) have "\<forall>x. x \<in> A \<longrightarrow> x \<in> B" by (subst (asm) subset_iff)
  hence "x \<in> A \<longrightarrow> x \<in> B" by (fact spec)
  with assms(2) show "x \<in> B" by (elim mp)
qed

text {* From now on, @{thm subsetD} can be used. *}

lemma
  assumes "P \<longleftrightarrow> Q" and
    "P"
  shows "Q"
proof -
  from assms(1) have "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P)" by (subst (asm) iff_conv_conj_imp)
  hence "P \<longrightarrow> Q" by (fact conjunct1)
  with assms(2) show "Q" by (elim mp)
qed

text {* From now on, @{thm iffD1} can be used. *}

lemma
  assumes "P \<longleftrightarrow> Q" and
    "Q"
  shows "P"
proof -
  from assms(1) have "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P)" by (subst (asm) iff_conv_conj_imp)
  hence "Q \<longrightarrow> P" by (fact conjunct2)
  with assms(2) show "P" by (elim mp)
qed

text {* From now on, @{thm iffD2} can be used. *}

lemma
  shows "A = B \<longleftrightarrow> (\<forall>x. x \<in> A \<longleftrightarrow> x \<in> B)"
proof (rule iffI)
  assume "A = B"
  {
    fix x
    from \<open>A = B\<close> have "x \<in> A \<longleftrightarrow> x \<in> B" by (fact arg_cong)
  }
  thus "\<forall>x. x \<in> A \<longleftrightarrow> x \<in> B" by (fact allI)
next
  assume *: "\<forall>x. x \<in> A \<longleftrightarrow> x \<in> B"
  have "{x. x \<in> A} = {x. x \<in> B}" by (subst *, fact refl)
  thus "A = B" by (subst (asm) (1 2) Collect_mem_eq)
qed

text {* From now on, @{thm set_eq_iff} can be used. *}

proposition prop_1_1_3:
  shows "A = B \<longleftrightarrow> A \<subseteq> B \<and> A \<supseteq> B"
proof (rule iffI)
  assume "A = B"
  hence *: "\<forall>x. x \<in> A \<longleftrightarrow> x \<in> B" by (subst (asm) set_eq_iff)
  have "A \<subseteq> B"
  proof (rule subsetI)
    fix x
    assume "x \<in> A"
    moreover from * have "x \<in> A \<longleftrightarrow> x \<in> B" by (rule spec)
    ultimately show "x \<in> B" by (elim iffD1)
  qed
  moreover have "B \<subseteq> A"
  proof (intro subsetI)
    fix x
    assume "x \<in> B"
    moreover from * have "x \<in> A \<longleftrightarrow> x \<in> B" by (rule spec)
    ultimately show "x \<in> A" by (elim iffD2)
  qed
  ultimately show "A \<subseteq> B \<and> B \<subseteq> A" by (intro conjI)
next
  assume "A \<subseteq> B \<and> B \<subseteq> A"
  {
    fix x
    {
      assume "x \<in> A"
      moreover from \<open>A \<subseteq> B \<and> B \<subseteq> A\<close> have "A \<subseteq> B" by (fact conjunct1)
      ultimately have "x \<in> B" by (elim subsetD)
    }
    moreover {
      assume "x \<in> B"
      moreover from \<open>A \<subseteq> B \<and> B \<subseteq> A\<close> have "B \<subseteq> A" by (fact conjunct2)
      ultimately have "x \<in> A" by (elim subsetD)
    }
    ultimately have "x \<in> A \<longleftrightarrow> x \<in> B" by (intro iffI)
  }
  hence "\<forall>x. x \<in> A \<longleftrightarrow> x \<in> B" by (fact allI)
  thus "A = B" by (subst (asm) set_eq_iff[THEN sym])
qed

lemma
  assumes "\<And>x. x \<in> A \<Longrightarrow> x \<in> B"
  shows "A \<subseteq> B"
proof -
  from assms have "\<forall>x. x \<in> A \<longrightarrow> x \<in> B" by atomize
  thus "?thesis" by (fold subset_iff)
qed

text {* From now on, @{thm subsetI} can be used. *}

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
  thus "?thesis" by (rule subsetI)
qed

lemma emptyD:
  assumes "x \<in> {}"
  shows "False"
proof -
  from assms show "?thesis" by (unfold empty_iff)
qed

lemma
  assumes "False"
  shows "P"
proof -
  from assms have "\<forall>P. P" by (unfold False_def)
  thus "P" by (fact spec)
qed

text {* Fron now on, @{thm FalseE} can be used. *}

proposition prop_1_1_5:
  fixes A :: "'a set"
  shows "{} \<subseteq> A"
proof -
  {
    fix x :: 'a
    assume "x \<in> {}"
    hence "False" by (fact emptyD)
    hence "x \<in> A" by (fact FalseE)
  }
  thus "?thesis" by (rule subsetI)
qed

lemma
  shows "x \<in> {} = False"
proof (rule iffI)
  assume "x \<in> {}"
  thus "False" by (fact emptyD)
next
  assume "False"
  thus "x \<in> {}" by (fact FalseE)
qed

text {* Fron now on, @{thm empty_iff} can be used. *}

lemma
  shows "P \<or> False \<longleftrightarrow> P"
proof (rule iffI)
  assume "P \<or> False"
  moreover {
    assume "P"
    hence "P" .
  }
  moreover {
    assume "False"
    hence "P" by (fact FalseE)
  }
  ultimately show "P" by (elim disjE)
next
  assume "P"
  thus "P \<or> False" by (fact disjI1)
qed

lemma
  shows "A \<union> {} = A"
proof -
  have "A \<union> {} = {x. x \<in> A \<or> x \<in> {}}" by (fact Un_def)
  also have "\<dots> = {x. x \<in> A \<or> False}" by (subst empty_iff, fact refl)
  also have "\<dots> = {x. x \<in> A}" by (subst HOL.simp_thms(31), fact refl)
  also have "\<dots> = A" by (subst Collect_mem_eq, fact refl)
  finally show "?thesis" .
qed

text {* Fron now on, @{thm Un_empty_right} can be used. *}

lemma
  assumes "x \<in> {a}"
  shows "x = a"
proof -
  from assms have "x \<in> {x. x = a} \<union> {}" by (subst (asm) insert_def)
  hence "x \<in> {x. x = a}" by (subst (asm) Un_empty_right)
  thus "?thesis" by (unfold mem_Collect_eq)
qed

text {* From now on, @{thm singletonD} can be used. *}

lemma
  shows "a \<in> {a}"
proof -
  have "a \<in> {x. x = a}" by (unfold mem_Collect_eq, fact refl)
  hence "a \<in> {x. x = a} \<union> {}" by (unfold Un_empty_right)
  thus "?thesis" by (fold insert_def)
qed

text {* From now on, @{thm singletonI} can be used. *}

proposition problem_1_1_1:
  shows "a \<in> A \<longleftrightarrow> {a} \<subseteq> A"
proof (rule iffI)
  assume "a \<in> A"
  {
    fix x
    assume "x \<in> {a}"
    hence "x = a" by (fact singletonD)
    from \<open>a \<in> A\<close> have "x \<in> A" by (subst \<open>x = a\<close>)
  }
  thus "{a} \<subseteq> A" by (rule subsetI)
next
  assume "{a} \<subseteq> A"
  moreover have "a \<in> {a}" by (fact singletonI)
  ultimately show "a \<in> A" by (elim subsetD)
qed

(* TODO: problem_1_1_2 *)
(* TODO: problem_1_1_3_a *)
(* TODO: problem_1_1_3_b *)
(* TODO: problem_1_1_3_c *)
(* TODO: problem_1_1_3_d *)
(* TODO: problem_1_1_3_e *)
(* TODO: problem_1_1_3_f *)
(* TODO: problem_1_1_4 *)
(* TODO: problem_1_1_5 *)

end
