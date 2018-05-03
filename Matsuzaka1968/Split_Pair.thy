theory Split_Pair
  imports Main
    "HOL-Eisbach.Eisbach"
begin

lemma split_paired_Coll:
  shows "{x. P x} = {(a, b). P (a, b)}"
  by simp

lemma split_paired_Collect:
  shows "{x \<in> X. P x} = {(a, b) \<in> X. P (a, b)}"
  by auto

lemma split_paired_Ball_Times:
  shows "(\<forall>x \<in> A \<times> B. P x) \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B. P (a, b))"
  by simp

lemma split_paired_Bex_Times:
  shows "(\<exists>x \<in> A \<times> B. P x) \<longleftrightarrow> (\<exists>a \<in> A. \<exists>b \<in> B. P (a, b))"
  by simp

method split_pair = (
    (unfold split_paired_all)?;
    (unfold split_paired_All)?;
    (unfold split_paired_Ex)?;
    (unfold split_paired_The)?;
    (subst split_paired_Coll)?;
    (subst split_paired_Collect)?;
    (unfold split_paired_Ball_Times)?;
    (unfold split_paired_Bex_Times)?;
    (unfold case_prod_conv)?)

experiment
  fixes A :: "('a \<times> 'b) set"
begin

lemma
  shows "A = A"
proof (rule set_eqI; split_pair)
  fix a b
  show "(a, b) \<in> A \<longleftrightarrow> (a, b) \<in> A" ..
qed

lemma subsetI_atomize:
  assumes "\<forall>x. x \<in> X \<longrightarrow> x \<in> Y"
  shows "X \<subseteq> Y"
  using assms by auto

lemma
  assumes "A = {}"
    and "B = {}"
  shows "A \<subseteq> B"
proof (rule subsetI_atomize; split_pair)
  {
    fix a b
    assume "(a, b) \<in> A"
    with assms(1) have "(a, b) \<in> B" by simp
  }
  thus "\<forall>a b. (a, b) \<in> A \<longrightarrow> (a, b) \<in> B" by simp
qed

lemma ex_mem_imp_not_empty:
  assumes "\<exists>x. x \<in> X"
  shows "X \<noteq> {}"
  using assms by auto

lemma
  assumes "(a, b) \<in> A"
  shows "A \<noteq> {}"
proof (rule ex_mem_imp_not_empty; split_pair)
  from assms show "\<exists>a b. (a, b) \<in> A" by auto
qed

lemma Coll_False_imp_empty:
  assumes "X = {x. False}"
  shows "X = {}"
  using assms by simp

lemma
  assumes "A = {(a, b). a \<noteq> a}"
  shows "A = {}"
proof (rule Coll_False_imp_empty; split_pair)
  from assms show "A = {(a, b). False}" by simp
qed

lemma Collect_False_imp_empty:
  assumes "X = {x \<in> Y. False}"
  shows "X = {}"
  using assms by simp

lemma
  assumes "A = {(a, b) \<in> Y. a \<noteq> a}"
  shows "A = {}"
proof (rule Collect_False_imp_empty; split_pair)
  from assms show "A = {(a, b) \<in> Y. False}" by simp
qed

lemma subsetI_Ball:
  assumes "\<forall>x \<in> X. x \<in> Y"
  shows "X \<subseteq> Y"
  using assms by auto

lemma
  assumes "\<And>a b. (a, b) \<in> X \<times> Y \<Longrightarrow> (a, b) \<in> Z \<times> W"
  shows "(X \<times> Y) \<subseteq> (Z \<times> W)"
proof (rule subsetI_Ball; split_pair)
  {
    fix a b
    assume "a \<in> X"
      and "b \<in> Y"
    with assms have "(a, b) \<in> Z \<times> W" by simp
  }
  thus "\<forall>a \<in> X. \<forall> b \<in> Y. (a, b) \<in> Z \<times> W" by simp
qed

lemma Bex_imp_not_empty:
  assumes "\<exists>x \<in> X. P x"
  shows "X \<noteq> {}"
  using assms by auto

lemma
  assumes "x \<in> X \<times> Y"
  shows "X \<times> Y \<noteq> {}"
proof (rule Bex_imp_not_empty[where P = "\<lambda>x. True"]; split_pair)
  from assms have "fst x \<in> X" and "snd x \<in> Y" by auto
  thus "\<exists>x \<in> X. \<exists>y \<in> Y. True" by auto
qed

end

end
