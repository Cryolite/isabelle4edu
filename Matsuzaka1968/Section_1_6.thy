theory Section_1_6
  imports Main
    "HOL-Library.Disjoint_Sets"
    "Split_Pair"
    "Section_1_5"
begin

section \<open>Equivalence Relation\<close>

subsection \<open>A) Notion of Relation\<close>

subsection \<open>B) Equivalence Relation\<close>

lemma refl_onE [elim]:
  assumes "refl_on A r"
  obtains "a \<in> A \<Longrightarrow> (a, a) \<in> r"
    and "(x, y) \<in> r \<Longrightarrow> x \<in> A"
    and "(x, y) \<in> r \<Longrightarrow> y \<in> A"
  using assms by (blast dest: refl_onD refl_on_domain)

lemmas [elim] = symE transE equivE

definition equiv_kernel_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set"
  where "equiv_kernel_on f A = {(a, a') \<in> A \<times> A. f a = f a'}"

lemma equiv_kernel_onI [intro]:
  assumes "a \<in> A"
    and "a' \<in> A"
    and "f a = f a'"
  shows "(a, a') \<in> equiv_kernel_on f A"
  using assms unfolding equiv_kernel_on_def by simp

lemma equiv_kernel_onE [elim]:
  assumes "(a, a') \<in> equiv_kernel_on f A"
  obtains "a \<in> A"
    and "a' \<in> A"
    and "f a = f a'"
  using assms unfolding equiv_kernel_on_def by simp

lemma equiv_equiv_kernel_on:
  shows "equiv A (equiv_kernel_on f A)"
proof (rule equivI)
  show "refl_on A (equiv_kernel_on f A)"
  proof (rule refl_onI)
    show "equiv_kernel_on f A \<subseteq> A \<times> A" by auto
    fix a
    assume "a \<in> A"
    moreover have "f a = f a" by simp
    ultimately show "(a, a) \<in> equiv_kernel_on f A" by auto
  qed
  show "sym (equiv_kernel_on f A)"
  proof (rule symI)
    fix a and a'
    assume "(a, a') \<in> equiv_kernel_on f A"
    thus "(a', a) \<in> equiv_kernel_on f A" by fastforce
  qed
  show "trans (equiv_kernel_on f A)"
  proof (rule transI)
    fix a and a' and a''
    assume "(a, a') \<in> equiv_kernel_on f A" and "(a', a'') \<in> equiv_kernel_on f A"
    thus "(a, a'') \<in> equiv_kernel_on f A" by fastforce
  qed
qed

lemma partition_onI2:
  assumes "{} \<notin> \<MM>"
    and "\<Union>\<MM> = A"
    and "\<And>M M'. M \<in> \<MM> \<Longrightarrow> M' \<in> \<MM> \<Longrightarrow> M \<noteq> M' \<Longrightarrow> M \<inter> M' = {}"
  shows "partition_on A \<MM>"
  using assms by (blast intro: partition_onI disjnt_def[THEN iffD2])

lemma partition_onE [elim]:
  assumes "partition_on A \<MM>"
  obtains "{} \<notin> \<MM>"
    and "\<Union>\<MM> = A"
    and "M \<in> \<MM> \<Longrightarrow> M' \<in> \<MM> \<Longrightarrow> M \<noteq> M' \<Longrightarrow> M \<inter> M' = {}"
  using assms by (auto dest: partition_onD1 partition_onD2 partition_onD3 disjointD)

lemma partition_on_definition:
  shows "partition_on A \<MM>
           \<longleftrightarrow> (\<forall>M \<in> \<MM>. M \<noteq> {}) \<and> \<Union>\<MM> = A \<and> (\<forall>M \<in> \<MM>. \<forall>M' \<in> \<MM>. M \<noteq> M' \<longrightarrow> M \<inter> M' = {})"
    (is "?L \<longleftrightarrow> ?R0 \<and> ?R1 \<and> ?R2")
proof (rule iffI)
  assume "?L"
  thus "?R0 \<and> ?R1 \<and> ?R2" by fast
next
  assume *: "?R0 \<and> ?R1 \<and> ?R2"
  from * have "?R1" by simp
  moreover {
    fix M and M'
    assume "M \<in> \<MM>" and "M' \<in> \<MM>" and "M \<noteq> M'"
    with * have "disjnt M M'" unfolding disjnt_def by simp
  }
  moreover from * have "{} \<notin> \<MM>" by auto
  ultimately show "partition_on A \<MM>" by (fact partition_onI)
qed

definition equiv_by_partition :: "'a set set \<Rightarrow> 'a rel"
  where "equiv_by_partition \<MM> = {(a, a'). \<exists>C \<in> \<MM>. a \<in> C \<and> a' \<in> C}"

lemma equiv_by_partition_iff [iff]:
  shows "(a, a') \<in> equiv_by_partition \<MM> \<longleftrightarrow> (\<exists>C \<in> \<MM>. a \<in> C \<and> a' \<in> C)"
  unfolding equiv_by_partition_def by simp

subsection \<open>C) Equivalence Classes, Quotient Set\<close>

proposition prop_1_6_1:
  assumes "equiv A R"
    and "a \<in> A"
  shows "a \<in> R `` {a}"
  using assms by (fact equiv_class_self)

proposition prop_1_6_2_a:
  assumes "equiv A R"
    and "(a, b) \<in> R"
  shows "R `` {a} = R `` {b}"
  using assms by (fact equiv_class_eq)

proposition prop_1_6_2_b:
  assumes "equiv A R"
    and "a \<in> A"
    and "R `` {a} = R `` {b}"
  shows "(a, b) \<in> R"
proof -
  from assms(1,2) have "a \<in> R `` {a}" by (rule prop_1_6_1)
  with assms(3) have "a \<in> R `` {b}" by simp
  with assms(1) show "(a, b) \<in> R" by auto
qed

proposition prop_1_6_2:
  assumes "equiv A R"
    and "a \<in> A"
  shows "(a, b) \<in> R \<longleftrightarrow> R `` {a} = R `` {b}"
  using assms prop_1_6_2_a prop_1_6_2_b by metis

proposition prop_1_6_3:
  assumes "equiv A R"
    and "R `` {a} \<noteq> R `` {b}"
  shows "R `` {a} \<inter> R `` {b} = {}"
proof (rule ccontr)
  assume "R `` {a} \<inter> R `` {b} \<noteq> {}"
  then obtain c where "c \<in> R `` {a}" and "c \<in> R `` {b}" by auto
  with assms(1) have "(a, b) \<in> R" by auto
  with assms(1) have "R `` {a} = R `` {b}" by (rule prop_1_6_2_a)
  with assms(2) show "False" by simp
qed

theorem thm_1_8_a:
  assumes "equiv A R"
  shows "partition_on A (A // R)"
  using assms by (fact partition_on_quotient)

theorem thm_1_8_b:
  assumes "equiv A R"
  shows "equiv_by_partition (A // R) = R"
proof (rule set_eqI, split_pair)
    fix a and a'
    have "(a, a') \<in> equiv_by_partition (A // R) \<longleftrightarrow> (\<exists>C \<in> A // R. a \<in> C \<and> a' \<in> C)" by simp
    also have "\<dots> \<longleftrightarrow> (\<exists>C \<in> (\<Union>a \<in> A. {R `` {a}}). a \<in> C \<and> a' \<in> C)"
      unfolding quotient_def by blast
    also have "\<dots> \<longleftrightarrow> (\<exists>C. \<exists>a'' \<in> A. C = R `` {a''} \<and> a \<in> C \<and> a' \<in> C)" by auto
    also have "\<dots> \<longleftrightarrow> (\<exists>a'' \<in> A. a \<in> R `` {a''} \<and> a' \<in> R `` {a''})" by blast
    also have "\<dots> \<longleftrightarrow> (\<exists>a'' \<in> A. (a'', a) \<in> R \<and> (a'', a') \<in> R)" by simp
    also from assms have "\<dots> \<longleftrightarrow> (\<exists>a'' \<in> A. (a, a'') \<in> R \<and> (a'', a') \<in> R)" by auto
    also from assms have "\<dots> \<longleftrightarrow> (a, a') \<in> R" by auto
    finally show "(a, a') \<in> equiv_by_partition (A // R) \<longleftrightarrow> (a, a') \<in> R" .
qed

lemmas [intro] = quotientI

lemmas [elim] = quotientE

proposition ex_1_1_a:
  shows "equiv A {(a, a') \<in> A \<times> A. a = a'}"
proof (rule equivI)
  let ?R = "{(a, a') \<in> A \<times> A. a = a'}"
  show "refl_on A ?R"
  proof (rule refl_onI)
    show "?R \<subseteq> A \<times> A" by auto
    fix a
    assume "a \<in> A"
    hence "(a, a) \<in> A \<times> A" by simp
    moreover have "a = a" by simp
    ultimately show "(a, a) \<in> ?R" by simp
  qed
  show "sym ?R"
  proof (rule symI)
    fix a and a'
    assume "(a, a') \<in> {(a, a') \<in> A \<times> A. a = a'}"
    hence "(a', a) \<in> A \<times> A" and "a' = a" by simp+
    thus "(a', a) \<in> {(a, a') \<in> A \<times> A. a = a'}" by simp
  qed
  show "trans ?R"
  proof (rule transI)
    fix a and a' and a''
    assume "(a, a') \<in> ?R" and "(a', a'') \<in> ?R"
    hence "(a, a'') \<in> A \<times> A" and "a = a''" by simp+
    thus "(a, a'') \<in> ?R" by simp
  qed
qed

proposition ex_1_1_b:
  shows "equiv A {(a, a') \<in> A \<times> A. True}"
proof (rule equivI)
  let ?R = "{(a, a') \<in> A \<times> A. True}"
  show "refl_on A ?R"
  proof (rule refl_onI)
    show "?R \<subseteq> A \<times> A" by simp
    fix a
    assume "a \<in> A"
    thus "(a, a) \<in> ?R" by simp
  qed
  show "sym ?R"
  proof (rule symI)
    fix a and a'
    assume "(a, a') \<in> ?R"
    hence "(a, a') \<in> A \<times> A" by simp
    thus "(a', a) \<in> ?R" by simp
  qed
  show "trans ?R"
  proof (rule transI)
    fix a and a' and a''
    assume "(a, a') \<in> ?R" and "(a', a'') \<in> ?R"
    hence "(a, a'') \<in> A \<times> A" by simp
    thus "(a, a'') \<in> ?R" by simp
  qed
qed

subsection \<open>D) Decomposition of Map\<close>

proposition prop_1_6_4:
  assumes "f ` A \<subseteq> B"
  obtains \<phi> and g and j where
    "\<phi> ` A = A // (equiv_kernel_on f A)"
    and "bij_betw g (A // (equiv_kernel_on f A)) (f ` A)"
    and "id_on j (f ` A)"
    and "ext_eq_on A (j \<circ> g \<circ> \<phi>) f"
proof -
  have *: "equiv A (equiv_kernel_on f A)" by (fact equiv_equiv_kernel_on)
  let ?\<phi> = "\<lambda>a. equiv_kernel_on f A `` {a}"
  let ?g = "\<lambda>C. (THE b. \<exists>a \<in> A. ?\<phi> a = C \<and> f a = b)"
  let ?j = "\<lambda>b. if b \<in> f ` A then b else undefined"
  have **: "?g (?\<phi> a) = f a" if "a \<in> A" for a
  proof (rule the_equality)
    from that show "\<exists>a' \<in> A. ?\<phi> a' = equiv_kernel_on f A `` {a} \<and> f a' = f a" by blast
    fix b
    assume "\<exists>a' \<in> A. ?\<phi> a' = equiv_kernel_on f A `` {a} \<and> f a' = b"
    then obtain a' where "a' \<in> A" and "?\<phi> a' = equiv_kernel_on f A `` {a}" and "f a' = b" by auto
    from * and this(1,2) have "(a', a) \<in> equiv_kernel_on f A" by (rule prop_1_6_2_b)
    hence "f a' = f a" by auto
    with \<open>f a' = b\<close> show "b = f a" by simp
  qed
  have "?\<phi> ` A = A // (equiv_kernel_on f A)"
  proof (rule surj_onI)
    fix a
    assume "a \<in> A"
    thus "?\<phi> a \<in> A // (equiv_kernel_on f A)" by auto
  next
    fix C
    assume "C \<in> A // (equiv_kernel_on f A)"
    then obtain a where "a \<in> A" and "C = equiv_kernel_on f A `` {a}" by fast
    thus "\<exists>a \<in> A. ?\<phi> a = C" by auto
  qed
  moreover have "bij_betw ?g (A // (equiv_kernel_on f A)) (f ` A)"
  proof (rule bij_betw_imageI)
    show "?g ` (A // (equiv_kernel_on f A)) = f ` A"
    proof (rule surj_onI)
      fix C
      assume "C \<in> A // (equiv_kernel_on f A)"
      then obtain a where "a \<in> A" and "C = ?\<phi> a" by fast
      from this(1) have "?g (?\<phi> a) = f a" by (fact **)
      with \<open>C = ?\<phi> a\<close> have "?g C = f a" by simp
      with \<open>a \<in> A\<close> show "?g C \<in> f ` A" by simp
    next
      fix b
      assume "b \<in> f ` A"
      then obtain a where "a \<in> A" and "b = f a" by auto
      from this(1) have "?g (?\<phi> a) = f a" by (fact **)
      with \<open>b = f a\<close> have "?g (?\<phi> a) = b" by simp
      moreover from \<open>a \<in> A\<close> have "?\<phi> a \<in> A // equiv_kernel_on f A" by auto
      ultimately show "\<exists>C \<in> A // (equiv_kernel_on f A). ?g C = b" by auto
    qed
    show "inj_on ?g (A // (equiv_kernel_on f A))"
    proof (rule inj_onI)
      fix C and C'
      assume "C \<in> A // (equiv_kernel_on f A)"
        and "C' \<in> A // (equiv_kernel_on f A)"
        and "?g C = ?g C'"
      from this(1,2) obtain a and a' where "a \<in> A" and "C = ?\<phi> a" "a' \<in> A" and "C' = ?\<phi> a'"
        by fastforce
      from this have "?g (?\<phi> a) = f a" and "?g (?\<phi> a') = f a'" by (auto intro: **)
      with \<open>?g C = ?g C'\<close> and \<open>C = ?\<phi> a\<close> and \<open>C' = ?\<phi> a'\<close> have "f a = f a'" by force
      with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> have "?\<phi> a = ?\<phi> a'" by fastforce
      with \<open>C = ?\<phi> a\<close> and \<open>C' = ?\<phi> a'\<close> show "C = C'" by simp
    qed
  qed
  moreover have "id_on ?j (f ` A)"
  proof (rule id_onI)
    fix b
    assume "b \<in> f ` A"
    thus "?j b = b" by simp
  qed
  moreover have "ext_eq_on A (?j \<circ> ?g \<circ> ?\<phi>) f"
  proof (rule ext_eq_onI)
    fix a
    assume "a \<in> A"
    hence "?g (?\<phi> a) = f a" by (fact **)
    with \<open>a \<in> A\<close> have "?g (?\<phi> a) \<in> f ` A" by simp
    hence "?j (?g (?\<phi> a)) = ?g (?\<phi> a)" by simp
    with \<open>?g (?\<phi> a) = f a\<close> show "(?j \<circ> ?g \<circ> ?\<phi>) a = f a" by force
  qed
  ultimately show "thesis" by (fact that)
qed

subsection \<open>Problems\<close>

proposition prob_1_6_1_a:
  assumes "A - B \<noteq> {}"
    and "B - A \<noteq> {}"
    and "A \<inter> B \<noteq> {}"
  defines R: "R \<equiv> A \<times> A \<union> B \<times> B"
  shows "refl_on (A \<union> B) R"
    and "sym R"
    and "\<not>trans R"
proof -
  have "R \<subseteq> (A \<union> B) \<times> (A \<union> B)" unfolding R by auto
  moreover {
    fix a
    assume "a \<in> A \<union> B"
    hence "(a, a) \<in> R" unfolding R by simp
  }
  ultimately show "refl_on (A \<union> B) R" by (rule refl_onI)
  {
    fix a and a'
    assume "(a, a') \<in> R"
    hence "(a', a) \<in> R" unfolding R by auto
  }
  thus "sym R" by (rule symI)
  {
    assume "trans R"
    from assms obtain a and b and c where "a \<in> A - B" and "b \<in> B - A" and "c \<in> A \<inter> B" by auto
    hence "(a, c) \<in> R" and "(c, b) \<in> R" and "(a, b) \<notin> R" unfolding R by auto
    from this(1,2) and \<open>trans R\<close> have "(a, b) \<in> R" by auto
    with \<open>(a, b) \<notin> R\<close> have "False" ..
  }
  thus "\<not>trans R" ..
qed

proposition prob_1_6_1_b:
  defines R: "R :: nat rel \<equiv> {(a, b). a \<le> b}"
  shows "refl_on UNIV R"
    and "\<not>sym R"
    and "trans R"
proof -
  have "R \<subseteq> UNIV \<times> UNIV" unfolding R by simp
  moreover {
    fix a
    have "(a, a) \<in> R" unfolding R by simp
  }
  ultimately show "refl_on UNIV R" by (rule refl_onI)
  {
    assume "sym R"
    moreover have "(0, 1) \<in> R" unfolding R by simp
    ultimately have "(1, 0) \<in> R" by auto
    moreover have "(1, 0) \<notin> R" unfolding R by simp
    ultimately have "False" by simp
  }
  thus "\<not>sym R" by auto
  {
    fix a and a' and a''
    assume "(a, a') \<in> R" and "(a', a'') \<in> R"
    hence "(a, a'') \<in> R" unfolding R by fastforce
  }
  thus "trans R" by (rule transI)
qed

proposition prob_1_6_2:
  assumes "R \<subseteq> A \<times> A"
    and "sym R"
    and "trans R"
    and "\<forall>a \<in> A. \<exists>x. (a, x) \<in> R"
  shows "equiv A R"
proof (rule equivI[OF _ assms(2) assms(3)])
  {
    fix a
    assume "a \<in> A"
    with assms(4) obtain a' where "(a, a') \<in> R" by auto
    moreover from this and assms(2) have "(a', a) \<in> R" by auto
    moreover note assms(3)
    ultimately have "(a, a) \<in> R" by auto
  }
  with assms(1) show "refl_on A R" by (rule refl_onI)
qed

proposition prob_1_6_3:
  assumes -- \<open>The assumption @{prop "R \<subseteq> A \<times> A"} is not necessary since it is implied by
              @{prop "refl_on A R"}.\<close>
    "refl_on A R"
    and "\<forall>a b c. (a, b) \<in> R \<and> (b, c) \<in> R \<longrightarrow> (c, a) \<in> R"
  shows "equiv A R"
proof (rule equivI[OF assms(1)])
  {
    fix a and a'
    assume "(a, a') \<in> R"
    moreover from this and assms(1) have "a \<in> A" and "a' \<in> A" by auto
    moreover from this(2) and assms(1) have "(a', a') \<in> R" by auto
    moreover note assms(2)
    ultimately have "(a', a) \<in> R" by blast
  }
  thus "sym R" by (rule symI)
  {
    fix a and a' and a''
    assume "(a, a') \<in> R" and "(a', a'') \<in> R"
    with assms(2) have "(a'', a) \<in> R" by blast
    with \<open>sym R\<close> have "(a, a'') \<in> R" by auto
  }
  thus "trans R" by (rule transI)
qed

proposition prob_1_6_4:
  defines A: "A :: int rel \<equiv> UNIV \<times> (UNIV - {0})"
  defines R: "R \<equiv> {((m, n), (m', n')) \<in> A \<times> A. m * n' = m' * n}"
  shows "equiv A R"
proof (rule equivI)
  have "R \<subseteq> A \<times> A" unfolding R by auto
  moreover {
    fix m and n
    assume "(m, n) \<in> A"
    hence "((m, n), (m, n)) \<in> R" unfolding R by simp
  }
  ultimately show "refl_on A R" by (intro refl_onI; split_pair)
  {
    fix m and n and m' and n'
    assume "((m, n), (m', n')) \<in> R"
    hence "(m, n) \<in> A" and "(m', n') \<in> A" and "m * n' = m' * n" unfolding R by auto
    from this(3) have "m' * n = m * n'" by simp
    with \<open>(m, n) \<in> A\<close> and \<open>(m', n') \<in> A\<close> have "((m', n'), (m, n)) \<in> R" unfolding R by fast
  }
  thus "sym R" by (intro symI, split_pair)
  {
    fix m and n and m' and n' and m'' and n''
    assume "((m, n), (m', n')) \<in> R" and "((m', n'), (m'', n'')) \<in> R"
    hence "(m, n) \<in> A"
      and "(m', n') \<in> A"
      and "(m'', n'') \<in> A"
      and "m * n' = m' * n"
      and "m' * n'' = m'' * n'" unfolding R by auto
    from this(4,5) have "m * n' * n'' = m' * n * n''"
      and "m' * n * n'' = m'' * n * n'" by simp+
    hence "m * n'' * n' = m'' * n * n'" by algebra
    moreover from \<open>(m', n') \<in> A\<close> have "n' \<noteq> 0" unfolding A by simp
    ultimately have "m * n'' = m'' * n" by simp
    with \<open>(m, n) \<in> A\<close> and \<open>(m'', n'') \<in> A\<close> have "((m, n), (m'', n'')) \<in> R" unfolding R by simp
  }
  thus "trans R" by (intro transI, split_pair)
qed

proposition prob_1_6_5:
  shows "equiv_kernel_on fst (A \<times> B) = {((a, b), (a', b')) \<in> (A \<times> B) \<times> (A \<times> B). a = a'}"
    (is "?L = ?R")
proof (rule set_eqI; split_pair)
  fix a and b and a' and b'
  have "((a, b), (a', b')) \<in> ?L
          \<longleftrightarrow> (a, b) \<in> A \<times> B \<and> (a', b') \<in> A \<times> B \<and> fst (a, b) = fst (a', b')" by blast
  also have "\<dots> \<longleftrightarrow> (a, b) \<in> A \<times> B \<and> (a', b') \<in> A \<times> B \<and> a = a'" by simp
  also have "\<dots> \<longleftrightarrow> ((a, b), (a', b')) \<in> ?R" by simp
  finally show "((a, b), (a', b')) \<in> ?L \<longleftrightarrow> ((a, b), (a', b')) \<in> ?R" .
qed

proposition prob_1_6_6_a:
  assumes "equiv A R"
  defines phi: "\<phi> a \<equiv> R `` {a}"
  assumes -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    -- \<open>The assumption @{prop "g ` (A // R) \<subseteq> B"} is not necessary.\<close>
    "ext_eq_on A f (g \<circ> \<phi>)"
  shows "\<forall>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> R \<longrightarrow> f a = f a'"
proof (intro ballI, rule impI)
  fix a and a'
  assume "(a, a') \<in> R"
  with assms(1) have "R `` {a} = R `` {a'}" by (rule prop_1_6_2_a)
  hence "\<phi> a = \<phi> a'" by (unfold phi)
  moreover from assms(1) and \<open>(a, a') \<in> R\<close> have "a \<in> A" and "a' \<in> A" by auto
  moreover note assms(3)
  ultimately show "f a = f a'" by (elim prob_1_5_14_a)
qed

proposition prob_1_6_6_b:
  assumes "equiv A R"
  defines phi: "\<phi> \<equiv> \<lambda>a. R `` {a}"
  assumes "f ` A \<subseteq> B"
    and "\<forall>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> R \<longrightarrow> f a = f a'"
  obtains g where "g ` (A // R) \<subseteq> B" and "ext_eq_on A f (g \<circ> \<phi>)"
proof -
  {
    fix a and a'
    assume "a \<in> A" and "a' \<in> A" and "\<phi> a = \<phi> a'"
    from this(3) have "R `` {a} = R `` {a'}" unfolding phi by simp
    with assms(1) and \<open>a \<in> A\<close> have "(a, a') \<in> R" by (rule prop_1_6_2_b)
    with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and assms(4) have "f a = f a'" by simp
  }
  moreover from assms(1) have "A = {} \<Longrightarrow> A // R = {}" by simp
  moreover note assms(3)
  ultimately obtain g where "g ` (A // R) \<subseteq> B" and "ext_eq_on A f (g \<circ> \<phi>)" by (elim prob_1_5_14_b)
  thus "thesis" by (fact that)
qed

proposition prob_1_6_6:
  assumes "equiv A R"
  defines phi: "\<phi> \<equiv> \<lambda>a. R `` {a}"
  assumes "f ` A \<subseteq> B"
  shows "(\<exists>g. g ` (A // R) \<subseteq> B \<and> ext_eq_on A f (g \<circ> \<phi>))
            \<longleftrightarrow> (\<forall>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> R \<longrightarrow> f a = f a')"
proof (rule iffI)
  assume "\<exists>g. g ` (A // R) \<subseteq> B \<and> ext_eq_on A f (g \<circ> \<phi>)"
  then obtain g where "ext_eq_on A f (g \<circ> \<phi>)" by auto
  with assms(1) and phi show "\<forall>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> R \<longrightarrow> f a = f a'"
    by (auto dest: prob_1_6_6_a)
next
  assume "\<forall>a \<in> A. \<forall>a' \<in> A. (a, a') \<in> R \<longrightarrow> f a = f a'"
  with assms(1,3) obtain g where "g ` (A // R) \<subseteq> B" and "ext_eq_on A f (g \<circ> \<phi>)"
    unfolding phi by (elim prob_1_6_6_b)
  thus "\<exists>g. g ` (A // R) \<subseteq> B \<and> ext_eq_on A f (g \<circ> \<phi>)" by auto
qed

end
