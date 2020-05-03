theory Section_1_3
  imports Main
    "Split_Pair"
    "Section_1_2"
begin

section \<open>Correspondences, Functions\<close>

subsection \<open>A) Direct Product of Two Sets\<close>

proposition example_1_3_1:
  fixes p and q and r
  defines "A \<equiv> {1, 2}"
    and "B \<equiv> {p, q, r}"
  shows "A \<times> B = {(1, p), (1, q), (1, r), (2, p), (2, q), (2, r)}"
    and "A \<times> A = {(1, 1), (1, 2), (2, 1), (2, 2)}"
  unfolding A_def and B_def by auto

proposition example_1_3_2:
  assumes "finite A"
    and "finite B"
    and "card A = m"
    and "card B = n"
  shows "card (A \<times> B) = m * n"
  using assms by simp

subsection \<open>B) Notion of Correspondence\<close>

text \<open>
  In this section, a correspondence is defined by a function of the type @{typ "'a => 'b set"}.
  Neither the initial nor target set of a correspondence is not explicitly specified. Instead, for
  a correspondence @{term "\<Gamma>"}, its initial set is implicitly specified by a set
  @{term [show_types] "A :: 'a set"} such that @{prop "\<forall>a. a \<notin> A \<longrightarrow> \<Gamma> a = {}"}, and its target
  set is implicitly specified by a set @{term "B :: 'b set"} such that @{prop "\<Gamma> `` A \<subseteq> B"}.
\<close>

subsection \<open>C) Graph of Correspondence\<close>

definition corr_graph :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<times> 'b) set"
  where "corr_graph \<Gamma> = {(a, b). b \<in> \<Gamma> a}"

lemma corr_graphI [intro]:
  assumes "b \<in> \<Gamma> a"
  shows "(a, b) \<in> corr_graph \<Gamma>"
  using assms unfolding corr_graph_def by simp

lemma corr_graphD [dest]:
  assumes "(a, b) \<in> corr_graph \<Gamma>"
  shows "b \<in> \<Gamma> a"
  using assms unfolding corr_graph_def by simp

proposition prop_1_3_1:
  shows "\<Gamma> a = {b. (a, b) \<in> corr_graph \<Gamma>}"
  by auto

theorem thm_1_1:
  shows "\<exists>!\<Gamma>. corr_graph \<Gamma> = G"
proof -
  define \<Gamma> where "\<Gamma> a \<equiv> {b. (a, b) \<in> G}" for a
  show ?thesis
  proof (rule ex1I)
    from \<Gamma>_def show "corr_graph \<Gamma> = G" by auto
  next
    fix \<Gamma>'
    assume "corr_graph \<Gamma>' = G"
    with \<Gamma>_def show "\<Gamma>' = \<Gamma>" by auto
  qed
qed

lemma corr_graph_inject:
  assumes "corr_graph \<Gamma> = corr_graph \<Gamma>'"
  shows "\<Gamma> = \<Gamma>'"
  using assms thm_1_1 by auto

definition corr_dom :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set"
  where "corr_dom \<Gamma> = {a. \<exists>b. (a, b) \<in> corr_graph \<Gamma>}"

lemma corr_domI [intro]:
  assumes "b \<in> \<Gamma> a"
  shows "a \<in> corr_dom \<Gamma>"
  using assms unfolding corr_dom_def by auto

lemma corr_domE [elim]:
  assumes "a \<in> corr_dom \<Gamma>"
  obtains b where "b \<in> \<Gamma> a"
  using assms unfolding corr_dom_def by auto

definition corr_range :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set"
  where "corr_range \<Gamma> = {b. \<exists>a. (a, b) \<in> corr_graph \<Gamma>}"

lemma corr_rangeI [intro]:
  assumes "b \<in> \<Gamma> a"
  shows "b \<in> corr_range \<Gamma>"
  using assms unfolding corr_range_def by auto

lemma corr_rangeE [elim]:
  assumes "b \<in> corr_range \<Gamma>"
  obtains a where "b \<in> \<Gamma> a"
  using assms unfolding corr_range_def by auto

subsection \<open>D) Inverse of Correspondence\<close>

definition corr_inv :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b \<Rightarrow> 'a set"
  where "corr_inv \<Gamma> b = {a. b \<in> \<Gamma> a}"

lemma corr_invI [intro]:
  assumes "b \<in> \<Gamma> a"
  shows "a \<in> corr_inv \<Gamma> b"
  using assms unfolding corr_inv_def by simp

lemma corr_invD [dest]:
  assumes "a \<in> corr_inv \<Gamma> b"
  shows "b \<in> \<Gamma> a"
  using assms unfolding corr_inv_def by simp

proposition prop_1_3_2:
  shows "b \<in> \<Gamma> a \<longleftrightarrow> a \<in> corr_inv \<Gamma> b"
  by auto

proposition prop_1_3_a:
  shows "corr_graph (corr_inv \<Gamma>) = {(b, a). (a, b) \<in> corr_graph \<Gamma>}"
  by auto

proposition prop_1_3_3_a:
  shows "corr_dom (corr_inv \<Gamma>) = corr_range \<Gamma>"
  by auto

proposition prop_1_3_3_b:
  shows "corr_range (corr_inv \<Gamma>) = corr_dom \<Gamma>"
  by auto

proposition prop_1_3_4:
  shows "corr_inv (corr_inv \<Gamma>) = \<Gamma>"
  by auto

proposition prop_1_3_b:
  shows "corr_inv \<Gamma> b \<noteq> {} \<longleftrightarrow> b \<in> corr_range \<Gamma>"
  by auto

subsection \<open>E) Maps\<close>

definition as_corr_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b set"
  where "as_corr_on f A a = (if a \<in> A then {f a} else {})"

text \<open>
  @{const "as_corr_on"} transforms a function into the correspondence. Since a function
  @{term "f :: 'a \<Rightarrow> 'b"} in Isabelle/HOL is total, which means that the function is always
  defined on the universal set @{term "UNIV :: 'a set"} of the type @{typ "'a"},
  @{const "as_corr_on"} additionally specifies a set of the type @{typ "'a set"} that should be
  considered as the domain of the function.
\<close>

lemma as_corr_onI [intro]:
  assumes "a \<in> A"
    and "f a = b"
  shows "b \<in> as_corr_on f A a"
  using assms unfolding as_corr_on_def by simp

lemma as_corr_onE [elim]:
  assumes "b \<in> as_corr_on f A a"
  obtains "a \<in> A" and "f a = b"
proof -
  from assms have *: "b \<in> (if a \<in> A then {f a} else {})" by (simp only: as_corr_on_def)
  {
    assume "a \<notin> A"
    with * have "False" by simp
  }
  hence "a \<in> A" by auto
  moreover from this and * have "f a = b" by simp
  ultimately show "thesis" by (fact that)
qed

definition corr_functional_on :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "corr_functional_on \<Gamma> A \<longleftrightarrow> (\<forall>a. (a \<in> A \<longrightarrow> (\<exists>!b. b \<in> \<Gamma> a)) \<and> (a \<notin> A \<longrightarrow> \<Gamma> a = {}))"

definition id_on :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "id_on f A \<longleftrightarrow> (\<forall>a \<in> A. f a = a)"

text \<open>
  @{prop "id_on f A"} states that the function @{term f} behaves as an identity function on
  the set @{term A}. This proposition does not specify any other property of @{term f} on an
  element out of @{term A}.
\<close>

lemmas id_on_iff = id_on_def

lemma id_onI [intro]:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a = a"
  shows "id_on f A"
  using assms unfolding id_on_def by simp

lemma id_onD [dest]:
  assumes "id_on f A"
    and "a \<in> A"
  shows "f a = a"
  using assms unfolding id_on_def by fast

lemma id_on_empty [simp]:
  shows "id_on f {}"
  by auto

lemma set_eqI2:
  assumes "\<And>x. x \<in> A \<Longrightarrow> x \<in> B"
    and "\<And>x. x \<in> B \<Longrightarrow> x \<in> A"
  shows "A = B"
  using assms by blast

lemma id_on_imp_surj_on:
  assumes "id_on f A"
  shows "f ` A = A"
  using assms by force

lemma id_on_imp_inj_on:
  assumes "id_on f A"
  shows "inj_on f A"
proof (rule inj_onI)
  fix a and a'
  assume "a \<in> A" and "a' \<in> A" and "f a = f a'"
  with assms show "a = a'" using id_onD by fastforce
qed

lemma id_on_imp_bij_betw:
  assumes "id_on f A"
  shows "bij_betw f A A"
  using assms by (auto intro: bij_betw_imageI dest: id_on_imp_surj_on id_on_imp_inj_on)

lemma thm_1_2_a:
  assumes \<comment> \<open> The assumption @{prop "G \<subseteq> A \<times> B"} is not necessary.\<close>
    "f ` A \<subseteq> B"
    and "corr_graph (as_corr_on f A) = G"
  shows "\<forall>a \<in> A. \<exists>!b \<in> B. (a, b) \<in> G"
  using assms by fast

lemma thm_1_2_b:
  assumes "G \<subseteq> A \<times> B"
    and "\<forall>a \<in> A. \<exists>!b \<in> B. (a, b) \<in> G"
  obtains f where
    "f ` A \<subseteq> B"
    and "corr_graph (as_corr_on f A) = G"
proof -
  define f where "f a \<equiv> THE b. b \<in> B \<and> (a, b) \<in> G" for a
  have f0: "f a \<in> B" and f1: "(a, f a) \<in> G" if "a \<in> A" for a
  proof -
    from assms(2) and that have "\<exists>!b. b \<in> B \<and> (a, b) \<in> G" by simp
    hence "f a \<in> B \<and> (a, f a) \<in> G" (is "?L \<and> ?R") unfolding f_def by (fact theI')
    thus ?L and ?R by simp+
  qed
  from f0 have "f ` A \<subseteq> B" by auto
  moreover have "corr_graph (as_corr_on f A) = G"
  proof (rule set_eqI2, split_pair; split_pair)
    fix a b
    assume "(a, b) \<in> corr_graph (as_corr_on f A)"
    hence "b \<in> as_corr_on f A a" by auto
    hence "a \<in> A" and "f a = b" by auto
    thus "(a, b) \<in> G" by (auto intro: f1)
  next
    fix a b
    assume "(a, b) \<in> G"
    with assms(1) have "a \<in> A" and "b \<in> B" by auto
    from this(1) and assms(2) have "\<exists>!b \<in> B. (a, b) \<in> G" by simp
    with \<open>b \<in> B\<close> and \<open>(a, b) \<in> G\<close> have "f a = b" unfolding f_def by auto
    with \<open>a \<in> A\<close> have "b \<in> as_corr_on f A a" by auto
    thus "(a, b) \<in> corr_graph (as_corr_on f A)" by auto
  qed
  ultimately show thesis by (fact that)
qed

theorem thm_1_2:
  assumes "G \<subseteq> A \<times> B"
  shows "(\<exists>f. f ` A \<subseteq> B \<and> corr_graph (as_corr_on f A) = G) \<longleftrightarrow> (\<forall>a \<in> A. \<exists>!b \<in> B. (a, b) \<in> G)"
    (is "?L \<longleftrightarrow> ?R")
proof (intro iffI)
  assume "?L"
  then obtain f where "f ` A \<subseteq> B" and "corr_graph (as_corr_on f A) = G" by blast
  thus "?R" by (elim thm_1_2_a)
next
  assume "?R"
  with assms obtain f where "f ` A \<subseteq> B" and "corr_graph (as_corr_on f A) = G" by (elim thm_1_2_b)
  thus "?L" by auto
qed

subsection \<open>Problems\<close>

(* TODO: prob_1_3_1 *)
(* TODO: prob_1_3_2 *)

proposition prob_1_3_3_a:
  assumes \<comment> \<open>The assumption @{prop "corr_graph \<Gamma> \<subseteq> A \<times> B"} is not necessary.\<close>
    \<comment> \<open>Since @{prop "corr_dom \<Gamma> = A"}* is an assumption, the assumption
        @{prop "corr_graph \<Gamma> \<subseteq> A \<times> B"} can be replaced by @{prop "corr_range \<Gamma> \<subseteq> B"}.\<close>
    "corr_range \<Gamma> \<subseteq> B"
    and "corr_dom \<Gamma> = A"
    and "\<And>b b'. b \<in> B \<Longrightarrow> b' \<in> B \<Longrightarrow> b \<noteq> b' \<Longrightarrow> corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' = {}"
  obtains f where "f ` A \<subseteq> B" and "as_corr_on f A = \<Gamma>"
proof -
  {
    fix a
    assume "a \<in> A"
    with assms(2) obtain b where *: "b \<in> \<Gamma> a" by auto
    with assms(1) have "b \<in> B" by auto
    moreover from * have "(a, b) \<in> corr_graph \<Gamma>" by auto
    moreover {
      fix b'
      assume "b' \<in> B" and "(a, b') \<in> corr_graph \<Gamma>"
      {
        assume "b' \<noteq> b"
        moreover note \<open>b \<in> B\<close> and \<open>b' \<in> B\<close>
        moreover have "corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' \<noteq> {}"
        proof -
          from \<open>b \<in> \<Gamma> a\<close> have "a \<in> corr_inv \<Gamma> b" by auto
          moreover from \<open>(a, b') \<in> corr_graph \<Gamma>\<close> have "a \<in> corr_inv \<Gamma> b'" by auto
          ultimately show ?thesis by auto
        qed
        ultimately have "False" using assms(3) by simp
      }
      hence "b' = b" by auto
    }
    ultimately have "\<exists>!b \<in> B. (a, b) \<in> corr_graph \<Gamma>" by blast
  }
  hence "\<forall>a \<in> A. \<exists>!b \<in> B. (a, b) \<in> corr_graph \<Gamma>" ..
  moreover from assms(1,2) have "corr_graph \<Gamma> \<subseteq> A \<times> B" by auto
  ultimately obtain f
    where "f ` A \<subseteq> B"
      and "corr_graph (as_corr_on f A) = corr_graph \<Gamma>" by (elim thm_1_2_b)
  hence "as_corr_on f A = \<Gamma>" by (elim corr_graph_inject)
  with \<open>f ` A \<subseteq> B\<close> show "thesis" by (rule that)
qed

proposition prob_1_3_3_b:
  assumes \<comment> \<open>The assumption @{prop "corr_graph \<Gamma> \<subseteq> A \<times> B"} is not necessary.\<close>
    \<comment> \<open>Original assumptions would include @{prop "corr_graph \<Gamma> \<subseteq> A \<times> B"} but it can be weakened
        to the assumption @{prop "corr_dom \<Gamma> \<subseteq> A"}.\<close>
    "corr_dom \<Gamma> \<subseteq> A"
    and "f ` A \<subseteq> B"
    and "as_corr_on f A = \<Gamma>"
  obtains "corr_dom \<Gamma> = A"
    and "\<And>b b'. b \<in> B \<Longrightarrow> b' \<in> B \<Longrightarrow> b \<noteq> b' \<Longrightarrow> corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' = {}"
proof -
  from assms(3) have "corr_graph (as_corr_on f A) = corr_graph \<Gamma>" by simp
  with assms(2) have *: "\<forall>a \<in> A. \<exists>!b \<in> B. (a, b) \<in> corr_graph \<Gamma>" by (rule thm_1_2_a)
  note assms(1)
  moreover have "A \<subseteq> corr_dom \<Gamma>" using * by blast
  ultimately have "corr_dom \<Gamma> = A" ..
  moreover {
    fix b and b'
    assume "b \<in> B" and "b' \<in> B" and "b \<noteq> b'"
    {
      fix a
      assume "a \<in> corr_inv \<Gamma> b" and "a \<in> corr_inv \<Gamma> b'"
      hence "(a, b) \<in> corr_graph \<Gamma>" and "(a, b') \<in> corr_graph \<Gamma>" by auto
      moreover from \<open>(a, b) \<in> corr_graph \<Gamma>\<close> and assms(1) have "a \<in> A" by auto
      moreover note \<open>b \<in> B\<close> and \<open>b' \<in> B\<close>
      ultimately have "b = b'" using * by auto
      with \<open>b \<noteq> b'\<close> have "False" ..
    }
    hence "corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' = {}" by auto
  }
  ultimately show "thesis" by (fact that)
qed

proposition prob_1_3_3:
  assumes "corr_dom \<Gamma> \<subseteq> A"
    and "corr_range \<Gamma> \<subseteq> B"
  shows "corr_dom \<Gamma> = A \<and> (\<forall>b \<in> B. \<forall>b' \<in> B. b \<noteq> b' \<longrightarrow> corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' = {}) \<longleftrightarrow>
         (\<exists>f. f ` A \<subseteq> B \<and> as_corr_on f A = \<Gamma>)" (is "?L \<longleftrightarrow> ?R")
proof (intro iffI)
  assume "?L"
  hence "corr_dom \<Gamma> = A"
    and "\<And>b b'. b \<in> B \<Longrightarrow> b' \<in> B \<Longrightarrow> b \<noteq> b' \<Longrightarrow> corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' = {}" by simp+
  with assms(2) obtain f where "f ` A \<subseteq> B" and "as_corr_on f A = \<Gamma>" by (rule prob_1_3_3_a)
  thus "?R" by auto
next
  assume "?R"
  then obtain f where "f ` A \<subseteq> B" and "as_corr_on f A = \<Gamma>" by auto
  with assms(1) show "?L" by blast
qed

proposition prob_1_3_4_a:
  assumes "id_on f A"
  shows "corr_graph (as_corr_on f A) = {(a, a) | a. a \<in> A}" (is "?L = ?R")
proof -
  have "?L = {(a, b). a \<in> A \<and> b = f a}" by auto
  also from assms have "\<dots> = ?R" by auto
  finally show ?thesis .
qed

proposition prob_1_3_4_b:
  assumes "\<forall>a \<in> A. f a = b\<^sub>0"
  shows "corr_graph (as_corr_on f A) = {(a, b\<^sub>0) | a. a \<in> A}" (is "?L = ?R")
proof -
  have "?L = {(a, b). a \<in> A \<and> b = f a}" by auto
  also from assms have "\<dots> = ?R" by fastforce
  finally show ?thesis .
qed

end
