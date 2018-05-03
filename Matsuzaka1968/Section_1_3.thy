theory Section_1_3
  imports Main
    "Split_Pair"
    "Section_1_2"
begin

section "Correspondences, Functions"

text {*
  In this section, a correspondence is defined by a function of the type @{typ "'a => 'b set"}.
  Neither the initial nor target set of a correspondence is not explicitly specified. Instead, for
  a correspondence @{term \<Gamma>}, its initial set is implicitly specified by a set @{term A} such that
  @{prop "\<forall>a. a \<notin> A \<longrightarrow> \<Gamma> a = {}"}, and its target set is implicitly specified by a set @{term B}
  such that @{prop "\<Gamma> `` A \<subseteq> B"}.
*}

definition corr_graph :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<times> 'b) set"
  where "corr_graph \<Gamma> = {(a, b). b \<in> \<Gamma> a}"

lemma corr_graphI:
  assumes "b \<in> \<Gamma> a"
  shows "(a, b) \<in> corr_graph \<Gamma>"
  using assms by (simp add: corr_graph_def)

lemma corr_graphD:
  assumes "(a, b) \<in> corr_graph \<Gamma>"
  shows "b \<in> \<Gamma> a"
  using assms by (simp add: corr_graph_def)

lemma corr_graph_iff:
  shows "(a, b) \<in> corr_graph \<Gamma> \<longleftrightarrow> b \<in> \<Gamma> a"
  by (simp add: corr_graph_def)

lemma corr_graph_eqI:
  assumes "\<And>a. \<Gamma> a = {b. (a, b) \<in> G}"
  shows "corr_graph \<Gamma> = G" (is "?LHS = _")
proof (intro set_eqI, split_pair)
  fix a and b
  have "(a, b) \<in> ?LHS \<longleftrightarrow> b \<in> \<Gamma> a" by (fact corr_graph_iff)
  also from this and assms have "\<dots> \<longleftrightarrow> (a, b) \<in> G" by simp
  finally show "(a, b) \<in> ?LHS \<longleftrightarrow> (a, b) \<in> G" .
qed

lemma corr_graph_eqD:
  assumes "corr_graph \<Gamma> = G"
  shows "\<Gamma> a = {b. (a, b) \<in> G}" (is "_ = ?R")
proof (intro set_eqI)
  fix b
  have "b \<in> \<Gamma> a \<longleftrightarrow> (a, b) \<in> corr_graph \<Gamma>" by (simp only: corr_graph_iff)
  also have "\<dots> \<longleftrightarrow> (a, b) \<in> G" by (simp only: assms)
  also have "\<dots> \<longleftrightarrow> b \<in> ?R" by simp
  finally show "b \<in> \<Gamma> a \<longleftrightarrow> b \<in> ?R" by simp
qed

proposition prop_1_3_1:
  shows "\<Gamma> a = {b. (a, b) \<in> corr_graph \<Gamma>}" (is "_ = ?RHS")
proof (intro set_eqI)
  fix b
  have "b \<in> ?RHS \<longleftrightarrow> (a, b) \<in> corr_graph \<Gamma>" by simp
  also have "\<dots> \<longleftrightarrow> b \<in> \<Gamma> a" by (fact corr_graph_iff)
  finally show "b \<in> \<Gamma> a \<longleftrightarrow> b \<in> ?RHS" ..
qed

theorem theorem_1_1:
  shows "\<exists>!\<Gamma>. corr_graph \<Gamma> = G"
proof (intro ex1I)
  let ?\<Gamma> = "\<lambda>a. {b. (a, b) \<in> G}"
  {
    fix a
    have "?\<Gamma> a = {b. (a, b) \<in> G}" ..
  }
  thus "corr_graph ?\<Gamma> = G" by (intro corr_graph_eqI)
  fix \<Gamma>
  assume *: "corr_graph \<Gamma> = G"
  {
    fix a
    from * have "\<Gamma> a = ?\<Gamma> a" by (fact corr_graph_eqD)
  }
  thus "\<Gamma> = ?\<Gamma>" ..
qed

lemma corr_graph_inject:
  assumes "corr_graph \<Gamma> = corr_graph \<Gamma>'"
  shows "\<Gamma> = \<Gamma>'"
  using assms theorem_1_1 by metis

definition corr_dom :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set"
  where "corr_dom \<Gamma> = {a. \<exists>b. (a, b) \<in> corr_graph \<Gamma>}"

lemma corr_dom_iff:
  shows "a \<in> corr_dom \<Gamma> \<longleftrightarrow> (\<exists>b. b \<in> \<Gamma> a)" (is "?L \<longleftrightarrow> ?R")
  by (simp add: corr_dom_def corr_graph_iff)

lemma corr_domI:
  assumes "b \<in> \<Gamma> a"
  shows "a \<in> corr_dom \<Gamma>"
  using assms by (auto simp only: corr_dom_iff)

lemma corr_domE:
  assumes "a \<in> corr_dom \<Gamma>"
  obtains b where "b \<in> \<Gamma> a"
  using assms by (auto simp only: corr_dom_iff)

lemma corr_graph_imp_corr_dom:
  assumes "(a, b) \<in> corr_graph \<Gamma>"
  shows "a \<in> corr_dom \<Gamma>"
  using assms by (auto simp only: corr_graph_iff intro: corr_domI)

definition corr_range :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set"
  where "corr_range \<Gamma> = {b. \<exists>a. (a, b) \<in> corr_graph \<Gamma>}"

lemma corr_range_iff:
  shows "b \<in> corr_range \<Gamma> \<longleftrightarrow> (\<exists>a. b \<in> \<Gamma> a)"
  by (simp add: corr_range_def corr_graph_iff)

lemma corr_rangeI:
  assumes "b \<in> \<Gamma> a"
  shows "b \<in> corr_range \<Gamma>"
  using assms by (auto simp only: corr_range_iff)

lemma corr_range_subsetD:
  assumes "corr_range \<Gamma> \<subseteq> B"
  shows "\<Gamma> a \<subseteq> B"
proof (intro subsetI)
  fix b
  assume "b \<in> \<Gamma> a"
  hence "b \<in> corr_range \<Gamma>" by (fact corr_rangeI)
  with assms show "b \<in> B" ..
qed

lemma corr_graph_imp_corr_range:
  assumes "(a, b) \<in> corr_graph \<Gamma>"
  shows "b \<in> corr_range \<Gamma>"
  using assms by (auto simp only: corr_graph_iff intro: corr_rangeI)

lemma corr_graph_subset_Times:
  assumes "corr_dom \<Gamma> \<subseteq> A" and
    "corr_range \<Gamma> \<subseteq> B"
  shows "corr_graph \<Gamma> \<subseteq> A \<times> B"
proof (intro subsetI, split_pair)
  fix a and b
  assume "(a, b) \<in> corr_graph \<Gamma>"
  hence "(a, b) \<in> corr_graph \<Gamma>" by simp
  hence "a \<in> corr_dom \<Gamma>" and "b \<in> corr_range \<Gamma>"
    by (fact corr_graph_imp_corr_dom, fact corr_graph_imp_corr_range)
  with assms show "(a, b) \<in> A \<times> B" by blast
qed

definition corr_inv :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b \<Rightarrow> 'a set"
  where "corr_inv \<Gamma> b = {a. b \<in> \<Gamma> a}"

lemma mem_corr_inv_iff:
  shows "a \<in> corr_inv \<Gamma> b \<longleftrightarrow> b \<in> \<Gamma> a"
  by (simp add: corr_inv_def)

lemma mem_corr_invI:
  assumes "b \<in> \<Gamma> a"
  shows "a \<in> corr_inv \<Gamma> b"
  using assms by (simp only: mem_corr_inv_iff)

lemma corr_graph_imp_mem_corr_inv:
  assumes "(a, b) \<in> corr_graph \<Gamma>"
  shows "a \<in> corr_inv \<Gamma> b"
  using assms by (auto simp only: corr_graph_iff intro: mem_corr_invI)

proposition prop_1_3_2:
  shows "b \<in> \<Gamma> a \<longleftrightarrow> a \<in> corr_inv \<Gamma> b"
  by (simp only: mem_corr_inv_iff)

proposition prop_1_3_3_a:
  shows "corr_dom (corr_inv \<Gamma>) = corr_range \<Gamma>" (is "?L = ?R")
proof (intro set_eqI)
  fix b
  have "b \<in> ?L \<longleftrightarrow> (\<exists>a. a \<in> (corr_inv \<Gamma>) b)" by (simp only: corr_dom_iff)
  also have "\<dots> \<longleftrightarrow> (\<exists>a. b \<in> \<Gamma> a)" by (simp only: mem_corr_inv_iff)
  also have "\<dots> \<longleftrightarrow> b \<in> ?R" by (simp only: corr_range_iff)
  finally show "b \<in> ?L \<longleftrightarrow> b \<in> ?R" .
qed

proposition prop_1_3_3_b:
  shows "corr_range (corr_inv \<Gamma>) = corr_dom \<Gamma>" (is "?L = ?R")
proof (intro set_eqI)
  fix a
  have "a \<in> ?L \<longleftrightarrow> (\<exists>b. a \<in> corr_inv \<Gamma> b)" by (simp only: corr_range_iff)
  also have "\<dots> \<longleftrightarrow> (\<exists>b. b \<in> \<Gamma> a)" by (simp only: mem_corr_inv_iff)
  also have "\<dots> \<longleftrightarrow> a \<in> ?R" by (simp only: corr_dom_iff)
  finally show "a \<in> ?L \<longleftrightarrow> a \<in> ?R" .
qed

proposition prop_1_3_4:
  shows "corr_inv (corr_inv \<Gamma>) = \<Gamma>" (is "?L = _")
proof (intro ext)
  fix a
  {
    fix b
    have "b \<in> ?L a \<longleftrightarrow> a \<in> (corr_inv \<Gamma>) b" by (simp only: mem_corr_inv_iff)
    also have "\<dots> \<longleftrightarrow> b \<in> \<Gamma> a" by (simp only: mem_corr_inv_iff)
    finally have "b \<in> ?L a \<longleftrightarrow> b \<in> \<Gamma> a" .
  }
  thus "?L a = \<Gamma> a" by (rule set_eqI)
qed

definition as_corr_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b set"
  where "as_corr_on f A a = (if a \<in> A then {f a} else {})"

text {*
  @{const as_corr_on} transforms a function into the correspondence. Since a function
  @{term "f :: 'a \<Rightarrow> 'b"} in Isabelle/HOL is total, which means that the function is always defined
  on the universal set @{term "UNIV :: 'a set"} of the type @{typ 'a}, @{const as_corr_on}
  additionally specifies a set of the type @{typ "'a set"} that should be considered as the domain
  of the function.
*}

lemma as_corr_on_eq:
  assumes "a \<in> A"
  shows "as_corr_on f A a = {f a}"
  using assms by (simp add: as_corr_on_def)

lemma as_corr_on_eq_empty:
  assumes "a \<notin> A"
  shows "as_corr_on f A a = {}"
  using assms by (simp add: as_corr_on_def)

lemma as_corr_on_eq2:
  shows "as_corr_on f A a = {b. a \<in> A \<and> b = f a}"
proof -
  {
    assume "a \<in> A"
    hence "as_corr_on f A a = {f a}" by (fact as_corr_on_eq)
    also from \<open>a \<in> A\<close> have "\<dots> = {b. a \<in> A \<and> b = f a}" by simp
    finally have "?thesis" .
  }
  moreover {
    assume "a \<notin> A"
    hence "as_corr_on f A a = {}" by (fact as_corr_on_eq_empty)
    also from \<open>a \<notin> A\<close> have "\<dots> = {b. a \<in> A \<and> b = f a}" by simp
    finally have "?thesis" .
  }
  ultimately show "?thesis" by blast
qed

lemma mem_as_corr_on_iff:
  assumes "a \<in> A"
  shows "b \<in> as_corr_on f A a \<longleftrightarrow> b = f a"
  using assms by (simp add: as_corr_on_eq)

lemma corr_graph_fun_eq:
  shows "corr_graph (as_corr_on f A) = {(a, b). a \<in> A \<and> b = f a}" (is "?L = ?R")
proof (intro set_eqI, split_pair)
  fix a and b
  {
    assume "a \<in> A"
    have "(a, b) \<in> ?L \<longleftrightarrow> b \<in> as_corr_on f A a" by (simp only: corr_graph_iff)
    also from \<open>a \<in> A\<close> have "\<dots> \<longleftrightarrow> b = f a" by (simp only: mem_as_corr_on_iff)
    also from \<open>a \<in> A\<close> have "\<dots> \<longleftrightarrow> (a, b) \<in> ?R" by simp
    finally have "(a, b) \<in> ?L \<longleftrightarrow> (a, b) \<in> ?R" .
  }
  moreover {
    assume "a \<notin> A"
    have "(a, b) \<in> ?L \<longleftrightarrow> b \<in> as_corr_on f A a" by (simp only: corr_graph_iff)
    also from \<open>a \<notin> A\<close> have "\<dots> \<longleftrightarrow> b \<in> {}" by (simp add: as_corr_on_eq_empty)
    also from \<open>a \<notin> A\<close> have "\<dots> \<longleftrightarrow> (a, b) \<in> ?R" by simp
    finally have "(a, b) \<in> ?L \<longleftrightarrow> (a, b) \<in> ?R" .
  }
  ultimately show "(a, b) \<in> ?L \<longleftrightarrow> (a, b) \<in> ?R" by auto
qed

definition corr_functional_on :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "corr_functional_on \<Gamma> A \<longleftrightarrow> (\<forall>a. (a \<in> A \<longrightarrow> (\<exists>!b. b \<in> \<Gamma> a)) \<and> (a \<notin> A \<longrightarrow> \<Gamma> a = {}))"

definition id_on :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "id_on f A \<longleftrightarrow> (\<forall>a \<in> A. f a = a)"

text {*
  @{prop "id_on f A"} states that the function @{term f} behaves as an identity function on the set
  @{term A}. This proposition does not specify any other property of @{term f} on an element out of
  @{term A}.
*}

lemmas id_on_iff = id_on_def

lemma id_onI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a = a"
  shows "id_on f A"
  using assms by (simp add: id_on_def)

lemma id_onD:
  assumes "id_on f A" and
    "a \<in> A"
  shows "f a = a"
  using assms by (simp only: id_on_def)

lemma id_on_empty:
  shows "id_on f {}"
  by (simp add: id_on_def)

lemma set_eqI2:
  assumes "\<And>x. x \<in> A \<Longrightarrow> x \<in> B" and
    "\<And>x. x \<in> B \<Longrightarrow> x \<in> A"
  shows "A = B"
  using assms by blast

lemma surj_onI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<in> B" and
    "\<And>b. b \<in> B \<Longrightarrow> \<exists>a \<in> A. f a = b"
  shows "f ` A = B"
proof (rule set_eqI2)
  fix b
  assume "b \<in> f ` A"
  then obtain a where "a \<in> A" and "b = f a" by auto
  thus "b \<in> B" by (auto intro: assms(1))
next
  fix b
  assume "b \<in> B"
  then obtain a where "a \<in> A" and "f a = b" using assms(2) by blast
  thus "b \<in> f ` A" by auto
qed

lemma id_on_imp_surj_on:
  assumes "id_on f A"
  shows "f ` A = A"
proof (rule surj_onI)
  fix a
  assume "a \<in> A"
  with assms show "f a \<in> A" by (auto dest: id_onD)
next
  fix a
  assume "a \<in> A"
  with assms have "f a = a" by (auto dest: id_onD)
  with \<open>a \<in> A\<close> show "\<exists>a' \<in> A. f a' = a" by auto
qed

lemma id_on_imp_inj_on:
  assumes "id_on f A"
  shows "inj_on f A"
proof (rule inj_onI)
  fix a and a'
  assume "a \<in> A" and
    "a' \<in> A" and
    "f a = f a'"
  with assms show "a = a'" using id_onD by fastforce
qed

lemma id_on_imp_bij_betw:
  assumes "id_on f A"
  shows "bij_betw f A A"
  using assms by (auto dest: id_on_imp_surj_on id_on_imp_inj_on intro: bij_betw_imageI)

lemma theorem_1_2':
  assumes -- {* @{prop "G \<subseteq> A \<times> B"}: an unnecessary assumption. *}
    "f ` A \<subseteq> B" and
    "corr_graph (as_corr_on f A) = G"
  shows "\<forall>a \<in> A. \<exists>!b \<in> B. (a, b) \<in> G"
proof (intro ballI)
  fix a
  assume "a \<in> A"
  with assms(1) have "f a \<in> B" by auto
  moreover have "(a, f a) \<in> G"
  proof -
    from assms(2) have "(as_corr_on f A) a = {b. (a, b) \<in> G}" by (fact corr_graph_eqD)
    with \<open>a \<in> A\<close> have "{f a} = {b. (a, b) \<in> G}" by (simp only: as_corr_on_eq)
    thus "?thesis" by blast
  qed
  moreover {
    fix b
    assume "b \<in> B" and
      "(a, b) \<in> G"
    from this(2) and assms(2) have "b \<in> (as_corr_on f A) a" by (auto simp only: corr_graph_iff)
    with \<open>a \<in> A\<close> have "b = f a" by (simp add: as_corr_on_eq)
  }
  ultimately show "\<exists>!b \<in> B. (a, b) \<in> G" by blast
qed

lemma theorem_1_2'':
  assumes "G \<subseteq> A \<times> B" and
    "\<forall>a \<in> A. \<exists>!b \<in> B. (a, b) \<in> G"
  obtains f where "f ` A \<subseteq> B" and
    "corr_graph (as_corr_on f A) = G"
proof -
  let ?f = "\<lambda>a. (THE b. b \<in> B \<and> (a, b) \<in> G)" -- {* Returns a unspecified value for @{term "a \<notin> A"}. *}
  have *: "?f a \<in> B \<and> (a, ?f a) \<in> G" if "a \<in> A" for a
  proof (intro theI[where ?P = "\<lambda>b. b \<in> B \<and> (a, b) \<in> G"])
    from that and assms(2) have *: "\<exists>!b \<in> B. (a, b) \<in> G" by simp
    thus **: "?f a \<in> B \<and> (a, ?f a) \<in> G" by (rule theI')
    fix b
    assume "b \<in> B \<and> (a, b) \<in> G"
    with * and ** show "b = ?f a" by blast
  qed
  from * have "?f ` A \<subseteq> B" by blast
  moreover have "corr_graph (as_corr_on ?f A) = G" (is "?L = _")
  proof -
    have "corr_graph (as_corr_on ?f A) = {(a, b). a \<in> A \<and> b = ?f a}" by (fact corr_graph_fun_eq)
    also have "\<dots> = G"
    proof (intro set_eqI, split_pair)
      fix a and b
      have "(a, b) \<in> {(a, b). a \<in> A \<and> b = ?f a} \<longleftrightarrow> a \<in> A \<and> b = ?f a" by simp
      also from * have "\<dots> \<longleftrightarrow> a \<in> A \<and> b = ?f a \<and> ?f a \<in> B \<and> (a, ?f a) \<in> G" by blast
      also have "\<dots> \<longleftrightarrow> a \<in> A \<and> b \<in> B \<and> (a, b) \<in> G"
      proof (intro iffI)
        assume "a \<in> A \<and> b = ?f a \<and> ?f a \<in> B \<and> (a, ?f a) \<in> G"
        thus "a \<in> A \<and> b \<in> B \<and> (a, b) \<in> G" by simp
      next
        assume **: "a \<in> A \<and> b \<in> B \<and> (a, b) \<in> G"
        moreover from this and * have ***: "?f a \<in> B" and "(a, ?f a) \<in> G" by simp+
        moreover note assms(2)
        ultimately have "b = ?f a" by blast
        with ** and *** show "a \<in> A \<and> b = ?f a \<and> ?f a \<in> B \<and> (a, ?f a) \<in> G" by simp
      qed
      also from assms(1) have "\<dots> \<longleftrightarrow> (a, b) \<in> G" by auto
      finally show "(a, b) \<in> {(a, b). a \<in> A \<and> b = ?f a} \<longleftrightarrow> (a, b) \<in> G" .
    qed
    finally show "?thesis" .
  qed
  ultimately show "thesis" by (rule that)
qed

theorem theorem_1_2:
  assumes "G \<subseteq> A \<times> B"
  shows "(\<exists>f. f ` A \<subseteq> B \<and> corr_graph (as_corr_on f A) = G) \<longleftrightarrow> (\<forall>a \<in> A. \<exists>!b \<in> B. (a, b) \<in> G)"
    (is "?L \<longleftrightarrow> ?R")
proof (intro iffI)
  assume "?L"
  then obtain f where "f ` A \<subseteq> B" and "corr_graph (as_corr_on f A) = G" by blast
  thus "?R" by (elim theorem_1_2')
next
  assume "?R"
  with assms obtain f where "f ` A \<subseteq> B" and "corr_graph (as_corr_on f A) = G"
    by (elim theorem_1_2'')
  thus "?L" by auto
qed

(* TODO: problem_1_3_1 *)
(* TODO: problem_1_3_2 *)

proposition problem_1_3_3':
  assumes (*"corr_graph \<Gamma> \<subseteq> A \<times> B" and*)
    -- {* Since @{prop "corr_dom \<Gamma> = A"}* is an assumption, the assumption
          @{prop "corr_graph \<Gamma> \<subseteq> A \<times> B"} can be replaced by @{prop "corr_range \<Gamma> \<subseteq> B"}*}
    "corr_range \<Gamma> \<subseteq> B" and
    "corr_dom \<Gamma> = A" and
    "\<And>b b'. b \<in> B \<Longrightarrow> b' \<in> B \<Longrightarrow> b \<noteq> b' \<Longrightarrow> corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' = {}"
  obtains f where "f ` A \<subseteq> B" and "as_corr_on f A = \<Gamma>"
proof -
  {
    fix a
    assume "a \<in> A"
    with assms(2) obtain b where *: "b \<in> \<Gamma> a" using corr_domE by metis
    with assms(1) have "b \<in> B" using corr_range_subsetD by fast
    moreover from * have "(a, b) \<in> corr_graph \<Gamma>" by (fact corr_graphI)
    moreover {
      fix b'
      assume "b' \<in> B" and "(a, b') \<in> corr_graph \<Gamma>"
      {
        assume "b' \<noteq> b"
        moreover note \<open>b \<in> B\<close> and \<open>b' \<in> B\<close>
        moreover have "corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' \<noteq> {}"
        proof -
          from \<open>b \<in> \<Gamma> a\<close> have "a \<in> corr_inv \<Gamma> b" by (fact mem_corr_invI)
          moreover from \<open>(a, b') \<in> corr_graph \<Gamma>\<close> have "a \<in> corr_inv \<Gamma> b'"
            by (rule corr_graph_imp_mem_corr_inv)
          ultimately show "?thesis" by auto
        qed
        ultimately have "False" using assms(3) by simp
      }
      hence "b' = b" by auto
    }
    ultimately have "\<exists>!b \<in> B. (a, b) \<in> corr_graph \<Gamma>" by blast
  }
  hence "\<forall>a \<in> A. \<exists>!b \<in> B. (a, b) \<in> corr_graph \<Gamma>" ..
  moreover from assms(1,2) have "corr_graph \<Gamma> \<subseteq> A \<times> B" using corr_graph_subset_Times by blast
  ultimately obtain f where "f ` A \<subseteq> B" and "corr_graph (as_corr_on f A) = corr_graph \<Gamma>"
    by (elim theorem_1_2'')
  hence "as_corr_on f A = \<Gamma>" by (elim corr_graph_inject)
  with \<open>f ` A \<subseteq> B\<close> show "thesis" by (rule that)
qed

lemma mem_corr_invD:
  assumes "a \<in> corr_inv \<Gamma> b"
  shows "b \<in> \<Gamma> a"
  using assms by (simp only: mem_corr_inv_iff)

lemma mem_corr_inv_imp_corr_graph:
  assumes "a \<in> corr_inv \<Gamma> b"
  shows "(a, b) \<in> corr_graph \<Gamma>"
  using assms by (auto intro: corr_graphI elim: mem_corr_invD)

proposition problem_1_3_3'':
  assumes (*"corr_graph \<Gamma> \<subseteq> A \<times> B" and*)
    -- {* Original assumptions would include @{prop "corr_graph \<Gamma> \<subseteq> A \<times> B"} but it can be weakened
          to the assumption @{prop "corr_dom \<Gamma> \<subseteq> A"}. *}
    "corr_dom \<Gamma> \<subseteq> A" and
    "f ` A \<subseteq> B" and
    "as_corr_on f A = \<Gamma>"
  shows "corr_dom \<Gamma> = A" and
    "\<And>b b'. b \<in> B \<Longrightarrow> b' \<in> B \<Longrightarrow> b \<noteq> b' \<Longrightarrow> corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' = {}"
proof -
  from assms(3) have "corr_graph (as_corr_on f A) = corr_graph \<Gamma>" by simp
  with assms(2) have *: "\<forall>a \<in> A. \<exists>!b \<in> B. (a, b) \<in> corr_graph \<Gamma>" by (rule theorem_1_2')
  note assms(1)
  moreover have "A \<subseteq> corr_dom \<Gamma>"
  proof (intro subsetI)
    fix a
    assume "a \<in> A"
    with * obtain b where "b \<in> B" and "(a, b) \<in> corr_graph \<Gamma>" by blast
    from this(2) show "a \<in> corr_dom \<Gamma>" by (fact corr_graph_imp_corr_dom)
  qed
  ultimately show "corr_dom \<Gamma> = A" ..
  fix b and b'
  assume "b \<in> B" and
    "b' \<in> B" and
    "b \<noteq> b'"
  {
    fix a
    assume "a \<in> corr_inv \<Gamma> b" and
      "a \<in> corr_inv \<Gamma> b'"
    hence "(a, b) \<in> corr_graph \<Gamma>" and
      "(a, b') \<in> corr_graph \<Gamma>" by (elim mem_corr_inv_imp_corr_graph)+
    moreover from \<open>(a, b) \<in> corr_graph \<Gamma>\<close> and assms(1) have "a \<in> A"
      by (auto elim: corr_graph_imp_corr_dom)
    moreover note \<open>b \<in> B\<close> and \<open>b' \<in> B\<close>
    ultimately have "b = b'" using * by auto
    with \<open>b \<noteq> b'\<close> have "False" ..
  }
  thus "corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' = {}" by auto
qed

proposition problem_1_3_3:
  assumes "corr_dom \<Gamma> \<subseteq> A" and
    "corr_range \<Gamma> \<subseteq> B"
  shows "corr_dom \<Gamma> = A \<and> (\<forall>b \<in> B. \<forall>b' \<in> B. b \<noteq> b' \<longrightarrow> corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' = {}) \<longleftrightarrow>
         (\<exists>f. f ` A \<subseteq> B \<and> as_corr_on f A = \<Gamma>)" (is "?L \<longleftrightarrow> ?R")
proof (intro iffI)
  assume "?L"
  hence "corr_dom \<Gamma> = A" and
    "\<And>b b'. b \<in> B \<Longrightarrow> b' \<in> B \<Longrightarrow> b \<noteq> b' \<Longrightarrow> corr_inv \<Gamma> b \<inter> corr_inv \<Gamma> b' = {}" by simp+
  with assms(2) obtain f where "f ` A \<subseteq> B" and "as_corr_on f A = \<Gamma>" by (rule problem_1_3_3')
  thus "?R" by auto
next
  assume "?R"
  then obtain f where "f ` A \<subseteq> B" and "as_corr_on f A = \<Gamma>" by auto
  with assms(1) show "?L" using problem_1_3_3'' by metis
qed

proposition problem_1_3_4_a:
  assumes "id_on f A"
  shows "corr_graph (as_corr_on f A) = {(a, b). a \<in> A \<and> b = a}" (is "?L = ?R")
proof -
  have "?L = {(a, b). a \<in> A \<and> b = f a}" by (fact corr_graph_fun_eq)
  also from assms have "\<dots> = ?R" by (auto simp add: id_on_iff)
  finally show "?thesis" .
qed

proposition problem_1_3_4_b:
  assumes "\<forall>a \<in> A. f a = b\<^sub>0"
  shows "corr_graph (as_corr_on f A) = {(a, b). a \<in> A \<and> b = b\<^sub>0}" (is "?L = ?R")
proof -
  have "?L = {(a, b). a \<in> A \<and> b = f a}" by (fact corr_graph_fun_eq)
  also from assms have "\<dots> = ?R" by auto
  finally show "?thesis" .
qed

end
