theory Section_1_4
  imports Main
    "Section_1_3"
begin

section "Various Concepts on Functions"

text {*
  In this and the following sections, functions in usual mathematics are formalized in terms of
  functions in Isabelle/HOL. Because careful handling is required in such formalization, let me
  explain the detail.

  Functions in usual mathematics are associated with its domain and codomain. The careful handling
  is required in their formalization. A function in Isabelle/HOL (say, @{term "f :: 'a \<Rightarrow> 'b"}) is
  associated with the domain (the universal set of the type @{typ 'a}) and the codomain (the
  universal set of the type @{typ 'b}). However, because (the universal set of) types in
  Isabelle/HOL are not expressive enough to encode an arbitrary set (which is equivalent to an
  arbitrary proposition under the axiom schema of comprehension in Isabelle/HOL), a subset of the
  universal set of the type @{typ 'a} is needed to be explicitly specified in order to formalize
  the domain of a function in usual mathematics.

  As a result, a function @{term f} in Isabelle/HOL that formalizes a function in usual mathematics
  has "two domains"; one is the original one, i.e., the universal set of the type @{typ 'a}, and
  the other is the one that is explicitly specified in order to express the domain of the function
  in usual mathematics.

  Let @{term "A :: 'a set"} be a set that is specified to express the domain of a function in usual
  mathematics. It should be always noted that the function in Isabelle/HOL is defined on
  @{term "-A"}. This fact is essentially different from the function in usual mathematics - it is
  simply undefined out of @{term "A"}. This difference demands careful handling. The statement of
  definitions and propositions concerning functions in usual mathematics should be properly
  rephrased to reflect the difference.

  The codomain is explicitly specified as a set @{term "B :: 'b set"} such that @{prop "f ` A \<subseteq> B"}
  only when it is actually required in definitions and propositions.

  The inverse image of a set @{term "Q \<subseteq> B"} under @{term f} is defined @{term "f -` Q \<inter> A"} since
  @{term "f -` Q"} could include an element out of @{term "A"}.

  Surjectivity is stated as the proposition @{term "f ` A = B"}.

  Injectivity is stated as the proposition @{term "inj_on f A"}.

  TODO: Inverses, (extensional) equality)
*}

text {* Extensional equality of two function on a set. *}

definition ext_eq_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "ext_eq_on A f f' \<longleftrightarrow> (\<forall>a \<in> A. f a = f' a)"

lemma ext_eq_onI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a = f' a"
  shows "ext_eq_on A f f'"
  using ext_eq_on_def assms by blast

lemma ext_eq_onD:
  assumes "ext_eq_on A f f'"
    and "a \<in> A"
  shows "f a = f' a"
  using assms by (simp only: ext_eq_on_def)

lemma ext_eq_on_refl:
  shows "ext_eq_on A f f"
  by (simp add: ext_eq_on_def)

lemma ext_eq_on_sym:
  assumes "ext_eq_on A f f'"
  shows "ext_eq_on A f' f"
  using assms by (simp add: ext_eq_on_def)

lemma ext_eq_on_trans:
  assumes "ext_eq_on A f g"
    and "ext_eq_on A g h"
  shows "ext_eq_on A f h"
  using assms by (simp add: ext_eq_on_def)

lemma ext_eq_on_empty:
  shows "ext_eq_on {} f g"
  by (simp add: ext_eq_on_def)

proposition prop_1_4_1:
  assumes -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption.*}
    -- {* @{prop "P\<^sub>1 \<subseteq> A"}: an unnecessary assumption. *}
    -- {* @{prop "P\<^sub>2 \<subseteq> A"}: an unnecessary assumption. *}
    "P\<^sub>1 \<subseteq> P\<^sub>2"
  shows "f ` P\<^sub>1 \<subseteq> f ` P\<^sub>2"
proof (rule subsetI)
  fix b
  assume "b \<in> f ` P\<^sub>1"
  then obtain a where "a \<in> P\<^sub>1" and "b = f a" by auto
  from this(1) and assms have "a \<in> P\<^sub>2" by auto
  with \<open>b = f a\<close> show "b \<in> f ` P\<^sub>2" by simp
qed

proposition prop_1_4_2:
  -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
  -- {* @{prop "P\<^sub>1 \<subseteq> A"}: an unnecessary assumption. *}
  -- {* @{prop "P\<^sub>2 \<subseteq> A"}: an unnecessary assumption. *}
  shows "f ` (P\<^sub>1 \<union> P\<^sub>2) = f ` P\<^sub>1 \<union> f ` P\<^sub>2" (is "?L = ?R")
proof (rule set_eqI)
  fix b
  have "b \<in> ?L \<longleftrightarrow> (\<exists>a \<in> P\<^sub>1 \<union> P\<^sub>2. b = f a)" by blast
  also have "\<dots> \<longleftrightarrow> (\<exists>a \<in> P\<^sub>1. b = f a) \<or> (\<exists>a \<in> P\<^sub>2. b = f a)" by blast
  also have "\<dots> \<longleftrightarrow> b \<in> ?R" by blast
  finally show "b \<in> ?L \<longleftrightarrow> b \<in> ?R" .
qed

proposition prop_1_4_3:
  -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
  -- {* @{prop "P\<^sub>1 \<subseteq> A"}: an unnecessary assumption. *}
  -- {* @{prop "P\<^sub>2 \<subseteq> A"}: an unnecessary assumption. *}
  shows "f ` (P\<^sub>1 \<inter> P\<^sub>2) \<subseteq> f ` P\<^sub>1 \<inter> f ` P\<^sub>2"
proof (rule subsetI)
  fix b
  assume "b \<in> f ` (P\<^sub>1 \<inter> P\<^sub>2)"
  then obtain a where "a \<in> P\<^sub>1" and "a \<in> P\<^sub>2" and "b = f a" by blast
  hence "b \<in> f ` P\<^sub>1" and "b \<in> f ` P\<^sub>2" by simp+
  thus "b \<in> f ` P\<^sub>1 \<inter> f ` P\<^sub>2" ..
qed

proposition prop_1_4_4:
  -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
  -- {* @{prop "P \<subseteq> A"}: an unnecessary assumption. *}
  shows "f ` (A - P) \<supseteq> f ` A - f ` P"
proof (rule subsetI)
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
  assumes -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    -- {* @{prop "Q\<^sub>1 \<subseteq> B"}: an unnecessary assumption. *}
    -- {* @{prop "Q\<^sub>2 \<subseteq> B"}: an unnecessary assumption. *}
    "Q\<^sub>1 \<subseteq> Q\<^sub>2"
  shows "(f -` Q\<^sub>1) \<inter> A \<subseteq> (f -` Q\<^sub>2) \<inter> A"
proof (rule subsetI)
  fix a
  assume "a \<in> f -` Q\<^sub>1 \<inter> A"
  hence "f a \<in> Q\<^sub>1" and "a \<in> A" by auto
  from this(1) assms have "f a \<in> Q\<^sub>2" by auto
  with \<open>a \<in> A\<close> show "a \<in> (f -` Q\<^sub>2) \<inter> A" by simp
qed

proposition prop_1_4_2':
  -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
  -- {* @{prop "Q\<^sub>1 \<subseteq> B"}: an unnecessary assumption. *}
  -- {* @{prop "Q\<^sub>2 \<subseteq> B"}: an unnecessary assumption. *}
  shows "f -` (Q\<^sub>1 \<union> Q\<^sub>2) \<inter> A = (f -` Q\<^sub>1 \<inter> A) \<union> (f -` Q\<^sub>2 \<inter> A)" (is "?L = ?R")
proof (rule set_eqI)
  fix a
  have "a \<in> ?L \<longleftrightarrow> (f a \<in> Q\<^sub>1 \<or> f a \<in> Q\<^sub>2) \<and> a \<in> A" by simp
  also have "\<dots> \<longleftrightarrow> (f a \<in> Q\<^sub>1 \<and> a \<in> A) \<or> (f a \<in> Q\<^sub>2 \<and> a \<in> A)" by auto
  also have "\<dots> \<longleftrightarrow> a \<in> ?R" by simp
  finally show "a \<in> ?L \<longleftrightarrow> a \<in> ?R" .
qed

proposition prop_1_4_3':
  -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
  -- {* @{prop "Q\<^sub>1 \<subseteq> B"}: an unnecessary assumption. *}
  -- {* @{prop "Q\<^sub>2 \<subseteq> B"}: an unnecessary assumption. *}
  shows "f -` (Q\<^sub>1 \<inter> Q\<^sub>2) \<inter> A = (f -` Q\<^sub>1 \<inter> A) \<inter> (f -` Q\<^sub>2 \<inter> A)" (is "?L = ?R")
proof (rule set_eqI)
  fix a
  have "a \<in> ?L \<longleftrightarrow> f a \<in> Q\<^sub>1 \<and> f a \<in> Q\<^sub>2 \<and> a \<in> A" by simp
  also have "\<dots> \<longleftrightarrow> (f a \<in> Q\<^sub>1 \<and> a \<in> A) \<and> (f a \<in> Q\<^sub>2 \<and> a \<in> A)" by auto
  also have "\<dots> \<longleftrightarrow> a \<in> ?R" by simp
  finally show "a \<in> ?L \<longleftrightarrow> a \<in> ?R" .
qed

proposition prop_1_4_4':
  assumes "f ` A \<subseteq> B"
    -- {* @{prop "Q \<subseteq> B"}: an unnecessary assumption. *}
  shows "f -` (B - Q) \<inter> A = A - (f -` Q \<inter> A)" (is "?L = ?R")
proof (rule set_eqI2)
  fix a
  assume "a \<in> ?L"
  hence "f a \<in> B" and "f a \<in> -Q" and "a \<in> A" by simp+
  from this(2) have "a \<notin> f -` Q" by simp
  hence "a \<notin> f -` Q \<inter> A" by simp
  with \<open>a \<in> A\<close> show "a \<in> ?R" ..
next
  fix a
  assume "a \<in> ?R"
  hence "a \<in> A" and "a \<notin> f -` Q" by auto
  from this(1) and assms have "f a \<in> B" by auto
  with \<open>a \<notin> f -` Q\<close> have "f a \<in> B - Q" by simp
  with \<open>a \<in> A\<close> show "a \<in> ?L" by simp
qed

proposition prop_1_4_5:
  assumes
  -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    "P \<subseteq> A"
  shows "(f -` (f ` P)) \<inter> A \<supseteq> P"
proof (rule subsetI)
  fix a
  assume "a \<in> P"
  hence "f a \<in> f ` P" by simp
  moreover from assms and \<open>a \<in> P\<close> have "a \<in> A" by auto
  ultimately show "a \<in> f -` (f ` P) \<inter> A" by simp
qed

proposition prop_1_4_5':
  -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
  -- {* @{prop "Q \<subseteq> B"}: an unnecessary assumption. *}
  shows "f ` ((f -` Q) \<inter> A) \<subseteq> Q"
proof (rule subsetI)
  fix b
  assume "b \<in> f ` (f -` Q \<inter> A)"
  then obtain a where "a \<in> (f -` Q) \<inter> A" and "b = f a" ..
  from this(1) have "f a \<in> Q" by simp
  with \<open>b = f a\<close> show "b \<in> Q" by simp
qed

(*lemma mem_corr_inv_iff:
  shows "a \<in> corr_inv \<Gamma> b \<longleftrightarrow> b \<in> \<Gamma> a"
proof -
  have "a \<in> corr_inv \<Gamma> b \<longleftrightarrow> a \<in> {a. b \<in> \<Gamma> a}" by (simp only: corr_inv_def)
  also have "\<dots> \<longleftrightarrow> b \<in> \<Gamma> a" by (fact mem_Collect_eq)
  finally show "?thesis" .
qed*)

(*lemma bex1D:
  assumes "\<exists>!x \<in> X. P x" and "a \<in> X" and "P a" and "b \<in> X" and "P b"
  shows "a = b"
proof -
  from assms(1) have "\<forall>x \<in> X. \<forall>y \<in> X. P x \<longrightarrow> P y \<longrightarrow> x = y" by auto
  with assms(2-5) show "a = b" by fast
qed*)

lemma corr_inv_fun_fun:
  assumes "a \<in> A"
  shows "corr_inv (as_corr_on f A) (f a) = {a' \<in> A. f a' = f a}" (is "?L = ?R")
proof (rule set_eqI)
  fix a'
  have "a' \<in> ?L \<longleftrightarrow> f a \<in> as_corr_on f A a'" by (fact mem_corr_inv_iff)
  also have "\<dots> \<longleftrightarrow> f a \<in> {b. a' \<in> A \<and> b = f a'}" by (simp only: as_corr_on_eq2)
  also have "\<dots> \<longleftrightarrow> a' \<in> A \<and> f a = f a'" by auto
  also have "\<dots> \<longleftrightarrow> a' \<in> ?R" by auto
  finally show "a' \<in> ?L \<longleftrightarrow> a' \<in> ?R" .
qed

lemma corr_inv_fun_eq:
  shows "corr_inv (as_corr_on f A) b = {a \<in> A. f a = b}" (is "?L = ?R")
proof (rule set_eqI)
  fix a
  have "a \<in> ?L \<longleftrightarrow> b \<in> as_corr_on f A a" by (fact mem_corr_inv_iff)
  also have "\<dots> \<longleftrightarrow> a \<in> A \<and> f a = b" by (auto simp add: as_corr_on_eq2)
  also have "\<dots> \<longleftrightarrow> a \<in> ?R" by simp
  finally show "a \<in> ?L \<longleftrightarrow> a \<in> ?R" .
qed

theorem theorem_1_4':
  assumes "f ` A \<subseteq> B" and
    "as_corr_on g B = corr_inv (as_corr_on f A)"
  shows "bij_betw f A B"
proof (rule bij_betw_imageI)
  {
    fix a and a'
    assume "a \<in> A" and
      "a' \<in> A" and
      "f a = f a'"
    from \<open>a \<in> A\<close> and assms(1) have "f a \<in> B" by auto
    moreover from assms(2) have "corr_inv (as_corr_on f A) (f a) = as_corr_on g B (f a)" by simp
    with \<open>a \<in> A\<close> and \<open>f a \<in> B\<close> have **: "{a'' \<in> A. f a'' = f a} = {g (f a)}"
      by (simp add: corr_inv_fun_fun as_corr_on_eq)
    with \<open>a \<in> A\<close> have "a = g (f a)" by blast
    moreover from ** and \<open>a' \<in> A\<close> and \<open>f a = f a'\<close> have "a' = g (f a)" by auto
    ultimately have "a = a'" by simp
  }
  thus "inj_on f A" by (rule inj_onI)
  {
    fix a
    assume "a \<in> A"
    with assms(1) have "f a \<in> B" by auto
  }
  moreover {
    fix b
    assume "b \<in> B"
    moreover from assms(2) have "corr_inv (as_corr_on f A) b = as_corr_on g B b" by simp
    ultimately have "{a \<in> A. f a = b} = {g b}" by (simp only: corr_inv_fun_eq as_corr_on_eq)
    hence "g b \<in> A" and "f (g b) = b" by auto
    hence "\<exists>a \<in> A. f a = b" by blast
  }
  ultimately show "f ` A = B" by (intro surj_onI)
qed

theorem theorem_1_4'':
  assumes "f ` A \<subseteq> B" and
    "bij_betw f A B"
  obtains g where "as_corr_on g B = corr_inv (as_corr_on f A)"
proof -
  {
    fix b
    {
      assume "b \<in> B"
      from assms(2) have "f ` A = B" and "inj_on f A"
        by (fact bij_betw_imp_surj_on, fact bij_betw_imp_inj_on)
      from this(1) and \<open>b \<in> B\<close> obtain a where "a \<in> A" and "b = f a" by auto
      {
        fix a'
        assume \<open>a' \<in> A\<close>
        with \<open>a \<in> A\<close> and \<open>inj_on f A\<close> have "a' = a \<longleftrightarrow> f a' = f a" by (simp only: inj_on_eq_iff)
        with \<open>a' \<in> A\<close> have "a' \<in> {a'. a' = a} \<longleftrightarrow> a' \<in> {a'. f a' = f a}" by simp
      }
      hence "{a' \<in> A. a' = a} = {a' \<in> A. f a' = f a}" by auto
      with \<open>a \<in> A\<close> have "{a'. a' = a} = {a' \<in> A. f a' = f a}" by blast
      with \<open>inj_on f A\<close> and \<open>a \<in> A\<close>
      have "{a'. a' = the_inv_into A f (f a)} = {a' \<in> A. f a' = f a}"
        by (simp only: the_inv_into_f_f)
      with \<open>b = f a\<close> have "{a. a = (the_inv_into A f) b} = {a \<in> A. f a = b}" by simp
      with \<open>b \<in> B\<close> have "as_corr_on (the_inv_into A f) B b = corr_inv (as_corr_on f A) b"
        by (simp add: as_corr_on_eq2 corr_inv_fun_eq)
    }
    moreover {
      assume "b \<notin> B"
      with assms(1) have "{a \<in> A. f a = b} = {}" by blast
      with \<open>b \<notin> B\<close> have "as_corr_on (the_inv_into A f) B b = corr_inv (as_corr_on f A) b"
        by (simp add: as_corr_on_eq_empty corr_inv_fun_eq)
    }
    ultimately have "as_corr_on (the_inv_into A f) B b = corr_inv (as_corr_on f A) b" by auto
  }
  hence "as_corr_on (the_inv_into A f) B = corr_inv (as_corr_on f A)" by auto
  thus "thesis" by (fact that)
qed

theorem theorem_1_4:
  assumes "f ` A \<subseteq> B"
  shows "(\<exists>g. as_corr_on g B = corr_inv (as_corr_on f A)) \<longleftrightarrow> bij_betw f A B"
proof (rule iffI)
  assume "\<exists>g. as_corr_on g B = corr_inv (as_corr_on f A)"
  then obtain g where "as_corr_on g B = corr_inv (as_corr_on f A)" by auto
  with assms show "bij_betw f A B" using theorem_1_4' by fast
next
  assume "bij_betw f A B"
  with assms obtain g where "as_corr_on g B = corr_inv (as_corr_on f A)" by (elim theorem_1_4'')
  thus "\<exists>g. as_corr_on g B = corr_inv (as_corr_on f A)" by auto
qed

definition is_inv_into :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "is_inv_into A f g \<longleftrightarrow> corr_inv (as_corr_on g (f ` A)) = as_corr_on f A"

(*lemma bij_betw_imp_is_inv_into1:
  assumes "bij_betw f A B"
  obtains g where "is_inv_into A f g"
proof -
  from assms have "f ` A = B" by (fact bij_betw_imp_surj_on)
  hence "f ` A \<subseteq> B" by simp
  with assms obtain g where "as_corr_on g B = corr_inv (as_corr_on f A)" by (elim theorem_1_4'')
  with \<open>f ` A = B\<close> have "corr_inv (as_corr_on g (f ` A)) = as_corr_on f A" using prop_1_3_4 by auto
  hence "is_inv_into A f g" by (fold is_inv_into_def)
  thus "thesis" by (fact that)
qed

lemma bij_betw_imp_is_inv_into2:
  assumes "bij_betw f A B"
  obtains g where "is_inv_into B g f"
proof -
  from assms have "f ` A = B" sorry
  have "f ` A \<subseteq> B" sorry
  with assms obtain g where "as_corr_on g B = corr_inv (as_corr_on f A)" by (elim theorem_1_4'')
  have "corr_inv (as_corr_on f (g ` B)) = as_corr_on g B" sorry
  hence "is_inv_into B g f" by (fold is_inv_into_def)
  thus "thesis" by (fact that)
qed*)

lemma is_inv_intoD1:
  assumes "is_inv_into A f g" and
    "a \<in> A"
  shows "g (f a) = a"
proof -
  from assms(1) have "corr_inv (as_corr_on g (f ` A)) = as_corr_on f A" by (unfold is_inv_into_def)
  hence "corr_inv (as_corr_on g (f ` A)) a = as_corr_on f A a" by simp
  with assms(2) have "{b \<in> f ` A. g b = a} = {f a}" by (simp only: corr_inv_fun_eq as_corr_on_eq)
  thus "g (f a) = a" by auto
qed

lemma is_inv_intoD2:
  assumes "is_inv_into A f g" and
    "b \<in> f ` A"
  shows "f (g b) = b"
proof -
  from assms(2) obtain a where "a \<in> A" and "b = f a" by auto
  from assms(1) have "corr_inv (as_corr_on g (f ` A)) = as_corr_on f A" by (unfold is_inv_into_def)
  hence "corr_inv (as_corr_on g (f ` A)) a = as_corr_on f A a" by simp
  with \<open>a \<in> A\<close> have "{b' \<in> f ` A. g b' = a} = {f a}" by (simp only: corr_inv_fun_eq as_corr_on_eq)
  hence "g (f a) = a" by auto
  with \<open>b = f a\<close> show "?thesis" by simp
qed

lemma is_inv_into_imp_bij_betw1:
  assumes "is_inv_into A f g"
  shows "bij_betw f A (f ` A)"
proof -
  from assms have "corr_inv (as_corr_on g (f ` A)) = as_corr_on f A" by (unfold is_inv_into_def)
  hence "as_corr_on g (f ` A) = corr_inv (as_corr_on f A)" using prop_1_3_4 by metis
  moreover have "f ` A \<subseteq> f ` A" by simp
  ultimately show "?thesis" by (intro theorem_1_4')
qed

lemma is_inv_into_imp_bij_betw2:
  assumes "is_inv_into A f g"
  shows "bij_betw g (f ` A) A"
proof (rule bij_betw_imageI)
  {
    fix a
    assume "a \<in> A"
    with assms have "g (f a) = a" by (rule is_inv_intoD1)
    with \<open>a \<in> A\<close> have"g (f a) \<in> A" by simp
  }
  moreover {
    fix a
    assume "a \<in> A"
    with assms have "g (f a) = a" by (rule is_inv_intoD1)
    with \<open>a \<in> A\<close> have "\<exists>a' \<in> A. g (f a') = a" by auto
  }
  ultimately show "g ` f ` A = A" by (blast intro: surj_onI)
  {
    fix b and b'
    assume "b \<in> f ` A" and
      "b' \<in> f ` A" and
      "g b = g b'"
    then obtain a and a' where "a \<in> A" and "b = f a" and "a' \<in> A" and "b' = f a'" by blast
    from \<open>g b = g b'\<close> and this(2,4) have "g (f a) = g (f a')" by simp
    with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and assms have "a = a'" using is_inv_intoD1 by fastforce
    with \<open>b = f a\<close> and \<open>b' = f a'\<close> have "b = b'" by simp
  }
  thus "inj_on g (f ` A)" by (blast intro: inj_onI)
qed

theorem theorem_1_5_a:
  assumes "f ` A = B" and "g ` B = C"
  shows "(g \<circ> f) ` A = C"
proof (rule set_eqI2)
  fix c
  assume "c \<in> (g \<circ> f) ` A"
  then obtain a where "a \<in> A" and "c = g (f a)" by force
  from this(1) and assms(1) have "f a \<in> B" by auto
  with assms(2) have "g (f a) \<in> C" by auto
  with \<open>c = g (f a)\<close> show "c \<in> C" by simp
next
  fix c
  assume "c \<in> C"
  with assms(2) obtain b where "b \<in> B" and "c = g b" by auto
  from this(1) and assms(1) obtain a where "a \<in> A" and "b = f a" by auto
  from \<open>c = g b\<close> and this(2) have "c = g (f a)" by simp
  with \<open>a \<in> A\<close> show "c \<in> (g \<circ> f) ` A" by simp
qed

theorem theorem_1_5_b:
  assumes "f ` A \<subseteq> B" and "inj_on f A" and "inj_on g B"
  shows "inj_on (g \<circ> f) A"
proof (rule inj_onI)
  fix a a'
  assume "a \<in> A" and "a' \<in> A" and "(g \<circ> f) a = (g \<circ> f) a'"
  from this(3) have "g (f a) = g (f a')" by simp
  moreover from \<open>a \<in> A\<close> and assms(1) have "f a \<in> B" by auto
  moreover from \<open>a' \<in> A\<close> and assms(1) have "f a' \<in> B" by auto
  moreover note assms(3)
  ultimately have "f a = f a'" by (elim inj_onD)
  with assms(2) and \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> show "a = a'"by (elim inj_onD)
qed

theorem theorem_1_5_c:
  assumes "bij_betw f A B" and "bij_betw g B C"
  shows "bij_betw (g \<circ> f) A C"
proof (rule bij_betw_imageI)
  from assms(1) have "f ` A = B" by (fact bij_betw_imp_surj_on)
  moreover from assms(2) have "g ` B = C" by (fact bij_betw_imp_surj_on)
  ultimately show "(g \<circ> f) ` A = C" by (fact theorem_1_5_a)
  from assms(1) have "inj_on f A" by (fact bij_betw_imp_inj_on)
  moreover from assms(2) have "inj_on g B" by (fact bij_betw_imp_inj_on)
  moreover from \<open>f ` A = B\<close> have "f ` A \<subseteq> B" by simp
  ultimately show "inj_on (g \<circ> f) A" by (intro theorem_1_5_b)
qed

theorem theorem_1_6_1:
  shows "(h \<circ> g) \<circ> f = h \<circ> (g \<circ> f)"
proof -
  {
    fix a
    have "((h \<circ> g) \<circ> f) a = (h \<circ> g) (f a)" by (simp only: comp_def)
    also have "\<dots> = h ( g (f a))" by (simp only: comp_def)
    also have "\<dots> = h ((g \<circ> f) a)" by (simp only: comp_def)
    also have "\<dots> = (h \<circ> (g \<circ> f)) a" by (simp only: comp_def)
    finally have "((h \<circ> g) \<circ> f) a = (h \<circ> (g \<circ> f)) a" .
  }
  thus "?thesis" ..
qed

theorem theorem_1_6_2_a:
  assumes -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    "id_on g A"
  shows "ext_eq_on A (f \<circ> g) f"
proof (rule ext_eq_onI)
  fix a
  assume "a \<in> A"
  with assms show "(f \<circ> g) a = f a" by (auto dest: id_onD)
qed

theorem theorem_1_6_2_b:
  assumes "f ` A \<subseteq> B" and
    "id_on g B"
  shows "ext_eq_on A (g \<circ> f) f"
proof (rule ext_eq_onI)
  fix a
  assume "a \<in> A"
  with assms(1) have "f a \<in> B" by auto
  with assms(2) show "(g \<circ> f) a = f a" by (auto dest: id_onD)
qed

theorem theorem_1_6_3_a:
  assumes "bij_betw f A B" and
    "is_inv_into A f g"
  shows "id_on (g \<circ> f) A"
proof (rule id_onI)
  fix a
  assume "a \<in> A"
  with assms(2) show "(g \<circ> f) a = a" by (auto dest: is_inv_intoD1)
qed

theorem theorem_1_6_3_b:
  assumes "bij_betw f A B" and
    "is_inv_into A f g"
  shows "id_on (f \<circ> g) B"
proof (rule id_onI)
  fix b
  assume "b \<in> B"
  with assms(1) have "b \<in> f ` A" by (auto dest: bij_betw_imp_surj_on)
  with assms(2) show "(f \<circ> g) b = b" by (auto dest: is_inv_intoD2)
qed

proposition problem_1_4_2':
  assumes "P \<subseteq> A" and
    "a \<in> P" and
    "a' \<in> A - P" and
    "f a = f a'"
  shows "P \<subset> (f -` f ` P) \<inter> A"
proof (rule psubsetI)
  from assms(1) show "P \<subseteq> (f -` f ` P) \<inter> A" by (fact prop_1_4_5)
  from assms(2) have "f a \<in> f ` P" by simp
  with assms(4) have "f a' \<in> f ` P" by simp
  hence "a' \<in> f -` f ` P" by simp
  with \<open>a' \<in> A - P\<close> have "a' \<in> (f -` f ` P) \<inter> A" by simp
  moreover from assms(3) have "a' \<notin> P" by simp
  ultimately show "P \<noteq> (f -` f ` P) \<inter> A" by auto
qed

proposition problem_1_4_3_a:
  assumes "inj_on f A" and
    "P \<subseteq> A"
  shows "(f -` (f ` P)) \<inter> A = P"
proof (rule set_eqI2)
  fix p
  assume "p \<in> (f -` (f ` P)) \<inter> A"
  hence "f p \<in> f ` P" and "p \<in> A" by simp+
  from this(1) obtain p' where "p' \<in> P" and "f p = f p'" by auto
  from this(1) and assms(2) have "p' \<in> A" by auto
  with \<open>p \<in> A\<close> and \<open>f p = f p'\<close> and assms(1) have "p = p'" by (elim inj_onD)
  with \<open>p' \<in> P\<close> show "p \<in> P" by simp
next
  fix p
  assume "p \<in> P"
  hence "f p \<in> f ` P" by simp
  hence "p \<in> f -` (f ` P)" by auto
  moreover from \<open>p \<in> P\<close> and assms(2) have "p \<in> A" ..
  ultimately show "p \<in> (f -` (f ` P)) \<inter> A" ..
qed

proposition problem_1_4_3_b:
  assumes "Q \<subseteq> B" and
    "f ` A = B"
  shows "f ` ((f -` Q) \<inter> A) = Q"
proof (rule set_eqI2)
  fix b
  assume "b \<in> f ` ((f -` Q) \<inter> A)"
  then obtain a where "a \<in> f -` Q" and "b = f a" by auto
  from this(1) have "f a \<in> Q" by simp
  with \<open>b = f a\<close> show "b \<in> Q" by simp
next
  fix b
  assume "b \<in> Q"
  with assms(1) have "b \<in> B" ..
  with assms(2) obtain a where "a \<in> A" and "b = f a" by auto
  with \<open>b \<in> Q\<close> have "a \<in> (f -` Q) \<inter> A" by simp
  with \<open>b = f a\<close> show "b \<in> f ` ((f -` Q) \<inter> A)" by simp
qed

proposition problem_1_4_4:
  assumes "inj_on f A" and
    "P\<^sub>1 \<subseteq> A" and
    "P\<^sub>2 \<subseteq> A"
  shows "f ` (P\<^sub>1 \<inter> P\<^sub>2) = f ` P\<^sub>1 \<inter> f ` P\<^sub>2"
proof (rule equalityI)
  show "f ` (P\<^sub>1 \<inter> P\<^sub>2) \<subseteq> f ` P\<^sub>1 \<inter> f ` P\<^sub>2" by (fact prop_1_4_3)
next
  {
    fix b
    assume "b \<in> f ` P\<^sub>1 \<inter> f ` P\<^sub>2"
    then obtain a a' where "a \<in> P\<^sub>1" and
      "b = f a" and
      "a' \<in> P\<^sub>2" and
      "b = f a'" by blast
    with assms(2,3) have "a \<in> A" and "a' \<in> A" and "f a = f a'" by auto
    with assms(1) have "a = a'" by (elim inj_onD)
    with \<open>a' \<in> P\<^sub>2\<close> have "a \<in> P\<^sub>2" by simp
    with \<open>a \<in> P\<^sub>1\<close> and \<open>b = f a\<close> have "b \<in> f ` (P\<^sub>1 \<inter> P\<^sub>2)" by simp
  }
  thus "f ` P\<^sub>1 \<inter> f ` P\<^sub>2 \<subseteq> f ` (P\<^sub>1 \<inter> P\<^sub>2)" by blast
qed

proposition problem_1_4_5_b:
  assumes "a \<in> P" and
    "a' \<in> A - P" and
    "f a = f a'"
  shows "f ` A - f ` P \<subset> f ` (A - P)"
proof (rule psubsetI)
  show "f ` A - f ` P \<subseteq> f ` (A - P)" by (fact prop_1_4_4)
next
  from assms(2) have "a' \<in> A" by simp
  hence "f a' \<in> f ` A" by simp
  from assms(1) have "f a \<in> f ` P" by simp
  with assms(3) have "f a' \<in> f ` P" by simp
  with \<open>f a' \<in> f ` A\<close> have "f a' \<notin> f ` A - f ` P" by simp
  moreover from assms(2) have "f a' \<in> f ` (A - P)" by simp
  ultimately show "f ` A - f ` P \<noteq> f ` (A - P)" by blast
qed

proposition problem_1_4_5_c:
  assumes "P \<subseteq> A" and
    "inj_on f A"
  shows "f ` (A - P) = f ` A - f ` P"
proof (rule set_eqI2)
  fix b
  assume "b \<in> f ` (A - P)"
  then obtain a where "a \<in> A" and "a \<notin> P" and "b = f a" by auto
  {
    assume "b \<in> f ` P"
    then obtain a' where "a' \<in> P" and "b = f a'" by auto
    from this(1) and assms(1) have "a' \<in> A" by auto
    with \<open>a \<in> A\<close> and \<open>b = f a\<close> and \<open>b = f a'\<close> and assms(2) have "a = a'" by (auto dest: inj_onD)
    with \<open>a' \<in> P\<close> and \<open>a \<notin> P\<close> have "False" by simp
  }
  hence "b \<notin> f ` P" by auto
  with \<open>a \<in> A\<close> and \<open>b = f a\<close> show "b \<in> f ` A - f ` P" by simp
next
  fix b
  assume "b \<in> f ` A - f ` P"
  thus "b \<in> f ` (A - P)" by blast
qed

proposition problem_1_4_8:
  assumes -- {* @{prop "bij_betw f A B"} can be weakened to @{prop "f ` A = B"} because
                @{prop "is_inv_into A f f'"} implies @{prop "bij_betw f A (f ` A)"}. *}
    "f ` A = B" and
    -- {* @{prop "bij_betw g B C"} can be weakened to @{prop "g ` B = C"} because
          @{prop "is_inv_into A f f'"} implies @{prop "bij_betw g B (g ` B)"}. *}
    "g ` B = C" and
    "is_inv_into A f f'" and
    "is_inv_into B g g'" and
    "is_inv_into A (g \<circ> f) h"
  shows "ext_eq_on C h (f' \<circ> g')"
proof (rule ext_eq_onI)
  fix c
  assume "c \<in> C"
  from assms(5) have "bij_betw h ((g \<circ> f) ` A) A" by (auto intro: is_inv_into_imp_bij_betw2)
  moreover from assms(1,2) have "(g \<circ> f) ` A = C" by auto
  ultimately have "bij_betw h C A" by simp
  with \<open>c \<in> C\<close> have "h c \<in> A" by (auto dest: bij_betw_imp_surj_on)
  from \<open>c \<in> C\<close> and \<open>(g \<circ> f) ` A = C\<close> have "c \<in> (g \<circ> f) ` A" by simp
  with assms(5) have "g (f (h c)) = c" by (auto dest: is_inv_intoD2)
  hence "g' (g (f (h c))) = g' c" by simp
  moreover from \<open>h c \<in> A\<close> and assms(1) have "f (h c) \<in> B" by auto
  moreover note assms(4)
  ultimately have "f (h c) = g' c" by (auto dest: is_inv_intoD1)
  hence "f' (f (h c)) = f' (g' c)" by simp
  moreover note \<open>h c \<in> A\<close>
  moreover note assms(3)
  ultimately have "h c = f' (g' c)" by (auto dest: is_inv_intoD1)
  thus "h c = (f' \<circ> g') c" by simp
qed

proposition problem_1_4_9_a:
    -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    -- {* @{prop "g ` B \<subseteq> C"}: an unnecessary assumption. *}
    -- {* @{prop "P \<subseteq> A"}: an unnecessary assumption. *}
  shows "(g \<circ> f) ` P = g ` (f ` P)"
proof (rule set_eqI)
  fix c
  have "c \<in> (g \<circ> f) ` P \<longleftrightarrow> (\<exists>a \<in> P. c = g (f a))" by fastforce
  also have "\<dots> \<longleftrightarrow> c \<in> g ` (f ` P)" by auto
  finally show "c \<in> (g \<circ> f) ` P \<longleftrightarrow> c \<in> g ` (f ` P)" by simp
qed

proposition problem_1_4_9_b:
    -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    -- {* @{prop "g ` B \<subseteq> C"}: an unnecessary assumption. *}
    -- {* @{prop "R \<subseteq> C"}: an unnecessary assumption. *}
  shows "((g \<circ> f) -` R) \<inter> A = (f -` (g -` R)) \<inter> A" (is "?L = ?R")
proof (rule set_eqI)
  fix a
  have "a \<in> ?L \<longleftrightarrow> g (f a) \<in> R \<and> a \<in> A" by simp
  also have "\<dots> \<longleftrightarrow> f a \<in> g -` R \<and> a \<in> A" by simp
  also have "\<dots> \<longleftrightarrow> a \<in> f -` (g -` R) \<and> a \<in> A" by simp
  also have "\<dots> \<longleftrightarrow> a \<in> ?R" by simp
  finally show "a \<in> ?L \<longleftrightarrow> a \<in> ?R" .
qed

proposition problem_1_4_10_a:
  assumes "f ` A \<subseteq> B" and
    "g ` B \<subseteq> C" and
    "(g \<circ> f) ` A = C"
  shows "g ` B = C"
proof (rule equalityI)
  show "g ` B \<subseteq> C" by (fact assms(2))
next
  {
    fix c
    assume "c \<in> C"
    with assms(3) obtain a where "a \<in> A" and "c = g (f a)" by auto
    from this(1) and assms(1) have "f a \<in> B" by auto
    with \<open>c = g (f a)\<close> have "c \<in> g ` B" by auto
  }
  thus "C \<subseteq> g ` B" by (intro subsetI)
qed

proposition problem_1_4_10_b:
  assumes "inj_on (g \<circ> f) A"
  shows "inj_on f A"
proof (rule inj_onI)
  fix a a'
  assume "a \<in> A" and
    "a' \<in> A" and
    "f a = f a'"
  from this(3) have "(g \<circ> f) a = (g \<circ> f) a'" by simp
  with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and assms show "a = a'" by (elim inj_onD)
qed

proposition problem_1_4_11:
  assumes "f ` A = B" and
    "ext_eq_on A (g \<circ> f) (g' \<circ> f)"
  shows "ext_eq_on B g g'"
proof (rule ext_eq_onI)
  fix b
  assume "b \<in> B"
  with assms(1) obtain a where "a \<in> A" and "b = f a" by auto
  from this(1) and assms(2) have "g (f a) = g' (f a)" by (auto dest: ext_eq_onD)
  with \<open>b = f a\<close> show "g b = g' b" by simp
qed

proposition problem_1_4_12:
  assumes "f ` A \<subseteq> B" and
    "f' ` A \<subseteq> B" and
    "inj_on g B" and
    "ext_eq_on A (g \<circ> f) (g \<circ> f')"
  shows "ext_eq_on A f f'"
proof (rule ext_eq_onI)
  fix a
  assume "a \<in> A"
  with assms(4) have "g (f a) = g (f' a)" by (auto dest: ext_eq_onD)
  moreover from \<open>a \<in> A\<close> and assms(1,2) have "f a \<in> B" and "f' a \<in> B" by auto
  moreover note assms(3)
  ultimately show "f a = f' a" by (elim inj_onD)
qed

proposition problem_1_4_13_a:
  assumes "f ` A \<subseteq> B" and
    "g ` B \<subseteq> C" and
    "(g \<circ> f) ` A = C" and
    "inj_on g B"
  shows "f ` A = B"
proof (rule surj_onI)
  fix a
  assume "a \<in> A"
  with assms(1) show "f a \<in> B" by auto
next
  fix b
  assume "b \<in> B"
  with assms(2) have "g b \<in> C" by auto
  with assms(3) obtain a where "a \<in> A" and "g (f a) = g b" by force
  moreover from this(1) and assms(1) have "f a \<in> B" by auto
  moreover note \<open>b \<in> B\<close> and assms(4)
  ultimately have "f a = b" by (elim inj_onD)
  with \<open>a \<in> A\<close> show "\<exists>a \<in> A. f a = b" by auto
qed

proposition problem_1_4_13_b:
  assumes "inj_on (g \<circ> f) A" and
    "f ` A = B"
  shows "inj_on g B"
proof (rule inj_onI)
  fix b b'
  assume "b \<in> B" and
    "b' \<in> B" and
    "g b = g b'"
  from this(1,2) and assms(2) obtain a and a' where
    "a \<in> A" and "b = f a" and "a' \<in> A" and "b' = f a'" by auto
  from \<open>g b = g b'\<close> and this(2,4) have "g (f a) = g (f a')" by simp
  with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and assms(1) have "a = a'" by (auto elim: inj_onD)
  with \<open>b = f a\<close> and \<open>b' = f a'\<close> show "b = b'" by simp
qed

proposition problem_1_4_14:
  assumes "f ` A \<subseteq> B" and
    "g ` B \<subseteq> A" and
    "g' ` B \<subseteq> A" and
    "id_on (g \<circ> f) A" and
    "id_on (f \<circ> g') B" and
    "is_inv_into A f f'"
  shows "bij_betw f A B" and
    "ext_eq_on B g g'" and
    "ext_eq_on B g' f'"
proof -
  have "B \<subseteq> f ` A"
  proof (rule subsetI)
    fix b
    assume "b \<in> B"
    with assms(5) have "f (g' b) = b" by (auto dest: id_onD)
    moreover from assms(3) and \<open>b \<in> B\<close> have "g' b \<in> A" by auto
    ultimately show "b \<in> f ` A" by force
  qed
  moreover have "inj_on f A"
  proof (rule inj_onI)
    fix a and a'
    assume "a \<in> A" and
      "a' \<in> A" and
      "f a = f a'"
    from this(3) have "g (f a) = g (f a')" by simp
    with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and assms(4) show "a = a'" using id_onD by fastforce
  qed
  moreover note assms(1)
  ultimately show "bij_betw f A B" by (auto intro: bij_betw_imageI)
  {
    fix b
    assume "b \<in> B"
    with assms(5) have "f (g' b) = b" by (auto dest: id_onD)
    hence "g (f (g' b)) = g b" by simp
    moreover from \<open>b \<in> B\<close> and assms(3) have "g' b \<in> A" by auto
    moreover note assms(4)
    ultimately have "g b = g' b" by (auto dest: id_onD)
  }
  thus "ext_eq_on B g g'" by (rule ext_eq_onI)
  {
    fix b
    assume "b \<in> B"
    with assms(5) have "f (g' b) = b" by (auto dest: id_onD)
    hence "f' (f (g' b)) = f' b" by simp
    moreover from \<open>b \<in> B\<close> and assms(3) have "g' b \<in> A" by auto
    moreover note assms(6)
    ultimately have "g' b = f' b" by (auto dest: is_inv_intoD1)
  }
  thus "ext_eq_on B g' f'" by (rule ext_eq_onI)
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
proof (rule iffI)
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

end
