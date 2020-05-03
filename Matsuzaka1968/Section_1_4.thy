theory Section_1_4
  imports Main
    "HOL-Library.Indicator_Function"
    "Section_1_3"
begin

section "Various Concepts on Functions"

text {*
  In this and the following sections, functions in usual mathematics are formalized in terms of
  functions in Isabelle/HOL. Because careful handling is required in such formalization, let me
  explain the detail.

  Functions in usual mathematics are associated with its domain and codomain. The careful handling
  is required in their formalization. A function in Isabelle/HOL (say,
  @{term [show_types] "f :: 'a \<Rightarrow> 'b"}) is associated with the domain (the universal set of the
  type @{typ "'a"}) and the codomain (the universal set of the type @{typ "'b"}). However, because
  (the universal set of) types in Isabelle/HOL are not expressive enough to encode an arbitrary
  set (which is equivalent to an arbitrary proposition under the axiom schema of comprehension in
  Isabelle/HOL), a subset of the universal set of the type @{typ "'a"} is needed to be explicitly
  specified in order to formalize the domain of a function in usual mathematics.

  As a result, a function @{term "f"} in Isabelle/HOL that formalizes a function in usual
  mathematics has "two domains"; one is the original one, i.e., the universal set of the type
  @{typ "'a"}, and the other is the one that is explicitly specified in order to express the
  domain of the function in usual mathematics.

  Let @{term "A :: 'a set"} be a set that is specified to express the domain of a function in
  usual mathematics. It should be always noted that the function in Isabelle/HOL is defined on
  @{term "-A"}. This fact is essentially different from the function in usual mathematics, where
  it is simply undefined out of @{term "A"}. This difference demands careful handling. The
  statement of definitions and propositions concerning functions in usual mathematics should be
  properly rephrased to reflect the difference.

  How each concept concerning functions in usual mathematics is rephrased in the following
  sections is named below;

    \<^item>The codomain is explicitly specified as a set @{term "B :: 'b set"} such that
     @{prop "f ` A \<subseteq> B"} only when it is actually required in definitions and propositions.
    \<^item>The inverse image of a set @{term "Q \<subseteq> B"} under @{term "f"} is defined @{term "f -` Q \<inter> A"}
     since @{term "f -` Q"} could include an element out of @{term "A"}.
    \<^item>Surjectivity of @{term "f"} is stated as the proposition @{term "f ` A = B"}.
    \<^item>Injectivity of @{term "f"} is stated as the proposition @{term "inj_on f A"}.
    \<^item>Equality of two function @{term "f"} and @{term "g"} on a set @{term "A"} is defined by the
     proposition @{prop "\<forall>a \<in> A. f a = g a"}, which is shortly stated as the proposition
     @{prop "ext_eq_on A f g"}. Note that @{term "f"} and @{term "g"} behaves differently out of
     @{term "A"} and thus @{prop "f = g"} does not hold even if @{prop "ext_eq_on A f g"} holds.
    \<^item>(TODO: inverse)
*}

text {* Extensional equality of two functions on a set. *}

definition ext_eq_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "ext_eq_on A f f' \<longleftrightarrow> (\<forall>a \<in> A. f a = f' a)"

lemma ext_eq_onI [intro]:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a = f' a"
  shows "ext_eq_on A f f'"
  using assms unfolding ext_eq_on_def by simp

lemma ext_eq_onD [dest]:
  assumes "ext_eq_on A f f'"
    and "a \<in> A"
  shows "f a = f' a"
  using assms unfolding ext_eq_on_def by simp

lemma ext_eq_on_refl [simp]:
  shows "ext_eq_on A f f"
  by auto

lemma ext_eq_on_sym [sym]:
  assumes "ext_eq_on A f f'"
  shows "ext_eq_on A f' f"
  using assms by fastforce

lemma ext_eq_on_trans [trans]:
  assumes "ext_eq_on A f g"
    and "ext_eq_on A g h"
  shows "ext_eq_on A f h"
  using assms by fastforce

lemma ext_eq_on_empty [simp]:
  shows "ext_eq_on {} f g"
  by auto

subsection \<open>A) Image and Inverse Image of Map\<close>

proposition prop_1_4_1:
  assumes -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    -- \<open>The assumption @{prop "P\<^sub>1 \<subseteq> A"} is not necessary.\<close>
    -- \<open>The assumption @{prop "P\<^sub>2 \<subseteq> A"} is not necessary.\<close>
    "P\<^sub>1 \<subseteq> P\<^sub>2"
  shows "f ` P\<^sub>1 \<subseteq> f ` P\<^sub>2"
  using assms by (fact image_mono)

proposition prop_1_4_2:
  -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
  -- \<open>The assumption @{prop "P\<^sub>1 \<subseteq> A"} is not necessary.\<close>
  -- \<open>The assumption @{prop "P\<^sub>2 \<subseteq> A"} is not necessary.\<close>
  shows "f ` (P\<^sub>1 \<union> P\<^sub>2) = f ` P\<^sub>1 \<union> f ` P\<^sub>2"
  by (fact image_Un)

proposition prop_1_4_3:
  -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
  -- \<open>The assumption @{prop "P\<^sub>1 \<subseteq> A"} is not necessary.\<close>
  -- \<open>The assumption @{prop "P\<^sub>2 \<subseteq> A"} is not necessary.\<close>
  shows "f ` (P\<^sub>1 \<inter> P\<^sub>2) \<subseteq> f ` P\<^sub>1 \<inter> f ` P\<^sub>2"
  by (fact image_Int_subset)

proposition prop_1_4_4:
  -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
  -- \<open>The assumption @{prop "P \<subseteq> A"} is not necessary.\<close>
  shows "f ` (A - P) \<supseteq> f ` A - f ` P"
  by (fact image_diff_subset)

proposition prop_1_4_1':
  assumes -- \<open>@The assumption {prop "f ` A \<subseteq> B"} is not necessary.\<close>
    -- \<open>The assumption @{prop "Q\<^sub>1 \<subseteq> B"} is not necessary.\<close>
    -- \<open>The assumption @{prop "Q\<^sub>2 \<subseteq> B"} is not necessary.\<close>
    "Q\<^sub>1 \<subseteq> Q\<^sub>2"
  shows "(f -` Q\<^sub>1) \<inter> A \<subseteq> (f -` Q\<^sub>2) \<inter> A"
  using assms by auto

proposition prop_1_4_2':
  -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
  -- \<open>The assumption @{prop "Q\<^sub>1 \<subseteq> B"} is not necessary.\<close>
  -- \<open>The assumption @{prop "Q\<^sub>2 \<subseteq> B"} is not necessary.\<close>
  shows "f -` (Q\<^sub>1 \<union> Q\<^sub>2) \<inter> A = (f -` Q\<^sub>1 \<inter> A) \<union> (f -` Q\<^sub>2 \<inter> A)"
  by auto

proposition prop_1_4_3':
  -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
  -- \<open>The assumption @{prop "Q\<^sub>1 \<subseteq> B"} is not necessary.\<close>
  -- \<open>The assumption @{prop "Q\<^sub>2 \<subseteq> B"} is not necessary.\<close>
  shows "f -` (Q\<^sub>1 \<inter> Q\<^sub>2) \<inter> A = (f -` Q\<^sub>1 \<inter> A) \<inter> (f -` Q\<^sub>2 \<inter> A)"
  by auto

proposition prop_1_4_4':
  assumes "f ` A \<subseteq> B"
    -- \<open>The assumption @{prop "Q \<subseteq> B"} is not necessary.\<close>
  shows "f -` (B - Q) \<inter> A = A - (f -` Q \<inter> A)"
  using assms by auto

proposition prop_1_4_5:
  assumes
  -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    "P \<subseteq> A"
  shows "P \<subseteq> f -` (f ` P) \<inter> A"
  using assms by auto

proposition prop_1_4_5':
  -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
  -- \<open>The assumption @{prop "Q \<subseteq> B"} is not necessary.\<close>
  shows "f ` (f -` Q \<inter> A) \<subseteq> Q"
  by auto

proposition prob_1_4_a:
  assumes "P \<subseteq> A"
    and "A - P = {a}"
    and "P = {p}"
    and "f(a) = f(p)"
  shows "f ` A - f ` P \<subset> f ` (A - P)"
  using assms by blast

proposition prob_1_4_b:
  assumes "P \<subseteq> A"
    and "{a} = A - P"
    and "{p} = P"
    and "f(a) = f(p)"
  shows "P \<subset> f -` (f ` (P))"
  using assms by blast

subsection \<open>B) Surjective, Injective, and Bijective Maps\<close>

lemma surj_onI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<in> B"
    and "\<And>b. b \<in> B \<Longrightarrow> b \<in> f ` A"
  shows "f ` A = B"
proof (intro equalityI)
  from assms(1) show "f ` A \<subseteq> B" by auto
  from assms(2) show "B \<subseteq> f ` A" by auto
qed

lemma bij_betw_imageI':
  assumes "\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> f a = f a' \<Longrightarrow> a = a'"
    and "\<And>a. a \<in> A \<Longrightarrow> f a \<in> B"
    and "\<And>b. b \<in> B \<Longrightarrow> b \<in> f ` A"
  shows "bij_betw f A B"
proof (rule bij_betw_imageI)
  from assms(1) show "inj_on f A" by (rule inj_onI)
  from assms(2,3) show "f ` A = B" by auto
qed

lemma corr_inv_fun_fun:
  assumes "a \<in> A"
  shows "corr_inv (as_corr_on f A) (f a) = {a' \<in> A. f a' = f a}"
  using assms by auto

lemma corr_inv_fun_eq:
  shows "corr_inv (as_corr_on f A) b = {a \<in> A. f a = b}" (is "?L = ?R")
proof (rule set_eqI)
  fix a
  have "a \<in> ?L \<longleftrightarrow> b \<in> as_corr_on f A a" by auto
  also have "\<dots> \<longleftrightarrow> a \<in> A \<and> f a = b" by auto
  also have "\<dots> \<longleftrightarrow> a \<in> ?R" by simp
  finally show "a \<in> ?L \<longleftrightarrow> a \<in> ?R" .
qed

theorem thm_1_4_a:
  assumes "f ` A \<subseteq> B"
    and "as_corr_on g B = corr_inv (as_corr_on f A)"
  shows "bij_betw f A B"
proof (rule bij_betw_imageI')
  fix a and a'
  assume "a \<in> A"
    and "a' \<in> A"
    and "f a = f a'"
  from \<open>a \<in> A\<close> and assms(1) have "f a \<in> B" by auto
  moreover from assms(2) have "corr_inv (as_corr_on f A) (f a) = as_corr_on g B (f a)" by simp
  with \<open>a \<in> A\<close> and \<open>f a \<in> B\<close> have **: "{a'' \<in> A. f a'' = f a} = {g (f a)}"
    by (auto simp only: corr_inv_fun_fun)
  with \<open>a \<in> A\<close> have "a = g (f a)" by blast
  moreover from ** and \<open>a' \<in> A\<close> and \<open>f a = f a'\<close> have "a' = g (f a)" by auto
  ultimately show "a = a'" by simp
next
  fix a
  assume "a \<in> A"
  with assms(1) show "f a \<in> B" by auto
next
  fix b
  assume "b \<in> B"
  moreover from assms(2) have "corr_inv (as_corr_on f A) b = as_corr_on g B b" by simp
  ultimately have "{a \<in> A. f a = b} = {g b}" by (force simp only: corr_inv_fun_eq)
  hence "g b \<in> A" and "f (g b) = b" by auto
  thus "b \<in> f ` A" by force
qed

lemma bij_betwE2 [elim]:
  assumes "bij_betw f A B"
  obtains "f ` A = B"
    and "inj_on f A"
  using assms by (auto dest: bij_betw_imp_surj_on bij_betw_imp_inj_on)

theorem thm_1_4_b:
  assumes "f ` A \<subseteq> B"
    and "bij_betw f A B"
  obtains g where "as_corr_on g B = corr_inv (as_corr_on f A)"
proof -
  {
    fix b
    {
      assume "b \<in> B"
      from assms(2) have "f ` A = B" and "inj_on f A" by auto
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
        by (force simp only: corr_inv_fun_eq)
    }
    moreover {
      assume "b \<notin> B"
      with assms(1) have "{a \<in> A. f a = b} = {}" by blast
      with \<open>b \<notin> B\<close> have "as_corr_on (the_inv_into A f) B b = corr_inv (as_corr_on f A) b" by blast
    }
    ultimately have "as_corr_on (the_inv_into A f) B b = corr_inv (as_corr_on f A) b" by auto
  }
  hence "as_corr_on (the_inv_into A f) B = corr_inv (as_corr_on f A)" by auto
  thus "thesis" by (fact that)
qed

theorem thm_1_4:
  assumes "f ` A \<subseteq> B"
  shows "(\<exists>g. as_corr_on g B = corr_inv (as_corr_on f A)) \<longleftrightarrow> bij_betw f A B"
proof (rule iffI)
  assume "\<exists>g. as_corr_on g B = corr_inv (as_corr_on f A)"
  then obtain g where "as_corr_on g B = corr_inv (as_corr_on f A)" by auto
  with assms show "bij_betw f A B" by (auto intro: thm_1_4_a)
next
  assume "bij_betw f A B"
  with assms obtain g where "as_corr_on g B = corr_inv (as_corr_on f A)" by (elim thm_1_4_b)
  thus "\<exists>g. as_corr_on g B = corr_inv (as_corr_on f A)" by auto
qed

definition is_inv_into :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "is_inv_into A f g \<longleftrightarrow> corr_inv (as_corr_on g (f ` A)) = as_corr_on f A"

lemma is_inv_intoD1:
  assumes "is_inv_into A f g"
    and "a \<in> A"
  shows "g (f a) = a"
proof -
  from assms(1) have "corr_inv (as_corr_on g (f ` A)) = as_corr_on f A" by (unfold is_inv_into_def)
  hence "corr_inv (as_corr_on g (f ` A)) a = as_corr_on f A a" by simp
  with assms(2) have "{b \<in> f ` A. g b = a} = {f a}" by (auto simp only: corr_inv_fun_eq)
  thus "g (f a) = a" by auto
qed

lemma is_inv_intoD2:
  assumes "is_inv_into A f g"
    and "b \<in> f ` A"
  shows "f (g b) = b"
  using assms by (auto dest: is_inv_intoD1)

lemma is_inv_into_imp_bij_betw1:
  assumes "is_inv_into A f g"
  shows "bij_betw f A (f ` A)"
proof -
  from assms have "corr_inv (as_corr_on g (f ` A)) = as_corr_on f A" by (unfold is_inv_into_def)
  hence "as_corr_on g (f ` A) = corr_inv (as_corr_on f A)" using prop_1_3_4 by metis
  moreover have "f ` A \<subseteq> f ` A" by simp
  ultimately show "?thesis" by (intro thm_1_4_a)
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
    assume "b \<in> f ` A"
      and "b' \<in> f ` A"
      and "g b = g b'"
    then obtain a and a' where "a \<in> A" and "b = f a" and "a' \<in> A" and "b' = f a'" by blast
    from \<open>g b = g b'\<close> and this(2,4) have "g (f a) = g (f a')" by simp
    with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and assms have "a = a'" using is_inv_intoD1 by fastforce
    with \<open>b = f a\<close> and \<open>b' = f a'\<close> have "b = b'" by simp
  }
  thus "inj_on g (f ` A)" by (blast intro: inj_onI)
qed

subsection \<open>C) Composition of Maps\<close>

theorem thm_1_5_a:
  assumes "f ` A = B"
    and "g ` B = C"
  shows "(g \<circ> f) ` A = C"
  using assms by auto

theorem thm_1_5_b:
  assumes "f ` A \<subseteq> B"
    -- \<open>The assumption @{prop "g ` B \<subseteq> C"} is not necessary.\<close>
    and "inj_on f A"
    and "inj_on g B"
  shows "inj_on (g \<circ> f) A"
proof (rule inj_onI)
  fix a a'
  assume "a \<in> A" and "a' \<in> A" and "(g \<circ> f) a = (g \<circ> f) a'"
  from this(3) have "g (f a) = g (f a')" by simp
  moreover from \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and assms(1) have "f a \<in> B" and "f a' \<in> B" by auto
  moreover note assms(3)
  ultimately have "f a = f a'" by (elim inj_onD)
  with assms(2) and \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> show "a = a'"by (elim inj_onD)
qed

theorem thm_1_5_c:
  assumes "bij_betw f A B"
    and "bij_betw g B C"
  shows "bij_betw (g \<circ> f) A C"
  using assms by (auto intro: bij_betw_trans)

theorem thm_1_6_1:
  shows "(h \<circ> g) \<circ> f = h \<circ> (g \<circ> f)"
  by (fact comp_assoc)

theorem thm_1_6_2_a:
  assumes -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    "id_on g A"
  shows "ext_eq_on A (f \<circ> g) f"
  using assms by fastforce

theorem thm_1_6_2_b:
  assumes "f ` A \<subseteq> B"
    and "id_on g B"
  shows "ext_eq_on A (g \<circ> f) f"
  using assms by fastforce

theorem thm_1_6_3_a:
  assumes "bij_betw f A B"
    and "is_inv_into A f g"
  shows "id_on (g \<circ> f) A"
  using assms by (fastforce dest: is_inv_intoD1)

theorem thm_1_6_3_b:
  assumes "bij_betw f A B"
    and "is_inv_into A f g"
  shows "id_on (f \<circ> g) B"
  using assms by (fastforce dest: is_inv_intoD2)

subsection \<open>D) Restriction and Extension of Maps\<close>

subsection \<open>E) Note on Codomain of Map\<close>

subsection \<open>F) Sets of Maps\<close>

subsection \<open>Problems\<close>

proposition prob_1_4_2_b:
  assumes -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    "P \<subseteq> A"
    and "a \<in> P"
    and "a' \<in> A - P"
    and "f a = f a'"
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

proposition prob_1_4_3_a:
  assumes -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    "inj_on f A"
    and "P \<subseteq> A"
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

proposition prob_1_4_3_b:
  assumes "Q \<subseteq> B"
    and "f ` A = B"
  shows "f ` ((f -` Q) \<inter> A) = Q"
  using assms by auto

proposition prob_1_4_4:
  assumes -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    "inj_on f A"
    and "P\<^sub>1 \<subseteq> A"
    and "P\<^sub>2 \<subseteq> A"
  shows "f ` (P\<^sub>1 \<inter> P\<^sub>2) = f ` P\<^sub>1 \<inter> f ` P\<^sub>2"
  using assms by (auto dest: inj_on_image_Int)

proposition prob_1_4_5_b:
  assumes -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    -- \<open>The assumption @{prop "P \<subseteq> A"} is not necessary.\<close>
    "a \<in> P"
    and "a' \<in> A - P"
    and "f a = f a'"
  shows "f ` A - f ` P \<subset> f ` (A - P)"
proof (rule psubsetI)
  show "f ` A - f ` P \<subseteq> f ` (A - P)" by (fact prop_1_4_4)
  from assms(2) have "a' \<in> A" by simp
  hence "f a' \<in> f ` A" by simp
  from assms(1) have "f a \<in> f ` P" by simp
  with assms(3) have "f a' \<in> f ` P" by simp
  with \<open>f a' \<in> f ` A\<close> have "f a' \<notin> f ` A - f ` P" by simp
  moreover from assms(2) have "f a' \<in> f ` (A - P)" by simp
  ultimately show "f ` A - f ` P \<noteq> f ` (A - P)" by blast
qed

proposition prob_1_4_5_c:
  assumes -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    "P \<subseteq> A"
    and "inj_on f A"
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

proposition prob_1_4_8:
  assumes -- \<open>The assumption @{prop "bij_betw f A B"} can be weakened to @{prop "f ` A = B"}
              because @{prop "is_inv_into A f f'"} implies @{prop "bij_betw f A (f ` A)"}.\<close>
    "f ` A = B"
    -- \<open>The assumption @{prop "bij_betw g B C"} can be weakened to @{prop "g ` B = C"} because
        @{prop "is_inv_into A f f'"} implies @{prop "bij_betw g B (g ` B)"}.\<close>
    and "g ` B = C"
    and "is_inv_into A f f'"
    and "is_inv_into B g g'"
    and "is_inv_into A (g \<circ> f) h"
  shows "ext_eq_on C h (f' \<circ> g')"
proof (rule ext_eq_onI)
  fix c
  assume "c \<in> C"
  from assms(5) have "bij_betw h ((g \<circ> f) ` A) A" by (intro is_inv_into_imp_bij_betw2)
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

proposition prob_1_4_9_a:
  -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
  -- \<open>The assumption @{prop "g ` B \<subseteq> C"} is not necessary.\<close>
  -- \<open>The assumption @{prop "P \<subseteq> A"} is not necessary.\<close>
  shows "(g \<circ> f) ` P = g ` (f ` P)" (is "?L = ?R")
  by auto

proposition prob_1_4_9_b:
  -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
  -- \<open>The assumption @{prop "g ` B \<subseteq> C"} is not necessary.\<close>
  -- \<open>The assumption @{prop "R \<subseteq> C"} is not necessary.\<close>
  shows "((g \<circ> f) -` R) \<inter> A = (f -` (g -` R)) \<inter> A" (is "?L = ?R")
  by fastforce

proposition prob_1_4_10_a:
  assumes "f ` A \<subseteq> B"
    and "g ` B \<subseteq> C"
    and "(g \<circ> f) ` A = C"
  shows "g ` B = C"
  using assms by fastforce

proposition prob_1_4_10_b:
  assumes -- \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    -- \<open>The assumption @{prop "g ` B \<subseteq> C"} is not necessary.\<close>
    "inj_on (g \<circ> f) A"
  shows "inj_on f A"
  using assms by (fact inj_on_imageI2)

proposition prob_1_4_11:
  assumes "f ` A = B"
    -- \<open>The assumption @{prop "g ` B \<subseteq> C"} is not necessary.\<close>
    -- \<open>The assumption @{prop "g' ` B \<subseteq> C"} is not necessary.\<close>
    and "ext_eq_on A (g \<circ> f) (g' \<circ> f)"
  shows "ext_eq_on B g g'"
  using assms by fastforce

proposition prob_1_4_12:
  assumes "f ` A \<subseteq> B"
    and "f' ` A \<subseteq> B"
    -- \<open>The assumption @{prop "g ` B \<subseteq> C"} is not necessary.\<close>
    and "inj_on g B"
    and "ext_eq_on A (g \<circ> f) (g \<circ> f')"
  shows "ext_eq_on A f f'"
proof (rule ext_eq_onI)
  fix a
  assume "a \<in> A"
  with assms(4) have "g (f a) = g (f' a)" by auto
  moreover from \<open>a \<in> A\<close> and assms(1,2) have "f a \<in> B" and "f' a \<in> B" by auto
  moreover note assms(3)
  ultimately show "f a = f' a" by (elim inj_onD)
qed

proposition prob_1_4_13_a:
  assumes "f ` A \<subseteq> B"
    and "g ` B \<subseteq> C"
    and "(g \<circ> f) ` A = C"
    and "inj_on g B"
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
  with \<open>a \<in> A\<close> show "b \<in> f ` A" by auto
qed

proposition prob_1_4_13_b:
  assumes -- \<open>The assumption @{prop "g ` B \<subseteq> C"} is not necessary.\<close>
    "inj_on (g \<circ> f) A"
    and "f ` A = B"
  shows "inj_on g B"
proof (rule inj_onI)
  fix b b'
  assume "b \<in> B" and "b' \<in> B" and "g b = g b'"
  from this(1,2) and assms(2) obtain a and a'
    where "a \<in> A" and "b = f a" and "a' \<in> A" and "b' = f a'" by auto
  from \<open>g b = g b'\<close> and this(2,4) have "g (f a) = g (f a')" by simp
  with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and assms(1) have "a = a'" by (auto elim: inj_onD)
  with \<open>b = f a\<close> and \<open>b' = f a'\<close> show "b = b'" by simp
qed

proposition prob_1_4_14:
  assumes "f ` A \<subseteq> B"
    and "g ` B \<subseteq> A"
    and "g' ` B \<subseteq> A"
    and "id_on (g \<circ> f) A"
    and "id_on (f \<circ> g') B"
    and "is_inv_into A f f'"
  obtains "bij_betw f A B"
    and "ext_eq_on B g g'"
    and "ext_eq_on B g' f'"
proof -
  have "bij_betw f A B"
  proof (rule bij_betw_imageI)
    {
      fix a and a'
      assume "a \<in> A" and "a' \<in> A" and "f a = f a'"
      from this(3) have "g (f a) = g (f a')" by simp
      with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and assms(4) have "a = a'" using id_onD by fastforce
    }
    thus "inj_on f A" by (intro inj_onI)
    {
      fix b
      assume "b \<in> B"
      with assms(5) have "f (g' b) = b" by auto
      moreover from assms(3) and \<open>b \<in> B\<close> have "g' b \<in> A" by auto
      ultimately have "b \<in> f ` A" by force
    }
    hence "B \<subseteq> f ` A" ..
    with assms(1) show "f ` A = B" by simp
  qed
  moreover have "ext_eq_on B g g'"
  proof (rule ext_eq_onI)
    fix b
    assume "b \<in> B"
    with assms(5) have "f (g' b) = b" by auto
    hence "g (f (g' b)) = g b" by simp
    moreover from \<open>b \<in> B\<close> and assms(3) have "g' b \<in> A" by auto
    moreover note assms(4)
    ultimately show "g b = g' b" by auto
  qed
  moreover have "ext_eq_on B g' f'"
  proof (rule ext_eq_onI)
    fix b
    assume "b \<in> B"
    with assms(5) have "f (g' b) = b" by auto
    hence "f' (f (g' b)) = f' b" by simp
    moreover from \<open>b \<in> B\<close> and assms(3) have "g' b \<in> A" by auto
    moreover note assms(6)
    ultimately show "g' b = f' b" by (auto dest: is_inv_intoD1)
  qed
  ultimately show "thesis" by (fact that)
qed

abbreviation \<chi> :: "'a set \<Rightarrow> 'a \<Rightarrow> int"
  where "\<chi> \<equiv> indicator"

lemma indicator_definition:
  obtains "x \<in> X \<Longrightarrow> \<chi> X x = 1"
  | "x \<notin> X \<Longrightarrow> \<chi> X x = 0"
  by simp

lemma chi_0_1:
  shows "\<chi> A a \<in> {0, 1}"
proof -
  {
    assume "a \<in> A"
    hence "\<chi> A a = 1" by simp
  }
  moreover {
    assume "a \<notin> A"
    hence "\<chi> A a = 0" by simp
  }
  ultimately show "\<chi> A a \<in> {0, 1}" by blast
qed

lemma one_leq_chiD:
  assumes "1 \<le> \<chi> A a"
  shows "a \<in> A"
proof -
  from assms and chi_0_1 have "\<chi> A a = 1" by force
  thus "?thesis" by (simp only: indicator_eq_1_iff)
qed

proposition prob_1_4_15_0_a:
  assumes "A \<subseteq> X"
    and "B \<subseteq> X"
    and "\<And>x. x \<in> X \<Longrightarrow> \<chi> A x \<le> \<chi> B x"
  shows "A \<subseteq> B"
proof (rule subsetI)
  fix a
  assume "a \<in> A"
  hence "1 = \<chi> A a" by simp
  also have "\<dots> \<le> \<chi> B a"
  proof -
    from \<open>a \<in> A\<close> and assms(1) have "a \<in> X" by auto
    with assms(3) show "?thesis" by simp
  qed
  finally have "1 \<le> \<chi> B a" by simp
  thus "a \<in> B" by (auto dest: one_leq_chiD)
qed

proposition prob_1_4_15_0_b:
  assumes "A \<subseteq> X"
    and "B \<subseteq> X"
    and "A \<subseteq> B"
    and "x \<in> X"
  shows "\<chi> A x \<le> \<chi> B x"
proof -
  from assms consider (A) "x \<in> A" | (B) "x \<in> B - A" | (X) "x \<in> X - B" by auto
  thus "?thesis"
  proof cases
    case A
    with assms(3) have "x \<in> A" and "x \<in> B" by auto
    thus "?thesis" by simp
  next
    case B
    hence "x \<notin> A" and "x \<in> B" by auto
    thus "?thesis" by simp
  next
    case X
    with assms(3) have "x \<notin> A" and "x \<notin> B" by auto
    thus "?thesis" by simp
  qed
qed

proposition prob_1_4_15:
  assumes "A \<subseteq> X"
    and "B \<subseteq> X"
  shows "(\<forall>x \<in> X. \<chi> A x \<le> \<chi> B x) \<longleftrightarrow> A \<subseteq> B"
proof (rule iffI)
  assume "\<forall>x \<in> X. \<chi> A x \<le> \<chi> B x"
  with assms show "A \<subseteq> B" using prob_1_4_15_0_a by metis
next
  assume "A \<subseteq> B"
  with assms show "\<forall>x \<in> X. \<chi> A x \<le> \<chi> B x" using prob_1_4_15_0_b by metis
qed

proposition prob_1_4_15_a:
  shows "\<chi> (A \<inter> B) a = \<chi> A a * \<chi> B a"
  by (fact indicator_inter_arith)

proposition prob_1_4_15_b:
  shows "\<chi> (A \<union> B) a = \<chi> A a + \<chi> B a - \<chi> (A \<inter> B) a"
proof -
  have "\<chi> (A \<union> B) a = \<chi> A a + \<chi> B a - \<chi> A a * \<chi> B a" by (fact indicator_union_arith)
  thus "?thesis" by (simp only: prob_1_4_15_a)
qed

proposition prob_1_4_15_c:
  assumes -- \<open>The assumption @{prop "A \<subseteq> X"} is not necessary.\<close>
    "x \<in> X"
  shows "\<chi> (X - A) x = 1 - \<chi> A x"
proof -
  have "\<chi> (X - A) x = \<chi> X x * (1 - \<chi> A x)" by (fact indicator_diff)
  also from assms have "\<dots> = 1 - \<chi> A x" by simp
  finally show "?thesis" .
qed

proposition prob_1_4_15_d:
  shows "\<chi> (A - B) x = \<chi> A x * (1 - (\<chi> B x))"
  by (fact indicator_diff)

proposition prob_1_4_15_e:
  shows "\<chi> (A \<triangle> B) x = \<bar>\<chi> A x - \<chi> B x\<bar>"
proof -
  consider (a) "x \<in> A" and "x \<in> B"
    | (b) "x \<in> A" and "x \<notin> B"
    | (c) "x \<notin> A" and "x \<in> B"
    | (d) "x \<notin> A" and "x \<notin> B"
    by auto
  thus "?thesis"
  proof cases
    case a
    hence "x \<notin> A \<triangle> B" by simp
    hence "\<chi> (A \<triangle> B) x = 0" by simp
    moreover from a have "\<bar>\<chi> A x - \<chi> B x\<bar> = 0" by simp
    ultimately show "?thesis" by simp
  next
    case b
    hence "x \<in> A \<triangle> B" by simp
    hence "\<chi> (A \<triangle> B) x = 1" by simp
    moreover from b have "\<bar>\<chi> A x - \<chi> B x\<bar> = 1" by simp
    ultimately show "?thesis" by simp
  next
    case c
    hence "x \<in> A \<triangle> B" by simp
    hence "\<chi> (A \<triangle> B) x = 1" by simp
    moreover from c have "\<bar>\<chi> A x - \<chi> B x\<bar> = 1" by simp
    ultimately show "?thesis" by simp
  next
    case d
    hence "x \<notin> A \<triangle> B" by simp
    hence "\<chi> (A \<triangle> B) x = 0" by simp
    moreover from d have "\<bar>\<chi> A x - \<chi> B x\<bar> = 0" by simp
    ultimately show "?thesis" by simp
  qed
qed

(* TODO: prob_1_4_16 *)
(* TODO: prob_1_4_17 *)
(* TODO: prob_1_4_18 *)
(* TODO: prob_1_4_19 *)

end
