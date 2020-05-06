theory Section_1_5
  imports Main
    "HOL-Library.Disjoint_Sets"
    "HOL-Library.FuncSet"
    "Section_1_4"
begin

section "Indexed Families, General Products"

subsection \<open>A) Infinite and Finite Sequence of Elements\<close>

subsection \<open>B) Family of Elements\<close>

subsection \<open>C) Families of Sets and Their Union and Intersection\<close>

proposition prop_1_5_1:
  shows "(\<Union>l \<in> \<Lambda>. A l) \<inter> B = (\<Union>l \<in> \<Lambda>. (A l \<inter> B))"
  by simp

proposition prop_1_5_1':
  shows "(\<Inter>l \<in> \<Lambda>. A l) \<union> B = (\<Inter>l \<in> \<Lambda>. A l \<union> B)"
  by simp

proposition prop_1_5_2:
  assumes "\<Lambda> \<noteq> {}" \<comment> \<open>This assumption is not specified in the book. However, there exits a
                       counterexample without it.\<close>
    \<comment> \<open>The assumption @{prop "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<subseteq> X"} is not necessary.\<close>
  shows "X - (\<Union>l \<in> \<Lambda>. A l) = (\<Inter>l \<in> \<Lambda>. (X - A l))"
  using assms by simp

proposition prop_1_5_2':
  \<comment> \<open>The assumption @{prop "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<subseteq> X"} is not necessary.\<close>
  shows "X - (\<Inter>l \<in> \<Lambda>. A l) = (\<Union>l \<in> \<Lambda>. X - A l)"
  by simp

proposition prop_1_5_3:
  \<comment> \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
  \<comment> \<open>The assumption @{prop "\<And>l. l \<in> \<Lambda> \<Longrightarrow> P l \<subseteq> A"} is not necessary.\<close>
  shows "f ` (\<Union>l \<in> \<Lambda>. P l) = (\<Union>l \<in> \<Lambda>. f ` (P l))"
  by (fact image_UN)

proposition prop_1_5_4:
  \<comment> \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
  \<comment> \<open>The assumption @{prop "\<And>l. l \<in> \<Lambda> \<Longrightarrow> P l \<subseteq> A"} is not necessary.\<close>
  shows "f ` (\<Inter>l \<in> \<Lambda>. P l) \<subseteq> (\<Inter>l \<in> \<Lambda>. f ` (P l))"
  by auto

proposition prop_1_5_3':
  \<comment> \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
  \<comment> \<open>The assumption @{prop "\<And>\<mu>. \<mu> \<in> M \<Longrightarrow> Q \<mu> \<subseteq> B"} is not necessary.\<close>
  shows "(f -` (\<Union>\<mu> \<in> M. Q \<mu>)) \<inter> A = (\<Union>\<mu> \<in> M. (f -` (Q \<mu>)) \<inter> A)"
  by auto

proposition prop_1_5_4':
  assumes "M \<noteq> {}" \<comment> \<open>This assumption is not specified in the book. However, there exists a
                       counterexample without it.\<close>
    \<comment> \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    \<comment> \<open>The assumption @{prop "\<And>\<mu>. \<mu> \<in> M \<Longrightarrow> Q \<mu> \<subseteq> B"} is not necessary.\<close>
  shows "(f -` (\<Inter>\<mu> \<in> M. Q \<mu>)) \<inter> A = (\<Inter>\<mu> \<in> M. (f -` (Q \<mu>)) \<inter> A)"
  using assms by auto

subsection \<open>Generalized Direct Product, Axiom of Choice\<close>

definition dprod :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "dprod \<Lambda> A \<equiv> {a \<in> \<Lambda> \<rightarrow>\<^sub>E \<Union>(A ` \<Lambda>). \<forall>l \<in> \<Lambda>. a l \<in> A l}"

syntax "_dprod" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) set"
  ("(3\<Prod>\<^sub>d _\<in>_./ _)" 10)

translations "\<Prod>\<^sub>d l \<in> \<Lambda>. A" \<rightleftharpoons> "CONST dprod \<Lambda> (\<lambda>l. A)"

lemma dprodI [intro]:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> a l \<in> A l"
    and "\<And>l. l \<notin> \<Lambda> \<Longrightarrow> a l = undefined"
  shows "a \<in> (\<Prod>\<^sub>d l \<in> \<Lambda>. A l)"
  using assms unfolding dprod_def by auto

lemma dprodD1 [dest]:
  assumes "a \<in> (\<Prod>\<^sub>d l \<in> \<Lambda>. A l)"
    and "l \<in> \<Lambda>"
  shows "a l \<in> A l"
  using assms unfolding dprod_def by blast

lemma dprodD2 [dest]:
  assumes "a \<in> (\<Prod>\<^sub>d l \<in> \<Lambda>. A l)"
    and "l \<notin> \<Lambda>"
  shows "a l = undefined"
  using assms unfolding dprod_def by blast

lemma dprodE [elim]:
  assumes "a \<in> (\<Prod>\<^sub>d l \<in> \<Lambda>. A l)"
  obtains "\<And>l. l \<in> \<Lambda> \<Longrightarrow> a l \<in> A l"
    and "\<And>l. l \<notin> \<Lambda> \<Longrightarrow> a l = undefined"
  using assms unfolding dprod_def by blast

theorem AC:
  assumes "\<forall>l \<in> \<Lambda>. A l \<noteq> {}"
  shows "(\<Pi> l \<in> \<Lambda>. A l) \<noteq> {}"
proof -
  let ?a = "\<lambda>l. if l \<in> \<Lambda> then (SOME al. al \<in> A l) else undefined"
  {
    fix l
    assume "l \<in> \<Lambda>"
    with assms have "A l \<noteq> {}" by auto
    with \<open>l \<in> \<Lambda>\<close> have "?a l \<in> A l" by (auto intro: some_in_eq[THEN iffD2])
  }
  hence "?a \<in> (\<Pi> l \<in> \<Lambda>. A l)" by simp
  thus ?thesis by auto
qed

lemma AC_E:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<noteq> {}"
  obtains a where "a \<in> (\<Pi> l \<in> \<Lambda>. A l)"
proof -
  from assms have "(\<Pi> l \<in> \<Lambda>. A l) \<noteq> {}" by (simp add: AC)
  then obtain a where "a \<in> (\<Pi> l \<in> \<Lambda>. A l)" by blast
  thus "thesis" by (fact that)
qed

lemma AC_E_prop:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> \<exists>al \<in> A l. P l al"
  obtains a where "a \<in> (\<Pi> l \<in> \<Lambda>. A l)"
    and "\<And>l. l \<in> \<Lambda> \<Longrightarrow> P l (a l)"
proof -
  let ?A' = "\<lambda>l'. {al \<in> A l'. P l' al}"
  {
    fix l
    assume "l \<in> \<Lambda>"
    with assms have "?A' l \<noteq> {}" by blast
  }
  then obtain a where *: "a \<in> (\<Pi> l \<in> \<Lambda>. ?A' l)" by (elim AC_E)
  {
    fix l
    assume "l \<in> \<Lambda>"
    with * have "a l \<in> ?A' l" by auto
    hence "a l \<in> A l" by simp
  }
  hence "a \<in> (\<Pi> l \<in> \<Lambda>. A l)" by simp
  moreover have "\<And>l. l \<in> \<Lambda> \<Longrightarrow> P l (a l)"
  proof -
    fix l
    assume "l \<in> \<Lambda>"
    with * have "a l \<in> ?A' l" by auto
    thus "P l (a l)" by simp
  qed
  ultimately show "thesis" by (fact that)
qed

lemma AC_E_ex:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> \<exists>x. P l x"
  obtains a where "a \<in> (\<Pi> l \<in> \<Lambda>. {x. P l x})"
proof -
  {
    fix l
    assume "l \<in> \<Lambda>"
    with assms have "{x. P l x} \<noteq> {}" by simp
  }
  then obtain a where a: "a \<in> (\<Pi> l \<in> \<Lambda>. {x. P l x})" by (elim AC_E)
  thus "thesis" by (fact that)
qed

lemma Pi_one_point:
  assumes "(\<Pi> l \<in> \<Lambda>. A l) \<noteq> {}"
    and "l \<in> \<Lambda>"
    and "al \<in> A l"
  obtains a where "a \<in> (\<Pi> l \<in> \<Lambda>. A l)"
    and "a l = al"
proof -
  from assms obtain a where "a \<in> (\<Pi> l \<in> \<Lambda>. A l)" by blast
  let ?a' = "\<lambda>l'. if l' = l then al else a l'"
  {
    fix l'
    assume "l' \<in> \<Lambda>"
    {
      assume "l' = l"
      hence "?a' l' = al" by simp
      also from assms(3) have "\<dots> \<in> A l" by simp
      also from \<open>l' = l\<close> have "\<dots> = A l'" by simp
      finally have "?a' l' \<in> A l'" by simp
    }
    moreover {
      assume "l' \<noteq> l"
      hence "?a' l' = a l'" by simp
      also from \<open>a \<in> (\<Pi> l \<in> \<Lambda>. A l)\<close> and \<open>l' \<in> \<Lambda>\<close> have "\<dots> \<in> A l'" by auto
      finally have "?a' l' \<in> A l'" by simp
    }
    ultimately have "?a' l' \<in> A l'" by simp
  }
  hence "?a' \<in> (\<Pi> l \<in> \<Lambda>. A l)" by simp
  moreover have "?a' l = al" by simp
  ultimately show "thesis" by (fact that)
qed

definition pie :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "pie \<Lambda> a = (\<lambda>l. if l \<in> \<Lambda> then a l else undefined)"

syntax
"_pie" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("(1'(_\<in>_./ _'))")

translations
"(l\<in>\<Lambda>. a)" \<rightleftharpoons> "CONST pie \<Lambda> (\<lambda>l. a)"

lemma pie_eq1 [iff]:
  assumes "l \<in> \<Lambda>"
  shows "(l \<in> \<Lambda>. a l) l = a l"
  using assms unfolding pie_def by simp

lemma pie_eq2 [iff]:
  assumes "l \<notin> \<Lambda>"
  shows "(l \<in> \<Lambda>. a l) l = undefined"
  using assms unfolding pie_def by simp

definition proj :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"
  where "proj l a = a l"

lemmas proj_eq = proj_def

lemma Pi_imp_proj:
  assumes "a \<in> (\<Pi> l \<in> \<Lambda>. A l)"
    and "l \<in> \<Lambda>"
  shows "proj l a \<in> A l"
  using assms unfolding proj_def by auto

subsection \<open>E) A Theorem on Map\<close>

theorem thm_1_7_a_a:
  assumes "f ` A = B"
  obtains s where "s ` B \<subseteq> A"
    and "id_on (f \<circ> s) B"
proof -
  {
    fix b
    assume "b \<in> B"
    with assms(1) obtain a where "a \<in> A" and "b = f a" by auto
    hence "a \<in> f -` {b}" by auto
    with \<open>a \<in> A\<close> have "(f -` {b}) \<inter> A \<noteq> {}" by auto
  }
  then obtain s where *: "s \<in> (\<Pi> b \<in> B. (f -` {b}) \<inter> A)" by (rule AC_E)
  have "s ` B \<subseteq> A"
  proof (rule subsetI)
    fix a
    assume "a \<in> s ` B"
    then obtain b where "b \<in> B" and "a = s b" by auto
    from this(1) and * have "s b \<in> A" by auto
    with \<open>a = s b\<close> show "a \<in> A" by simp
  qed
  moreover have "id_on (f \<circ> s) B"
  proof (rule id_onI)
    fix b
    assume "b \<in> B"
    with * have "s b \<in> f -` {b}" by auto
    thus "(f \<circ> s) b = b" by simp
  qed
  ultimately show "thesis" by (fact that)
qed

theorem thm_1_7_a_b:
  assumes "f ` A \<subseteq> B"
    and "s ` B \<subseteq> A"
    and "id_on (f \<circ> s) B"
  shows "f ` A = B"
proof -
  from assms(3) have "(f \<circ> s) ` B = B" by (fact id_on_imp_surj_on)
  with assms(1,2) show ?thesis by (intro prob_1_4_10_a[where A = "B" and f = "s" and g = "f"])
qed

theorem thm_1_7_a:
  assumes "f ` A \<subseteq> B"
  shows "f ` A = B \<longleftrightarrow> (\<exists>s. s ` B \<subseteq> A \<and> id_on (f \<circ> s) B)"
proof (rule iffI)
  assume "f ` A = B"
  then obtain s where "s ` B \<subseteq> A" and "id_on (f \<circ> s) B" by (rule thm_1_7_a_a)
  thus "\<exists>s. s ` B \<subseteq> A \<and> id_on (f \<circ> s) B" by auto
next
  assume "\<exists>s. s ` B \<subseteq> A \<and> id_on (f \<circ> s) B"
  then obtain s where "s ` B \<subseteq> A" and "id_on (f \<circ> s) B" by auto
  with assms show "f ` A = B" by (rule thm_1_7_a_b)
qed

theorem thm_1_7_b_a:
  assumes "A = {} \<Longrightarrow> B = {}" \<comment> \<open>This assumption is not specified in the book. However, there
                                  exists a counterexample without it.\<close>
    \<comment> \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    and "inj_on f A"
  obtains r where "r ` B \<subseteq> A"
    and "id_on (r \<circ> f) A"
proof -
  {
    assume "A = {}"
    with assms(1) have "B = {}" by simp
    let ?r = "\<lambda>b. undefined"
    from \<open>A = {}\<close> and \<open>B = {}\<close> have "?r ` B \<subseteq> A" by simp
    moreover from \<open>A = {}\<close> have "id_on (?r \<circ> f) A" by simp
    ultimately have "thesis" by (fact that)
  }
  moreover {
    assume "A \<noteq> {}"
    then obtain a where "a \<in> A" by auto
    let ?r = "\<lambda>b. if b \<in> f ` A then the_inv_into A f b else a"
    have "?r ` B \<subseteq> A"
    proof (rule subsetI)
      fix a'
      assume "a' \<in> ?r ` B"
      then obtain b where "b \<in> B" and "a' = ?r b" by auto
      {
        assume "b \<in> f ` A"
        then obtain a'' where "a'' \<in> A" and "b = f a''" by auto
        from \<open>b \<in> f ` A\<close> have "?r b = the_inv_into A f b" by simp
        with \<open>a' = ?r b\<close> have "the_inv_into A f b = a'" by simp
        with \<open>b = f a''\<close> have "the_inv_into A f (f a'') = a'" by simp
        moreover from this and assms(2) and \<open>a'' \<in> A\<close> have "the_inv_into A f (f a'') = a''"
          by (intro the_inv_into_f_f)
        ultimately have "a' = a''" by simp
        with \<open>a'' \<in> A\<close> have "a' \<in> A" by simp
      }
      moreover {
        assume "b \<notin> f ` A"
        hence "?r b = a" by simp
        with \<open>a' = ?r b\<close> have "a' = a" by simp
        with \<open>a \<in> A\<close> have "a' \<in> A" by simp
      }
      ultimately show "a' \<in> A" by auto
    qed
    moreover have "id_on (?r \<circ> f) A"
    proof (rule id_onI)
      fix a'
      assume "a' \<in> A"
      hence "f a' \<in> f ` A" by simp
      hence "?r (f a') = the_inv_into A f (f a')" by simp
      also from assms(2) and \<open>a' \<in> A\<close> have "\<dots> = a'" by (intro the_inv_into_f_f)
      finally have "?r (f a') = a'" .
      thus "(?r \<circ> f) a' = a'" by simp
    qed
    ultimately have "thesis" by (fact that)
  }
  ultimately show "thesis" by auto
qed

theorem thm_1_7_b_b:
  assumes \<comment> \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    \<comment> \<open>The assumption @{prop "r ` B \<subseteq> A"} is not necessary.\<close>
    "id_on (r \<circ> f) A"
  shows "inj_on f A"
proof -
  from assms have "inj_on (r \<circ> f) A" by (fact id_on_imp_inj_on)
  thus ?thesis by (fact prob_1_4_10_b)
qed

theorem thm_1_7_b:
  assumes "A = {} \<Longrightarrow> B = {}"\<comment> \<open>This assumption is not specified in the book. However, there
                                 exists a counterexample without it.\<close>
  shows "inj_on f A \<longleftrightarrow> (\<exists>r. r ` B \<subseteq> A \<and> id_on (r \<circ> f) A)"
  using assms thm_1_7_b_a thm_1_7_b_b by metis

definition right_inv_into :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "right_inv_into A f s \<longleftrightarrow> s ` (f ` A) \<subseteq> A \<and> id_on (f \<circ> s) (f ` A)"

lemma right_inv_into:
  obtains s where "right_inv_into A f s"
proof -
  obtain s where "s ` f ` A \<subseteq> A" and "id_on (f \<circ> s) (f ` A)" using thm_1_7_a_a by blast
  thus "thesis" using that unfolding right_inv_into_def by simp
qed

lemma right_inv_intoI:
  assumes "\<And>b. b \<in> f ` A \<Longrightarrow> s b \<in> A"
    and "\<And>b. b \<in> f ` A \<Longrightarrow> f (s b) = b"
  shows "right_inv_into A f s"
  using assms unfolding right_inv_into_def by fastforce

lemma right_inv_intoD1:
  assumes "right_inv_into A f s"
  shows "s ` (f ` A) \<subseteq> A"
  using assms unfolding right_inv_into_def by simp

lemma right_inv_intoD2_pf:
  assumes "right_inv_into A f s"
  shows "id_on (f \<circ> s) (f ` A)"
  using assms unfolding right_inv_into_def by simp

lemma right_inv_intoD2:
  assumes "right_inv_into A f s"
    and "x \<in> f ` A"
  shows "f (s x) = x"
proof -
  from assms(1) have "id_on (f \<circ> s) (f ` A)" by (fact right_inv_intoD2_pf)
  with assms(2) have "(f \<circ> s) x = x" by blast
  thus ?thesis by simp
qed

definition left_inv_into :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "left_inv_into A f r \<longleftrightarrow> id_on (r \<circ> f) A"

lemma left_inv_into:
  assumes "inj_on f A"
  obtains r where "left_inv_into A f r"
proof -
  {
    assume "A = {}"
    then obtain r where "id_on (r \<circ> f) A" by simp
    hence "left_inv_into A f r" unfolding left_inv_into_def by simp
    hence "thesis" by (fact that)
  }
  moreover {
    assume "A \<noteq> {}"
    with assms obtain r where "id_on (r \<circ> f) A" by (blast intro: thm_1_7_b_a)
    hence "left_inv_into A f r" unfolding left_inv_into_def by simp
    hence "thesis" by (fact that)
  }
  ultimately show "thesis" by auto
qed

lemma left_inv_intoI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> r (f a) = a"
  shows "left_inv_into A f r"
  using assms unfolding left_inv_into_def by auto

lemma left_inv_intoD1:
  assumes "left_inv_into A f r"
  shows "r ` f ` A \<subseteq> A"
  using assms unfolding left_inv_into_def by auto

lemma left_inv_intoD2_pf:
  assumes "left_inv_into A f r"
  shows "id_on (r \<circ> f) A"
  using assms unfolding left_inv_into_def by simp

lemma left_inv_intoD2:
  assumes "left_inv_into A f r"
    and "a \<in> A"
  shows "r (f a) = a"
  using assms unfolding left_inv_into_def by fastforce

corollary cor_inj_on_iff_surj_on_a:
  assumes "A = {} \<Longrightarrow> B = {}"
    and "f ` A \<subseteq> B"
    and "inj_on f A"
  obtains g where "g ` B = A"
proof -
  from assms(1,3) obtain g where "g ` B \<subseteq> A" and "id_on (g \<circ> f) A" by (elim thm_1_7_b_a)
  with \<open>f ` A \<subseteq> B\<close> have "g ` B = A" by (intro thm_1_7_a_b)
  thus "thesis" by (fact that)
qed

corollary cor_inj_on_iff_surj_on_b:
  assumes "f ` A = B"
  obtains g where "g ` B \<subseteq> A" and "inj_on g B"
proof -
  from assms obtain g where "g ` B \<subseteq> A" and "id_on (f \<circ> g) B" by (elim thm_1_7_a_a)
  from this(2) have "inj_on g B" by (intro thm_1_7_b_b)
  with \<open>g ` B \<subseteq> A\<close> show "thesis" by (fact that)
qed

corollary cor_inj_on_iff_surj_on:
  assumes "A = {} \<Longrightarrow> B = {}" \<comment> \<open>This assumption is not specified in the book. However, there
                                  exists a counterexample without it.\<close>
  shows "(\<exists>f. f ` A \<subseteq> B \<and> inj_on f A) \<longleftrightarrow> (\<exists>g. g ` B = A)"
proof (rule iffI)
  assume "\<exists>f. f ` A \<subseteq> B \<and> inj_on f A"
  then obtain f where "f ` A \<subseteq> B" and "inj_on f A" by auto
  with assms obtain g where "g ` B = A" by (elim cor_inj_on_iff_surj_on_a)
  thus "\<exists>f. f ` B = A" by auto
next
  assume "\<exists>g. g ` B = A"
  then obtain g where "g ` B = A" ..
  then obtain f where "f ` A \<subseteq> B" and "inj_on f A" by (elim cor_inj_on_iff_surj_on_b)
  thus "\<exists>f. f ` A \<subseteq> B \<and> inj_on f A" by auto
qed

subsection \<open>F) Multivariate Maps\<close>

subsection \<open>Problems\<close>

(* TODO: prob_1_5_1 *)

proposition prob_1_5_5_a:
  shows "(\<Union>l \<in> \<Lambda>. A l) \<inter> (\<Union>\<mu> \<in> M. B \<mu>) = (\<Union>(l, \<mu>) \<in> \<Lambda> \<times> M. A l \<inter> B \<mu>)"
  by auto

proposition prob_1_5_5_b:
  shows "(\<Inter>l \<in> \<Lambda>. A l) \<union> (\<Inter>\<mu> \<in> M. B \<mu>) = (\<Inter>(l, \<mu>) \<in> \<Lambda> \<times> M. A l \<union> B \<mu>)"
  by blast

proposition prob_1_5_5_c:
  shows "(\<Union>l \<in> \<Lambda>. A l) \<times> (\<Union>\<mu> \<in> M. B \<mu>) = (\<Union>(l, \<mu>) \<in> \<Lambda> \<times> M. A l \<times> B \<mu>)"
  by auto

proposition prob_1_5_5_d:
  assumes "\<Lambda> \<noteq> {}"
    and "M \<noteq> {}" \<comment> \<open>These assumptions are not specified in the book. However, there exists a
                     counterexample without them.\<close>
  shows "(\<Inter>l \<in> \<Lambda>. A l) \<times> (\<Inter>\<mu> \<in> M. B \<mu>) = (\<Inter>(l, \<mu>) \<in> \<Lambda> \<times> M. A l \<times> B \<mu>)"
  using assms by blast

lemma disjoint_family_on_imp_eq:
  assumes "disjoint_family_on A \<Lambda>"
    and "l \<in> \<Lambda>"
    and "l' \<in> \<Lambda>"
    and "a \<in> A l"
    and "a \<in> A l'"
  shows "l = l'"
proof -
  from assms(4,5) have "a \<in> A l \<inter> A l'" by simp
  {
    assume "l \<noteq> l'"
    with assms(1-3) have "A l \<inter> A l' = {}" by (elim disjoint_family_onD)
    with \<open>a \<in> A l \<inter> A l'\<close> have "False" by simp
  }
  thus ?thesis by auto
qed

lemma disjoint_family_on_imp_uniq_idx:
  assumes "disjoint_family_on A \<Lambda>"
    and "a \<in> (\<Union>l \<in> \<Lambda>. A l)"
  shows "\<exists>!l \<in> \<Lambda>. a \<in> A l"
proof (rule ex_ex1I)
  from assms(2) obtain l where "l \<in> \<Lambda>" and "a \<in> A l" by auto
  thus "\<exists>l. l \<in> \<Lambda> \<and> a \<in> A l" by auto
next
  thm disjoint_family_onD
  fix l and l'
  assume "l \<in> \<Lambda> \<and> a \<in> A l" and "l' \<in> \<Lambda> \<and> a \<in> A l'"
  with assms(1) show "l = l'" by (blast dest: disjoint_family_on_imp_eq)
qed

proposition prob_1_5_6_existence:
  assumes "disjoint_family_on A \<Lambda>"
    and "\<And>l. l \<in> \<Lambda> \<Longrightarrow> (f l) ` (A l) \<subseteq> B"
  obtains F where "F ` (\<Union>l \<in> \<Lambda>. A l) \<subseteq> B"
    and "\<And>l. l \<in> \<Lambda> \<Longrightarrow> ext_eq_on (A l) F (f l)"
proof -
  let ?F = "\<lambda>a. f (THE l. l \<in> \<Lambda> \<and> a \<in> A l) a"
  have "?F ` (\<Union>l \<in> \<Lambda>. A l) \<subseteq> B"
  proof (rule image_subsetI)
    fix a
    assume "a \<in> (\<Union>l \<in> \<Lambda>. A l)"
    with assms(1) have "\<exists>!l \<in> \<Lambda>. a \<in> A l" by (elim disjoint_family_on_imp_uniq_idx)
    then obtain l where "l \<in> \<Lambda> \<and> a \<in> A l" by auto
    hence "l \<in> \<Lambda>" and \<open>a \<in> A l\<close> by auto
    from \<open>\<exists>!l \<in> \<Lambda>. a \<in> A l\<close> and \<open>l \<in> \<Lambda> \<and> a \<in> A l\<close> have "(THE l. l \<in> \<Lambda> \<and> a \<in> A l) = l" by auto
    hence "?F a = f l a" by simp
    from assms(2) and \<open>l \<in> \<Lambda>\<close> have "(f l) ` (A l) \<subseteq> B" by simp
    with \<open>a \<in> A l\<close> have "f l a \<in> B" by auto
    with \<open>?F a = f l a\<close> show "?F a \<in> B" by simp
  qed
  moreover have "\<And>l. l \<in> \<Lambda> \<Longrightarrow> ext_eq_on (A l) ?F (f l)"
  proof -
    fix l
    assume "l \<in> \<Lambda>"
    {
      fix a
      assume "a \<in> A l"
      with \<open>l \<in> \<Lambda>\<close> have "l \<in> \<Lambda> \<and> a \<in> A l" ..
      moreover {
        fix l'
        assume *: "l' \<in> \<Lambda> \<and> a \<in> A l'"
        hence "l' \<in> \<Lambda>" and "a \<in> A l'" by simp+
        with \<open>l \<in> \<Lambda>\<close> and \<open>a \<in> A l\<close> and assms(1) have "l' = l" by (elim disjoint_family_on_imp_eq)
      }
      ultimately have "(THE l. l \<in> \<Lambda> \<and> a \<in> A l) = l" by (intro the_equality)
      hence "?F a = f l a" by simp
    }
    thus "ext_eq_on (A l) ?F (f l)" by (intro ext_eq_onI)
  qed
  ultimately show "thesis" by (fact that)
qed

proposition prob_1_5_6_uniqueness:
  assumes \<comment> \<open>The assumption @{prop "disjoint_family_on A \<Lambda>"} is not necessary.\<close>
    \<comment> \<open>The assumption @{prop "F ` (\<Union>l \<in> \<Lambda>. A l) \<subseteq> B"} is not necessary.\<close>
    "\<And>l. l \<in> \<Lambda> \<Longrightarrow> ext_eq_on (A l) F (f l)"
    \<comment> \<open>The assumption @{prop "F' ` (\<Union>l \<in> \<Lambda>. A l) \<subseteq> B"} is not necessary.\<close>
    and "\<And>l. l \<in> \<Lambda> \<Longrightarrow> ext_eq_on (A l) F' (f l)"
  shows "ext_eq_on (\<Union>l \<in> \<Lambda>. A l) F F'"
proof (rule ext_eq_onI)
  fix a
  assume "a \<in> (\<Union>l \<in> \<Lambda>. A l)"
  then obtain l where "l \<in> \<Lambda>" and "a \<in> A l" by blast
  from this(1) and assms(1) have "ext_eq_on (A l) F (f l)" by simp
  also have "ext_eq_on (A l) \<dots> F'"
  proof -
    from \<open>l \<in> \<Lambda>\<close> and assms(2) have "ext_eq_on (A l) F' (f l)" by simp
    thus ?thesis by (fact ext_eq_on_sym)
  qed
  finally have "ext_eq_on (A l) F F'" .
  with \<open>a \<in> A l\<close> show "F a = F' a" by auto
qed

proposition prob_1_5_7:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<noteq> {}"
    and "l \<in> \<Lambda>"
  shows "(proj l) ` (\<Pi> l \<in> \<Lambda>. A l) = A l"
proof (rule surj_onI)
  fix a
  assume "a \<in> (\<Pi> l \<in> \<Lambda>. A l)"
  with assms(2) show "proj l a \<in> A l" by (intro Pi_imp_proj)
next
  fix al
  assume "al \<in> A l"
  moreover from assms(1) have "(\<Pi> l \<in> \<Lambda>. A l) \<noteq> {}" by (auto intro: AC)
  moreover note assms(2)
  ultimately obtain a where "a \<in> (\<Pi> l \<in> \<Lambda>. A l)" and "a l = al" by (elim Pi_one_point)
  from this(2) have "proj l a = al" unfolding proj_eq by simp
  with \<open>a \<in> (\<Pi> l \<in> \<Lambda>. A l)\<close> show "al \<in> proj l ` Pi \<Lambda> A" by auto
qed

proposition prob_1_5_8_a:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<noteq> {}"
    and "(\<Pi> l \<in> \<Lambda>. A l) \<subseteq> (\<Pi> l \<in> \<Lambda>. B l)"
    and "l \<in> \<Lambda>"
  shows "A l \<subseteq> B l"
proof -
  {
    assume "\<exists>l \<in> \<Lambda>. B l = {}"
    then obtain l' where "l' \<in> \<Lambda>" and "B l' = {}" by auto
    hence "(\<Pi> l \<in> \<Lambda>. B l) = {}" by auto
    with assms(2) have "(\<Pi> l \<in> \<Lambda>. A l) = {}" by simp
    moreover from assms(1) have "(\<Pi> l \<in> \<Lambda>. A l) \<noteq> {}" by (auto intro: AC)
    ultimately have "False" by simp
  }
  hence *: "\<forall>l \<in> \<Lambda>. B l \<noteq> {}" by auto
  from assms(1,3) have "A l = (proj l) ` (\<Pi> l \<in> \<Lambda>. A l)" by (fact prob_1_5_7[THEN sym])
  also from assms(2) have "\<dots> \<subseteq> (proj l) ` (\<Pi> l \<in> \<Lambda>. B l)" by auto
  also from * and assms(3) have "\<dots> = B l" by (simp add: prob_1_5_7)
  finally show ?thesis .
qed

proposition prob_1_5_8_b:
  assumes \<comment> \<open>The assumption @{prop "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<noteq> {}"} is not necessary.\<close>
    "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<subseteq> B l"
  shows "(\<Pi> l \<in> \<Lambda>. A l) \<subseteq> (\<Pi> l \<in> \<Lambda>. B l)"
  using assms by (fact Pi_mono)

proposition prob_1_5_8:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<noteq> {}"
  shows "(\<Pi> l \<in> \<Lambda>. A l) \<subseteq> (\<Pi> l \<in> \<Lambda>. B l) \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. A l \<subseteq> B l)"
proof (rule iffI)
  assume "(\<Pi> l \<in> \<Lambda>. A l) \<subseteq> (\<Pi> l \<in> \<Lambda>. B l)"
  {
    fix l
    assume "l \<in> \<Lambda>"
    with assms and \<open>(\<Pi> l \<in> \<Lambda>. A l) \<subseteq> (\<Pi> l \<in> \<Lambda>. B l)\<close> have "A l \<subseteq> B l" by (rule prob_1_5_8_a)
  }
  thus "\<forall>l \<in> \<Lambda>. A l \<subseteq> B l" ..
next
  assume "\<forall>l \<in> \<Lambda>. A l \<subseteq> B l"
  thus "(\<Pi> l \<in> \<Lambda>. A l) \<subseteq> (\<Pi> l \<in> \<Lambda>. B l)" by (auto intro: prob_1_5_8_b)
qed

proposition prob_1_5_9:
  shows "(\<Pi> l \<in> \<Lambda>. A l) \<inter> (\<Pi> l \<in> \<Lambda>. B l) = (\<Pi> l \<in> \<Lambda>. A l \<inter> B l)"
  by (fact Pi_Int)

proposition prob_1_5_10:
  assumes "(\<Pi> l \<in> \<Lambda>. A l) \<noteq> {}" \<comment> \<open>This assumption is not specified in the book. However, there
                                     exists a counterexample without it.\<close>
    and "\<And>l. l \<in> \<Lambda> \<Longrightarrow> (f l) ` (A l) \<subseteq> B l"
  defines F: "F a \<equiv> (l \<in> \<Lambda>. f l (a l))"
  obtains "(\<forall>b \<in> (\<Pi> l \<in> \<Lambda>. B l). \<exists>a \<in> (\<Pi> l \<in> \<Lambda>. A l). ext_eq_on \<Lambda> (F a) b)
           \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. f l ` A l = B l)" (*(is "?L0 \<longleftrightarrow> ?R0")*)
    and "(\<forall>a \<in> (\<Pi> l \<in> \<Lambda>. A l). \<forall>a' \<in> (\<Pi> l \<in> \<Lambda>. A l). F a = F a' \<longrightarrow> ext_eq_on \<Lambda> a a')
           \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. inj_on (f l) (A l))" (*(is "?L1 \<longleftrightarrow> ?R1")*)
proof -
  let ?\<AA> = "\<Pi> l \<in> \<Lambda>. A l"
    and ?\<BB> = "\<Pi> l \<in> \<Lambda>. B l"
  let ?L0 = "\<forall>b \<in> ?\<BB>. \<exists>a \<in> ?\<AA>. ext_eq_on \<Lambda> (F a) b"
    and ?R0 = "\<forall>l \<in> \<Lambda>. f l ` A l = B l"
    and ?L1 = "\<forall>a \<in> ?\<AA>. \<forall>a' \<in> ?\<AA>. F a = F a' \<longrightarrow> ext_eq_on \<Lambda> a a'"
    and ?R1 = "\<forall>l \<in> \<Lambda>. inj_on (f l) (A l)"
  {
    fix a
    assume "a \<in> ?\<AA>"
    {
      fix l
      assume "l \<in> \<Lambda>"
      with \<open>a \<in> ?\<AA>\<close> have "a l \<in> A l" by auto
      with \<open>l \<in> \<Lambda>\<close> and assms(2) have "f l (a l) \<in> B l" by auto
      with \<open>l \<in> \<Lambda>\<close> have "F a l \<in> B l" unfolding F by simp
    }
    hence "F a \<in> ?\<BB>" by simp
  }
  hence "F ` ?\<AA> \<subseteq> ?\<BB>" by auto
  with assms(1) have "?\<BB> \<noteq> {}" by blast
  have *: "F a l = f l (a l)" if "l \<in> \<Lambda>" for a and l using that unfolding F by simp
  have "?L0 \<longleftrightarrow> ?R0"
  proof (rule iffI)
    assume "?L0"
    {
      fix l
      assume "l \<in> \<Lambda>"
      {
        fix al
        assume "al \<in> A l"
        with \<open>l \<in> \<Lambda>\<close> have "f l al \<in> B l" by (auto dest: assms(2))
      }
      moreover {
        fix bl
        assume "bl \<in> B l"
        with \<open>?\<BB> \<noteq> {}\<close> and \<open>l \<in> \<Lambda>\<close> obtain b where "b \<in> ?\<BB>" and "b l = bl" by (elim Pi_one_point)
        from this(1) and \<open>?L0\<close> obtain a where "a \<in> ?\<AA>" and "ext_eq_on \<Lambda> (F a) b" by blast
        from this(2) and \<open>l \<in> \<Lambda>\<close> have "F a l = b l" by auto
        with \<open>l \<in> \<Lambda>\<close> and * have "f l (a l) = b l" by simp
        also from \<open>b l = bl\<close> have "\<dots> = bl" by simp
        moreover from \<open>a \<in> ?\<AA>\<close> and \<open>l \<in> \<Lambda>\<close> have "a l \<in> A l" by auto
        ultimately have "\<exists>al \<in> A l. f l al = bl" by auto
      }
      ultimately have "f l ` A l = B l" by blast
    }
    thus "?R0" by simp
  next
    assume "?R0"
    {
      fix b
      assume "b \<in> ?\<BB>"
      {
        fix l
        assume "l \<in> \<Lambda>"
        with \<open>b \<in> ?\<BB>\<close> have "b l \<in> B l" by auto
        with \<open>l \<in> \<Lambda>\<close> and \<open>?R0\<close> obtain al where "al \<in> A l" and "b l = f l al" by auto
        hence "\<exists>al \<in> A l. b l = f l al" by auto
      }
      then obtain a where "a \<in> ?\<AA>" and **: "\<And>l. l \<in> \<Lambda> \<Longrightarrow> b l = f l (a l)"
        using AC_E_prop[where P = "\<lambda>l. \<lambda>al. b l = f l al"] by blast
      {
        fix l
        assume "l \<in> \<Lambda>"
        with ** have "b l = f l (a l)" by simp
        also from \<open>l \<in> \<Lambda>\<close> and * have "\<dots> = F a l" by simp
        finally have "F a l = b l" by simp
      }
      with \<open>a \<in> ?\<AA>\<close> have "\<exists>a \<in> ?\<AA>. ext_eq_on \<Lambda> (F a) b" by auto
    }
    thus "?L0" by blast
  qed
  moreover have "?L1 \<longleftrightarrow> ?R1"
  proof (rule iffI)
    assume "?L1"
    {
      fix l
      assume "l \<in> \<Lambda>"
      {
        fix al and al'
        assume "al \<in> A l" and "al' \<in> A l" and "f l al = f l al'"
        from \<open>?\<AA> \<noteq> {}\<close> and this(1) and \<open>l \<in> \<Lambda>\<close> obtain a where "a \<in> ?\<AA>" and "a l = al"
          using Pi_one_point by metis
        let ?a' = "\<lambda>l'. if l' = l then al' else a l'"
        {
          fix l'
          assume "l' \<in> \<Lambda>"
          {
            assume "l' = l"
            with \<open>al' \<in> A l\<close> have "?a' l' \<in> A l'" by simp
          }
          moreover {
            assume "l' \<noteq> l"
            with \<open>a \<in> ?\<AA>\<close> and \<open>l' \<in> \<Lambda>\<close> have "?a' l' \<in> A l'" by auto
          }
          ultimately have "?a' l' \<in> A l'" by blast
        }
        hence "?a' \<in> ?\<AA>" by simp
        {
          fix l'
          {
            assume "l' \<in> \<Lambda>"
            with \<open>a l = al\<close> and \<open>f l al = f l al'\<close> and * have "F a l' = F ?a' l'" by simp
          }
          moreover {
            assume "l' \<notin> \<Lambda>"
            hence "F a l' = F ?a' l'" unfolding F by simp
          }
          ultimately have "F a l' = F ?a' l'" by auto
        }
        hence "F a = F ?a'" by auto
        with \<open>a \<in> ?\<AA>\<close> and \<open>?a' \<in> ?\<AA>\<close> and \<open>?L1\<close> have "ext_eq_on \<Lambda> a ?a'" by blast
        with \<open>l \<in> \<Lambda>\<close> have "a l = ?a' l" by auto
        with \<open>a l = al\<close> have "al = al'" by simp
      }
      hence "inj_on (f l) (A l)" by (fact inj_onI)
    }
    thus "?R1" by simp
  next
    assume "?R1"
    {
      fix a and a'
      assume "a \<in> ?\<AA>" and "a' \<in> ?\<AA>" and "F a = F a'"
      {
        fix l
        assume "l \<in> \<Lambda>"
        from \<open>F a = F a'\<close> have "F a l = F a' l" by simp
        with \<open>l \<in> \<Lambda>\<close> have "f l (a l) = f l (a' l)" by (simp only: *)
        moreover from \<open>a \<in> ?\<AA>\<close> and \<open>l \<in> \<Lambda>\<close> have "a l \<in> A l" by auto
        moreover from \<open>a' \<in> ?\<AA>\<close> and \<open>l \<in> \<Lambda>\<close> have "a' l \<in> A l" by auto
        moreover from \<open>l \<in> \<Lambda>\<close> and \<open>?R1\<close> have "inj_on (f l) (A l)" by simp
        ultimately have "a l = a' l" using \<open>?R1\<close> by (elim inj_onD)
      }
      hence "ext_eq_on \<Lambda> a a'" by auto
    }
    thus "?L1" by blast
  qed
  ultimately show "thesis" by (fact that)
qed

proposition prob_1_5_11_a:
  assumes "f ` A = B"
    and "right_inv_into A f s"
    and "right_inv_into A f s'"
    and "s ` B \<subseteq> s' ` B"
  shows "ext_eq_on B s s'"
proof (rule ext_eq_onI)
  fix b
  assume "b \<in> B"
  with assms(4) have "s b \<in> s' ` B" by auto
  then obtain b' where "b' \<in> B" and "s' b' = s b" by auto
  from this(2) have "f (s' b') = f (s b)" by simp
  moreover from assms(1) and \<open>b \<in> B\<close> and \<open>b' \<in> B\<close> have "b \<in> f ` A" and "b' \<in> f ` A" by simp+
  moreover note assms(2,3)
  ultimately have "b' = b" by (fastforce dest: right_inv_intoD2)
  with \<open>s' b' = s b\<close> show "s b = s' b" by simp
qed

proposition prob_1_5_11:
  assumes "f ` A = B"
    and "right_inv_into A f s"
    and "right_inv_into A f s'"
    and "s ` B \<subseteq> s' ` B \<or> s' ` B \<subseteq> s ` B"
  shows "ext_eq_on B s s'"
proof -
  {
    assume "s ` B \<subseteq> s' ` B"
    with assms(1-3) have ?thesis by (elim prob_1_5_11_a)
  }
  moreover {
    assume "s' ` B \<subseteq> s ` B"
    with assms(1-3) have "ext_eq_on B s' s" by (elim prob_1_5_11_a)
    hence ?thesis by (fact ext_eq_on_sym)
  }
  moreover note assms(4)
  ultimately show ?thesis by auto
qed

proposition prob_1_5_12_a:
  assumes "f ` A = B"
    \<comment> \<open>The assumption @{prop "f' ` B = C"} is not necessary.\<close>
    and "right_inv_into A f s"
    and "right_inv_into B f' s'"
  shows "right_inv_into A (f' \<circ> f) (s \<circ> s')"
proof (rule right_inv_intoI)
  fix c
  assume "c \<in> (f' \<circ> f) ` A"
  with assms(1) have "c \<in> f' ` B" by auto
  moreover from assms(3) have "s' ` f' ` B \<subseteq> B" by (elim right_inv_intoD1)
  ultimately have "s' c \<in> B" by auto
  with assms(1) have "s' c \<in> f ` A" by simp
  moreover from assms(2) have "s ` f ` A \<subseteq> A" by (elim right_inv_intoD1)
  ultimately have "s (s' c) \<in> A" by auto
  thus "(s \<circ> s') c \<in> A" by simp
  from \<open>s' c \<in> B\<close> and assms(1) have "s' c \<in> f ` A" by simp
  with assms(2) have "f (s (s' c)) = s' c" by (elim right_inv_intoD2)
  moreover from \<open>c \<in> f' ` B\<close> and assms(3) have "f' (s' c) = c" by (elim right_inv_intoD2)
  ultimately show "(f' \<circ> f) ((s \<circ> s') c) = c" by simp
qed

proposition prob_1_5_12_b:
  assumes "f ` A \<subseteq> B"
    and "f' ` B \<subseteq> C"
    and "inj_on f A"
    and "inj_on f' B"
    and "left_inv_into A f r"
    and "left_inv_into B f' r'"
  shows "left_inv_into A (f' \<circ> f) (r \<circ> r')"
proof (rule left_inv_intoI)
  fix a
  assume "a \<in> A"
  with assms(1) have "f a \<in> B" by auto
  with assms(6) have "r' (f' (f a)) = f a" by (auto dest: left_inv_intoD2)
  hence "r (r' (f' (f a))) = r (f a)" by simp
  with \<open>a \<in> A\<close> and assms(5) have "r (r' (f' (f a))) = a" by (auto dest: left_inv_intoD2)
  thus "(r \<circ> r') ((f' \<circ> f) a) = a" by simp
qed

proposition prob_1_5_13_a:
  assumes \<comment> \<open>The assumption @{prop "g ` B \<subseteq> C"} is not necessary.\<close>
    \<comment> \<open>The assumption @{prop "h ` A \<subseteq> C"} is not necessary.\<close>
    "f ` A \<subseteq> B"
    and "ext_eq_on A h (g \<circ> f)"
  shows "h ` A \<subseteq> g ` B"
proof (rule subsetI)
  fix c
  assume "c \<in> h ` A"
  then obtain a where "a \<in> A" and "c = h a" by auto
  from \<open>a \<in> A\<close> and assms(1) have "f a \<in> B" by auto
  moreover from \<open>a \<in> A\<close> and assms(2) and \<open>c = h a\<close> have "g (f a) = c" by auto
  ultimately show "c \<in> g ` B" by auto
qed

proposition prob_1_5_13_b:
  assumes \<comment> \<open>The assumption @{prop "g ` B \<subseteq> C"} is not necessary.\<close>
    \<comment> \<open>The assumption @{prop "h ` A \<subseteq> C"} is not necessary.\<close>
    "h ` A \<subseteq> g ` B"
  obtains f where "f ` A \<subseteq> B"
    and "ext_eq_on A h (g \<circ> f)"
proof -
  obtain s where *: "right_inv_into B g s" by (elim right_inv_into)
  hence "id_on (g \<circ> s) (g ` B)" by (elim right_inv_intoD2_pf)
  let ?f = "\<lambda>a. s (h a)"
  have "?f ` A \<subseteq> B"
  proof (rule image_subsetI)
    fix a
    assume "a \<in> A"
    with assms have "h a \<in> g ` B" by auto
    moreover from * have "s ` g ` B \<subseteq> B" by (elim right_inv_intoD1)
    ultimately show "?f a \<in> B" by auto
  qed
  moreover have "ext_eq_on A h (g \<circ> ?f)"
  proof (rule ext_eq_onI)
    fix a
    assume "a \<in> A"
    with assms have "h a \<in> g ` B" by auto
    with * have "g (s (h a)) = h a" by (elim right_inv_intoD2)
    thus "h a = (g \<circ> ?f) a" by simp
  qed
  ultimately show "thesis" by (rule that)
qed

proposition prob_1_5_13:
  \<comment> \<open>The assumption @{prop "g ` B \<subseteq> C"} is not necessary.\<close>
  \<comment> \<open>The assumption @{prop "h ` A \<subseteq> C"} is not necessary.\<close>
  shows "(\<exists>f. f ` A \<subseteq> B \<and> ext_eq_on A h (g \<circ> f)) \<longleftrightarrow> h ` A \<subseteq> g ` B"
  using prob_1_5_13_a prob_1_5_13_b by metis

proposition prob_1_5_14_a:
  assumes \<comment> \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    \<comment> \<open>The assumption @{prop "h ` A \<subseteq> C"} is not necessary.\<close>
    \<comment> \<open>The assumption @{prop "g ` B \<subseteq> C"} is not necessary.\<close>
    "ext_eq_on A h (g \<circ> f)"
    and "a \<in> A"
    and "a' \<in> A"
    and "f a = f a'"
  shows "h a = h a'"
proof -
  from assms(4) have "g (f a) = g (f a')" by simp
  with assms(1-3) show "h a = h a'" using ext_eq_onD by fastforce
qed

lemma the_singleton_equality:
  assumes "a \<in> A"
    and "\<And>x. x \<in> A \<Longrightarrow> x = a"
  shows "(THE a. A = {a}) = a"
  using assms by blast

proposition prob_1_5_14_b:
  fixes A :: "'a set"
    and B :: "'b set"
    and C :: "'c set"
  assumes "A = {} \<Longrightarrow> B = {}" \<comment> \<open>This assumption is not specified in the book. However, there
                                  exists a counterexample without it.\<close>
    \<comment> \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    and "h ` A \<subseteq> C"
    and "\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> f a = f a' \<Longrightarrow> h a = h a'"
  obtains g where "g ` B \<subseteq> C" and "ext_eq_on A h (g \<circ> f)"
proof -
  {
    assume "A \<noteq> {}"
    then obtain a where "a \<in> A" by auto
    let ?g = "\<lambda>b. if b \<in> f ` A then (THE c. h ` (f -` {b} \<inter> A) = {c}) else h a"
    have *: "?g (f a) = h a" if "a \<in> A" for a
    proof -
      from that have "f a \<in> f ` A" by simp
      hence "?g (f a) = (THE c. h ` (f -` {f a} \<inter> A) = {c})" by simp
      also have "\<dots> = h a"
      proof (rule the_singleton_equality)
        have "a \<in> f -` {f a}" by simp
        with that have "a \<in> f -` {f a} \<inter> A" by simp
        thus "h a \<in> h ` (f -` {f a} \<inter> A)" by simp
        fix x
        assume "x \<in> h ` (f -` {f a} \<inter> A)"
        then obtain a' where "a' \<in> f -` {f a} \<inter> A" and "x = h a'" by auto
        from \<open>a' \<in> f -` {f a} \<inter> A\<close> have "f a' = f a" by simp
        moreover note \<open>a \<in> A\<close>
        moreover from \<open>a' \<in> f -` {f a} \<inter> A\<close> have "a' \<in> A" by simp
        moreover note assms(3)
        ultimately have "h a' = h a" by blast
        with \<open>x = h a'\<close> show "x = h a" by simp
      qed
      finally show ?thesis .
    qed
    have "?g ` B \<subseteq> C"
    proof (rule image_subsetI)
      fix b
      assume "b \<in> B"
      {
        assume "b \<in> f ` A"
        then obtain a where "a \<in> A" and "b = f a" by auto
        from \<open>a \<in> A\<close> and * have "?g (f a) = h a" by simp
        with \<open>b = f a\<close> have "?g b = h a" by blast
        moreover from \<open>a \<in> A\<close> and assms(2) have "h a \<in> C" by auto
        ultimately have "?g b \<in> C" by simp
      }
      moreover {
        assume "b \<notin> f ` A"
        hence "?g b = h a" by simp
        also from \<open>a \<in> A\<close> and assms(2) have "h a \<in> C" by auto
        finally have "?g b \<in> C" .
      }
      ultimately show "?g b \<in> C" by blast
    qed
    moreover have "ext_eq_on A h (?g \<circ> f)"
    proof (rule ext_eq_onI)
      fix a'
      assume "a' \<in> A"
      hence "?g (f a') = h a'" by (intro *)
      thus "h a' = (?g \<circ> f) a'" by simp
    qed
    ultimately have "thesis" using that by blast
  }
  moreover {
    let ?g = "\<lambda>b. undefined :: 'c"
    assume "A = {}"
    with assms(1) have "B = {}" .
    hence "?g ` B \<subseteq> C" by simp
    moreover from \<open>A = {}\<close> have "ext_eq_on A h (?g \<circ> f)" by simp
    ultimately have "thesis" by (fact that)
  }
  ultimately show "thesis" by auto
qed

proposition prob_1_5_14:
  assumes "A = {} \<Longrightarrow> B = {}" \<comment> \<open>This assumption is not specified in the book. However, there
                                  exists a counterexample without it.\<close>
    \<comment> \<open>The assumption @{prop "f ` A \<subseteq> B"} is not necessary.\<close>
    and "h ` A \<subseteq> C"
  shows "(\<exists>g. g ` B \<subseteq> C \<and> ext_eq_on A h (g \<circ> f)) \<longleftrightarrow> (\<forall>a \<in> A. \<forall>a' \<in> A. f a = f a' \<longrightarrow> h a = h a')"
proof (rule iffI)
  assume "\<exists>g. g ` B \<subseteq> C \<and> ext_eq_on A h (g \<circ> f)"
  then obtain g where "g ` B \<subseteq> C" and *: "ext_eq_on A h (g \<circ> f)" by auto
  {
    fix a and a'
    assume "a \<in> A" and "a' \<in> A" and "f a = f a'"
    with * have "h a = h a'" by (rule prob_1_5_14_a)
  }
  thus "\<forall>a \<in> A. \<forall>a' \<in> A. f a = f a' \<longrightarrow> h a = h a'" by blast
next
  assume *: "\<forall>a \<in> A. \<forall>a' \<in> A. f a = f a' \<longrightarrow> h a = h a'"
  {
    fix a and a'
    assume "a \<in> A" and "a' \<in> A" and "f a = f a'"
    with * have "h a = h a'" by blast
  }
  with assms obtain g where "g ` B \<subseteq> C" and "ext_eq_on A h (g \<circ> f)" by (elim prob_1_5_14_b)
  thus "\<exists>g. g ` B \<subseteq> C \<and> ext_eq_on A h (g \<circ> f)" by auto
qed

proposition prob_1_5_15:
  assumes "A' = {} \<Longrightarrow> A = {}" \<comment> \<open>This assumption is not specified in the book. However, there
                                   exists a counterexample without it.\<close>
    and "u ` A' \<subseteq> A"
    and "v ` B \<subseteq> B'"
  defines Phi: "\<Phi> f \<equiv> v \<circ> f \<circ> u"
  obtains "u ` A' = A \<longrightarrow> inj_on v B
             \<longrightarrow> (\<forall>f \<in> A \<rightarrow> B. \<forall>f' \<in> A \<rightarrow> B. ext_eq_on A' (\<Phi> f) (\<Phi> f') \<longrightarrow> ext_eq_on A f f')"
    and "inj_on u A' \<longrightarrow> v ` B = B' \<longrightarrow> (\<forall>f' \<in> A' \<rightarrow> B'. \<exists>f \<in> A \<rightarrow> B. ext_eq_on A' (\<Phi> f) f')"
proof -
  have "u ` A' = A \<longrightarrow> inj_on v B
          \<longrightarrow> (\<forall>f \<in> A \<rightarrow> B. \<forall>f' \<in> A \<rightarrow> B. ext_eq_on A' (\<Phi> f) (\<Phi> f') \<longrightarrow> ext_eq_on A f f')"
  proof (intro impI)
    assume "u ` A' = A" and "inj_on v B"
    {
      fix f and f'
      assume "f \<in> A \<rightarrow> B" and "f' \<in> A \<rightarrow> B" and "ext_eq_on A' (\<Phi> f) (\<Phi> f')"
      obtain u' where "right_inv_into A' u u'" by (fact right_inv_into)
      hence "id_on (u \<circ> u') (u ` A')" by (fact right_inv_intoD2_pf)
      with \<open>u ` A' = A\<close> have "id_on (u \<circ> u') A" by simp
      from \<open>inj_on v B\<close> obtain v' where "left_inv_into B v v'" by (elim left_inv_into)
      hence *: "id_on (v' \<circ> v) B" by (fact left_inv_intoD2_pf)
      from \<open>id_on (u \<circ> u') A\<close> have "ext_eq_on A (f \<circ> (u \<circ> u')) f" by (fact thm_1_6_2_a)
      hence "ext_eq_on A (f \<circ> u \<circ> u') f" by (simp only: comp_assoc)
      moreover have "(f \<circ> u \<circ> u') ` A \<subseteq> B"
      proof -
        from \<open>id_on (u \<circ> u') A\<close> have "(u \<circ> u') ` A = A" by (fact id_on_imp_surj_on)
        with \<open>f \<in> A \<rightarrow> B\<close> show ?thesis by fastforce
      qed
      moreover note *
      ultimately have "ext_eq_on A ((v' \<circ> v) \<circ> f \<circ> u \<circ> u') f" by fastforce
      hence "ext_eq_on A (v' \<circ> (\<Phi> f) \<circ> u') f" unfolding Phi by (simp only: comp_assoc)
      {
        fix a
        assume "a \<in> A"
        moreover from \<open>u ` A' = A\<close> and \<open>right_inv_into A' u u'\<close> have "u' ` A \<subseteq> A'"
          by (auto dest: right_inv_intoD1)
        ultimately have "u' a \<in> A'" by auto
        with \<open>ext_eq_on A' (\<Phi> f) (\<Phi> f')\<close> have "(\<Phi> f') (u' a) = (\<Phi> f) (u' a)" by auto
        hence "v' ((\<Phi> f') (u' a)) = v' ((\<Phi> f) (u' a))" by simp
        also have "\<dots> = v' (v (f (u (u' a))))" by (simp add: Phi)
        also from \<open>u ` A' = A\<close> and \<open>right_inv_into A' u u'\<close> and \<open>a \<in> A\<close> have "\<dots> = v' (v (f a))"
          by (simp only: right_inv_intoD2)
        also have "\<dots> = f a"
        proof -
          from \<open>f \<in> A \<rightarrow> B\<close> and \<open>a \<in> A\<close> have "f a \<in> B" by auto
          with \<open>left_inv_into B v v'\<close> show ?thesis by (fact left_inv_intoD2)
        qed
        finally have "v' ((\<Phi> f') (u' a)) = f a" .
      }
      hence "ext_eq_on A (v' \<circ> (\<Phi> f') \<circ> u') f" by auto
      hence "ext_eq_on A ((v' \<circ> v) \<circ> f' \<circ> u \<circ> u') f" unfolding Phi by (simp only: comp_assoc)
      moreover have "(f' \<circ> u \<circ> u') ` A \<subseteq> B"
      proof -
        from \<open>id_on (u \<circ> u') A\<close> have "(u \<circ> u') ` A = A" by (fact id_on_imp_surj_on)
        with \<open>f' \<in> A \<rightarrow> B\<close> show ?thesis by fastforce
      qed
      moreover note *
      ultimately have "ext_eq_on A (f' \<circ> u \<circ> u') f" by fastforce
      with \<open>id_on (u \<circ> u') A\<close> have "ext_eq_on A f' f" by fastforce
      hence "ext_eq_on A f f'" by (fact ext_eq_on_sym)
    }
    thus "\<forall>f \<in> A \<rightarrow> B. \<forall>f' \<in> A \<rightarrow> B. ext_eq_on A' (\<Phi> f) (\<Phi> f') \<longrightarrow> ext_eq_on A f f'" by simp
  qed
  moreover have "inj_on u A' \<longrightarrow> v ` B = B'
                   \<longrightarrow> (\<forall>f' \<in> A' \<rightarrow> B'. \<exists>f \<in> A \<rightarrow> B. ext_eq_on A' (\<Phi> f) f')"
  proof (intro impI)
    assume "inj_on u A'" and "v ` B = B'"
    {
      fix f'
      assume "f' \<in> A' \<rightarrow> B'"
      from \<open>inj_on u A'\<close> and assms(1) obtain u'
        where "u' ` A \<subseteq> A'" and "id_on (u' \<circ> u) A'" by (elim thm_1_7_b_a)
      obtain v' where "right_inv_into B v v'" by (fact right_inv_into)
      hence "v' ` v ` B \<subseteq> B" and "id_on (v \<circ> v') (v ` B)"
        by (fact right_inv_intoD1, fact right_inv_intoD2_pf)
      with \<open>v ` B = B'\<close> have "v' ` B' \<subseteq> B" and "id_on (v \<circ> v') B'" by simp+
      let ?f = "v' \<circ> f' \<circ> u'"
      from \<open>u' ` A \<subseteq> A'\<close> and \<open>f' \<in> A' \<rightarrow> B'\<close> and \<open>v' ` B' \<subseteq> B\<close> have "?f ` A \<subseteq> B" by fastforce
      moreover have "ext_eq_on A' (\<Phi> ?f) f'"
      proof -
        have "ext_eq_on A' (\<Phi> ?f) (v \<circ> v' \<circ> f' \<circ> u' \<circ> u)" unfolding Phi by auto
        also have "ext_eq_on A' \<dots> (f' \<circ> u' \<circ> u)"
        proof -
          from \<open>id_on (u' \<circ> u) A'\<close> and \<open>f' \<in> A' \<rightarrow> B'\<close> have "(f' \<circ> u' \<circ> u) ` A' \<subseteq> B'" by fastforce
          with \<open>id_on (v \<circ> v') B'\<close> show ?thesis by fastforce
        qed
        also from \<open>id_on (u' \<circ> u) A'\<close> have "ext_eq_on A' \<dots> f'" by fastforce
        finally show "ext_eq_on A' (\<Phi> ?f) f'" .
      qed
      ultimately have "\<exists>f \<in> A \<rightarrow> B. ext_eq_on A' (\<Phi> f) f'" by blast
    }
    thus "\<forall>f' \<in> A' \<rightarrow> B'. \<exists>f \<in> A \<rightarrow> B. ext_eq_on A' (\<Phi> f) f'" ..
  qed
  ultimately show "thesis" by (fact that)
qed

proposition prob_1_5_15_ext_a:
  assumes "u ` A' = A"
    and "inj_on v B"
  defines "\<Phi> f \<equiv> \<lambda>a'. if a' \<in> A' then v (f (u a')) else undefined"
  shows "inj_on \<Phi> (A \<rightarrow>\<^sub>E B)"
proof (rule inj_onI)
  fix f f'
  assume f: "f \<in> A \<rightarrow>\<^sub>E B"
    and f': "f' \<in> A \<rightarrow>\<^sub>E B"
    and "\<Phi> f = \<Phi> f'"
  {
    fix a
    consider "a \<in> A" | "a \<notin> A" by auto
    moreover {
      assume a: "a \<in> A"
      with assms(1) obtain a' where "a' \<in> A'" and "u a' = a" by auto
      with \<open>\<Phi> f = \<Phi> f'\<close> and \<Phi>_def have "v (f a) = v (f' a)" by metis
      moreover from f and a have "f a \<in> B" by auto
      moreover from f' and a have "f' a \<in> B" by auto
      moreover note assms(2)
      ultimately have "f a = f' a" by (simp only: inj_onD)
    }
    moreover {
      assume "a \<notin> A"
      with f and f' have "f a = f' a" by fastforce
    }
    ultimately have "f a = f' a" by auto
  }
  thus "f = f'" by auto
qed

proposition prob_1_5_15_ext_b:
  fixes A :: "'a set"
    and B :: "'b set"
  assumes "A' = {} \<Longrightarrow> A = {}"
    and "u ` A' \<subseteq> A"
    and "inj_on u A'"
    and "v ` B = B'"
  defines "\<Phi> f \<equiv> \<lambda>a'. if a' \<in> A' then v (f (u a')) else undefined"
  shows "\<Phi> ` (A \<rightarrow>\<^sub>E B) = (A' \<rightarrow>\<^sub>E B')"
proof (rule surj_onI)
  fix f
  assume f: "f \<in> A \<rightarrow>\<^sub>E B"
  {
    fix a'
    assume a': "a' \<in> A'"
    with \<Phi>_def have "\<Phi> f a' = v (f (u a'))" by simp
    also from a' and assms(2) and f and assms(4) have "\<dots> \<in> B'" by auto
    finally have "\<Phi> f a' \<in> B'" .
  }
  moreover {
    fix a'
    assume "a' \<notin> A'"
    with \<Phi>_def have "\<Phi> f a' = undefined" by simp
  }
  ultimately show "\<Phi> f \<in> A' \<rightarrow>\<^sub>E B'" by auto
next
  fix g
  assume g: "g \<in> A' \<rightarrow>\<^sub>E B'"
  consider "A' = {}" | "A' \<noteq> {}" by auto
  moreover {
    assume "A' = {}"
    with assms(1) have "A = {}" by simp
    moreover define f :: "'a \<Rightarrow> 'b" where "f a \<equiv> undefined" for a
    ultimately have "f \<in> A \<rightarrow>\<^sub>E B" by auto
    moreover have "\<Phi> f = g"
    proof (rule ext)
      fix a'
      from \<Phi>_def and \<open>A' = {}\<close> and g show "\<Phi> f a' = g a'" by simp
    qed
    ultimately have "\<exists>f \<in> A \<rightarrow>\<^sub>E B. \<Phi> f = g" by auto
  }
  moreover {
    assume "A' \<noteq> {}"
    with g and assms(4) have "B \<noteq> {}" by auto
    then obtain b where b: "b \<in> B" by auto
    from assms(3) obtain u' where "left_inv_into A' u u'" by (rule left_inv_into)
    hence u'1: "u' ` u ` A' \<subseteq> A'" and u'2: "id_on (u' \<circ> u) A'"
      by (fact left_inv_intoD1, fact left_inv_intoD2_pf)
    obtain v' where "right_inv_into B v v'" by (fact right_inv_into)
    hence "v' ` v ` B \<subseteq> B" and "id_on (v \<circ> v') (v ` B)"
      by (fact right_inv_intoD1, fact right_inv_intoD2_pf)
    with assms(4) have v'1: "v' ` B' \<subseteq> B" and v'2: "id_on (v \<circ> v') B'" by simp+
    define f where "f a \<equiv> if a \<in> u ` A' then v' (g (u' a)) else (if a \<in> A then b else undefined)" for a
    {
      fix a
      assume "a \<in> A"
      consider "a \<in> u ` A'" | "a \<notin> u ` A'" by auto
      moreover {
        assume "a \<in> u ` A'"
        with f_def have "f a = v' (g (u' a))" by simp
        also from \<open>a \<in> u ` A'\<close> and u'1 and g and v'1 have "\<dots> \<in> B" by auto
        finally have "f a \<in> B" by simp
      }
      moreover {
        assume "a \<notin> u ` A'"
        with \<open>a \<in> A\<close> and f_def and b have "f a \<in> B" by simp
      }
      ultimately have "f a \<in> B" by auto
    }
    moreover {
      fix a
      assume "a \<notin> A"
      moreover from this and assms(2) have "a \<notin> u ` A'" by auto
      moreover note f_def
      ultimately have "f a = undefined" by simp
    }
    ultimately have "f \<in> A \<rightarrow>\<^sub>E B" by auto
    moreover have "\<Phi> f = g"
    proof (rule ext)
      fix a'
      consider "a' \<in> A'" | "a' \<notin> A'" by auto
      moreover {
        assume a': "a' \<in> A'"
        with \<Phi>_def have "\<Phi> f a' = v (f (u a'))" by simp
        also from a' and f_def have "\<dots> = (v \<circ> v') (g ((u' \<circ> u) a'))" by auto
        also from a' and u'2 and g and v'2 have "\<dots> = g a'" by fastforce
        finally have "\<Phi> f a' = g a'" .
      }
      moreover {
        assume a': "a' \<notin> A'"
        with \<Phi>_def and g have "\<Phi> f a' = g a'" by auto
      }
      ultimately show "\<Phi> f a' = g a'" by auto
    qed
    ultimately have "\<exists>f \<in> A \<rightarrow>\<^sub>E B. \<Phi> f = g" by auto
  }
  ultimately show "g \<in> \<Phi> ` (A \<rightarrow>\<^sub>E B)" by auto
qed

end
