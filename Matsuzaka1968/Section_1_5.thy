theory Section_1_5
  imports Main
    "HOL-Library.FuncSet"
    "Section_1_4"
begin

section "Indexed Families, General Products"

proposition prop_1_5_1:
  shows "(\<Union>l \<in> \<Lambda>. A l) \<inter> B = (\<Union>l \<in> \<Lambda>. (A l \<inter> B))"
proof (rule set_eqI)
  fix x
  have "x \<in> (\<Union>l \<in> \<Lambda>. A l) \<inter> B \<longleftrightarrow> x \<in> (\<Union>l \<in> \<Lambda>. A l) \<and> x \<in> B" by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>l \<in> \<Lambda>. x \<in> A l) \<and> x \<in> B" by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>l \<in> \<Lambda>. x \<in> A l \<and> x \<in> B)" by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>l \<in> \<Lambda>. x \<in> A l \<inter> B)" by simp
  also have "\<dots> \<longleftrightarrow> x \<in> (\<Union>l \<in> \<Lambda>. A l \<inter> B)" by simp
  finally show "x \<in> (\<Union>l \<in> \<Lambda>. A l) \<inter> B \<longleftrightarrow> x \<in> (\<Union>l \<in> \<Lambda>. (A l \<inter> B))" .
qed

proposition prop_1_5_1':
  shows "(\<Inter>l \<in> \<Lambda>. A l) \<union> B = (\<Inter>l \<in> \<Lambda>. A l \<union> B)"
proof (rule set_eqI)
  fix x
  have "x \<in> (\<Inter>l \<in> \<Lambda>. A l) \<union> B \<longleftrightarrow> x \<in> (\<Inter>l \<in> \<Lambda>. A l) \<or> x \<in> B" by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. x \<in> A l) \<or> x \<in> B" by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. x \<in> A l \<or> x \<in> B)" by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. x \<in> A l \<union> B)" by simp
  also have "\<dots> \<longleftrightarrow> x \<in> (\<Inter>l \<in> \<Lambda>. A l \<union> B)" by simp
  finally show "x \<in> (\<Inter>l \<in> \<Lambda>. A l) \<union> B \<longleftrightarrow> x \<in> (\<Inter>l \<in> \<Lambda>. A l \<union> B)" .
qed

proposition prop_1_5_2:
  assumes "\<Lambda> \<noteq> {}" (*and*)
    -- {* @{prop "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<subseteq> X"}: an unnecessary condition. *}
  shows "X - (\<Union>l \<in> \<Lambda>. A l) = (\<Inter>l \<in> \<Lambda>. (X - A l))"
proof (rule set_eqI2)
  fix x
  assume "x \<in> X - (\<Union>l \<in> \<Lambda>. A l)"
  hence "x \<in> X" and "x \<notin> (\<Union>l \<in> \<Lambda>. A l)" by auto
  from this(2) have "\<not>(\<exists>l \<in> \<Lambda>. x \<in> A l)" by simp
  hence "\<forall>l \<in> \<Lambda>. x \<notin> A l" by simp
  with \<open>x \<in> X\<close> have "\<forall>l \<in> \<Lambda>. x \<in> X \<and> x \<notin> A l" by simp
  hence "\<forall>l \<in> \<Lambda>. x \<in> X - A l" by simp
  thus "x \<in> (\<Inter>l \<in> \<Lambda>. X - A l)" by auto
next
  fix x
  assume "x \<in> (\<Inter>l \<in> \<Lambda>. X - A l)"
  hence "\<forall>l \<in> \<Lambda>. x \<in> X - A l" by blast
  hence "\<forall>l \<in> \<Lambda>. x \<in> X \<and> x \<notin> A l" by auto
  hence "\<forall>l \<in> \<Lambda>. x \<notin> A l" by auto
  hence "\<not>(\<exists>l \<in> \<Lambda>. x \<in> A l)" by auto
  hence "x \<notin> (\<Union>l \<in> \<Lambda>. A l)" by auto
  moreover have "x \<in> X"
  proof -
    from assms(1) obtain l where "l \<in> \<Lambda>" by auto
    with \<open>\<forall>l \<in> \<Lambda>. x \<in> X \<and> x \<notin> A l\<close> have "x \<in> X \<and> x \<notin> A l" by auto
    thus "?thesis" ..
  qed
  ultimately show "x \<in> X - (\<Union>l \<in> \<Lambda>. A l)" by auto
qed

proposition prop_1_5_2':
    -- {* @{prop "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<subseteq> X"}: an unnecessary assumption. *}
  shows "X - (\<Inter>l \<in> \<Lambda>. A l) = (\<Union>l \<in> \<Lambda>. X - A l)"
proof (rule set_eqI)
  fix x
  have "x \<in> X - (\<Inter>l \<in> \<Lambda>. A l) \<longleftrightarrow> x \<in> X \<and> x \<notin> (\<Inter>l \<in> \<Lambda>. A l)" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> X \<and> \<not>(\<forall>l \<in> \<Lambda>. x \<in> A l)" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> X \<and> (\<exists>l \<in> \<Lambda>. x \<notin> A l)" by auto
  also have "\<dots> \<longleftrightarrow> (\<exists>l \<in> \<Lambda>. x \<in> X \<and> x \<notin> A l)" by auto
  also have "\<dots> \<longleftrightarrow> (\<exists>l \<in> \<Lambda>. x \<in> X - A l)" by auto
  also have "\<dots> \<longleftrightarrow> x \<in> (\<Union>l \<in> \<Lambda>. X - A l)" by auto
  finally show "x \<in> X - (\<Inter>l \<in> \<Lambda>. A l) \<longleftrightarrow> x \<in> (\<Union>l \<in> \<Lambda>. X - A l)" .
qed

proposition prop_1_5_3:
    -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    -- {* @{prop "\<And>l. l \<in> \<Lambda> \<Longrightarrow> P l \<subseteq> A"}: an unnecessary assumption. *}
  shows "f ` (\<Union>l \<in> \<Lambda>. P l) = (\<Union>l \<in> \<Lambda>. f ` (P l))"
proof (rule equalityI)
  {
    fix b
    assume "b \<in> f ` (\<Union>l \<in> \<Lambda>. P l)"
    then obtain a where "a \<in> (\<Union>l \<in> \<Lambda>. P l)" and "b = f a" by auto
    from this(1) have "\<exists>l \<in> \<Lambda>. a \<in> P l" by auto
    then obtain l where "l \<in> \<Lambda>" and "a \<in> P l" by auto
    from this(2) \<open>b = f a\<close> have "b \<in> f ` P l" by auto
    with \<open>l \<in> \<Lambda>\<close> have "b \<in> (\<Union>l \<in> \<Lambda>. f ` P l)" by auto
  }
  thus "f ` (\<Union>l \<in> \<Lambda>. P l) \<subseteq> (\<Union>l \<in> \<Lambda>. f ` (P l))" by (intro subsetI)
  {
    fix b
    assume "b \<in> (\<Union>l \<in> \<Lambda>. f ` (P l))"
    then obtain l where "l \<in> \<Lambda>" and "b \<in> f ` P l" by auto
    from this(2) obtain a where "a \<in> P l" and "b = f a" by auto
    from this(1) and \<open>l \<in> \<Lambda>\<close> have "a \<in> (\<Union>l \<in> \<Lambda>. P l)" by auto
    with \<open>b = f a\<close> have "b \<in> f ` (\<Union>l \<in> \<Lambda>. P l)" by auto
  }
  thus "(\<Union>l \<in> \<Lambda>. f ` (P l)) \<subseteq> f ` (\<Union>l \<in> \<Lambda>. P l)" by (intro subsetI)
qed

proposition prop_1_5_4:
    -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    -- {* @{prop "\<And>l. l \<in> \<Lambda> \<Longrightarrow> P l \<subseteq> A"}: an unnecessary assumption. *}
  shows "f ` (\<Inter>l \<in> \<Lambda>. P l) \<subseteq> (\<Inter>l \<in> \<Lambda>. f ` (P l))"
proof (rule subsetI)
  fix b
  assume "b \<in> f ` (\<Inter>l \<in> \<Lambda>. P l)"
  then obtain a where "a \<in> (\<Inter>l \<in> \<Lambda>. P l)" and "b = f a" by auto
  from this(1) have "\<forall>l \<in> \<Lambda>. a \<in> P l" by auto
  {
    fix l
    assume "l \<in> \<Lambda>"
    with \<open>\<forall>l \<in> \<Lambda>. a \<in> P l\<close> have "a \<in> P l" by auto
    with \<open>b = f a\<close> have "b \<in> f ` (P l)" by auto
  }
  thus "b \<in> (\<Inter>l \<in> \<Lambda>. f ` (P l))" by auto
qed

proposition prop_1_5_3':
    -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    -- {* @{prop "\<And>\<mu>. \<mu> \<in> M \<Longrightarrow> Q \<mu> \<subseteq> B"}: an unnecessary assumption. *}
  shows "(f -` (\<Union>\<mu> \<in> M. Q \<mu>)) \<inter> A = (\<Union>\<mu> \<in> M. (f -` (Q \<mu>)) \<inter> A)"
proof (rule set_eqI2)
  fix a
  assume "a \<in> (f -` (\<Union>\<mu> \<in> M. Q \<mu>)) \<inter> A"
  hence "f a \<in> (\<Union>\<mu> \<in> M. Q \<mu>)" and "a \<in> A" by auto
  then obtain \<mu> where "\<mu> \<in> M" and "f a \<in> Q \<mu>" by auto
  from this(2) and \<open>a \<in> A\<close> have "a \<in> (f -` Q \<mu>) \<inter> A" by auto
  with \<open>\<mu> \<in> M\<close> show "a \<in> (\<Union>\<mu> \<in> M. (f -` (Q \<mu>)) \<inter> A)" by auto
next
  fix a
  assume "a \<in> (\<Union>\<mu> \<in> M. (f -` (Q \<mu>)) \<inter> A)"
  then obtain \<mu> where "\<mu> \<in> M" and "f a \<in> Q \<mu>" and "a \<in> A" by blast
  from this(1,2) have "f a \<in> (\<Union>\<mu> \<in> M. Q \<mu>)" by auto
  with \<open>a \<in> A\<close> show "a \<in> (f -` (\<Union>\<mu> \<in> M. Q \<mu>)) \<inter> A" by auto
qed

proposition prop_1_5_4':
  assumes "M \<noteq> {}"
    -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    -- {* @{prop "\<And>\<mu>. \<mu> \<in> M \<Longrightarrow> Q \<mu> \<subseteq> B"}: an unnecessary assumption. *}
  shows "(f -` (\<Inter>\<mu> \<in> M. Q \<mu>)) \<inter> A = (\<Inter>\<mu> \<in> M. (f -` (Q \<mu>)) \<inter> A)"
proof (rule set_eqI2)
  fix a
  assume "a \<in> (f -` (\<Inter>\<mu> \<in> M. Q \<mu>)) \<inter> A"
  hence *: "f a \<in> (\<Inter>\<mu> \<in> M. Q \<mu>)" and "a \<in> A" by auto
  {
    fix \<mu>
    assume "\<mu> \<in> M"
    with * have "f a \<in> Q \<mu>" by auto
    with \<open>a \<in> A\<close> have "a \<in> (f -` (Q \<mu>)) \<inter> A" by auto
  }
  thus "a \<in> (\<Inter>\<mu> \<in> M. (f -` (Q \<mu>)) \<inter> A)" by auto
next
  fix a
  assume "a \<in> (\<Inter>\<mu> \<in> M. (f -` (Q \<mu>)) \<inter> A)"
  hence *: "\<forall>\<mu> \<in> M. a \<in> (f -` (Q \<mu>)) \<inter> A" by blast
  with assms have "a \<in> A" by auto
  {
    fix \<mu>
    assume "\<mu> \<in> M"
    with * have "f a \<in> Q \<mu>" by blast
  }
  hence "f a \<in> (\<Inter>\<mu> \<in> M. Q \<mu>)" by auto
  with \<open>a \<in> A\<close> show "a \<in> (f -` (\<Inter>\<mu> \<in> M. Q \<mu>)) \<inter> A" by auto
qed

text {* @{const Pi\<^sub>E} comes from @{theory "FuncSet"}. *}

lemma extensional_iff:
  shows "f \<in> extensional A \<longleftrightarrow> (\<forall>x. x \<notin> A \<longrightarrow> f x = undefined)"
  by (simp add: extensional_def)

theorem AC:
  assumes "\<forall>l \<in> \<Lambda>. A l \<noteq> {}"
  shows "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<noteq> {}"
proof -
  let ?a = "\<lambda>l. if l \<in> \<Lambda> then (SOME b. b \<in> A l) else undefined"
  {
    fix l
    assume "l \<in> \<Lambda>"
    with assms have "A l \<noteq> {}" ..
    hence "\<exists>b. b \<in> A l" by auto
    hence "(SOME b. b \<in> A l) \<in> A l" by (fact someI_ex)
    with \<open>l \<in> \<Lambda>\<close> have "?a l \<in> A l" by simp
  }
  moreover {
    fix l
    assume "l \<notin> \<Lambda>"
    hence "?a l = undefined" by simp
  }
  ultimately have "?a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" by auto
  thus ?thesis by auto
qed

lemma AC_E:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<noteq> {}"
  obtains a where "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
proof -
  {
    fix l
    assume "l \<in> \<Lambda>"
    with assms have "A l \<noteq> {}" by simp
  }
  hence "\<forall>l \<in> \<Lambda>. A l \<noteq> {}" ..
  hence "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<noteq> {}" by (fact AC)
  then obtain a where "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" by auto
  thus "thesis" by (fact that)
qed

lemma PiE_eqI:
  assumes "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" and
    "a' \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" and
    "\<And>l. l \<in> \<Lambda> \<Longrightarrow> a l = a' l"
  shows "a = a'"
proof (rule ext)
  fix l
  {
    assume "l \<in> \<Lambda>"
    with assms(3) have "a l = a' l" by simp
  }
  moreover {
    assume "l \<notin> \<Lambda>"
    with assms(1,2) have "a l = undefined" and "a' l = undefined" by auto
    hence "a l = a' l" by simp
  }
  ultimately show "a l = a' l" by auto
qed

lemma PiE_eq_iff:
  assumes "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" and
    "a' \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
  shows "a = a' \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. a l = a' l)"
proof (rule iffI)
  assume "a = a'"
  thus "\<forall>l \<in> \<Lambda>. a l = a' l" by simp
next
  assume *: "\<forall>l \<in> \<Lambda>. a l = a' l"
  {
    fix l
    assume "l \<in> \<Lambda>"
    with * have "a l = a' l" ..
  }
  with assms show "a = a'" by (intro PiE_eqI)
qed

lemma PiE_D1_ball:
  assumes "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
  shows "\<forall>l \<in> \<Lambda>. a l \<in> A l"
proof -
  from assms have "a \<in> (\<Pi> l \<in> \<Lambda>. A l) \<inter> extensional \<Lambda>" by (simp only: PiE_def)
  hence "a \<in> (\<Pi> l \<in> \<Lambda>. A l)" ..
  thus "?thesis" by (simp add: Pi_def)
qed

lemma PiE_D1:
  assumes "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" and
    "l \<in> \<Lambda>"
  shows "a l \<in> A l"
proof -
  from assms(1) have "\<forall>l \<in> \<Lambda>. a l \<in> A l" by (elim PiE_D1_ball)
  with assms(2) show "?thesis" by simp
qed

(*lemma PiE_D1_forall:
  assumes "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
  shows "\<forall>l \<in> \<Lambda>. a l \<in> A l"
  oops*)

lemma PiE_D2:
  assumes "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" and
    "l \<notin> \<Lambda>"
  shows "a l = undefined"
proof -
  from assms(1) have "a \<in> (\<Pi> l \<in> \<Lambda>. A l) \<inter> extensional \<Lambda>" by (simp only: PiE_def)
  hence "a \<in> extensional \<Lambda>" ..
  with assms(2) show "?thesis" by (elim extensional_arb)
qed

lemma PiE_D2_ball:
  assumes "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
  shows "\<forall>l. l \<notin> \<Lambda> \<longrightarrow> a l = undefined"
proof (rule allI)
  fix l
  {
    assume "l \<notin> \<Lambda>"
    with assms have "a l = undefined" by (elim PiE_D2)
  }
  thus "l \<notin> \<Lambda> \<longrightarrow> a l = undefined" ..
qed

lemma mem_PiE_iff:
  shows "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. a l \<in> A l) \<and> (\<forall>l. l \<notin> \<Lambda> \<longrightarrow> a l = undefined)"
proof -
  have "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<longleftrightarrow> a \<in> (\<Pi> l \<in> \<Lambda>. A l) \<inter> extensional \<Lambda>" by (simp only: PiE_def)
  also have "\<dots> \<longleftrightarrow> a \<in> (\<Pi> l \<in> \<Lambda>. A l) \<and> a \<in> extensional \<Lambda>" by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. a l \<in> A l) \<and> a \<in> extensional \<Lambda>" using Pi_iff by blast
  also have "\<dots> \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. a l \<in> A l) \<and> (\<forall>l. l \<notin> \<Lambda> \<longrightarrow> a l = undefined)"
    using extensional_iff by fast
  finally show "?thesis" .
qed

lemma PiE_not_emptyE:
  assumes "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<noteq> {}"
  obtains a where "\<forall>l \<in> \<Lambda>. a l \<in> A l" and "\<forall>l. l \<notin> \<Lambda> \<longrightarrow> a l = undefined"
proof -
  from assms obtain a where *: "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" by auto
  {
    fix l
    assume "l \<in> \<Lambda>"
    with * have "a l \<in> A l" by (elim PiE_D1)
  }
  hence "\<forall>l \<in> \<Lambda>. a l \<in> A l" ..
  moreover from * have "\<forall>l. l \<notin> \<Lambda> \<longrightarrow> a l = undefined" by (elim PiE_D2_ball)
  ultimately show "thesis" by (intro that)
qed

lemma PiE_empty_domain_D:
  assumes "a \<in> (\<Pi>\<^sub>E l \<in> {}. A l)"
  shows "a l = undefined"
proof -
  from assms have "a \<in> {\<lambda>l. undefined}" by (simp only: PiE_empty_domain)
  thus "?thesis" by simp
qed

definition pie :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "pie \<Lambda> a = (\<lambda>l. if l \<in> \<Lambda> then a l else undefined)"

syntax
"_pie" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("(1'(_\<in>_./ _'))")

translations
"(l\<in>\<Lambda>. a)" \<rightleftharpoons> "CONST pie \<Lambda> (\<lambda>l. a)"

lemma pie_eq:
  assumes "l \<in> \<Lambda>"
  shows "(l \<in> \<Lambda>. a l) l = a l"
  using assms by (simp add: pie_def)

lemma pie_eq_undefined:
  assumes "l \<notin> \<Lambda>"
  shows "(l \<in> \<Lambda>. a l) l = undefined"
  using assms by (simp add: pie_def)

lemma pie_mem_PiE:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> a l \<in> A l"
  shows "(l \<in> \<Lambda>. a l) \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
proof (rule PiE_I)
  fix l
  assume "l \<in> \<Lambda>"
  hence "(l \<in> \<Lambda>. a l) l = a l" by (fact pie_eq)
  with \<open>l \<in> \<Lambda>\<close> and assms show "(l \<in> \<Lambda>. a l) l \<in> A l" by simp
next
  fix l
  assume "l \<notin> \<Lambda>"
  thus "(l \<in> \<Lambda>. a l) l = undefined" by (fact pie_eq_undefined)
qed

lemma pie_collapse:
  assumes "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
  shows "(l \<in> \<Lambda>. a l) = a"
proof (rule ext)
  fix l
  {
    assume "l \<in> \<Lambda>"
    with assms have "(l \<in> \<Lambda>. a l) l = a l" by (simp only: pie_eq)
  }
  moreover {
    assume "l \<notin> \<Lambda>"
    hence "(l \<in> \<Lambda>. a l) l = undefined" by (fact pie_eq_undefined)
    also from \<open>l \<notin> \<Lambda>\<close> and assms have "a l = undefined" by (elim PiE_D2)
    finally have "(l \<in> \<Lambda>. a l) l = a l" by simp
  }
  ultimately show "(l \<in> \<Lambda>. a l) l = a l" by auto
qed

lemma pie_ext:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> a l = b l"
  shows "(l \<in> \<Lambda>. a l) = (l \<in> \<Lambda>. b l)"
proof (rule ext)
  fix l
  {
    assume "l \<in> \<Lambda>"
    hence "(l \<in> \<Lambda>. a l) l = a l" by (fact pie_eq)
    also from \<open>l \<in> \<Lambda>\<close> and assms have "\<dots> = b l" by simp
    also from \<open>l \<in> \<Lambda>\<close> have "\<dots> = (l \<in> \<Lambda>. b l) l" by (simp only: pie_eq)
    finally have "(l \<in> \<Lambda>. a l) l = (l \<in> \<Lambda>. b l) l" .
  }
  moreover {
    assume "l \<notin> \<Lambda>"
    hence "(l \<in> \<Lambda>. a l) l = undefined" and "(l \<in> \<Lambda>. b l) l = undefined"
      by (simp_all add: pie_eq_undefined)
    hence "(l \<in> \<Lambda>. a l) l = (l \<in> \<Lambda>. b l) l" by simp
  }
  ultimately show "(l \<in> \<Lambda>. a l) l = (l \<in> \<Lambda>. b l) l" by auto
qed

lemma pie_eq_iff:
  shows "(l \<in> \<Lambda>. a l) = (l \<in> \<Lambda>. b l) \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. a l = b l)"
proof (rule iffI)
  assume *: "(l \<in> \<Lambda>. a l) = (l \<in> \<Lambda>. b l)"
  {
    fix l
    assume "l \<in> \<Lambda>"
    hence "a l = (l \<in> \<Lambda>. a l) l" by (simp only: pie_eq)
    also from * have "\<dots> = (l \<in> \<Lambda>. b l) l" by simp
    also from \<open>l \<in> \<Lambda>\<close> have "\<dots> = b l" by (simp only: pie_eq)
    finally have "a l = b l" .
  }
  thus "\<forall>l \<in> \<Lambda>. a l = b l" ..
next
  assume **: "\<forall>l \<in> \<Lambda>. a l = b l"
  {
    fix l
    assume "l \<in> \<Lambda>"
    with ** have "a l = b l" ..
  }
  thus "(l \<in> \<Lambda>. a l) = (l \<in> \<Lambda>. b l)" by (intro pie_ext)
qed

definition proj :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"
  where "proj l a = a l"

lemmas proj_eq = proj_def

lemma mem_PiE_imp_proj_mem:
  assumes "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" and
    "l \<in> \<Lambda>"
  shows "proj l a \<in> A l"
proof -
  from assms have "a l \<in> A l" by (elim PiE_D1)
  thus "?thesis" by (simp only: proj_eq)
qed

lemma proj_pie_eq:
  assumes "l \<in> \<Lambda>"
  shows "proj l (l \<in> \<Lambda>. a l) = a l"
  using assms by (simp add: proj_eq pie_eq)

theorem theorem_1_7_a':
  assumes "f ` A = B"
  obtains s where "s ` B \<subseteq> A" and
    "id_on (f \<circ> s) B"
proof -
  {
    fix b
    assume "b \<in> B"
    with assms(1) obtain a where "a \<in> A" and "b = f a" by auto
    hence "a \<in> f -` {b}" by auto
    with \<open>a \<in> A\<close> have "(f -` {b}) \<inter> A \<noteq> {}" by auto
  }
  then obtain s where *: "s \<in> (\<Pi>\<^sub>E b \<in> B. (f -` {b}) \<inter> A)" by (rule AC_E)
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

theorem theorem_1_7_a'':
  assumes "f ` A \<subseteq> B" and
    "s ` B \<subseteq> A" and
    "id_on (f \<circ> s) B"
  shows "f ` A = B"
proof -
  from assms(3) have "(f \<circ> s) ` B = B" by (fact id_on_imp_surj_on)
  with assms(1,2) show "?thesis" by (intro problem_1_4_10_a[where A = "B" and f = "s" and g = "f"])
qed

theorem theorem_1_7_a:
  assumes "f ` A \<subseteq> B"
  shows "f ` A = B \<longleftrightarrow> (\<exists>s. s ` B \<subseteq> A \<and> id_on (f \<circ> s) B)"
proof (rule iffI)
  assume "f ` A = B"
  then obtain s where "s ` B \<subseteq> A" and "id_on (f \<circ> s) B" by (rule theorem_1_7_a')
  thus "\<exists>s. s ` B \<subseteq> A \<and> id_on (f \<circ> s) B" by auto
next
  assume "\<exists>s. s ` B \<subseteq> A \<and> id_on (f \<circ> s) B"
  then obtain s where "s ` B \<subseteq> A" and "id_on (f \<circ> s) B" by auto
  with assms show "f ` A = B" by (rule theorem_1_7_a'')
qed

theorem theorem_1_7_b':
  -- {* @{prop "A \<noteq> {}"} is a necessary assumption, otherwise there exists a counterexample. *}
  assumes "A \<noteq> {}" and
    -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    "inj_on f A"
  obtains r where "r ` B \<subseteq> A" and
    "id_on (r \<circ> f) A"
proof -
  from assms(1) obtain a where "a \<in> A" by auto
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
  ultimately show "thesis" by (fact that)
qed

theorem theorem_1_7_b'':
  assumes "id_on (r \<circ> f) A"
  shows "inj_on f A"
proof (rule inj_onI)
  fix a a'
  assume "a \<in> A" and
    "a' \<in> A" and
    "f a = f a'"
  from assms and \<open>a \<in> A\<close> have "(r \<circ> f) a = a" by (elim id_onD)
  moreover from assms and \<open>a' \<in> A\<close> have "(r \<circ> f) a' = a'" by (elim id_onD)
  moreover from \<open>f a = f a'\<close> have "(r \<circ> f) a = (r \<circ> f) a'" by auto
  ultimately show "a = a'" by simp
qed

theorem theorem_1_7_b:
  assumes "A \<noteq> {}"
  shows "inj_on f A \<longleftrightarrow> (\<exists>r. r ` B \<subseteq> A \<and> id_on (r \<circ> f) A)"
  using assms theorem_1_7_b' theorem_1_7_b'' by metis

definition right_inv_into :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "right_inv_into A f s \<longleftrightarrow> s ` (f ` A) \<subseteq> A \<and> id_on (f \<circ> s) (f ` A)"

lemma right_inv_into:
  obtains s where "right_inv_into A f s"
proof -
  obtain s where "s ` f ` A \<subseteq> A" and "id_on (f \<circ> s) (f ` A)" using theorem_1_7_a' by blast
  thus "thesis" using that right_inv_into_def by fast
qed

lemma right_inv_intoD1:
  assumes "right_inv_into A f s"
  shows "s ` (f ` A) \<subseteq> A"
  using assms by (simp only: right_inv_into_def)

lemma right_inv_intoD2_pf:
  assumes "right_inv_into A f s"
  shows "id_on (f \<circ> s) (f ` A)"
  using assms by (simp only: right_inv_into_def)

lemma right_inv_intoD2:
  assumes "right_inv_into A f s" and
    "x \<in> f ` A"
  shows "f (s x) = x"
proof -
  from assms(1) have "id_on (f \<circ> s) (f ` A)" by (fact right_inv_intoD2_pf)
  with assms(2) have "(f \<circ> s) x = x" by (elim id_onD)
  thus "?thesis" by simp
qed

lemma right_inv_intoI:
  assumes "\<And>b. b \<in> f ` A \<Longrightarrow> s b \<in> A" and
    "\<And>b. b \<in> f ` A \<Longrightarrow> f (s b) = b"
  shows "right_inv_into A f s"
proof -
  have "s ` f ` A \<subseteq> A"
  proof (rule image_subsetI)
    fix b
    assume "b \<in> f ` A"
    thus "s b \<in> A" using assms(1) by auto
  qed
  moreover have "id_on (f \<circ> s) (f ` A)"
  proof (rule id_onI)
    fix b
    assume "b \<in> f ` A"
    hence "f (s b) = b" using assms(2) by auto
    thus "(f \<circ> s) b = b" by simp
  qed
  ultimately show "?thesis" by (simp only: right_inv_into_def)
qed

definition left_inv_into :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "left_inv_into A f r \<longleftrightarrow> id_on (r \<circ> f) A"

(*lemma left_inv_into:
  assumes "inj_on f A"
  obtains r where "left_inv_into A f r"
  sorry*)

lemma left_inv_intoD2_pf:
  assumes "left_inv_into A f r"
  shows "id_on (r \<circ> f) A"
  using assms by (simp only: left_inv_into_def)

lemma left_inv_intoD2:
  assumes "left_inv_into A f r" and
    "a \<in> A"
  shows "r (f a) = a"
proof -
  from assms(1) have "id_on (r \<circ> f) A" by (fact left_inv_intoD2_pf)
  with assms(2) have "(r \<circ> f) a = a" by (elim id_onD)
  thus "?thesis" by simp
qed

(*lemma left_inv_intoD1:
  assumes "left_inv_into A f r"
  shows "r ` f ` A \<subseteq> A"
proof (rule image_subsetI)
  fix b
  assume "b \<in> f ` A"
  then obtain a where "a \<in> A" and "b = f a" by auto
  from assms and \<open>a \<in> A\<close> have "r (f a) = a" by (elim left_inv_intoD2)
  with \<open>b = f a\<close> and \<open>a \<in> A\<close> show "r b \<in> A" by simp
qed*)

lemma left_inv_intoI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> r (f a) = a"
  shows "left_inv_into A f r"
proof -
  from assms have "id_on (r \<circ> f) A" by (auto intro: id_onI)
  thus "?thesis" by (fold left_inv_into_def)
qed

corollary
  assumes "A \<noteq> {}"
  shows "(\<exists>f. f ` A \<subseteq> B \<and> inj_on f A) \<longleftrightarrow> (\<exists>f. f ` B = A)"
proof (rule iffI)
  assume "\<exists>f. f ` A \<subseteq> B \<and> inj_on f A"
  then obtain f where "f ` A \<subseteq> B" and "inj_on f A" by auto
  from this(2) and assms obtain r where "r ` B \<subseteq> A" and "id_on (r \<circ> f) A" by (elim theorem_1_7_b')
  with \<open>f ` A \<subseteq> B\<close> have "r ` B = A" by (intro theorem_1_7_a'')
  thus "\<exists>f. f ` B = A" by auto
next
  assume "\<exists>f. f ` B = A"
  then obtain f where "f ` B = A" ..
  then obtain s where "s ` A \<subseteq> B" and "id_on (f \<circ> s) A" by (elim theorem_1_7_a')
  from this(2) have "inj_on s A" by (intro theorem_1_7_b'')
  with \<open>s ` A \<subseteq> B\<close> show "\<exists>f. f ` A \<subseteq> B \<and> inj_on f A" by auto
qed

(* TODO: problem_1_5_1 *)

proposition problem_1_5_5_a:
  shows "(\<Union>l \<in> \<Lambda>. A l) \<inter> (\<Union>\<mu> \<in> M. B \<mu>) = (\<Union>(l, \<mu>) \<in> \<Lambda> \<times> M. A l \<inter> B \<mu>)" (is "?LHS = ?RHS")
proof (rule set_eqI2)
  fix x
  assume "x \<in> ?LHS"
  hence "x \<in> (\<Union>l \<in> \<Lambda>. A l)" and "x \<in> (\<Union>\<mu> \<in> M. B \<mu>)" by auto
  from \<open>x \<in> (\<Union>l \<in> \<Lambda>. A l)\<close> obtain l where "l \<in> \<Lambda>" and "x \<in> A l" by auto
  from \<open>x \<in> (\<Union>\<mu> \<in> M. B \<mu>)\<close> obtain \<mu> where "\<mu> \<in> M" and "x \<in> B \<mu>" by auto
  from \<open>l \<in> \<Lambda>\<close> and \<open>\<mu> \<in> M\<close> have "(l, \<mu>) \<in> \<Lambda> \<times> M" by auto
  moreover from \<open>x \<in> A l\<close> and \<open>x \<in> B \<mu>\<close> have "x \<in> A l \<inter> B \<mu>" by auto
  ultimately show "x \<in> ?RHS" by auto
next
  fix x
  assume "x \<in> ?RHS"
  then obtain l and \<mu> where "(l, \<mu>) \<in> \<Lambda> \<times> M" and "x \<in> A l \<inter> B \<mu>" by auto
  hence "l \<in> \<Lambda>" and "\<mu> \<in> M" and "x \<in> A l" and "x \<in> B \<mu>" by auto
  from \<open>l \<in> \<Lambda>\<close> and \<open>x \<in> A l\<close> have "x \<in> (\<Union>l \<in> \<Lambda>. A l)" by auto
  moreover from \<open>\<mu> \<in> M\<close> and \<open>x \<in> B \<mu>\<close> have "x \<in> (\<Union>\<mu> \<in> M. B \<mu>)" by auto
  ultimately show "x \<in> ?LHS" by auto
qed

proposition problem_1_5_5_b:
  shows "(\<Inter>l \<in> \<Lambda>. A l) \<union> (\<Inter>\<mu> \<in> M. B \<mu>) = (\<Inter>(l, \<mu>) \<in> \<Lambda> \<times> M. A l \<union> B \<mu>)" (is "?LHS = ?RHS")
proof (rule set_eqI2)
  fix x
  assume "x \<in> ?LHS"
  moreover {
    assume "x \<in> (\<Inter>l \<in> \<Lambda>. A l)"
    {
      fix l and \<mu>
      assume "(l, \<mu>) \<in> \<Lambda> \<times> M"
      hence "l \<in> \<Lambda>" by simp
      with \<open>x \<in> (\<Inter>l \<in> \<Lambda>. A l)\<close> have "x \<in> A l" by simp
      hence "x \<in> A l \<union> B \<mu>" ..
    }
    hence "x \<in> (\<Inter>(l, \<mu>) \<in> \<Lambda> \<times> M. A l \<union> B \<mu>)" by simp
  }
  moreover {
    assume "x \<in> (\<Inter>\<mu> \<in> M. B \<mu>)"
    {
      fix l and \<mu>
      assume "(l, \<mu>) \<in> \<Lambda> \<times> M"
      hence "\<mu> \<in> M" by simp
      with \<open>x \<in> (\<Inter>\<mu> \<in> M. B \<mu>)\<close> have "x \<in> B \<mu>" by simp
      hence "x \<in> A l \<union> B \<mu>" ..
    }
    hence "x \<in> (\<Inter>(l, \<mu>) \<in> \<Lambda> \<times> M. A l \<union> B \<mu>)" by simp
  }
  ultimately show "x \<in> ?RHS" ..
next
  fix x
  assume "x \<in> ?RHS"
  {
    assume "x \<notin> (\<Inter>l \<in> \<Lambda>. A l)"
    then obtain l where "l \<in> \<Lambda>" and "x \<notin> A l" by auto
    {
      fix \<mu>
      assume "\<mu> \<in> M"
      with \<open>l \<in> \<Lambda>\<close> and \<open>x \<in> ?RHS\<close> have "x \<in> A l \<union> B \<mu>" by auto
      with \<open>x \<notin> A l\<close> have "x \<in> B \<mu>" by simp
    }
    hence "x \<in> (\<Inter>\<mu> \<in> M. B \<mu>)" ..
  }
  thus "x \<in> ?LHS" by auto
qed

lemma mem_TimesI:
  assumes "fst p \<in> A" and "snd p \<in> B"
  shows "p \<in> A \<times> B"
  using assms by (simp only: mem_Times_iff)

proposition problem_1_5_5_c:
  shows "(\<Union>l \<in> \<Lambda>. A l) \<times> (\<Union>\<mu> \<in> M. B \<mu>) = (\<Union>(l, \<mu>) \<in> \<Lambda> \<times> M. A l \<times> B \<mu>)" (is "?LHS = ?RHS")
proof (rule set_eqI2)
  fix x
  assume "x \<in> ?LHS"
  hence "fst x \<in> (\<Union>l \<in> \<Lambda>. A l)" and "snd x \<in> (\<Union>\<mu> \<in> M. B \<mu>)" by auto
  then obtain l and \<mu> where "l \<in> \<Lambda>" and "fst x \<in> A l" and "\<mu> \<in> M" and "snd x \<in> B \<mu>" by auto
  from \<open>l \<in> \<Lambda>\<close> and \<open>\<mu> \<in> M\<close> have "(l, \<mu>) \<in> \<Lambda> \<times> M" by simp
  moreover from \<open>fst x \<in> A l\<close> and \<open>snd x \<in> B \<mu>\<close> have "x \<in> A l \<times> B \<mu>" by (fact mem_TimesI)
  ultimately show "x \<in> ?RHS" by auto
next
  fix x
  assume "x \<in> ?RHS"
  then obtain l and \<mu> where "l \<in> \<Lambda>" and "\<mu> \<in> M" and "x \<in> A l \<times> B \<mu>" by auto
  from this(3) have "fst x \<in> A l" and "snd x \<in> B \<mu>" by auto
  from \<open>l \<in> \<Lambda>\<close> and \<open>fst x \<in> A l\<close> have "fst x \<in> (\<Union>l \<in> \<Lambda>. A l)" by auto
  moreover from \<open>\<mu> \<in> M\<close> and \<open>snd x \<in> B \<mu>\<close> have "snd x \<in> (\<Union>\<mu> \<in> M. B \<mu>)" by auto
  ultimately show "x \<in> ?LHS" by (intro mem_TimesI)
qed

proposition problem_1_5_5_d:
  assumes "\<Lambda> \<noteq> {}" and "M \<noteq> {}"
  shows "(\<Inter>l \<in> \<Lambda>. A l) \<times> (\<Inter>\<mu> \<in> M. B \<mu>) = (\<Inter>(l, \<mu>) \<in> \<Lambda> \<times> M. A l \<times> B \<mu>)" (is "?LHS = ?RHS")
proof (rule set_eqI2)
  fix x
  assume "x \<in> ?LHS"
  hence "fst x \<in> (\<Inter>l \<in> \<Lambda>. A l)" and "snd x \<in> (\<Inter>\<mu> \<in> M. B \<mu>)" by auto
  {
    fix l and \<mu>
    assume "(l, \<mu>) \<in> \<Lambda> \<times> M"
    hence "l \<in> \<Lambda>" and "\<mu> \<in> M" by auto
    from \<open>l \<in> \<Lambda>\<close> and \<open>fst x \<in> (\<Inter>l \<in> \<Lambda>. A l)\<close> have "fst x \<in> A l" by simp
    moreover from \<open>\<mu> \<in> M\<close> and \<open>snd x \<in> (\<Inter>\<mu> \<in> M. B \<mu>)\<close> have "snd x \<in> B \<mu>" by simp
    ultimately have "x \<in> A l \<times> B \<mu>" by (intro mem_TimesI)
  }
  thus "x \<in> ?RHS" by auto
next
  fix x
  assume "x \<in> ?RHS"
  have "fst x \<in> (\<Inter>l \<in> \<Lambda>. A l)"
  proof (rule INT_I)
    fix l
    assume "l \<in> \<Lambda>"
    with \<open>x \<in> ?RHS\<close> have "\<forall>\<mu> \<in> M. x \<in> A l \<times> B \<mu>" by blast
    with assms(2) obtain \<mu> where "\<mu> \<in> M" and "x \<in> A l \<times> B \<mu>" by blast
    thus "fst x \<in> A l" by auto
  qed
  moreover have "snd x \<in> (\<Inter>\<mu> \<in> M. B \<mu>)"
  proof (rule INT_I)
    fix \<mu>
    assume "\<mu> \<in> M"
    with \<open>x \<in> ?RHS\<close> have "\<forall>l \<in> \<Lambda>. x \<in> A l \<times> B \<mu>" by blast
    with assms(1) obtain l where "l \<in> \<Lambda>" and "x \<in> A l \<times> B \<mu>" by blast
    thus "snd x \<in> B \<mu>" by auto
  qed
  ultimately show "x \<in> ?LHS" by (intro mem_TimesI)
qed

definition pairwise_disjnt_idx :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> bool"
  where "pairwise_disjnt_idx \<Lambda> A \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. \<forall>l' \<in> \<Lambda>. l \<noteq> l' \<longrightarrow> A l \<inter> A l' = {})"

lemma pairwise_disjnt_idxD:
  assumes "pairwise_disjnt_idx \<Lambda> A" and
    "l \<in> \<Lambda>" and
    "l' \<in> \<Lambda>" and
    "l \<noteq> l'"
  shows "A l \<inter> A l' = {}"
proof -
  from assms(1) have "\<forall>l \<in> \<Lambda>. \<forall>l' \<in> \<Lambda>. l \<noteq> l' \<longrightarrow> A l \<inter> A l' = {}"
    by (simp only: pairwise_disjnt_idx_def)
  with assms(2-4) show ?thesis by blast
qed

lemma pairwise_disjnt_idx_mem_imp_eq:
  assumes "pairwise_disjnt_idx \<Lambda> A" and
    "l \<in> \<Lambda>" and
    "l' \<in> \<Lambda>" and
    "a \<in> A l \<inter> A l'"
  shows "l = l'"
proof (rule ccontr)
  assume "l \<noteq> l'"
  with assms(1-3) have "A l \<inter> A l' = {}" by (elim pairwise_disjnt_idxD)
  with assms(4) show "False" by simp
qed

lemma pairwise_disjnt_idx_imp_uniq_idx:
  assumes "pairwise_disjnt_idx \<Lambda> A"
    and "a \<in> (\<Union>l \<in> \<Lambda>. A l)"
  shows "\<exists>!l \<in> \<Lambda>. a \<in> A l"
proof -
  from assms(2) obtain l where *: "l \<in> \<Lambda> \<and> a \<in> A l" by auto
  moreover {
    fix l'
    assume **: "l' \<in> \<Lambda> \<and> a \<in> A l'"
    from * have "l \<in> \<Lambda>" ..
    moreover from ** have "l' \<in> \<Lambda>" ..
    moreover from * and ** have "a \<in> A l \<inter> A l'" by simp
    moreover note assms(1)
    ultimately have "l = l'" by (elim pairwise_disjnt_idx_mem_imp_eq)
  }
  ultimately show ?thesis by auto
qed

proposition problem_1_5_6:
  assumes "pairwise_disjnt_idx \<Lambda> A"
    and "\<forall>l \<in> \<Lambda>. (f l) ` (A l) \<subseteq> B"
  shows "\<exists>F. F ` (\<Union>l \<in> \<Lambda>. A l) \<subseteq> B \<and> (\<forall>l \<in> \<Lambda>. ext_eq_on (A l) F (f l))"
proof -
  let ?F = "\<lambda>a. f (THE l. l \<in> \<Lambda> \<and> a \<in> A l) a"
  have "?F ` (\<Union>l \<in> \<Lambda>. A l) \<subseteq> B"
  proof (rule image_subsetI)
    fix a
    assume "a \<in> (\<Union>l \<in> \<Lambda>. A l)"
    with assms(1) have "\<exists>!l \<in> \<Lambda>. a \<in> A l" by (elim pairwise_disjnt_idx_imp_uniq_idx)
    then obtain l where "l \<in> \<Lambda> \<and> a \<in> A l" by auto
    hence "l \<in> \<Lambda>" and \<open>a \<in> A l\<close> by auto
    from \<open>\<exists>!l \<in> \<Lambda>. a \<in> A l\<close> and \<open>l \<in> \<Lambda> \<and> a \<in> A l\<close> have "(THE l. l \<in> \<Lambda> \<and> a \<in> A l) = l" by auto
    hence "?F a = f l a" by simp
    from assms(2) and \<open>l \<in> \<Lambda>\<close> have "(f l) ` (A l) \<subseteq> B" ..
    with \<open>a \<in> A l\<close> have "f l a \<in> B" by auto
    with \<open>?F a = f l a\<close> show "?F a \<in> B" by simp
  qed
  moreover have "\<forall>l \<in> \<Lambda>. ext_eq_on (A l) ?F (f l)"
  proof (rule ballI)
    fix l
    assume "l \<in> \<Lambda>"
    {
      fix a
      assume "a \<in> A l"
      with \<open>l \<in> \<Lambda>\<close> have "l \<in> \<Lambda> \<and> a \<in> A l" ..
      moreover {
        fix l'
        assume *: "l' \<in> \<Lambda> \<and> a \<in> A l'"
        note \<open>l \<in> \<Lambda>\<close>
        moreover from * have "l' \<in> \<Lambda>" ..
        moreover from \<open>a \<in> A l\<close> and * have "a \<in> A l' \<inter> A l" by simp
        moreover note assms(1)
        ultimately have "l' = l" by (elim pairwise_disjnt_idx_mem_imp_eq)
      }
      ultimately have "(THE l. l \<in> \<Lambda> \<and> a \<in> A l) = l" by (intro the_equality)
      hence "?F a = f l a" by simp
    }
    thus "ext_eq_on (A l) ?F (f l)" by (intro ext_eq_onI)
  qed
  ultimately show ?thesis by auto
qed

proposition problem_1_5_6':
  assumes -- {* @{prop "pairwise_disjnt_idx \<Lambda> A"}: an unnecessary condition. *}
    -- {* @{prop "F ` (\<Union>l \<in> \<Lambda>. A l) \<subseteq> B"}: an unnecessary condition. *}
    "\<forall>l \<in> \<Lambda>. ext_eq_on (A l) F (f l)" and
    -- {* @{prop "F' ` (\<Union>l \<in> \<Lambda>. A l) \<subseteq> B"}: an unnecessary condition. *}
    "\<forall>l \<in> \<Lambda>. ext_eq_on (A l) F' (f l)"
  shows "ext_eq_on (\<Union>l \<in> \<Lambda>. A l) F F'"
proof (rule ext_eq_onI)
  fix a
  assume "a \<in> (\<Union>l \<in> \<Lambda>. A l)"
  then obtain l where "l \<in> \<Lambda>" and "a \<in> A l" by blast
  from \<open>l \<in> \<Lambda>\<close> and assms(1) have "ext_eq_on (A l) F (f l)" by simp
  moreover from \<open>l \<in> \<Lambda>\<close> and assms(2) have "ext_eq_on (A l) F' (f l)" by simp
  ultimately have "ext_eq_on (A l) F F'" using ext_eq_on_sym ext_eq_on_trans by blast
  with \<open>a \<in> A l\<close> show "F a = F' a" by (elim ext_eq_onD)
qed

lemma PiE_not_emptyE_one_point:
  assumes "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<noteq> {}" and
    "l \<in> \<Lambda>" and
    "al \<in> A l"
  obtains a where "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" and
    "a l = al"
proof -
  from assms(1) obtain a where *: "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" by auto
  let ?a' = "\<lambda>l'. if l' = l then al else a l'"
  have "?a' l = al" by simp
  moreover have "?a' \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
  proof (rule PiE_I)
    fix l'
    assume "l' \<in> \<Lambda>"
    {
      assume "l' = l"
      hence "?a' l' = al" by simp
      with assms(3) have "?a' l' \<in> A l" by simp
      with \<open>l' = l\<close> have "?a' l' \<in> A l'" by simp
    }
    moreover {
      assume "l' \<noteq> l"
      hence "?a' l' = a l'" by simp
      also from * and \<open>l' \<in> \<Lambda>\<close> have "\<dots> \<in> A l'" by (elim PiE_D1)
      finally have "?a' l' \<in> A l'" .
    }
    ultimately show "?a' l' \<in> A l'" by simp
  next
    fix l'
    assume "l' \<notin> \<Lambda>"
    with assms(2) have "l' \<noteq> l" by auto
    hence "?a' l' = a l'" by simp
    also from * and \<open>l' \<notin> \<Lambda>\<close> have "a l' = undefined" by (elim PiE_D2)
    finally show "?a' l' = undefined" .
  qed
  ultimately show "thesis" using that by blast
qed

proposition problem_1_5_7:
  assumes "\<forall>l \<in> \<Lambda>. A l \<noteq> {}" and
    "l \<in> \<Lambda>"
  shows "(proj l) ` (\<Pi>\<^sub>E l \<in> \<Lambda>. A l) = A l"
proof (rule surj_onI)
  fix a
  assume "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
  with assms(2) show "proj l a \<in> A l" by (elim mem_PiE_imp_proj_mem)
next
  fix al
  assume "al \<in> A l"
  moreover from assms(1) have "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<noteq> {}" by (fact AC)
  moreover note assms(2)
  ultimately obtain a where "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" and
    "a l = al" by (elim PiE_not_emptyE_one_point)
  from this(2) have "proj l a = al" by (auto simp only: proj_eq)
  with \<open>a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)\<close> show "\<exists>a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l). proj l a = al" by auto
qed

proposition problem_1_5_8':
  assumes "\<forall>l \<in> \<Lambda>. A l \<noteq> {}" and
    "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<subseteq> (\<Pi>\<^sub>E l \<in> \<Lambda>. B l)" and
    "l \<in> \<Lambda>"
  shows "A l \<subseteq> B l"
proof -
  {
    assume "\<exists>l \<in> \<Lambda>. B l = {}"
    then obtain l' where "l' \<in> \<Lambda>" and "B l' = {}" by auto
    hence "(\<Pi>\<^sub>E l \<in> \<Lambda>. B l) = {}" by (rule PiE_empty_range)
    with assms(2) have "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) = {}" by simp
    moreover from assms(1) have "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<noteq> {}" by (fact AC)
    ultimately have "False" by simp
  }
  hence *: "\<forall>l \<in> \<Lambda>. B l \<noteq> {}" by auto
  from assms(1,3) have "A l = (proj l) ` (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" by (fact problem_1_5_7[THEN sym])
  also from assms(2) have "\<dots> \<subseteq> (proj l) ` (\<Pi>\<^sub>E l \<in> \<Lambda>. B l)" by auto
  also from * and assms(3) have "\<dots> = B l" by (fact problem_1_5_7)
  finally show "?thesis" .
qed

proposition problem_1_5_8'':
  assumes -- {* @{prop "\<forall>l \<in> \<Lambda>. A l \<noteq> {}"}: an unnecessary condition. *}
    "\<forall>l \<in> \<Lambda>. A l \<subseteq> B l"
  shows "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<subseteq> (\<Pi>\<^sub>E l \<in> \<Lambda>. B l)"
proof (rule subsetI)
  fix a
  assume *: "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
  {
    fix l
    assume "l \<in> \<Lambda>"
    with * have "a l \<in> A l" by (elim PiE_D1)
    also from \<open>l \<in> \<Lambda>\<close> and assms(1) have "A l \<subseteq> B l" by simp
    finally have "a l \<in> B l" .
  }
  moreover {
    fix l
    assume "l \<notin> \<Lambda>"
    with * have "a l = undefined" by (rule PiE_D2)
  }
  ultimately show "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. B l)" by (rule PiE_I)
qed

proposition problem_1_5_8:
  assumes "\<forall>l \<in> \<Lambda>. A l \<noteq> {}"
  shows "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<subseteq> (\<Pi>\<^sub>E l \<in> \<Lambda>. B l) \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. A l \<subseteq> B l)"
proof (rule iffI)
  assume "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<subseteq> (\<Pi>\<^sub>E l \<in> \<Lambda>. B l)"
  {
    fix l
    assume "l \<in> \<Lambda>"
    with assms and \<open>(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<subseteq> (\<Pi>\<^sub>E l \<in> \<Lambda>. B l)\<close> have "A l \<subseteq> B l" by (rule problem_1_5_8')
  }
  thus "\<forall>l \<in> \<Lambda>. A l \<subseteq> B l" ..
next
  assume "\<forall>l \<in> \<Lambda>. A l \<subseteq> B l"
  thus "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<subseteq> (\<Pi>\<^sub>E l \<in> \<Lambda>. B l)" by (fact problem_1_5_8'')
qed

proposition problem_1_5_9:
  shows "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<inter> (\<Pi>\<^sub>E l \<in> \<Lambda>. B l) = (\<Pi>\<^sub>E l \<in> \<Lambda>. A l \<inter> B l)" (is "?LHS = ?RHS")
proof (rule set_eqI)
  fix a
  have "a \<in> ?LHS \<longleftrightarrow> a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<and> a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. B l)" by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. a l \<in> A l) \<and> (\<forall>l. l \<notin> \<Lambda> \<longrightarrow> a l = undefined)
                      \<and> (\<forall>l \<in> \<Lambda>. a l \<in> B l) \<and> (\<forall>l. l \<notin> \<Lambda> \<longrightarrow> a l = undefined)"
    by (simp add: mem_PiE_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. a l \<in> A l \<and> a l \<in> B l) \<and> (\<forall>l. l \<notin> \<Lambda> \<longrightarrow> a l = undefined)" by blast
  also have "\<dots> \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. a l \<in> A l \<inter> B l) \<and> (\<forall>l. l \<notin> \<Lambda> \<longrightarrow> a l = undefined)" by simp
  also have "\<dots> \<longleftrightarrow> a \<in> ?RHS" by (simp only: mem_PiE_iff)
  finally show "a \<in> ?LHS \<longleftrightarrow> a \<in> ?RHS" .
qed

lemma AC_E_prop:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> \<exists>al \<in> A l. P l al"
  obtains a where "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" and
    "\<forall>l \<in> \<Lambda>. P l (a l)"
proof -
  let ?A' = "\<lambda>l'. {al \<in> A l'. P l' al}"
  {
    fix l
    assume "l \<in> \<Lambda>"
    with assms have "?A' l \<noteq> {}" by blast
  }
  then obtain a where *: "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. ?A' l)" by (elim AC_E)
  {
    fix l
    assume "l \<in> \<Lambda>"
    with * have "a l \<in> ?A' l" by (elim PiE_D1)
    hence "a l \<in> A l" by simp
  }
  moreover {
    fix l
    assume "l \<notin> \<Lambda>"
    with * have "a l = undefined" by (elim PiE_D2)
  }
  ultimately have "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" by (intro PiE_I)
  moreover have "\<forall>l \<in> \<Lambda>. P l (a l)"
  proof (rule ballI)
    fix l
    assume "l \<in> \<Lambda>"
    with * have "a l \<in> ?A' l" by (elim PiE_D1)
    thus "P l (a l)" by simp
  qed
  ultimately obtain a where "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" and
    "\<forall>l \<in> \<Lambda>. P l (a l)" by blast
  thus "thesis" by (simp only: that)
qed

proposition problem_1_5_10:
  assumes "(\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<noteq> {}" and -- {* This assumption is not specified in the book. However,
                                            there exists a counterexample without it. *}
    "\<forall>l \<in> \<Lambda>. (f l) ` (A l) \<subseteq> B l"
  defines F: "F a \<equiv> (l \<in> \<Lambda>. f l (a l))"
  shows "F ` (\<Pi>\<^sub>E l \<in> \<Lambda>. A l) = (\<Pi>\<^sub>E l \<in> \<Lambda>. B l) \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. f l ` A l = B l)"
    (is "?LHS1 \<longleftrightarrow> ?RHS1") and
    "inj_on F (\<Pi>\<^sub>E l \<in> \<Lambda>. A l) \<longleftrightarrow> (\<forall>l \<in> \<Lambda>. inj_on (f l) (A l))" (is "?LHS2 \<longleftrightarrow> ?RHS2")
proof -
  let ?\<AA> = "\<Pi>\<^sub>E l \<in> \<Lambda>. A l" and
    ?\<BB> = "\<Pi>\<^sub>E l \<in> \<Lambda>. B l"
  {
    fix a
    assume "a \<in> ?\<AA>"
    {
      fix l
      assume "l \<in> \<Lambda>"
      with \<open>a \<in> ?\<AA>\<close> have "a l \<in> A l" by (elim PiE_D1)
      with \<open>l \<in> \<Lambda>\<close> and assms(2) have "f l (a l) \<in> B l" by auto
      with \<open>l \<in> \<Lambda>\<close> have "F a l \<in> B l" by (simp only: F pie_eq)
    }
    moreover {
      fix l
      assume "l \<notin> \<Lambda>"
      hence "F a l = undefined" by (simp add: F pie_eq_undefined)
    }
    ultimately have "F a \<in> ?\<BB>" by (intro PiE_I)
  }
  hence "F ` ?\<AA> \<subseteq> ?\<BB>" by auto
  with assms(1) have "?\<BB> \<noteq> {}" by blast
  have "F a l = f l (a l)" if "l \<in> \<Lambda>" for a and l using that by (simp only: F pie_eq)
  have "F a l \<in> B l" if "a \<in> ?\<AA>" and "l \<in> \<Lambda>" for a and l
  proof -
    from \<open>F ` ?\<AA> \<subseteq> ?\<BB>\<close> and that(1) have "F a \<in> ?\<BB>" by blast
    with that(2) show "?thesis" by (elim PiE_D1)
  qed
  {
    assume *: "?LHS1"
    {
      fix l
      assume "l \<in> \<Lambda>"
      {
        fix al
        assume "al \<in> A l"
        with \<open>l \<in> \<Lambda>\<close> and assms(2) have "f l al \<in> B l" by auto
      }
      moreover {
        fix bl
        assume "bl \<in> B l"
        with \<open>?\<BB> \<noteq> {}\<close> and \<open>l \<in> \<Lambda>\<close> obtain b where "b \<in> ?\<BB>" and "b l = bl"
          by (elim PiE_not_emptyE_one_point)
        from \<open>b \<in> ?\<BB>\<close> and * obtain a where "a \<in> ?\<AA>" and "b = F a" by blast
        from \<open>a \<in> ?\<AA>\<close> and \<open>l \<in> \<Lambda>\<close> have "a l \<in> A l" by (elim PiE_D1)
        moreover have "f l (a l) = bl"
        proof -
          from \<open>b = F a\<close> have "b = (l \<in> \<Lambda>. f l (a l))" by (simp only: F)
          hence "b l = (l \<in> \<Lambda>. f l (a l)) l" by simp
          with \<open>l \<in> \<Lambda>\<close> show "?thesis" by (simp only: \<open>b l = bl\<close> pie_eq)
        qed
        ultimately have "\<exists>al \<in> A l. f l al = bl" by auto
      }
      ultimately have "f l ` A l = B l" by (intro surj_onI)
    }
    hence "?RHS1" ..
  }
  moreover {
    assume "\<forall>l \<in> \<Lambda>. f l ` A l = B l"
    {
      fix a
      assume "a \<in> ?\<AA>"
      with \<open>F ` ?\<AA> \<subseteq> ?\<BB>\<close> have "F a \<in> ?\<BB>" by auto
    }
    moreover {
      fix b
      assume "b \<in> ?\<BB>"
      {
        fix l
        assume "l \<in> \<Lambda>"
        with \<open>b \<in> ?\<BB>\<close> have "b l \<in> B l" by (elim PiE_D1)
        with \<open>l \<in> \<Lambda>\<close> and \<open>\<forall>l \<in> \<Lambda>. f l ` A l = B l\<close> have "\<exists>al \<in> A l. b l = f l al" by auto
      }
      then obtain a where "a \<in> ?\<AA>" and "\<forall>l \<in> \<Lambda>. b l = f l (a l)" by (elim AC_E_prop)
      from \<open>\<forall>l \<in> \<Lambda>. b l = f l (a l)\<close> have "(l \<in> \<Lambda>. b l) = (l \<in> \<Lambda>. f l (a l))"
        using pie_eq_iff by auto
      with \<open>b \<in> ?\<BB>\<close> have "(l \<in> \<Lambda>. f l (a l)) = b" by (simp add: pie_collapse)
      hence "F a = b" by (simp only: F)
      with \<open>a \<in> ?\<AA>\<close> have "\<exists>a \<in> ?\<AA>. F a = b" by auto
    }
    ultimately have "F ` ?\<AA> = ?\<BB>" by (intro surj_onI)
  }
  ultimately show "?LHS1 \<longleftrightarrow> ?RHS1" ..
  {
    assume "?LHS2"
    {
      fix l
      assume "l \<in> \<Lambda>"
      {
        fix al and al'
        assume "al \<in> A l" and
          "al' \<in> A l" and
          "f l al = f l al'"
        from \<open>al \<in> A l\<close> and \<open>l \<in> \<Lambda>\<close> and assms(1) obtain a where "a \<in> ?\<AA>" and "a l = al"
          by (elim PiE_not_emptyE_one_point)
        let ?a' = "\<lambda>l'. if l' = l then al' else a l'"
        have "?a' \<in> ?\<AA>"
        proof (rule PiE_I)
          fix l'
          assume "l' \<in> \<Lambda>"
          {
            assume "l' = l"
            hence "?a' l' = al'" by simp
            also note \<open>al' \<in> A l\<close>
            finally have "?a' l' \<in> A l" .
            with \<open>l' = l\<close> have "?a' l' \<in> A l'" by simp
          }
          moreover {
            assume "l' \<noteq> l"
            hence "?a' l' = a l'" by simp
            also from this and \<open>a \<in> ?\<AA>\<close> and \<open>l' \<in> \<Lambda>\<close> have "a l' \<in> A l'" by (elim PiE_D1)
            finally have "?a' l' \<in> A l'" .
          }
          ultimately show "?a' l' \<in> A l'" by simp
        next
          fix l'
          assume "l' \<notin> \<Lambda>"
          with \<open>l \<in> \<Lambda>\<close> have "l' \<noteq> l" by auto
          hence "?a' l' = a l'" by simp
          also from this and \<open>a \<in> ?\<AA>\<close> and \<open>l' \<notin> \<Lambda>\<close> have "a l' = undefined" by auto
          finally show "?a' l' = undefined" .
        qed
        moreover have "F a = F ?a'"
        proof (rule PiE_eqI)
          from \<open>a \<in> ?\<AA>\<close> and \<open>F ` ?\<AA> \<subseteq> ?\<BB>\<close> show "F a \<in> ?\<BB>" by auto
          from \<open>?a' \<in> ?\<AA>\<close> and \<open>F ` ?\<AA> \<subseteq> ?\<BB>\<close> show "F ?a' \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. B l)" by auto
          fix l'
          assume "l' \<in> \<Lambda>"
          {
            assume "l' = l"
            hence "F a l' = F a l" by simp
            also from \<open>l \<in> \<Lambda>\<close> have "\<dots> = f l (a l)" by (simp only: F pie_eq)
            also have "\<dots> = f l al" by (simp only: \<open>a l = al\<close>)
            also have "\<dots> = f l al'" by (fact \<open>f l al = f l al'\<close>)
            also from \<open>l' = l\<close> have "\<dots> = f l (?a' l')" by simp
            also from \<open>l \<in> \<Lambda>\<close> have "\<dots> = F ?a' l'" by (simp only: \<open>l' = l\<close> pie_eq F)
            finally have "F a l' = F ?a' l'" .
          }
          moreover {
            assume "l' \<noteq> l"
            from \<open>l' \<in> \<Lambda>\<close> have "F a l' = f l' (a l')" by (simp only: F pie_eq)
            also from \<open>l' \<noteq> l\<close> have "\<dots> = f l' (?a' l')" by simp
            also from \<open>l' \<in> \<Lambda>\<close> have "\<dots> = F ?a' l'" by (simp only: pie_eq F)
            finally have "F a l' = F ?a' l'" .
          }
          ultimately show "F a l' = F ?a' l'" by auto
        qed
        moreover note \<open>a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)\<close>
        moreover note \<open>?LHS2\<close>
        ultimately have "a = ?a'" by (elim inj_onD)
        hence "a l = ?a' l" by (fact fun_cong)
        with \<open>a l = al\<close> have "al = al'" by simp
      }
      hence "inj_on (f l) (A l)" by (intro inj_onI)
    }
    hence "?RHS2" ..
  }
  moreover {
    assume "?RHS2"
    {
      fix a and a'
      assume "a \<in> ?\<AA>" and
        "a' \<in> ?\<AA>" and
        "F a = F a'"
      {
        fix l
        assume "l \<in> \<Lambda>"
        with \<open>?RHS2\<close> have "inj_on (f l) (A l)" ..
        moreover from \<open>a \<in> ?\<AA>\<close> and \<open>l \<in> \<Lambda>\<close> have "a l \<in> A l" by (elim PiE_D1)
        moreover from \<open>a' \<in> ?\<AA>\<close> and \<open>l \<in> \<Lambda>\<close> have "a' l \<in> A l" by (elim PiE_D1)
        moreover have "f l (a l) = f l (a' l)"
        proof -
          from \<open>l \<in> \<Lambda>\<close> have "f l (a l) = F a l" by (simp only: pie_eq F)
          also have "\<dots> = F a' l" by (simp only: \<open>F a = F a'\<close>)
          also from \<open>l \<in> \<Lambda>\<close> have "\<dots> = f l (a' l)" by (simp only: F pie_eq)
          finally show "?thesis" .
        qed
        ultimately have "a l = a' l" by (elim inj_onD)
      }
      with \<open>a \<in> ?\<AA>\<close> and \<open>a' \<in> ?\<AA>\<close> have "a = a'" by (intro PiE_eqI)
    }
    hence "?LHS2" by (intro inj_onI)
  }
  ultimately show "?LHS2 \<longleftrightarrow> ?RHS2" ..
qed

proposition problem_1_5_11':
  assumes "f ` A = B" and
    "right_inv_into A f s" and
    "right_inv_into A f s'" and
    "s ` B \<subseteq> s' ` B"
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

proposition problem_1_5_11:
  assumes "f ` A = B" and
    "right_inv_into A f s" and
    "right_inv_into A f s'" and
    "s ` B \<subseteq> s' ` B \<or> s' ` B \<subseteq> s ` B"
  shows "ext_eq_on B s s'"
proof -
  {
    assume "s ` B \<subseteq> s' ` B"
    with assms(1-3) have "?thesis" by (elim problem_1_5_11')
  }
  moreover {
    assume "s' ` B \<subseteq> s ` B"
    with assms(1-3) have "ext_eq_on B s' s" by (elim problem_1_5_11')
    hence "?thesis" by (fact ext_eq_on_sym)
  }
  moreover note assms(4)
  ultimately show "?thesis" by auto
qed

proposition problem_1_5_12_a:
  assumes "f ` A = B" and
    -- {* @{prop "f' ` B = C"}: an unnecessary condition. *}
    "right_inv_into A f s" and
    "right_inv_into B f' s'"
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

proposition problem_1_5_12_b:
  assumes "f ` A \<subseteq> B" and
    "f' ` B \<subseteq> C" and
    "inj_on f A" and
    "inj_on f' B" and
    "left_inv_into A f r" and
    "left_inv_into B f' r'"
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

proposition problem_1_5_13':
  assumes -- {* @{prop "g ` B \<subseteq> C"}: an unnecessary assumption. *}
    -- {* @{prop "h ` A \<subseteq> C"}: an unnecessary assumption. *}
    "f ` A \<subseteq> B" and
    "ext_eq_on A h (g \<circ> f)"
  shows "h ` A \<subseteq> g ` B"
proof (rule subsetI)
  fix c
  assume "c \<in> h ` A"
  then obtain a where "a \<in> A" and "c = h a" by auto
  from \<open>a \<in> A\<close> and assms(1) have "f a \<in> B" by auto
  moreover have "g (f a) = c"
  proof -
    from \<open>a \<in> A\<close> and assms(2) have "h a = (g \<circ> f) a" by (elim ext_eq_onD)
    with \<open>c = h a\<close> show "?thesis" by simp
  qed
  ultimately show "c \<in> g ` B" by auto
qed

proposition problem_1_5_13'':
  assumes -- {* @{prop "g ` B \<subseteq> C"}: an unnecessary condition. *}
    -- {* @{prop "h ` A \<subseteq> C"}: an unnecessary condition. *}
    "h ` A \<subseteq> g ` B"
  obtains f where "f ` A \<subseteq> B" and "ext_eq_on A h (g \<circ> f)"
proof -
  obtain s where *: "right_inv_into B g s" by (elim right_inv_into)
  from \<open>right_inv_into B g s\<close> have "id_on (g \<circ> s) (g ` B)" by (elim right_inv_intoD2_pf)
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

proposition problem_1_5_13:
  shows "(\<exists>f. f ` A \<subseteq> B \<and> ext_eq_on A h (g \<circ> f)) \<longleftrightarrow> h ` A \<subseteq> g ` B"
  using problem_1_5_13' problem_1_5_13'' by metis

proposition problem_1_5_14':
  assumes -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    -- {* @{prop "h ` A \<subseteq> C"}: an unnecessary assumption. *}
    -- {* @{prop "g ` B \<subseteq> C"}: an unnecessary assumption. *}
    "ext_eq_on A h (g \<circ> f)" and
    "a \<in> A" and
    "a' \<in> A" and
    "f a = f a'"
  shows "h a = h a'"
proof -
  from assms(4) have "g (f a) = g (f a')" by simp
  with assms(1-3) show "h a = h a'" using ext_eq_onD by fastforce
qed

lemma the_singleton_equality:
  assumes "a \<in> A" and
    "\<And>x. x \<in> A \<Longrightarrow> x = a"
  shows "(THE a. A = {a}) = a"
  using assms by blast

proposition problem_1_5_14'':
  fixes A :: "'a set" and
    B :: "'b set" and
    C :: "'c set"
  assumes "A = {} \<Longrightarrow> B = {}" and -- {* This assumption is not specified in the book. However,
                                        there exists a counterexample without it. *}
    -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    "h ` A \<subseteq> C" and
    "\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> f a = f a' \<Longrightarrow> h a = h a'"
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
      finally show "?thesis" .
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
    moreover from \<open>A = {}\<close> have "ext_eq_on A h (?g \<circ> f)" by (auto simp only: ext_eq_on_empty)
    ultimately have "thesis" by (fact that)
  }
  ultimately show "thesis" by auto
qed

proposition problem_1_5_14:
  assumes "A = {} \<Longrightarrow> B = {}" and-- {* This assumption is not specified in the book. However, there
                                       exists a counterexample without it. *}
    -- {* @{prop "f ` A \<subseteq> B"}: an unnecessary assumption. *}
    "h ` A \<subseteq> C"
  shows "(\<exists>g. g ` B \<subseteq> C \<and> ext_eq_on A h (g \<circ> f)) \<longleftrightarrow> (\<forall>a \<in> A. \<forall>a' \<in> A. f a = f a' \<longrightarrow> h a = h a')"
proof (rule iffI)
  assume "\<exists>g. g ` B \<subseteq> C \<and> ext_eq_on A h (g \<circ> f)"
  then obtain g where "g ` B \<subseteq> C" and *: "ext_eq_on A h (g \<circ> f)" by auto
  {
    fix a and a'
    assume "a \<in> A" and
      "a' \<in> A" and
      "f a = f a'"
    with * have "h a = h a'" by (rule problem_1_5_14')
  }
  thus "\<forall>a \<in> A. \<forall>a' \<in> A. f a = f a' \<longrightarrow> h a = h a'" by blast
next
  assume *: "\<forall>a \<in> A. \<forall>a' \<in> A. f a = f a' \<longrightarrow> h a = h a'"
  {
    fix a and a'
    assume "a \<in> A" and
      "a' \<in> A" and
      "f a = f a'"
    with * have "h a = h a'" by blast
  }
  with assms obtain g where "g ` B \<subseteq> C" and "ext_eq_on A h (g \<circ> f)" by (elim problem_1_5_14'')
  thus "\<exists>g. g ` B \<subseteq> C \<and> ext_eq_on A h (g \<circ> f)" by auto
qed

proposition problem_1_5_15:
  assumes "A' \<noteq> {}" and -- {* This assumption is not specified in the book. However, there exists
                              a counterexample without it. *}
    "u ` A' \<subseteq> A" and
    "v ` B \<subseteq> B'"
  defines Phi: "\<Phi> f a' \<equiv> if a' \<in> A' then v (f (u a')) else undefined"
  shows "u ` A' = A \<longrightarrow> inj_on v B \<longrightarrow> inj_on \<Phi> (A \<rightarrow>\<^sub>E B)" (is ?thesis1) and
    "inj_on u A' \<longrightarrow> v ` B = B' \<longrightarrow> \<Phi> ` (A \<rightarrow>\<^sub>E B) = (A' \<rightarrow>\<^sub>E B')" (is ?thesis2)
proof -
  {
    assume "u ` A' = A" and
      "inj_on v B"
    {
      fix f and f'
      assume "f \<in> A \<rightarrow>\<^sub>E B" and
        "f' \<in> A \<rightarrow>\<^sub>E B" and
        "\<Phi> f = \<Phi> f'"
      {
        fix a
        assume "a \<in> A"
        with \<open>u ` A' = A\<close> obtain a' where "a' \<in> A'" and "a = u a'" by auto
        from \<open>a = u a'\<close> have "v (f a) = v (f (u a'))" by simp
        also from \<open>a' \<in> A'\<close> have "\<dots> = \<Phi> f a'" by (simp add: Phi)
        also from \<open>\<Phi> f = \<Phi> f'\<close> have "\<dots> = \<Phi> f' a'" by simp
        also from \<open>a' \<in> A'\<close> have "\<dots> = v (f' (u a'))" by (simp add: Phi)
        also from \<open>a = u a'\<close> have "\<dots> = v (f' a)" by simp
        finally have "v (f a) = v (f' a)" .
        moreover from \<open>a \<in> A\<close> and \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> have "f a \<in> B" by (elim PiE_D1)
        moreover from \<open>a \<in> A\<close> and \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> have "f' a \<in> B" by (elim PiE_D1)
        moreover note \<open>inj_on v B\<close>
        ultimately have "f a = f' a" by (elim inj_onD)
      }
      with \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> and \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> have "f = f'" by (intro PiE_eqI)
    }
    hence "inj_on \<Phi> (A \<rightarrow>\<^sub>E B)" by (intro inj_onI)
  }
  thus "?thesis1" by simp
  {
    assume "inj_on u A'" and
      "v ` B = B'"
    {
      fix f
      assume "f \<in> A \<rightarrow>\<^sub>E B"
      {
        fix a'
        assume "a' \<in> A'"
        with assms(2) have "u a' \<in> A" by auto
        with \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> have "f (u a') \<in> B" by auto
        with assms(3) have "v (f (u a')) \<in> B'" by auto
        with \<open>a' \<in> A'\<close> have "\<Phi> f a' \<in> B'" by (simp add: Phi)
      }
      moreover {
        fix a'
        assume "a' \<notin> A'"
        hence "\<Phi> f a' = undefined" by (simp add: Phi)
      }
      ultimately have "\<Phi> f \<in> A' \<rightarrow>\<^sub>E B'" by (intro PiE_I)
    }
    moreover {
      fix f'
      assume "f' \<in> A' \<rightarrow>\<^sub>E B'"
      have "\<exists>f \<in> A \<rightarrow>\<^sub>E B. \<Phi> f = f'" sorry
    }
    ultimately have "\<Phi> ` (A \<rightarrow>\<^sub>E B) = A' \<rightarrow>\<^sub>E B'" by (intro surj_onI)
  }
  thus "?thesis2" by blast
qed

end
