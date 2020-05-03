theory Section_2_3
  imports Main
    "HOL-Library.Disjoint_Sets"
    "HOL-Cardinals.Cardinal_Arithmetic"
    "Section_2_2"
begin

proposition csum_definition:
  fixes A :: "'a set"
    and B :: "'b set"
  shows "|A| +c |B| = |A <+> B|"
  by (simp add: csum_def)

proposition csum_welldefinedness:
  assumes "|A| =o |A'|"
    and "|B| =o |B'|"
  shows "|A| +c |B| =o |A'| +c |B'|"
proof -
  from assms(1) obtain f where f: "bij_betw f A A'" by auto
  hence "inj_on f A" and "f ` A = A'" by auto
  from assms(2) obtain g where g: "bij_betw g B B'" by auto
  hence "inj_on g B" and "g ` B = B'" by auto
  define h where "h \<equiv> map_sum f g"
  have "bij_betw h (A <+> B) (A' <+> B')"
  proof (rule bij_betw_imageI)
    show "inj_on h (A <+> B)"
    proof (rule inj_onI)
      fix x and x'
      assume x: "x \<in> A <+> B"
        and x': "x' \<in> A <+> B"
        and h: "h x = h x'"
      from x and x' consider (A) "x \<in> Inl ` A" and "x' \<in> Inl ` A"
        | (B) "x \<in> Inl ` A" and "x' \<in> Inr ` B"
        | (C) "x \<in> Inr ` B" and "x' \<in> Inl ` A"
        | (D) "x \<in> Inr ` B" and "x' \<in> Inr ` B"
        by blast
      thus "x = x'"
      proof cases
        case A
        then obtain a and a' where
          "a \<in> A"
          and "Inl a = x"
          and "a' \<in> A"
          and "Inl a' = x'" by auto
        with h_def have "h x = Inl (f a)" and "h x' = Inl (f a')" by auto
        with h have "f a = f a'" by simp
        with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and \<open>inj_on f A\<close> have "a = a'" by (elim inj_onD)
        with \<open>Inl a = x\<close> and \<open>Inl a' = x'\<close> show ?thesis by simp
      next
        case B
        with h_def and h have "False" by auto
        thus "?thesis" ..
      next
        case C
        with h_def and h have "False" by auto
        thus "?thesis" ..
      next
        case D
        then obtain b and b' where
          "b \<in> B"
          and "Inr b = x"
          and "b' \<in> B"
          and "Inr b' = x'" by auto
        with h_def have "h x = Inr (g b)" and "h x' = Inr (g b')" by auto
        with h have "g b = g b'" by simp
        with \<open>b \<in> B\<close> and \<open>b' \<in> B\<close> and \<open>inj_on g B\<close> have "b = b'" by (elim inj_onD)
        with \<open>Inr b = x\<close> and \<open>Inr b' = x'\<close> show ?thesis by simp
      qed
    qed
  next
    show "h ` (A <+> B) = A' <+> B'"
    proof (rule surj_onI)
      fix x
      assume "x \<in> A <+> B"
      with h_def and \<open>f ` A = A'\<close> and \<open>g ` B = B'\<close> show "h x \<in> A' <+> B'" by auto
    next
      fix x'
      assume "x' \<in> A' <+> B'"
      then consider (A) "x' \<in> Inl ` A'"
        | (B) "x' \<in> Inr ` B'" by auto
      thus "x' \<in> h ` (A <+> B)"
      proof cases
        case A
        then obtain a' where "a' \<in> A'" and "Inl a' = x'" by blast
        from \<open>a' \<in> A'\<close> and \<open>f ` A = A'\<close> obtain a where "a \<in> A" and "f a = a'" by auto
        with \<open>Inl a' = x'\<close> and h_def have "x' = h (Inl a)" by simp
        with \<open>a \<in> A\<close> show ?thesis by auto
      next
        case B
        then obtain b' where "b' \<in> B'" and "Inr b' = x'" by blast
        from \<open>b' \<in> B'\<close> and \<open>g ` B = B'\<close> obtain b where "b \<in> B" and "g b = b'" by auto
        with \<open>Inr b' = x'\<close> and h_def have "x' = h (Inr b)" by simp
        with \<open>b \<in> B\<close> show ?thesis by auto
      qed
    qed
  qed
  hence "|A <+> B| =o |A' <+> B'|" by auto
  thus ?thesis unfolding csum_definition by simp
qed

lemmas csum_cong' = csum_welldefinedness

lemma csum_cong1':
  assumes "|A| =o |A'|"
  shows "|A| +c |B| =o |A'| +c |B|"
proof -
  have "|B| =o |B|" by simp
  with assms show "?thesis" by (intro csum_cong')
qed

lemma csum_cong2':
  assumes "|B| =o |B'|"
  shows "|A| +c |B| =o |A| +c |B'|"
proof -
  have "|A| =o |A|" by simp
  with assms show "?thesis" by (intro csum_cong')
qed

primrec sum_swap where
  "sum_swap (Inl a) = Inr a"
| "sum_swap (Inr b) = Inl b"

lemma inj_on_sum_swap:
  shows "inj_on sum_swap (A <+> B)"
  unfolding inj_on_def by auto

lemma sum_swap_surj_on:
  shows "sum_swap ` (A <+> B) = B <+> A"
  unfolding sum_swap_def by force

lemma bij_betw_sum_swap:
  shows "bij_betw sum_swap (A <+> B) (B <+> A)"
  using inj_on_sum_swap sum_swap_surj_on by (intro bij_betw_imageI)

proposition prop_2_3_1:
  shows "|A| +c |B| =o |B| +c |A|"
proof -
  from bij_betw_sum_swap have "|A <+> B| =o |B <+> A|" by auto
  thus ?thesis unfolding csum_definition by simp
qed

fun sum_rotate :: "('a + 'b) + 'c \<Rightarrow> 'a + ('b + 'c)" where
  "sum_rotate (Inl (Inl a)) = Inl a"
| "sum_rotate (Inl (Inr b)) = Inr (Inl b)"
| "sum_rotate (Inr c) = Inr (Inr c)"

lemma inj_on_sum_rotate:
  shows "inj_on sum_rotate ((A <+> B) <+> C)"
  unfolding inj_on_def by auto

lemma sum_rotate_surj_on:
  shows "sum_rotate ` ((A <+> B) <+> C) = A <+> (B <+> C)"
  by force

lemma bij_betw_sum_rotate:
  shows "bij_betw sum_rotate ((A <+> B) <+> C) (A <+> (B <+> C))"
  using inj_on_sum_rotate and sum_rotate_surj_on by (intro bij_betw_imageI)

proposition prop_2_3_2:
  shows "( |A| +c |B| ) +c |C| =o |A| +c ( |B| +c |C| )"
proof -
  from bij_betw_sum_rotate have "|(A <+> B) <+> C| =o |A <+> (B <+> C)|" by auto
  thus ?thesis unfolding csum_definition by simp
qed

proposition prop_2_3_3:
  fixes A :: "'a set"
  shows "|A| +c czero =o |A|"
proof -
  have "|A| +c czero = |A| +c |{}|" unfolding czero_def ..
  moreover have "|A| +c |{}| = |A <+> {}|" unfolding csum_definition ..
  moreover have "|A <+> {}| =o |A|"
  proof (rule card_eqI)
    have "inj_on Inl A" by simp
    moreover have "Inl ` A = A <+> {}" by auto
    ultimately have "bij_betw Inl A (A <+> {})" by (intro bij_betw_imageI)
    thus "bij_betw (the_inv_into A Inl) (A <+> {}) A" by (intro bij_betw_the_inv_into)
  qed
  ultimately show ?thesis by metis
qed

proposition prop_2_3_4:
  assumes "|A| \<le>o |A'|"
    and "|B| \<le>o |B'|"
  shows "|A| +c |B| \<le>o |A'| +c |B'|"
proof -
  from assms(1) obtain f where f0: "f ` A \<subseteq> A'" and f1: "inj_on f A" ..
  from assms(2) obtain g where g0: "g ` B \<subseteq> B'" and g1: "inj_on g B" ..
  define h where "h \<equiv> map_sum f g"
  have "|A| +c |B| = |A <+> B|" by (fact csum_definition)
  also have "|A <+> B| \<le>o |A' <+> B'|"
  proof (rule card_leqI)
    show "h ` (A <+> B) \<subseteq> A' <+> B'"
    proof (rule image_subsetI)
      fix x
      assume "x \<in> A <+> B"
      then consider a where "a \<in> A" and "x = Inl a"
        | b where "b \<in> B" and "x = Inr b" by auto
      note this[where thesis = "h x \<in> A' <+> B'"]
      thus "h x \<in> A' <+> B'" using f0 and g0 and h_def by auto
    qed
    moreover show "inj_on h (A <+> B)"
    proof (intro inj_onI)
      fix x y
      assume "x \<in> A <+> B"
        and "y \<in> A <+> B"
        and "h x = h y"
      from this(1,2) consider
        (A)a and s where "a \<in> A" and "x = Inl a" and "s \<in> A" and "y = Inl s"
        | (B) a and b where "a \<in> A" and "x = Inl a" and "b \<in> B" and "y = Inr b"
        | (C) b and a where "b \<in> B" and "x = Inr b" and "a \<in> A" and "y = Inl a"
        | (D) b and t where "b \<in> B" and "x = Inr b" and "t \<in> B" and "y = Inr t" by auto
      thus "x = y"
      proof cases
        case A
        from \<open>x = Inl a\<close> and \<open>y = Inl s\<close> have "h x = Inl (f a)" and "h y = Inl (f s)"
          unfolding h_def by simp+
        with \<open>h x = h y\<close> have "f a = f s" by simp
        with \<open>a \<in> A\<close> and \<open>s \<in> A\<close> and f1 have "a = s" by (elim inj_onD)
        with \<open>x = Inl a\<close> and \<open>y = Inl s\<close> show ?thesis by simp
      next
        case B
        from \<open>x = Inl a\<close> and \<open>y = Inr b\<close> have "h x = Inl (f a)" and "h y = Inr (g b)"
          unfolding h_def by simp+
        with \<open>h x = h y\<close> have "False" by simp
        thus ?thesis ..
      next
        case C
        from \<open>x = Inr b\<close> and \<open>y = Inl a\<close> have "h x = Inr (g b)" and "h y = Inl (f a)"
          unfolding h_def by simp+
        with \<open>h x = h y\<close> have "False" unfolding h_def by simp
        thus ?thesis ..
      next
        case D
        from \<open>x = Inr b\<close> and \<open>y = Inr t\<close> have "h x = Inr (g b)" and "h y = Inr (g t)"
          unfolding h_def by simp+
        with \<open>h x = h y\<close> have "g b = g t" by simp
        with \<open>b \<in> B\<close> and \<open>t \<in> B\<close> and g1 have "b = t" by (elim inj_onD)
        with \<open>x = Inr b\<close> and \<open>y = Inr t\<close> show ?thesis by simp
      qed
    qed
  qed
  also have "|A' <+> B'| = |A'| +c |B'|" unfolding csum_definition by simp
  finally show ?thesis .
qed

proposition cprod_definition:
  shows "|A| *c |B| = |A \<times> B|"
  by (simp add: cprod_def)

lemma cprod_welldefinedness:
  assumes "|A| =o |A'|"
    and "|B| =o |B'|"
  shows "|A| *c |B| =o |A'| *c |B'|"
proof -
  from assms(1) obtain f where f: "bij_betw f A A'" by auto
  from f have f_inj: "inj_on f A" and f_surj: "f ` A = A'" by auto
  from assms(2) obtain g where g: "bij_betw g B B'" by auto
  from g have g_inj: "inj_on g B" and g_surj: "g ` B = B'" by auto
  define h where "h \<equiv> map_prod f g"
  from f_inj and g_inj and h_def have "inj_on h (A \<times> B)" by (auto intro: map_prod_inj_on)
  moreover from f_surj and g_surj and h_def have "h ` (A \<times> B) = A' \<times> B'" by auto
  ultimately have "bij_betw h (A \<times> B) (A' \<times> B')" by (rule bij_betw_imageI)
  hence "|A \<times> B| =o |A' \<times> B'|" by auto
  thus ?thesis unfolding cprod_definition by simp
qed

lemmas cprod_cong' = cprod_welldefinedness

lemma cprod_cong1':
  assumes "|A| =o |A'|"
  shows "|A| *c |B| =o |A'| *c |B|"
proof -
  have "|B| =o |B|" by simp
  with assms show ?thesis by (intro cprod_cong)
qed

lemma cprod_cong2':
  assumes "|B| =o |B'|"
  shows "|A| *c |B| =o |A| *c |B'|"
proof -
  have "|A| =o |A|" by simp
  with assms show ?thesis by (intro cprod_cong)
qed

proposition prop_2_3_5:
  shows "|A| *c |B| =o |B| *c |A|"
proof -
  have "|A \<times> B| =o |B \<times> A|" by (fact Times_card_commute)
  thus ?thesis unfolding cprod_definition by simp
qed

fun prod_rotate where
  "prod_rotate ((a, b), c) = (a, (b, c))"

lemma inj_on_prod_rotate:
  shows "inj_on prod_rotate ((A \<times> B) \<times> C)"
  unfolding inj_on_def by force

lemma prod_rotate_surj_on:
  shows "prod_rotate ` ((A \<times> B) \<times> C) = (A \<times> (B \<times> C))"
  by force

lemma bij_betw_prod_rotate:
  shows "bij_betw prod_rotate ((A \<times> B) \<times> C) (A \<times> (B \<times> C))"
  using inj_on_prod_rotate and prod_rotate_surj_on by (intro bij_betw_imageI)

proposition prop_2_3_6:
  shows "( |A| *c |B| ) *c |C| =o |A| *c ( |B| *c |C| )"
proof -
  from bij_betw_prod_rotate have "|(A \<times> B) \<times> C| =o |A \<times> (B \<times> C)|" by auto
  thus ?thesis unfolding cprod_definition by simp
qed

proposition prop_2_3_7_a:
  fixes A :: "'a set"
  shows "|A| *c (czero :: 'b rel) =o (czero :: 'c rel)"
proof -
  have "czero = |{} :: 'b set|" by (fact czero_def)
  hence "|A| *c (czero :: 'b rel) = |A| *c |{} :: 'b set|" by simp
  moreover have "|A| *c |{} :: 'b set| = |A \<times> {}|" unfolding cprod_definition ..
  moreover have "|A \<times> ({} :: 'b set)| = |{} :: ('a \<times> 'b) set|" by simp
  moreover have "|{} :: ('a \<times> 'b) set| = (czero :: ('a \<times> 'b) rel)"
    unfolding czero_definition by simp
  moreover have "(czero :: ('a \<times> 'b) rel) =o (czero :: 'c rel)" by (fact czero_refl)
  ultimately show ?thesis by simp
qed

lemma empty_cprod_card_eq_czero:
  fixes A :: "'a set"
  shows "(czero :: 'b rel) *c |A| =o (czero :: 'c rel)"
proof -
  have "(czero :: 'b rel) *c |A| = |{} :: 'b set| *c |A|" unfolding czero_definition ..
  moreover have "|{} :: 'b set| *c |A| = |{} \<times> A|" by (fact cprod_definition)
  moreover have "|{} \<times> A| = |{}|" by simp
  moreover have "|{}| =o (czero :: 'c rel)" by (fact empty_card_eq_czero)
  ultimately show ?thesis by simp
qed

lemma cprod_empty_card_eq_czero:
  fixes A :: "'a set"
  shows "|A| *c (czero :: 'b rel) =o (czero :: 'c rel)"
proof -
  have "|A| *c (czero :: 'b rel) = |A| *c |{} :: 'b set|" unfolding czero_definition ..
  moreover have "|A| *c |{} :: 'b set| =o |{} :: 'b set| *c |A|" by (fact prop_2_3_5)
  moreover have "|{} :: 'b set| *c |A| = (czero :: 'b rel) *c |A|" unfolding czero_definition ..
  moreover have "(czero :: 'b rel) *c |A| =o (czero :: 'c rel)" by (fact empty_cprod_card_eq_czero)
  ultimately show ?thesis by (intro prop_2_3_7_a)
qed

lemma empty_imp_cprod_card_eq_czero1:
  fixes A :: "'a set"
    and B:: "'b set"
  assumes "A = {}"
  shows "|A| *c |B| =o (czero :: 'c rel)"
proof -
  from assms have "|A| =o czero" by (fact eq_empty_imp_card_eq_czero)
  have "|A| *c |B| = |A \<times> B|" unfolding cprod_definition ..
  moreover from assms(1) have "|A \<times> B| = |{}|" by simp
  moreover have "|{} :: ('a \<times> 'b) set| =o (czero :: 'c rel)" try sorry
  ultimately show ?thesis by simp
qed

lemma empty_imp_cprod_card_eq_czero2:
  fixes A :: "'a set"
    and B :: "'b set"
  assumes "B = {}"
  shows "|A| *c |B| =o (czero :: 'c rel)"
proof -
  from assms have "|A| *c |B| = |A| *c |{}|" by simp
  moreover have "|A| *c |{}| = |A| *c czero" unfolding czero_definition ..
  moreover have "|A| *c czero =o (czero :: 'c rel)" by (fact prop_2_3_7_a)
  ultimately show ?thesis by metis
qed

(*lemma czero_cprod_absorb2_sym:
  shows "czero =o |A| *c czero"
  using prop_2_3_7_a by (auto intro: ordIso_symmetric)

lemma czero_cprod_cong2:
  fixes A :: "'a set"
    and B :: "'b set"
  assumes "B = {}"
  shows "|A| *c (czero :: 'd rel) =o |A| *c |B|"
  sorry*)

lemma inj_on_fst_Times_unit:
  shows "inj_on fst (A \<times> {()})"
  unfolding inj_on_def by simp

lemma fst_surj_on_Times_unit:
  shows "fst ` (A \<times> {()}) = A"
  by simp

lemma bij_betw_fst_Times_unit:
  shows "bij_betw fst (A \<times> {()}) A"
  using inj_on_fst_Times_unit and fst_surj_on_Times_unit by (intro bij_betw_imageI)

proposition prop_2_3_7_b:
  shows "|A| *c cone =o |A|"
proof -
  have "|A| *c cone = |A| *c |{()}|" unfolding cone_def ..
  moreover have "|A| *c |{()}| = |A \<times> {()}|" unfolding cprod_definition ..
  moreover from bij_betw_fst_Times_unit have "|A \<times> {()}| =o |A|" by auto
  ultimately show ?thesis by simp
qed

proposition prop_2_3_8:
  assumes "|A| \<le>o |B|"
    and "|A'| \<le>o |B'|"
  shows "|A| *c |A'| \<le>o |B| *c |B'|"
proof -
  from assms(1) obtain f where "f ` A \<subseteq> B" and "inj_on f A" by auto
  from assms(2) obtain g where "g ` A' \<subseteq> B'" and "inj_on g A'" by auto
  define h where "h \<equiv> map_prod f g"
  from \<open>inj_on f A\<close> and \<open>inj_on g A'\<close> and h_def have "inj_on h (A \<times> A')"
    by (auto intro: map_prod_inj_on)
  moreover from \<open>f ` A \<subseteq> B\<close> and \<open>g ` A' \<subseteq> B'\<close> and h_def have "h ` (A \<times> A') \<subseteq> B \<times> B'" by auto
  ultimately have "|A \<times> A'| \<le>o |B \<times> B'|" by auto
  thus ?thesis unfolding cprod_definition by simp
qed

fun prod_sum_distribute where
  "prod_sum_distribute (a, Inl b) = Inl (a, b)"
| "prod_sum_distribute (a, Inr c) = Inr (a, c)"

lemma inj_on_prod_sum_distribute:
  shows "inj_on prod_sum_distribute (A \<times> (B <+> C))"
  unfolding inj_on_def by fastforce

lemma prod_sum_distribute_surj_on:
  shows "prod_sum_distribute ` (A \<times> (B <+> C)) = A \<times> B <+> A \<times> C"
  by force

lemma bij_betw_prod_sum_distribute:
  shows "bij_betw prod_sum_distribute (A \<times> (B <+> C)) (A \<times> B <+> A \<times> C)"
  using inj_on_prod_sum_distribute and prod_sum_distribute_surj_on by (intro bij_betw_imageI)

proposition prop_2_3_9:
  shows "|A| *c ( |B| +c |C| ) =o |A| *c |B| +c |A| *c |C|"
proof -
  from bij_betw_prod_sum_distribute have "|A \<times> (B <+> C)| =o |A \<times> B <+> A \<times> C|" by auto
  thus ?thesis unfolding csum_definition and cprod_definition by simp
qed

theorem thm_2_9:
  fixes A :: "'b \<Rightarrow> 'a set"
  assumes "|\<Lambda>| = \<nn>"
    and "\<And>l. l \<in> \<Lambda> \<Longrightarrow> |A l| =o \<mm>"
    and "\<Lambda> = {} \<Longrightarrow> \<exists>X. |X| = \<mm>" -- \<open>This assumption guarantees that @{term "\<mm>"} is a cardinal
                                      number even if @{prop "\<Lambda> = {}"}.\<close>
    and "disjoint_family_on A \<Lambda>"
  shows "|\<Union>l \<in> \<Lambda>. A l| =o \<mm> *c \<nn>"
proof -
  let ?B = "\<Union>l \<in> \<Lambda>. A l"
  {
    assume "\<Lambda> = {}"
    have "|?B| =o |{} :: 'c set|"
    proof -
      from \<open>\<Lambda> = {}\<close> have "?B = {}" by simp
      hence "|?B| = |{}|" by simp
      also have "|{} :: 'a set| =o |{} :: 'c set|" by (fact empty_card_eq_empty)
      finally show ?thesis .
    qed
    also have "|{} :: 'c set| =o \<mm> *c \<nn>"
    proof -
      from \<open>\<Lambda> = {}\<close> obtain X where "|X| = \<mm>" by (auto dest: assms(3))
      from \<open>\<Lambda> = {}\<close> have "|X \<times> \<Lambda>| = |{}|" by simp
      also have "\<dots> =o |{} :: 'c set|" by (fact empty_card_eq_empty)
      finally have "|X \<times> \<Lambda>| =o |{} :: 'c set|" .
      hence "|{} :: 'c set| =o |X \<times> \<Lambda>|" by auto
      also have "|X \<times> \<Lambda>| = |X| *c |\<Lambda>|" unfolding cprod_definition ..
      also from \<open>|X| = \<mm>\<close> and \<open>|\<Lambda>| = \<nn>\<close> have "\<dots> = \<mm> *c \<nn>" by simp
      finally show ?thesis .
    qed
    finally have "|?B| =o \<mm> *c \<nn>" .
  }
  moreover {
    assume "\<Lambda> \<noteq> {}"
    then obtain l\<^sub>0 where "l\<^sub>0 \<in> \<Lambda>" by auto
    hence "|A l\<^sub>0| =o \<mm>" by (auto dest: assms(2))
    {
      fix l
      assume "l \<in> \<Lambda>"
      hence "|A l| =o \<mm>" by (auto dest: assms(2))
      also from \<open>|A l\<^sub>0| =o \<mm>\<close> have "\<mm> =o |A l\<^sub>0|" by (fact ordIso_symmetric)
      finally have "|A l| =o |A l\<^sub>0|" .
      hence "\<exists>f. bij_betw f (A l) (A l\<^sub>0)" by auto
      hence "\<exists>f. bij_betw f (A l\<^sub>0) (A l)" by (auto dest: bij_betw_inv)
    }
    then obtain f where f: "f \<in> (\<Pi> l \<in> \<Lambda>. {f. bij_betw f (A l\<^sub>0) (A l)})" by (elim AC_E_ex)
    hence fl: "bij_betw (f l) (A l\<^sub>0) (A l)" if "l \<in> \<Lambda>" for l using that by auto
    let ?f' = "\<lambda>(a, l). f l a"
    have "?f' ` (A l\<^sub>0 \<times> \<Lambda>) = ?B"
    proof (rule surj_onI; split_pair)
      fix a and l
      assume "(a, l) \<in> A l\<^sub>0 \<times> \<Lambda>"
      hence "a \<in> A l\<^sub>0" and "l \<in> \<Lambda>" by simp+
      from this(2) and fl have "bij_betw (f l) (A l\<^sub>0) (A l)" by simp
      with \<open>a \<in> A l\<^sub>0\<close> have "f l a \<in> A l" by auto
      with \<open>l \<in> \<Lambda>\<close> show "f l a \<in> ?B" by auto
    next
      fix b
      assume "b \<in> ?B"
      then obtain l where "l \<in> \<Lambda>" and "b \<in> A l" by auto
      with fl obtain a where "a \<in> A l\<^sub>0" and "b = f l a" by blast
      with \<open>l \<in> \<Lambda>\<close> show "b \<in> ?f' ` (A l\<^sub>0 \<times> \<Lambda>)" by auto
    qed
    moreover have "inj_on ?f' (A l\<^sub>0 \<times> \<Lambda>)"
    proof (rule inj_onI; split_pair)
      fix a l a' l'
      assume "(a, l) \<in> A l\<^sub>0 \<times> \<Lambda>"
        and "(a', l') \<in> A l\<^sub>0 \<times> \<Lambda>"
        and "f l a = f l' a'"
      from this(1,2) have "a \<in> A l\<^sub>0" and "l \<in> \<Lambda>" and "a' \<in> A l\<^sub>0" and "l' \<in> \<Lambda>" by auto
      with fl have "f l a \<in> A l" and "f l' a' \<in> A l'" by auto
      with \<open>f l a = f l' a'\<close> have "A l \<inter> A l' \<noteq> {}" by auto
      {
        assume "l \<noteq> l'"
        with \<open>l \<in> \<Lambda>\<close> and \<open>l' \<in> \<Lambda>\<close> and assms(4) have "A l \<inter> A l' = {}"
          by (elim disjoint_family_onD)
        with \<open>A l \<inter> A l' \<noteq> {}\<close> have "False" ..
      }
      hence "l = l'" by auto
      with \<open>f l a = f l' a'\<close> have "f l a = f l a'" by simp
      moreover from \<open>l \<in> \<Lambda>\<close> and fl have "inj_on (f l) (A l\<^sub>0)" by auto
      moreover note \<open>a \<in> A l\<^sub>0\<close> and \<open>a' \<in> A l\<^sub>0\<close>
      ultimately have "a = a'" by (elim inj_onD)
      with \<open>l = l'\<close> show "(a, l) = (a', l')" by simp
    qed
    ultimately have "bij_betw ?f' (A l\<^sub>0 \<times> \<Lambda>) ?B" by (intro bij_betw_imageI)
    hence "|A l\<^sub>0 \<times> \<Lambda>| =o |?B|" by auto
    hence "|?B| =o |A l\<^sub>0 \<times> \<Lambda>|" by (fact ordIso_symmetric)
    also have "|A l\<^sub>0 \<times> \<Lambda>| =o |A l\<^sub>0| *c |\<Lambda>|" by (fact Times_cprod)
    also have "|A l\<^sub>0| *c |\<Lambda>| =o \<mm> *c |\<Lambda>|"
    proof -
      from \<open>l\<^sub>0 \<in> \<Lambda>\<close> have "|A l\<^sub>0| =o \<mm>" by (fact assms(2))
      thus "?thesis" by (fact cprod_cong1)
    qed
    finally have "|?B| =o \<mm> *c |\<Lambda>|" .
    with assms(1) have "|?B| =o \<mm> *c \<nn>" by simp
  }
  ultimately show "?thesis" by blast
qed

proposition cexp_definition:
  shows "|A| ^c |B| = |B \<rightarrow>\<^sub>E A|"
proof -
  have "|A| ^c |B| = |Func B A|" unfolding cexp_def by simp
  also have "\<dots> = |B \<rightarrow>\<^sub>E A|"
  proof -
    have "Func B A = B \<rightarrow>\<^sub>E A" unfolding Func_def by auto
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma bij_betw_imp_id_on_comp:
  assumes "bij_betw f A B"
  obtains g where "id_on (g \<circ> f) A"
    and "id_on (f \<circ> g) B"
proof -
  have "id_on ((the_inv_into A f) \<circ> f) A"
  proof (rule id_onI)
    fix a
    assume "a \<in> A"
    moreover from assms have "inj_on f A" ..
    ultimately have "(the_inv_into A f) (f a) = a" by (intro the_inv_into_f_f)
    thus "((the_inv_into A f) \<circ> f) a = a" by simp
  qed
  moreover have "id_on (f \<circ> (the_inv_into A f)) B"
  proof (rule id_onI)
    fix b
    assume "b \<in> B"
    with assms have "f ((the_inv_into A f) b) = b" by (intro f_the_inv_into_f_bij_betw)
    thus "(f \<circ> (the_inv_into A f)) b = b" by simp
  qed
  moreover note that
  ultimately show thesis by simp
qed

lemma cexp_cong':
  assumes "|A| =o |A'|"
    and "|B| =o |B'|"
  shows "|B| ^c |A| =o |B'| ^c |A'|" (is "?LHS =o ?RHS")
proof -
  from assms(1) obtain u where "bij_betw u A' A" by auto
  hence u1: "u ` A' = A" and u2: "inj_on u A'" by auto
  from assms(2) obtain v where v: "bij_betw v B B'" by auto
  hence v1: "v ` B = B'" and v2: "inj_on v B" by auto
  define \<Phi> where "\<Phi> f a' \<equiv> if a' \<in> A' then v (f (u a')) else undefined" for f a'
  from u1 and v2 have \<Phi>1: "inj_on \<Phi> (A \<rightarrow>\<^sub>E B)" unfolding \<Phi>_def by (rule prob_1_5_15_ext_a)
  from assms(1) have "A' = {} \<Longrightarrow> A = {}" by auto
  moreover from u1 have "u ` A' \<subseteq> A" by simp
  moreover note u2 and v1
  ultimately have "\<Phi> ` (A \<rightarrow>\<^sub>E B) = (A' \<rightarrow>\<^sub>E B')" unfolding \<Phi>_def by (rule prob_1_5_15_ext_b)
  with \<Phi>1 have \<Phi>3: "bij_betw \<Phi> (A \<rightarrow>\<^sub>E B) (A' \<rightarrow>\<^sub>E B')" by (rule bij_betw_imageI)
  have "?LHS =o |A \<rightarrow>\<^sub>E B|" unfolding cexp_definition by simp
  also from \<Phi>3 have "|A \<rightarrow>\<^sub>E B| =o |A' \<rightarrow>\<^sub>E B'|" by auto
  also have "|A' \<rightarrow>\<^sub>E B'| =o ?RHS" unfolding cexp_definition by simp
  finally show "?LHS =o ?RHS" .
qed

lemma cexp_cong1':
  assumes "|M| =o |N|"
  shows "|M| ^c |P| =o |N| ^c |P|"
  by (rule cexp_cong', simp, fact assms)

lemma cexp_cong2':
  assumes "|P| =o |Q|"
  shows "|M| ^c |P| =o |M| ^c |Q|"
  by (rule cexp_cong', fact assms, simp)

proposition prop_2_3_10_a:
  fixes A :: "'a set"
    and x :: 'x
  shows "|A| ^c |{x}| =o |A|"
proof -
  define \<FF> :: "('x \<Rightarrow> 'a) \<Rightarrow> 'a" where "\<FF> f \<equiv> f x" for f
  have "\<FF> ` ({x} \<rightarrow>\<^sub>E A) = A"
  proof (rule surj_onI)
    fix f
    assume "f \<in> {x} \<rightarrow>\<^sub>E A"
    with \<FF>_def show "\<FF> f \<in> A" by auto
  next
    fix a
    assume a: "a \<in> A"
    define f where "f t \<equiv> if t = x then a else undefined" for t
    have "f \<in> {x} \<rightarrow>\<^sub>E A"
    proof (rule PiE_I)
      fix t
      assume "t \<in> {x}"
      with f_def and a show "f t \<in> A" by simp
    next
      fix t
      assume "t \<notin> {x}"
      with f_def show "f t = undefined" by simp
    qed
    moreover from f_def and \<FF>_def have "\<FF> f = a" by simp
    ultimately show "a \<in> \<FF> ` ({x} \<rightarrow>\<^sub>E A)" by auto
  qed
  moreover have "inj_on \<FF> ({x} \<rightarrow>\<^sub>E A)"
  proof (rule inj_onI)
    fix f g
    assume f0: "f \<in> {x} \<rightarrow>\<^sub>E A"
      and g0: "g \<in> {x} \<rightarrow>\<^sub>E A"
      and "\<FF> f = \<FF> g"
    from this(3) and \<FF>_def have "f x = g x" by simp
    show "f = g"
    proof (rule ext)
      fix t
      consider "t = x" | "t \<noteq> x" by auto
      moreover  {
        assume "t = x"
        with \<open>f x = g x\<close> have "f t = g t" by simp
      }
      moreover {
        assume "t \<noteq> x"
        with f0 and g0 have "f t = g t" by fastforce
      }
      ultimately show "f t = g t" by auto
    qed
  qed
  ultimately have \<FF>: "bij_betw \<FF> ({x} \<rightarrow>\<^sub>E A) A" by (intro bij_betw_imageI)
  have "|A| ^c |{x}| = |{x} \<rightarrow>\<^sub>E A|" by (fact cexp_definition)
  also from \<FF> have "\<dots> =o |A|" by auto
  finally show ?thesis .
qed

proposition prop_2_3_10_b:
  shows "cone ^c |A| =o cone"
proof -
  define f where "f a \<equiv> if a \<in> A then () else undefined" for a
  have "cone ^c |A| = |{()}| ^c |A|" unfolding cone_def ..
  also have "\<dots> = |A \<rightarrow>\<^sub>E {()}|" by (fact cexp_definition)
  also have "|A \<rightarrow>\<^sub>E {()}| = |{f}|"
  proof -
    have "A \<rightarrow>\<^sub>E {()} = {f}" by auto
    thus ?thesis by simp
  qed
  also have "\<dots> =o cone" by (fact singleton_card_eq_cone)
  finally show ?thesis .
qed

proposition prop_2_3_11:
  assumes "|A| \<le>o |A'|"
    and "|B| \<le>o |B'|"
    and "B = {} \<longleftrightarrow> B' = {}" -- \<open>Is this assumption necessary?\<close>
  shows "|A| ^c |B| \<le>o |A'| ^c |B'|"
proof -
  from assms(2) and assms(3)[THEN iffD1] obtain u where u: "u ` B' = B"
    by (elim card_leq_imp_surj_on)
  from assms(1) obtain v where v1: "v ` A \<subseteq> A'" and v2: "inj_on v A" by auto
  let ?\<Phi> = "\<lambda>f. v \<circ> f \<circ> u"
  let ?\<Phi>' = "\<lambda>f. \<lambda>b'. if b' \<in> B' then ?\<Phi> f b' else undefined"
  from assms(3)[THEN iffD2] u v1 v2
  have Phi_inj: "\<forall>f \<in> B \<rightarrow> A. \<forall>f' \<in> B \<rightarrow> A. ext_eq_on B' (?\<Phi> f) (?\<Phi> f') \<longrightarrow> ext_eq_on B f f'"
    by (auto intro: prob_1_5_15[where A = "B" and A' = "B'" and B = "A"])
  have "|A| ^c |B| = |B \<rightarrow>\<^sub>E A|" by (fact cexp_definition)
  also have "|B \<rightarrow>\<^sub>E A| \<le>o |B' \<rightarrow>\<^sub>E A'|"
  proof -
    have "?\<Phi>' ` (B \<rightarrow>\<^sub>E A) \<subseteq> B' \<rightarrow>\<^sub>E A'"
    proof (rule image_subsetI)
      fix f
      assume f: "f \<in> B \<rightarrow>\<^sub>E A"
      {
        fix b'
        assume "b' \<in> B'"
        with u and f and v1 have "?\<Phi>' f b' \<in> A'" by auto
      }
      moreover {
        fix b'
        assume "b' \<notin> B'"
        hence "?\<Phi>' f b' = undefined" by simp
      }
      ultimately show "?\<Phi>' f \<in> B' \<rightarrow>\<^sub>E A'" by blast
    qed
    moreover have "inj_on ?\<Phi>' (B \<rightarrow>\<^sub>E A)"
    proof (rule inj_onI)
      fix f and f'
      assume f: "f \<in> B \<rightarrow>\<^sub>E A" and f': "f' \<in> B \<rightarrow>\<^sub>E A" and "?\<Phi>' f = ?\<Phi>' f'"
      {
        fix b'
        assume "b' \<in> B'"
        with \<open>?\<Phi>' f = ?\<Phi>' f'\<close> have "?\<Phi>' f b' = ?\<Phi>' f' b'" by meson
        with \<open>b' \<in> B'\<close> have "?\<Phi> f b' = ?\<Phi> f' b'" by simp
      }
      hence "ext_eq_on B' (?\<Phi> f) (?\<Phi> f')" by blast
      with f and f' and Phi_inj have "ext_eq_on B f f'" by blast
      moreover {
        fix b
        assume "b \<notin> B"
        with f and f' have "f b = f' b" by fastforce
      }
      ultimately show "f = f'" by auto
    qed
    ultimately show "?thesis" by auto
  qed
  also have "|B' \<rightarrow>\<^sub>E A'| = |A'| ^c |B'|" unfolding cexp_definition by simp
  finally show "?thesis" .
qed

primrec map_dom_sum :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a + 'b) \<Rightarrow> 'c" where
  "map_dom_sum f g (Inl a) = f a"
| "map_dom_sum f g (Inr a) = g a"

lemma pair_neqE:
  assumes "p \<noteq> q"
  obtains "fst p \<noteq> fst q"
  | "snd p \<noteq> snd q"
proof -
  {
    assume "fst p = fst q"
      and "snd p = snd q"
    hence "p = q" by (fact prod_eqI)
    with assms have "False" ..
  }
  hence "fst p \<noteq> fst q \<or> snd p \<noteq> snd q" by auto
  thus "thesis" by (auto intro: that)
qed

theorem thm_2_10_a:
  fixes A :: "'a set"
    and B :: "'b set"
    and C :: "'c set"
  shows "|C| ^c |A| *c |C| ^c |B| =o |C| ^c ( |A| +c |B| )"
proof -
  define \<Phi> :: "('a + 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c) \<times> ('b \<Rightarrow> 'c)"
    where "\<Phi> h \<equiv> (\<lambda>a. h (Inl a), \<lambda>b. h (Inr b))" for h
  let ?f = "\<lambda>\<phi> :: 'a + 'b \<Rightarrow> 'c. (\<lambda>a. \<phi> (Inl a), \<lambda>b. \<phi> (Inr b))"
  have "|C| ^c |A| *c |C| ^c |B| = |A \<rightarrow>\<^sub>E C| *c |B \<rightarrow>\<^sub>E C|"
  proof -
    have "|C| ^c |A| = |A \<rightarrow>\<^sub>E C|" and "|C| ^c |B| = |B \<rightarrow>\<^sub>E C|" by (fact cexp_definition)+
    thus ?thesis by simp
  qed
  also have "\<dots> = |(A \<rightarrow>\<^sub>E C) \<times> (B \<rightarrow>\<^sub>E C)|" by (fact cprod_definition)
  also have "\<dots> =o |A <+> B \<rightarrow>\<^sub>E C|"
  proof -
    let ?S = "(A \<rightarrow>\<^sub>E C) \<times> (B \<rightarrow>\<^sub>E C)"
    let ?T = "A <+> B \<rightarrow>\<^sub>E C"
    let ?f = "\<lambda>x :: ('a \<Rightarrow> 'c) \<times> ('b \<Rightarrow> 'c). map_dom_sum (fst x) (snd x)"
    have "inj_on ?f ?S"
    proof (intro inj_onI)
      fix x x'
      assume "x \<in> ?S"
        and "x' \<in> ?S"
        and "map_dom_sum (fst x) (snd x) = map_dom_sum (fst x') (snd x')"
      {
        assume "x \<noteq> x'"
        moreover {
          assume "fst x \<noteq> fst x'"
          then obtain a where "fst x a \<noteq> fst x' a" by auto
          hence "map_dom_sum (fst x) (snd x) (Inl a) \<noteq> map_dom_sum (fst x') (snd x') (Inl a)"
            by simp
          with \<open>map_dom_sum (fst x) (snd x) = map_dom_sum (fst x') (snd x')\<close> have "False" by simp
        }
        moreover {
          assume "snd x \<noteq> snd x'"
          then obtain b where "snd x b \<noteq> snd x' b" by auto
          hence "map_dom_sum (fst x) (snd x) (Inr b) \<noteq> map_dom_sum (fst x') (snd x') (Inr b)"
            by simp
          with \<open>map_dom_sum (fst x) (snd x) = map_dom_sum (fst x') (snd x')\<close> have "False" by simp
        }
        ultimately have "False" by (fact pair_neqE)
      }
      thus "x = x'" by auto
    qed
    moreover have "?f ` ?S = ?T"
    proof (intro surj_onI)
      fix s
      assume "s \<in> ?S"
      {
        fix x
        assume "x \<in> A <+> B"
        moreover {
          fix a
          assume "a \<in> A"
            and "x = Inl a"
          from this(2) have "?f s x = ?f s (Inl a)" by simp
          also have "\<dots> = (fst s) a" by simp
          also have "\<dots> \<in> C"
          proof -
            from \<open>s \<in> ?S\<close> have "fst s \<in> A \<rightarrow>\<^sub>E C" by auto
            with \<open>a \<in> A\<close> show "?thesis" by auto
          qed
          finally have "?f s x \<in> C" .
        }
        moreover {
          fix b
          assume "b \<in> B"
            and "x = Inr b"
          from this(2) have "?f s x = ?f s (Inr b)" by simp
          also have "\<dots> = (snd s) b" by simp
          also have "\<dots> \<in> C"
          proof -
            from \<open>s \<in> ?S\<close> have "snd s \<in> B \<rightarrow>\<^sub>E C" by auto
            with \<open>b \<in> B\<close> show "?thesis" by auto
          qed
          finally have "?f s x \<in> C" .
        }
        ultimately have "?f s x \<in> C" by (fact PlusE)
      }
      moreover {
        fix x
        assume "x \<notin> A <+> B"
        {
          fix a
          assume "x = Inl a"
          with \<open>x \<notin> A <+> B\<close> have "a \<notin> A" by auto
          from \<open>x = Inl a\<close> have "?f s x = ?f s (Inl a)" by simp
          also have "\<dots> = (fst s) a" by simp
          also have "\<dots> = undefined"
          proof -
            from \<open>s \<in> ?S\<close> have "fst s \<in> A \<rightarrow>\<^sub>E C" by auto
            with \<open>a \<notin> A\<close> show "?thesis" by auto
          qed
          finally have "?f s x = undefined" .
        }
        moreover {
          fix b
          assume "x = Inr b"
          with \<open>x \<notin> A <+> B\<close> have "b \<notin> B" by auto
          from \<open>x = Inr b\<close> have "?f s x = ?f s (Inr b)" by simp
          also have "\<dots> = (snd s) b" by simp
          also have "\<dots> = undefined"
          proof -
            from \<open>s \<in> ?S\<close> have "snd s \<in> B \<rightarrow>\<^sub>E C" by auto
            with \<open>b \<notin> B\<close> show "?thesis" by auto
          qed
          finally have "?f s x = undefined" .
        }
        ultimately have "?f s x = undefined" by (fact sumE)
      }
      ultimately show "?f s \<in> ?T" by auto
    next
      fix t
      assume "t \<in> ?T"
      let ?g = "\<lambda>a. t (Inl a)"
      let ?h = "\<lambda>b. t (Inr b)"
      {
        fix x :: "'a + 'b"
        {
          fix a
          assume "x = Inl a"
          hence "?f (?g, ?h) x = t x" by simp
        }
        moreover {
          fix b
          assume "x = Inr b"
          hence "?f (?g, ?h) x = t x" by simp
        }
        ultimately have "?f (?g, ?h) x = t x" by (fact sumE)
      }
      hence "?f (?g, ?h) = t" by auto
      moreover have "(?g, ?h) \<in> ?S"
      proof -
        have "?g \<in> A \<rightarrow>\<^sub>E C"
        proof (intro PiE_I)
          fix a
          assume "a \<in> A"
          hence "Inl a \<in> A <+> B" by auto
          with \<open>t \<in> ?T\<close> show "?g a \<in> C" by auto
        next
          fix a
          assume "a \<notin> A"
          hence "Inl a \<notin> A <+> B" by auto
          with \<open>t \<in> ?T\<close> show "?g a = undefined" by auto
        qed
        moreover have "?h \<in> B \<rightarrow>\<^sub>E C"
        proof (intro PiE_I)
          fix b
          assume "b \<in> B"
          hence "Inr b \<in> A <+> B" by auto
          with \<open>t \<in> ?T\<close> show "?h b \<in> C" by auto
        next
          fix b
          assume "b \<notin> B"
          hence "Inr b \<notin> A <+> B" by auto
          with \<open>t \<in> ?T\<close> show "?h b = undefined" by auto
        qed
        ultimately show "?thesis" ..
      qed
      ultimately show "t \<in> ?f ` ?S" by force
    qed
    ultimately have "bij_betw ?f ((A \<rightarrow>\<^sub>E C) \<times> (B \<rightarrow>\<^sub>E C)) ( A<+> B \<rightarrow>\<^sub>E C)" by (fact bij_betw_imageI)
    thus "?thesis" by auto
  qed
  also have "|A <+> B \<rightarrow>\<^sub>E C| =o |C| ^c |A <+> B|" unfolding cexp_definition by simp
  also have "|C| ^c |A <+> B| = |C| ^c ( |A| +c |B| )" unfolding csum_definition ..
  finally show "?thesis" by simp
qed

primrec map_prod' where "map_prod' (f, g) x = (f x, g x)"

lemma map_prod'_eq1:
  assumes "map_prod' (f, g) = map_prod' (f', g')"
  shows "f = f'"
proof (rule ext)
  fix x
  from assms have "map_prod' (f, g) x = map_prod' (f', g') x" by simp
  thus "f x = f' x" by simp
qed

lemma map_prod'_eq2:
  assumes "map_prod' (f, g) = map_prod' (f', g')"
  shows "g = g'"
proof (rule ext)
  fix x
  from assms have "map_prod' (f, g) x = map_prod' (f', g') x" by simp
  thus "g x = g' x" by simp
qed

theorem thm_2_10_b:
  fixes P :: "'p set"
    and M :: "'m set"
    and N :: "'n set"
  shows "( |M| *c |N| ) ^c |P| =o |M| ^c |P| *c |N| ^c |P|"
proof -
  define \<FF> where "\<FF> h p \<equiv> if p \<in> P then map_prod' h p else undefined"
    for h :: "('p \<Rightarrow> 'm) \<times> ('p \<Rightarrow> 'n)" and p
  have "bij_betw \<FF> ((P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N)) (P \<rightarrow>\<^sub>E M \<times> N)"
  proof (rule bij_betw_imageI)
    show "inj_on \<FF> ((P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N))"
    proof (rule inj_onI, split_pair)
      fix f and g and f' and g'
      assume "(f, g) \<in> (P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N)"
        and "(f', g') \<in> (P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N)"
        and \<FF>: "\<FF> (f, g) = \<FF> (f', g')"
      hence "f \<in> P \<rightarrow>\<^sub>E M"
        and "g \<in> P \<rightarrow>\<^sub>E N"
        and "f' \<in> P \<rightarrow>\<^sub>E M"
        and "g' \<in> P \<rightarrow>\<^sub>E N" by simp_all
      have "f = f'"
      proof (rule ext)
        fix p
        {
          assume "p \<in> P"
          from \<FF> have "\<FF> (f, g) p = \<FF> (f', g') p" by simp
          with \<FF>_def and \<open>p \<in> P\<close> have "f p = f' p" by simp
        }
        moreover {
          assume "p \<notin> P"
          with \<open>f \<in> P \<rightarrow>\<^sub>E M\<close> and \<open>f' \<in> P \<rightarrow>\<^sub>E M\<close> have "f p = f' p" by fastforce
        }
        ultimately show "f p = f' p" by auto
      qed
      moreover have "g = g'"
      proof (rule ext)
        fix p
        {
          assume "p \<in> P"
          from \<FF> have "\<FF> (f, g) p = \<FF> (f', g') p" by simp
          with \<FF>_def and \<open>p \<in> P\<close> have "g p = g' p" by simp
        }
        moreover {
          assume "p \<notin> P"
          with \<open>g \<in> P \<rightarrow>\<^sub>E N\<close> and \<open>g' \<in> P \<rightarrow>\<^sub>E N\<close> have "g p = g' p" by fastforce
        }
        ultimately show "g p = g' p" by auto
      qed
      ultimately show "(f, g) = (f', g')" by simp
    qed
  next
    show "\<FF> ` ((P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N)) = P \<rightarrow>\<^sub>E M \<times> N"
    proof (rule surj_onI, split_pair)
      fix f and g
      assume "(f, g) \<in> (P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N)"
      hence "f \<in> P \<rightarrow>\<^sub>E M" and "g \<in> P \<rightarrow>\<^sub>E N" by simp_all
      show "\<FF> (f, g) \<in> P \<rightarrow>\<^sub>E M \<times> N"
      proof (rule PiE_I)
        fix p
        assume "p \<in> P"
        hence "\<FF> (f, g) p = (f p, g p)" unfolding \<FF>_def by simp
        also from \<open>p \<in> P\<close> and \<open>f \<in> P \<rightarrow>\<^sub>E M\<close> and \<open>g \<in> P \<rightarrow>\<^sub>E N\<close> have "\<dots> \<in> M \<times> N" by auto
        finally show "\<FF> (f, g) p \<in> M \<times> N" .
      next
        fix p
        assume "p \<notin> P"
        with \<FF>_def show "\<FF> (f, g) p = undefined" by simp
      qed
    next
      fix h
      assume h: "h \<in> P \<rightarrow>\<^sub>E M \<times> N"
      define f where "f p \<equiv> if p \<in> P then fst (h p) else undefined" for p
      from f_def and h have "f \<in> P \<rightarrow>\<^sub>E M" by force
      define g where "g p \<equiv> if p \<in> P then snd (h p) else undefined" for p
      from g_def and h have "g \<in> P \<rightarrow>\<^sub>E N" by force
      have "\<FF> (f, g) = h"
      proof (rule ext)
        fix p
        {
          assume "p \<in> P"
          hence "\<FF> (f, g) p = (f p, g p)" unfolding \<FF>_def and map_prod'_def by simp
          also from \<open>p \<in> P\<close> have "\<dots> = h p" unfolding f_def and g_def by simp
          finally have "\<FF> (f, g) p = h p" .
        }
        moreover {
          assume "p \<notin> P"
          hence "\<FF> (f, g) p = undefined" unfolding \<FF>_def by simp
          also from h and \<open>p \<notin> P\<close> have "\<dots> = h p" by fastforce
          finally have "\<FF> (f, g) p = h p" .
        }
        ultimately show "\<FF> (f, g) p = h p" by auto
      qed
      with \<open>f \<in> P \<rightarrow>\<^sub>E M\<close> and \<open>g \<in> P \<rightarrow>\<^sub>E N\<close> show "h \<in> \<FF> ` ((P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N))" by auto
    qed
  qed
  hence "bij_betw (the_inv_into ((P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N)) \<FF>) (P \<rightarrow>\<^sub>E M \<times> N) ((P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N))"
    by (fact bij_betw_the_inv_into)
  hence "|P \<rightarrow>\<^sub>E M \<times> N| =o |(P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N)|" by auto
  thus ?thesis unfolding cprod_definition and cexp_definition by simp
qed

theorem thm_2_10_c:
  fixes A :: "'a set"
    and B :: "'b set"
    and C :: "'c set"
  shows "( |C| ^c |A| ) ^c |B| =o |C| ^c ( |A| *c |B| )"
proof -
  define \<FF> where "\<FF> f b \<equiv> if b \<in> B then \<lambda>a. f (b, a) else undefined"
    for f :: "'b \<times> 'a \<Rightarrow> 'c" and b
  have "bij_betw \<FF> (B \<times> A \<rightarrow>\<^sub>E C) (B \<rightarrow>\<^sub>E (A \<rightarrow>\<^sub>E C))"
  proof (rule bij_betw_imageI)
    show "inj_on \<FF> (B \<times> A \<rightarrow>\<^sub>E C)"
    proof (rule inj_onI)
      fix f and g
      assume f: "f \<in> B \<times> A \<rightarrow>\<^sub>E C"
        and g: "g \<in> B \<times> A \<rightarrow>\<^sub>E C"
        and \<FF>: "\<FF> f = \<FF> g"
      show "f = g"
      proof (rule ext)
        fix x :: "'b \<times> 'a"
        from \<FF> have *: "\<FF> f (fst x) (snd x) = \<FF> g (fst x) (snd x)" by simp
        {
          assume "fst x \<in> B"
          with * have "f x = g x" unfolding \<FF>_def by simp
        }
        moreover {
          assume "fst x \<notin> B"
          hence "x \<notin> B \<times> A" by auto
          with f and g have "f x = undefined" and "g x = undefined" by auto
          hence "f x = g x" by simp
        }
        ultimately show "f x = g x" by auto
      qed
    qed
  next
    show "\<FF> ` (B \<times> A \<rightarrow>\<^sub>E C) = B \<rightarrow>\<^sub>E (A \<rightarrow>\<^sub>E C)"
    proof (rule surj_onI)
      fix f
      assume f: "f \<in> B \<times> A \<rightarrow>\<^sub>E C"
      show "\<FF> f \<in> B \<rightarrow>\<^sub>E (A \<rightarrow>\<^sub>E C)"
      proof (rule PiE_I)
        fix b
        assume "b \<in> B"
        show "\<FF> f b \<in> A \<rightarrow>\<^sub>E C"
        proof (rule PiE_I)
          fix a
          assume "a \<in> A"
          with \<open>b \<in> B\<close> and f show "\<FF> f b a \<in> C" unfolding \<FF>_def by auto
        next
          fix a
          assume "a \<notin> A"
          with \<open>b \<in> B\<close> and f show "\<FF> f b a = undefined" unfolding \<FF>_def by auto
        qed
      next
        fix b
        assume "b \<notin> B"
        with \<FF>_def show "\<FF> f b = undefined" by simp
      qed
    next
      fix f
      assume f: "f \<in> B \<rightarrow>\<^sub>E (A \<rightarrow>\<^sub>E C)"
      define f' where f': "f' x \<equiv> if x \<in> B \<times> A then f (fst x) (snd x) else undefined" for x
      have "f' \<in> B \<times> A \<rightarrow>\<^sub>E C"
      proof (rule PiE_I)
        fix x
        assume "x \<in> B \<times> A"
        with f' and f show "f' x \<in> C" by fastforce
      next
        fix x
        assume "x \<notin> B \<times> A"
        with f' show "f' x = undefined" by simp
      qed
      moreover have "\<FF> f' = f"
      proof (rule ext)
        fix b
        consider (A) "b \<in> B"
          | (B) "b \<notin> B" by auto
        thus "\<FF> f' b = f b"
        proof cases
          case A
          show ?thesis
          proof (rule ext)
            fix a
            consider (C) "a \<in> A"
              | (D) "a \<notin> A" by auto
            thus "\<FF> f' b a = f b a"
            proof cases
              case C
              with A and f' show ?thesis unfolding \<FF>_def by simp
            next
              case D
              with A and f' and f show ?thesis unfolding \<FF>_def by force
            qed
          qed
        next
          case B
          with f show ?thesis unfolding \<FF>_def by auto
        qed
      qed
      ultimately show "f \<in> \<FF> ` (B \<times> A \<rightarrow>\<^sub>E C)" by auto
    qed
  qed
  hence "|B \<times> A \<rightarrow>\<^sub>E C| =o |B \<rightarrow>\<^sub>E (A \<rightarrow>\<^sub>E C)|" by auto
  moreover have "|A \<times> B \<rightarrow>\<^sub>E C| =o |B \<times> A \<rightarrow>\<^sub>E C|"
  proof -
    have "|A \<times> B| =o |B \<times> A|" by (fact Times_card_commute)
    hence "|C| ^c |A \<times> B| =o |C| ^c |B \<times> A|" by (fact cexp_cong2')
    thus ?thesis unfolding cexp_definition by simp
  qed
  ultimately have "|A \<times> B \<rightarrow>\<^sub>E C| =o |B \<rightarrow>\<^sub>E (A \<rightarrow>\<^sub>E C)|" by (auto intro: card_eq_trans)
  hence "|B \<rightarrow>\<^sub>E (A \<rightarrow>\<^sub>E C)| =o |A \<times> B \<rightarrow>\<^sub>E C|" by auto
  moreover have "|B \<rightarrow>\<^sub>E (A \<rightarrow>\<^sub>E C)| = ( |C| ^c |A| ) ^c |B|" unfolding cexp_definition by simp
  moreover have "|A \<times> B \<rightarrow>\<^sub>E C| = |C| ^c ( |A| *c |B| )"
    unfolding cprod_definition and cexp_definition by simp
  ultimately show ?thesis by simp
qed

end
