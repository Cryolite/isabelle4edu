theory Section_2_3
  imports Main
    "HOL-Library.Disjoint_Sets"
    "HOL-Library.FuncSet"
    "Section_2_2"
begin

context includes cardinal_syntax begin

section \<open>3. Operations on Cardinalities\<close>

subsection \<open>A) Sum and Product of Cardinalities\<close>

proposition csum_definition:
  fixes A :: "'a set"
    and B :: "'b set"
  shows "|A| +c |B| = |A <+> B|"
  unfolding csum_def by (simp only: Field_card_of)

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

lemma union_card_leq_csum:
  shows "|A \<union> B| \<le>o |A| +c |B|"
proof -
  define f where "f x \<equiv> if x \<in> A then Inl x else Inr x" for x
  have "f ` (A \<union> B) \<subseteq> A <+> B"
  proof (rule image_subsetI)
    fix x
    assume "x \<in> A \<union> B"
    moreover {
      assume "x \<in> A"
      hence "f x \<in> A <+> B" unfolding f_def by auto
    }
    moreover {
      assume "x \<in> B"
      hence "f x \<in> A <+> B" unfolding f_def by auto
    }
    ultimately show "f x \<in> A <+> B" by auto
  qed
  moreover have "inj_on f (A \<union> B)"
  proof (rule inj_onI)
    fix x and y
    assume "x \<in> A \<union> B"
      and "y \<in> A \<union> B"
      and f: "f x = f y"
    from this(1,2) consider
      (A) "x \<in> A" and "y \<in> A"
      | (B) "x \<in> A" and "y \<in> B - A"
      | (C) "x \<in> B - A" and "y \<in> A"
      | (D) "x \<in> B - A" and "y \<in> B - A"
      by auto
    thus "x = y"
    proof cases
      case A
      with f show ?thesis unfolding f_def by simp
    next
      case B
      with f show ?thesis unfolding f_def by simp
    next
      case C
      with f show ?thesis unfolding f_def by simp
    next
      case D
      with f show ?thesis unfolding f_def by simp
    qed
  qed
  ultimately show ?thesis unfolding csum_definition by auto
qed

fun fun_disjoint_union_card_eq_csum where
  "fun_disjoint_union_card_eq_csum (Inl x) = x"
| "fun_disjoint_union_card_eq_csum (Inr x) = x"

lemma disjoint_union_card_eq_csum:
  assumes "A \<inter> B = {}"
  shows "|A \<union> B| =o |A| +c |B|"
proof -
  have "fun_disjoint_union_card_eq_csum ` (A <+> B) \<subseteq> A \<union> B"
  proof (rule image_subsetI)
    fix x
    assume "x \<in> A <+> B"
    moreover {
      assume "x \<in> Inl ` A"
      hence "fun_disjoint_union_card_eq_csum x \<in> A \<union> B" by auto
    }
    moreover {
      assume "x \<in> Inr ` B"
      hence "fun_disjoint_union_card_eq_csum x \<in> A \<union> B" by auto
    }
    ultimately show "fun_disjoint_union_card_eq_csum x \<in> A \<union> B" by auto
  qed
  moreover have "inj_on fun_disjoint_union_card_eq_csum (A <+> B)"
  proof (rule inj_onI)
    fix x and y
    assume "x \<in> A <+> B"
      and "y \<in> A <+> B"
      and *: "fun_disjoint_union_card_eq_csum x = fun_disjoint_union_card_eq_csum y"
    from this(1,2) consider
      (A) "x \<in> Inl ` A" and "y \<in> Inl ` A"
      | (B) "x \<in> Inl ` A" and "y \<in> Inr ` B"
      | (C) "x \<in> Inr ` B" and "y \<in> Inl ` A"
      | (D) "x \<in> Inr ` B" and "y \<in> Inr ` B"
      by blast
    thus "x = y"
    proof cases
      case A
      with * show ?thesis by auto
    next
      case B
      with * and assms show ?thesis by fastforce
    next
      case C
      with * and assms show ?thesis by fastforce
    next
      case D
      with * show ?thesis by auto
    qed
  qed
  ultimately have "|A| +c |B| \<le>o |A \<union> B|" unfolding csum_definition by auto
  moreover have "|A \<union> B| \<le>o |A <+> B|"
  proof -
    have "|A \<union> B| \<le>o |A| +c |B|" by (fact union_card_leq_csum)
    thus ?thesis unfolding csum_definition .
  qed
  ultimately show "|A \<union> B| =o |A| +c |B|" unfolding csum_definition by (intro thm_2_3_2)
qed

proposition cprod_definition:
  shows "|A| *c |B| = |A \<times> B|"
  unfolding cprod_def by (simp only: Field_card_of)

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
  moreover have "|{} :: ('a \<times> 'b) set| =o (czero :: 'c rel)" by (fact empty_card_eq_czero)
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

proposition prop_2_3_9':
  shows "|A| *c ( |B| +c |C| ) =o |A| *c |B| +c |A| *c |C|"
proof -
  from bij_betw_prod_sum_distribute have "|A \<times> (B <+> C)| =o |A \<times> B <+> A \<times> C|" by auto
  thus ?thesis unfolding csum_definition and cprod_definition by simp
qed

proposition prop_2_3_9:
  shows "( |A| +c |B| ) *c |C| =o |A| *c |C| +c |B| *c |C|"
proof -
  have "( |A| +c |B| ) *c |C| = |A <+> B| *c |C|" unfolding csum_definition ..
  also have "\<dots> =o |C| *c |A <+> B|" by (fact prop_2_3_5)
  also have "|C| *c |A <+> B| = |C| *c ( |A| +c |B| )" unfolding csum_definition ..
  also have "\<dots> =o |C| *c |A| +c |C| *c |B|" by (fact prop_2_3_9')
  also have "|C| *c |A| +c |C| *c |B| = |C \<times> A| +c |C \<times> B|" unfolding cprod_definition ..
  also have "\<dots> =o |A \<times> C| +c |B \<times> C|"
  proof -
    have "|C \<times> A| =o |A \<times> C|" unfolding cprod_definition by (fact Times_card_commute)
    moreover have "|C \<times> B| =o |B \<times> C|" unfolding cprod_definition by (fact Times_card_commute)
    ultimately show ?thesis by (fact csum_cong')
  qed
  also have "|A \<times> C| +c |B \<times> C| = |A| *c |C| +c |B| *c |C|" unfolding cprod_definition ..
  finally show ?thesis .
qed

theorem thm_2_9:
  fixes A :: "'b \<Rightarrow> 'a set"
  assumes "|\<Lambda>| = \<nn>"
    and "\<And>l. l \<in> \<Lambda> \<Longrightarrow> |A l| =o \<mm>"
    and "\<Lambda> = {} \<Longrightarrow> \<exists>X. |X| = \<mm>" \<comment> \<open>This assumption guarantees that @{term "\<mm>"} is a cardinal
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
    also have "|A l\<^sub>0 \<times> \<Lambda>| = |A l\<^sub>0| *c |\<Lambda>|" unfolding cprod_definition ..
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

subsection \<open>B) Power of Cardinalities\<close>

proposition cexp_definition:
  shows "|A| ^c |B| = |B \<rightarrow>\<^sub>E A|"
proof -
  have "|A| ^c |B| = |Func B A|" unfolding cexp_def by (simp only: Field_card_of)
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
    and "B = {} \<longleftrightarrow> B' = {}" \<comment> \<open>Is this assumption necessary?\<close>
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

proposition thm_2_3_b:
  fixes \<Lambda> :: "'l set"
    and B :: "'l \<Rightarrow> 'b set"
    and B\<^sub>0 :: "'c set"
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> |B l| =o |B\<^sub>0|"
  shows "|\<Prod>\<^sub>d l \<in> \<Lambda>. B l| =o |B\<^sub>0| ^c |\<Lambda>|"
proof -
  {
    fix l
    assume "l \<in> \<Lambda>"
    with assms have "\<exists>\<sigma>. bij_betw (\<sigma> l) (B l) B\<^sub>0" by fast
  }
  then obtain \<sigma>' where \<sigma>': "\<sigma>' \<in> (\<Pi> l \<in> \<Lambda>. {\<sigma>. bij_betw (\<sigma> l) (B l) B\<^sub>0})" by (elim AC_E_ex)
  define \<sigma> where "\<sigma> l \<equiv> (\<sigma>' l) l" for l
  {
    fix l
    assume "l \<in> \<Lambda>"
    with \<sigma>' have "bij_betw ((\<sigma>' l) l) (B l) B\<^sub>0" by auto
  }
  hence \<sigma>: "bij_betw (\<sigma> l) (B l) B\<^sub>0" if "l \<in> \<Lambda>" for l unfolding \<sigma>_def by (simp add: that)
  hence \<sigma>_inj: "inj_on (\<sigma> l) (B l)" if "l \<in> \<Lambda>" for l by (auto intro: that)
  from \<sigma> have \<sigma>_surj: "(\<sigma> l) ` (B l) = B\<^sub>0" if "l \<in> \<Lambda>" for l
    by (simp add: bij_betw_imp_surj_on that)
  define \<FF> where "\<FF> \<BB> l \<equiv> if l \<in> \<Lambda> then (\<sigma> l) (\<BB> l) else undefined" for \<BB> :: "'l \<Rightarrow> 'b" and l
  have "bij_betw \<FF> (\<Prod>\<^sub>d l \<in> \<Lambda>. B l) (\<Lambda> \<rightarrow>\<^sub>E B\<^sub>0)"
  proof (rule bij_betw_imageI)
    show "inj_on \<FF> (\<Prod>\<^sub>d l \<in> \<Lambda>. B l)"
    proof (rule inj_onI)
      fix \<BB> and \<BB>'
      assume \<BB>: "\<BB> \<in> (\<Prod>\<^sub>d l \<in> \<Lambda>. B l)"
        and \<BB>': "\<BB>' \<in> (\<Prod>\<^sub>d l \<in> \<Lambda>. B l)"
        and *: "\<FF> \<BB> = \<FF> \<BB>'"
      show "\<BB> = \<BB>'"
      proof (rule ext)
        fix l
        {
          assume l: "l \<in> \<Lambda>"
          with \<BB> and \<BB>' have "\<BB> l \<in> B l" and "\<BB>' l \<in> B l" by auto
          moreover from * and l have "(\<sigma> l) (\<BB> l) = (\<sigma> l) (\<BB>' l)" unfolding \<FF>_def by meson
          moreover from \<sigma>_inj and l have "inj_on (\<sigma> l) (B l)" by simp
          ultimately have "\<BB> l = \<BB>' l" by (auto dest: inj_onD)
        }
        moreover {
          assume l: "l \<notin> \<Lambda>"
          with \<BB> and \<BB>' have "\<BB> l = \<BB>' l" by fastforce
        }
        ultimately show "\<BB> l = \<BB>' l" by auto
      qed
    qed
  next
    show "\<FF> ` (\<Prod>\<^sub>d l \<in> \<Lambda>. B l) = (\<Lambda> \<rightarrow>\<^sub>E B\<^sub>0)"
    proof (rule surj_onI)
      fix \<BB>
      assume \<BB>: "\<BB> \<in> (\<Prod>\<^sub>d l \<in> \<Lambda>. B l)"
      show "\<FF> \<BB> \<in> \<Lambda> \<rightarrow>\<^sub>E B\<^sub>0"
      proof (rule PiE_I)
        fix l
        assume l: "l \<in> \<Lambda>"
        hence "\<FF> \<BB> l = (\<sigma> l) (\<BB> l)" unfolding \<FF>_def by simp
        also from \<BB> and l and \<sigma>_surj have "\<dots> \<in> B\<^sub>0" by fast
        finally show "\<FF> \<BB> l \<in> B\<^sub>0" .
      next
        fix l
        assume "l \<notin> \<Lambda>"
        with \<FF>_def show "\<FF> \<BB> l = undefined" by simp
      qed
    next
      fix f
      assume f: "f \<in> \<Lambda> \<rightarrow>\<^sub>E B\<^sub>0"
      define \<tau> where "\<tau> l \<equiv> the_inv_into (B l) (\<sigma> l)" for l
      define \<BB> where "\<BB> l \<equiv> if l \<in> \<Lambda> then (\<tau> l) (f l) else undefined" for l
      have "\<BB> \<in> (\<Prod>\<^sub>d l \<in> \<Lambda>. B l)"
      proof (rule dprodI)
        fix l
        assume l: "l \<in> \<Lambda>"
        with f have "f l \<in> B\<^sub>0" by auto
        moreover have "(\<tau> l) ` B\<^sub>0 = B l"
        proof -
          from \<sigma> and l have "bij_betw (\<sigma> l) (B l) B\<^sub>0" by simp
          hence "bij_betw (\<tau> l) B\<^sub>0 (B l)" unfolding \<tau>_def by (fact bij_betw_the_inv_into)
          thus ?thesis by auto
        qed
        moreover note l
        ultimately show "\<BB> l \<in> B l" unfolding \<BB>_def by auto
      next
        fix l
        assume "l \<notin> \<Lambda>"
        thus "\<BB> l = undefined" unfolding \<BB>_def by simp
      qed
      moreover have "\<FF> \<BB> = f"
      proof (rule ext)
        fix l
        {
          assume l: "l \<in> \<Lambda>"
          hence "(\<FF> \<BB>) l = (\<sigma> l) ((\<tau> l) (f l))" unfolding \<FF>_def \<BB>_def by simp
          moreover have "id_on ((\<sigma> l) \<circ> (\<tau> l)) B\<^sub>0"
          proof (rule id_onI)
            fix b
            assume b: "b \<in> B\<^sub>0"
            have "((\<sigma> l) \<circ> (\<tau> l)) b = (\<sigma> l) ((\<tau> l) b)" by simp
            also have "\<dots> = (\<sigma> l) ((the_inv_into (B l) (\<sigma> l)) b)" unfolding \<tau>_def ..
            also have "\<dots> = b"
            proof (rule f_the_inv_into_f)
              from \<sigma>_inj and l show "inj_on (\<sigma> l) (B l)" .
            next
              from \<sigma>_surj and l and b show "b \<in> (\<sigma> l) ` (B l)" by simp
            qed
            finally show "((\<sigma> l) \<circ> (\<tau> l)) b = b" .
          qed
          moreover from f and l have "f l \<in> B\<^sub>0" by auto
          ultimately have "(\<FF> \<BB>) l = f l" by auto
        }
        moreover {
          assume "l \<notin> \<Lambda>"
          with f have "(\<FF> \<BB>) l = f l" unfolding \<FF>_def by fastforce
        }
        ultimately show "(\<FF> \<BB>) l = f l" by auto
      qed
      ultimately show "f \<in> \<FF> ` (\<Prod>\<^sub>d l \<in> \<Lambda>. B l)" by auto
    qed
  qed
  thus ?thesis unfolding cexp_definition by auto
qed

proposition prop_2_3_15_a:
  fixes M :: "'m set"
  shows "|Pow M| =o ctwo ^c |M|"
proof -
  define \<FF> where "\<FF> X m \<equiv> if m \<in> M then m \<in> X else undefined" for X :: "'m set" and m
  have "bij_betw \<FF> (Pow M) (M \<rightarrow>\<^sub>E (UNIV :: bool set))"
  proof (rule bij_betw_imageI')
    fix X and Y
    assume "X \<in> Pow M"
      and "Y \<in> Pow M"
      and \<FF>: "\<FF> X = \<FF> Y"
    show "X = Y"
    proof (rule equalityI)
      {
        fix x
        assume x: "x \<in> X"
        with \<open>X \<in> Pow M\<close> have x': "x \<in> M" by auto
        {
          assume "x \<notin> Y"
          with x and x' and \<FF> have "False" unfolding \<FF>_def by meson
        }
        hence "x \<in> Y" by auto
      }
      thus "X \<subseteq> Y" ..
    next
      {
        fix y
        assume y: "y \<in> Y"
        with \<open>Y \<in> Pow M\<close> have y': "y \<in> M" by auto
        {
          assume "y \<notin> X"
          with y and y' and \<FF> have "False" unfolding \<FF>_def by meson
        }
        hence "y \<in> X" by auto
      }
      thus "Y \<subseteq> X" ..
    qed
  next
    fix X
    assume "X \<in> Pow M"
    show "\<FF> X \<in> M \<rightarrow>\<^sub>E UNIV"
    proof (rule PiE_I)
      fix x
      show "\<FF> X x \<in> UNIV" ..
    next
      fix x
      assume "x \<notin> M"
      thus "\<FF> X x = undefined" unfolding \<FF>_def by simp
    qed
  next
    fix f :: "'m \<Rightarrow> bool"
    assume f: "f \<in> M \<rightarrow>\<^sub>E UNIV"
    define X where "X \<equiv> {x \<in> M. f x}"
    have "\<FF> X = f"
    proof (rule ext)
      fix x
      {
        assume x: "x \<in> M"
        hence "\<FF> X x = f x" unfolding \<FF>_def and X_def by simp
      }
      moreover {
        assume "x \<notin> M"
        with f have "\<FF> X x = f x" unfolding \<FF>_def by auto
      }
      ultimately show "\<FF> X x = f x" by auto
    qed
    moreover have "X \<in> Pow M"
    proof (rule PowI; rule subsetI)
      fix x
      assume "x \<in> X"
      hence "x \<in> M" and "f x" unfolding X_def by simp_all
      with f show "x \<in> M" by simp
    qed
    ultimately show "f \<in> \<FF> ` (Pow M)" by auto
  qed
  hence "|Pow M| =o |M \<rightarrow>\<^sub>E (UNIV :: bool set)|" by auto
  thus ?thesis unfolding cexp_definition and ctwo_def .
qed

proposition prop_2_3_15_b:
  shows "|M| <o ctwo ^c |M|"
proof -
  have "|M| <o |Pow M|" by (fact thm_2_8)
  also have "|Pow M| =o ctwo ^c |M|" by (fact prop_2_3_15_a)
  finally show ?thesis .
qed

subsection \<open>C) Operations on Cardinalities @{term "\<aleph>\<^sub>0"} and @{term "\<aleph>"}\<close>

fun fun_2_11_a where
  "fun_2_11_a f (Inl x) = 2 * (f x)"
| "fun_2_11_a f (Inr x) = 2 * x + 1"

theorem thm_2_11_a:
  fixes M :: "'m set"
  assumes "|M| \<le>o \<aleph>\<^sub>0"
  shows "|M| +c \<aleph>\<^sub>0 =o \<aleph>\<^sub>0"
proof -
  have "|M <+> (UNIV :: nat set)| \<le>o |UNIV :: nat set|"
  proof -
    from assms obtain f where "f ` M \<subseteq> (UNIV :: nat set)" and f: "inj_on f M" by auto
    have "inj_on (fun_2_11_a f) (M <+> (UNIV :: nat set))"
    proof (rule inj_onI)
      fix x and y
      assume "x \<in> M <+> (UNIV :: nat set)"
        and "y \<in> M <+> (UNIV :: nat set)"
        and fun_2_11_a: "fun_2_11_a f x = fun_2_11_a f y"
      from this(1,2) consider (A) "x \<in> Inl ` M" and "y \<in> Inl ` M"
        | (B) "x \<in> Inl ` M" and "y \<in> Inr ` UNIV"
        | (C) "x \<in> Inr ` UNIV" and "y \<in> Inl ` M"
        | (D) "x \<in> Inr ` UNIV" and "y \<in> Inr ` UNIV" by blast
      thus "x = y"
      proof cases
        case A
        then obtain m and m' where "m \<in> M" and "Inl m = x" and "m' \<in> M" and "Inl m' = y" by auto
        with fun_2_11_a have "2 * (f m) = 2 * (f m')" by auto
        hence "f m = f m'" by simp
        with f and \<open>m \<in> M\<close> and \<open>m' \<in> M\<close> have "m = m'" by (elim inj_onD)
        with \<open>Inl m = x\<close> and \<open>Inl m' = y\<close> show ?thesis by simp
      next
        case B
        then obtain m and n where "Inl m = x" and "Inr n = y" by auto
        with fun_2_11_a have "2 * (f m) = 2 * n + 1" by auto
        hence "False" by presburger
        thus ?thesis by simp
      next
        case C
        then obtain n and m where "Inr n = x" and "Inl m = y" by auto
        with fun_2_11_a have "2 * n + 1 = 2 * (f m)" by auto
        hence "False" by presburger
        thus ?thesis by simp
      next
        case D
        then obtain n and n' where n: "Inr n = x" and n': "Inr n' = y" by auto
        with fun_2_11_a have "2 * n + 1 = 2 * n' + 1" by auto
        hence "n = n'" by simp
        with n and n' show ?thesis by simp
      qed
    qed
    thus ?thesis by auto
  qed
  moreover have "|UNIV :: nat set| \<le>o |M <+> (UNIV :: nat set)|"
  proof -
    have "inj_on Inr (UNIV :: nat set)" by simp
    thus ?thesis by auto
  qed
  ultimately have "|M <+> (UNIV :: nat set)| =o |UNIV :: nat set|" by (fact thm_2_3_2)
  thus "|M| +c \<aleph>\<^sub>0 =o \<aleph>\<^sub>0" unfolding csum_definition by simp
qed

theorem thm_2_11_a':
  shows "\<aleph>\<^sub>0 +c \<aleph>\<^sub>0 =o \<aleph>\<^sub>0"
  by (rule thm_2_11_a; simp)

lemma inj_on_map_sum:
  assumes "inj_on f A"
    and "inj_on g B"
  shows "inj_on (map_sum f g) (A <+> B)"
proof (rule inj_onI)
  fix x and x'
  assume "x \<in> A <+> B"
    and "x' \<in> A <+> B"
    and *: "(map_sum f g) x = (map_sum f g) x'"
  from this(1,2) consider
    (A) "x \<in> Inl ` A" and "x' \<in> Inl ` A"
    | (B) "x \<in> Inl ` A" and "x' \<in> Inr ` B"
    | (C) "x \<in> Inr ` B" and "x' \<in> Inl ` A"
    | (D) "x \<in> Inr ` B" and "x' \<in> Inr ` B"
    by blast
  thus "x = x'"
  proof cases
    case A
    then obtain a and a' where "a \<in> A" and "Inl a = x" and "a' \<in> A" and "Inl a' = x'" by auto
    with * have "Inl (f a) = Inl (f a')" by auto
    hence "f a = f a'" by simp
    with assms(1) and \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> have "a = a'" by (elim inj_onD)
    with \<open>Inl a = x\<close> and \<open>Inl a' = x'\<close> show ?thesis by simp
  next
    case B
    with * have "False" by auto
    thus ?thesis ..
  next
    case C
    with * have "False" by auto
    thus ?thesis ..
  next
    case D
    then obtain b and b' where "b \<in> B" and "Inr b = x" and "b' \<in> B" and "Inr b' = x'" by auto
    with * have "Inr (g b) = Inr (g b')" by auto
    hence "g b = g b'" by simp
    with assms(2) and \<open>b \<in> B\<close> and \<open>b' \<in> B\<close> have "b = b'" by (elim inj_onD)
    with \<open>Inr b = x\<close> and \<open>Inr b' = x'\<close> show ?thesis by simp
  qed
qed

theorem thm_2_11_b:
  assumes "|M| \<le>o \<aleph>"
  shows "|M| +c \<aleph> =o \<aleph>"
proof -
  let ?A = "{-(1 :: real) <..< (0 :: real)}"
  let ?B = "{(0 :: real) <..< (1 :: real)}"
  have "|UNIV :: real set| \<le>o |M <+> (UNIV :: real set)|" by auto
  moreover have "|M <+> (UNIV :: real set)| \<le>o |UNIV :: real set|"
  proof -
    have "|M <+> (UNIV :: real set)| = |M| +c |UNIV :: real set|" unfolding csum_definition ..
    also have "\<dots> =o |M| +c |?B|"
    proof -
      have "equipotent ?B (UNIV :: real set)" by (simp add: ex_2_5''')
      hence "|?B| =o |UNIV :: real set|" by auto
      hence "|UNIV :: real set| =o |?B|" by auto
      thus ?thesis by (fact csum_cong2')
    qed
    also have "|M| +c |?B| = |M <+> ?B|" unfolding csum_definition ..
    also have "\<dots> \<le>o |?A <+> ?B|"
    proof -
      have "equipotent ?A (UNIV :: real set)" by (simp add: ex_2_5''')
      hence "|?A| =o |UNIV :: real set|" by auto
      hence "|UNIV :: real set| =o |?A|" by auto
      with assms have "|M| \<le>o |?A|" by (fact card_leq_card_eq_trans)
      then obtain f where f: "f ` M \<subseteq> ?A" and f': "inj_on f M" by auto
      have id: "id ` ?B \<subseteq> ?B" and id': "inj_on id ?B" by simp_all
      from f and id have "(map_sum f id) ` (M <+> ?B) \<subseteq> ?A <+> ?B" by fastforce
      moreover from f' and id' have "inj_on (map_sum f id) (M <+> ?B)" by (fact inj_on_map_sum)
      ultimately show ?thesis by auto
    qed
    also have "|?A <+> ?B| \<le>o |?A \<union> ?B|"
    proof -
      have "?A \<inter> ?B = {}" by simp
      hence "|?A \<union> ?B| =o |?A| +c |?B|" by (fact disjoint_union_card_eq_csum)
      thus ?thesis unfolding csum_definition by fast
    qed
    also have "|?A \<union> ?B| \<le>o |UNIV :: real set|" by auto
    finally show ?thesis by simp
  qed
  ultimately have "|M <+> (UNIV :: real set)| =o |UNIV :: real set|" by (elim thm_2_3_2)
  thus ?thesis unfolding csum_definition by simp
qed

(* TODO:
theorem thm_2_11_b':
  shows "\<aleph>\<^sub>0 +c \<aleph> =o \<aleph>"
proof -
  have "\<aleph>\<^sub>0 \<le>o \<aleph>" sorry
  thus ?thesis by (fact thm_2_11_b)
qed
*)

theorem thm_2_11_b'':
  shows "\<aleph> +c \<aleph> =o \<aleph>"
  by (simp add: thm_2_11_b)

theorem thm_2_11_c:
  fixes M :: "'m set"
  assumes "cone \<le>o |M|"
    and "|M| \<le>o \<aleph>\<^sub>0"
  shows "|M| *c \<aleph>\<^sub>0 =o \<aleph>\<^sub>0"
proof -
  have "|M \<times> (UNIV :: nat set)| \<le>o |UNIV :: nat set|"
  proof -
    from assms(2) obtain f where f: "f ` M \<subseteq> (UNIV :: nat set)" and f': "inj_on f M" by auto
    define \<FF> :: "'m \<times> nat \<Rightarrow> nat \<times> nat" where "\<FF> \<equiv> map_prod f id"
    have id: "id ` (UNIV :: nat set) \<subseteq> (UNIV :: nat set)" by simp
    have id': "inj_on id (UNIV :: nat set)" by simp
    from f and id have "\<FF> ` (M \<times> (UNIV :: nat set)) \<subseteq> (UNIV :: nat set) \<times> (UNIV :: nat set)"
      unfolding \<FF>_def by simp
    moreover from f' and id' have "inj_on \<FF> (M \<times> (UNIV :: nat set))"
      unfolding \<FF>_def by (fact map_prod_inj_on)
    ultimately have "|M \<times> (UNIV :: nat set)| \<le>o |(UNIV :: nat set) \<times> (UNIV :: nat set)|" by auto
    also have "|(UNIV :: nat set) \<times> (UNIV :: nat set)| =o |UNIV :: nat set|"
      by (fact nat_Times_nat_card_eq_aleph_zero)
    finally show ?thesis unfolding cprod_definition .
  qed
  moreover have "|UNIV :: nat set| \<le>o |M \<times> (UNIV :: nat set)|"
  proof -
    from assms(1) have "|{()}| \<le>o |M|" unfolding cone_def by simp
    then obtain f where "f ` {()} \<subseteq> M" by auto
    hence "f () \<in> M" by simp
    define \<FF> where "\<FF> n \<equiv> (f (), n)" for n :: nat
    from \<open>f () \<in> M\<close> have "\<FF> ` (UNIV :: nat set) \<subseteq> M \<times> (UNIV :: nat set)" unfolding \<FF>_def by auto
    moreover have "inj_on \<FF> (UNIV :: nat set)" unfolding \<FF>_def by (meson injI prod.inject)
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis unfolding cprod_definition by (fact thm_2_3_2)
qed

lemma surj_Real:
  shows "surj Real.Real"
proof -
  obtain rr :: "(real \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> rat" where
    "\<forall>p r. p r \<or> \<not> p (Real.Real (rr p)) \<and> realrel (rr p) (rr p)"
    by (metis real.abs_induct)
  hence "surj (quot_type.abs realrel Abs_real)" using Real_def by auto
  thus ?thesis unfolding Real.Real_def .
qed

lemma aleph_card_leq_rational_sequence:
  shows "\<aleph> \<le>o |UNIV :: (nat \<Rightarrow> rat) set|"
  using surj_Real by (fact surj_on_imp_card_leq)

(* TODO:
lemma aleph_card_leq_ctwo_cexp_aleph_naught:
  shows "\<aleph> \<le>o ctwo ^c \<aleph>\<^sub>0"
proof -
  have "|UNIV ::real set| \<le>o |UNIV :: (nat \<Rightarrow> rat) set|" by (fact aleph_card_leq_rational_sequence)
  also have "|UNIV :: (nat \<Rightarrow> rat) set| =o |UNIV :: (nat \<Rightarrow> bool) set|" sorry
  finally show ?thesis unfolding cexp_definition and ctwo_definition by simp
qed
*)

lemma ctwo_cexp_aleph_naught_card_leq_aleph:
  shows "ctwo ^c \<aleph>\<^sub>0 \<le>o \<aleph>"
proof -
  have "ctwo ^c \<aleph>\<^sub>0 = |UNIV :: bool set| ^c \<aleph>\<^sub>0" unfolding ctwo_definition ..
  also have "\<dots> =o |{1 :: rat, 2 :: rat}| ^c \<aleph>\<^sub>0"
  proof -
    have "|UNIV :: bool set| =o |{1 :: rat, 2 :: rat}|" by (simp add: card_of_bool)
    thus ?thesis by (fact cexp_cong1')
  qed
  also have "|{1 :: rat, 2 :: rat}| ^c \<aleph>\<^sub>0 = |(UNIV :: nat set) \<rightarrow>\<^sub>E {1 :: rat, 2 :: rat}|"
    unfolding cexp_definition ..
  also have "\<dots> \<le>o |UNIV :: real set|"
  proof -
    define a where "a f n \<equiv> (f n) / (3^n)" for f :: "nat \<Rightarrow> rat" and n
    define g where "g f n \<equiv> \<Sum>i \<in> {0 .. n}. a f i" for f :: "nat \<Rightarrow> rat" and n
    have f_inf: "1 \<le> f n" if "f \<in> UNIV \<rightarrow>\<^sub>E {1, 2}" for f :: "nat \<Rightarrow> rat" and n
    proof -
      from that have "f n \<in> {1, 2}" by auto
      moreover have "f n \<ge> 1" if "f n = 1" by (simp only: that)
      moreover have "f n \<ge> 1" if "f n = 2" by (simp only: that)
      ultimately show ?thesis by auto
    qed
    have f_sup: "f n \<le> 2" if "f \<in> UNIV \<rightarrow>\<^sub>E {1, 2}" for f :: "nat \<Rightarrow> rat" and n
    proof -
      from that have "f n \<in> {1, 2}" by auto
      moreover have "f n \<le> 2" if "f n = 1" by (simp only: that)
      moreover have "f n \<le> 2" if "f n = 2" by (simp only: that)
      ultimately show ?thesis by auto
    qed
    have *: "g f m - g f n = (\<Sum>i \<in> {n + 1 .. m}. a f i)" if "n \<le> m" for f and m and n
      using that proof (induct rule: Nat.dec_induct)
      case base
      show ?case by simp
    next
      case (step k)
      have "g f (Suc k) - g f n = (g f k + a f (Suc k)) - g f n" unfolding g_def and a_def by auto
      also have "\<dots> = (g f k - g f n) + a f (Suc k)" by simp
      also from step.hyps(3) have "\<dots> = (\<Sum>i \<in> {n + 1 .. k}. a f i) + a f (Suc k)" by simp
      also from step.hyps(1) have "\<dots> = (\<Sum>i \<in> {n + 1 .. (Suc k)}. a f i)" by simp
      finally show ?case .
    qed
    have **: "0 \<le> g f m - g f n" if "f \<in> UNIV \<rightarrow>\<^sub>E {1, 2}" and "n \<le> m" for f and m and n
    proof -
      from that(1) have "f i \<in> {1, 2}" for i by auto
      moreover have "0 \<le> f i" if "f i = 1" for i by (simp only: that)
      moreover have "0 \<le> f i" if "f i = 2" for i by (simp only: that)
      ultimately have "0 \<le> f i" for i by blast
      moreover have "(0 :: rat) < 3^i" for i by simp
      ultimately have "0 \<le> a f i" for i unfolding a_def by simp
      hence "0 \<le> (\<Sum>i \<in> {n + 1 .. m}. a f i)" by (simp only: sum_nonneg)
      also from that(2) have "\<dots> = g f m - g f n" by (simp only: *)
      finally show ?thesis .
    qed
    have ***: "g f m - g f n < 1 / (3^n)" if "f \<in> UNIV \<rightarrow>\<^sub>E {1, 2}" and "n \<le> m" for f and m and n
    proof -
      have "g f m - g f n = (\<Sum>i \<in> {n + 1 .. m}. a f i)"
        using that(2) proof (induct rule: Nat.dec_induct)
        case base
        show ?case unfolding g_def by simp
      next
        case (step k)
        have "g f (Suc k) - g f n = (g f k + a f (Suc k)) - g f n"
          unfolding g_def and a_def by simp
        also have "\<dots> = (g f k - g f n) + a f (Suc k)" by simp
        also from step.hyps(3) have "\<dots> = (\<Sum>i \<in> {n + 1 .. k}. a f i) + a f (Suc k)"
          by simp
        also from step.hyps(1) have "\<dots> = (\<Sum>i \<in> {n + 1 .. (Suc k)}. a f i)" by simp
        finally show ?case .
      qed
      also have "\<dots> \<le> (\<Sum>i \<in> {n + 1 .. m}. 2 / (3 ^ i))"
      proof (rule sum_mono)
        fix i
        from that(1) have "f i \<le> 2" by (fact f_sup)
        moreover have "(0 :: rat) < 3 ^ i" by simp
        ultimately show "a f i \<le> 2 / (3 ^ i)" unfolding a_def by (simp add: divide_right_mono)
      qed
      also have "\<dots> = 1 / (3 ^ n) - 1 / (3 ^ m)"
        using that(2) proof (induct rule: Nat.dec_induct)
        case base
        show ?case by simp
      next
        case (step k)
        from step.hyps(3) have "(\<Sum>i \<in> {n + 1 .. (Suc k)}. (2 :: rat) / (3 ^ i)) = 1 / (3 ^ n) - 1 / (3 ^ k) + 2 / (3 ^ (Suc k))" by auto
        also have "\<dots> = 1 / (3 ^ n) - 1 / (3 ^ (Suc k))" by simp
        finally show ?case .
      qed
      also have "\<dots> < 1 / (3 ^ n)" by simp
      finally show ?thesis .
    qed
    have g: "Real.cauchy (g f)" if "f \<in> (UNIV :: nat set) \<rightarrow>\<^sub>E {1 :: rat, 2 :: rat}" for f
    proof (rule Real.cauchyI)
      fix r :: rat
      assume "0 < r"
      then obtain k' :: nat where k': "1 < (of_nat k') * r" using ex_less_of_nat_mult by blast
      obtain k :: nat where "k' < 3 ^ k"
        by (metis of_nat_eq_of_nat_power_cancel_iff of_nat_less_iff of_nat_numeral one_less_numeral_iff real_arch_pow semiring_norm(77))
      with \<open>0 < r\<close> have "(of_nat k') * r < (3 ^ k) * r" by simp
      with k' have "1 < (3 ^ k) * r" by simp
      hence "1 < r * (3 ^ k)" by (simp add: mult.commute)
      moreover have "(0 :: rat) < 3 ^ k" by simp
      ultimately have k: "1 / (3 ^ k) < r" by (simp only: mult_imp_div_pos_less)
      {
        fix m :: nat and n :: nat
        assume m: "m \<ge> k"
          and n: "n \<ge> k"
        {
          assume "m \<le> n"
          have "\<bar>g f m - g f n\<bar> = g f n - g f m"
          proof -
            from that and \<open>m \<le> n\<close> have "g f m - g f n \<le> 0" using ** by auto
            thus ?thesis by simp
          qed
          also from that and \<open>m \<le> n\<close> have "\<dots> < 1 / (3 ^ m)" by (fact ***)
          also have "\<dots> \<le> 1 / (3 ^ k)"
          proof -
            from m have "(3 :: rat) ^ k \<le> 3 ^ m" by simp
            moreover have "(0 :: rat) < 3 ^ k" by simp
            ultimately show ?thesis by (simp add: frac_le)
          qed
          also from k have "\<dots> < r" by simp
          finally have "\<bar>g f m - g f n\<bar> < r" .
        }
        moreover {
          assume "n \<le> m"
          hence "\<bar>g f m - g f n\<bar> = g f m - g f n"
          proof -
            from that and \<open>n \<le> m\<close> have "0 \<le> g f m - g f n" using ** by auto
            thus ?thesis by simp
          qed
          also from that and \<open>n \<le> m\<close> have "\<dots> < 1 / (3 ^ n)" by (fact ***)
          also have "\<dots> \<le> 1 / (3 ^ k)"
          proof -
            from n have "(3 :: rat) ^ k \<le> 3 ^ n" by simp
            moreover have "(0 :: rat) < 3 ^ k" by simp
            ultimately show ?thesis by (simp add: frac_le)
          qed
          also from k have "\<dots> < r" by simp
          finally have "\<bar>g f m - g f n\<bar> < r" .
        }
        ultimately have "\<bar>g f m - g f n\<bar> < r" by linarith
      }
      thus "\<exists>k. \<forall>m \<ge> k. \<forall>n \<ge> k. \<bar>g f m - g f n\<bar> < r" by auto
    qed
    have "(Real.Real \<circ> g) ` ((UNIV :: nat set) \<rightarrow>\<^sub>E {1 :: rat, 2 :: rat}) \<subseteq> (UNIV :: real set)"
      by simp
    moreover have "inj_on (Real.Real \<circ> g) ((UNIV :: nat set) \<rightarrow>\<^sub>E {1 :: rat, 2 :: rat})"
    proof (rule inj_onI)
      fix f and f'
      assume f: "f \<in> (UNIV :: nat set) \<rightarrow>\<^sub>E {1 :: rat, 2 :: rat}"
        and f': "f' \<in> (UNIV :: nat set) \<rightarrow>\<^sub>E {1 :: rat, 2 :: rat}"
        and "(Real.Real \<circ> g) f = (Real.Real \<circ> g) f'"
      from this(3) have "Real.Real (g f) = Real.Real (g f')" by simp
      moreover from f have "Real.cauchy (g f)" by (fact g)
      moreover from f' have "Real.cauchy (g f')" by (fact g)
      ultimately have "realrel (g f) (g f')" by (smt Quotient3_def Quotient3_real realrel_refl)
      hence "Real.vanishes (\<lambda>i. (g f) i - (g f') i)" unfolding realrel_def by simp
      hence vanishes: "\<forall>\<epsilon> > 0. \<exists>k. \<forall>n \<ge> k. \<bar>(g f) n - (g f') n\<bar> < \<epsilon>" unfolding Real.vanishes_def .
      show "f = f'"
      proof (rule ccontr)
        assume "f \<noteq> f'"
        hence "\<exists>n. f n \<noteq> f' n" by auto
        hence "\<exists>n. f n \<noteq> f' n \<and> (\<forall>i < n. \<not>(f i \<noteq> f' i))" by (auto cong: exists_least_iff)
        then obtain n where "f n \<noteq> f' n" and f_eq: "\<forall>i < n. f i = f' i" by auto
        from this(1) and f and f' consider
          (A) "f n = 2" and "f' n = 1"
          | (B) "f n = 1" and "f' n = 2" by force
        hence "\<bar>f n - f' n\<bar> = 1" by (cases, simp_all)
        have ****: "g f n - g f' n = a f n - a f' n"
        proof -
          {
            assume "n = 0"
            hence ?thesis unfolding g_def by simp
          }
          moreover {
            assume "n \<noteq> 0"
            have "g f n - g f' n = (\<Sum>i \<in> {0 .. n}. a f i - a f' i)"
              unfolding g_def by (simp only: sum_subtractf)
            also from \<open>n \<noteq> 0\<close> have "\<dots> = (\<Sum>i \<in> {0 .. Suc (n - 1)}. a f i - a f' i)" by simp
            also have "\<dots> = (\<Sum>i \<in> {0 .. n - 1}. a f i - a f' i) + (a f (Suc (n - 1)) - a f' (Suc (n - 1)))"
              by simp
            also have "\<dots> = a f n - a f' n"
            proof -
              have "\<forall>i \<in> {0 .. n - 1}. a f i = a f' i"
              proof (rule ballI)
                fix i
                assume "i \<in> {0 .. n - 1}"
                with \<open>n \<noteq> 0\<close> have "i < n" by simp
                with f_eq have "f i = f' i" by simp
                thus "a f i = a f' i" unfolding a_def by simp
              qed
              hence "(\<Sum>i \<in> {0 .. n - 1}. a f i - a f' i) = 0" by simp
              with \<open>n \<noteq> 0\<close> show ?thesis by simp
            qed
            finally have ?thesis .
          }
          ultimately show ?thesis by blast
        qed
        from vanishes obtain k where *****: "\<forall>m \<ge> k. \<bar>(g f) m - (g f') m\<bar> < 1 / (2 * 3^n)"
          by fastforce
        {
          assume "k \<le> n"
          with ***** have "\<bar>g f n - g f' n\<bar> < 1 / (2 * 3^n)" by simp
          also have "\<dots> < 1 / (3^n)"
          proof -
            have "(1 :: rat) / (2 * 3^n) = (1 / 2) * (1 / 3^n)" by simp
            moreover have "(0 :: rat) < 1 / 3^n" by simp
            ultimately show ?thesis by linarith
          qed
          also have "\<dots> = \<bar>g f n - g f' n\<bar>"
          proof -
            have "g f n - g f' n = a f n - a f' n" by (fact ****)
            also have "\<dots> = ((f n) - (f' n)) / (3^n)" unfolding a_def by algebra
            finally have "g f n - g f' n = ((f n) - (f' n)) / (3^n)" .
            with \<open>\<bar>f n - f' n\<bar> = 1\<close> show ?thesis by simp
          qed
          finally have False by simp
        }
        moreover {
          assume "n < k"
          with ***** have "\<bar>g f k - g f' k\<bar> < 1 / (2 * 3^n)" by simp
          also have "\<dots> = 1 / (3^n) - 1 / (2 * 3^n)" by simp
          also have "\<dots> \<le> \<bar>g f n - g f' n\<bar> - \<bar>\<Sum>i \<in> {n + 1 .. k}. a f i - a f' i\<bar>" (is "_ \<le> _ - \<bar>?\<Delta>'\<bar>")
          proof -
            have "\<bar>g f n - g f' n\<bar> = 1 / (3^n)"
            proof -
              have "g f n - g f' n = a f n - a f' n" by (fact ****)
              also have "\<dots> = (f n - f' n) / (3^n)" unfolding a_def by algebra
              finally have "\<bar>g f n - g f' n\<bar> = \<bar>(f n - f' n) / (3^n)\<bar>" by simp
              also have "\<dots> = \<bar>f n - f' n\<bar> / (3^n)" by simp
              also from \<open>\<bar>f n - f' n\<bar> = 1\<close> have "\<dots> = 1 / (3^n)" by simp
              finally show ?thesis .
            qed
            moreover have "\<bar>?\<Delta>'\<bar> \<le> 1 / (2 * 3^n)"
            proof -
              have "?\<Delta>' \<le> 1 / (2 * 3^n)"
              proof -
                have "?\<Delta>' \<le> 1 / (2 * 3^n) - 1 / (2 * 3^k)"
                proof -
                  have \<delta>_sup: "a f i - a f' i \<le> 1 / (3^i)" for i
                  proof -
                    from f and f' consider
                      "f i = 1" and "f' i = 1"
                      | "f i = 1" and "f' i = 2"
                      | "f i = 2" and "f' i = 1"
                      | "f i = 2" and "f' i = 2"
                      by blast
                    thus ?thesis unfolding a_def by (cases, simp_all)
                  qed
                  from \<open>n < k\<close> have "n \<le> k" by simp
                  thus ?thesis
                  proof (induct rule: Nat.dec_induct)
                    case base
                    show ?case by simp
                  next
                    case (step k)
                    from step.hyps(1) have "(\<Sum>i \<in> {n + 1 .. Suc k}. a f i - a f' i) = (\<Sum>i \<in> {n + 1 .. k}. a f i - a f' i) + (a f (Suc k) - (a f' (Suc k)))" by simp
                    also from step.hyps(3) have "\<dots> \<le> 1 / (2 * 3^n) - (1 / (2 * 3^k)) + a f (k + 1) - a f' (k + 1)" by simp
                    also from \<delta>_sup[where i = "k + 1"] have "\<dots> \<le> 1 / (2 * 3^n) - (1 / (2 * 3^k)) + 1 / (3^(k + 1))" by simp
                    also have "\<dots> = 1 / (2 * 3^n) - (1 / (2 * 3^(Suc k)))" by simp
                    finally show ?case .
                  qed
                qed
                also have "\<dots> \<le> 1 / (2 * 3^n)" by simp
                finally show ?thesis .
              qed
              moreover have "-(1 / (2 * 3^n)) \<le> ?\<Delta>'"
              proof -
                have "-((1 :: rat) / (2 * 3^n)) \<le> 1 / (2 * 3^k) - (1 / (2 * 3^n))" by simp
                also have "\<dots> \<le> ?\<Delta>'"
                proof -
                  have \<delta>_inf: "-(1 / (3^i)) \<le> a f i - a f' i" for i
                  proof -
                    from f and f' consider
                      "f i = 1" and "f' i = 1"
                      | "f i = 1" and "f' i = 2"
                      | "f i = 2" and "f' i = 1"
                      | "f i = 2" and "f' i = 2" by blast
                    thus ?thesis unfolding a_def by (cases, simp_all)
                  qed
                  from \<open>n < k\<close> have "n \<le> k" by simp
                  thus ?thesis
                  proof (induct rule: Nat.dec_induct)
                    case base
                    show ?case by simp
                  next
                    case (step k)
                    have "(1 :: rat) / (2 * 3^(Suc k)) - (1 / (2 * 3^n)) = 1 / (2 * 3^k) - (1 / (2 * 3^n)) - (1 / (3^(k + 1)))" by simp
                    also from step.hyps(3) and \<delta>_inf[where i = "k + 1"] have "\<dots> \<le> (\<Sum>i \<in> {n + 1 .. k}. a f i - a f' i) + (a f (k + 1) - a f' (k + 1))" by simp
                    also from step.hyps(1) have "\<dots> = (\<Sum>i \<in> {n + 1 .. Suc k}. a f i - a f' i)" by simp
                    finally show ?case .
                  qed
                qed
                finally show ?thesis .
              qed
              ultimately show ?thesis by simp
            qed
            ultimately show ?thesis by simp
          qed
          also have "\<dots> \<le> \<bar>(g f n - g f' n) + ?\<Delta>'\<bar>" by simp
          also have "\<dots> = \<bar>g f k - g f' k\<bar>"
          proof -
            have "g f n - g f' n = (\<Sum>i \<in> {0 .. n}. a f i - a f' i)" (is "_ = ?\<Delta>")
              unfolding g_def by (simp only: sum_subtractf)
            hence "(g f n - g f' n) + ?\<Delta>' = ?\<Delta> + ?\<Delta>'" by simp
            also have "\<dots> = (\<Sum>i \<in> {0 .. k}. a f i - a f' i)" (is "_ = ?R")
            proof -
              have "finite {0 .. n}" by simp
              moreover have "finite {n + 1 .. k}" by simp
              moreover have "\<forall>i \<in> {0 .. n} \<inter> {n + 1 .. k}. a f i - a f' i = 0" by simp
              ultimately have "?\<Delta> + ?\<Delta>' = (\<Sum>i \<in> {0 .. n} \<union> {n + 1 .. k}. a f i - a f' i)"
                by (fact sum.union_inter_neutral[THEN sym])
              also have "\<dots> = ?R"
              proof -
                from \<open>n < k\<close> have "{0 .. n} \<union> {n + 1 .. k} = {0 .. k}" by auto
                thus ?thesis by simp
              qed
              finally show ?thesis .
            qed
            also have "\<dots> = g f k - g f' k" unfolding g_def by (simp only: sum_subtractf)
            finally show ?thesis by simp
          qed
          finally have "False" by simp
        }
        ultimately show False by linarith
      qed
    qed
    ultimately have "|(UNIV :: nat set) \<rightarrow>\<^sub>E {1 :: rat, 2 :: rat}| \<le>o |UNIV :: real set|" by auto
    thus ?thesis unfolding cexp_definition .
  qed
  finally show ?thesis .
qed

(* TODO:
lemma ctwo_cexp_aleph_naught_card_eq_aleph:
  shows "ctwo ^c \<aleph>\<^sub>0 =o \<aleph>"
proof -
  have "|UNIV :: (nat \<Rightarrow> bool) set| \<le>o |UNIV :: real set|"
  proof -
    have "ctwo ^c \<aleph>\<^sub>0 \<le>o \<aleph>" by (fact ctwo_cexp_aleph_naught_card_leq_aleph)
    thus ?thesis unfolding ctwo_definition and cexp_definition by simp
  qed
  moreover have "|UNIV :: real set| \<le>o |UNIV :: (nat \<Rightarrow> bool) set|"
  proof -
    have "\<aleph> \<le>o ctwo ^c \<aleph>\<^sub>0" by (fact aleph_card_leq_ctwo_cexp_aleph_naught)
    thus ?thesis unfolding ctwo_definition and cexp_definition by simp
  qed
  ultimately have "|UNIV :: (nat \<Rightarrow> bool) set| =o |UNIV :: real set|" by (fact thm_2_3_2)
  thus ?thesis unfolding cexp_definition and ctwo_definition by simp
qed
*)

(* TODO:
theorem thm_2_11_d:
  assumes "ctwo \<le>o |M|"
    and "|M| \<le>o \<aleph>\<^sub>0"
  shows "|M| ^c \<aleph>\<^sub>0 =o \<aleph>"
  sorry
*)

(* TODO:
theorem thm_2_11_e:
  assumes "cone \<le>o |M|"
    and "|M| \<le> \<aleph>"
  shows "|M| *c \<aleph> =o \<aleph>"
  sorry
*)

(* TODO:
theorem thm_2_11_f:
  assumes "ctwo \<le>o |M|"
    and "|M| \<le>o \<aleph>"
  shows "ctwo ^c \<aleph> =o \<aleph>\<^sub>0 ^c \<aleph>"
  sorry
*)

(* TODO:
proposition
  shows "equipotent ((UNIV :: nat set) \<times> (UNIV :: real set)) (UNIV :: real set)"
  sorry
*)

(* TODO:
proposition
  shows "equipotent ((UNIV :: real set) \<times> (UNIV :: real set)) (UNIV :: real set)"
  sorry
*)

(* TODO:
proposition
  shows "equipotent (Pow (UNIV :: nat set)) (UNIV :: real set)"
  sorry
*)

(* TODO:
proposition
  shows "equipotent ((UNIV :: nat set) \<rightarrow>\<^sub>E (UNIV :: bool set)) (UNIV :: real set)"
  sorry
*)

(* TODO:
proposition
  shows "equipotent ((UNIV :: nat set) \<rightarrow>\<^sub>E (UNIV :: nat set)) (UNIV :: real set)"
  sorry
*)

subsection \<open>Problems\<close>

proposition prob_2_3_1_a:
  shows "|M| +c |N| =o |N| +c |M|"
  by (fact prop_2_3_1)

proposition prob_2_3_1_b:
  shows "( |M| +c |N| ) +c |P| =o |M| +c ( |N| +c |P| )"
  by (fact prop_2_3_2)

proposition prob_2_3_1_c:
  shows "|M| +c czero =o |M|"
  by (fact prop_2_3_3)

proposition prob_2_3_1_d:
  assumes "|M| \<le>o |M'|"
    and "|N| \<le>o |N'|"
  shows "|M| +c |N| \<le>o |M'| +c |N'|"
  using assms by (fact prop_2_3_4)

proposition prob_2_3_1_e:
  shows "|M| *c |N| =o |N| *c |M|"
  by (fact prop_2_3_5)

proposition prob_2_3_1_f:
  shows "( |M| *c |N| ) *c |P| =o |M| *c ( |N| *c |P| )"
  by (fact prop_2_3_6)

proposition prob_2_3_1_g_a:
  shows "|M| *c czero =o czero"
  by (fact prop_2_3_7_a)

proposition prob_2_3_1_g_b:
  shows "|M| *c cone =o |M|"
  by (fact prop_2_3_7_b)

proposition prob_2_3_1_h:
  assumes "|M| \<le>o |M'|"
    and "|N| \<le>o |N'|"
  shows "|M| *c |N| \<le>o |M'| *c |N'|"
  using assms by (fact prop_2_3_8)

proposition prob_2_3_1_i:
  shows "( |M| +c |N| ) *c |P| =o |M| *c |P| +c |N| *c |P|"
  by (fact prop_2_3_9)

proposition prob_2_3_2:
  assumes "equipotent A A'"
    and "equipotent B B'"
  shows "equipotent (A \<times> B) (A' \<times> B')"
proof -
  from assms have "|A| =o |A'|" and "|B| =o |B'|" by auto
  hence "|A| *c |B| =o |A'| *c |B'|" by (fact cprod_cong')
  thus ?thesis unfolding cprod_definition by auto
qed

proposition prob_2_3_3:
  assumes "|N| \<le>o |N'|"
    and "|M| \<le>o |M'|"
    and "M = {} \<longleftrightarrow> M' = {}" \<comment> \<open>Is this assumption really necessary?\<close>
  shows "|N| ^c |M| \<le>o |N'| ^c |M'|"
  using assms by (fact prop_2_3_11)

(*
proposition prob_2_3_4:
  assumes "ctwo \<le>o |M|"
    and "|M| \<le> \<aleph>"
  shows "ctwo ^c \<aleph> =o |M| ^c \<aleph>"
  using assms sorry
*)

proposition prob_2_3_5:
  fixes M :: "'m set"
  assumes "infinite M"
  shows "|M| +c \<aleph>\<^sub>0 =o |M|"
proof -
  define N :: "('m + nat) set" where "N \<equiv> Inr ` UNIV"
  have "infinite (M <+> (UNIV :: nat set))" by simp
  moreover have "N \<subseteq> M <+> UNIV" unfolding N_def by auto
  moreover have "|N| \<le>o \<aleph>\<^sub>0" unfolding N_def by (fact card_of_image)
  moreover have "infinite ((M <+> UNIV) - N)"
  proof -
    have "(M <+> UNIV) - N = Inl ` M" unfolding N_def by auto
    moreover have "infinite (Inl ` M)"
    proof -
      have "inj_on Inl M" by simp
      with assms show ?thesis by (simp add: finite_image_iff)
    qed
    ultimately show ?thesis by simp
  qed
  ultimately have "equipotent ((M <+> UNIV) - N) (M <+> (UNIV :: nat set))" by (fact thm_2_6)
  moreover have "equipotent M ((M <+> UNIV) - N)"
  proof -
    have "bij_betw Inl M (Inl ` M)" by (metis bij_betw_imageI' image_eqI sum.inject(1))
    hence "equipotent M (Inl ` M)" by auto
    moreover have "Inl ` M = (M <+> UNIV) - N" unfolding N_def by auto
    ultimately show ?thesis by metis
  qed
  ultimately have "equipotent M (M <+> (UNIV :: nat set))" by (auto dest: prop_2_1_3)
  hence "|M| =o |M <+> (UNIV :: nat set)|" by auto
  thus ?thesis unfolding csum_definition by auto
qed

(*
proposition prob_2_3_6_a:
  assumes "cone \<le>o |M|"
    and "|M| \<le>o \<aleph>\<^sub>0"
  shows "\<aleph> ^c |M| =o \<aleph>"
  using assms sorry
*)

(*
proposition prob_2_3_6_b:
  assumes "|M| \<le>o \<ff>"
  shows "|M| +c \<ff> =o \<ff>"
  using assms sorry
*)

end (* context includes cardinal_syntax begin *)

end
