theory Section_2_3
  imports Main
    "HOL-Library.Disjoint_Sets"
    "HOL-Cardinals.Cardinal_Arithmetic"
    "Section_2_2"
begin

proposition csum_definition:
  fixes A :: "'a set"
    and B :: "'b set"
  (*assumes "Inl ` A \<inter> Inr ` B = {}"*)
  shows "|A| +c |B| =o |A <+> B|"
proof -
  have "|A| +c |B| =o |A <+> B|"
  proof -
    have "|A <+> B| =o |A| +c |B|" by (fact Plus_csum)
    thus "?thesis" by (fact ordIso_symmetric)
  qed
  also have "|A <+> B| =o |Inl ` A \<union> Inr ` B|" by (simp add: Plus_def)
  also have "|Inl ` A \<union> Inr ` B| =o |A <+> B|"
  proof -
    have "Inl ` A \<union> Inr ` B = A <+> B" by auto
    thus "?thesis" by simp
  qed
  finally show "?thesis" .
qed

proposition csum_definition_sym:
  shows "|A <+> B| =o |A| +c |B|"
  by (fact Plus_csum)

proposition prop_2_3_1:
  shows "|A| +c |B| =o |B| +c |A|"
proof -
  have "|A| +c |B| =o |A <+> B|" by (fact csum_definition)
  also have "|A <+> B| =o |B <+> A|" by (fact card_of_Plus_commute)
  also have "|B <+> A| =o |B| +c |A|" by (fact csum_definition_sym)
  finally show "?thesis" by simp
qed

fun sum_assoc_perm :: "('a + 'b) + 'c \<Rightarrow> 'a + ('b + 'c)" where
  "sum_assoc_perm (Inl (Inl a)) = Inl a"
| "sum_assoc_perm (Inl (Inr b)) = Inr (Inl b)"
| "sum_assoc_perm (Inr c) = Inr (Inr c)"

proposition prop_2_3_2:
  shows "( |A| +c |B| ) +c |C| =o |A| +c ( |B| +c |C| )"
proof -
  have "( |A| +c |B| ) +c |C| =o |A <+> B| +c |C|"
  proof -
    have "|A| +c |B| =o |A <+> B|" by (fact csum_definition)
    thus "?thesis" by (fact csum_cong1)
  qed
  also have "|A <+> B| +c |C| =o |(A <+> B) <+> C|" by (fact csum_definition)
  also have "|(A <+> B) <+> C| =o |A <+> (B <+> C)|"
  proof -
    have "inj_on sum_assoc_perm ((A <+> B) <+> C)"
    proof (intro inj_onI)
      fix x y
      assume "x \<in> (A <+> B) <+> C"
        and "y \<in> (A <+> B) <+> C"
        and "sum_assoc_perm x = sum_assoc_perm y"
      note this(3)
      moreover {
        fix a
        assume "x = Inl (Inl a)"
          and "sum_assoc_perm y = Inl a"
        note this(2)
        moreover {
          fix a'
          assume "y = Inl (Inl a')"
            and "Inl a = Inl a'"
          from this(2) have "a = a'" by simp
          with \<open>x = Inl (Inl a)\<close> and \<open>y = Inl (Inl a')\<close> have "x = y" by simp
        }
        moreover {
          fix b'
          assume "y = Inl (Inr b')"
            and "Inl a = Inr (Inl b')"
          from this(2) have "False" ..
        }
        moreover {
          fix c'
          assume "y = Inr c'"
            and "Inl a = Inr c'"
          from this(2) have "False" ..
        }
        ultimately have "x = y" by (auto elim: sum_assoc_perm.elims)
      }
      moreover {
        fix b
        assume "x = Inl (Inr b)"
          and "sum_assoc_perm y = Inr (Inl b)"
        note this(2)
        moreover {
          fix a'
          assume "y = Inl (Inl a')"
            and "Inl (Inr b) = Inl (Inl a')"
          from this(2) have "False" by simp
        }
        moreover {
          fix b'
          assume "y = Inl (Inr b')"
            and "Inl (Inr b) = Inl (Inr b')"
          from this(2) have "b = b'" by simp
          with \<open>x = Inl (Inr b)\<close> and \<open>y = Inl (Inr b')\<close> have "x = y" by simp
        }
        moreover {
          fix c'
          assume "y = Inr c'"
            and "Inl (Inr b) = Inr c'"
          from this(2) have "False" ..
        }
        ultimately have "x = y" by (auto elim: sum_assoc_perm.elims)
      }
      moreover {
        fix c
        assume "x = Inr c"
          and "sum_assoc_perm y = Inr (Inr c)"
        note this(2)
        moreover {
          fix a'
          assume "y = Inl (Inl a')"
            and "Inr (Inr c) = Inl (Inl a')"
          from this(2) have "False" ..
        }
        moreover {
          fix b'
          assume "y = Inl (Inr b')"
            and "Inr (Inr c) = Inl (Inr b')"
          from this(2) have "False" ..
        }
        moreover {
          fix c'
          assume "y = Inr c'"
            and "Inr c = Inr c'"
          from this(2) have "c = c'" ..
          with \<open>x = Inr c\<close> and \<open>y = Inr c'\<close> have "x = y" by simp
        }
        ultimately have "x = y" by (auto elim: sum_assoc_perm.elims)
      }
      ultimately show "x = y" by (fact sum_assoc_perm.elims)
    qed
    moreover have "sum_assoc_perm ` ((A <+> B) <+> C) = (A <+> (B <+> C))"
    proof (intro surj_onI)
      fix x
      assume "x \<in> (A <+> B) <+> C"
      moreover {
        fix ab
        assume "ab \<in> A <+> B"
          and "x = Inl ab"
        note this(1)
        moreover {
          fix a
          assume "a \<in> A"
            and "ab = Inl a"
          from this(2) and \<open>x = Inl ab\<close> have "x = Inl (Inl a)" by simp
          hence "sum_assoc_perm x = Inl a" by simp
          with \<open>a \<in> A\<close> have "sum_assoc_perm x \<in> A <+> (B <+> C)" by auto
        }
        moreover {
          fix b
          assume "b \<in> B"
            and "ab = Inr b"
          from this(2) and \<open>x = Inl ab\<close> have "x = Inl (Inr b)" by simp
          hence "sum_assoc_perm x = Inr (Inl b)" by simp
          with \<open>b \<in> B\<close> have "sum_assoc_perm x \<in> A <+> (B <+> C)" by auto
        }
        ultimately have "sum_assoc_perm x \<in> A <+> (B <+> C)" ..
      }
      moreover {
        fix c
        assume "c \<in> C"
          and "x = Inr c"
        from this(2) have "sum_assoc_perm x = Inr (Inr c)" by simp
        with \<open>c \<in> C\<close> have "sum_assoc_perm x \<in> A<+> (B <+> C)" by auto
      }
      ultimately show "sum_assoc_perm x \<in> A <+> (B <+> C)" ..
    next
      fix y
      assume "y \<in> A <+> (B <+> C)"
      moreover {
        fix a
        assume "a \<in> A"
          and "y = Inl a"
        from this(1) have "Inl (Inl a) \<in> (A <+> B) <+> C" by auto
        moreover have "sum_assoc_perm (Inl (Inl a)) = y"
        proof -
          have "sum_assoc_perm (Inl (Inl a)) = Inl a" by simp
          also from \<open>y = Inl a\<close> have "\<dots> = y" ..
          finally show "?thesis" .
        qed
        ultimately have "\<exists>x \<in> (A <+> B) <+> C. sum_assoc_perm x = y" ..
      }
      moreover {
        fix bc
        assume "bc \<in> B <+> C"
          and "y = Inr bc"
        note this(1)
        moreover {
          fix b
          assume "b \<in> B"
            and "bc = Inl b"
          from this(1) have "Inl (Inr b) \<in> (A <+> B) <+> C" by auto
          moreover have "sum_assoc_perm (Inl (Inr b)) = y"
          proof -
            have "sum_assoc_perm (Inl (Inr b)) = Inr (Inl b)" by simp
            also from \<open>bc = Inl b\<close> and \<open>y = Inr bc\<close> have "\<dots> = y" by simp
            finally show "?thesis" .
          qed
          ultimately have "\<exists>x \<in> (A <+> B) <+> C. sum_assoc_perm x = y" ..
        }
        moreover {
          fix c
          assume "c \<in> C"
            and "bc = Inr c"
          from this(1) have "Inr c \<in> (A <+> B) <+> C" ..
          moreover have "sum_assoc_perm (Inr c) = y"
          proof -
            have "sum_assoc_perm (Inr c) = Inr (Inr c)" by simp
            also from \<open>bc = Inr c\<close> and \<open>y = Inr bc\<close> have "\<dots> = y" by simp
            finally show "?thesis" .
          qed
          ultimately have "\<exists>x \<in> (A <+> B) <+> C. sum_assoc_perm x = y" ..
        }
        ultimately have "\<exists>x \<in> (A <+> B) <+> C. sum_assoc_perm x = y" ..
      }
      ultimately show "\<exists>x \<in> (A <+> B) <+> C. sum_assoc_perm x = y" ..
    qed
    ultimately have "bij_betw sum_assoc_perm ((A <+> B) <+> C) (A <+> (B <+> C))"
      by (fact bij_betw_imageI)
    thus "?thesis" by auto
  qed
  also have "|A <+> (B <+> C)| =o |A| +c |B <+> C|" by (fact csum_definition_sym)
  also have "|A| +c |B <+> C| =o |A| +c ( |B| +c |C| )"
  proof -
    have "|B <+> C| =o |B| +c |C|" by (fact csum_definition_sym)
    thus "?thesis" by (fact csum_cong2)
  qed
  finally show "?thesis" .
qed

lemma bijbetw_Inl:
  shows "|Inl ` A| =o |A|"
proof -
  have "inj_on Inl A" by simp
  hence "bij_betw Inl A (Inl ` A)" by (fact inj_on_imp_bij_betw)
  hence "|A| =o |Inl ` A|" by auto
  thus "?thesis" by (fact card_eq_sym)
qed

proposition prop_2_3_3:
  fixes A :: "'a set"
  shows "|A| +c czero =o |A|"
proof -
  have "|A| +c czero =o |A| +c |{} :: 'b set|"
  proof -
    have "czero =o |{} :: 'b set|" by (fact czero_definition)
    thus "?thesis" by (fact csum_cong2)
  qed
  also have "|A| +c |{} :: 'b set| =o |A <+> ({} :: 'b set)|" by (fact csum_definition)
  also have "|A <+> ({} :: 'b set)| =o |(Inl ` A) :: ('a + 'b) set|"
  proof -
    have "A <+> ({} :: 'b set) = Inl ` A" by auto
    thus "?thesis" by simp
  qed
  also have "|Inl ` A| =o |A|" by (fact bijbetw_Inl)
  finally show "?thesis" .
qed

proposition prop_2_3_4:
  assumes "|A| \<le>o |A'|"
    and "|B| \<le>o |B'|"
  shows "|A| +c |B| \<le>o |A'| +c |B'|"
proof -
  from assms(1) obtain f where "f ` A \<subseteq> A'" and "inj_on f A" ..
  from assms(2) obtain g where "g ` B \<subseteq> B'" and "inj_on g B" ..
  have "|A| +c |B| =o |A <+> B|" by (fact csum_definition)
  also have "|A <+> B| \<le>o |A' <+> B'|"
  proof -
    let ?h = "map_sum f g"
    have "?h ` (A <+> B) \<subseteq> A' <+> B'"
    proof (intro image_subsetI)
      fix x
      assume "x \<in> A <+> B"
      moreover {
        fix a
        assume "a \<in> A"
          and "x = Inl a"
        from this(2) have "?h x = Inl (f a)" by simp
        also from \<open>a \<in> A\<close> and \<open>f ` A \<subseteq> A'\<close> have "\<dots> \<in> A' <+> B'" by auto
        finally have "?h x \<in> A' <+> B'" .
      }
      moreover {
        fix b
        assume "b \<in> B"
          and "x = Inr b"
        from this(2) have "?h x = Inr (g b)" by simp
        also from \<open>b \<in> B\<close> and \<open>g ` B \<subseteq> B'\<close> have "\<dots> \<in> A' <+> B'" by auto
        finally have "?h x \<in> A' <+> B'" .
      }
      ultimately show "?h x \<in> A' <+> B'" ..
    qed
    moreover have "inj_on ?h (A <+> B)"
    proof (intro inj_onI)
      fix x y
      assume "x \<in> A <+> B"
        and "y \<in> A <+> B"
        and "?h x = ?h y"
      note this(1)
      moreover {
        fix a
        assume "a \<in> A"
          and "x = Inl a"
        note \<open>y \<in> A <+> B\<close>
        moreover {
          fix a'
          assume "a' \<in> A"
            and "y = Inl a'"
          from this(2) and \<open>x = Inl a\<close> and \<open>?h x = ?h y\<close> have "?h (Inl a) = ?h (Inl a')" by simp
          hence "Inl (f a) = Inl (f a')" by simp
          hence "f a = f a'" ..
          with \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and \<open>inj_on f A\<close> have "a = a'" by (elim inj_onD)
          with \<open>x = Inl a\<close> and \<open>y = Inl a'\<close> have "x = y" by simp
        }
        moreover {
          fix b'
          assume "b' \<in> B"
            and "y = Inr b'"
          from this(2) and \<open>x = Inl a\<close> and \<open>?h x = ?h y\<close> have "?h (Inl a) = ?h (Inr b')" by simp
          hence "Inl (f a) = Inr (g b')" by simp
          hence "False" ..
        }
        ultimately have "x = y" by auto
      }
      moreover {
        fix b
        assume "b \<in> B"
          and "x = Inr b"
        note \<open>y \<in> A <+> B\<close>
        moreover {
          fix a'
          assume "a' \<in> A"
            and "y = Inl a'"
          from this(2) and \<open>x = Inr b\<close> and \<open>?h x = ?h y\<close> have "Inr (g b) = Inl (f a')" by simp
          hence "False" ..
        }
        moreover {
          fix b'
          assume "b' \<in> B"
            and "y = Inr b'"
          from this(2) and \<open>x = Inr b\<close> and \<open>?h x = ?h y\<close> have "Inr (g b) = Inr (g b')" by simp
          hence "g b = g b'" ..
          with \<open>b \<in> B\<close> and \<open>b' \<in> B\<close> and \<open>inj_on g B\<close> have "b = b'" by (elim inj_onD)
          with \<open>x = Inr b\<close> and \<open>y = Inr b'\<close> have "x = y" by simp
        }
        ultimately have "x = y" by auto
      }
      ultimately show "x = y" ..
    qed
    ultimately show "?thesis" ..
  qed
  also have "|A' <+> B'| =o |A'| +c |B'|" by (fact csum_definition_sym)
  finally show "?thesis" .
qed

proposition cprod_definition:
  shows "|A| *c |B| =o |A \<times> B|"
proof -
  have "|A \<times> B| =o |A| *c |B|" by (fact Times_cprod)
  thus "?thesis" by (fact ordIso_symmetric)
qed

proposition prop_2_3_5:
  shows "|A| *c |B| =o |B| *c |A|"
  by (fact cprod_com)

proposition prop_2_3_6:
  shows "( |A| *c |B| ) *c |C| =o |A| *c ( |B| *c |C| )"
  by (fact cprod_assoc)

proposition prop_2_3_7_a:
  shows "|A| *c czero =o czero"
  by (fact cprod_czero)

lemma czero_cprod_absorb2_sym:
  shows "czero =o |A| *c czero"
  by (auto intro: prop_2_3_7_a ordIso_symmetric)

lemma czero_cprod_cong2:
  assumes "B = {}"
  shows "|A| *c czero =o |A| *c |B|"
  by (simp only: assms czero_definition cprod_cong2)

proposition prop_2_3_7_b:
  shows "|A| *c cone =o |A|"
  by (simp add: cprod_cone)

proposition prop_2_3_8:
  assumes "|A| \<le>o |B|"
    and "|A'| \<le>o |B'|"
  shows "|A| *c |A'| \<le>o |B| *c |B'|"
  using assms by (fact cprod_mono)

proposition prop_2_3_9:
  shows "|A| *c ( |B| +c |C| ) =o |A| *c |B| +c |A| *c |C|"
proof -
  have "|A| *c ( |B| +c |C| ) =o |A| *c |B <+> C|"
  proof -
    have "|B <+> C| =o |B| +c |C|" by (fact Plus_csum)
    hence "|B| +c |C| =o |B <+> C|" by (fact ordIso_symmetric)
    thus "?thesis" by (fact cprod_cong2)
  qed
  also have "|A| *c |B <+> C| =o |A \<times> (B <+> C)|" by (fact cprod_definition)
  also have "|A \<times> (B <+> C)| =o |A \<times> B <+> A \<times> C|" by (fact card_of_Times_Plus_distrib)
  also have "|A \<times> B <+> A \<times> C| =o |A \<times> B| +c |A \<times> C|" by (fact Plus_csum)
  also have "|A \<times> B| +c |A \<times> C| =o |A| *c |B| +c |A| *c |C|"
  proof -
    have "|A \<times> B| =o |A| *c |B|" by (fact Times_cprod)
    moreover have "|A \<times> C| =o |A| *c |C|" by (fact Times_cprod)
    ultimately show "?thesis" by (fact csum_cong)
  qed
  finally show "?thesis" .
qed

theorem thm_2_9:
  fixes A :: "'b \<Rightarrow> 'a set"
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> |A l| =o \<mm>"
    and "\<Lambda> = {} \<Longrightarrow> \<exists>X. |X| = \<mm>" -- \<open>This assumption guarantees that @{term "\<mm>"} is a cardinal
                                      number even if @{prop "\<Lambda> = {}"}.\<close>
    and "disjoint_family_on A \<Lambda>"
  shows "|\<Union>l \<in> \<Lambda>. A l| =o \<mm> *c |\<Lambda>|"
proof -
  let ?B = "\<Union>l \<in> \<Lambda>. A l"
  {
    assume "\<Lambda> = {}"
    with assms(2) obtain X where "|X| = \<mm>" by auto
    from \<open>\<Lambda> = {}\<close> have "?B = {}" by simp
    hence "|?B| =o czero" by (fact eq_empty_imp_card_eq_czero)
    also have "czero =o |X| *c czero" by (fact czero_cprod_absorb2_sym)
    also from \<open>\<Lambda> = {}\<close> have "|X| *c czero =o |X| *c |\<Lambda>|" by (fact czero_cprod_cong2)
    also from \<open>|X| = \<mm>\<close> have "|X| *c |\<Lambda>| = \<mm> *c |\<Lambda>|" by simp
    finally have "|?B| =o \<mm> *c |\<Lambda>|" .
  }
  moreover {
    assume "\<Lambda> \<noteq> {}"
    then obtain l\<^sub>0 where "l\<^sub>0 \<in> \<Lambda>" by auto
    hence "|A l\<^sub>0| =o \<mm>" by (auto dest: assms(1))
    {
      fix l
      assume "l \<in> \<Lambda>"
      hence "|A l| =o \<mm>" by (auto dest: assms(1))
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
      with \<open>l \<in> \<Lambda>\<close> show "\<exists>a \<in> A l\<^sub>0. \<exists>l \<in> \<Lambda>. f l a = b" by auto
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
        with \<open>l \<in> \<Lambda>\<close> and \<open>l' \<in> \<Lambda>\<close> and assms(3) have "A l \<inter> A l' = {}"
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
      from \<open>l\<^sub>0 \<in> \<Lambda>\<close> have "|A l\<^sub>0| =o \<mm>" by (fact assms(1))
      thus "?thesis" by (fact cprod_cong1)
    qed
    finally have "|?B| =o \<mm> *c |\<Lambda>|" .
  }
  ultimately show "?thesis" by blast
qed

proposition cexp_definition:
  shows "|B| ^c |A| =o |A \<rightarrow>\<^sub>E B|"
proof -
  have "|B| ^c |A| =o |Func A B|" by (simp add: cexp_def)
  also have "|Func A B| =o |A \<rightarrow>\<^sub>E B|"
  proof -
    have "Func A B = A \<rightarrow>\<^sub>E B" by (auto simp: Func_def)
    thus "?thesis" by simp
  qed
  finally show "?thesis" .
qed

lemma cexp_definition_sym:
  shows "|A \<rightarrow>\<^sub>E B| =o |B| ^c |A|"
  by (auto intro: ordIso_symmetric cexp_definition)

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

lemma cexp_cong1:
  fixes M :: "'m set"
    and N :: "'n set"
    and P :: "'p set"
  assumes "\<mm> = |M|"
    and "\<nn> = |N|"
    and "\<pp> = |P|"
    and "\<mm> =o \<nn>"
  shows "\<mm> ^c \<pp> =o \<nn> ^c \<pp>"
proof -
  have "|M| ^c |P| =o |P \<rightarrow>\<^sub>E M|" by (fact cexp_definition)
  moreover have "|P \<rightarrow>\<^sub>E M| =o |P \<rightarrow>\<^sub>E N|"
  proof -
    from assms(1,2,4) have "|M| =o |N|" by simp
    then obtain h where "bij_betw h M N" by auto
    then obtain h' where "id_on (h' \<circ> h) M" by (rule bij_betw_imp_id_on_comp)
    from \<open>bij_betw h M N\<close> and \<open>id_on (h' \<circ> h) M\<close> have "id_on (h \<circ> h') N" by fastforce
    have "bij_betw h' N M"
      using \<open>bij_betw h M N\<close> \<open>id_on (h' \<circ> h) M\<close> bij_betw_comp_iff id_on_imp_bij_betw by blast
    define \<phi> where "\<phi> f \<equiv> \<lambda>p. if p \<in> P then h (f p) else undefined" for f
    have "inj_on \<phi> (P \<rightarrow>\<^sub>E M)"
    proof (rule inj_onI)
      fix f f'
      assume "f \<in> P \<rightarrow>\<^sub>E M"
        and "f' \<in> P \<rightarrow>\<^sub>E M"
        and "\<phi> f = \<phi> f'"
      {
        fix p
        assume "p \<in> P"
        from \<open>\<phi> f = \<phi> f'\<close> have "(\<phi> f) p = (\<phi> f') p" by simp
        with \<phi>_def and \<open>p \<in> P\<close> have "h (f p) = h (f' p)" by simp
        hence "(h' \<circ> h) (f p) = (h' \<circ> h) (f' p)" by simp
        moreover have "(h' \<circ> h) (f p) = f p"
        proof -
          from \<open>f \<in> P \<rightarrow>\<^sub>E M\<close> and \<open>p \<in> P\<close> have "f p \<in> M" by auto
          with \<open>id_on (h' \<circ> h) M\<close> show ?thesis ..
        qed
        moreover have "(h' \<circ> h) (f' p) = f' p"
        proof -
          from \<open>f' \<in> P \<rightarrow>\<^sub>E M\<close> and \<open>p \<in> P\<close> have "f' p \<in> M" by auto
          with \<open>id_on (h' \<circ> h) M\<close> show ?thesis ..
        qed
        ultimately have "f p = f' p" by simp
      }
      with \<open>f \<in> P \<rightarrow>\<^sub>E M\<close> and \<open>f' \<in> P \<rightarrow>\<^sub>E M\<close> show "f = f'" by fastforce
    qed
    moreover have "\<phi> ` (P \<rightarrow>\<^sub>E M) = P \<rightarrow>\<^sub>E N"
    proof (rule surj_onI)
      fix f
      assume "f \<in> P \<rightarrow>\<^sub>E M"
      {
        fix p
        assume "p \<in> P"
        with \<phi>_def have "\<phi> f p = h (f p)" by simp
        also from \<open>p \<in> P\<close> and \<open>f \<in> P \<rightarrow>\<^sub>E M\<close> and \<open>bij_betw h M N\<close> have "\<dots> \<in> N" by auto
        finally have "\<phi> f p \<in> N" by simp
      }
      moreover{
        fix p
        assume "p \<notin> P"
        with \<phi>_def have "\<phi> f p = undefined" by simp
      }
      ultimately show "\<phi> f \<in> P \<rightarrow>\<^sub>E N" ..
    next
      fix g
      assume "g \<in> P \<rightarrow>\<^sub>E N"
      define f'' where "f'' p \<equiv> if p \<in> P then h' (g p) else undefined" for p
      have "f'' \<in> P \<rightarrow>\<^sub>E M"
      proof (rule PiE_I)
        fix p
        assume "p \<in> P"
        with f''_def have "f'' p = h' (g p)" by simp
        also from \<open>p \<in> P\<close> and \<open>g \<in> P \<rightarrow>\<^sub>E N\<close> and \<open>bij_betw h' N M\<close> have "\<dots> \<in> M" by auto
        finally show "f'' p \<in> M" by simp
      next
        fix p
        assume "p \<notin> P"
        with f''_def show "f'' p = undefined" by simp
      qed
      moreover have "\<phi> f'' = g"
      proof (rule ext)
        fix p
        consider "p \<in> P" | "p \<notin> P" by auto
        moreover{
          assume "p \<in> P"
          with \<phi>_def have "(\<phi> f'') p = h (f'' p)" by simp
          also from \<open>p \<in> P\<close> and f''_def have "\<dots> = h (h' (g p))" by simp
          also from \<open>p \<in> P\<close> and \<open>g \<in> P \<rightarrow>\<^sub>E N\<close> and \<open>id_on (h \<circ> h') N\<close> have "\<dots> = g p" by auto
          finally have "(\<phi> f'') p = g p" .
        }
        moreover {
          assume "p \<notin> P"
          with \<phi>_def have "(\<phi> f'') p = undefined" by simp
          also from \<open>p \<notin> P\<close> and \<open>g \<in> P \<rightarrow>\<^sub>E N\<close> have "\<dots> = g p" by auto
          finally have "(\<phi> f'') p = g p" .
        }
        ultimately show "\<phi> f'' p = g p" by auto
      qed
      ultimately show "\<exists>f'' \<in> P \<rightarrow>\<^sub>E M. \<phi> f'' = g" by auto
    qed
    ultimately have "bij_betw \<phi> (P \<rightarrow>\<^sub>E M) (P \<rightarrow>\<^sub>E N)" by (fact bij_betw_imageI)
    thus ?thesis by auto
  qed
  ultimately have "|M| ^c |P| =o |P \<rightarrow>\<^sub>E N|" by (fact ordIso_transitive)
  moreover have "|P \<rightarrow>\<^sub>E N| =o |N| ^c |P|" by (fact cexp_definition_sym)
  ultimately have "|M| ^c |P| =o |N| ^c |P|" by (fact ordIso_transitive)
  with assms(1-3) show ?thesis by simp
qed

lemma cexp_cong2:
  fixes M :: "'m set"
    and P :: "'p set"
    and Q :: "'q set"
  assumes "\<mm> = |M|"
    and "\<pp> = |P|"
    and "\<qq> = |Q|"
    and "\<pp> =o \<qq>"
  shows "\<mm> ^c \<pp> =o \<mm> ^c \<qq>"
proof -
  from assms(2-4) have "|P| =o |Q|" by simp
  then obtain h where "bij_betw h P Q" by auto
  moreover define h' where "h' \<equiv> inv_into P h"
  ultimately have "bij_betw h' Q P" by (simp add: bij_betw_inv_into)
  from \<open>bij_betw h P Q\<close> and h'_def have "id_on (h' \<circ> h) P" and "id_on (h \<circ> h') Q" by fastforce+
  define \<phi> where "\<phi> g \<equiv> \<lambda>p. if p \<in> P then g (h p) else undefined" for g :: "'q \<Rightarrow> 'm"
  have "bij_betw \<phi> (Q \<rightarrow>\<^sub>E M) (P \<rightarrow>\<^sub>E M)"
  proof (rule bij_betw_imageI)
    {
      fix g g'
      assume "g \<in> Q \<rightarrow>\<^sub>E M"
        and "g' \<in> Q \<rightarrow>\<^sub>E M"
        and "\<phi> g = \<phi> g'"
      {
        fix q
        consider "q \<in> Q" | "q \<notin> Q" by auto
        moreover {
          assume "q \<in> Q"
          with \<open>bij_betw h P Q\<close> obtain p where "p \<in> P" and "h p = q" by auto
          with \<open>p \<in> P\<close> and \<open>\<phi> g = \<phi> g'\<close> and \<phi>_def have "g (h p) = g' (h p)" by metis
          with \<open>h p = q\<close> have "g q = g' q" by simp
        }
        moreover {
          assume "q \<notin> Q"
          with \<open>g \<in> Q \<rightarrow>\<^sub>E M\<close> and \<open>g' \<in> Q \<rightarrow>\<^sub>E M\<close> have "g q = g' q" by fastforce
        }
        ultimately have "g q = g' q" by auto
      }
      hence "g = g'" ..
    }
    thus "inj_on \<phi> (Q \<rightarrow>\<^sub>E M)" by (fact inj_onI)
  next
    {
      fix g
      assume "g \<in> Q \<rightarrow>\<^sub>E M"
      {
        fix p
        assume "p \<in> P"
        with \<phi>_def have "\<phi> g p = g (h p)" by simp
        also from \<open>p \<in> P\<close> and \<open>bij_betw h P Q\<close> and \<open>g \<in> Q \<rightarrow>\<^sub>E M\<close> have "\<dots> \<in> M" by auto
        finally have "\<phi> g p \<in> M" .
      }
      moreover {
        fix p
        assume "p \<notin> P"
        with \<phi>_def have "\<phi> g p = undefined" by simp
      }
      ultimately have "\<phi> g \<in> P \<rightarrow>\<^sub>E M" by auto
    }
    moreover {
      fix f
      assume "f \<in> P \<rightarrow>\<^sub>E M"
      define g where "g q \<equiv> if q \<in> Q then f (h' q) else undefined" for q
      have "g \<in> Q \<rightarrow>\<^sub>E M"
      proof (rule PiE_I)
        fix q
        assume "q \<in> Q"
        with g_def and \<open>bij_betw h' Q P\<close> and \<open>f \<in> P \<rightarrow>\<^sub>E M\<close> show "g q \<in> M" by auto
      next
        fix q
        assume "q \<notin> Q"
        with g_def show "g q = undefined" by simp
      qed
      moreover have "\<phi> g = f"
      proof (rule ext)
        fix p
        consider "p \<in> P" | "p \<notin> P" by auto
        moreover {
          assume "p \<in> P"
          with \<phi>_def have "\<phi> g p = g (h p)" by simp
          moreover from \<open>p \<in> P\<close> and \<open>bij_betw h P Q\<close> have "h p \<in> Q" by auto
          moreover note g_def
          ultimately have "\<phi> g p = f (h' (h p))" by simp
          with \<open>p \<in> P\<close> and \<open>id_on (h' \<circ> h) P\<close> have "\<phi> g p = f p" by auto
        }
        moreover {
          assume "p \<notin> P"
          with \<phi>_def \<open>f \<in> P \<rightarrow>\<^sub>E M\<close> have "\<phi> g p = f p" by auto
        }
        ultimately show "\<phi> g p = f p" by auto
      qed
      ultimately have "\<exists>g \<in> Q \<rightarrow>\<^sub>E M. \<phi> g = f" by auto
    }
    ultimately show "\<phi> ` (Q \<rightarrow>\<^sub>E M) = (P \<rightarrow>\<^sub>E M)" by (fact surj_onI)
  qed
  from assms(1,2) have "\<mm> ^c \<pp> = |M| ^c |P|" by simp
  also have "\<dots> =o |P \<rightarrow>\<^sub>E M|" by (fact cexp_definition)
  finally have "\<mm> ^c \<pp> =o |P \<rightarrow>\<^sub>E M|" .
  moreover have "|P \<rightarrow>\<^sub>E M| =o |Q \<rightarrow>\<^sub>E M|"
  proof (rule ordIso_symmetric)
    from \<open>bij_betw \<phi> (Q \<rightarrow>\<^sub>E M) (P \<rightarrow>\<^sub>E M)\<close> show "|Q \<rightarrow>\<^sub>E M| =o |P \<rightarrow>\<^sub>E M|" by auto
  qed
  ultimately have "\<mm> ^c \<pp> =o |Q \<rightarrow>\<^sub>E M|" by (rule ordIso_transitive)
  also have "|Q \<rightarrow>\<^sub>E M| =o |M| ^c |Q|" by (rule cexp_definition_sym)
  also from assms(1,3) have "|M| ^c |Q| = \<mm> ^c \<qq>" by simp 
  finally show "\<mm> ^c \<pp> =o \<mm> ^c \<qq>" .
qed

proposition prop_2_3_10_a:
  shows "|A| ^c |{x}| =o |A|"
proof -
  have "|A| ^c |{x}| =o |{x} \<rightarrow>\<^sub>E A|" by (fact cexp_definition)
  also have "|{x} \<rightarrow>\<^sub>E A| =o |A|"
  proof -
    let ?f = "\<lambda>a. \<lambda>y. if y = x then a else undefined"
    have "?f ` A = {x} \<rightarrow>\<^sub>E A"
    proof (rule surj_onI)
      fix a'
      assume "a' \<in> A"
      {
        fix x'
        assume "x' \<in> {x}"
        with \<open>a' \<in> A\<close> have "?f a' x' \<in> A" by simp
      }
      moreover {
        fix x'
        assume "x' \<notin> {x}"
        hence "?f a' x' = undefined" by simp
      }
      ultimately show "?f a' \<in> {x} \<rightarrow>\<^sub>E A" by (fact PiE_I)
    next
      fix g
      assume "g \<in> {x} \<rightarrow>\<^sub>E A"
      hence "g x \<in> A" by auto
      moreover {
        fix x'
        {
          assume "x' \<in> {x}"
          hence "?f (g x) x' = g x'" by simp
        }
        moreover {
          assume "x' \<notin> {x}"
          with \<open>g \<in> {x} \<rightarrow>\<^sub>E A\<close> have "?f (g x) x' = g x'" by fastforce
        }
        ultimately have "?f (g x) x' = g x'" by simp
      }
      ultimately show "\<exists>a' \<in> A. ?f a' = g" by auto
    qed
    moreover have "inj_on ?f A"
    proof (rule inj_onI)
      fix a and a'
      assume "a \<in> A" and "a' \<in> A" and "?f a = ?f a'"
      thus "a = a'" by metis
    qed
    ultimately have "bij_betw ?f A ({x} \<rightarrow>\<^sub>E A)" by (intro bij_betw_imageI)
    hence "|A| =o |{x} \<rightarrow>\<^sub>E A|" by auto
    thus "|{x} \<rightarrow>\<^sub>E A| =o |A|" by (fact ordIso_symmetric)
  qed
  finally show "?thesis" .
qed

proposition prop_2_3_10_b:
  shows "cone ^c |A| =o cone"
  by (fact cone_cexp)

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
  have "|A| ^c |B| =o |B \<rightarrow>\<^sub>E A|" by (fact cexp_definition)
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
  also have "|B' \<rightarrow>\<^sub>E A'| =o |A'| ^c |B'|" by (fact cexp_definition_sym)
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
  (*assumes "Inl ` A \<inter> Inr ` B = {}"*)
  shows "|C| ^c |A| *c |C| ^c |B| =o |C| ^c ( |A| +c |B| )"
proof -
  let ?f = "\<lambda>\<phi> :: 'a + 'b \<Rightarrow> 'c. (\<lambda>a. \<phi> (Inl a), \<lambda>b. \<phi> (Inr b))"
  have "|C| ^c |A| *c |C| ^c |B| =o |A \<rightarrow>\<^sub>E C| *c |C| ^c |B|"
  proof -
    have "|C| ^c |A| =o |A \<rightarrow>\<^sub>E C|" by (fact cexp_definition)
    thus "?thesis" by (fact cprod_cong1)
  qed
  also have "|A \<rightarrow>\<^sub>E C| *c |C| ^c |B| =o |A \<rightarrow>\<^sub>E C| *c |B \<rightarrow>\<^sub>E C|"
  proof -
    have "|C| ^c |B| =o |B \<rightarrow>\<^sub>E C|" by (fact cexp_definition)
    thus "?thesis" by (fact cprod_cong2)
  qed
  also have "|A \<rightarrow>\<^sub>E C| *c |B \<rightarrow>\<^sub>E C| =o |(A \<rightarrow>\<^sub>E C) \<times> (B \<rightarrow>\<^sub>E C)|" by (fact cprod_definition)
  also have "|(A \<rightarrow>\<^sub>E C) \<times> (B \<rightarrow>\<^sub>E C)| =o |A <+> B \<rightarrow>\<^sub>E C|"
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
      ultimately show "\<exists>s \<in> ?S. ?f s = t" by auto
    qed
    ultimately have "bij_betw ?f ((A \<rightarrow>\<^sub>E C) \<times> (B \<rightarrow>\<^sub>E C)) ( A<+> B \<rightarrow>\<^sub>E C)" by (fact bij_betw_imageI)
    thus "?thesis" by auto
  qed
  also have "|A <+> B \<rightarrow>\<^sub>E C| =o |C| ^c |A <+> B|" by (fact cexp_definition_sym)
  also have "|C| ^c |A <+> B| =o |C| ^c ( |A| +c |B| )"
  proof -
    have "|A <+> B| =o ( |A| +c |B| )" by (fact Plus_csum)
    thus "?thesis" by (fact cexp_cong2)
  qed
  finally show "?thesis" by simp
qed

theorem thm_2_10_b:
  fixes P :: "'p set"
    and M :: "'m set"
    and N :: "'n set"
  assumes "\<pp> = |P|"
    and "\<mm> = |M|"
    and "\<nn> = |N|"
  shows "(\<mm> *c \<nn>) ^c \<pp> =o \<mm> ^c \<pp> *c \<nn> ^c \<pp>"
proof -
  define \<FF> where "\<FF> f \<equiv> (fst \<circ> f, snd \<circ> f)" for f :: "'p \<Rightarrow> 'm \<times> 'n"
  have "bij_betw \<FF> (P \<rightarrow>\<^sub>E M \<times> N) ((P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N))" sorry
  have "(\<mm> *c \<nn>) ^c \<pp> =o "
  hence "|P \<rightarrow>\<^sub>E M \<times> N| =o |(P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N)|" by auto
  moreover have "|M \<times> N| ^c |P| =o |P \<rightarrow>\<^sub>E M \<times> N|" by (fact cexp_definition)
  ultimately have "|M \<times> N| ^c |P| =o |(P \<rightarrow>\<^sub>E M) \<times> (P \<rightarrow>\<^sub>E N)|" 
  hence "( |A| *c |B| ) ^c |C| =o |A \<times> B| ^c |C|" try
qed

theorem thm_2_10_c:
  shows "|C| ^c |A| ^c |B| =o |C| ^c ( |A| *c |B| )"
  sorry

end
