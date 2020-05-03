theory Section_2_2
  imports Complex_Main
    "HOL-Library.Cardinal_Notations"
    "Split_Pair"
    "Section_2_1"
begin

fun dc_seq :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a set" where
"dc_seq M a 0 = {}" |
"dc_seq M a (Suc n) = dc_seq M a n \<union> {a (M - dc_seq M a n)}"

lemma finite_dc_seq:
  shows "finite (dc_seq M a n)"
proof (induct n)
  case 0
  show "?case" by simp
next
  case (Suc n)
  from Suc.hyps show "?case" by simp
qed

lemma strict_dec_induct [consumes 1, case_names base step]:
  assumes "i < j"
    and "P (Suc i)"
    and "\<And>j. i < j \<Longrightarrow> P j \<Longrightarrow> P (Suc j)"
  shows "P j"
proof -
  let ?P = "\<lambda>n. P (n + i + 1)"
  have "?P n" for n
  proof (induct n)
    case 0
    from assms(2) show "?P 0" by simp
  next
    case (Suc n)
    note \<open>?P n\<close>
    from Suc.hyps have "P (n + i + 1)" by simp
    moreover have "i < n + i + 1" by simp
    ultimately have "P (Suc (n + i + 1))" by (intro assms(3))
    thus "?P (Suc n)" by simp
  qed
  from assms(1) obtain k where "j = Suc (i + k)" by (auto dest: less_imp_Suc_add)
  hence "j = k + i + 1" by simp
  with \<open>?P k\<close> show "P j" by simp
qed

theorem thm_2_4:
  assumes "infinite M"
  obtains A where "A \<subseteq> M" and "|A| =o \<aleph>\<^sub>0"
proof -
  let ?\<MM> = "Pow M - {{}}"
  {
    fix A
    assume "A \<in> ?\<MM>"
    hence "A \<noteq> {}" by simp
  }
  then obtain a where "a \<in> (\<Pi> A \<in> ?\<MM>. A)" by (elim AC_E)
  have *: "dc_seq M a n \<subset> M" for n
  proof (induct n)
    case 0
    from assms have "M \<noteq> {}" by auto
    thus "?case" by auto
  next
    case (Suc n)
    from Suc.hyps have "M - dc_seq M a n \<noteq> {}" by auto
    moreover have "M - dc_seq M a n \<subseteq> M" by auto
    ultimately have "M - dc_seq M a n \<in> ?\<MM>" by simp
    with \<open>a \<in> (\<Pi> A \<in> ?\<MM>. A)\<close> have "a (M - dc_seq M a n) \<in> M - dc_seq M a n" by (fact Pi_mem)
    also have "M - dc_seq M a n \<subseteq> M" by auto
    finally have "a (M - dc_seq M a n) \<in> M" .
    moreover note Suc.hyps
    ultimately have "dc_seq M a (Suc n) \<subseteq> M" by simp
    moreover from assms and finite_dc_seq have "dc_seq M a (Suc n) \<noteq> M" by metis
    ultimately show "?case" by auto
  qed
  hence "M - dc_seq M a n \<in> ?\<MM>" for n by auto
  let ?A = "\<Union>n. dc_seq M a n"
  let ?f = "\<lambda>n. a (M - dc_seq M a n)"
  have **: "?f n \<in> M - dc_seq M a n" for n
    using \<open>a \<in> (\<Pi> A \<in> ?\<MM>. A)\<close> and \<open>M - dc_seq M a n \<in> ?\<MM>\<close> by (fact Pi_mem)
  have ***: "n < n' \<Longrightarrow> ?f n \<in> dc_seq M a n'" for n and n'
  proof (induct n' rule: strict_dec_induct)
    case base
    show "a (M - dc_seq M a n) \<in> dc_seq M a (Suc n)" by simp
  next
    case (step n')
    from step.hyps(2) show "a (M - dc_seq M a n) \<in> dc_seq M a (Suc n')" by simp
  qed
  have "bij_betw ?f (UNIV :: nat set) ?A"
  proof (rule bij_betw_imageI)
    show "inj_on ?f (UNIV :: nat set)"
    proof (rule inj_onI)
      fix n and n'
      assume "?f n = ?f n'"
      {
        assume "n < n'"
        with *** have "?f n \<in> dc_seq M a n'" by simp
        moreover from ** have "?f n' \<notin> dc_seq M a n'" by simp
        moreover note \<open>?f n = ?f n'\<close>
        ultimately have "False" by simp
      }
      moreover {
        assume "n' < n"
        with *** have "?f n' \<in> dc_seq M a n" by simp
        moreover from ** have "?f n \<notin> dc_seq M a n" by simp
        moreover note \<open>?f n = ?f n'\<close>
        ultimately have "False" by simp
      }
      ultimately show "n = n'" by fastforce
    qed
    show "?f ` UNIV = ?A"
    proof (rule surj_onI)
      fix n
      have "?f n \<in> dc_seq M a n \<union> {?f n}" by simp
      hence "?f n \<in> dc_seq M a (Suc n)" by simp
      thus "?f n \<in> ?A" by blast
    next
      fix x
      assume "x \<in> ?A"
      then obtain n where "x \<in> dc_seq M a n" by auto
      {
        assume "\<forall>n. ?f n \<noteq> x"
        have "x \<notin> dc_seq M a n'" for n'
        proof (induct n')
          case 0
          show "?case" by simp
        next
          case (Suc n)
          from Suc.hyps and \<open>\<forall>n. ?f n \<noteq> x\<close> show "?case" by auto
        qed
        with \<open>x \<in> dc_seq M a n\<close> have "False" by simp
      }
      thus "\<exists>n \<in> UNIV. ?f n = x" by auto
    qed
  qed
  hence "\<aleph>\<^sub>0 =o |?A|" by auto
  hence "|?A| =o \<aleph>\<^sub>0" by (fact card_eq_sym)
  moreover from * have "?A \<subseteq> M" by auto
  ultimately show "thesis" by (intro that)
qed

corollary cor_infinite_imp_card_leq_aleph_zero:
  assumes "infinite M"
  shows "\<aleph>\<^sub>0 \<le>o |M|"
proof -
  from assms obtain A where "A \<subseteq> M" and "|A| =o \<aleph>\<^sub>0" by (elim thm_2_4)
  from this(2) have "\<aleph>\<^sub>0 =o |A|" by (fact card_eq_sym)
  moreover from \<open>A \<subseteq> M\<close> have "|A| \<le>o |M|" by auto
  ultimately show "\<aleph>\<^sub>0 \<le>o |M|" by (fact card_eq_card_leq_trans)
qed

lemma nat_Times_nat_card_eq_aleph_zero:
  shows "|(UNIV :: nat set) \<times> (UNIV :: nat set)| =o \<aleph>\<^sub>0"
  using ex_2_3 by auto

theorem thm_2_5_1_a:
  assumes "|A| \<le>o \<aleph>\<^sub>0"
    and "|B| \<le>o \<aleph>\<^sub>0"
  shows "|A \<times> B| \<le>o \<aleph>\<^sub>0"
proof -
  from assms(1) obtain f where "f ` A \<subseteq> (UNIV :: nat set)" and "inj_on f A" by auto
  from assms(2) obtain g where "g ` B \<subseteq> (UNIV :: nat set)" and "inj_on g B" by auto
  from \<open>f ` A \<subseteq> UNIV\<close> and \<open>g ` B \<subseteq> UNIV\<close> have "map_prod f g ` (A \<times> B) \<subseteq> UNIV \<times> UNIV" by simp
  moreover from \<open>inj_on f A\<close> and \<open>inj_on g B\<close> have "inj_on (map_prod f g) (A \<times> B)"
    by (rule map_prod_inj_on)
  ultimately have "|A \<times> B| \<le>o |(UNIV :: nat set) \<times> (UNIV :: nat set)|" by auto
  moreover note nat_Times_nat_card_eq_aleph_zero
  ultimately show "?thesis" by (fact card_leq_card_eq_trans)
qed

lemma thm_2_5_1_b_a:
  assumes "|A| =o \<aleph>\<^sub>0"
    and "|B| \<le>o \<aleph>\<^sub>0"
    and "B \<noteq> {}"
  shows "|A \<times> B| =o \<aleph>\<^sub>0"
proof -
  from assms(1) have "\<aleph>\<^sub>0 =o |A|" by (fact card_eq_sym)
  then obtain f where "bij_betw f (UNIV :: nat set) A" by auto
  from assms(3) obtain b where "b \<in> B" by auto
  let ?g = "\<lambda>n. (f n, b)"
  have "?g ` UNIV \<subseteq> A \<times> B"
  proof (rule image_subsetI)
    fix n
    from \<open>bij_betw f UNIV A\<close> have "f n \<in> A" by auto
    with \<open>b \<in> B\<close> show "?g n \<in> A \<times> B" by simp
  qed
  moreover have "inj_on ?g UNIV"
  proof (rule inj_onI)
    fix m n
    assume "(f m, b) = (f n, b)"
    hence "f m = f n" by simp
    moreover from \<open>bij_betw f UNIV A\<close> have "inj_on f UNIV" by auto
    ultimately show "m = n" by (auto dest: injD)
  qed
  ultimately have "\<aleph>\<^sub>0 \<le>o |A \<times> B|" by auto
  from assms(1) have "|A| \<le>o \<aleph>\<^sub>0" by blast
  with assms(2) have "|A \<times> B| \<le>o \<aleph>\<^sub>0" by (intro thm_2_5_1_a)
  with \<open>\<aleph>\<^sub>0 \<le>o |A \<times> B|\<close> show "?thesis" by (intro thm_2_3_2)
qed

lemma Times_card_commute:
  fixes A :: "'a set"
  shows "|A \<times> B| =o |B \<times> A|"
proof -
  have "prod.swap \<in> A \<times> B \<rightarrow> B \<times> A" by auto
  moreover have "prod.swap \<in> B \<times> A \<rightarrow> A \<times> B" by auto
  moreover {
    fix x
    assume "x \<in> A \<times> B"
    have "prod.swap (prod.swap x) = x" by simp
  }
  moreover {
    fix x
    assume "x \<in> B \<times> A"
    have "prod.swap (prod.swap x) = x" by simp
  }
  ultimately have "bij_betw prod.swap (A \<times> B) (B \<times> A)" by (fact bij_betwI)
  thus "?thesis" by auto
qed

lemma thm_2_5_1_b_b:
  assumes "|A| \<le>o \<aleph>\<^sub>0"
    and "A \<noteq> {}"
    and "|B| =o \<aleph>\<^sub>0"
  shows "|A \<times> B| =o \<aleph>\<^sub>0"
proof -
  have "|A \<times> B| =o |B \<times> A|" by (fact Times_card_commute)
  moreover from assms have "|B \<times> A| =o \<aleph>\<^sub>0" by (intro thm_2_5_1_b_a)
  ultimately show "?thesis" by (fact card_eq_trans)
qed

theorem thm_2_5_1_b:
  assumes "|A| \<le>o \<aleph>\<^sub>0"
    and "A \<noteq> {}"
    and "|B| \<le>o \<aleph>\<^sub>0"
    and "B \<noteq> {}"
    and "|A| =o \<aleph>\<^sub>0 \<or> |B| =o \<aleph>\<^sub>0"
  shows "|A \<times> B| =o \<aleph>\<^sub>0"
  using assms thm_2_5_1_b_a thm_2_5_1_b_b by metis

lemma aleph_zero_Times_aleph_zero:
  assumes "|A| =o \<aleph>\<^sub>0"
    and "|B| =o \<aleph>\<^sub>0"
  shows "|A \<times> B| =o \<aleph>\<^sub>0"
proof -
  from assms(2) have "|B| \<le>o \<aleph>\<^sub>0" and "B \<noteq> {}" by blast+
  with assms show "?thesis" by (blast intro: thm_2_5_1_b_a)
qed

lemma card_leq_imp_surj_on:
  assumes "|A| \<le>o |B|"
    and "A = {} \<Longrightarrow> B = {}"
  obtains g where "g ` B = A"
proof -
  from assms obtain f where "f ` A \<subseteq> B" and "inj_on f A" by auto
  with assms(2) obtain g where "g ` B = A" by(elim cor_inj_on_iff_surj_on_a)
  thus "thesis" by (fact that)
qed

lemma surj_on_imp_card_leq:
  assumes "f ` A = B"
  shows "|B| \<le>o |A|"
proof -
  from assms obtain g where "g ` B \<subseteq> A" and "inj_on g B" by (elim cor_inj_on_iff_surj_on_b)
  thus "?thesis" by auto
qed

theorem thm_2_5_2_a:
  fixes \<Lambda> :: "'b set"
    and A :: "'b \<Rightarrow> 'a set"
  assumes "\<Lambda> \<noteq> {}"
    and "\<And>l. l \<in> \<Lambda> \<Longrightarrow> |A l| \<le>o \<aleph>\<^sub>0"
    and "|\<Lambda>| \<le>o \<aleph>\<^sub>0"
  shows "|\<Union>l \<in> \<Lambda>. A l| \<le>o \<aleph>\<^sub>0"
proof -
  let ?A = "\<Union>l \<in> \<Lambda>. A l"
  {
    assume "?A = {}"
    hence "?thesis" by auto
  }
  moreover {
    assume "?A \<noteq> {}"
    then obtain a\<^sub>0 where "a\<^sub>0 \<in> ?A" by blast
    {
      fix l
      assume "l \<in> \<Lambda>"
      {
        let ?g = "\<lambda>n :: nat. a\<^sub>0"
        assume "A l = {}"
        hence "A l \<subseteq> ?g ` UNIV" by simp
        moreover from \<open>a\<^sub>0 \<in> ?A\<close> have "?g ` UNIV \<subseteq> ?A" by auto
        ultimately have "A l \<subseteq> ?g ` UNIV \<and> ?g ` UNIV \<subseteq> ?A" ..
        hence "{g :: nat \<Rightarrow> 'a. A l \<subseteq> g ` UNIV \<and> g ` UNIV \<subseteq> ?A} \<noteq> {}" by fast
      }
      moreover {
        assume "A l \<noteq> {}"
        with \<open>l \<in> \<Lambda>\<close> assms(2) obtain g :: "nat \<Rightarrow> 'a" where "g ` UNIV = A l"
          by (metis card_leq_imp_surj_on)
        moreover from this and \<open>l \<in> \<Lambda>\<close> have "g ` UNIV \<subseteq> ?A" by auto
        ultimately have "A l \<subseteq> g ` UNIV \<and> g ` UNIV \<subseteq> ?A" by simp
        hence "{g :: nat \<Rightarrow> 'a. A l \<subseteq> g ` UNIV \<and> g ` UNIV \<subseteq> ?A} \<noteq> {}" by auto
      }
      ultimately have "{g :: nat \<Rightarrow> 'a. A l \<subseteq> g ` UNIV \<and> g ` UNIV \<subseteq> ?A} \<noteq> {}" by blast
    }
    then obtain f :: "'b \<Rightarrow> nat \<Rightarrow> 'a"
      where f: "f \<in> (\<Pi> l \<in> \<Lambda>. {g. A l \<subseteq> g ` UNIV \<and> g ` UNIV \<subseteq> ?A})" by (elim AC_E)
    let ?\<phi> = "\<lambda>(l, n). f l n"
    have "?\<phi> ` (\<Lambda> \<times> UNIV) = ?A"
    proof (rule surj_onI; split_pair)
      fix l and  n :: nat
      assume "(l, n) \<in> \<Lambda> \<times> UNIV"
      hence "l \<in> \<Lambda>" by simp
      with f have "f l ` UNIV \<subseteq> ?A" by fast
      thus "f l n \<in> ?A" by auto
    next
      fix a
      assume "a \<in> ?A"
      then obtain l where "l \<in> \<Lambda>" and "a \<in> A l" by auto
      with f obtain n where "f l n = a" by auto
      with \<open>l \<in> \<Lambda>\<close> show "\<exists>l \<in> \<Lambda>. \<exists>n \<in> UNIV. f l n = a" by auto
    qed
    hence "|?A| \<le>o |\<Lambda> \<times> (UNIV :: nat set)|" by (fact surj_on_imp_card_leq)
    also from assms(3) have "|\<Lambda> \<times> (UNIV :: nat set)| \<le>o \<aleph>\<^sub>0" by (auto elim: thm_2_5_1_a)
    finally have "?thesis" .
  }
  ultimately show "?thesis" by blast
qed

theorem thm_2_5_2_b:
  fixes \<Lambda> :: "'b set"
    and A :: "'b \<Rightarrow> 'a set"
  assumes "\<Lambda> \<noteq> {}"
    and "\<And>l. l \<in> \<Lambda> \<Longrightarrow> |A l| \<le>o \<aleph>\<^sub>0"
    and "|\<Lambda>| \<le>o \<aleph>\<^sub>0"
    and "l \<in> \<Lambda>"
    and "|A l| =o \<aleph>\<^sub>0"
  shows "|\<Union>l \<in> \<Lambda>. A l| =o \<aleph>\<^sub>0"
proof -
  let ?A = "\<Union>l \<in> \<Lambda>. A l"
  from assms(5) have "\<aleph>\<^sub>0 =o |A l|" by (fact ordIso_symmetric)
  then obtain f :: "nat \<Rightarrow> 'a" where *: "bij_betw f UNIV (A l)" by blast
  with assms(4) have "f ` UNIV \<subseteq> ?A" by auto
  moreover from * have "inj_on f UNIV" by auto
  ultimately have "\<aleph>\<^sub>0 \<le>o |?A|" by auto
  moreover from assms(1-3) have "|?A| \<le>o \<aleph>\<^sub>0" by (rule thm_2_5_2_a)
  ultimately show "?thesis" by (intro thm_2_3_2)
qed

lemma countable_Un_aleph_zero:
  assumes "|A| \<le>o \<aleph>\<^sub>0"
    and "|B| =o \<aleph>\<^sub>0"
  shows "|A \<union> B| =o \<aleph>\<^sub>0"
proof -
  let ?\<Lambda> = "{0 :: nat, 1}"
  let ?A = "(\<lambda>l :: nat. undefined)(0 := A, 1 := B)"
  have "?\<Lambda> \<noteq> {}" by simp
  moreover have "\<And>l. l \<in> ?\<Lambda> \<Longrightarrow> |?A l| \<le>o \<aleph>\<^sub>0"
  proof -
    fix l
    assume "l \<in> ?\<Lambda>"
    moreover {
      assume "l = 0"
      with assms(1) have "|?A l| \<le>o \<aleph>\<^sub>0" by simp
    }
    moreover {
      assume "l = 1"
      from assms(2) have "|?A 1| \<le>o \<aleph>\<^sub>0" by fastforce
      with \<open>l = 1\<close> have "|?A l| \<le>o \<aleph>\<^sub>0" by simp
    }
    ultimately show "|?A l| \<le>o \<aleph>\<^sub>0" by blast
  qed
  moreover have "|?\<Lambda>| \<le>o \<aleph>\<^sub>0"
  proof -
    have "inj_on id ?\<Lambda>" by simp
    thus "?thesis" by blast
  qed
  moreover have "1 \<in> ?\<Lambda>" by simp
  moreover from assms(2) have "|?A 1| =o \<aleph>\<^sub>0" by simp
  ultimately have "|\<Union>l \<in> ?\<Lambda>. ?A l| =o \<aleph>\<^sub>0" by (rule thm_2_5_2_b)
  moreover have "(\<Union>l \<in> ?\<Lambda>. ?A l) = A \<union> B" by simp
  ultimately show "?thesis" by argo
qed

lemma aleph_zero_Un_aleph_zero:
  assumes "|A| =o \<aleph>\<^sub>0"
    and "|B| =o \<aleph>\<^sub>0"
  shows "|A \<union> B| =o \<aleph>\<^sub>0"
proof -
  from assms(1) have "|A| \<le>o \<aleph>\<^sub>0" by fast
  with assms(2) show "?thesis" by (intro countable_Un_aleph_zero)
qed

corollary cor_card_int_eq_aleph_zero:
  shows "|UNIV :: int set| =o \<aleph>\<^sub>0"
proof -
  let ?A = "{x :: int. 0 \<le> x}"
  let ?B = "{x :: int. x \<le> 0}"
  have "|?A| =o \<aleph>\<^sub>0"
  proof -
    let ?f = "\<lambda>n :: nat. (of_nat n) :: int"
    have "?f ` UNIV = ?A"
    proof (rule surj_onI)
      fix n
      show "int n \<in> ?A" by simp
    next
      fix n
      assume "n \<in> ?A"
      hence "0 \<le> n" by simp
      then obtain m where "n = ?f m" by (elim nonneg_int_cases)
      thus "\<exists>m \<in> UNIV. ?f m = n" by simp
    qed
    moreover have "inj_on ?f UNIV" by (fact inj_of_nat)
    ultimately have "bij_betw ?f UNIV ?A" by (intro bij_betw_imageI)
    hence "\<aleph>\<^sub>0 =o |?A|" by auto
    thus "?thesis" by (fact ordIso_symmetric)
  qed
  moreover have "|?B| =o \<aleph>\<^sub>0"
  proof -
    let ?f = "\<lambda>n :: nat. -((of_nat n) :: int)"
    have "?f ` UNIV = ?B"
    proof (rule surj_onI)
      fix n
      show "?f n \<in> ?B" by simp
    next
      fix n
      assume "n \<in> ?B"
      hence "0 \<le> -n" by simp
      then obtain m :: nat where "-n = m" by (elim nonneg_int_cases)
      hence "-int m = n" by simp
      thus "\<exists>m \<in> UNIV. -int m = n" by auto
    qed
    moreover have "inj_on ?f UNIV" by (simp add: inj_on_def)
    ultimately have "bij_betw ?f UNIV ?B" by (intro bij_betw_imageI)
    hence "\<aleph>\<^sub>0 =o |?B|" by auto
    thus "?thesis" by (fact ordIso_symmetric)
  qed
  ultimately have "|?A \<union> ?B| =o \<aleph>\<^sub>0" by (rule aleph_zero_Un_aleph_zero)
  moreover have "?A \<union> ?B = UNIV" by auto
  ultimately show "?thesis" by simp
qed

corollary cor_card_rat_eq_aleph_zero:
  shows "|UNIV :: rat set| =o \<aleph>\<^sub>0"
proof -
  let ?f = "\<lambda>(a, b). Fract a b"
  have "?f ` (UNIV \<times> UNIV) = UNIV"
  proof (rule surj_onI; split_pair)
    fix a b
    show "Fract a b \<in> UNIV" by simp
  next
    fix q
    obtain a b where "q = Fract a b" by (auto intro: Rat_cases)
    thus "\<exists>a \<in> UNIV. \<exists>b \<in> UNIV. Fract a b = q" by auto
  qed
  hence "|UNIV :: rat set| \<le>o |(UNIV :: int set) \<times> (UNIV :: int set)|"
    by (fact surj_on_imp_card_leq)
  also have "|(UNIV :: int set) \<times> (UNIV :: int set)| =o \<aleph>\<^sub>0"
  proof -
    have "|UNIV :: int set| =o \<aleph>\<^sub>0" by (fact cor_card_int_eq_aleph_zero)
    moreover from this have "|UNIV :: int set| \<le>o \<aleph>\<^sub>0" by fast
    ultimately show "|(UNIV :: int set) \<times> (UNIV :: int set)| =o \<aleph>\<^sub>0" by (blast intro: thm_2_5_1_b)
  qed
  finally have "|UNIV :: rat set| \<le>o \<aleph>\<^sub>0" .
  moreover have "\<aleph>\<^sub>0 \<le>o |UNIV :: rat set|"
  proof -
    let ?g = "\<lambda>n :: nat. (of_nat n) :: rat"
    have "inj_on ?g UNIV" by (auto intro: inj_of_nat)
    thus "?thesis" by auto
  qed
  ultimately show "?thesis" by (intro thm_2_3_2)
qed

theorem thm_2_6:
  assumes "infinite A"
    and "B \<subseteq> A"
    and "|B| \<le>o \<aleph>\<^sub>0"
    and "infinite (A - B)"
  shows "equipotent (A - B) A"
proof -
  let ?A\<^sub>1 = "A - B"
  from assms(4) obtain C where "C \<subseteq> ?A\<^sub>1" and "|C| =o \<aleph>\<^sub>0" by (elim thm_2_4)
  let ?A\<^sub>2 = "?A\<^sub>1 - C"
  from assms(3) and \<open>|C| =o \<aleph>\<^sub>0\<close> have "|B \<union> C| =o \<aleph>\<^sub>0" by (rule countable_Un_aleph_zero)
  also from \<open>|C| =o \<aleph>\<^sub>0\<close> have "\<aleph>\<^sub>0 =o |C|" by (fact ordIso_symmetric)
  finally have "|B \<union> C| =o |C|" .
  then obtain f\<^sub>1 where "bij_betw f\<^sub>1 (B \<union> C) C" by auto
  let ?f = "\<lambda>a. if a \<in> ?A\<^sub>2 then a else f\<^sub>1 a"
  have "?f ` A = ?A\<^sub>1"
  proof (rule surj_onI)
    fix a
    assume "a \<in> A"
    {
      assume "a \<in> ?A\<^sub>2"
      hence "?f a \<in> ?A\<^sub>1" by simp
    }
    moreover {
      assume "a \<notin> ?A\<^sub>2"
      with \<open>a \<in> A\<close> have "a \<in> B \<union> C" by simp
      from \<open>a \<notin> ?A\<^sub>2\<close> have "?f a = f\<^sub>1 a"by argo
      also from \<open>a \<in> B \<union> C\<close> and \<open>bij_betw f\<^sub>1 (B \<union> C) C\<close> have "\<dots> \<in> C" by auto
      also from \<open>C \<subseteq> ?A\<^sub>1\<close> have "\<dots> \<subseteq> ?A\<^sub>1" by simp
      finally have "?f a \<in> ?A\<^sub>1" .
    }
    ultimately show "?f a \<in> ?A\<^sub>1" by blast
  next
    fix b
    assume "b \<in> ?A\<^sub>1"
    {
      assume "b \<in> C"
      with \<open>bij_betw f\<^sub>1 (B \<union> C) C\<close> obtain a where "a \<in> B \<union> C" and "b = f\<^sub>1 a" by auto
      from this(1) have "a \<notin> ?A\<^sub>2" by simp
      with \<open>b = f\<^sub>1 a\<close> have "?f a = b" by argo
      moreover from \<open>a \<in> B \<union> C\<close> and assms(2) and \<open>C \<subseteq> ?A\<^sub>1\<close> have "a \<in> A" by auto
      ultimately have "\<exists>a \<in> A. ?f a = b" by blast
    }
    moreover {
      assume "b \<notin> C"
      with \<open>b \<in> ?A\<^sub>1\<close> have "b \<in> ?A\<^sub>2" by simp
      hence "?f b = b" by simp
      moreover from \<open>b \<in> ?A\<^sub>1\<close> have "b \<in> A" by simp
      ultimately have "\<exists>a \<in> A. ?f a = b" by blast
    }
    ultimately show "\<exists>a \<in> A. ?f a = b" by blast
  qed
  moreover have "inj_on ?f A"
  proof (rule inj_onI)
    fix a a'
    assume "a \<in> A" and "a' \<in> A" and "?f a = ?f a'"
    consider (A) "a \<in> ?A\<^sub>2" and "a' \<in> ?A\<^sub>2"
      | (B) "a \<in> ?A\<^sub>2" and "a' \<notin> ?A\<^sub>2"
      | (C) "a \<notin> ?A\<^sub>2" and "a' \<in> ?A\<^sub>2"
      | (D) "a \<notin> ?A\<^sub>2" and "a' \<notin> ?A\<^sub>2" by argo
    thus "a = a'"
    proof cases
      case A
      with \<open>?f a = ?f a'\<close> show "?thesis" by simp
    next
      case B
      from B(2) and \<open>a' \<in> A\<close> have "a' \<in> B \<union> C" by simp
      with \<open>?f a = ?f a'\<close> B have "a = f\<^sub>1 a'" by meson
      with \<open>bij_betw f\<^sub>1 (B \<union> C) C\<close> and \<open>a' \<in> B \<union> C\<close> and B(1) have "False" by fast
      thus "?thesis" ..
    next
      case C
      from C(1) and \<open>a \<in> A\<close> have "a \<in> B \<union> C" by simp
      with \<open>?f a = ?f a'\<close> C have "f\<^sub>1 a = a'" by metis
      with \<open>bij_betw f\<^sub>1 (B \<union> C) C\<close> and \<open>a \<in> B \<union> C\<close> and C(2) have "False" by auto
      thus "?thesis" ..
    next
      case D
      with \<open>?f a = ?f a'\<close> have "f\<^sub>1 a = f\<^sub>1 a'" by argo
      moreover from D and \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> have "a \<in> B \<union> C" and "a' \<in> B \<union> C" by blast+
      moreover from \<open>bij_betw f\<^sub>1 (B \<union> C) C\<close> have "inj_on f\<^sub>1 (B \<union> C)" by auto
      ultimately show "?thesis" by (elim inj_onD)
    qed
  qed
  ultimately have "bij_betw ?f A ?A\<^sub>1" by (intro bij_betw_imageI)
  hence "equipotent A ?A\<^sub>1" by auto
  thus "?thesis" by (fact prop_2_1_2)
qed

corollary cor_2_1:
  assumes "infinite A"
    and "|B| \<le>o \<aleph>\<^sub>0"
  shows "equipotent (A \<union> B) A"
proof -
  have A: "(A \<union> B) - (B - A) = A" by auto
  from assms(1) have "infinite (A \<union> B)" by simp
  moreover have "B - A \<subseteq> A \<union> B" by auto
  moreover have "|B - A| \<le>o \<aleph>\<^sub>0"
  proof -
    from assms(2) obtain f where "f ` B \<subseteq> (UNIV :: nat set)" and "inj_on f B" by auto
    hence "f ` (B - A) \<subseteq> UNIV" and "inj_on f (B - A)" by (auto dest: inj_on_diff)
    thus "?thesis" by blast
  qed
  moreover from assms(1) and A have "infinite ((A \<union> B) - (B - A))" by simp
  ultimately have "equipotent ((A \<union> B) - (B - A)) (A \<union> B)" by (rule thm_2_6)
  with A have "equipotent A (A \<union> B)" by simp
  thus "?thesis" by (fact prop_2_1_2)
qed

corollary cor_dedekind_infinity:
  assumes "infinite A"
  obtains B where "B \<subset> A" and "equipotent A B"
proof -
  from assms obtain a where "a \<in> A" by fastforce
  from assms have "infinite (A - {a})" by simp
  moreover have "|{a}| \<le>o \<aleph>\<^sub>0" by fast
  ultimately have "equipotent ((A - {a}) \<union> {a}) (A - {a})" by (rule cor_2_1)
  moreover from \<open>a \<in> A\<close> have "(A - {a}) \<union> {a} = A" by blast
  ultimately have "equipotent A (A - {a})" by simp
  moreover from \<open>a \<in> A\<close> have "A - {a} \<subset> A" by auto
  ultimately show "thesis" by (intro that)
qed

(* TODO:
theorem thm_2_7:
  shows "\<aleph>\<^sub>0 <o \<aleph>"
  sorry
*)

theorem thm_2_8:
  shows "|M| <o |Pow M|"
proof (rule card_lessI)
  show "|M| \<le>o |Pow M|"
  proof (rule card_leqI)
    let ?f = "\<lambda>a. {a}"
    show "?f ` M \<subseteq> Pow M" by auto
    show "inj_on ?f M" by simp
  qed
  show "\<not>|M| =o |Pow M|"
  proof (rule notI)
    assume "|M| =o |Pow M|"
    then obtain f where f: "bij_betw f M (Pow M)" by auto
    let ?X = "{x \<in> M. x \<notin> f x}"
    have "?X \<in> Pow M" by auto
    moreover from f have "f ` M = Pow M" by auto
    ultimately have "?X \<in> f ` M" by simp
    then obtain x where "x \<in> M" and "f x = ?X" by auto
    {
      assume "x \<in> ?X"
      hence "x \<notin> f x" by simp
      with \<open>f x = ?X\<close> have "x \<notin> ?X" by blast
      with \<open>x \<in> ?X\<close> have "False" by simp
    }
    moreover {
      assume "x \<notin> ?X"
      with \<open>x \<in> M\<close> have "x \<in> f x" by simp
      with \<open>f x = ?X\<close> have "x \<in> ?X" by blast
      with \<open>x \<notin> ?X\<close> have "False" by simp
    }
    ultimately show "False" by auto
  qed
qed

subsection \<open>Problems\<close>

proposition prob_2_2_1:
  assumes "|A| =o \<aleph>\<^sub>0"
    and "B \<subseteq> A"
    and "infinite B"
  shows "|B| =o \<aleph>\<^sub>0"
proof -
  from assms(3) have "\<aleph>\<^sub>0 \<le>o |B|" by (fact cor_infinite_imp_card_leq_aleph_zero)
  moreover have "|B| \<le>o \<aleph>\<^sub>0"
  proof -
    from assms(2) obtain f where f0: "f ` B \<subseteq> A" and f1: "inj_on f B" by fastforce
    from assms(1) obtain g where g0: "g ` A \<subseteq> (UNIV :: nat set)" and g1: "inj_on g A" by fast
    from f0 and g0 have "(g \<circ> f) ` B \<subseteq> UNIV" by simp
    moreover from f0 and f1 and g1 have "inj_on (g \<circ> f) B" by (blast dest: thm_1_5_b)
    ultimately show "?thesis" by auto
  qed
  ultimately show "?thesis" by (intro thm_2_3_2)
qed

lemma disjoint_family_onI:
  assumes "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
  shows "disjoint_family_on A I"
  using assms unfolding disjoint_family_on_def by simp

proposition prob_2_2_2:
  fixes A :: "'a set"
  assumes "|A| =o \<aleph>\<^sub>0"
  obtains A' :: "nat \<Rightarrow> 'a set" where "\<And>n. |A' n| =o \<aleph>\<^sub>0"
    and "(\<Union>n. A' n) = A"
    and "disjoint_family_on A' UNIV"
proof -
  have "|(UNIV :: nat set) \<times> (UNIV :: nat set)| =o \<aleph>\<^sub>0" by (fact nat_Times_nat_card_eq_aleph_zero)
  also from assms have "\<aleph>\<^sub>0 =o |A|" by (fact ordIso_symmetric)
  finally have "|(UNIV :: nat set) \<times> (UNIV :: nat set)| =o |A|" .
  then obtain f :: "nat \<times> nat \<Rightarrow> 'a" where f: "bij_betw f (UNIV \<times> UNIV) A" by auto
  hence inj_f: "inj f" by auto
  let ?A' = "\<lambda>n :: nat. f ` ({n} \<times> UNIV)"
  have "\<And>n. |?A' n| =o \<aleph>\<^sub>0"
  proof -
    fix m
    let ?g = "\<lambda>a. THE n. f (m, n) = a"
    have g: "?g a = n" if "f (m, n) = a" for n and a
    proof -
      {
        fix n'
        assume "f (m, n') = a"
        with that have "f (m, n') = f (m, n)" by simp
        with inj_f have "n' = n" by (auto dest: injD)
      }
      with that show "?thesis" by blast
    qed
    have "?g ` (?A' m) = UNIV"
    proof (rule surj_onI)
      fix a
      assume "a \<in> ?A' m"
      show "?g a \<in> UNIV" by simp
    next
      fix n
      have "f (m, n) \<in> ?A' m" by simp
      moreover have "?g (f (m, n)) = n"
      proof (rule the_equality, rule refl)
        fix n'
        assume "f (m, n') = f (m, n)"
        with inj_f have "(m, n') = (m, n)" by (auto dest: injD)
        thus "n' = n" by simp
      qed
      ultimately show "\<exists>a \<in> ?A' m. ?g a = n" by blast
    qed
    moreover have "inj_on ?g (?A' m)"
    proof (rule inj_onI)
      fix a and a'
      assume "a \<in> ?A' m" and "a' \<in> ?A' m" and "?g a = ?g a'"
      from this(1,2) obtain n and n' where "f (m, n) = a" and "f (m, n') = a'" by auto
      moreover from this and \<open>?g a = ?g a'\<close> have "n = n'" using g by simp+
      ultimately show "a = a'" by simp
    qed
    ultimately show "|?A' m| =o \<aleph>\<^sub>0" by (blast intro: bij_betw_imageI)
  qed
  moreover have "(\<Union>n. ?A' n) = A"
  proof (rule set_eqI2)
    fix a
    assume "a \<in> (\<Union>n. ?A' n)"
    then obtain m where "a \<in> ?A' m" by auto
    then obtain n where "a = f (m, n)" by auto
    also from f have "f (m, n) \<in> A" by blast
    finally show "a \<in> A" .
  next
    fix a
    assume "a \<in> A"
    with f obtain m and n where "a = f (m, n)" by blast
    hence "a \<in> ?A' m" by simp
    thus "a \<in> (\<Union>n. ?A' n)" by blast
  qed
  moreover have "disjoint_family_on ?A' UNIV"
  proof (rule disjoint_family_onI)
    fix m m' :: "nat"
    assume "m \<noteq> m'"
    {
      fix a
      assume "a \<in> ?A' m" and "a \<in> ?A' m'"
      then obtain n n' :: "nat" where "a = f (m, n)" and "a = f (m', n')" by blast
      hence "f (m, n) = f (m', n')" by simp
      with inj_f have "(m, n) = (m', n')" by (auto dest: injD)
      with \<open>m \<noteq> m'\<close> have "False" by simp
    }
    thus "?A' m \<inter> ?A' m' = {}" by fast
  qed
  ultimately show "thesis" by (fact that)
qed

proposition prob_2_2_3:
  defines QQ: "\<QQ> \<equiv> {{a :: rat <..< b} | a b. a < b}"
  shows "|\<QQ>| =o \<aleph>\<^sub>0"
proof -
  have "|\<QQ>| \<le>o \<aleph>\<^sub>0"
  proof -
    let ?f = "\<lambda>(a :: rat, b). {a <..< b}"
    have "?f ` (UNIV \<times> UNIV) = \<QQ> \<union> {{}}"
    proof (rule surj_onI; split_pair)
      fix a b :: "rat"
      {
        assume "a < b"
        hence "{a <..< b} \<in> \<QQ> \<union> {{}}" unfolding QQ by auto
      }
      moreover {
        assume "b \<le> a"
        hence "{a <..< b} = {}" by simp
        hence "{a <..< b} \<in> \<QQ> \<union> {{}}" by simp
      }
      ultimately show "{a <..< b} \<in> \<QQ> \<union> {{}}" by linarith
    next
      fix Q
      assume "Q \<in> \<QQ> \<union> {{}}"
      moreover {
        assume "Q \<in> \<QQ>"
        hence "\<exists>a b. {a <..< b} = Q" unfolding QQ by auto
      }
      moreover {
        assume "Q \<in> {{}}"
        moreover have "{0 :: rat <..< 0} = {}" by simp
        ultimately have "\<exists>a b. {a <..< b} = Q" by auto
      }
      ultimately show "\<exists>a \<in> UNIV. \<exists>b \<in> UNIV. {a <..< b} = Q" by auto
    qed
    hence "|\<QQ> \<union> {{}}| \<le>o |(UNIV :: rat set) \<times> (UNIV :: rat set)|" by (fact surj_on_imp_card_leq)
    also have "|(UNIV :: rat set) \<times> (UNIV :: rat set)| =o \<aleph>\<^sub>0"
    proof -
      have "|UNIV :: rat set| =o \<aleph>\<^sub>0" by (fact cor_card_rat_eq_aleph_zero)
      thus "?thesis" by (blast intro: aleph_zero_Times_aleph_zero)
    qed
    finally have "|\<QQ> \<union> {{}}| \<le>o \<aleph>\<^sub>0" .
    thus "|\<QQ>| \<le>o \<aleph>\<^sub>0" by fastforce
  qed
  moreover have "\<aleph>\<^sub>0 \<le>o |\<QQ>|"
  proof (rule card_leqI)
    let ?f = "\<lambda>n :: nat. {(rat_of_nat n) - 1 <..< (of_nat n) + 1}"
    {
      fix n
      have "{(rat_of_nat n) - 1 <..< (of_nat n) + 1} \<in> \<QQ>" unfolding QQ by fastforce
    }
    thus "range ?f \<subseteq> \<QQ>" by auto
    {
      fix n n' :: "nat"
      assume "?f n = ?f n'"
      {
        assume "n < n'"
        hence "of_nat n \<in> ?f n" and "of_nat n \<notin> ?f n'" by simp+
        hence "?f n \<noteq> ?f n'" by blast
        with \<open>?f n = ?f n'\<close> have "False" by simp
      }
      moreover {
        assume "n' < n"
        hence "of_nat n \<in> ?f n" and "of_nat n \<notin> ?f n'" by simp+
        hence "?f n \<noteq> ?f n'" by blast
        with \<open>?f n = ?f n'\<close> have "False" by simp
      }
      ultimately have "n = n'" by fastforce
    }
    thus "inj ?f" by (fact injI)
  qed
  ultimately show "?thesis" by (fact thm_2_3_2)
qed

lemmas [dest] = disjointD

proposition prob_2_2_4:
  assumes "\<And>I. I \<in> \<II> \<Longrightarrow> \<exists>a b :: real. a < b \<and> I = {a <..< b}"
    and "disjoint \<II>"
  shows "|\<II>| \<le>o \<aleph>\<^sub>0"
proof -
  let ?f = "\<lambda>I. {q :: rat. (of_rat q) \<in> I}"
  {
    fix I
    assume "I \<in> \<II>"
    with assms(1) obtain a and b where "a < b" and I: "I = {a <..< b}" by blast
    from this(1) obtain q :: rat where "a < of_rat q" and "of_rat q < b"
      by (blast dest: of_rat_dense)
    with I have "of_rat q \<in> I" by simp
    hence "?f I \<noteq> {}" by auto
  }
  moreover have "disjoint_family_on ?f \<II>"
  proof (rule disjoint_family_onI)
    fix I and J
    assume "I \<in> \<II>" and "J \<in> \<II>" and "I \<noteq> J"
    with assms(2) have "I \<inter> J = {}" by blast
    from \<open>I \<in> \<II>\<close> and \<open>J \<in> \<II>\<close> obtain a b a' b'
      where "a < b" and I: "I = {a <..< b}"
        and "a' < b'" and J: "J = {a' <..< b'}" by (fast dest: assms(1))
    {
      assume "a' < b \<and> a < b'"
      with \<open>a < b\<close> and \<open>a' < b'\<close> have "max a a' < min b b'" by simp
      then obtain c where "max a a' < c" and "c < min b b'" by (blast dest: dense)
      with I and J have "c \<in> I" and "c \<in> J" by simp+
      with \<open>I \<inter> J = {}\<close> have "False" by auto
    }
    hence "b \<le> a' \<or> b' \<le> a" by argo
    moreover {
      assume "b \<le> a'"
      with I and J have "?f I \<inter> ?f J = {}" by fastforce
    }
    moreover {
      assume "b' \<le> a"
      with I and J have "?f I \<inter> ?f J = {}" by fastforce
    }
    ultimately show "?f I \<inter> ?f J = {}" by linarith
  qed
  ultimately have "|\<II>| \<le>o |\<Union>I \<in> \<II>. {q :: rat. (of_rat q) \<in> I}|" by (fact prob_2_1_5)
  also have "|\<Union>I \<in> \<II>. {q :: rat. (of_rat q) \<in> I}| \<le>o |UNIV :: rat set|" by auto
  also have "|UNIV :: rat set| =o \<aleph>\<^sub>0" by (fact cor_card_rat_eq_aleph_zero)
  finally show "?thesis" .
qed

lemma fixed_length_lists_of_aleph_zero:
  fixes A :: "'a set"
  assumes "|A| =o \<aleph>\<^sub>0"
    and "1 \<le> n"
  defines XS: "XS l \<equiv> {xs \<in> lists A. length xs = l}"
  shows "|XS n| =o \<aleph>\<^sub>0"
using assms(2) proof (induct n rule: dec_induct)
  case base
  let ?f = "\<lambda>a. [a]"
  have "?f ` A = XS 1"
  proof (rule surj_onI)
    fix a
    assume "a \<in> A"
    thus "?f a \<in> XS 1" unfolding XS by simp
  next
    fix xs
    assume "xs \<in> XS 1"
    hence "xs \<in> lists A" and "length xs = 1" unfolding XS by simp+
    from this(2) have "length xs = Suc 0" by simp
    then obtain y and ys where "xs = y # ys" and "length ys = 0" by (auto simp: length_Suc_conv)
    from this(2) have "ys = []" by simp
    with \<open>xs = y # ys\<close> have "xs = [y]" by simp
    moreover from \<open>xs = y # ys\<close> and \<open>xs \<in> lists A\<close> have "y \<in> A" by simp
    ultimately show "\<exists>a \<in> A. ?f a = xs" by simp
  qed
  moreover have "inj_on ?f A"
  proof (rule inj_onI)
    fix a a' :: "'a"
    assume "?f a = ?f a'"
    thus "a = a'" by simp
  qed
  ultimately have "bij_betw ?f A (XS 1)" by (intro bij_betw_imageI)
  hence "|A| =o |XS 1|" by auto
  hence "|XS 1| =o |A|" by (fact ordIso_symmetric)
  also note assms(1)
  finally show "?case" .
next
  case (step n)
  let ?f = "\<lambda>(xs, x). x # xs"
  have "?f ` ((XS n) \<times> A) = XS (Suc n)"
  proof (rule surj_onI; split_pair)
    fix xs and a
    assume "(xs, a) \<in> (XS n) \<times> A"
    hence "xs \<in> XS n" and "a \<in> A" by simp+
    from this(1) have "xs \<in> lists A" and "length xs = n" unfolding XS by simp+
    from this(1) and \<open>a \<in> A\<close> have "a # xs \<in> lists A" by simp
    moreover from \<open>length xs = n\<close> have "length (a # xs) = Suc n" by simp
    ultimately show "a # xs \<in> XS (Suc n)" unfolding XS by simp
  next
    fix xs
    assume "xs \<in> XS (Suc n)"
    hence "xs \<in> lists A" and "length xs = Suc n" unfolding XS by simp+
    from this(2) obtain a and ys where "xs = a # ys" and "length ys = n"
      by (auto simp: length_Suc_conv)
    from \<open>xs \<in> lists A\<close> and this(1) have "ys \<in> lists A" by simp
    with \<open>length ys = n\<close> have "ys \<in> XS n" unfolding XS by simp
    moreover from \<open>xs \<in> lists A\<close> and \<open>xs = a # ys\<close> have "a \<in> A" by simp
    moreover note \<open>xs = a # ys\<close>
    ultimately show "\<exists>ys \<in> XS n. \<exists>a \<in> A. a # ys = xs" by simp
  qed
  hence "|XS (Suc n)| \<le>o |(XS n) \<times> A|" by (fact surj_on_imp_card_leq)
  also from assms(1) and step.hyps have "|(XS n) \<times> A| =o \<aleph>\<^sub>0"
    by (intro aleph_zero_Times_aleph_zero)
  finally have "|XS (Suc n)| \<le>o \<aleph>\<^sub>0" .
  moreover have "\<aleph>\<^sub>0 \<le>o |XS (Suc n)|"
  proof -
    from step.hyps(3) have "\<aleph>\<^sub>0 =o |XS n|" by (fact ordIso_symmetric)
    also have "|XS n| \<le>o |XS (Suc n)|"
    proof -
      from assms(1) obtain a where "a \<in> A" by blast
      let ?f = "\<lambda>xs. a # xs"
      have "?f ` (XS n) \<subseteq> XS (Suc n)"
      proof (rule image_subsetI)
        fix xs
        assume "xs \<in> XS n"
        hence "xs \<in> lists A" and "length xs = n" unfolding XS by simp+
        from this(1) and \<open>a \<in> A\<close> have "?f xs \<in> lists A" by simp
        moreover from \<open>length xs = n\<close> have "length (?f xs) = Suc n" by simp
        ultimately show "?f xs \<in> XS (Suc n)" unfolding XS by simp
      qed
      moreover have "inj_on ?f (XS n)" by simp
      ultimately show "?thesis" by blast
    qed
    finally show "?thesis" .
  qed
  ultimately show "?case" by (fact thm_2_3_2)
qed

lemma lists_aleph_zero_eq_aleph_zero:
  assumes "|A| =o \<aleph>\<^sub>0"
  shows "|lists A| =o \<aleph>\<^sub>0"
proof -
  let ?A' = "\<lambda>n. {xs \<in> lists A. length xs = n}"
  let ?B = "\<Union>i. ?A' i"
  have "lists A \<subseteq> ?B"
  proof (rule subsetI)
    fix xs
    assume "xs \<in> lists A"
    hence "xs \<in> ?A' (length xs)" by simp
    thus "xs \<in> ?B" by blast
  qed
  hence "|lists A| \<le>o |?B|" by fastforce
  also have "|?B| =o \<aleph>\<^sub>0"
  proof (rule thm_2_5_2_b; simp?)
    fix n :: nat
    {
      assume "n = 0"
      hence "?A' n = {[]}" by auto
      hence "|?A' n| \<le>o \<aleph>\<^sub>0" by auto
    }
    moreover {
      assume "1 \<le> n"
      with assms have "|?A' n| =o \<aleph>\<^sub>0" by (fact fixed_length_lists_of_aleph_zero)
      hence "|?A' n| \<le>o \<aleph>\<^sub>0" by fast
    }
    ultimately show "|?A' n| \<le>o \<aleph>\<^sub>0" by linarith
  next
    from assms show "|?A' 1| =o \<aleph>\<^sub>0" by (blast intro: fixed_length_lists_of_aleph_zero)
  qed
  finally have "|lists A| \<le>o \<aleph>\<^sub>0" by simp
  moreover have "\<aleph>\<^sub>0 \<le>o |lists A|"
  proof -
    from assms have "|?A' 1| =o \<aleph>\<^sub>0" by (blast intro: fixed_length_lists_of_aleph_zero)
    hence "\<aleph>\<^sub>0 =o |?A' 1|" by (fact ordIso_symmetric)
    also have "|?A' 1| \<le>o |lists A|"
    proof -
      have "?A' 1 \<subseteq> lists A" by auto
      thus "?thesis" by auto
    qed
    finally show "?thesis" .
  qed
  ultimately show "?thesis" by (fact thm_2_3_2)
qed

proposition prob_2_2_5:
  assumes "|A| =o \<aleph>\<^sub>0"
  defines AA: "\<AA> \<equiv> {X. X \<subseteq> A \<and> finite X}"
  shows "|\<AA>| =o \<aleph>\<^sub>0"
proof -
  let ?A' = "\<lambda>n. {xs \<in> lists A. length xs = n}"
  let ?B = "\<Union>n. ?A' n"
  let ?f = "\<lambda>xs. set xs"
  have "?f ` ?B = \<AA>"
  proof (rule surj_onI)
    fix xs
    assume "xs \<in> ?B"
    then obtain n where "xs \<in> ?A' n" by simp
    hence "xs \<in> lists A" by simp
    hence "?f xs \<subseteq> A" by auto
    moreover have "finite (?f xs)" by simp
    ultimately show "?f xs \<in> \<AA>" unfolding AA by simp
  next
    fix X
    assume "X \<in> \<AA>"
    hence "X \<subseteq> A" and "finite X" unfolding AA by simp+
    then obtain xs where "xs \<in> lists A" and "set xs = X" by (fast dest: finite_list)
    from this(1) have "xs \<in> ?A' (length xs)" by simp
    hence "xs \<in> ?B" by simp
    with \<open>set xs = X\<close> show "\<exists>xs \<in> ?B. ?f xs = X" by blast
  qed
  hence "|\<AA>| \<le>o |?B|" by (fact surj_on_imp_card_leq)
  also have "|?B| \<le>o \<aleph>\<^sub>0"
  proof (rule thm_2_5_2_a; simp)
    fix n
    have "?A' n \<subseteq> lists A" by auto
    hence "|?A' n| \<le>o |lists A|" by auto
    also from assms(1) have "|lists A| =o \<aleph>\<^sub>0" by (fact lists_aleph_zero_eq_aleph_zero)
    finally show "|?A' n| \<le>o \<aleph>\<^sub>0" .
  qed
  finally have "|\<AA>| \<le>o \<aleph>\<^sub>0" .
  moreover have "\<aleph>\<^sub>0 \<le>o |\<AA>|"
  proof -
    from assms(1) have "\<aleph>\<^sub>0 =o |A|" by (fact ordIso_symmetric)
    also have "|A| \<le>o |\<AA>|"
    proof (rule card_leqI)
      let ?f = "\<lambda>a :: 'a. {a}"
      {
        fix a
        assume "a \<in> A"
        hence "?f a \<in> \<AA>" unfolding AA by simp
      }
      thus "?f ` A \<subseteq> \<AA>" by auto
      show "inj_on ?f A" by simp
    qed
    finally show "?thesis" .
  qed
  ultimately show "?thesis" by (fact thm_2_3_2)
qed

(* TODO: prob_2_2_6 *)

(* TODO: proposition prob_2_2_7:
  shows "|(UNIV :: real set) - \<rat>| =o \<aleph>"
  sorry*)

end
