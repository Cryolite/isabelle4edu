theory Section_2_2
  imports Complex_Main
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

corollary cor_infinite_imp_aleph_zero_card_leq:
  assumes "infinite M"
  shows "\<aleph>\<^sub>0 \<le>o |M|"
proof -
  from assms obtain A where "A \<subseteq> M" and "|A| =o \<aleph>\<^sub>0" by (elim thm_2_4)
  from this(2) have "\<aleph>\<^sub>0 =o |A|" by (fact card_eq_sym)
  also from \<open>A \<subseteq> M\<close> have "\<dots> \<le>o |M|" by (fact subset_imp_card_leq)
  finally show "\<aleph>\<^sub>0 \<le>o |M|" .
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
  also note nat_Times_nat_card_eq_aleph_zero
  finally show "|A \<times> B| \<le>o \<aleph>\<^sub>0" .
qed

lemma thm_2_5_1_b_a:
  assumes "|A| =o \<aleph>\<^sub>0"
    and "|B| \<le>o \<aleph>\<^sub>0"
    and "B \<noteq> {}"
  shows "|A \<times> B| =o \<aleph>\<^sub>0"
proof -
  from assms(1) have "\<aleph>\<^sub>0 =o |A|" by (fact card_eq_sym)
  then obtain f where "bij_betw f (UNIV :: nat set) A" by (elim card_eqE)
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
  from assms(1) have "|A| \<le>o \<aleph>\<^sub>0" by (intro card_eq_imp_card_leq)
  with assms(2) have "|A \<times> B| \<le>o \<aleph>\<^sub>0" by (intro thm_2_5_1_a)
  with \<open>\<aleph>\<^sub>0 \<le>o |A \<times> B|\<close> show "?thesis" by (intro thm_2_3_2)
qed

lemma thm_2_5_1_b_b:
  assumes "|A| \<le>o \<aleph>\<^sub>0"
    and "A \<noteq> {}"
    and "|B| =o \<aleph>\<^sub>0"
  shows "|A \<times> B| =o \<aleph>\<^sub>0"
proof -
  from assms have "|B \<times> A| =o \<aleph>\<^sub>0" by (intro thm_2_5_1_b_a)
  hence "\<aleph>\<^sub>0 =o |B \<times> A|" by (fact card_eq_sym)
  also have "\<dots> =o |A \<times> B|"
  proof (rule card_eqI)
    have "prod.swap ` (B \<times> A) = (A \<times> B)"
    proof (rule surj_onI; split_pair)
      fix b a
      assume "(b, a) \<in> B \<times> A"
      thus "prod.swap (b, a) \<in> A \<times> B" by simp
    next
      fix a b
      assume "(a, b) \<in> A \<times> B"
      hence "prod.swap (b, a) = (a, b)" by simp
      with \<open>(a, b) \<in> A \<times> B\<close> show "\<exists>b' \<in> B. \<exists>a' \<in> A. prod.swap (b', a') = (a, b)" by simp
    qed
    moreover have "inj_on prod.swap (B \<times> A)"
    proof (rule inj_onI, split_pair)
      fix a a' :: 'a and  b b' :: 'b
      assume "prod.swap (b, a) = prod.swap(b', a')"
      thus "(b, a) = (b', a')" by simp
    qed
    ultimately show "bij_betw prod.swap (B \<times> A) (A \<times> B)" by (intro bij_betw_imageI)
  qed
  finally have "\<aleph>\<^sub>0 =o |A \<times> B|" .
  thus "?thesis" by (fact card_eq_sym)
qed

theorem thm_2_5_1_b:
  assumes "|A| \<le>o \<aleph>\<^sub>0"
    and "A \<noteq> {}"
    and "|B| \<le>o \<aleph>\<^sub>0"
    and "B \<noteq> {}"
    and "|A| =o \<aleph>\<^sub>0 \<or> |B| =o \<aleph>\<^sub>0"
  shows "|A \<times> B| =o \<aleph>\<^sub>0"
  using assms thm_2_5_1_b_a thm_2_5_1_b_b by metis

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
    also from assms(3) have "\<dots> \<le>o \<aleph>\<^sub>0" by (auto elim: thm_2_5_1_a)
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
  from assms(5) obtain f :: "nat \<Rightarrow> 'a" where *: "bij_betw f UNIV (A l)"
    by (blast dest: card_eq_sym)
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
    thus "?thesis" by (fact card_eq_sym)
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
    thus "?thesis" by (fact card_eq_sym)
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
  also have "\<dots> =o \<aleph>\<^sub>0"
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
  also from \<open>|C| =o \<aleph>\<^sub>0\<close> have "\<dots> =o |C|" by (fact card_eq_sym)
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
  from assms(3) have "\<aleph>\<^sub>0 \<le>o |B|" by (fact cor_infinite_imp_aleph_zero_card_leq)
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
  also from assms have "\<aleph>\<^sub>0 =o |A|" by (fact card_eq_sym)
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

end
