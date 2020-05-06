theory Section_2_1
  imports Complex_Main
    "HOL-Library.Disjoint_Sets"
    "HOL-Library.Quadratic_Discriminant"
    "HOL-Computational_Algebra.Primes"
    "Split_Pair"
    "Section_1_6"
begin

context includes cardinal_syntax begin

chapter \<open>Cardinality of Sets\<close>

section \<open>Equipotence and Cardinality of Sets\<close>

subsection \<open>A) Equipotence of Sets\<close>

definition equipotent :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "equipotent A B \<longleftrightarrow> (\<exists>f. bij_betw f A B)"

lemma equipotentI [intro]:
  assumes "bij_betw f A B"
  shows "equipotent A B"
  using assms unfolding equipotent_def by auto

lemma equipotentE [elim]:
  assumes "equipotent A B"
  obtains f where "bij_betw f A B"
  using assms unfolding equipotent_def by auto

lemma equipotent_empty1 [simp]:
  assumes "equipotent {} B"
  shows "B = {}"
  using assms by auto

lemma equipotent_empty2 [simp]:
  assumes "equipotent A {}"
  shows "A = {}"
  using assms by auto

proposition prop_2_1_1 [simp]:
  shows "equipotent A A"
  by auto

proposition prop_2_1_2:
  assumes "equipotent A B"
  shows "equipotent B A"
proof -
  from assms obtain f where "bij_betw f A B" by auto
  hence "bij_betw (the_inv_into A f) B A" by (fact bij_betw_the_inv_into)
  thus ?thesis by auto
qed

proposition prop_2_1_3 [trans]:
  assumes "equipotent A B"
    and "equipotent B C"
  shows "equipotent A C"
proof -
  from assms obtain f and g where "bij_betw f A B" and "bij_betw g B C" by blast
  hence "bij_betw (g \<circ> f) A C" by (rule thm_1_5_c)
  thus ?thesis by auto
qed

proposition ex_2_3_factorization_existence:
  assumes "0 < n"
  obtains i :: nat and j :: nat where "n = 2^i * (2 * j + 1)"
proof -
  have "prime (2 :: nat)" by (fact two_is_prime_nat)
  with assms obtain i and m
    where "\<not>2 dvd m"
    and "n = m * 2^i" by (blast dest: prime_power_canonical)
  from this(1) obtain j where "m = 2 * j + 1" by (elim oddE)
  with \<open>n = m * 2^i\<close> have "n = 2^i * (2 * j + 1)" by simp
  thus "thesis" by (fact that)
qed

proposition ex_2_3_factorization_uniqueness:
  fixes i j i' j' :: nat
  assumes "2^i * (2 * j + 1) = 2^i' * (2 * j' + 1)"
  obtains "i = i'" and "j = j'"
proof -
  from assms have "(2 * j' + 1) * 2^i' = (2 * j + 1) * 2^i" by (simp only: mult.commute)
  moreover have "prime (2 :: nat)" by simp
  moreover have "\<not>2 dvd (2 * j' + 1)" by simp
  moreover have "\<not>2 dvd (2 * j + 1)" by simp
  ultimately have "2 * j' + 1 = 2 * j + 1" and "i' = i" using prime_power_cancel2 by blast+
  hence "j = j'" and "i = i'" by simp+
  thus "thesis" by (intro that)
qed

proposition ex_2_3:
  shows "equipotent ((UNIV :: nat set) \<times> (UNIV :: nat set)) (UNIV :: nat set)"
proof -
  let ?f = "\<lambda>(i :: nat, j :: nat). 2^i * (2 * j + 1) - 1"
  have "?f ` (UNIV \<times> UNIV) = UNIV"
  proof (rule surj_onI; split_pair)
    fix i j :: nat
    show "2^i * (2 * j + 1) - 1 \<in> UNIV" by simp
  next
    fix n :: nat
    obtain i and j where "n + 1 = 2^i * (2 * j + 1)" using ex_2_3_factorization_existence by auto
    hence "2^i * (2 * j + 1) - 1 = n" by presburger
    thus "n \<in> ?f ` (UNIV \<times> UNIV)" by auto
  qed
  moreover have "inj_on ?f (UNIV \<times> UNIV)"
  proof (rule inj_onI, split_pair)
    thm inj_onI
    fix i j i' j' :: nat
    assume "2^i * (2 * j + 1) - 1 = 2^i' * (2 * j' + 1) - 1"
    moreover have "0 < 2^i * (2 * j + 1)" and "0 < 2^i' * (2 * j' + 1)" by simp+
    ultimately have "2^i * (2 * j + 1) = 2^i' * (2 * j' + 1)" by linarith
    hence "i = i'" and "j = j'" using ex_2_3_factorization_uniqueness by blast+
    thus "(i, j) = (i', j')" by simp
  qed
  ultimately have "bij_betw ?f (UNIV \<times> UNIV) UNIV" by (intro bij_betw_imageI)
  thus "equipotent ((UNIV :: nat set) \<times> (UNIV :: nat set)) (UNIV :: nat set)" by auto
qed

proposition ex_2_4:
  assumes "(a :: real) < (b :: real)"
    and "(c :: real) < (d :: real)"
  shows "equipotent {a .. b} {c .. d}"
proof -
  define f where "f x \<equiv> (d - c) * (x - a) / (b - a) + c" for x
  have "bij_betw f {a .. b} {c .. d}"
  proof (rule bij_betw_imageI')
    fix x and x'
    assume "x \<in> {a .. b}"
      and "x' \<in> {a .. b}"
      and "f x = f x'"
    with f_def have "(d - c) * (x - a) / (b - a) = (d - c) * (x' - a) / (b - a)" by simp
    with assms(1) have "(d - c) * (x - a) = (d - c) * (x' - a)" by simp
    with assms(2) show "x = x'" by simp
  next
    fix x
    assume x: "x \<in> {a .. b}"
    have "c \<le> f x"
    proof -
      from assms(2) have "0 \<le> d - c" by simp
      moreover from x have "0 \<le> x - a" by simp
      moreover from assms(1) have "0 \<le> b - a" by simp
      ultimately have "0 \<le> (d - c) * (x - a) / (b - a)" by simp
      with f_def show ?thesis by simp
    qed
    moreover have "f x \<le> d"
    proof -
      from x and assms(1) have "(x - a) / (b - a) \<le> 1" by simp
      moreover from assms(2) have "0 \<le> d - c" by simp
      ultimately have "(d - c) * ((x - a) / (b - a)) \<le> d - c" by (fact mult_left_le)
      thus ?thesis unfolding f_def by simp
    qed
    ultimately show "f x \<in> {c .. d}" by simp
  next
    fix y
    assume y: "y \<in> {c .. d}"
    define x where "x \<equiv> (y - c) * (b - a) / (d - c) + a"
    with f_def have "f x = y"
    proof -
      have "f x = (d - c) * (((y - c) * (b - a) / (d - c) + a) - a) / (b - a) + c"
        unfolding f_def and x_def ..
      also from assms have "\<dots> = y" by simp
      finally show ?thesis .
    qed
    moreover have "x \<in> {a .. b}"
    proof -
      have "a \<le> x"
      proof -
        from y have "0 \<le> y - c" by simp
        moreover from assms(1) have "0 \<le> b - a" by simp
        moreover from assms(2) have "0 \<le> d - c" by simp
        ultimately have "0 \<le> (y - c) * (b - a) / (d - c)" by simp
        thus ?thesis unfolding x_def by simp
      qed
      moreover have "x \<le> b"
      proof -
        from y and assms(2) have "(y - c) / (d - c) \<le> 1" by simp
        moreover from assms(1) have "0 \<le> (b - a)" by simp
        ultimately have "(b - a) * ((y - c) / (d - c)) \<le> b - a" by (fact mult_left_le)
        hence "(y - c) * (b - a) / (d - c) + a \<le> b" by argo
        thus ?thesis unfolding x_def by simp
      qed
      ultimately show ?thesis by simp
    qed
    ultimately show "y \<in> f ` {a .. b}" by auto
  qed
  thus ?thesis by (fact equipotentI)
qed

lemma non_negative_quadratic_discriminant_implies_real_root:
  assumes "a \<noteq> 0"
    and "discrim a b c \<ge> 0"
  obtains x where "a * x\<^sup>2 + b * x + c = 0"
    and "x = (-b + sqrt(discrim a b c)) / (2 * a)"
  using assms and discriminant_iff by blast

proposition ex_2_5:
  shows "equipotent {-(1 :: real) <..< (1 :: real)} (UNIV :: real set)"
proof -
  define f where "f x \<equiv> x / (1 - x\<^sup>2)" for x :: real
  have "bij_betw f {-(1 ::real) <..< (1 :: real)} (UNIV :: real set)"
  proof (rule bij_betw_imageI')
    fix x and x'
    assume x: "x \<in> {-1 <..< 1}"
      and x': "x' \<in> {-1 <..< 1}"
      and "f x = f x'"
    from this(3) have "x / (1 - x\<^sup>2) = x' / (1 - x'\<^sup>2)" unfolding f_def .
    hence "(1 - x\<^sup>2) * (1 - x'\<^sup>2) * (x / (1 - x\<^sup>2)) = (1 - x\<^sup>2) * (1 - x'\<^sup>2) * (x' / (1 - x'\<^sup>2))" by simp
    moreover have "1 - x\<^sup>2 \<noteq> 0"
    proof (rule notI)
      assume "1 - x\<^sup>2 = 0"
      hence "x = 1 \<or> x = -1" by algebra
      with x show "False" by simp
    qed
    moreover have "1 - x'\<^sup>2 \<noteq> 0"
    proof (rule notI)
      assume "1 - x'\<^sup>2 = 0"
      hence "x' = 1 \<or> x' = -1" by algebra
      with x' show "False" by simp
    qed
    ultimately have "(1 - x'\<^sup>2) * x = (1 - x\<^sup>2) * x'" by auto
    hence "x - x * x'\<^sup>2 - x' + x' * x\<^sup>2 = 0" by argo
    hence *: "x - x' + x * x' * (x - x') = 0" by algebra
    {
      assume "x \<noteq> x'"
      with * have "1 + x * x' = 0" by algebra
      moreover from x and x' have "-1 < x * x'"
      proof -
        consider (A) "x * x' \<ge> 0"
            | (B) "x > 0"
            | (C) "x' > 0"
          by (metis less_eq_real_def linorder_neqE_linordered_idom zero_le_mult_iff)
        thus ?thesis
        proof cases
          case A
          thus ?thesis by simp
        next
          case B
          moreover from x' have "-1 < x'" by simp
          ultimately have "x * (-1) < x * x'" by (blast dest: mult_strict_left_mono)
          hence "-x < x * x'" by simp
          moreover from x have "-1 < -x" by simp
          ultimately show ?thesis by simp
        next
          case C
          moreover from x have "-1 < x" by simp
          ultimately have "(-1) * x' < x * x'" by (blast dest: mult_strict_right_mono)
          hence "-x' < x * x'" by simp
          moreover from x' have "-1 < -x'" by simp
          ultimately show ?thesis by simp
        qed
      qed
      ultimately have "False" by simp
    }
    thus "x = x'" by (fact ccontr)
  next
    fix x :: real
    show "f x \<in> UNIV" by simp
  next
    fix y :: real
    {
      assume y: "y = 0"
      with f_def have  "f 0 = y" by simp
      hence "y \<in> f ` {-1 <..< 1}" by auto
    }
    moreover {
      assume "y \<noteq> 0"
      have discrim: "discrim y 1 (-y) \<ge> 0" unfolding discrim_def by simp
      from \<open>y \<noteq> 0\<close> and discrim obtain x where x_root: "y * x\<^sup>2 + 1 * x + (-y) = 0"
        and x: "x = (-1 + sqrt(discrim y 1 (-y))) / (2 * y)"
        by (elim non_negative_quadratic_discriminant_implies_real_root)
      have "f x = y"
      proof -
        from x_root have "(1 - x\<^sup>2) * y = x" by argo
        moreover have "1 - x\<^sup>2 \<noteq> 0"
        proof (rule notI)
          assume "1 - x\<^sup>2 = 0"
          moreover from this and x_root have "x = 0" by simp
          ultimately show "False" by simp
        qed
        ultimately have "y = x / (1 - x\<^sup>2)" by (metis nonzero_mult_div_cancel_left)
        thus ?thesis unfolding f_def by simp
      qed
      moreover have "x \<in> {-1 <..< 1}"
      proof -
        {
          assume "y > 0"
          have "0 < x"
          proof -
            from \<open>y > 0\<close> have "0 < -1 + sqrt(1 + 4 * y * y)" by simp
            moreover from \<open>y > 0\<close> have "0 < 2 * y" by simp
            ultimately have "0 < (-1 + sqrt(1 + 4 * y * y)) / (2 * y)" by simp
            with x show "0 < x" unfolding discrim_def by simp
          qed
          moreover have "x < 1"
          proof -
            from \<open>y > 0\<close> have "1 + 4 * y * y < (1 + 2 * y) * (1 + 2 * y)" by argo
            hence "sqrt(1 + 4 * y * y) < sqrt((1 + 2 * y) * (1 + 2 * y))"
              by (fact real_sqrt_less_mono)
            moreover from \<open>y > 0\<close> have "0 < 1 + 2 * y" by simp
            ultimately have "sqrt(1 + 4 * y * y) < 1 + 2 * y" by simp
            hence "-1 + sqrt(1 + 4 * y * y) < 2 * y" by simp
            moreover from \<open>y > 0\<close> have "0 < 2 * y" by simp
            ultimately have "(-1 + sqrt(1 + 4 * y * y)) / (2 * y) < 1" by simp
            with x show "x < 1" unfolding discrim_def by simp
          qed
          ultimately have "x \<in> {-1 <..< 1}" by simp
        }
        moreover {
          assume "y < 0"
          have "-1 < x"
          proof -
            from \<open>y < 0\<close> have "0 < -4 * y" by simp
            hence "1 + 4 * y * y < (1 - 2 * y) * (1 - 2 * y)" by argo
            hence "sqrt(1 + 4 * y * y) < sqrt((1 - 2 * y) * (1 - 2 * y))"
              by (fact real_sqrt_less_mono)
            moreover from \<open>y < 0\<close> have "0 < 1 - 2 * y" by simp
            ultimately have "sqrt(1 + 4 * y * y) < 1 - 2 * y" by simp
            hence "2 * y < 1 - sqrt(1 + 4 * y * y)" by simp
            moreover from \<open>y < 0\<close> have "2 * y < 0" by simp
            ultimately have "(1 - sqrt(1 + 4 * y * y)) / (2 * y) < 1" by simp
            hence "-1 < (-1 + sqrt(1 + 4 * y * y)) / (2 * y)" by argo
            with x show ?thesis unfolding discrim_def by simp
          qed
          moreover have "x < 0"
          proof -
            from \<open>y < 0\<close> have "y \<noteq> 0" by simp
            hence "0 < y * y" using not_real_square_gt_zero by blast
            hence "0 < -1 + sqrt(1 + 4 * y * y)" by simp
            moreover from \<open>y < 0\<close> have "2 * y < 0" by simp
            ultimately have "(-1 + sqrt(1 + 4 * y * y)) / (2 * y) < 0" by (fact divide_pos_neg)
            with x show ?thesis unfolding discrim_def by simp
          qed
          ultimately have "x \<in> {-1 <..< 1}" by simp
        }
        moreover note \<open>y \<noteq> 0\<close>
        ultimately show "x \<in> {-1 <..< 1}" by argo
      qed
      ultimately have "y \<in> f ` {-1 <..< 1}" by auto
    }
    ultimately show "y \<in> f ` {-1 <..< 1}" by auto
  qed
  thus ?thesis by auto
qed

\<comment> \<open>Proof for the remaining propositions of example 2.5 is postponed after theorem 2.2\<close>

subsection \<open>B) Bernstein Theorem\<close>

fun bernstein_seq :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a set"
  and bernstein_seq' :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'b set" where
    "bernstein_seq' A B f g 0 = B - f ` A"
  | "bernstein_seq A B f g n = g ` bernstein_seq' A B f g n"
  | "bernstein_seq' A B f g (Suc n) = f ` bernstein_seq A B f g n"

lemma bernstein_seq_subset:
  assumes "f ` A \<subseteq> B"
    and "g ` B \<subseteq> A"
  shows "bernstein_seq A B f g n \<subseteq> A"
proof (induct n)
  case 0
  have "bernstein_seq A B f g 0 = g ` (B - f ` A)" by simp
  also from assms have "\<dots> \<subseteq> A" by auto
  finally show "?case" .
next
  case (Suc n)
  have "bernstein_seq A B f g (Suc n) = g ` f ` bernstein_seq A B f g n" by simp
  with assms and Suc.hyps show "?case" by fastforce
qed

lemma bernstein_seq'_subset:
  assumes "f ` A \<subseteq> B"
    and "g ` B \<subseteq> A"
  shows "bernstein_seq' A B f g n \<subseteq> B"
proof (induct n)
  case 0
  have "bernstein_seq' A B f g 0 = B - f ` A" by simp
  also have "\<dots> \<subseteq> B" by auto
  finally show "?case" .
next
  case (Suc n)
  have "bernstein_seq' A B f g (Suc n) = f ` g ` bernstein_seq' A B f g n" by simp
  with assms and Suc.hyps show "?case" by fastforce
qed

lemma zero_Un_UNION_Suc_eq:
  shows "A 0 \<union> (\<Union>n. A (Suc n)) = (\<Union>n. A n)"
proof -
  have "A 0 \<union> (\<Union>n. A (Suc n)) = (\<Union>n \<in> {0}. A n) \<union>(\<Union>n \<in> {Suc n | n. True}. A n)" by auto
  also have "\<dots> = (\<Union>n \<in> {0} \<union> {Suc n | n. True}. A n)" by simp
  also have "\<dots> = (\<Union>n. A n)"
  proof -
    {
      fix n
      have "n \<in> {0} \<union> {Suc n | n. True}"
      proof (induct n)
        case 0
        show "?case" by simp
      next
        case (Suc n)
        show "?case" by simp
      qed
    }
    hence "{0} \<union> {Suc n | n. True} = UNIV" by blast
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

theorem thm_2_2:
  assumes "f ` A \<subseteq> B"
    and "inj_on f A"
    and "g ` B \<subseteq> A"
    and "inj_on g B"
  shows "equipotent A B"
proof -
  let ?A = "\<Union>n. bernstein_seq A B f g n"
  let ?A' = "A - ?A"
  let ?B = "\<Union>n. bernstein_seq' A B f g n"
  let ?B' = "B - ?B"
  {
    fix n
    from assms(1,3) have "bernstein_seq A B f g n \<subseteq> A" by (rule bernstein_seq_subset)
  }
  hence "?A \<subseteq> A" by auto
  hence "?A' \<subseteq> A" by auto
  {
    fix n
    from assms(1,3) have "bernstein_seq' A B f g n \<subseteq> B" by (rule bernstein_seq'_subset)
  }
  hence "?B \<subseteq> B" by auto
  hence "?B' \<subseteq> B" by auto
  have "f ` ?A' = ?B'"
  proof -
    from \<open>?A \<subseteq> A\<close> and assms(2) have "f ` ?A' = f ` A - f ` ?A" by (intro prob_1_4_5_c)
    also have "\<dots> = f ` A - (\<Union>n. f ` bernstein_seq A B f g n)" by blast
    also have "\<dots> = f ` A - (\<Union>n. bernstein_seq' A B f g (Suc n))" by simp
    also from assms(1) have "\<dots> = B - (B - f ` A) - (\<Union>n. bernstein_seq' A B f g (Suc n))" by auto
    also have "\<dots> = B - bernstein_seq' A B f g 0 - (\<Union>n. bernstein_seq' A B f g (Suc n))" by simp
    also have "\<dots> = B - (bernstein_seq' A B f g 0 \<union> (\<Union>n. bernstein_seq' A B f g (Suc n)))" by auto
    also have "\<dots> = ?B'"
      by (simp only: zero_Un_UNION_Suc_eq[where A = "\<lambda>n. bernstein_seq' A B f g n"])
    finally show ?thesis .
  qed
  moreover from assms(2) have "inj_on f ?A'" by (fact inj_on_diff)
  ultimately have "bij_betw f ?A' ?B'" by (intro bij_betw_imageI)
  have "g ` ?B = ?A"
  proof (rule surj_onI)
    fix b
    assume "b \<in> ?B"
    then obtain n where "b \<in> bernstein_seq' A B f g n" by fast
    hence "g b \<in> bernstein_seq A B f g n" by simp
    thus "g b \<in> ?A" by auto
  next
    fix a
    assume "a \<in> ?A"
    then obtain n where "a \<in> bernstein_seq A B f g n" by blast
    hence "a \<in> g ` bernstein_seq' A B f g n" by simp
    then obtain b where "b \<in> bernstein_seq' A B f g n" and "a = g b" by auto
    from this(1) have "b \<in> ?B" by auto
    with \<open>a = g b\<close> show "a \<in> g ` ?B" by simp
  qed
  moreover from \<open>?B \<subseteq> B\<close> and assms(4) have "inj_on g ?B" by (elim inj_on_subset)
  ultimately have "bij_betw g ?B ?A" by (intro bij_betw_imageI)
  then obtain f' where "bij_betw f' ?A ?B" using bij_betw_inv by blast
  hence "f' ` ?A = ?B" by (fact bij_betw_imp_surj_on)
  let ?F = "\<lambda>a. if a \<in> ?A' then f a else f' a"
  have "?F ` A = B"
  proof (rule surj_onI)
    fix a
    assume "a \<in> A"
    {
      assume "a \<in> ?A'"
      hence "?F a = f a" by simp
      with \<open>a \<in> A\<close> and assms(1) have "?F a \<in> B" by fast
    }
    moreover {
      assume "a \<notin> ?A'"
      hence "?F a = f' a" by argo
      also have "\<dots> \<in> ?B"
      proof -
        from \<open>a \<in> A\<close> and \<open>a \<notin> ?A'\<close> have "a \<in> ?A" by simp
        moreover note \<open>f' ` ?A = ?B\<close>
        ultimately show "f' a \<in> ?B" by blast
      qed
      also note \<open>\<dots> \<subseteq> B\<close>
      finally have "?F a \<in> B" .
    }
    ultimately show "?F a \<in> B" by blast
  next
    fix b
    assume "b \<in> B"
    {
      assume "b \<in> ?B"
      with \<open>f' ` ?A = ?B\<close> obtain a where "a \<in> ?A" and "b = f' a" by blast
      hence "?F a = b" by simp
      moreover from \<open>a \<in> ?A\<close> and \<open>?A \<subseteq> A\<close> have "a \<in> A" ..
      ultimately have "b \<in> ?F ` A" by blast
    }
    moreover {
      assume "b \<notin> ?B"
      with \<open>b \<in> B\<close> have "b \<in> ?B'" by simp
      with \<open>f ` ?A' = ?B'\<close> have "b \<in> f ` ?A'" by simp
      then obtain a where "a \<in> ?A'" and "b = f a" by blast
      hence "?F a = b" by argo
      moreover from \<open>a \<in> ?A'\<close> and \<open>?A' \<subseteq> A\<close> have "a \<in> A" ..
      ultimately have "b \<in> ?F ` A" by blast
    }
    ultimately show "b \<in> ?F ` A" by blast
  qed
  moreover have "inj_on ?F A"
  proof (rule inj_onI)
    fix a and a'
    assume "a \<in> A" and
      "a' \<in> A" and
      "?F a = ?F a'"
    consider (A) "a \<in> ?A'" and "a' \<in> ?A'" |
      (B) "a \<in> ?A'" and "a' \<notin> ?A'" |
      (C) "a \<notin> ?A'" and "a' \<in> ?A'" |
      (D) "a \<notin> ?A'" and "a' \<notin> ?A'" by blast
    thus "a = a'"
    proof cases
      case A
      with \<open>?F a = ?F a'\<close> have "f a = f a'" by argo
      with A and \<open>inj_on f ?A'\<close> show ?thesis by (elim inj_onD)
    next
      case B
      from B(2) and \<open>a' \<in> A\<close> have "a' \<in> ?A" by blast
      from B and \<open>?F a = ?F a'\<close> have "f a = f' a'" by argo
      moreover from \<open>a \<in> ?A'\<close> and \<open>f ` ?A' = ?B'\<close> have "f a \<in> ?B'" by blast
      moreover from \<open>a' \<in> ?A\<close> and \<open>f' ` ?A = ?B\<close> have "f' a' \<in> ?B" by blast
      ultimately have "False" by simp
      thus ?thesis ..
    next
      case C
      from C(1) and \<open>a \<in> A\<close> have "a \<in> ?A" by simp
      from C and \<open>?F a = ?F a'\<close> have "f' a = f a'" by argo
      moreover from \<open>a \<in> ?A\<close> and \<open>f' ` ?A = ?B\<close> have "f' a \<in> ?B" by blast
      moreover from \<open>a' \<in> ?A'\<close> and \<open>f ` ?A' = ?B'\<close> have "f a' \<in> ?B'" by blast
      ultimately have "False" by simp
      thus ?thesis ..
    next
      case D
      from D and \<open>?F a = ?F a'\<close> have "f' a = f' a'" by argo
      moreover from D and \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> have "a \<in> ?A" and "a' \<in> ?A" by simp+
      moreover from \<open>bij_betw f' ?A ?B\<close> have "inj_on f' ?A" by auto
      ultimately show ?thesis by (elim inj_onD)
    qed
  qed
  ultimately have "bij_betw ?F A B" by (intro bij_betw_imageI)
  thus ?thesis by auto
qed

lemma ex_2_5':
  assumes "(a :: real) < (b :: real)"
    and "(c :: real) < (d :: real)"
  obtains f where "f ` {a <..< b} \<subseteq> {c <..< d}"
    and "inj_on f {a <..< b}"
proof -
  define f where "f x \<equiv> (d - c) * (x - a) / (b - a) + c" for x
  have "f ` {a <..< b} \<subseteq> {c <..< d}"
  proof (rule image_subsetI)
    fix x
    assume x: "x \<in> {a <..< b}"
    have "c < f x"
    proof -
      from assms(1) have "0 < b - a" by simp
      moreover from assms(2) have "0 < d - c" by simp
      moreover from x have "0 < x - a" by simp
      ultimately show ?thesis unfolding f_def by simp
    qed
    moreover have "f x < d"
    proof -
      from assms(1) have "0 < b - a" by simp
      moreover from x have "0 < x - a" by simp
      moreover from x have "x - a < b - a" by simp
      ultimately have "(x - a) / (b - a) < 1" by simp
      moreover from assms(2) have "0 < d - c" by simp
      ultimately have "(d - c) * ((x - a) / (b - a)) < (d - c) * 1" by (fact mult_strict_left_mono)
      thus ?thesis unfolding f_def by simp
    qed
    ultimately show "f x \<in> {c <..< d}" by simp
  qed
  moreover have "inj_on f {a <..< b}"
  proof (rule inj_onI)
    fix x and x'
    assume "f x = f x'"
    hence "(d - c) * (x - a) / (b - a) = (d - c) * (x' - a) / (b - a)" unfolding f_def by simp
    moreover from assms(1) have "b - a \<noteq> 0" by simp
    ultimately have "(d - c) * (x - a) = (d - c) * (x' - a)" by simp
    moreover from assms(2) have "d - c \<noteq> 0" by simp
    ultimately show "x = x'" by simp
  qed
  ultimately show thesis by (fact that)
qed

lemma ex_2_5'':
  assumes "(a :: real) < (b :: real)"
    and "(c :: real) < (d :: real)"
  shows "equipotent {a <..< b} {c <..< d}"
proof -
  from assms obtain f where f1: "f ` {a <..< b} \<subseteq> {c <..< d}"
    and f2: "inj_on f {a <..< b}" by (auto elim: ex_2_5')
  from assms obtain g where g1: "g ` {c <..< d} \<subseteq> {a <..< b}"
    and g2: "inj_on g {c <..< d}" by (auto elim: ex_2_5')
  from f1 and f2 and g1 and g2 show ?thesis by (fact thm_2_2)
qed

lemma ex_2_5''':
  assumes "(a :: real) < (b :: real)"
  shows "equipotent {a <..< b} (UNIV :: real set)"
proof -
  from assms have "equipotent {a <..< b} {-(1 :: real) <..< (1 :: real)}" by (simp add: ex_2_5'')
  moreover have "equipotent {-(1 :: real) <..< (1 :: real)} (UNIV :: real set)" by (fact ex_2_5)
  ultimately show ?thesis by (fact prop_2_1_3)
qed

theorem thm_2_2':
  assumes "f ` A \<subseteq> B"
    and "inj_on f A"
    and "f' ` A = B"
  shows "equipotent A B"
proof -
  from assms(3) obtain g where "g ` B \<subseteq> A" and "inj_on g B" by (elim cor_inj_on_iff_surj_on_b)
  moreover from assms(3) have "f' ` A \<subseteq> B" by simp
  moreover note assms(1,2)
  ultimately show "equipotent A B" by (intro thm_2_2)
qed

theorem thm_2_2'':
  assumes "f ` A = B"
    and "g ` B = A"
  shows "equipotent A B"
proof -
  from assms(2) obtain f' where "f' ` A \<subseteq> B" and "inj_on f' A" by (elim cor_inj_on_iff_surj_on_b)
  with assms(1) show ?thesis by (intro thm_2_2')
qed

lemma surj_on_from_subset_imp_surj_on:
  assumes "f ` A' = B"
    and "A' \<subseteq> A"
    and "A' = {} \<Longrightarrow> A = {}"
  obtains f' where "f' ` A = B"
proof -
  {
    assume "A' = {}"
    with assms(1,3) have "A = {}" and "B = {}" by simp+
    hence "\<exists>f'. f' ` A = B" by simp
  }
  moreover {
    assume "A' \<noteq> {}"
    with assms(1) have "B \<noteq> {}" by auto
    then obtain b where "b \<in> B" by auto
    let ?f' = "\<lambda>a. if a \<in> A' then f a else b"
    have "?f' ` A = B"
    proof (rule surj_onI)
      fix a
      assume "a \<in> A"
      {
        assume "a \<in> A'"
        with assms(1) have "?f' a \<in> B" by auto
      }
      moreover {
        assume "a \<notin> A'"
        with \<open>b \<in> B\<close> have "?f' a \<in> B" by simp
      }
      ultimately show "?f' a \<in> B" by simp
    next
      fix b'
      assume "b' \<in> B"
      with assms(1) obtain a where "a \<in> A'" and "f a = b'" by blast
      hence "?f' a = b'" by simp
      moreover from \<open>a \<in> A'\<close> and assms(2) have "a \<in> A" ..
      ultimately show "b' \<in> ?f' ` A" by auto
    qed
    hence "\<exists>f'. f' ` A = B" by blast
  }
  ultimately show "thesis" using that by auto
qed

theorem thm_2_2''':
  assumes "B\<^sub>1 \<subseteq> B"
    and "equipotent A B\<^sub>1"
    and "A\<^sub>1 \<subseteq> A"
    and "equipotent B A\<^sub>1"
  shows "equipotent A B"
proof -
  from assms(2) obtain f where "bij_betw f A B\<^sub>1" by auto
  then obtain g where "bij_betw g B\<^sub>1 A" by (auto dest: bij_betw_inv)
  hence "g ` B\<^sub>1 = A" by auto
  moreover have "B\<^sub>1 = {} \<Longrightarrow> B = {}"
  proof -
    assume "B\<^sub>1 = {}"
    with assms(2) have "A = {}" by simp
    with assms(3) have "A\<^sub>1 = {}" by simp
    with assms(4) show "B = {}" by simp
  qed
  moreover note assms(1)
  ultimately obtain g' where "g' ` B = A" using surj_on_from_subset_imp_surj_on by blast
  from assms(4) obtain g'' where "bij_betw g'' B A\<^sub>1" by auto
  then obtain f' where "bij_betw f' A\<^sub>1 B" by (auto dest: bij_betw_inv)
  hence "f' ` A\<^sub>1 = B" by auto
  moreover have "A\<^sub>1 = {} \<Longrightarrow> A = {}"
  proof -
    assume "A\<^sub>1 = {}"
    with assms(4) have "B = {}" by simp
    with assms(1) have "B\<^sub>1 = {}" by simp
    with assms(2) show "A = {}" by simp
  qed
  moreover note assms(3)
  ultimately obtain f'' where "f'' ` A = B" by (auto intro: surj_on_from_subset_imp_surj_on)
  with \<open>g' ` B = A\<close> show "equipotent A B" by (intro thm_2_2'')
qed

subsection \<open>C) Notion of Cardinality\<close>

abbreviation aleph_zero :: "nat rel" ("\<aleph>\<^sub>0")
  where "aleph_zero \<equiv> |UNIV :: nat set|"

abbreviation aleph :: "real rel" ("\<aleph>")
  where "aleph \<equiv> |UNIV :: real set|"

lemmas card_eqI [intro] = card_of_ordIsoI

lemma card_eqI' [intro]:
  assumes "equipotent A B"
  shows "|A| =o |B|"
proof -
  from assms obtain f where "bij_betw f A B" by auto
  thus ?thesis by auto
qed

lemma card_eqE [elim]:
  assumes "|A| =o |B|"
  obtains f where "bij_betw f A B"
proof -
  from assms obtain f where "bij_betw f A B" using card_of_ordIso by blast
  thus "thesis" by (fact that)
qed

lemma card_eqE' [elim]:
  assumes "|A| =o |B|"
  obtains f where "bij_betw f B A"
proof -
  from assms obtain f where "bij_betw f A B" by auto
  hence "bij_betw (inv_into A f) B A" by (fact bij_betw_inv_into)
  with that show thesis by simp
qed

proposition card_eq_definition:
  shows "|A| =o |B| \<longleftrightarrow> equipotent A B"
  by auto

lemma card_eq_refl [simp]:
  shows "|A| =o |A|"
proof -
  have "equipotent A A" by simp
  thus ?thesis by auto
qed

lemma card_eq_sym:
  fixes A :: "'a set"
    and B :: "'b set"
  assumes "|A| =o |B|"
  shows "|B| =o |A|"
proof -
  from assms have "equipotent A B" by auto
  hence "equipotent B A" by (fact prop_2_1_2)
  thus ?thesis by auto
qed

lemma card_eq_trans [trans]:
  fixes A :: "'a set"
    and B :: "'b set"
    and C :: "'c set"
  assumes "|A| =o |B|"
    and "|B| =o |C|"
  shows "|A| =o |C|"
proof -
  from assms(1) have "equipotent A B" by auto
  moreover from assms(2) have "equipotent B C" by auto
  ultimately have "equipotent A C" by (fact prop_2_1_3)
  thus ?thesis by auto
qed

proposition czero_definition:
  shows "(czero :: 'a rel) = |{} :: 'a set|"
  by (fact czero_def)

lemma empty_card_eq_czero:
  shows "|{} :: 'a set| =o (czero :: 'b rel)"
proof -
  define f :: "'a \<Rightarrow> 'b" where "f a \<equiv> undefined" for a
  from f_def have "inj_on f {}" and "f ` {} = {}" by simp_all
  hence "bij_betw f ({} :: 'a set) ({} :: 'b set)" by (intro bij_betw_imageI)
  hence "|{} :: 'a set| =o |{} :: 'b set|" by auto
  thus ?thesis unfolding czero_definition by simp
qed

lemma empty_card_eq_empty:
  shows "|{} :: 'a set| =o |{} :: 'b set|"
proof -
  define f :: "'a \<Rightarrow> 'b" where "f a \<equiv> undefined" for a
  from f_def have "inj_on f {}" and "f ` {} = {}" by simp_all
  hence "bij_betw f {} {}" by (intro bij_betw_imageI)
  thus ?thesis by auto
qed

lemma czero_card_eq_empty:
  shows "(czero :: 'a rel) =o |{} :: 'b set|"
proof -
  have "(czero :: 'a rel) = |{} :: 'a set|" unfolding czero_definition ..
  moreover have "|{} :: 'a set| =o |{} :: 'b set|" by (fact empty_card_eq_empty)
  ultimately show ?thesis by simp
qed

lemma czero_refl:
  shows "(czero :: 'a rel) =o (czero :: 'b rel)"
proof -
  define f :: "'a \<Rightarrow> 'b" where "f a \<equiv> undefined" for a
  have "bij_betw f ({} :: 'a set) ({} :: 'b set)" by (auto intro: bij_betwI')
  hence "|{} :: 'a set| =o |{} :: 'b set|" by auto
  thus ?thesis unfolding czero_definition by simp
qed

lemma eq_empty_imp_card_eq_czero:
  fixes A :: "'a set"
  assumes "A = {}"
  shows "|A| =o (czero :: 'b rel)"
proof -
  from assms have "|A| = |{} :: 'a set|" by auto
  also have "\<dots> =o (czero :: 'b rel)" by (fact empty_card_eq_czero)
  finally show ?thesis by auto
qed

proposition cone_definition [simp]:
  shows "cone =o |{a}|"
proof -
  have "cone = |{()}|" by (simp only: card_of_refl cone_def)
  also have "\<dots> =o |{a}|"
  proof -
    let ?f = "\<lambda>x. a"
    have "?f ` {()} = {a}" by simp
    moreover have "inj_on ?f {()}" by simp
    ultimately have "bij_betw ?f {()} {a}" by (intro bij_betw_imageI)
    thus ?thesis by (fact card_of_ordIsoI)
  qed
  finally show "cone =o |{a}|" .
qed

lemma singleton_card_eq_cone:
  shows "|{a}| =o cone"
proof -
  define f where "f x \<equiv> if x = a then () else undefined" for x
  from f_def have "inj_on f {a}" by simp
  moreover from f_def have "f ` {a} = {()}" by simp
  ultimately have "bij_betw f {a} {()}" by (intro bij_betw_imageI)
  hence "|{a}| =o |{()}|" by auto
  thus ?thesis unfolding cone_def by simp
qed

lemma ctwo_definition:
  shows "ctwo = |UNIV :: bool set|"
  unfolding ctwo_def ..

lemma doubleton_card_eq_ctwo:
  assumes "a \<noteq> b"
  shows "|{a, b}| =o ctwo"
  using assms unfolding ctwo_definition by (simp add: card_of_bool ordIso_symmetric)

lemma card_leqI [intro]:
  assumes "f ` A \<subseteq> B"
    and "inj_on f A"
  shows "|A| \<le>o |B|"
proof -
  from assms show "|A| \<le>o |B|" by (blast intro: card_of_ordLeq[THEN iffD1])
qed

lemma card_leqE [elim]:
  assumes "|A| \<le>o |B|"
  obtains f where "f ` A \<subseteq> B" and "inj_on f A"
proof -
  from assms obtain f where "f ` A \<subseteq> B" and "inj_on f A"
    by (fast dest: card_of_ordLeq[THEN iffD2])
  thus "thesis" by (fact that)
qed

proposition card_leq_definition:
  shows "|A| \<le>o |B| \<longleftrightarrow> (\<exists>f. f ` A \<subseteq> B \<and> inj_on f A)"
  by fast

lemma card_lessI [intro]:
  assumes "|A| \<le>o |B|"
    and "\<not>|A| =o |B|"
  shows "|A| <o |B|"
  using assms by (simp add: ordLeq_iff_ordLess_or_ordIso)

lemma card_less_imp_card_leq [dest]:
  assumes "|A| <o |B|"
  shows "|A| \<le>o |B|"
  by (fact ordLess_imp_ordLeq[OF assms])

lemma card_less_imp_not_card_eq [dest]:
  assumes "|A| <o |B|"
  shows "\<not>|A| =o |B|"
  by (fact not_ordLess_ordIso[OF assms])

lemma card_lessE [elim]:
  assumes "|A| <o |B|"
  obtains "|A| \<le>o |B|"
    and "\<not>|A| =o |B|"
  using assms by auto

lemma card_less_definition:
  shows "|A| <o |B| \<longleftrightarrow> |A| \<le>o |B| \<and> \<not> |A| =o |B|"
  by auto

lemma card_eq_imp_card_leq:
  assumes "|A| =o |B|"
  shows "|A| \<le>o |B|"
proof -
  from assms obtain f where "bij_betw f A B" by auto
  hence "f ` A \<subseteq> B" and "inj_on f A" by auto
  thus ?thesis by auto
qed

theorem thm_2_3_1 [simp]:
  shows "|A| \<le>o |A|"
proof -
  have "|A| =o |A|" by simp
  thus ?thesis by (fact card_eq_imp_card_leq)
qed

theorem thm_2_3_2:
  assumes "|A| \<le>o |B|"
    and "|B| \<le>o |A|"
  shows "|A| =o |B|"
proof -
  from assms(1) obtain f where "f ` A \<subseteq> B" and "inj_on f A" by auto
  moreover from assms(2) obtain g where "g ` B \<subseteq> A" and "inj_on g B" by auto
  ultimately have "equipotent A B" by (rule thm_2_2)
  thus ?thesis by (fact card_eqI')
qed

theorem thm_2_3_3 [trans]:
  assumes "|A| \<le>o |B|"
    and "|B| \<le>o |C|"
  shows "|A| \<le>o |C|"
proof -
  from assms(1) obtain f where "f ` A \<subseteq> B" and "inj_on f A" by auto
  from assms(2) obtain g where "g ` B \<subseteq> C" and "inj_on g B" by auto
  from \<open>f ` A \<subseteq> B\<close> and \<open>g ` B \<subseteq> C\<close> have "(g \<circ> f) ` A \<subseteq> C" by fastforce
  moreover from \<open>f ` A \<subseteq> B\<close> and \<open>inj_on f A\<close> and \<open>inj_on g B\<close> have "inj_on (g \<circ> f) A"
    by (fact thm_1_5_b)
  ultimately show ?thesis by blast
qed

lemma card_eq_card_leq_trans [trans]:
  fixes A :: "'a set"
    and B :: "'b set"
    and C :: "'c set"
  assumes "|A| =o |B|"
    and "|B| \<le>o |C|"
  shows "|A| \<le>o |C|"
proof -
  from assms(1) have "|A| \<le>o |B|" by auto
  also note assms(2)
  finally show ?thesis .
qed

lemma card_leq_card_eq_trans [trans]:
  fixes A :: "'a set"
    and B :: "'b set"
    and C :: "'c set"
  assumes "|A| \<le>o |B|"
    and "|B| =o |C|"
  shows "|A| \<le>o |C|"
proof -
  note assms(1)
  also from assms(2) have "|B| \<le>o |C|" by (fact card_eq_imp_card_leq)
  finally show ?thesis .
qed

subsection \<open>Problems\<close>

proposition prob_2_1_2:
  fixes X :: "'a set"
  assumes "X \<subseteq> Y"
    and "Y \<subseteq> Z"
    and "equipotent X Z"
  obtains "equipotent X Y" and "equipotent Y Z"
proof -
  have "equipotent X Y"
  proof -
    from assms(3) have "equipotent Z X" by (fact prop_2_1_2)
    then obtain h where "bij_betw h Z X" by auto
    have "equipotent X X" by simp
    moreover note assms(1)
    moreover have "equipotent Y (h ` Y)"
    proof (rule equipotentI)
      from \<open>bij_betw h Z X\<close> and assms(2) have "bij_betw h Y (h ` Y)"
        by (auto elim: bij_betw_subset)
      moreover have "bij_betw id Y Y" by simp
      ultimately show "bij_betw (h \<circ> id) Y (h ` Y)" by simp
    qed
    moreover from \<open>bij_betw h Z X\<close> and assms(2) have "h ` Y \<subseteq> X" by auto
    ultimately show ?thesis by (blast intro: thm_2_2''')
  qed
  moreover have "equipotent Y Z"
  proof -
    from \<open>equipotent X Y\<close> have "equipotent Y X" by (fact prop_2_1_2)
    also note assms(3)
    finally show ?thesis .
  qed
  ultimately show "thesis" by (fact that)
qed

(* TODO: prob_2_1_3 *)

proposition prob_2_1_4:
  fixes A :: "'a set"
  assumes "B \<noteq> {}"
  shows "|A| \<le>o |A \<times> B|"
proof -
  from assms obtain b where "b \<in> B" by auto
  let ?f = "\<lambda>a :: 'a. (a, b)"
  {
    fix a
    assume "a \<in> A"
    with \<open>b \<in> B\<close> have "?f a \<in> A \<times> B" by simp
  }
  hence "?f ` A \<subseteq> A \<times> B" by auto
  moreover have "inj_on ?f A"
  proof (rule inj_onI)
    fix a and a'
    assume "?f a = ?f a'"
    thus "a = a'" by simp
  qed
  ultimately show ?thesis by auto
qed

proposition prob_2_1_5:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<noteq> {}"
    and "disjoint_family_on A \<Lambda>"
  shows "|\<Lambda>| \<le>o |\<Union>l \<in> \<Lambda>. A l|"
proof -
  let ?f = "\<lambda>a. (THE l. l \<in> \<Lambda> \<and> a \<in> A l)"
  have *: "?f a = l" if "l \<in> \<Lambda>" and "a \<in> A l" for a and l
  proof -
    from that have "a \<in> (\<Union>l \<in> \<Lambda>. A l)" by auto
    with assms have "\<exists>!l \<in> \<Lambda>. a \<in> A l" by (intro disjoint_family_on_imp_uniq_idx)
    with that show ?thesis by auto
  qed
  have "?f ` (\<Union>l \<in> \<Lambda>. A l) = \<Lambda>"
  proof (rule surj_onI)
    fix a
    assume "a \<in> (\<Union>l \<in> \<Lambda>. A l)"
    then obtain l where "l \<in> \<Lambda>" and "a \<in> A l" by auto
    hence "?f a = l" by (fact *)
    with \<open>l \<in> \<Lambda>\<close> show "?f a \<in> \<Lambda>" by simp
  next
    fix l
    assume "l \<in> \<Lambda>"
    moreover from this and assms(1) obtain a where "a \<in> A l" by auto
    ultimately have "a \<in> (\<Union>l \<in> \<Lambda>. A l)" and "?f a = l" by (auto dest: *)
    thus "l \<in> ?f ` (\<Union>l \<in> \<Lambda>. A l)" by auto
  qed
  then obtain g where "g ` \<Lambda> \<subseteq> (\<Union>l \<in> \<Lambda>. A l)" and "inj_on g \<Lambda>"
    by (elim cor_inj_on_iff_surj_on_b)
  thus ?thesis by auto
qed

lemma AC_E_ext:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> A l \<noteq> {}"
  obtains a where "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
proof -
  from assms obtain a where a: "a \<in> (\<Pi> l \<in> \<Lambda>. A l)" by (elim AC_E)
  let ?a' = "\<lambda>l. if l \<in> \<Lambda> then a l else undefined"
  {
    fix l
    assume "l \<in> \<Lambda>"
    with a have "?a' l \<in> A l" by auto
  }
  moreover {
    fix l
    assume "l \<notin> \<Lambda>"
    hence "?a' l = undefined" by simp
  }
  ultimately have "?a' \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" by blast
  thus "thesis" by (fact that)
qed

proposition prob_2_1_6:
  assumes "\<And>l. l \<in> \<Lambda> \<Longrightarrow> \<exists>a \<in> A l. \<exists>b \<in> A l. a \<noteq> b"
  shows "|\<Lambda>| \<le>o |\<Pi>\<^sub>E l \<in> \<Lambda>. A l|"
proof -
  {
    fix l
    assume "l \<in> \<Lambda>"
    with assms have "A l \<noteq> {}" by auto
  }
  then obtain a where "a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"  by (elim AC_E_ext)
  {
    fix l
    assume "l \<in> \<Lambda>"
    with assms have "A l - {a l} \<noteq> {}" by auto
  }
  then obtain b where "b \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l - {a l})" by (elim AC_E_ext)
  let ?f = "\<lambda>l. \<lambda>l'. if l' = l then a l' else b l'"
  have "?f ` \<Lambda> \<subseteq> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)"
  proof (rule subsetI)
    fix c
    assume "c \<in> ?f ` \<Lambda>"
    then obtain l where "l \<in> \<Lambda>" and "c = ?f l" by auto
    {
      fix l'
      assume "l' \<in> \<Lambda>"
      from \<open>c = ?f l\<close> have "c l' = ?f l l'" by simp
      {
        assume "l' = l"
        hence "?f l l' = a l'" by simp
        also from this and \<open>a \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)\<close> and \<open>l' \<in> \<Lambda>\<close> have "a l' \<in> A l'" by auto
        finally have "?f l l' \<in> A l'" .
      }
      moreover {
        assume "l' \<noteq> l"
        hence "?f l l' = b l'" by simp
        also from this and \<open>b \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l - {a l})\<close> and \<open>l' \<in> \<Lambda>\<close> have "b l' \<in> A l'" by auto
        finally have "?f l l' \<in> A l'" .
      }
      ultimately have "?f l l' \<in> A l'" by simp
      with \<open>c l' = ?f l l'\<close> have "c l' \<in> A l'" by simp
    }
    moreover {
      fix l'
      assume "l' \<notin> \<Lambda>"
      with \<open>l \<in> \<Lambda>\<close> have "l' \<noteq> l" by auto
      from \<open>c = ?f l\<close> have "c l' = ?f l l'"  by simp
      also from \<open>l' \<noteq> l\<close> have "?f l l' = b l'" by simp
      also from \<open>l' \<notin> \<Lambda>\<close> and \<open>b \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l - {a l})\<close> have "b l' = undefined" by auto
      finally have "c l' = undefined" .
    }
    ultimately show "c \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l)" by (intro PiE_I)
  qed
  moreover have "inj_on ?f \<Lambda>"
  proof (rule inj_onI)
    fix l and l'
    assume "l \<in> \<Lambda>" and
      "l' \<in> \<Lambda>" and
      "?f l = ?f l'"
    {
      assume "l \<noteq> l'"
      hence "?f l' l = b l" by simp
      moreover have "?f l l = a l" by simp
      moreover note \<open>?f l = ?f l'\<close>
      ultimately have "a l = b l" by metis
      also from \<open>l \<in> \<Lambda>\<close> and \<open>b \<in> (\<Pi>\<^sub>E l \<in> \<Lambda>. A l - {a l})\<close> have "b l \<in> A l - {a l}" by blast
      finally have "a l \<in> A l - {a l}" .
      hence "False" by simp
    }
    thus "l = l'" by auto
  qed
  ultimately show ?thesis by auto
qed

proposition prob_2_1_7:
  assumes "f ` A = B"
  obtains R where "equiv A R" and "equipotent B (A // R)"
proof -
  from assms have "f ` A \<subseteq> B" by simp
  then obtain g where "bij_betw g (A // (equiv_kernel_on f A)) (f ` A)"
    by (fastforce elim: prop_1_6_4)
  with assms have "bij_betw g (A // (equiv_kernel_on f A)) B" by blast
  hence "equipotent (A // equiv_kernel_on f A) B" by auto
  hence "equipotent B (A // equiv_kernel_on f A)" by (fact prop_2_1_2)
  moreover have "equiv A (equiv_kernel_on f A)" by (fact equiv_equiv_kernel_on)
  ultimately show "thesis" by (intro that)
qed

(* TODO: prob_2_1_8 *)

end (* context includes cardinal_syntax *)

end
