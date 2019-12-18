theory List_Join_Split
  imports 
    Main
begin

section "Join and split functions for lists of lists"

text "This implements a join and split function for a list of lists, where the lists are delimited by a single type. Works great for strings, which are lists of characters, where the delimiter is a single character."

fun join :: "'t \<Rightarrow> 't list list \<Rightarrow> 't list" where
  "join d [] = []" |
  "join d [x] = x" |
  "join d (x#xs) = x @ [d] @ (join d xs)"

fun join_alt :: "'t \<Rightarrow> 't list list \<Rightarrow> 't list" where
  "join_alt d [] = []" |
  "join_alt d [x] = x" |
  "join_alt d (xs) = join_alt d (butlast (xs)) @ [d] @ last (xs)"

fun split_rec :: "'t \<Rightarrow> 't list \<Rightarrow> 't list list \<Rightarrow> 't list \<Rightarrow> 't list list" where
  "split_rec d [] xss ys = xss @ [ys]" |
  "split_rec d (x#xs) xss ys = (if x = d then split_rec d xs (xss @ [ys]) [] else split_rec d xs xss (ys @ [x]))"

definition split :: "'t \<Rightarrow> 't list \<Rightarrow> 't list list" where
  "split d s \<equiv> split_rec d s [] []"


subsection "Lemma's on definitions"

lemma join_prepend: "xs \<noteq> [] \<Longrightarrow> join d (x#xs) = x @ [d] @ join d xs"
  by (induct xs) simp_all

lemma join_append: "xs \<noteq> [] \<Longrightarrow> join d (xs @ [x]) = join d xs @ [d] @ x"
proof (induct xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys)
  then show ?case
  proof (induct ys)
    case Nil
    then show ?case
      by simp
  next
    case (Cons z zs)
    then show ?case
      by simp
  qed
qed

lemma join_alt_append: "xs \<noteq> [] \<Longrightarrow> join_alt d (xs @ [x]) = join_alt d xs @ [d] @ x"
proof-
  fix xs :: "'a list list"
  fix x :: "'a list"
  assume "xs \<noteq> []"
  then have "join_alt d (xs @ [x]) = join_alt d (butlast (xs @ [x])) @ [d] @ last (xs @ [x])"
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons y ys)
    then show ?case
    proof (induct ys)
      case Nil
      then show ?case
        by simp
    next
      case (Cons z zs)
      then show ?case
        by simp
    qed
  qed
  then show "join_alt d (xs @ [x]) = join_alt d xs @ [d] @ x"
    by simp
qed

lemma join_alt_def: "join d = join_alt d"
proof
  fix d :: "'t"
  fix x :: "'t list list"
  show "join d x = join_alt d x"
  proof (induct x rule: rev_induct)
    case Nil
    then show ?case
      by simp
  next
    case (snoc x xs)
    then show ?case
      using append_Nil join.simps(2) join_alt.simps(2) join_alt_append join_append
      by metis
  qed
qed

lemma join_alt_prepend: "xs \<noteq> [] \<Longrightarrow> join_alt d (x#xs) = x @ [d] @ join_alt d xs"
  using join_alt_def join_prepend
  by metis

lemma join_singleton_preserve: "d \<notin> set xs \<Longrightarrow> d \<notin> set (join d [xs])"
  by simp

lemma split_rec_base_list: "\<And>xss ys. split_rec d xs xss ys = xss @ split_rec d xs [] ys"
proof (induct xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then show ?case
  proof (induct "x = d")
    case True
    then have "split_rec d (x # xs) xss ys = split_rec d xs (xss @ [ys]) []"
      using split_rec.simps(2)
      by metis
    then have "split_rec d xs (xss @ [ys]) [] = xss @ [ys] @ split_rec d xs [] []"
      using True.prems append.assoc
      by metis
    then show ?case
      using True.prems append_Nil split_rec.simps(2)
      by metis
  next
    case False
    then have "split_rec d (x # xs) xss ys = split_rec d xs xss (ys @ [x])"
      using split_rec.simps(2)
      by metis
    then show ?case
      using False.hyps False.prems split_rec.simps(2)
      by metis
  qed
qed

lemma split_rec_delimiter_char: "\<And>xss ys. split_rec d ([d] @ xs) xss ys = xss @ [ys] @ split_rec d xs [] []"
  using append_Cons append_Nil split_rec.simps(2) split_rec_base_list
  by metis

lemma split_rec_not_empty: "\<And>xss ys. xs \<noteq> [] \<Longrightarrow> split_rec d xs xss ys \<noteq> []"
proof-
  fix xs :: "'a list"
  assume "xs \<noteq> []"
  then show "\<And>xss ys. split_rec d xs xss ys \<noteq> []"
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    then show ?case
      using snoc_eq_iff_butlast split_rec.simps
      by metis
  qed
qed

lemma split_rec_singleton_build: "\<And>xss ys. d \<notin> set xs \<Longrightarrow> split_rec d xs xss ys = split_rec d [] xss (ys @ xs)"
proof-
  fix xs :: "'a list"
  assume "d \<notin> set xs"
  then show "\<And>xss ys. split_rec d xs xss ys = split_rec d [] xss (ys @ xs)"
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    then show ?case
      by fastforce
  qed
qed

lemma split_rec_singleton_left: "\<And>xss ys. d \<notin> set xs \<Longrightarrow> split_rec d xs xss ys = xss @ [ys @ xs]"
  by (simp add: split_rec_singleton_build)

lemma split_rec_singleton: "d \<notin> set xs \<Longrightarrow> split_rec d xs [] [] = [xs]"
  by (simp add: split_rec_singleton_left)

lemma split_rec_append: "\<And>xss zs. d \<notin> set ys \<Longrightarrow> split_rec d (xs @ [d] @ ys) xss zs = split_rec d xs xss zs @ [ys]"
  by (induct xs) (simp_all add: split_rec_singleton_left)

lemma split_rec_prepend: "\<And>xss zs. d \<notin> set ys \<Longrightarrow> split_rec d (ys @ [d] @ xs) xss zs = xss @ [zs @ ys] @ split_rec d xs [] []"
proof (induct ys)
  case Nil
  then show ?case
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    then show ?case
      using append_Nil append_Nil2 split_rec_delimiter_char
      by metis
  qed
next
  case (Cons y ys)
  then show ?case
    by auto
qed

lemma split_empty: "split d [] = [[]]"
  by (simp add: split_def)

lemma split_singleton: "d \<notin> set xs \<Longrightarrow> split d xs = [xs]"
  by (simp add: split_def split_rec_singleton)

lemma split_append: "d \<notin> set ys \<Longrightarrow> split d (xs @ [d] @ ys) = split d xs @ [ys]"
  using split_def split_rec_append 
  by metis

lemma split_prepend: "d \<notin> set ys \<Longrightarrow> split d (ys @ [d] @ xs) = [ys] @ split d xs"
  using split_def append.left_neutral split_rec_prepend
  by metis


subsection "Domain & Range"

inductive_set join_bij_domain :: "'t \<Rightarrow> 't list list set"
  for d :: "'t"
  where
    rule_first_elem: "d \<notin> set xs \<Longrightarrow> [xs] \<in> join_bij_domain d" |
    rule_append: "xs \<in> join_bij_domain d \<Longrightarrow> d \<notin> set ys \<Longrightarrow> xs @ [ys] \<in> join_bij_domain d"

inductive_set split_bij_domain :: "'t \<Rightarrow> 't list set"
  for d :: "'t"
  where
    rule_no_delim: "d \<notin> set xs \<Longrightarrow> xs \<in> split_bij_domain d" |
    rule_append: "xs \<in> split_bij_domain d \<Longrightarrow> d \<notin> set ys \<Longrightarrow> xs @ [d] @ ys \<in> split_bij_domain d"


subsection "Inverse function"

lemma join_inverse: "x \<in> join_bij_domain d \<Longrightarrow> split d (join d x) = x"
proof (induct x rule: join_bij_domain.induct)
  case (rule_first_elem xs)
  then show ?case
    by (simp add: split_singleton)
next
  case (rule_append xs ys)
  then have "split d (join d (xs @ [ys])) = split d (join d xs @ [d] @ ys)"
    using join.simps(1) join_append list.distinct(1) split_empty
    by metis
  then have "split d (join d (xs @ [ys])) = split d (join d xs) @ [ys]"
    using rule_append.hyps(3) split_append by fastforce
  then show ?case
    by (simp add: rule_append.hyps(2))
qed

lemma split_inverse: "x \<in> split_bij_domain d \<Longrightarrow> join d (split d x) = x"
proof (induct x rule: split_bij_domain.induct)
  case (rule_no_delim xs)
  then show ?case
    by (simp add: split_singleton)
next
  case (rule_append xs ys)
  then have "join d (split d (xs @ [d] @ ys)) = join d (split d (xs) @ [ys])"
    using split_append by fastforce
  then have "join d (split d (xs @ [d] @ ys)) = join d (split d (xs)) @ [d] @ ys"
    using join.simps(1) join_append list.distinct(1) rule_append.hyps(2) split_empty
    by metis
  then show ?case
    by (simp add: rule_append.hyps(2))
qed


subsection "Bijection range of join and split"

lemma join_bij_range: "join d ` join_bij_domain d = split_bij_domain d"
proof
  show "join d ` join_bij_domain d \<subseteq> split_bij_domain d"
  proof
    fix x
    assume "x \<in> join d ` join_bij_domain d"
    then show "x \<in> split_bij_domain d"
    proof
      fix xa
      assume x_is_xa: "x = join d xa"
      assume "xa \<in> join_bij_domain d"
      then have "join d xa \<in> split_bij_domain d"
      proof (induct)
        case (rule_first_elem xs)
        then show ?case
          by (simp add: split_bij_domain.rule_no_delim)
      next
        case (rule_append xs ys)
        then show ?case
          using join.simps(2) join_append self_append_conv2 split_bij_domain.simps
          by metis
      qed
      then show "x \<in> split_bij_domain d"
        by (simp add: x_is_xa)
    qed
  qed
next
  show "split_bij_domain d \<subseteq> join d ` join_bij_domain d"
  proof
    fix x
    assume "x \<in> split_bij_domain d"
    then show "x \<in> join d ` join_bij_domain d"
    proof (induct)
      case (rule_no_delim ys)
      then show ?case
        using image_iff join_bij_domain.rule_first_elem by fastforce
    next
      case (rule_append xs ys)
      then have xss_domain_existance: "\<exists>xss. xss \<in> join_bij_domain d \<and> xs = join d xss"
        by auto
      assume "d \<notin> set ys"
      then have "\<And>xss. xss \<in> join_bij_domain d \<Longrightarrow> xss @ [ys] \<in> join_bij_domain d"
        by (fact join_bij_domain.rule_append)
      then have "\<And>xss. xss \<in> join_bij_domain d \<Longrightarrow> join d (xss @ [ys]) \<in> join d ` join_bij_domain d"
        by simp
      then have "\<And>xss. xss \<in> join_bij_domain d \<Longrightarrow> join d xss @ [d] @ ys \<in> join d ` join_bij_domain d"
        using Nil_is_append_conv append_Nil in_set_conv_decomp_last join.simps(1) join.simps(2) join_append join_bij_domain.rule_append list.distinct(1)
        by metis
      then show ?case
        using xss_domain_existance by blast
    qed
  qed
qed

lemma split_bij_range: "split d ` split_bij_domain d = join_bij_domain d"
proof
  show "split d ` split_bij_domain d \<subseteq> join_bij_domain d"
  proof
    fix x
    assume "x \<in> split d ` split_bij_domain d"
    then show "x \<in> join_bij_domain d"
    proof
      fix xa
      assume x_is_xa: "x = split d xa"
      assume "xa \<in> split_bij_domain d"
      then have "split d xa \<in> join_bij_domain d"
      proof (induct)
        case (rule_no_delim ys)
        then show ?case
          by (simp add: join_bij_domain.rule_first_elem split_singleton)
      next
        case (rule_append xs ys)
        then show ?case
          using join_bij_domain.rule_append split_append by fastforce
      qed
      then show "x \<in> join_bij_domain d"
        by (simp add: x_is_xa)
    qed
  qed
next
  show "join_bij_domain d \<subseteq> split d ` split_bij_domain d"
  proof
    fix x
    assume "x \<in> join_bij_domain d"
    then show "x \<in> split d ` split_bij_domain d"
    proof (induct)
      case (rule_first_elem xs)
      then show ?case
        using image_iff split_bij_domain.rule_no_delim split_singleton by fastforce
    next
      case (rule_append xs ys)
      then have xss_domain_existance: "\<exists>xss. xss \<in> split_bij_domain d \<and> xs = split d xss"
        by auto
      assume "d \<notin> set ys"
      then have "\<And>xss. xss \<in> split_bij_domain d \<Longrightarrow> xss @ [d] @ ys \<in> split_bij_domain d"
        by (fact split_bij_domain.rule_append)
      then have "\<And>xss. xss \<in> split_bij_domain d \<Longrightarrow> split d (xss @ [d] @ ys) \<in> split d ` split_bij_domain d"
        by simp
      then have "\<And>xss. xss \<in> split_bij_domain d \<Longrightarrow> split d xss @ [ys] \<in> split d ` split_bij_domain d"
        using rule_append.hyps(3) split_append by fastforce
      then show ?case
        using xss_domain_existance by blast
    qed
  qed
qed


subsection "Surjectivity"

lemma join_surj[simp]: "surj (join d)"
proof
  show "range (join d) \<subseteq> UNIV"
    by simp
next
  show "UNIV \<subseteq> range (join d)"
    using join.simps(2) surj_def top_greatest
    by metis
qed


subsection "Injectivity"

lemma join_inj[simp]: "inj_on (join d) (join_bij_domain d)"
proof
  fix x y :: "'a list list"
  assume x_in_domain: "x \<in> join_bij_domain d"
  assume y_in_domain: "y \<in> join_bij_domain d"
  assume mapping_eq: "join d x = join d y"
  then show "x = y"
    using join_inverse x_in_domain y_in_domain
    by metis
qed

lemma split_inj[simp]: "inj_on (split d) (split_bij_domain d)"
proof
  fix x y :: "'a list"
  assume x_in_domain: "x \<in> split_bij_domain d"
  assume y_in_domain: "y \<in> split_bij_domain d"
  assume mapping_eq: "split d x = split d y"
  then show "x = y"
    using split_inverse x_in_domain y_in_domain
    by metis
qed


subsection "Bijectivity"

lemma join_bij[simp]: "bij_betw (join d) (join_bij_domain d) (split_bij_domain d)"
  unfolding bij_betw_def
  using join_inj join_bij_range
  by simp

lemma split_bij[simp]: "bij_betw (split d) (split_bij_domain d) (join_bij_domain d)"
  unfolding bij_betw_def
  using split_inj split_bij_range
  by simp

end