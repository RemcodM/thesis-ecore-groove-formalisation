theory Namespace_List
  imports 
    Main
    Ecore.Model_Namespace
begin

section "Namespace to list mapping"

text "Maps a namespace of arbitrary type to a list of the same type. This mapping is lossless."
  
fun ns_to_list :: "'t Namespace \<Rightarrow> 't list" where
  "ns_to_list Root = []" |
  "ns_to_list (Identifier (namespace, name)) = ns_to_list namespace @ [name]"

fun list_to_ns_rec :: "'t list \<Rightarrow> 't Namespace" where
  "list_to_ns_rec [] = \<bottom>" |
  "list_to_ns_rec (x#xs) = Identifier (list_to_ns_rec xs, x)"

definition list_to_ns :: "'t list \<Rightarrow> 't Namespace" where
  "list_to_ns l = list_to_ns_rec (rev l)"


subsection "Domain & Range"

definition list_namespace_domain :: "'t Namespace set" where
  [simp]: "list_namespace_domain \<equiv> namespace_domain"

inductive_set list_namespace_range :: "'t list set"
  where
    rule_root: "[] \<in> list_namespace_range" |
    rule_nested: "l \<in> list_namespace_range \<Longrightarrow> l @ [n] \<in> list_namespace_range"

lemma list_namespace_range_alt: "list_namespace_range = UNIV"
proof
  show "list_namespace_range \<subseteq> UNIV"
    by simp
next
  show "UNIV \<subseteq> list_namespace_range"
  proof
    fix x :: "'t list"
    assume "x \<in> UNIV"
    then show "x \<in> list_namespace_range"
    proof (induct x rule: rev_induct)
      case Nil
      then show ?case
        using list_namespace_range.rule_root
        by simp
    next
      case (snoc x xs)
      then show ?case
        using list_namespace_range.rule_nested
        by simp
    qed
  qed
qed


subsection "Inverse function"

lemma ns_to_list_inverse: "list_to_ns (ns_to_list x) = x"
  unfolding list_to_ns_def
proof (induct x)
  case Root
  then show ?case
    by simp
next
  case (Identifier x)
  then show ?case
  proof-
    have "ns_to_list (Identifier x) = ns_to_list (fst x) @ [snd x]"
      using ns_to_list.simps(2) prod.exhaust_sel
      by metis
    then have "rev (ns_to_list (Identifier x)) = (snd x) # rev (ns_to_list (fst x))"
      by simp
    then have "list_to_ns_rec (rev (ns_to_list (Identifier x))) = Identifier (list_to_ns_rec (rev (ns_to_list (fst x))), snd x)"
      by simp
    then show "list_to_ns_rec (rev (ns_to_list (Identifier x))) = Identifier x"
      by (simp add: Identifier.hyps fsts.intros)
  qed
qed

lemma list_to_ns_inverse: "ns_to_list (list_to_ns l) = l"
  unfolding list_to_ns_def
proof (induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then show ?case
  proof-
    have "rev (x # xs) = rev xs @ [x]"
      by simp
    then show "ns_to_list (list_to_ns_rec (rev (x # xs))) = x # xs"
    proof (induct xs rule: rev_induct)
      case Nil
      then show ?case
        by simp
    next
      case (snoc y ys)
      then show ?case
      proof-
        have "ns_to_list (list_to_ns_rec (rev (x # ys @ [y]))) = (ns_to_list (list_to_ns_rec (rev ys @ [x])) @ [y])"
          by simp
        then show "ns_to_list (list_to_ns_rec (rev (x # ys @ [y]))) = x # ys @ [y]"
          using snoc.hyps by simp
      qed
    qed
  qed
qed

lemma ns_to_list_inv[simp]: "inv ns_to_list = list_to_ns"
  unfolding inv_def
proof
  fix y :: "'t list"
  show "(SOME x. ns_to_list x = y) = list_to_ns y"
  proof (induction y)
    case Nil
    then show ?case 
    proof
      show "ns_to_list (list_to_ns []) = []"
        by (fact list_to_ns_inverse)
      show "\<And>x. ns_to_list x = [] \<Longrightarrow> x = list_to_ns []"
        using ns_to_list_inverse
        by metis
    qed
  next
    case (Cons a y)
    then show ?case
    proof (intro some_equality)
      show "ns_to_list (list_to_ns (a # y)) = a # y"
        by (fact list_to_ns_inverse)
    next
      fix x
      assume "ns_to_list x = a # y"
      then show "x = list_to_ns (a # y)"
        using ns_to_list_inverse
        by metis
    qed
  qed
qed

lemma list_to_ns_inv[simp]: "inv list_to_ns = ns_to_list"
  unfolding inv_def
proof
  fix y :: "'t Namespace"
  show "(SOME x. list_to_ns x = y) = ns_to_list y"
  proof (induction y)
    case Root
    then show ?case
    proof
      show "list_to_ns (ns_to_list \<bottom>) = \<bottom>"
        by (fact ns_to_list_inverse)
      show "\<And>x. list_to_ns x = \<bottom> \<Longrightarrow> x = ns_to_list \<bottom>"
        using list_to_ns_inverse
        by metis
    qed
  next
    case (Identifier x)
    then show ?case
    proof (intro some_equality)
      show "list_to_ns (ns_to_list (Identifier x)) = Identifier x"
        by (fact ns_to_list_inverse)
    next
      fix xa
      assume "list_to_ns xa = Identifier x"
      then show "xa = ns_to_list (Identifier x)"
        using list_to_ns_inverse
        by metis
    qed
  qed
qed


subsection "Range of mapping functions"

lemma ns_to_list_range: "range ns_to_list = list_namespace_range"
proof
  show "range ns_to_list \<subseteq> list_namespace_range"
    by (simp add: list_namespace_range_alt)
next
  show "list_namespace_range \<subseteq> range ns_to_list"
    by (simp add: equalityD2 list_namespace_range_alt list_to_ns_inverse surj_iff_all)
qed

lemma list_to_ns_range: "range list_to_ns = list_namespace_domain"
proof
  show "range list_to_ns \<subseteq> list_namespace_domain"
    by (simp add: namespace_domain_alt)
next
  show "list_namespace_domain \<subseteq> range list_to_ns"
    by (simp add: equalityD2 namespace_domain_alt ns_to_list_inverse surj_iff_all)
qed


subsection "Surjectivity"

lemma ns_to_list_surj[simp]: "surj ns_to_list"
proof
  show "range ns_to_list \<subseteq> UNIV"
    by simp
next
  show "UNIV \<subseteq> range ns_to_list"
    by (simp add: list_namespace_range_alt ns_to_list_range)
qed

lemma list_to_ns_surj[simp]: "surj list_to_ns"
proof
  show "range list_to_ns \<subseteq> UNIV"
    by simp
next
  show "UNIV \<subseteq> range list_to_ns"
    by (simp add: equalityD2 namespace_domain_alt ns_to_list_inverse surj_iff_all)
qed


subsection "Injectivity"

lemma ns_to_list_inj[simp]: "inj ns_to_list"
proof
  fix x y :: "'t Namespace"
  assume mapping_eq: "ns_to_list x = ns_to_list y"
  then show "x = y"
    using ns_to_list_inverse
    by metis
qed

lemma list_to_ns_inj[simp]: "inj list_to_ns"
proof
  fix x y :: "'t list"
  assume mapping_eq: "list_to_ns x = list_to_ns y"
  then show "x = y"
    using list_to_ns_inverse
    by metis
qed


subsection "Bijectivity"

lemma ns_to_list_bij[simp]: "bij ns_to_list"
  unfolding bij_def
  using ns_to_list_inj ns_to_list_surj
  by simp

lemma list_to_ns_bij[simp]: "bij list_to_ns"
  unfolding bij_def
  using list_to_ns_inj list_to_ns_surj
  by simp


subsection "Subnamespaces"

lemma ns_in_ns_list_def: "ns_in_ns x y \<Longrightarrow> \<exists>z. ns_to_list x = ns_to_list y @ z"
proof-
  fix x y :: "'t Namespace"
  fix z :: "'t list"
  assume "ns_in_ns x y"
  then show "\<exists>z. ns_to_list x = ns_to_list y @ z"
  proof (induct rule: ns_in_ns.induct)
    case (1 uu)
    then show ?case
      by simp
  next
    case (2 x y)
    then show ?case
      using append.assoc eq_fst_iff ns_in_ns.simps(2) ns_to_list.simps(2)
      by metis
  qed
qed

definition ns_list_in_ns_list :: "'t list \<Rightarrow> 't list \<Rightarrow> bool" where
  "ns_list_in_ns_list xs ys \<equiv> length ys < length xs \<and> take (length ys) xs = ys"

lemma ns_to_list_in_ns_to_list: "\<And>x y. ns_in_ns x y \<longleftrightarrow> ns_list_in_ns_list (ns_to_list x) (ns_to_list y)"
proof
  fix x y :: "'t Namespace"
  assume "ns_in_ns x y"
  then show "ns_list_in_ns_list (ns_to_list x) (ns_to_list y)"
    unfolding ns_list_in_ns_list_def
  proof (intro conjI)
    assume x_ns_in_y_ns: "ns_in_ns x y"
    show "length (ns_to_list y) < length (ns_to_list x)"
      using x_ns_in_y_ns
    proof (induct x)
      case Root
      then show ?case
        by simp
    next
      case (Identifier x)
      then show ?case
      proof (induct x)
        case (Pair a b)
        then show ?case
          using fst_conv fsts.intros length_append_singleton lessI less_trans ns_in_ns.elims(2) ns_to_id.simps(1) ns_to_list.simps(2)
          by metis
      qed
    qed
    then show "take (length (ns_to_list y)) (ns_to_list x) = ns_to_list y"
      using x_ns_in_y_ns
    proof (induct y)
      case Root
      then show ?case
        by simp
    next
      case (Identifier y)
      then show ?case
      proof (induct y)
        case (Pair a b)
        then have ns_in_ns_x_a: "ns_in_ns x a"
          using fst_conv ns_def ns_in_parent_ns
          by metis
        have length_a_x: "length (ns_to_list a) < length (ns_to_list x)"
          using Pair.prems(2) by auto
        then have take_a_x: "take (length (ns_to_list a)) (ns_to_list x) = ns_to_list a"
          by (simp add: Pair.prems(1) ns_in_ns_x_a)
        then have "ns_to_list (Identifier (a, b)) = take (length (ns_to_list a)) (ns_to_list x) @ [b]"
          by simp
        then show ?case
          using Pair.prems(3) ns_in_ns_list_def 
          by fastforce
      qed
    qed
  qed
next
  fix x y :: "'t Namespace"
  assume "ns_list_in_ns_list (ns_to_list x) (ns_to_list y)"
  then show "ns_in_ns x y"
    unfolding ns_list_in_ns_list_def
  proof (induct rule: ns_in_ns.induct)
    case (1 uu)
    then show ?case
      by simp
  next
    case (2 x y)
    then show ?case
      using butlast_snoc fst_conv not_le ns_in_ns.simps(2) ns_to_list.simps(2) ns_to_list_inverse surj_pair take_all take_butlast
      by metis
  qed
qed

lemma list_to_ns_in_list_to_ns: "\<And>x y. ns_in_ns (list_to_ns x) (list_to_ns y) \<longleftrightarrow> ns_list_in_ns_list x y"
  by (simp add: list_to_ns_inverse ns_to_list_in_ns_to_list)

end