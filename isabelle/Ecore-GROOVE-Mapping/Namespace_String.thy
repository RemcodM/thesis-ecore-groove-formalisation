theory Namespace_String
  imports 
    Main
    Ecore.Model_Namespace
    List_Join_Split
    Namespace_List
begin

section "Namespace to string mapping for string based namespaces"

text "Maps a namespace consisting of strings to a single string, entirely lossless."

definition ns_to_string :: "'t \<Rightarrow> 't list Namespace \<Rightarrow> 't list" where
  "ns_to_string d n \<equiv> join d ([[]] @ (ns_to_list n))"

definition string_to_ns :: "'t \<Rightarrow> 't list \<Rightarrow> 't list Namespace" where
  "string_to_ns d s \<equiv> list_to_ns (tl (split d s))"


subsection "Lemma's on the definition"

lemma ns_to_string_root: "ns_to_string d \<bottom> = []"
  by (simp add: ns_to_string_def)

lemma ns_to_string_identifier: "ns_to_string d (Identifier \<bottom>\<^enum>x) = [d] @ x"
  by (simp add: ns_to_string_def)

lemma ns_to_string_append: "ns_to_string d (Identifier (x, y)) = ns_to_string d x @ [d] @ y"
  unfolding ns_to_string_def
  using join_append by fastforce

lemma string_to_ns_root: "string_to_ns d [] = \<bottom>"
  by (simp add: split_def list_to_ns_def string_to_ns_def)

lemma string_to_ns_identifier: "d \<notin> set x \<Longrightarrow> string_to_ns d ([d] @ x) = Identifier \<bottom>\<^enum>x"
  unfolding string_to_ns_def
proof-
  fix x
  assume "d \<notin> set x"
  then have "list_to_ns (tl (split d ([d] @ x))) = list_to_ns (tl ([[], x]))"
    by (simp add: split_def split_rec_singleton_left)
  then have "list_to_ns (tl (split d ([d] @ x))) = list_to_ns [x]"
    by simp
  then show "list_to_ns (tl (split d ([d] @ x))) = Identifier \<bottom>\<^enum>x"
    by (simp add: list_to_ns_def)
qed

lemma string_to_ns_append: "d \<notin> set y \<Longrightarrow> string_to_ns d (x @ [d] @ y) = Identifier (string_to_ns d x, y)"
  unfolding string_to_ns_def
proof-
  fix x y
  assume no_delimiter: "d \<notin> set y"
  then have "list_to_ns (tl (split d (x @ [d] @ y))) = list_to_ns (tl (split d x) @ [y])"
    using split_def list.distinct(1) split_append split_empty split_rec_not_empty tl_append2
    by metis
  then show "list_to_ns (tl (split d (x @ [d] @ y))) = Identifier (list_to_ns (tl (split d x)), y)"
    using list_to_ns_inverse ns_to_list.simps(2) ns_to_list_inverse
    by metis
qed

lemma string_to_ns_delim_impl_identifier: "d \<in> set x \<Longrightarrow> \<exists>y. string_to_ns d x = Identifier y"
  using split_list_last string_to_ns_append by fastforce


subsection "Domain & Range"

inductive_set string_namespace_domain :: "'t \<Rightarrow> 't list Namespace set"
  for d :: "'t"
  where
    rule_root: "\<bottom> \<in> string_namespace_domain d" |
    rule_nested: "namespace \<in> string_namespace_domain d \<Longrightarrow> d \<notin> set name \<Longrightarrow> Identifier (namespace, name) \<in> string_namespace_domain d"

lemma string_namespace_domain_subset: "string_namespace_domain d \<subseteq> namespace_domain"
  using namespace_domainI
  by blast

inductive_set string_namespace_range :: "'t \<Rightarrow> 't list set"
  for d :: "'t"
  where
    rule_root: "[] \<in> string_namespace_range d" |
    rule_nested: "str \<in> string_namespace_range d \<Longrightarrow> d \<notin> set name \<Longrightarrow> str @ [d] @ name \<in> string_namespace_range d"

lemma string_namespace_range_subset: "string_namespace_range d \<subseteq> split_bij_domain d"
proof
  fix x
  assume "x \<in> string_namespace_range d"
  then show "x \<in> split_bij_domain d"
  proof (induct)
    case rule_root
    then show ?case
      by (simp add: split_bij_domain.rule_no_delim)
  next
    case (rule_nested str name)
    then show ?case
      using split_bij_domain.rule_append
      by simp
  qed
qed


subsection "Inverse function"

lemma ns_to_string_inverse: "x \<in> string_namespace_domain d \<Longrightarrow> string_to_ns d (ns_to_string d x) = x"
proof (induct x rule: string_namespace_domain.induct)
  case rule_root
  then show ?case
    by (simp add: ns_to_string_root string_to_ns_root)
next
  case (rule_nested namespace name)
  then show ?case
    using ns_to_string_append string_to_ns_append
    by metis
qed

lemma string_to_ns_inverse: "x \<in> string_namespace_range d \<Longrightarrow> ns_to_string d (string_to_ns d x) = x"
proof (induct x rule: string_namespace_range.induct)
  case rule_root
  then show ?case
    by (simp add: ns_to_string_root string_to_ns_root)
next
  case (rule_nested str name)
  then show ?case
    using ns_to_string_append string_to_ns_append
    by metis
qed


subsection "Range of mapping functions"

lemma ns_to_string_range: "ns_to_string d ` string_namespace_domain d = string_namespace_range d"
proof
  show "ns_to_string d ` string_namespace_domain d \<subseteq> string_namespace_range d"
  proof
    fix x
    assume "x \<in> ns_to_string d ` string_namespace_domain d"
    then show "x \<in> string_namespace_range d"
    proof
      fix xa
      assume x_is_xa: "x = ns_to_string d xa"
      assume "xa \<in> string_namespace_domain d"
      then have "ns_to_string d xa \<in> string_namespace_range d"
      proof (induct xa)
        case rule_root
        then show ?case
          by (simp add: ns_to_string_root string_namespace_range.rule_root)
      next
        case (rule_nested namespace name)
        then show ?case
          using ns_to_string_append string_namespace_range.rule_nested
          by metis
      qed
      then show "x \<in> string_namespace_range d"
        using x_is_xa
        by simp
    qed
  qed
next
  show "string_namespace_range d \<subseteq> ns_to_string d ` string_namespace_domain d"
  proof
    fix x
    assume "x \<in> string_namespace_range d"
    then show "x \<in> ns_to_string d ` string_namespace_domain d"
    proof (induct x)
      case rule_root
      then show ?case
        unfolding ns_to_string_def
        using image_iff string_namespace_domain.intros(1) 
        by fastforce
    next
      case (rule_nested str name)
      then have namespace_existance: "\<exists>namespace. namespace \<in> string_namespace_domain d \<and> str = ns_to_string d namespace"
        by blast
      have "\<And>namespace. namespace \<in> string_namespace_domain d \<Longrightarrow> Identifier (namespace, name) \<in> string_namespace_domain d"
        by (simp add: rule_nested.hyps(3) string_namespace_domain.rule_nested)
      then have "\<And>namespace. namespace \<in> string_namespace_domain d \<Longrightarrow> ns_to_string d (Identifier (namespace, name)) \<in> ns_to_string d ` string_namespace_domain d"
        by simp
      then have "\<And>namespace. namespace \<in> string_namespace_domain d \<Longrightarrow> ns_to_string d (namespace) @ [d] @ name \<in> ns_to_string d ` string_namespace_domain d"
        by (simp add: ns_to_string_append)
      then show ?case
        using namespace_existance
        by blast
    qed
  qed
qed

lemma string_to_ns_range: "string_to_ns d ` string_namespace_range d = string_namespace_domain d"
proof
  show "string_to_ns d ` string_namespace_range d \<subseteq> string_namespace_domain d"
  proof
    fix x
    assume "x \<in> string_to_ns d ` string_namespace_range d"
    then show "x \<in> string_namespace_domain d"
    proof
      fix xa
      assume x_is_xa: "x = string_to_ns d xa"
      assume "xa \<in> string_namespace_range d"
      then have "string_to_ns d xa \<in> string_namespace_domain d"
      proof (induct xa)
        case rule_root
        then show ?case
          by (simp add: string_namespace_domain.rule_root string_to_ns_root)
      next
        case (rule_nested str name)
        then show ?case
          using string_namespace_domain.simps string_to_ns_append
          by metis
      qed
      then show "x \<in> string_namespace_domain d"
        using x_is_xa
        by simp
    qed
  qed
next
  show "string_namespace_domain d \<subseteq> string_to_ns d ` string_namespace_range d"
  proof
    fix x
    assume "x \<in> string_namespace_domain d"
    then show "x \<in> string_to_ns d ` string_namespace_range d"
    proof (induct x)
      case rule_root
      then show ?case
        using image_iff string_namespace_range.rule_root string_to_ns_root 
        by metis
    next
      case (rule_nested namespace name)
      then have str_existance: "\<exists>str. str \<in> string_namespace_range d \<and> namespace = string_to_ns d str"
        by blast
      have "\<And>str. str \<in> string_namespace_range d \<Longrightarrow> str @ [d] @ name \<in> string_namespace_range d"
        using rule_nested.hyps(3) string_namespace_range.rule_nested
        by metis
      then have "\<And>str. str \<in> string_namespace_range d \<Longrightarrow> string_to_ns d (str @ [d] @ name) \<in> string_to_ns d ` string_namespace_range d"
        by simp
      then have "\<And>str. str \<in> string_namespace_range d \<Longrightarrow> Identifier ((string_to_ns d str), name) \<in> string_to_ns d ` string_namespace_range d"
        using rule_nested.hyps(3) string_to_ns_append 
        by metis
      then show ?case
        using str_existance
        by blast
    qed
  qed
qed


subsection "Injectivity"

lemma ns_to_string_inj[simp]: "inj_on (ns_to_string d) (string_namespace_domain d)"
proof
  fix x y
  assume x_in_domain: "x \<in> string_namespace_domain d"
  assume y_in_domain: "y \<in> string_namespace_domain d"
  assume mapping_eq: "ns_to_string d x = ns_to_string d y"
  then show "x = y"
    using x_in_domain y_in_domain ns_to_string_inverse
    by metis
qed

lemma string_to_ns_inj[simp]: "inj_on (string_to_ns d) (string_namespace_range d)"
proof
  fix x y
  assume x_in_range: "x \<in> string_namespace_range d"
  assume y_in_range: "y \<in> string_namespace_range d"
  assume mapping_eq: "string_to_ns d x = string_to_ns d y"
  then show "x = y"
    using x_in_range y_in_range string_to_ns_inverse
    by metis
qed


subsection "Bijectivity"

lemma ns_to_string_bij[simp]: "bij_betw (ns_to_string d) (string_namespace_domain d) (string_namespace_range d)"
  unfolding bij_betw_def
  using ns_to_string_inj ns_to_string_range
  by simp

lemma string_to_ns_bij[simp]: "bij_betw (string_to_ns d) (string_namespace_range d) (string_namespace_domain d)"
  unfolding bij_betw_def
  using string_to_ns_inj string_to_ns_range
  by simp


subsection "Subnamespaces"

definition ns_string_in_ns_string :: "char \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool" where
  "ns_string_in_ns_string d xs ys \<equiv> ns_list_in_ns_list (tl (split d xs)) (tl (split d ys))"

lemma ns_to_string_in_ns_to_string: "\<And>x y. x \<in> string_namespace_domain d \<Longrightarrow> y \<in> string_namespace_domain d \<Longrightarrow> ns_in_ns x y \<longleftrightarrow> ns_string_in_ns_string d (ns_to_string d x) (ns_to_string d y)"
proof-
  fix x y
  assume x_in_domain: "x \<in> string_namespace_domain d"
  assume y_in_domain: "y \<in> string_namespace_domain d"
  show "ns_in_ns x y \<longleftrightarrow> ns_string_in_ns_string d (ns_to_string d x) (ns_to_string d y)"
    using list_to_ns_in_list_to_ns ns_string_in_ns_string_def ns_to_string_inverse string_to_ns_def x_in_domain y_in_domain
    by metis
qed

lemma string_to_ns_in_string_to_ns: "\<And>x y. x \<in> string_namespace_range d \<Longrightarrow> y \<in> string_namespace_range d \<Longrightarrow> ns_in_ns (string_to_ns d x) (string_to_ns d y) \<longleftrightarrow> ns_string_in_ns_string d x y"
  by (simp add: list_to_ns_in_list_to_ns ns_string_in_ns_string_def string_to_ns_def)

end