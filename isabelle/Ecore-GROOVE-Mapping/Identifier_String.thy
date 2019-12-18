theory Identifier_String
  imports 
    Main
    Ecore.Model_Namespace
    Namespace_String
begin

section "Identifier to string mapping for string based identifiers"

text "Maps an identifier consisting of strings to a single string, entirely lossless."

definition id_to_string :: "'t \<Rightarrow> 't list Id \<Rightarrow> 't list" where
  "id_to_string d i \<equiv> ns_to_string d (Identifier i)"

definition string_to_id :: "'t \<Rightarrow> 't list \<Rightarrow> 't list Id" where
  "string_to_id d s \<equiv> ns_to_id (string_to_ns d s)"


subsection "Lemma's on definitions"

lemma id_to_string_not_empty: "id_to_string d i \<noteq> []"
  unfolding id_to_string_def ns_to_string_def
  by (induct i) (simp_all add: join_prepend)

lemma id_to_string_identifier: "id_to_string d \<bottom>\<^enum>x = [d] @ x"
  by (simp add: id_to_string_def ns_to_string_def)

lemma id_to_string_append: "id_to_string d (m\<^enum>n) = id_to_string d m @ [d] @ n"
  using id_to_string_def ns_to_string_append
  by metis

lemma string_to_id_identifier: "d \<notin> set x \<Longrightarrow> string_to_id d ([d] @ x) = \<bottom>\<^enum>x"
  using string_to_id_def string_to_ns_identifier ns_to_id.simps(1)
  by metis

lemma string_to_id_append: "d \<notin> set n \<Longrightarrow> string_to_id d (m @ [d] @ n) = ((string_to_ns d m), n)"
  using string_to_id_def string_to_ns_append ns_to_id.simps(1)
  by metis


subsection "Domain & Range"

inductive_set string_identifier_domain :: "'t \<Rightarrow> 't list Id set"
  for d :: "'t"
  where
    rule_identifier: "d \<notin> set name \<Longrightarrow> \<bottom>\<^enum>name \<in> string_identifier_domain d" |
    rule_nested: "identifier \<in> string_identifier_domain d \<Longrightarrow> d \<notin> set name \<Longrightarrow> (identifier\<^enum>name) \<in> string_identifier_domain d"

lemma string_identifier_domain_subset: "Identifier ` string_identifier_domain d \<subseteq> string_namespace_domain d"
proof
  fix x
  assume "x \<in> Identifier ` string_identifier_domain d"
  then show "x \<in> string_namespace_domain d"
  proof
    fix xa
    assume x_is_xa: "x = Identifier xa"
    assume "xa \<in> string_identifier_domain d"
    then have "Identifier xa \<in> string_namespace_domain d"
    proof (induct xa)
      case (rule_identifier name)
      then show ?case
        by (simp add: string_namespace_domain.rule_nested string_namespace_domain.rule_root)
    next
      case (rule_nested identifier name)
      then show ?case
        by (simp add: string_namespace_domain.rule_nested)
    qed
    then show "x \<in> string_namespace_domain d"
      using x_is_xa
      by simp
  qed
qed

lemma string_identifier_domain_subset_alt: "Identifier ` string_identifier_domain d \<subseteq> namespace_domain"
  by (simp add: namespace_domainI subsetI)

inductive_set string_identifier_range :: "'t \<Rightarrow> 't list set"
  for d :: "'t"
  where
    rule_identifier: "d \<notin> set name \<Longrightarrow> [d] @ name \<in> string_identifier_range d" |
    rule_nested: "str \<in> string_identifier_range d \<Longrightarrow> d \<notin> set name \<Longrightarrow> str @ [d] @ name \<in> string_identifier_range d"

lemma string_identifier_range_altdef: "string_identifier_range d = string_namespace_range d - {[]}"
proof
  show "string_identifier_range d \<subseteq> string_namespace_range d - {[]}"
  proof
    fix x
    assume "x \<in> string_identifier_range d"
    then show "x \<in> string_namespace_range d - {[]}"
    proof (induct x)
      case (rule_identifier name)
      then show ?case
        using Diff_iff append_Cons append_self_conv2 empty_iff in_listsD list.set_intros(1) lists_empty string_namespace_range.rule_root string_namespace_range.simps
        by metis
    next
      case (rule_nested str name)
      then show ?case
        using string_namespace_range.rule_nested by auto
    qed
  qed
next
  show "string_namespace_range d - {[]} \<subseteq> string_identifier_range d"
  proof
    fix x
    assume "x \<in> string_namespace_range d - {[]}"
    then have x_not_empty: "x \<noteq> []"
      by blast
    assume "x \<in> string_namespace_range d - {[]}"
    then have "x \<in> string_namespace_range d"
      by blast
    then show "x \<in> string_identifier_range d"
      using x_not_empty
    proof (induct x)
      case rule_root
      then show ?case
        by simp
    next
      case (rule_nested str name)
      then show ?case
        using string_identifier_range.rule_identifier string_identifier_range.rule_nested 
        by force
    qed
  qed
qed

lemma string_identifier_range_subset: "string_identifier_range d \<subseteq> string_namespace_range d"
proof
  fix x
  assume "x \<in> string_identifier_range d"
  then show "x \<in> string_namespace_range d"
  proof (induct x)
    case (rule_identifier name)
    then show ?case
      using string_namespace_range.rule_nested string_namespace_range.rule_root 
      by fastforce
  next
    case (rule_nested str name)
    then show ?case
      using string_namespace_range.rule_nested
      by simp
  qed
qed

lemma string_identifier_range_subset_alt: "string_identifier_range d \<subseteq> split_bij_domain d"
  using string_identifier_range_altdef string_namespace_range_subset 
  by fastforce


subsection "Inverse function"

lemma id_to_string_inverse: "x \<in> string_identifier_domain c \<Longrightarrow> string_to_id c (id_to_string c x) = x"
  unfolding string_to_id_def id_to_string_def
  using ns_to_string_inverse string_identifier_domain_subset by fastforce

lemma string_to_id_inverse: "x \<in> string_identifier_range d \<Longrightarrow> id_to_string d (string_to_id d x) = x"
proof-
  fix x
  assume "x \<in> string_identifier_range d"
  then show "id_to_string d (string_to_id d x) = x"
  proof (induct x)
    case (rule_identifier name)
    then show ?case
      using id_to_string_identifier string_to_id_identifier
      by metis
  next
    case (rule_nested str name)
    then have "id_to_string d (string_to_id d (str @ [d] @ name)) = id_to_string d ((string_to_id d str)\<^enum>name)"
      using string_identifier_range.simps string_to_id_append string_to_id_identifier string_to_ns_append string_to_ns_identifier
      by metis
    then show ?case
      by (simp add: id_to_string_append rule_nested.hyps(2))
  qed
qed


subsection "Range of mapping functions"

lemma id_to_string_range: "id_to_string d ` string_identifier_domain d = string_identifier_range d"
proof
  show "id_to_string d ` string_identifier_domain d \<subseteq> string_identifier_range d"
  proof
    fix x
    assume "x \<in> id_to_string d ` string_identifier_domain d"
    then show "x \<in> string_identifier_range d"
    proof
      fix xa
      assume x_is_string_xa: "x = id_to_string d xa"
      assume "xa \<in> string_identifier_domain d"
      then have "id_to_string d xa \<in> string_identifier_range d"
      proof (induct xa)
        case (rule_identifier name)
        then show ?case
          using id_to_string_identifier string_identifier_range.rule_identifier 
          by metis
      next
        case (rule_nested identifier name)
        then show ?case
          using id_to_string_append string_identifier_range.rule_nested 
          by metis
      qed
      then show "x \<in> string_identifier_range d"
        using x_is_string_xa
        by blast
    qed
  qed
next
  show "string_identifier_range d \<subseteq> id_to_string d ` string_identifier_domain d"
  proof
    fix x
    assume "x \<in> string_identifier_range d"
    then show "x \<in> id_to_string d ` string_identifier_domain d"
    proof (induct x)
      case (rule_identifier name)
      then show ?case
        using image_iff string_identifier_domain.rule_identifier string_identifier_range.rule_identifier string_to_id_identifier string_to_id_inverse 
        by fastforce
    next
      case (rule_nested str name)
      then have id_existance: "\<exists>identifier. identifier \<in> string_identifier_domain d \<and> str = id_to_string d identifier"
        by blast
      have "\<And>identifier. identifier \<in> string_identifier_domain d \<Longrightarrow> (identifier\<^enum>name) \<in> string_identifier_domain d"
        by (simp add: rule_nested.hyps(3) string_identifier_domain.rule_nested)
      then have "\<And>identifier. identifier \<in> string_identifier_domain d \<Longrightarrow> id_to_string d (identifier\<^enum>name) \<in> id_to_string d ` string_identifier_domain d"
        by simp
      then have "\<And>identifier. identifier \<in> string_identifier_domain d \<Longrightarrow> id_to_string d identifier @ [d] @ name \<in> id_to_string d ` string_identifier_domain d"
        by (simp add: id_to_string_append)
      then show ?case
        using id_existance
        by blast
    qed
  qed
qed

lemma string_to_id_range: "string_to_id d ` string_identifier_range d = string_identifier_domain d"
proof
  show "string_to_id d ` string_identifier_range d \<subseteq> string_identifier_domain d"
  proof
    fix x
    assume "x \<in> string_to_id d ` string_identifier_range d"
    then show "x \<in> string_identifier_domain d"
    proof
      fix xa
      assume x_is_xa: "x = string_to_id d xa"
      assume "xa \<in> string_identifier_range d"
      then have "string_to_id d xa \<in> string_identifier_domain d"
      proof (induct xa)
        case (rule_identifier name)
        then show ?case
          using string_identifier_domain.rule_identifier string_to_id_identifier 
          by metis
      next
        case (rule_nested str name)
        then show ?case
          using id_to_string_append id_to_string_inverse string_identifier_domain.rule_nested string_to_id_inverse
          by metis
      qed
      then show "x \<in> string_identifier_domain d"
        using x_is_xa
        by simp
    qed
  qed
next
  show "string_identifier_domain d \<subseteq> string_to_id d ` string_identifier_range d"
  proof
    fix x
    assume "x \<in> string_identifier_domain d"
    then show "x \<in> string_to_id d ` string_identifier_range d"
    proof (induct x)
      case (rule_identifier name)
      then show ?case
        using image_iff string_identifier_range.rule_identifier string_to_id_identifier 
        by fastforce
    next
      case (rule_nested identifier name)
      then have str_existance: "\<exists>str. str \<in> string_identifier_range d \<and> identifier = string_to_id d str"
        using string_identifier_range_altdef 
        by auto
      have "\<And>str. str \<in> string_identifier_range d \<Longrightarrow> str @ [d] @ name \<in> string_identifier_range d"
        using rule_nested.hyps(3) string_identifier_range.rule_nested 
        by metis
      then have "\<And>str. str \<in> string_identifier_range d \<Longrightarrow> string_to_id d (str @ [d] @ name) \<in> string_to_id d ` string_identifier_range d"
        by simp
      then have "\<And>str. str \<in> string_identifier_range d \<Longrightarrow> ((string_to_id d str)\<^enum>name) \<in> string_to_id d ` string_identifier_range d"
        using rule_nested.hyps(3) string_identifier_range.simps string_to_id_append string_to_id_identifier string_to_ns_append string_to_ns_identifier
        by metis
      then show ?case
        using str_existance
        by blast
    qed
  qed
qed


subsection "Injectivity"

lemma id_to_string_inj[simp]: "inj_on (id_to_string d) (string_identifier_domain d)"
proof
  fix x y
  assume x_in_domain: "x \<in> string_identifier_domain d"
  assume y_in_domain: "y \<in> string_identifier_domain d"
  assume mapping_eq: "id_to_string d x = id_to_string d y"
  then show "x = y"
    using x_in_domain y_in_domain id_to_string_inverse
    by metis
qed

lemma string_to_id_inj[simp]: "inj_on (string_to_id d) (string_identifier_range d)"
proof
  fix x y
  assume x_in_range: "x \<in> string_identifier_range d"
  assume y_in_range: "y \<in> string_identifier_range d"
  assume mapping_eq: "string_to_id d x = string_to_id d y"
  then show "x = y"
    using x_in_range y_in_range string_to_id_inverse
    by metis
qed


subsection "Bijectivity"

lemma id_to_string_bij[simp]: "bij_betw (id_to_string d) (string_identifier_domain d) (string_identifier_range d)"
  unfolding bij_betw_def
  using id_to_string_inj id_to_string_range
  by simp

lemma string_to_id_bij[simp]: "bij_betw (string_to_id d) (string_identifier_range d) (string_identifier_domain d)"
  unfolding bij_betw_def
  using string_to_id_inj string_to_id_range
  by simp


subsection "Subnamespaces"

definition id_string_in_ns_string :: "char \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool" where
  "id_string_in_ns_string \<equiv> ns_string_in_ns_string"

lemma id_to_string_in_ns_to_string: "\<And>x y. x \<in> string_identifier_domain d \<Longrightarrow> y \<in> string_namespace_domain d \<Longrightarrow> id_in_ns x y \<longleftrightarrow> id_string_in_ns_string d (id_to_string d x) (ns_to_string d y)"
proof-
  fix x y
  assume x_in_domain: "x \<in> string_identifier_domain d"
  assume y_in_domain: "y \<in> string_namespace_domain d"
  show "id_in_ns x y \<longleftrightarrow> id_string_in_ns_string d (id_to_string d x) (ns_to_string d y)"
    using id_in_ns_def id_string_in_ns_string_def id_to_string_def image_subset_iff ns_to_string_in_ns_to_string string_identifier_domain_subset x_in_domain y_in_domain
    by metis
qed

lemma string_to_id_in_string_to_ns: "\<And>x y. x \<in> string_identifier_range d \<Longrightarrow> y \<in> string_namespace_range d \<Longrightarrow> id_in_ns (string_to_id d x) (string_to_ns d y) \<longleftrightarrow> id_string_in_ns_string d x y"
  using bij_betwE id_to_string_in_ns_to_string string_to_id_bij string_to_id_inverse string_to_ns_bij string_to_ns_inverse
  by metis

end