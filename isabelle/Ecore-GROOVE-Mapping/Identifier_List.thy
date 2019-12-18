theory Identifier_List
  imports 
    Main
    Ecore.Model_Namespace
    Namespace_List
begin

section "Identifier to list mapping for arbitrary types"

text "Maps an identifier of arbitrary type to a list of the same type. This mapping is lossless."

definition id_to_list :: "'t Id \<Rightarrow> 't list" where
  "id_to_list ident \<equiv> ns_to_list (Identifier ident)"

definition list_to_id :: "'t list \<Rightarrow> 't Id" where
  "list_to_id l = ns_to_id (list_to_ns l)"


subsection "Domain & Range"

definition list_identifier_domain :: "'t Id set" where
  [simp]: "list_identifier_domain \<equiv> identifier_domain"

inductive_set list_identifier_range :: "'t list set"
  where
    rule_identifier: "[n] \<in> list_identifier_range" |
    rule_nested: "l \<in> list_identifier_range \<Longrightarrow> l @ [n] \<in> list_identifier_range"


subsection "Inverse function"

lemma id_to_list_inverse: "list_to_id (id_to_list x) = x"
  using id_to_list_def list_to_id_def ns_to_id.simps(1) ns_to_list_inverse
  by metis

lemma list_to_id_inverse: "l \<noteq> [] \<Longrightarrow> id_to_list (list_to_id l) = l"
proof (induction l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    unfolding list_to_id_def id_to_list_def
    using ns_to_id.elims list_to_ns_inverse ns_to_list.simps(1)
    by metis
qed


subsection "Range of mapping functions"

lemma id_to_list_range: "range id_to_list = list_identifier_range"
proof
  show "range id_to_list \<subseteq> list_identifier_range"
  proof
    fix x :: "'t list"
    assume "x \<in> range id_to_list"
    then show "x \<in> list_identifier_range"
      unfolding id_to_list_def
    proof (induction x)
      case Nil
      then show ?case
        using Namespace.distinct(1) ns_to_list.simps(1) ns_to_list_inverse rangeE
        by metis
    next
      case (Cons a x)
      then show ?case
        by (simp add: list_identifier_range_def list_identifier_rangep.rule_identifier list_identifier_rangep.rule_nested rev_nonempty_induct)
    qed
  qed
next
  show "list_identifier_range \<subseteq> range id_to_list"
    using Nil_is_append_conv list.distinct(1) list_identifier_range.cases list_to_id_inverse rangeI subset_iff
    by metis
qed

lemma list_to_id_range: "range list_to_id = list_identifier_domain"
proof
  show "range list_to_id \<subseteq> list_identifier_domain"
    by (simp add: identifier_domain_alt)
next
  show "list_identifier_domain \<subseteq> range list_to_id"
    using id_to_list_inverse subset_UNIV surj_def
    by metis
qed


subsection "Surjectivity"

lemma list_to_id_surj[simp]: "surj list_to_id"
proof
  show "range list_to_id \<subseteq> UNIV"
    by simp
next
  show "UNIV \<subseteq> range list_to_id"
  proof
    fix x :: "'t Id"
    have "x \<in> list_identifier_domain"
      using list_to_id_def list_to_id_range ns_to_id.simps(1) ns_to_list_inverse rangeI
      by metis
    then show "x \<in> range list_to_id"
      by (simp add: list_to_id_range)
  qed
qed


subsection "Injectivity"

lemma id_to_list_inj[simp]: "inj id_to_list"
proof
  fix x y :: "'t Id"
  assume mapping_eq: "id_to_list x = id_to_list y"
  then show "x = y"
    using id_to_list_inverse
    by metis
qed

lemma list_to_id_inj[simp]: "inj_on list_to_id list_identifier_range"
proof
  fix x y :: "'t list"
  assume x_def: "x \<in> list_identifier_range"
  assume y_def: "y \<in> list_identifier_range"
  assume mapping_eq: "list_to_id x = list_to_id y"
  then show "x = y"
    using x_def y_def id_to_list_inverse id_to_list_range rangeE
    by metis
qed


subsection "Bijectivity"

lemma id_to_list_bij[simp]: "bij_betw id_to_list UNIV list_identifier_range"
  unfolding bij_betw_def
proof
  show "inj id_to_list"
    by (fact id_to_list_inj)
  show "range id_to_list = list_identifier_range"
    by (fact id_to_list_range)
qed

lemma list_to_id_bij[simp]: "bij_betw list_to_id list_identifier_range UNIV"
  unfolding bij_betw_def
proof
  show "inj_on list_to_id list_identifier_range"
    by (fact list_to_id_inj)
  show "list_to_id ` list_identifier_range = UNIV"
    using UNIV_eq_I id_to_list_inverse id_to_list_range imageI rangeI
    by metis
qed


subsection "Subnamespaces"

definition id_list_in_ns_list :: "'t list \<Rightarrow> 't list \<Rightarrow> bool" where
  "id_list_in_ns_list \<equiv> ns_list_in_ns_list"

lemma id_to_list_in_ns_to_list: "\<And>x y. x \<in> identifier_domain \<Longrightarrow> id_in_ns x y \<longleftrightarrow> id_list_in_ns_list (id_to_list x) (ns_to_list y)"
proof-
  fix x :: "'t Id"
  fix y :: "'t Namespace"
  assume "x \<in> identifier_domain"
  show "id_in_ns x y \<longleftrightarrow> id_list_in_ns_list (id_to_list x) (ns_to_list y)"
    by (simp add: id_in_ns_def id_list_in_ns_list_def id_to_list_def ns_to_list_in_ns_to_list)
qed

lemma list_to_id_in_list_to_ns: "\<And>x y. x \<in> list_identifier_range \<Longrightarrow> id_in_ns (list_to_id x) (list_to_ns y) \<longleftrightarrow> id_list_in_ns_list x y"
  using id_to_list_in_ns_to_list id_to_list_inverse id_to_list_range identifier_domainI inj_on_eq_iff list_to_id_inj list_to_ns_inverse rangeI
  by metis

end