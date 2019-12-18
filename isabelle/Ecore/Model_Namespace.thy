theory Model_Namespace
  imports 
    Main
begin

section "Definitions"

datatype ('nametype) Namespace = Root | Identifier "('nametype) Namespace \<times> 'nametype"
type_synonym ('nametype) Id = "('nametype) Namespace \<times> 'nametype"


subsection "Notation"

notation Root ("(\<bottom>)" 1000)

abbreviation identifier_notation :: "('nt) Id \<Rightarrow> 'nt \<Rightarrow> ('nt) Id" (infixl "\<^enum>" 50) where
  "ns\<^enum>n \<equiv> (Identifier ns, n)"

abbreviation root_namespace_notation :: "'nt \<Rightarrow> ('nt) Id" ("\<bottom>\<^enum>_" [1000] 1000) where
  "\<bottom>\<^enum>n \<equiv> (\<bottom>, n)"


subsection "Domain"

subsubsection "Namespaces"

inductive_set namespace_domain :: "'nt Namespace set"
  where
    rule_root: "\<bottom> \<in> namespace_domain" |
    rule_nested: "ns \<in> namespace_domain \<Longrightarrow> Identifier (ns, n) \<in> namespace_domain"

lemma namespace_domainI: "ns \<in> namespace_domain"
proof (induct ns)
  case Root
  then show ?case
    by (fact namespace_domain.rule_root)
next
  case (Identifier x)
  then show ?case
    using fsts.intros namespace_domain.rule_nested prod.exhaust_sel
    by metis
qed

lemma namespace_domain_alt: "namespace_domain = UNIV"
proof
  show "namespace_domain \<subseteq> UNIV"
    by simp
next
  show "UNIV \<subseteq> namespace_domain"
  proof
    fix x :: "'nt Namespace"
    show "x \<in> namespace_domain"
      by (fact namespace_domainI)
  qed
qed

subsubsection "Identifiers"

inductive_set identifier_domain :: "'nt Id set"
  where
    rule_identifier: "(\<bottom>, i) \<in> identifier_domain" |
    rule_nested: "ns \<in> identifier_domain \<Longrightarrow> (Identifier ns, i) \<in> identifier_domain"

lemma identifier_domain_subset: "Identifier ` identifier_domain \<subseteq> namespace_domain"
  by (simp add: namespace_domain_alt)

lemma identifier_domainI: "i \<in> identifier_domain"
proof (induct i)
  case (Pair a b)
  then show ?case
  proof (induct a)
    case Root
    then show ?case
      by (fact identifier_domain.rule_identifier)
  next
    case (Identifier x)
    then show ?case
      using eq_fst_iff fsts.intros identifier_domain.simps
      by metis
  qed
qed

lemma identifier_domain_alt: "identifier_domain = UNIV"
proof
  show "identifier_domain \<subseteq> UNIV"
    by simp
next
  show "UNIV \<subseteq> identifier_domain"
  proof
    fix x :: "'nt Id"
    show "x \<in> identifier_domain"
      by (fact identifier_domainI)
  qed
qed


subsection "Helper functions"

fun ns_to_id :: "'t Namespace \<Rightarrow> 't Id" where
  "ns_to_id (Identifier x) = x" |
  "ns_to_id Root = undefined"

definition ns :: "('nt) Id \<Rightarrow> ('nt) Namespace" where
  "ns identifier = fst identifier"


subsection "Subnamespaces"

fun ns_in_ns :: "('nt) Namespace \<Rightarrow> ('nt) Namespace \<Rightarrow> bool" where
  "ns_in_ns (Root) _ = False" |
  "ns_in_ns (Identifier x) y = (if fst x = y then True else ns_in_ns (fst x) y)"

lemma identifier_in_root[simp]: "ns_in_ns (Identifier x) \<bottom>"
proof (induct x)
  case (Pair a b)
  then show ?case
  proof (induct a)
    case Root
    then show ?case
      by auto
  next
    case (Identifier x)
    then show ?case
      using fsts.intros by fastforce
  qed
qed

lemma ns_in_parent_ns[simp]: "ns_in_ns x (Identifier y) \<Longrightarrow> ns_in_ns x (ns y)"
proof (induct x)
  case Root
  then show ?case
    by simp
next
  case (Identifier x)
  then show ?case
    using fsts.intros ns_def ns_in_ns.simps(2)
    by metis
qed

lemma ns_extend_in_ns[simp]: "ns_in_ns (fst x) y \<Longrightarrow> ns_in_ns (Identifier x) y"
proof (induct x)
  case (Pair a b)
  then show ?case
  proof (induct a)
    case Root
    then show ?case
      by auto
  next
    case (Identifier x)
    then show ?case
      by simp
  qed
qed

lemma ns_not_in_itself[simp]: "\<not>ns_in_ns x x"
proof (induct x)
  case Root
  then show ?case
    by simp
next
  case (Identifier x)
  then show ?case
    using fsts.simps ns_def ns_in_ns.simps(2) ns_in_parent_ns
    by metis
qed


definition id_in_ns :: "('nt) Id \<Rightarrow> ('nt) Namespace \<Rightarrow> bool" where
  "id_in_ns identifier \<equiv> ns_in_ns (Identifier identifier)"

lemma id_in_root_alt[simp]: "id_in_ns x \<bottom>"
  unfolding id_in_ns_def
  by (fact identifier_in_root)

lemma id_in_parent_ns[simp]: "id_in_ns x (Identifier y) \<Longrightarrow> id_in_ns x (ns y)"
  unfolding id_in_ns_def
  by (fact ns_in_parent_ns)

lemma id_extend_in_ns[simp]: "id_in_ns x y \<Longrightarrow> id_in_ns (x\<^enum>b) y"
  unfolding id_in_ns_def
  by simp

lemma id_not_in_ns_itself[simp]: "\<not>id_in_ns x (Identifier x)"
  unfolding id_in_ns_def
  by simp

end