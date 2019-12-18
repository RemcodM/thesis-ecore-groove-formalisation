theory Instance_Graph
  imports 
    Main
    Multiplicity_Pair
    Type_Graph
    Extended_Graph_Theory
begin

section "Node set definitions"

datatype ('nt, 'lt) NodeDef = typed "'lt LabDef" "'nt" | bool bool | int int | real real | string string | invalid

fun nodeType :: "('nt, 'lt) NodeDef \<Rightarrow> ('lt) LabDef" where
  "nodeType (typed t n) = t" |
  "nodeType (bool v) = LabDef.bool" |
  "nodeType (int v) = LabDef.int" |
  "nodeType (real v) = LabDef.real" |
  "nodeType (string v) = LabDef.string" |
  "nodeType invalid = undefined"

fun nodeId :: "('nt, 'lt) NodeDef \<Rightarrow> 'nt" where
  "nodeId (typed t n) = n" | 
  "nodeId _ = undefined"


subsection "Typed nodes"

inductive_set Node\<^sub>t :: "('nt, 'lt) NodeDef set"
  where
    rule_typed_nodes: "\<And>t n. t \<in> Lab\<^sub>t \<Longrightarrow> typed t n \<in> Node\<^sub>t"

lemma typed_nodes_member[simp]: "x \<in> Node\<^sub>t \<Longrightarrow> \<exists>y z. x = typed y z"
  using Node\<^sub>t.cases by blast

lemma typed_nodes_contains_no_bool[simp]: "bool x \<notin> Node\<^sub>t"
  using typed_nodes_member by blast

lemma typed_nodes_contains_no_int[simp]: "int x \<notin> Node\<^sub>t"
  using typed_nodes_member by blast

lemma typed_nodes_contains_no_real[simp]: "real x \<notin> Node\<^sub>t"
  using typed_nodes_member by blast

lemma typed_nodes_contains_no_string[simp]: "string x \<notin> Node\<^sub>t"
  using typed_nodes_member by blast

lemma typed_nodes_node_type: "x \<in> Node\<^sub>t \<Longrightarrow> nodeType x \<in> Lab\<^sub>t"
  using Node\<^sub>t.cases nodeType.simps(1)
  by metis

lemma typed_nodes_not_invalid[simp]: "invalid \<notin> Node\<^sub>t"
  using typed_nodes_member by blast


subsection "Set of value nodes"

subsubsection "Boolean nodes"

definition BooleanNode\<^sub>v :: "('nt, 'lt) NodeDef set" where
  "BooleanNode\<^sub>v \<equiv> {bool True, bool False}"

fun boolValue :: "('nt, 'lt) NodeDef \<Rightarrow> bool" where
  "boolValue (bool v) = v" |
  "boolValue _ = undefined"

lemma boolean_nodes_member[simp]: "x \<in> BooleanNode\<^sub>v \<Longrightarrow> x = bool True \<or> x = bool False"
  by (simp add: BooleanNode\<^sub>v_def)

lemma boolean_nodes_contains_no_typed_node[simp]: "typed x y \<notin> BooleanNode\<^sub>v"
  using boolean_nodes_member by blast

lemma boolean_nodes_contains_no_int[simp]: "int x \<notin> BooleanNode\<^sub>v"
  using boolean_nodes_member by blast

lemma boolean_nodes_contains_no_real[simp]: "real x \<notin> BooleanNode\<^sub>v"
  using boolean_nodes_member by blast

lemma boolean_nodes_contains_no_string[simp]: "string x \<notin> BooleanNode\<^sub>v"
  using boolean_nodes_member by blast

lemma boolean_nodes_typed_nodes_intersect[simp]: "BooleanNode\<^sub>v \<inter> Node\<^sub>t = {}"
  using typed_nodes_member by fastforce

lemma boolean_nodes_node_type[simp]: "x \<in> BooleanNode\<^sub>v \<Longrightarrow> nodeType x = LabDef.bool"
  using boolean_nodes_member nodeType.simps(2) by blast

lemma boolean_nodes_not_invalid[simp]: "invalid \<notin> BooleanNode\<^sub>v"
  using boolean_nodes_member by blast

lemma boolean_nodes_value[simp]: "x \<in> BooleanNode\<^sub>v \<Longrightarrow> x = bool y \<Longrightarrow> boolValue x = y"
  by simp

subsubsection "Integer nodes"

inductive_set IntegerNode\<^sub>v :: "('nt, 'lt) NodeDef set"
  where
    rule_integer_nodes: "\<And>i. int i \<in> IntegerNode\<^sub>v"

fun intValue :: "('nt, 'lt) NodeDef \<Rightarrow> int" where
  "intValue (int v) = v" |
  "intValue _ = undefined"

lemma integer_nodes_member[simp]: "x \<in> IntegerNode\<^sub>v \<Longrightarrow> \<exists>y. x = int y"
  using IntegerNode\<^sub>v.cases by blast

lemma integer_nodes_contains_no_typed_node[simp]: "typed x y \<notin> IntegerNode\<^sub>v"
  using integer_nodes_member by blast

lemma integer_nodes_contains_no_bool[simp]: "bool x \<notin> IntegerNode\<^sub>v"
  using integer_nodes_member by blast

lemma integer_nodes_contains_no_real[simp]: "real x \<notin> IntegerNode\<^sub>v"
  using integer_nodes_member by blast

lemma integer_nodes_contains_no_string[simp]: "string x \<notin> IntegerNode\<^sub>v"
  using integer_nodes_member by blast

lemma integer_nodes_typed_nodes_intersect[simp]: "IntegerNode\<^sub>v \<inter> Node\<^sub>t = {}"
  using typed_nodes_member by fastforce

lemma integer_nodes_boolean_nodes_intersect[simp]: "IntegerNode\<^sub>v \<inter> BooleanNode\<^sub>v = {}"
  using boolean_nodes_member by fastforce

lemma integer_nodes_node_type[simp]: "x \<in> IntegerNode\<^sub>v \<Longrightarrow> nodeType x = LabDef.int"
  using integer_nodes_member nodeType.simps(3) by blast

lemma integer_nodes_not_invalid[simp]: "invalid \<notin> IntegerNode\<^sub>v"
  using integer_nodes_member by blast

lemma integer_nodes_value[simp]: "x \<in> IntegerNode\<^sub>v \<Longrightarrow> x = int y \<Longrightarrow> intValue x = y"
  by simp

subsubsection "Real nodes"

inductive_set RealNode\<^sub>v :: "('nt, 'lt) NodeDef set"
  where
    rule_real_nodes: "\<And>r. real r \<in> RealNode\<^sub>v"

fun realValue :: "('nt, 'lt) NodeDef \<Rightarrow> real" where
  "realValue (real v) = v" |
  "realValue _ = undefined"

lemma real_nodes_member[simp]: "x \<in> RealNode\<^sub>v \<Longrightarrow> \<exists>y. x = real y"
  using RealNode\<^sub>v.cases by blast

lemma real_nodes_contains_no_typed_node[simp]: "typed x y \<notin> RealNode\<^sub>v"
  using real_nodes_member by blast

lemma real_nodes_contains_no_bool[simp]: "bool x \<notin> RealNode\<^sub>v"
  using real_nodes_member by blast

lemma real_nodes_contains_no_int[simp]: "int x \<notin> RealNode\<^sub>v"
  using real_nodes_member by blast

lemma real_nodes_contains_no_string[simp]: "string x \<notin> RealNode\<^sub>v"
  using real_nodes_member by blast

lemma real_nodes_typed_nodes_intersect[simp]: "RealNode\<^sub>v \<inter> Node\<^sub>t = {}"
  using typed_nodes_member by fastforce

lemma real_nodes_boolean_nodes_intersect[simp]: "RealNode\<^sub>v \<inter> BooleanNode\<^sub>v = {}"
  using boolean_nodes_member by fastforce

lemma real_nodes_integer_nodes_intersect[simp]: "RealNode\<^sub>v \<inter> IntegerNode\<^sub>v = {}"
  using integer_nodes_member by fastforce

lemma real_nodes_node_type[simp]: "x \<in> RealNode\<^sub>v \<Longrightarrow> nodeType x = LabDef.real"
  using real_nodes_member nodeType.simps(4) by blast

lemma real_nodes_not_invalid[simp]: "invalid \<notin> RealNode\<^sub>v"
  using real_nodes_member by blast

lemma real_nodes_value[simp]: "x \<in> RealNode\<^sub>v \<Longrightarrow> x = real y \<Longrightarrow> realValue x = y"
  by simp

subsubsection "String nodes"

inductive_set StringNode\<^sub>v :: "('nt, 'lt) NodeDef set"
  where
    rule_string_nodes: "\<And>s. string s \<in> StringNode\<^sub>v"

fun stringValue :: "('nt, 'lt) NodeDef \<Rightarrow> string" where
  "stringValue (string v) = v" |
  "stringValue _ = undefined"

lemma string_nodes_member[simp]: "x \<in> StringNode\<^sub>v \<Longrightarrow> \<exists>y. x = string y"
  using StringNode\<^sub>v.cases by blast

lemma string_nodes_contains_no_typed_node[simp]: "typed x y \<notin> StringNode\<^sub>v"
  using string_nodes_member by blast

lemma string_nodes_contains_no_bool[simp]: "bool x \<notin> StringNode\<^sub>v"
  using string_nodes_member by blast

lemma string_nodes_contains_no_int[simp]: "int x \<notin> StringNode\<^sub>v"
  using string_nodes_member by blast

lemma string_nodes_contains_no_real[simp]: "real x \<notin> StringNode\<^sub>v"
  using string_nodes_member by blast

lemma string_nodes_typed_nodes_intersect[simp]: "StringNode\<^sub>v \<inter> Node\<^sub>t = {}"
  using typed_nodes_member by fastforce

lemma string_nodes_boolean_nodes_intersect[simp]: "StringNode\<^sub>v \<inter> BooleanNode\<^sub>v = {}"
  using boolean_nodes_member by fastforce

lemma string_nodes_integer_nodes_intersect[simp]: "StringNode\<^sub>v \<inter> IntegerNode\<^sub>v = {}"
  using integer_nodes_member by fastforce

lemma string_nodes_real_nodes_intersect[simp]: "StringNode\<^sub>v \<inter> RealNode\<^sub>v = {}"
  using real_nodes_member by fastforce

lemma string_nodes_node_type[simp]: "x \<in> StringNode\<^sub>v \<Longrightarrow> nodeType x = LabDef.string"
  using string_nodes_member nodeType.simps(5) by blast

lemma string_nodes_not_invalid[simp]: "invalid \<notin> StringNode\<^sub>v"
  using string_nodes_member by blast

lemma string_nodes_value[simp]: "x \<in> StringNode\<^sub>v \<Longrightarrow> x = string y \<Longrightarrow> stringValue x = y"
  by simp

subsubsection "Value nodes"

definition Node\<^sub>v :: "('nt, 'lt) NodeDef set" where
  "Node\<^sub>v \<equiv> BooleanNode\<^sub>v \<union> IntegerNode\<^sub>v \<union> RealNode\<^sub>v \<union> StringNode\<^sub>v"

lemma value_nodes_member[simp]: "x \<in> Node\<^sub>v \<Longrightarrow> x = bool True \<or> x = bool False \<or> (\<exists>y. x = int y) \<or> (\<exists>y. x = real y) \<or> (\<exists>y. x = string y)"
  unfolding Node\<^sub>v_def
  using boolean_nodes_member integer_nodes_member real_nodes_member string_nodes_member
  by blast

lemma value_nodes_contains_no_typed_node[simp]: "typed x y \<notin> Node\<^sub>v"
  using value_nodes_member by blast

lemma value_nodes_typed_nodes_intersect[simp]: "Node\<^sub>v \<inter> Node\<^sub>t = {}"
  using typed_nodes_member by fastforce

lemma value_nodes_boolean_nodes_intersect[simp]: "Node\<^sub>v \<inter> BooleanNode\<^sub>v = BooleanNode\<^sub>v"
  using Node\<^sub>v_def by fastforce

lemma value_nodes_integer_nodes_intersect[simp]: "Node\<^sub>v \<inter> IntegerNode\<^sub>v = IntegerNode\<^sub>v"
  using Node\<^sub>v_def by fastforce

lemma value_nodes_real_nodes_intersect[simp]: "Node\<^sub>v \<inter> RealNode\<^sub>v = RealNode\<^sub>v"
  using Node\<^sub>v_def by fastforce

lemma value_nodes_string_nodes_intersect[simp]: "Node\<^sub>v \<inter> StringNode\<^sub>v = StringNode\<^sub>v"
  using Node\<^sub>v_def by fastforce

lemma value_nodes_contain_boolean_nodes[simp]: "BooleanNode\<^sub>v \<subseteq> Node\<^sub>v"
  using value_nodes_boolean_nodes_intersect by fastforce

lemma value_nodes_contain_integer_nodes[simp]: "IntegerNode\<^sub>v \<subseteq> Node\<^sub>v"
  using value_nodes_integer_nodes_intersect by fastforce

lemma value_nodes_contain_real_nodes[simp]: "RealNode\<^sub>v \<subseteq> Node\<^sub>v"
  using value_nodes_real_nodes_intersect by fastforce

lemma value_nodes_contain_string_nodes[simp]: "StringNode\<^sub>v \<subseteq> Node\<^sub>v"
  using value_nodes_string_nodes_intersect by fastforce

lemma value_nodes_node_type: "x \<in> Node\<^sub>v \<Longrightarrow> nodeType x \<in> Lab\<^sub>p"
  using Lab\<^sub>p_def value_nodes_member by fastforce

lemma value_nodes_not_invalid[simp]: "invalid \<notin> Node\<^sub>v"
  using value_nodes_member by blast


subsection "Nodes"

definition Node :: "('nt, 'lt) NodeDef set" where
  "Node \<equiv> Node\<^sub>t \<union> Node\<^sub>v"

lemma nodes_typed_nodes_intersect[simp]: "Node \<inter> Node\<^sub>t = Node\<^sub>t"
  using Node_def by fastforce

lemma nodes_value_nodes_intersect[simp]: "Node \<inter> Node\<^sub>v = Node\<^sub>v"
  using Node_def by fastforce

lemma nodes_boolean_nodes_intersect[simp]: "Node \<inter> BooleanNode\<^sub>v = BooleanNode\<^sub>v"
  using nodes_value_nodes_intersect value_nodes_boolean_nodes_intersect
  by blast

lemma nodes_integer_nodes_intersect[simp]: "Node \<inter> IntegerNode\<^sub>v = IntegerNode\<^sub>v"
  using nodes_value_nodes_intersect value_nodes_integer_nodes_intersect
  by blast

lemma nodes_real_nodes_intersect[simp]: "Node \<inter> RealNode\<^sub>v = RealNode\<^sub>v"
  using nodes_value_nodes_intersect value_nodes_real_nodes_intersect
  by blast

lemma nodes_string_nodes_intersect[simp]: "Node \<inter> StringNode\<^sub>v = StringNode\<^sub>v"
  using nodes_value_nodes_intersect value_nodes_string_nodes_intersect
  by blast

lemma nodes_contain_typed_nodes[simp]: "Node\<^sub>t \<subseteq> Node"
  using nodes_typed_nodes_intersect by fastforce

lemma nodes_contain_value_nodes[simp]: "Node\<^sub>v \<subseteq> Node"
  using nodes_value_nodes_intersect by fastforce

lemma nodes_contain_boolean_nodes[simp]: "BooleanNode\<^sub>v \<subseteq> Node"
  using nodes_boolean_nodes_intersect by fastforce

lemma nodes_contain_integer_nodes[simp]: "IntegerNode\<^sub>v \<subseteq> Node"
  using nodes_integer_nodes_intersect by fastforce

lemma nodes_contain_real_nodes[simp]: "RealNode\<^sub>v \<subseteq> Node"
  using nodes_real_nodes_intersect by fastforce

lemma nodes_contain_string_nodes[simp]: "StringNode\<^sub>v \<subseteq> Node"
  using nodes_string_nodes_intersect by fastforce

lemma nodes_node_type: "x \<in> Node \<Longrightarrow> nodeType x \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
  using Node_def typed_nodes_node_type value_nodes_node_type by auto

lemma nodes_not_invalid[simp]: "invalid \<notin> Node"
  unfolding Node_def
  by simp



section "Instance graph tuple definition"

record ('nt, 'lt, 'id) instance_graph =
  TG :: "('lt) type_graph"
  Id :: "'id set"
  N :: "('nt, 'lt) NodeDef set"
  E :: "(('nt, 'lt) NodeDef \<times> ('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) \<times> ('nt, 'lt) NodeDef) set"
  ident :: "'id \<Rightarrow> ('nt, 'lt) NodeDef"



section "Types"

definition type\<^sub>n :: "('nt, 'lt) NodeDef \<Rightarrow> 'lt LabDef" where
  "type\<^sub>n \<equiv> nodeType"

declare type\<^sub>n_def[simp add]

definition type\<^sub>e :: "('nt, 'lt) NodeDef \<times> ('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) \<times> ('nt, 'lt) NodeDef \<Rightarrow> 'lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef" where
  "type\<^sub>e e \<equiv> fst (snd e)"

declare type\<^sub>e_def[simp add]



section "Graph theory projection"

definition instance_graph_proj :: "('nt, 'lt, 'id) instance_graph \<Rightarrow> (('nt, 'lt) NodeDef, ('nt, 'lt) NodeDef \<times> ('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) \<times> ('nt, 'lt) NodeDef) pre_digraph" where
  "instance_graph_proj IG = \<lparr> verts = N IG, arcs = E IG, tail = tgt, head = src \<rparr>"

declare [[coercion instance_graph_proj]]

definition instance_graph_containment_proj :: "('nt, 'lt, 'id) instance_graph \<Rightarrow> (('nt, 'lt) NodeDef, ('nt, 'lt) NodeDef \<times> ('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) \<times> ('nt, 'lt) NodeDef) pre_digraph" where
  "instance_graph_containment_proj IG = \<lparr> verts = N IG, arcs = { e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) }, tail = tgt, head = src \<rparr>"



section "Instance graph validity"

locale instance_graph = fixes IG :: "('nt, 'lt, 'id) instance_graph"
  assumes structure_nodes_wellformed[simp]: "\<And>n. n \<in> N IG \<Longrightarrow> n \<in> Node"
  assumes structure_edges_wellformed: "\<And>s l t. (s, l, t) \<in> E IG \<Longrightarrow> s \<in> N IG \<and> l \<in> ET (TG IG) \<and> t \<in> N IG"
  assumes structure_ident_wellformed: "\<And>i. i \<in> Id IG \<Longrightarrow> ident IG i \<in> N IG \<and> type\<^sub>n (ident IG i) \<in> Lab\<^sub>t"
  assumes structure_ident_domain[simp]: "\<And>i. i \<notin> Id IG \<Longrightarrow> ident IG i = undefined"
  assumes validity_type_graph[simp]: "type_graph (TG IG)"
  assumes validity_node_typed[simp]: "\<And>n. n \<in> N IG \<Longrightarrow> type\<^sub>n n \<in> NT (TG IG)"
  assumes validity_edge_src_typed[simp]: "\<And>e. e \<in> E IG \<Longrightarrow> (type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG IG)"
  assumes validity_edge_tgt_typed[simp]: "\<And>e. e \<in> E IG \<Longrightarrow> (type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG IG)"
  assumes validity_abs_no_instances[simp]: "\<And>n. n \<in> N IG \<Longrightarrow> type\<^sub>n n \<notin> abs (TG IG)"
  assumes validity_outgoing_mult[simp]: "\<And>et n. et \<in> ET (TG IG) \<Longrightarrow> n \<in> N IG \<Longrightarrow> (type\<^sub>n n, src et) \<in> inh (TG IG) \<Longrightarrow> card { e. e \<in> E IG \<and> src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG) et)"
  assumes validity_ingoing_mult[simp]: "\<And>et n. et \<in> ET (TG IG) \<Longrightarrow> n \<in> N IG \<Longrightarrow> (type\<^sub>n n, tgt et) \<in> inh (TG IG) \<Longrightarrow> card { e. e \<in> E IG \<and> tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG) et)"
  assumes validity_contained_node[simp]: "\<And>n. n \<in> N IG \<Longrightarrow> card { e. e \<in> E IG \<and> tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG) } \<le> 1"
  assumes validity_containment[simp]: "\<And>p. \<not>pre_digraph.cycle (instance_graph_containment_proj IG) p"

context instance_graph 
begin

lemma structure_edges_wellformed_src_node[simp]: "\<And>s. (s, l, t) \<in> E IG \<Longrightarrow> s \<in> N IG"
  by (simp add: structure_edges_wellformed)

lemma structure_edges_wellformed_edge_type[simp]: "\<And>l. (s, l, t) \<in> E IG \<Longrightarrow> l \<in> ET (TG IG)"
  by (simp add: structure_edges_wellformed)

lemma structure_edges_wellformed_tgt_node[simp]: "\<And>t. (s, l, t) \<in> E IG \<Longrightarrow> t \<in> N IG"
  by (simp add: structure_edges_wellformed)

lemma structure_edges_wellformed_alt: "\<And>e. e \<in> E IG \<Longrightarrow> src e \<in> N IG \<and> type\<^sub>e e \<in> ET (TG IG) \<and> tgt e \<in> N IG"
  by auto

lemma structure_edges_wellformed_src_node_alt[simp]: "\<And>e. e \<in> E IG \<Longrightarrow> src e \<in> N IG"
  by auto

lemma structure_edges_wellformed_edge_type_alt[simp]: "\<And>e. e \<in> E IG \<Longrightarrow> type\<^sub>e e \<in> ET (TG IG)"
  by auto

lemma structure_edges_wellformed_tgt_node_alt[simp]: "\<And>e. e \<in> E IG \<Longrightarrow> tgt e \<in> N IG"
  by auto

lemma structure_ident_wellformed_node[simp]: "\<And>i. i \<in> Id IG \<Longrightarrow> ident IG i \<in> N IG"
  using structure_ident_wellformed
  by blast

lemma structure_ident_wellformed_node_type[simp]: "\<And>i. i \<in> Id IG \<Longrightarrow> type\<^sub>n (ident IG i) \<in> Lab\<^sub>t"
  using structure_ident_wellformed
  by blast

lemma validity_edge_src_typed_alt[simp]: "\<And>s l t. (s, l, t) \<in> E IG \<Longrightarrow> (type\<^sub>n s, src l) \<in> inh (TG IG)"
proof-
  fix s l t
  assume "(s, l, t) \<in> E IG"
  then have "(type\<^sub>n (src (s, l, t)), src (type\<^sub>e (s, l, t))) \<in> inh (TG IG)"
    by (fact validity_edge_src_typed)
  then show "(type\<^sub>n s, src l) \<in> inh (TG IG)"
    by simp
qed

lemma validity_edge_tgt_typed_alt[simp]: "\<And>s l t. (s, l, t) \<in> E IG \<Longrightarrow> (type\<^sub>n t, tgt l) \<in> inh (TG IG)"
proof-
  fix s l t
  assume "(s, l, t) \<in> E IG"
  then have "(type\<^sub>n (tgt (s, l, t)), tgt (type\<^sub>e (s, l, t))) \<in> inh (TG IG)"
    by (fact validity_edge_tgt_typed)
  then show "(type\<^sub>n t, tgt l) \<in> inh (TG IG)"
    by simp
qed

lemma validity_contained_node_alt[simp]: "\<And>n. n \<in> N IG \<Longrightarrow> card { (s, l, t). (s, l, t) \<in> E IG \<and> t = n \<and> l \<in> contains (TG IG) } \<le> 1"
proof-
  fix n
  assume n_in_nodes: "n \<in> N IG"
  have "{ e. e \<in> E IG \<and> tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG) } = { (s, l, t). (s, l, t) \<in> E IG \<and> tgt (s, l, t) = n \<and> type\<^sub>e (s, l, t) \<in> contains (TG IG) }"
    by blast
  then have "card { (s, l, t). (s, l, t) \<in> E IG \<and> tgt (s, l, t) = n \<and> type\<^sub>e (s, l, t) \<in> contains (TG IG) } \<le> 1"
    using n_in_nodes validity_contained_node by fastforce
  then show "card { (s, l, t). (s, l, t) \<in> E IG \<and> t = n \<and> l \<in> contains (TG IG) } \<le> 1"
    by simp
qed

end



section "Graph theory compatibility"

sublocale instance_graph \<subseteq> pre_digraph "instance_graph_proj IG"
  rewrites "verts IG = N IG" and "arcs IG = E IG" and "tail IG = tgt" and "head IG = src"
  by unfold_locales (simp_all add: instance_graph_proj_def)

sublocale instance_graph \<subseteq> wf_digraph IG
proof
  have verts_are_nodes: "verts (instance_graph_proj IG) = N IG"
    by (simp add: instance_graph_proj_def)
  have head_is_src: "head (instance_graph_proj IG) = src"
    by (simp add: instance_graph_proj_def)
  have tail_is_tgt: "tail (instance_graph_proj IG) = tgt"
    by (simp add: instance_graph_proj_def)
  fix e
  assume "e \<in> arcs (instance_graph_proj IG)"
  then have e_in_edges: "e \<in> E IG"
    by (simp add: instance_graph_proj_def)
  show "tail (instance_graph_proj IG) e \<in> verts (instance_graph_proj IG)"
    using e_in_edges verts_are_nodes tail_is_tgt structure_edges_wellformed_tgt_node_alt 
    by auto
  show "head (instance_graph_proj IG) e \<in> verts (instance_graph_proj IG)"
    using e_in_edges verts_are_nodes head_is_src structure_edges_wellformed_src_node_alt 
    by auto
qed

lemma validity_containment_alt:
  assumes structure_edges_wellformed: "\<And>e. e \<in> E IG \<Longrightarrow> type\<^sub>e e \<in> contains (TG IG) \<Longrightarrow> src e \<in> N IG \<and> tgt e \<in> N IG"
  assumes validity_containment: "\<And>p. \<not>pre_digraph.cycle (instance_graph_containment_proj IG) p"
  shows "irrefl ((edge_to_tuple ` { e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) })\<^sup>+)"
proof-
  have "irrefl ((pre_digraph.arc_to_tuple (instance_graph_containment_proj IG) ` arcs (instance_graph_containment_proj IG))\<^sup>+)"
  proof (intro wf_digraph.acyclic_impl_irrefl_trancl)
    show "wf_digraph (instance_graph_containment_proj IG)"
    proof (intro wf_digraph.intro)
      fix e
      assume "e \<in> arcs (instance_graph_containment_proj IG)"
      then have "e \<in> { e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) }"
        unfolding instance_graph_containment_proj_def
        by simp
      then show "tail (instance_graph_containment_proj IG) e \<in> verts (instance_graph_containment_proj IG)"
        unfolding instance_graph_containment_proj_def
        using structure_edges_wellformed
        by simp
    next
      fix e
      assume "e \<in> arcs (instance_graph_containment_proj IG)"
      then have "e \<in> { e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) }"
        unfolding instance_graph_containment_proj_def
        by simp
      then show "head (instance_graph_containment_proj IG) e \<in> verts (instance_graph_containment_proj IG)"
        unfolding instance_graph_containment_proj_def
        using structure_edges_wellformed
        by simp
    qed
  next
    show "\<And>p. \<not>pre_digraph.cycle (instance_graph_containment_proj IG) p"
      by (fact validity_containment)
  qed
  then show "irrefl ((edge_to_tuple ` { e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) })\<^sup>+)"
    unfolding pre_digraph.arc_to_tuple_def edge_to_tuple_def instance_graph_containment_proj_def
    by simp
qed

lemma (in instance_graph) validity_containment_alt':
  shows "irrefl ((edge_to_tuple ` { e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) })\<^sup>+)"
proof (intro validity_containment_alt)
  show "\<And>e. e \<in> E IG \<Longrightarrow> type\<^sub>e e \<in> contains (TG IG) \<Longrightarrow> src e \<in> N IG \<and> tgt e \<in> N IG"
    by fastforce
next
  show "\<And>p. \<not>pre_digraph.cycle (instance_graph_containment_proj IG) p"
    by simp
qed

lemma validity_containmentI[intro]:
  assumes structure_edges_wellformed: "\<And>e. e \<in> E IG \<Longrightarrow> type\<^sub>e e \<in> contains (TG IG) \<Longrightarrow> src e \<in> N IG \<and> tgt e \<in> N IG"
  assumes irrefl_contains_edges: "irrefl ((edge_to_tuple ` { e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) })\<^sup>+)"
  shows "\<not>pre_digraph.cycle (instance_graph_containment_proj IG) p"
proof (intro wf_digraph.irrefl_trancl_impl_acyclic)
  show "wf_digraph (instance_graph_containment_proj IG)"
  proof (intro wf_digraph.intro)
    fix e
    assume "e \<in> arcs (instance_graph_containment_proj IG)"
    then have "e \<in> { e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) }"
      unfolding instance_graph_containment_proj_def
      by simp
    then show "tail (instance_graph_containment_proj IG) e \<in> verts (instance_graph_containment_proj IG)"
      unfolding instance_graph_containment_proj_def
      using structure_edges_wellformed
      by simp
  next
    fix e
    assume "e \<in> arcs (instance_graph_containment_proj IG)"
    then have "e \<in> { e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) }"
      unfolding instance_graph_containment_proj_def
      by simp
    then show "head (instance_graph_containment_proj IG) e \<in> verts (instance_graph_containment_proj IG)"
      unfolding instance_graph_containment_proj_def
      using structure_edges_wellformed
      by simp
  qed
next
  have "pre_digraph.arc_to_tuple (instance_graph_containment_proj IG) ` arcs (instance_graph_containment_proj IG) =
    edge_to_tuple ` { e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) }"
  proof
    show "pre_digraph.arc_to_tuple (instance_graph_containment_proj IG) ` arcs (instance_graph_containment_proj IG)
      \<subseteq> edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}"
    proof
      fix x
      assume "x \<in> pre_digraph.arc_to_tuple (instance_graph_containment_proj IG) ` arcs (instance_graph_containment_proj IG)"
      then show "x \<in> edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}"
      proof
        fix xa
        assume x_is_xa: "x = pre_digraph.arc_to_tuple (instance_graph_containment_proj IG) xa"
        assume "xa \<in> arcs (instance_graph_containment_proj IG)"
        then have "pre_digraph.arc_to_tuple (instance_graph_containment_proj IG) xa 
          \<in> edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}"
          unfolding instance_graph_containment_proj_def pre_digraph.arc_to_tuple_def
          by simp
        then show "x \<in> edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}"
          by (simp add: x_is_xa)
      qed
    qed
  next
    show "edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}
      \<subseteq> pre_digraph.arc_to_tuple (instance_graph_containment_proj IG) ` arcs (instance_graph_containment_proj IG)"
    proof
      fix x
      assume "x \<in> edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}"
      then show "x \<in> pre_digraph.arc_to_tuple (instance_graph_containment_proj IG) ` arcs (instance_graph_containment_proj IG)"
        unfolding instance_graph_containment_proj_def pre_digraph.arc_to_tuple_def edge_to_tuple_def
        by simp
    qed
  qed
  then show "irrefl ((pre_digraph.arc_to_tuple (instance_graph_containment_proj IG) ` arcs (instance_graph_containment_proj IG))\<^sup>+)"
    using irrefl_contains_edges
    by simp
qed



section "Validity of trivial instance graphs"

definition ig_empty :: "('nt, 'lt, 'id) instance_graph" where
  [simp]: "ig_empty = \<lparr>
    TG = tg_empty,
    Id = {},
    N = {},
    E = {},
    ident = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_empty_correct[simp]: "instance_graph ig_empty"
proof (intro instance_graph.intro)
  show "type_graph (TG ig_empty)"
    unfolding ig_empty_def
    using tg_empty_correct
    by simp
next
  fix p :: "(('nt, 'lt) NodeDef \<times> ('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) \<times> ('nt, 'lt) NodeDef) awalk"
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj ig_empty) p"
    unfolding instance_graph_containment_proj_def pre_digraph.cycle_def pre_digraph.awalk_def
    by simp
qed (simp_all)

lemma ig_empty_any_type_graph_correct[simp]:
  assumes instance_graph_type_graph: "type_graph (TG IG)"
  assumes instance_graph_id: "Id IG = {}"
  assumes instance_graph_nodes: "N IG = {}"
  assumes instance_graph_edges: "E IG = {}"
  assumes instance_graph_ident: "ident IG = (\<lambda>x. undefined)"
  shows "instance_graph IG"
proof (intro instance_graph.intro)
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj IG) p"
    unfolding instance_graph_containment_proj_def pre_digraph.cycle_def pre_digraph.awalk_def
    by (simp add: instance_graph_nodes)
qed (simp_all add: assms)

end
