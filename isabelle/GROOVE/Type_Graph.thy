theory Type_Graph
  imports 
    Main
    HOL.Order_Relation
    Graph_Theory.Digraph
    Multiplicity_Pair
begin

section "Label definitions"

datatype ('lt) LabDef = type 'lt | edge 'lt | flag 'lt | bool | int | real | string

fun unlabel :: "'lt LabDef \<Rightarrow> 'lt" where
  "unlabel (type t) = t" |
  "unlabel (edge e) = e" |
  "unlabel (flag f) = f" |
  "unlabel _ = undefined"


subsection "Type labels"

inductive_set Lab\<^sub>t :: "'nt LabDef set"
  where
    rule_type_labels: "\<And>n. type n \<in> Lab\<^sub>t"

lemma lab_type_member[simp]: "x \<in> Lab\<^sub>t \<Longrightarrow> \<exists>y. x = type y"
  by (simp add: Lab\<^sub>t.simps)

lemma lab_type_contains_no_edge_labels[simp]: "edge x \<notin> Lab\<^sub>t"
  using lab_type_member by blast

lemma lab_type_contains_no_flag_labels[simp]: "flag x \<notin> Lab\<^sub>t"
  using lab_type_member by blast

lemma lab_type_contains_no_bool[simp]: "bool \<notin> Lab\<^sub>t"
  using lab_type_member by blast

lemma lab_type_contains_no_int[simp]: "int \<notin> Lab\<^sub>t"
  using lab_type_member by blast

lemma lab_type_contains_no_real[simp]: "real \<notin> Lab\<^sub>t"
  using lab_type_member by blast

lemma lab_type_contains_no_string[simp]: "string \<notin> Lab\<^sub>t"
  using lab_type_member by blast


subsection "Edge labels"

inductive_set Lab\<^sub>e :: "'nt LabDef set"
  where
    rule_edge_labels: "\<And>n. edge n \<in> Lab\<^sub>e"

lemma lab_edge_member[simp]: "x \<in> Lab\<^sub>e \<Longrightarrow> \<exists>y. x = edge y"
  by (simp add: Lab\<^sub>e.simps)

lemma lab_edge_contains_no_type_labels[simp]: "type x \<notin> Lab\<^sub>e"
  using lab_edge_member by blast

lemma lab_edge_contains_no_flag_labels[simp]: "flag x \<notin> Lab\<^sub>e"
  using lab_edge_member by blast

lemma lab_edge_contains_no_bool[simp]: "bool \<notin> Lab\<^sub>e"
  using lab_edge_member by blast

lemma lab_edge_contains_no_int[simp]: "int \<notin> Lab\<^sub>e"
  using lab_edge_member by blast

lemma lab_edge_contains_no_real[simp]: "real \<notin> Lab\<^sub>e"
  using lab_edge_member by blast

lemma lab_edge_contains_no_string[simp]: "string \<notin> Lab\<^sub>e"
  using lab_edge_member by blast

lemma lab_edge_lab_type_intersect[simp]: "Lab\<^sub>e \<inter> Lab\<^sub>t = {}"
  using lab_edge_member by fastforce


subsection "Flag labels"

inductive_set Lab\<^sub>f :: "'nt LabDef set"
  where
    rule_type_labels: "\<And>n. flag n \<in> Lab\<^sub>f"

lemma lab_flag_member[simp]: "x \<in> Lab\<^sub>f \<Longrightarrow> \<exists>y. x = flag y"
  by (simp add: Lab\<^sub>f.simps)

lemma lab_flag_contains_no_type_labels[simp]: "type x \<notin> Lab\<^sub>f"
  using lab_flag_member by blast

lemma lab_flag_contains_no_edge_labels[simp]: "edge x \<notin> Lab\<^sub>f"
  using lab_flag_member by blast

lemma lab_flag_contains_no_bool[simp]: "bool \<notin> Lab\<^sub>f"
  using lab_flag_member by blast

lemma lab_flag_contains_no_int[simp]: "int \<notin> Lab\<^sub>f"
  using lab_flag_member by blast

lemma lab_flag_contains_no_real[simp]: "real \<notin> Lab\<^sub>f"
  using lab_flag_member by blast

lemma lab_flag_contains_no_string[simp]: "string \<notin> Lab\<^sub>f"
  using lab_flag_member by blast

lemma lab_flag_lab_type_intersect[simp]: "Lab\<^sub>f \<inter> Lab\<^sub>t = {}"
  using lab_flag_member by fastforce

lemma lab_flag_lab_edge_intersect[simp]: "Lab\<^sub>f \<inter> Lab\<^sub>e = {}"
  using lab_flag_member by fastforce


subsection "Labels"

definition Lab :: "'nt LabDef set" where
  "Lab = Lab\<^sub>t \<union> Lab\<^sub>e \<union> Lab\<^sub>f"

lemma lab_member[simp]: "x \<in> Lab \<Longrightarrow> (\<exists>y. x = type y) \<or> (\<exists>y. x = edge y) \<or> (\<exists>y. x = flag y)"
  by (simp add: Lab\<^sub>e.simps Lab\<^sub>f.simps Lab\<^sub>t.simps Lab_def)

lemma lab_contains_no_bool[simp]: "bool \<notin> Lab"
  using lab_member by blast

lemma lab_contains_no_int[simp]: "int \<notin> Lab"
  using lab_member by blast

lemma lab_contains_no_real[simp]: "real \<notin> Lab"
  using lab_member by blast

lemma lab_contains_no_string[simp]: "string \<notin> Lab"
  using lab_member by blast

lemma lab_lab_type_intersect[simp]: "Lab \<inter> Lab\<^sub>t = Lab\<^sub>t"
  using Lab_def by blast

lemma lab_lab_edge_intersect[simp]: "Lab \<inter> Lab\<^sub>e = Lab\<^sub>e"
  using Lab_def by blast

lemma lab_lab_flag_intersect[simp]: "Lab \<inter> Lab\<^sub>f = Lab\<^sub>f"
  using Lab_def by blast

lemma lab_contains_lab_type[simp]: "Lab\<^sub>t \<subseteq> Lab"
  by (simp add: inf.absorb_iff2)

lemma lab_contains_lab_edge[simp]: "Lab\<^sub>e \<subseteq> Lab"
  by (simp add: inf.absorb_iff2)

lemma lab_contains_lab_flag[simp]: "Lab\<^sub>f \<subseteq> Lab"
  by (simp add: inf.absorb_iff2)


subsection "Primitive type labels"

definition Lab\<^sub>p :: "'nt LabDef set" where
  "Lab\<^sub>p = {bool, int, real, string}"

lemma lab_primitive_member[simp]: "x \<in> Lab\<^sub>p \<Longrightarrow> x = bool \<or> x = int \<or> x = real \<or> x = string"
  by (simp add: Lab\<^sub>p_def)

lemma lab_primitive_contains_no_type_labels[simp]: "type x \<notin> Lab\<^sub>p"
  using lab_primitive_member by blast

lemma lab_primitive_contains_no_edge_labels[simp]: "edge x \<notin> Lab\<^sub>p"
  using lab_primitive_member by blast

lemma lab_primitive_contains_no_flag_labels[simp]: "flag x \<notin> Lab\<^sub>p"
  using lab_primitive_member by blast

lemma lab_primitive_lab_intersect[simp]: "Lab\<^sub>p \<inter> Lab = {}"
  using lab_primitive_member by fastforce

lemma lab_primitive_lab_type_intersect[simp]: "Lab\<^sub>p \<inter> Lab\<^sub>t = {}"
  using lab_primitive_member by fastforce

lemma lab_primitive_lab_edge_intersect[simp]: "Lab\<^sub>p \<inter> Lab\<^sub>e = {}"
  using lab_primitive_member by fastforce

lemma lab_primitive_lab_flag_intersect[simp]: "Lab\<^sub>p \<inter> Lab\<^sub>f = {}"
  using lab_primitive_member by fastforce



section "Type graph tuple definition"

record ('lt) type_graph =
  NT :: "'lt LabDef set"
  ET :: "('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) set"
  inh :: "'lt LabDef rel"
  abs :: "'lt LabDef set"
  mult :: "('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) \<Rightarrow> multiplicity_pair"
  contains :: "('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) set"

inductive type_graph_eq :: "('lt) type_graph \<Rightarrow> ('lt) type_graph \<Rightarrow> bool"
  for TG1 TG2 :: "('lt) type_graph"
  where
    rule_equality: "\<lbrakk> NT TG1 = NT TG2; 
                      ET TG1 = ET TG2; 
                      inh TG1 = inh TG2; 
                      abs TG1 = abs TG2; 
                      mult TG1 = mult TG2; 
                      contains TG1 = contains TG2 \<rbrakk> \<Longrightarrow> type_graph_eq TG1 TG2"

definition src :: "('a \<times> 'b \<times> 'a) \<Rightarrow> 'a" where
  [simp]: "src e = fst e"

definition lab :: "('a \<times> 'b \<times> 'a) \<Rightarrow> 'b" where
  [simp]: "lab e = fst (snd e)"

definition tgt :: "('a \<times> 'b \<times> 'a) \<Rightarrow> 'a" where
  [simp]: "tgt e = snd (snd e)"

definition edge_to_tuple :: "'a \<times> 'b \<times> 'a \<Rightarrow> 'a \<times> 'a" where
  [simp]: "edge_to_tuple a \<equiv> (src a, tgt a)"



section "Graph theory projection"

definition type_graph_proj :: "('lt) type_graph \<Rightarrow> ('lt LabDef, 'lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) pre_digraph" where
  "type_graph_proj TG = \<lparr> verts = NT TG, arcs = ET TG, tail = tgt, head = src \<rparr>"

declare [[coercion type_graph_proj]]



section "Type graph validity"

locale type_graph = fixes TG :: "('lt) type_graph"
  assumes structure_nodes_wellformed: "\<And>n. n \<in> NT TG \<Longrightarrow> n \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
  assumes structure_edges_wellformed: "\<And>s l t. (s, l, t) \<in> ET TG \<Longrightarrow> s \<in> NT TG \<and> l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> NT TG"
  assumes structure_inheritance_wellformed[simp]: "Field (inh TG) = NT TG"
  assumes structure_abstract_wellformed[simp]: "\<And>n. n \<in> abs TG \<Longrightarrow> n \<in> NT TG"
  assumes structure_mult_wellformed[simp]: "\<And>e. e \<in> ET TG \<Longrightarrow> multiplicity_pair (mult TG e)"
  assumes structure_mult_domain[simp]: "\<And>e. e \<notin> ET TG \<Longrightarrow> mult TG e = undefined"
  assumes structure_contains_wellformed[simp]: "\<And>e. e \<in> contains TG \<Longrightarrow> e \<in> ET TG"
  assumes validity_edges_inh[simp]: "\<And>l s1 t1 s2 t2. (s1, l, t1) \<in> ET TG \<Longrightarrow> (s2, l, t2) \<in> ET TG \<Longrightarrow> 
    (s1, s2) \<in> inh TG \<or> (s2, s1) \<in> inh TG \<Longrightarrow> (t1, t2) \<in> inh TG \<or> (t2, t1) \<in> inh TG \<Longrightarrow> s1 = s2 \<and> t1 = t2"
  assumes validity_flags[simp]: "\<And>s l t. (s, l, t) \<in> ET TG \<Longrightarrow> l \<in> Lab\<^sub>f \<Longrightarrow> s = t"
  assumes validity_inh: "Partial_order (inh TG)"
  assumes validity_mult_containment[simp]: "\<And>e. e \<in> contains TG \<Longrightarrow> upper (m_in (mult TG e)) = \<^bold>1"

context type_graph
begin

lemma structure_nodes_wellformed_alt[simp]: "\<And>n. n \<in> NT TG \<Longrightarrow> n \<in> Lab\<^sub>t \<or> n \<in> Lab\<^sub>p"
  using structure_nodes_wellformed by auto

lemma structure_edges_wellformed_src_node[simp]: "\<And>s. (s, l, t) \<in> ET TG \<Longrightarrow> s \<in> NT TG"
  by (simp add: structure_edges_wellformed)

lemma structure_edges_wellformed_edge_lab[simp]: "\<And>l. (s, l, t) \<in> ET TG \<Longrightarrow> l \<in> Lab\<^sub>e \<union> Lab\<^sub>f"
  using structure_edges_wellformed by auto

lemma structure_edges_wellformed_edge_lab_alt1[simp]: "\<And>l. (s, l, t) \<in> ET TG \<Longrightarrow> l \<in> Lab\<^sub>e \<or> l \<in> Lab\<^sub>f"
  using structure_edges_wellformed_edge_lab by auto

lemma structure_edges_wellformed_tgt_node[simp]: "\<And>t. (s, l, t) \<in> ET TG \<Longrightarrow> t \<in> NT TG"
  by (simp add: structure_edges_wellformed)

lemma structure_edges_wellformed_alt: "\<And>e. e \<in> ET TG \<Longrightarrow> src e \<in> NT TG \<and> lab e \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> tgt e \<in> NT TG"
proof (intro conjI)
  fix e
  assume e_in_edges: "e \<in> ET TG"
  show "src e \<in> NT TG"
    using e_in_edges prod.collapse structure_edges_wellformed_src_node src_def
    by metis
  show "lab e \<in> Lab\<^sub>e \<union> Lab\<^sub>f"                        
    using e_in_edges prod.collapse structure_edges_wellformed_edge_lab lab_def
    by metis
  show "tgt e \<in> NT TG"
    using e_in_edges prod.collapse structure_edges_wellformed_tgt_node tgt_def
    by metis
qed

lemma structure_edges_wellformed_src_node_alt[simp]: "\<And>e. e \<in> ET TG \<Longrightarrow> src e \<in> NT TG"
  by auto

lemma structure_edges_wellformed_edge_lab_alt2[simp]: "\<And>e. e \<in> ET TG \<Longrightarrow> lab e \<in> Lab\<^sub>e \<or> lab e \<in> Lab\<^sub>f"
  using structure_edges_wellformed_alt by blast

lemma structure_edges_wellformed_tgt_node_alt[simp]: "\<And>e. e \<in> ET TG \<Longrightarrow> tgt e \<in> NT TG"
  by auto

lemma structure_inheritance_wellformed_first_node[simp]: "\<And>x. (x, y) \<in> inh TG \<Longrightarrow> x \<in> NT TG"
  using FieldI1 structure_inheritance_wellformed by fastforce

lemma structure_inheritance_wellformed_second_node[simp]: "\<And>y. (x, y) \<in> inh TG \<Longrightarrow> y \<in> NT TG"
  using FieldI2 structure_inheritance_wellformed by fastforce

lemma structure_inheritance_wellformed_alt: "\<And>x. x \<in> inh TG \<Longrightarrow> fst x \<in> NT TG \<and> snd x \<in> NT TG"
  by auto

lemma structure_inheritance_wellformed_first_node_alt[simp]: "\<And>x. x \<in> inh TG \<Longrightarrow> fst x \<in> NT TG"
  by auto

lemma structure_inheritance_wellformed_second_node_alt[simp]: "\<And>x. x \<in> inh TG \<Longrightarrow> snd x \<in> NT TG"
  by auto

lemma validity_edges_inh_alt: "\<And>e1 e2. e1 \<in> ET TG \<Longrightarrow> e2 \<in> ET TG \<Longrightarrow> 
    (src e1, src e2) \<in> inh TG \<or> (src e2, src e1) \<in> inh TG \<Longrightarrow> 
    (tgt e1, tgt e2) \<in> inh TG \<or> (tgt e2, tgt e1) \<in> inh TG \<Longrightarrow> 
    lab e1 = lab e2 \<Longrightarrow> src e1 = src e2 \<and> tgt e1 = tgt e2"
  using validity_edges_inh
  by fastforce

lemma validity_flags_alt: "\<And>e. e \<in> ET TG \<Longrightarrow> lab e \<in> Lab\<^sub>f \<Longrightarrow> src e = tgt e"
  by auto

lemma validity_inh_antisym[simp]: "antisym (inh TG)"
  using partial_order_on_def validity_inh by blast

lemma validity_inh_trans[simp]: "trans (inh TG)"
  using partial_order_on_def preorder_on_def validity_inh by blast

lemma validity_inh_refl[simp]: "refl_on (Field (inh TG)) (inh TG)"
  using partial_order_on_def preorder_on_def validity_inh by auto

lemma validity_inh_node[simp]: "\<And>n. n \<in> NT TG \<Longrightarrow> (n, n) \<in> (inh TG)"
  using refl_onD structure_inheritance_wellformed validity_inh_refl by fastforce

lemma validity_inh_domain[simp]: "Domain (inh TG) = NT TG"
proof
  show "Domain (inh TG) \<subseteq> NT TG"
    by auto
next
  show "NT TG \<subseteq> Domain (inh TG)"
  proof
    fix x
    assume "x \<in> NT TG"
    then show "x \<in> Domain (inh TG)"
      by (intro DomainI) (fact validity_inh_node)
  qed
qed

lemma validity_inh_range[simp]: "Range (inh TG) = NT TG"
proof
  show "Range (inh TG) \<subseteq> NT TG"
    by auto
next
  show "NT TG \<subseteq> Range (inh TG)"
  proof
    fix x
    assume "x \<in> NT TG"
    then show "x \<in> Range (inh TG)"
      by (intro RangeI) (fact validity_inh_node)
  qed
qed

end



section "Graph theory compatibility"

sublocale type_graph \<subseteq> pre_digraph "type_graph_proj TG"
  rewrites "verts TG = NT TG" and "arcs TG = ET TG" and "tail TG = tgt" and "head TG = src"
  by unfold_locales (simp_all add: type_graph_proj_def)

sublocale type_graph \<subseteq> wf_digraph TG
proof
  have verts_are_nodes: "verts (type_graph_proj TG) = NT TG"
    by (simp add: type_graph_proj_def)
  have head_is_src: "head (type_graph_proj TG) = src"
    by (simp add: type_graph_proj_def)
  have tail_is_tgt: "tail (type_graph_proj TG) = tgt"
    by (simp add: type_graph_proj_def)
  fix e
  assume "e \<in> arcs (type_graph_proj TG)"
  then have e_in_edges: "e \<in> ET TG"
    by (simp add: type_graph_proj_def)
  show "tail (type_graph_proj TG) e \<in> verts (type_graph_proj TG)"
    using e_in_edges verts_are_nodes tail_is_tgt structure_edges_wellformed_tgt_node_alt 
    by auto
  show "head (type_graph_proj TG) e \<in> verts (type_graph_proj TG)"
    using e_in_edges verts_are_nodes head_is_src structure_edges_wellformed_src_node_alt 
    by auto
qed



section "Validity of trivial type graphs"

definition tg_empty :: "('lt) type_graph" where
  [simp]: "tg_empty = \<lparr>
    NT = {},
    ET = {},
    inh = {},
    abs = {},
    mult = (\<lambda>x. undefined),
    contains = {}
  \<rparr>"

lemma tg_empty_correct[simp]: "type_graph tg_empty"
  by (intro type_graph.intro) (simp_all)

end
