theory UserDataTypeType
  imports
    Main
    "Ecore-GROOVE-Mapping.Type_Model_Graph_Mapping"
    "Ecore-GROOVE-Mapping.Identifier_List"
begin

section "Definition of a type model which introduces a User defined data type"

definition tmod_userdatatype :: "'t Id \<Rightarrow> 't type_model" where
  "tmod_userdatatype name = \<lparr>
    Class = {},
    Enum = {},
    UserDataType = {name},
    Field = {},
    FieldSig = (\<lambda>x. undefined),
    EnumValue = {},
    Inh = {},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tmod_userdatatype_correct: "type_model (tmod_userdatatype name)"
proof (intro type_model.intro)
  have "asym {} \<and> irrefl {}"
    by (simp add: asym.intros irrefl_def)
  then show "asym (Inh (tmod_userdatatype name)) \<and> irrefl ((Inh (tmod_userdatatype name))\<^sup>+)"
    unfolding tmod_userdatatype_def
    by simp
qed (simp_all add: tmod_userdatatype_def)

lemma tmod_userdatatype_combine_correct:
  assumes "type_model Tmod"
  assumes new_userdatatype: "name \<notin> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
  assumes "\<And>x. x \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod \<Longrightarrow> \<not>id_in_ns name (Identifier x) \<and> \<not>id_in_ns x (Identifier name)"
  shows "type_model (tmod_combine Tmod (tmod_userdatatype name))"
proof (intro tmod_combine_full_distinct_correct)
  show "type_model (tmod_userdatatype name)"
    by (fact tmod_userdatatype_correct)
next
  show "(Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod) \<inter> (Class (tmod_userdatatype name) \<union> Enum (tmod_userdatatype name) \<union> UserDataType (tmod_userdatatype name)) = {}"
    unfolding tmod_userdatatype_def
    using new_userdatatype
    by simp
qed (simp_all add: assms tmod_userdatatype_def)



section "Encoding of an User defined data type as Node Type in GROOVE"

definition tg_userdatatype_as_node_type :: "'t Id \<Rightarrow> 't \<Rightarrow> ('t list) type_graph" where
  "tg_userdatatype_as_node_type name data_edge = \<lparr>
    NT = {type (id_to_list name), string},
    ET = {(type (id_to_list name), edge [data_edge], string)},
    inh = {(type (id_to_list name), type (id_to_list name)), (string, string)},
    abs = {},
    mult = (\<lambda>x. (if x = (type (id_to_list name), edge [data_edge], string) then (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1) else undefined)),
    contains = {}
  \<rparr>"

lemma tg_userdatatype_as_node_type_correct: "type_graph (tg_userdatatype_as_node_type name data_edge)"
proof (intro type_graph.intro)
  fix n
  assume "n \<in> NT (tg_userdatatype_as_node_type name data_edge)"
  then have "n = type (id_to_list name) \<or> n = string"
    unfolding tg_userdatatype_as_node_type_def
    by simp
  then show "n \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
    using Lab\<^sub>p_def Lab\<^sub>t.simps
    by blast
next
  fix s l t
  assume "(s, l, t) \<in> ET (tg_userdatatype_as_node_type name data_edge)"
  then show "s \<in> NT (tg_userdatatype_as_node_type name data_edge) \<and> l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> NT (tg_userdatatype_as_node_type name data_edge)"
  proof (intro conjI)
    assume "(s, l, t) \<in> ET (tg_userdatatype_as_node_type name data_edge)"
    then show "s \<in> NT (tg_userdatatype_as_node_type name data_edge)"
      unfolding tg_userdatatype_as_node_type_def
      by simp
  next
    assume "(s, l, t) \<in> ET (tg_userdatatype_as_node_type name data_edge)"
    then have "l = edge [data_edge]"
      unfolding tg_userdatatype_as_node_type_def
      by simp
    then show "l \<in> Lab\<^sub>e \<union> Lab\<^sub>f"
      by (simp add: Lab\<^sub>e.rule_edge_labels)
  next
    assume "(s, l, t) \<in> ET (tg_userdatatype_as_node_type name data_edge)"
    then show "t \<in> NT (tg_userdatatype_as_node_type name data_edge)"
      unfolding tg_userdatatype_as_node_type_def
      by simp
  qed
next
  have "Relation.Field (inh (tg_userdatatype_as_node_type name data_edge)) = {type (id_to_list name), string}"
    unfolding tg_userdatatype_as_node_type_def
    by fastforce
  then show "Relation.Field (inh (tg_userdatatype_as_node_type name data_edge)) = NT (tg_userdatatype_as_node_type name data_edge)"
    unfolding tg_userdatatype_as_node_type_def
    by simp
next
  fix e
  assume e_def: "e \<in> ET (tg_userdatatype_as_node_type name data_edge)"
  have "multiplicity_pair (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1)"
  proof (intro multiplicity_pair.intro)
    show "multiplicity (m_in (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1))"
      by (simp add: multiplicity_def)
  next
    show "multiplicity (m_out (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1))"
      by (simp add: multiplicity_def)
  qed
  then show "multiplicity_pair (mult (tg_userdatatype_as_node_type name data_edge) e)"
    using e_def
    unfolding tg_userdatatype_as_node_type_def
    by simp
next
  show "Partial_order (inh (tg_userdatatype_as_node_type name data_edge))"
    unfolding partial_order_on_def preorder_on_def
  proof (intro conjI)
    show "Refl (inh (tg_userdatatype_as_node_type name data_edge))"
      unfolding refl_on_def tg_userdatatype_as_node_type_def
      by simp
  next
    show "trans (inh (tg_userdatatype_as_node_type name data_edge))"
      unfolding trans_def tg_userdatatype_as_node_type_def
      by simp
  next
    show "antisym (inh (tg_userdatatype_as_node_type name data_edge))"
      unfolding antisym_def tg_userdatatype_as_node_type_def
      by simp
  qed
qed (simp_all add: tg_userdatatype_as_node_type_def)

lemma tg_userdatatype_as_node_type_combine_inh:
  assumes "type_graph TG"
  shows "(inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+ =
    inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge)"
proof
  show "(inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+ \<subseteq>
    inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge)"
  proof
    fix x
    assume "x \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+"
    then have "x \<in> (inh TG)\<^sup>+ \<union> inh (tg_userdatatype_as_node_type name data_edge)"
    proof (induct x)
      case (Pair a b)
      then show ?case
      proof (induct)
        case (base y)
        then show ?case
          by auto
      next
        case (step y z)
        then show ?case
        proof (elim UnE)
          assume yz_def: "(y, z) \<in> inh TG"
          assume ay_def: "(a, y) \<in> (inh TG)\<^sup>+"
          show ?thesis
            using yz_def ay_def
            by auto
        next
          assume yz_def: "(y, z) \<in> inh (tg_userdatatype_as_node_type name data_edge)"
          assume ay_def: "(a, y) \<in> (inh TG)\<^sup>+"
          show ?thesis
            using yz_def ay_def
            unfolding tg_userdatatype_as_node_type_def
            by auto
        next
          assume yz_def: "(y, z) \<in> inh TG"
          assume ay_def: "(a, y) \<in> inh (tg_userdatatype_as_node_type name data_edge)"
          show ?thesis
            using yz_def ay_def
            unfolding tg_userdatatype_as_node_type_def
            by auto
        next
          assume yz_def: "(y, z) \<in> inh (tg_userdatatype_as_node_type name data_edge)"
          assume ay_def: "(a, y) \<in> inh (tg_userdatatype_as_node_type name data_edge)"
          show ?thesis
            using yz_def ay_def
            unfolding tg_userdatatype_as_node_type_def
            by auto
        qed
      qed
    qed
    then show "x \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge)"
      by (simp add: assms type_graph.validity_inh_trans)
  qed
next
  show "inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge) \<subseteq>
    (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+"
    by auto
qed

lemma tg_userdatatype_as_node_type_combine_correct:
  assumes "type_graph TG"
  assumes combined_node_types: "NT TG \<inter> {type (id_to_list name), string} \<subseteq> {string}"
  shows "type_graph (tg_combine TG (tg_userdatatype_as_node_type name data_edge))"
proof (intro tg_combine_merge_correct)
  show "type_graph (tg_userdatatype_as_node_type name data_edge)"
    by (fact tg_userdatatype_as_node_type_correct)
next
  show "ET TG \<inter> ET (tg_userdatatype_as_node_type name data_edge) = {}"
    unfolding tg_userdatatype_as_node_type_def
    using assms type_graph.structure_edges_wellformed_src_node
    by fastforce
next
  fix l s1 t1 s2 t2
  assume edge1: "(s1, l, t1) \<in> ET TG"
  assume edge2: "(s2, l, t2) \<in> ET TG"
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+ - inh TG \<or>
    (s2, s1) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+ - inh TG"
  then have "(s1, s2) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge) - inh TG \<or>
    (s2, s1) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge) - inh TG"
    by (simp add: assms tg_userdatatype_as_node_type_combine_inh)
  then have "(s1, s2) \<in> inh (tg_userdatatype_as_node_type name data_edge) \<or>
    (s2, s1) \<in> inh (tg_userdatatype_as_node_type name data_edge)"
    by blast
  then have src_eq: "s1 = s2"
    unfolding tg_userdatatype_as_node_type_def
    by auto
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+ \<or>
    (t2, t1) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+"
  then have "(t1, t2) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge) \<or>
    (t2, t1) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge)"
    by (simp add: assms tg_userdatatype_as_node_type_combine_inh)
  then have "(t1, t2) \<in> inh TG \<or> (t2, t1) \<in> inh TG \<or> 
    (t1, t2) = (type (id_to_list name), type (id_to_list name)) \<or> (t1, t2) = (string, string)"
    unfolding tg_userdatatype_as_node_type_def
    by auto
  then have tgt_eq: "t1 = t2"
  proof (elim disjE)
    assume "(t1, t2) \<in> inh TG"
    then show ?thesis
      using assms(1) edge1 edge2 src_eq type_graph.structure_edges_wellformed_src_node 
      using type_graph.validity_edges_inh type_graph.validity_inh_node
      by fastforce
  next
    assume "(t2, t1) \<in> inh TG"
    then show ?thesis
      using assms(1) edge1 edge2 src_eq type_graph.structure_edges_wellformed_src_node 
      using type_graph.validity_edges_inh type_graph.validity_inh_node
      by fastforce
  qed (simp_all)
  show "s1 = s2 \<and> t1 = t2"
    using src_eq tgt_eq
    by simp
next
  fix l s1 t1 s2 t2
  assume edge1: "(s1, l, t1) \<in> ET TG"
  assume edge2: "(s2, l, t2) \<in> ET TG"
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+ - inh TG \<or>
    (t2, t1) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+ - inh TG"
  then have "(t1, t2) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge) - inh TG \<or>
    (t2, t1) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge) - inh TG"
    by (simp add: assms tg_userdatatype_as_node_type_combine_inh)
  then have "(t1, t2) \<in> inh (tg_userdatatype_as_node_type name data_edge) \<or>
    (t2, t1) \<in> inh (tg_userdatatype_as_node_type name data_edge)"
    by blast
  then have tgt_eq: "t1 = t2"
    unfolding tg_userdatatype_as_node_type_def
    by auto
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+ \<or>
    (s2, s1) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+"
  then have "(s1, s2) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge) \<or>
    (s2, s1) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge)"
    by (simp add: assms tg_userdatatype_as_node_type_combine_inh)
  then have "(s1, s2) \<in> inh TG \<or> (s2, s1) \<in> inh TG \<or> 
    (s1, s2) = (type (id_to_list name), type (id_to_list name)) \<or> (s1, s2) = (string, string)"
    unfolding tg_userdatatype_as_node_type_def
    by auto
  then have src_eq: "s1 = s2"
  proof (elim disjE)
    assume "(s1, s2) \<in> inh TG"
    then show ?thesis
      using assms(1) edge1 edge2 tgt_eq type_graph.structure_edges_wellformed_tgt_node 
      using type_graph.validity_edges_inh type_graph.validity_inh_node
      by fastforce
  next
    assume "(s2, s1) \<in> inh TG"
    then show ?thesis
      using assms(1) edge1 edge2 tgt_eq type_graph.structure_edges_wellformed_tgt_node 
      using type_graph.validity_edges_inh type_graph.validity_inh_node
      by fastforce
  qed (simp_all)
  show "s1 = s2 \<and> t1 = t2"
    using src_eq tgt_eq
    by simp
next
  fix l s1 t1 s2 t2
  assume edge1: "(s1, l, t1) \<in> ET TG"
  assume "(s2, l, t2) \<in> ET (tg_userdatatype_as_node_type name data_edge)"
  then have edge2: "(s2, l, t2) = (type (id_to_list name), edge [data_edge], string)"
    unfolding tg_userdatatype_as_node_type_def
    by simp
  then have not_inh_tg: "(s1, s2) \<notin> inh TG \<and> (s2, s1) \<notin> inh TG"
    using assms type_graph.structure_inheritance_wellformed_first_node 
    using type_graph.structure_inheritance_wellformed_second_node
    by fastforce
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+ \<or>
    (s2, s1) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+"
  then have "(s1, s2) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge) \<or>
    (s2, s1) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge)"
    by (simp add: assms tg_userdatatype_as_node_type_combine_inh)
  then have src_eq: "s1 = s2"
    unfolding tg_userdatatype_as_node_type_def
    using not_inh_tg
    by auto
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+ \<or>
    (t2, t1) \<in> (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+"
  then have "(t1, t2) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge) \<or>
    (t2, t1) \<in> inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge)"
    by (simp add: assms tg_userdatatype_as_node_type_combine_inh)
  then show "s1 = s2 \<and> t1 = t2"
    using assms(1) edge1 edge2 src_eq not_inh_tg 
    using type_graph.structure_edges_wellformed_src_node type_graph.validity_inh_node
    by blast
next
  have "antisym (inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))"
    using assms type_graph.validity_inh_antisym
    unfolding antisym_def tg_userdatatype_as_node_type_def
    by simp
  then show "antisym ((inh TG \<union> inh (tg_userdatatype_as_node_type name data_edge))\<^sup>+)"
    by (simp add: assms tg_userdatatype_as_node_type_combine_inh)
qed (simp_all add: tg_userdatatype_as_node_type_def assms)


subsection "Transformation functions"

definition tmod_userdatatype_to_tg_userdatatype_as_node_type :: "'t \<Rightarrow> 't type_model \<Rightarrow> ('t list) type_graph" where
  "tmod_userdatatype_to_tg_userdatatype_as_node_type data_edge Tmod = \<lparr>
    NT = type ` id_to_list ` UserDataType Tmod \<union> {string},
    ET = type ` id_to_list ` UserDataType Tmod \<times> {edge [data_edge]} \<times> {string},
    inh = type ` id_to_list ` UserDataType Tmod \<times> type ` id_to_list ` UserDataType Tmod \<union> {(string, string)},
    abs = {},
    mult = (\<lambda>x. (if x \<in> type ` id_to_list ` UserDataType Tmod \<times> {edge [data_edge]} \<times> {string} then (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1) else undefined)),
    contains = {}
  \<rparr>"

lemma tmod_userdatatype_to_tg_userdatatype_as_node_type_proj:
  shows "tmod_userdatatype_to_tg_userdatatype_as_node_type data_edge (tmod_userdatatype name) = tg_userdatatype_as_node_type name data_edge"
  unfolding tmod_userdatatype_to_tg_userdatatype_as_node_type_def tmod_userdatatype_def tg_userdatatype_as_node_type_def
  by auto

lemma tmod_userdatatype_to_tg_userdatatype_as_node_type_func:
  shows "tg_combine_mapping_function (tmod_userdatatype_to_tg_userdatatype_as_node_type data_edge) (tmod_userdatatype name) (tg_userdatatype_as_node_type name data_edge)"
  by (intro tg_combine_mapping_function.intro)
    (auto simp add: tmod_userdatatype_to_tg_userdatatype_as_node_type_def tmod_userdatatype_def tg_userdatatype_as_node_type_def tmod_combine_def)

definition tg_userdatatype_as_node_type_to_tmod_userdatatype :: "('t list) type_graph \<Rightarrow> 't type_model" where
  "tg_userdatatype_as_node_type_to_tmod_userdatatype TG = \<lparr>
    Class = {},
    Enum = {},
    UserDataType = list_to_id ` unlabel ` (NT TG \<inter> Lab\<^sub>t),
    Field = {},
    FieldSig = (\<lambda>x. undefined),
    EnumValue = {},
    Inh = {},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tg_userdatatype_as_node_type_to_tmod_userdatatype_proj:
  shows "tg_userdatatype_as_node_type_to_tmod_userdatatype (tg_userdatatype_as_node_type name data_edge) = tmod_userdatatype name"
proof-
  have "list_to_id ` unlabel ` {type (id_to_list name)} = {name}"
    by (simp add: id_to_list_inverse)
  then have "list_to_id ` unlabel ` ({type (id_to_list name), string} \<inter> Lab\<^sub>t) = {name}"
    by (simp add: Lab\<^sub>t.rule_type_labels)
  then have "list_to_id ` unlabel ` (NT (tg_userdatatype_as_node_type name data_edge) \<inter> Lab\<^sub>t) = {name}"
    unfolding tg_userdatatype_as_node_type_def
    by simp
  then show "tg_userdatatype_as_node_type_to_tmod_userdatatype (tg_userdatatype_as_node_type name data_edge) = tmod_userdatatype name"
    unfolding tg_userdatatype_as_node_type_to_tmod_userdatatype_def tmod_userdatatype_def
    by simp
qed

lemma tg_userdatatype_as_node_type_to_tmod_userdatatype_func:
  shows "tmod_combine_mapping_function (tg_userdatatype_as_node_type_to_tmod_userdatatype) (tg_userdatatype_as_node_type name data_edge) (tmod_userdatatype name)"
proof (intro tmod_combine_mapping_function.intro)
  show "tg_userdatatype_as_node_type_to_tmod_userdatatype (tg_userdatatype_as_node_type name data_edge) = tmod_userdatatype name"
    by (fact tg_userdatatype_as_node_type_to_tmod_userdatatype_proj)
next
  fix TGX
  have "(NT (tg_userdatatype_as_node_type name data_edge) \<inter> Lab\<^sub>t) \<subseteq>
    (NT (tg_combine (tg_userdatatype_as_node_type name data_edge) TGX) \<inter> Lab\<^sub>t)"
    unfolding tg_combine_def
    by fastforce
  then have "list_to_id ` unlabel ` (NT (tg_userdatatype_as_node_type name data_edge) \<inter> Lab\<^sub>t) \<subseteq>
    list_to_id ` unlabel ` (NT (tg_combine (tg_userdatatype_as_node_type name data_edge) TGX) \<inter> Lab\<^sub>t)"
    by fastforce
  then show "UserDataType (tg_userdatatype_as_node_type_to_tmod_userdatatype (tg_userdatatype_as_node_type name data_edge)) \<subseteq>
    UserDataType (tg_userdatatype_as_node_type_to_tmod_userdatatype (tg_combine (tg_userdatatype_as_node_type name data_edge) TGX))"
    unfolding tg_userdatatype_as_node_type_to_tmod_userdatatype_def
    by simp
qed (simp_all add: tg_userdatatype_as_node_type_to_tmod_userdatatype_def)

end