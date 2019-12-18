theory AbstractClassType
  imports
    Main
    "Ecore-GROOVE-Mapping.Type_Model_Graph_Mapping"
    "Ecore-GROOVE-Mapping.Identifier_List"
begin

section "Definition of a type model which introduces an abstract class"

definition tmod_abstract_class :: "'t Id \<Rightarrow> 't type_model" where
  "tmod_abstract_class name = \<lparr>
    Class = {name},
    Enum = {},
    UserDataType = {},
    Field = {},
    FieldSig = (\<lambda>x. undefined),
    EnumValue = {},
    Inh = {},
    Prop = {abstract name},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tmod_abstract_class_correct: "type_model (tmod_abstract_class name)"
proof (intro type_model.intro)
  fix p
  assume "p \<in> Prop (tmod_abstract_class name)"
  then have p_def: "p = abstract name"
    unfolding tmod_abstract_class_def
    by simp
  have "abstract name \<in> Property (tmod_abstract_class name)"
  proof (intro Property.abstract_property)
    show "name \<in> Class (tmod_abstract_class name)"
      unfolding tmod_abstract_class_def
      by simp
  qed
  then show "p \<in> Property (tmod_abstract_class name)"
    by (simp add: p_def)
next
  have "asym {} \<and> irrefl {}"
    by (simp add: asym.intros irrefl_def)
  then show "asym (Inh (tmod_abstract_class name)) \<and> irrefl ((Inh (tmod_abstract_class name))\<^sup>+)"
    unfolding tmod_abstract_class_def
    by simp
qed (simp_all add: tmod_abstract_class_def)

lemma tmod_abstract_class_combine_correct:
  assumes "type_model Tmod"
  assumes new_class: "name \<notin> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
  assumes "\<And>x. x \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod \<Longrightarrow> \<not>id_in_ns name (Identifier x) \<and> \<not>id_in_ns x (Identifier name)"
  shows "type_model (tmod_combine Tmod (tmod_abstract_class name))"
proof (intro tmod_combine_full_distinct_correct)
  show "type_model (tmod_abstract_class name)"
    by (fact tmod_abstract_class_correct)
next
  show "(Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod) \<inter> (Class (tmod_abstract_class name) \<union> Enum (tmod_abstract_class name) \<union> UserDataType (tmod_abstract_class name)) = {}"
    unfolding tmod_abstract_class_def
    using new_class
    by simp
qed (simp_all add: assms tmod_abstract_class_def)



section "Encoding of a Class as Node Type in GROOVE"

definition tg_abstract_class_as_node_type :: "'t Id \<Rightarrow> ('t list) type_graph" where
  "tg_abstract_class_as_node_type name = \<lparr>
    NT = {type (id_to_list name)},
    ET = {},
    inh = {(type (id_to_list name), type (id_to_list name))},
    abs = {type (id_to_list name)},
    mult = (\<lambda>x. undefined),
    contains = {}
  \<rparr>"

lemma tg_abstract_class_as_node_type_correct: "type_graph (tg_abstract_class_as_node_type name)"
proof (intro type_graph.intro)
  fix n
  assume "n \<in> NT (tg_abstract_class_as_node_type name)"
  then have "n = type (id_to_list name)"
    unfolding tg_abstract_class_as_node_type_def
    by simp
  then have "n \<in> Lab\<^sub>t"
    by (simp add: Lab\<^sub>t.rule_type_labels)
  then show "n \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
    by blast
next
  show "Partial_order (inh (tg_abstract_class_as_node_type name))"
    unfolding tg_abstract_class_as_node_type_def partial_order_on_def preorder_on_def
    by simp
qed (simp_all add: tg_abstract_class_as_node_type_def)

lemma tg_abstract_class_as_node_type_combine_correct:
  assumes "type_graph TG"
  assumes new_node_type: "type (id_to_list name) \<notin> NT TG"
  shows "type_graph (tg_combine TG (tg_abstract_class_as_node_type name))"
proof (intro tg_combine_distinct_correct)
  show "type_graph (tg_abstract_class_as_node_type name)"
    by (fact tg_abstract_class_as_node_type_correct)
qed (simp_all add: tg_abstract_class_as_node_type_def assms)


subsection "Transformation functions"

definition tmod_abstract_class_to_tg_abstract_class_as_node_type :: "'t type_model \<Rightarrow> ('t list) type_graph" where
  "tmod_abstract_class_to_tg_abstract_class_as_node_type Tmod = \<lparr>
    NT = type ` id_to_list ` Class Tmod,
    ET = {},
    inh = type ` id_to_list ` Class Tmod \<times> type ` id_to_list ` Class Tmod,
    abs = type ` id_to_list ` Class Tmod,
    mult = (\<lambda>x. undefined),
    contains = {}
  \<rparr>"

lemma tmod_abstract_class_to_tg_abstract_class_as_node_type_proj:
  shows "tmod_abstract_class_to_tg_abstract_class_as_node_type (tmod_abstract_class name) = tg_abstract_class_as_node_type name"
  unfolding tmod_abstract_class_to_tg_abstract_class_as_node_type_def tmod_abstract_class_def tg_abstract_class_as_node_type_def
  by simp

lemma tmod_abstract_class_to_tg_abstract_class_as_node_type_func:
  shows "tg_combine_mapping_function (tmod_abstract_class_to_tg_abstract_class_as_node_type) (tmod_abstract_class name) (tg_abstract_class_as_node_type name)"
  by (intro tg_combine_mapping_function.intro)
    (simp_all add: tmod_abstract_class_to_tg_abstract_class_as_node_type_def tmod_abstract_class_def tg_abstract_class_as_node_type_def tmod_combine_def)

definition tg_abstract_class_as_node_type_to_tmod_abstract_class :: "('t list) type_graph \<Rightarrow> 't type_model" where
  "tg_abstract_class_as_node_type_to_tmod_abstract_class TG = \<lparr>
    Class = list_to_id ` unlabel ` NT TG,
    Enum = {},
    UserDataType = {},
    Field = {},
    FieldSig = (\<lambda>x. undefined),
    EnumValue = {},
    Inh = {},
    Prop = abstract ` list_to_id ` unlabel ` NT TG,
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tg_abstract_class_as_node_type_to_tmod_abstract_class_proj:
  shows "tg_abstract_class_as_node_type_to_tmod_abstract_class (tg_abstract_class_as_node_type name) = tmod_abstract_class name"
  unfolding tg_abstract_class_as_node_type_to_tmod_abstract_class_def tmod_abstract_class_def tg_abstract_class_as_node_type_def
  by (simp add: id_to_list_inverse)

lemma tg_abstract_class_as_node_type_to_tmod_abstract_class_func:
  shows "tmod_combine_mapping_function (tg_abstract_class_as_node_type_to_tmod_abstract_class) (tg_abstract_class_as_node_type name) (tmod_abstract_class name)"
  by (intro tmod_combine_mapping_function.intro)
    (simp_all add: tg_abstract_class_as_node_type_to_tmod_abstract_class_def tmod_abstract_class_def tg_abstract_class_as_node_type_def tg_combine_def id_to_list_inverse)

end