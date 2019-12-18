theory AbstractClassInstance
  imports
    Main
    "Ecore-GROOVE-Mapping.Instance_Model_Graph_Mapping"
    AbstractClassType
begin

section "Definition of an instance model belonging to the introduction of an abstract class"

definition imod_abstract_class :: "'t Id \<Rightarrow> ('o, 't) instance_model" where
  "imod_abstract_class name = \<lparr>
    Tm = tmod_abstract_class name,
    Object = {},
    ObjectClass = (\<lambda>x. undefined),
    ObjectId = (\<lambda>x. undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_abstract_class_correct: "instance_model (imod_abstract_class name)"
proof (intro imod_empty_any_type_model_correct)
  show "type_model (Tm (imod_abstract_class name))"
    unfolding imod_abstract_class_def
    using tmod_abstract_class_correct
    by simp
qed (simp_all add: imod_abstract_class_def tmod_abstract_class_def)

lemma imod_abstract_class_combine_correct:
  assumes "instance_model Imod"
  assumes new_class: "name \<notin> Class (Tm Imod) \<union> Enum (Tm Imod) \<union> UserDataType (Tm Imod)"
  assumes valid_identifier: "\<And>x. x \<in> Class (Tm Imod) \<union> Enum (Tm Imod) \<union> UserDataType (Tm Imod) \<Longrightarrow> \<not>id_in_ns name (Identifier x) \<and> \<not>id_in_ns x (Identifier name)"
  shows "instance_model (imod_combine Imod (imod_abstract_class name))"
proof (intro imod_combine_distinct_correct)
  show "instance_model (imod_abstract_class name)"
    by (fact imod_abstract_class_correct)
next
  show "type_model (tmod_combine (Tm Imod) (Tm (imod_abstract_class name)))"
    unfolding imod_abstract_class_def
    using assms instance_model.select_convs(1) instance_model.validity_type_model_consistent tmod_abstract_class_combine_correct
    by metis
next
  show "Class (Tm Imod) \<inter> Class (Tm (imod_abstract_class name)) = {}"
    unfolding imod_abstract_class_def tmod_abstract_class_def
    using new_class
    by simp
qed (simp_all add: assms imod_abstract_class_def tmod_abstract_class_def)



section "Encoding of an abstract class as Node Type in GROOVE"

definition ig_abstract_class_as_node_type :: "'t Id \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "ig_abstract_class_as_node_type name = \<lparr>
    TG = tg_abstract_class_as_node_type name,
    Id = {},
    N = {},
    E = {},
    ident = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_abstract_class_as_node_type_correct: "instance_graph (ig_abstract_class_as_node_type name)"
proof (intro ig_empty_any_type_graph_correct)
  show "type_graph (TG (ig_abstract_class_as_node_type name))"
    unfolding ig_abstract_class_as_node_type_def
    using tg_abstract_class_as_node_type_correct
    by simp
qed (simp_all add: ig_abstract_class_as_node_type_def tg_abstract_class_as_node_type_def)

lemma ig_abstract_class_as_node_type_combine_correct:
  assumes "instance_graph IG"
  assumes new_node_type: "type (id_to_list name) \<notin> NT (TG IG)"
  shows "instance_graph (ig_combine IG (ig_abstract_class_as_node_type name))"
proof (intro ig_combine_distinct_correct)
  show "instance_graph (ig_abstract_class_as_node_type name)"
    by (fact ig_abstract_class_as_node_type_correct)
qed (simp_all add: ig_abstract_class_as_node_type_def tg_abstract_class_as_node_type_def assms)


subsection "Transformation functions"

definition imod_abstract_class_to_ig_abstract_class_as_node_type :: "'t Id \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "imod_abstract_class_to_ig_abstract_class_as_node_type name Imod = \<lparr>
    TG = tg_abstract_class_as_node_type name,
    Id = {},
    N = {},
    E = {},
    ident = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_abstract_class_to_ig_abstract_class_as_node_type_proj:
  shows "imod_abstract_class_to_ig_abstract_class_as_node_type name (imod_abstract_class name) = ig_abstract_class_as_node_type name"
  unfolding imod_abstract_class_to_ig_abstract_class_as_node_type_def ig_abstract_class_as_node_type_def imod_abstract_class_def
  by simp

lemma imod_abstract_class_to_ig_abstract_class_as_node_type_func:
  shows "ig_combine_mapping_function (imod_abstract_class_to_ig_abstract_class_as_node_type name) (imod_abstract_class name) (ig_abstract_class_as_node_type name)"
  by (intro ig_combine_mapping_function.intro)
    (simp_all add: imod_abstract_class_to_ig_abstract_class_as_node_type_def imod_abstract_class_def ig_abstract_class_as_node_type_def imod_combine_def)

definition ig_abstract_class_as_node_type_to_imod_abstract_class :: "'t Id \<Rightarrow> ('o, 't list, 't) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "ig_abstract_class_as_node_type_to_imod_abstract_class name IG = \<lparr>
    Tm = tmod_abstract_class name,
    Object = {},
    ObjectClass = (\<lambda>x. undefined),
    ObjectId = (\<lambda>x. undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_abstract_class_as_node_type_to_imod_abstract_class_proj:
  shows "ig_abstract_class_as_node_type_to_imod_abstract_class name (ig_abstract_class_as_node_type name) = imod_abstract_class name"
  unfolding ig_abstract_class_as_node_type_to_imod_abstract_class_def imod_abstract_class_def ig_abstract_class_as_node_type_def
  by simp

lemma ig_abstract_class_as_node_type_to_imod_abstract_class_func:
  shows "imod_combine_mapping_function (ig_abstract_class_as_node_type_to_imod_abstract_class name) (ig_abstract_class_as_node_type name) (imod_abstract_class name)"
  by (intro imod_combine_mapping_function.intro)
      (simp_all add: ig_abstract_class_as_node_type_to_imod_abstract_class_def imod_abstract_class_def ig_abstract_class_as_node_type_def ig_combine_def)

end