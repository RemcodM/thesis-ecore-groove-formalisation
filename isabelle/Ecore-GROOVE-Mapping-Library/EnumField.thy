theory EnumField
  imports
    Main
    "Ecore-GROOVE-Mapping.Type_Model_Graph_Mapping"
    "Ecore-GROOVE-Mapping.Identifier_List"
begin

section "Definition of a type model which introduces a field typed by an enumeration type."

definition tmod_enum_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 't set \<Rightarrow> 't type_model" where
  "tmod_enum_field classtype name enumid enumvalues = \<lparr>
    Class = {classtype},
    Enum = {enumid},
    UserDataType = {},
    Field = {(classtype, name)},
    FieldSig = (\<lambda>x. if x = (classtype, name) then (enumtype enumid, \<^bold>1..\<^bold>1) else undefined),
    EnumValue = Pair enumid ` enumvalues,
    Inh = {},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tmod_enum_field_correct:
  assumes enum_class_neq: "classtype \<noteq> enumid"
  assumes valid_ns: "\<not>id_in_ns enumid (Identifier classtype) \<and> \<not>id_in_ns classtype (Identifier enumid)"
  shows "type_model (tmod_enum_field classtype name enumid enumvalues)"
proof (intro type_model.intro)
  fix f
  assume "f \<in> Field (tmod_enum_field classtype name enumid enumvalues)"
  then have "f = (classtype, name)"
    unfolding tmod_enum_field_def
    by simp
  then have "FieldSig (tmod_enum_field classtype name enumid enumvalues) f = (enumtype enumid, \<^bold>1..\<^bold>1)"
    unfolding tmod_enum_field_def
    by simp
  then show "fst (FieldSig (tmod_enum_field classtype name enumid enumvalues) f) \<in> Type (tmod_enum_field classtype name enumid enumvalues) \<and> 
    multiplicity (snd (FieldSig (tmod_enum_field classtype name enumid enumvalues) f))"
  proof (intro conjI)
    assume "FieldSig (tmod_enum_field classtype name enumid enumvalues) f = (enumtype enumid, \<^bold>1..\<^bold>1)"
    then have "fst (FieldSig (tmod_enum_field classtype name enumid enumvalues) f) = enumtype enumid"
      by simp
    then show "fst (FieldSig (tmod_enum_field classtype name enumid enumvalues) f) \<in> Type (tmod_enum_field classtype name enumid enumvalues)"
      unfolding Type_def NonContainerType_def
      by (simp add: EnumType.rule_enum_types tmod_enum_field_def)
  next
    assume "FieldSig (tmod_enum_field classtype name enumid enumvalues) f = (enumtype enumid, \<^bold>1..\<^bold>1)"
    then have snd_def: "snd (FieldSig (tmod_enum_field classtype name enumid enumvalues) f) = \<^bold>1..\<^bold>1"
      by simp
    then show "multiplicity (snd (FieldSig (tmod_enum_field classtype name enumid enumvalues) f))"
      by (intro multiplicity.intro) (simp_all)
  qed
next
  fix ev
  assume "ev \<in> EnumValue (tmod_enum_field classtype name enumid enumvalues)"
  then have "ev \<in> Pair enumid ` enumvalues"
    unfolding tmod_enum_field_def
    by simp
  then have "fst ev = enumid"
    by fastforce
  then show "fst ev \<in> Enum (tmod_enum_field classtype name enumid enumvalues)"
    unfolding tmod_enum_field_def
    by simp
next
  fix c
  assume "c \<in> Class (tmod_enum_field classtype name enumid enumvalues)"
  then have "c = classtype"
    unfolding tmod_enum_field_def
    by simp
  then have "c \<noteq> enumid"
    using enum_class_neq
    by simp
  then show "c \<notin> Enum (tmod_enum_field classtype name enumid enumvalues) \<and> c \<notin> UserDataType (tmod_enum_field classtype name enumid enumvalues)"
    unfolding tmod_enum_field_def
    by simp
next
  fix e
  assume "e \<in> Enum (tmod_enum_field classtype name enumid enumvalues)"
  then have "e = enumid"
    unfolding tmod_enum_field_def
    by simp
  then have "e \<noteq> classtype"
    using enum_class_neq
    by simp
  then show "e \<notin> Class (tmod_enum_field classtype name enumid enumvalues) \<and> e \<notin> UserDataType (tmod_enum_field classtype name enumid enumvalues)"
    unfolding tmod_enum_field_def
    by simp
next
  fix x y
  assume "x \<in> Class (tmod_enum_field classtype name enumid enumvalues) \<union> Enum (tmod_enum_field classtype name enumid enumvalues) \<union> UserDataType (tmod_enum_field classtype name enumid enumvalues)"
  then have x_def: "x = classtype \<or> x = enumid"
    unfolding tmod_enum_field_def
    by fastforce
  assume "y \<in> Class (tmod_enum_field classtype name enumid enumvalues) \<union> Enum (tmod_enum_field classtype name enumid enumvalues) \<union> UserDataType (tmod_enum_field classtype name enumid enumvalues)"
  then have y_def: "y = classtype \<or> y = enumid"
    unfolding tmod_enum_field_def
    by fastforce
  show "\<not>id_in_ns x (Identifier y)"
    using x_def y_def valid_ns
    by fastforce
next
  have "asym {} \<and> irrefl {}"
    by (simp add: asym.intros irrefl_def)
  then show "asym (Inh (tmod_enum_field classtype name enumid enumvalues)) \<and> irrefl ((Inh (tmod_enum_field classtype name enumid enumvalues))\<^sup>+)"
    unfolding tmod_enum_field_def
    by simp
next
  fix f
  assume "f \<in> Field (tmod_enum_field classtype name enumid enumvalues) \<and> 
    Type_Model.type (tmod_enum_field classtype name enumid enumvalues) f \<in> DataType \<union> 
      EnumType (tmod_enum_field classtype name enumid enumvalues) \<union> 
      UserDataTypeType (tmod_enum_field classtype name enumid enumvalues) \<union> 
      ProperClassType (tmod_enum_field classtype name enumid enumvalues)"
  then have "f = (classtype, name)"
    unfolding tmod_enum_field_def
    by simp
  then show "lower (tmod_enum_field classtype name enumid enumvalues) f = \<^bold>1"
    unfolding lower_def tmod_enum_field_def
    by simp
next
  fix f
  assume assump: "f \<in> Field (tmod_enum_field classtype name enumid enumvalues) \<and> 
    Type_Model.type (tmod_enum_field classtype name enumid enumvalues) f \<in> NullableClassType (tmod_enum_field classtype name enumid enumvalues)"
  then have "f = (classtype, name)"
    unfolding tmod_enum_field_def
    by simp
  then have "Type_Model.type (tmod_enum_field classtype name enumid enumvalues) f = enumtype enumid"
    unfolding Type_Model.type_def tmod_enum_field_def
    by simp
  then show "lower (tmod_enum_field classtype name enumid enumvalues) f = \<^bold>0"
    using assump
    by simp
next
  fix f
  assume "f \<in> Field (tmod_enum_field classtype name enumid enumvalues) \<and> 
    Type_Model.type (tmod_enum_field classtype name enumid enumvalues) f \<in> NonContainerType (tmod_enum_field classtype name enumid enumvalues)"
  then have "f = (classtype, name)"
    unfolding tmod_enum_field_def
    by simp
  then show "upper (tmod_enum_field classtype name enumid enumvalues) f = \<^bold>1"
    unfolding upper_def tmod_enum_field_def
    by simp
qed (simp_all add: tmod_enum_field_def)

lemma tmod_enum_field_combine_correct:
  assumes "type_model Tmod"
  assumes existing_class: "classtype \<in> Class Tmod"
  assumes existing_enum: "enumid \<in> Enum Tmod"
  assumes existing_enum_values: "Pair enumid ` enumvalues \<subseteq> EnumValue Tmod"
  assumes new_field: "(classtype, name) \<notin> Field Tmod"
  shows "type_model (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues))"
proof (intro tmod_combine_merge_correct)
  show "type_model (tmod_enum_field classtype name enumid enumvalues)"
  proof (intro tmod_enum_field_correct)
    show "classtype \<noteq> enumid"
      using assms(1) existing_class existing_enum type_model.property_enum_disjoint
      by blast
  next
    show "\<not>id_in_ns enumid (Identifier classtype) \<and> \<not>id_in_ns classtype (Identifier enumid)"
      using Un_iff assms(1) existing_class existing_enum type_model.property_namespace_restriction
      by metis
  qed
next
  fix c
  assume "c \<in> Class (tmod_enum_field classtype name enumid enumvalues)"
  then have "c \<in> Class Tmod"
    unfolding tmod_enum_field_def
    by (simp add: existing_class)
  then show "c \<notin> Enum Tmod \<and> c \<notin> UserDataType Tmod"
    using assms(1) type_model.property_class_disjoint
    by blast
next
  fix e
  assume "e \<in> Enum (tmod_enum_field classtype name enumid enumvalues)"
  then have "e \<in> Enum Tmod"
    unfolding tmod_enum_field_def
    by (simp add: existing_enum)
  then show "e \<notin> Class Tmod \<and> e \<notin> UserDataType Tmod"
    using assms(1) type_model.property_enum_disjoint
    by blast
next
  fix c
  assume "c \<in> Class Tmod"
  then have "c \<noteq> enumid"
    using assms(1) existing_enum type_model.property_enum_disjoint
    by blast
  then show "c \<notin> Enum (tmod_enum_field classtype name enumid enumvalues) \<and> c \<notin> UserDataType (tmod_enum_field classtype name enumid enumvalues)"
    unfolding tmod_enum_field_def
    by simp
next
  fix e
  assume "e \<in> Enum Tmod"
  then have "e \<noteq> classtype"
    using assms(1) existing_class type_model.property_enum_disjoint
    by blast
  then show "e \<notin> Class (tmod_enum_field classtype name enumid enumvalues) \<and> e \<notin> UserDataType (tmod_enum_field classtype name enumid enumvalues)"
    unfolding tmod_enum_field_def
    by simp
next
  fix x y
  assume x_def: "x \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
  assume "y \<in> Class (tmod_enum_field classtype name enumid enumvalues) \<union> 
    Enum (tmod_enum_field classtype name enumid enumvalues) \<union> 
    UserDataType (tmod_enum_field classtype name enumid enumvalues)"
  then have y_def: "y \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
    unfolding tmod_enum_field_def
    using existing_class existing_enum
    by fastforce
  show "\<not>id_in_ns x (Identifier y)"
    using x_def y_def assms(1) type_model.property_namespace_restriction
    by blast
  show "\<not>id_in_ns y (Identifier x)"
    using x_def y_def assms(1) type_model.property_namespace_restriction
    by blast
next
  have "irrefl ((Inh Tmod)\<^sup>+)"
    using assms(1) type_model.property_inh_wellformed_trancl_irrefl
    by blast
  then show "irrefl ((Inh Tmod \<union> Inh (tmod_enum_field classtype name enumid enumvalues))\<^sup>+)"
    unfolding tmod_enum_field_def
    by simp
next
  have inh_wellformed_classes: "\<And>c. c \<in> Inh (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues)) \<Longrightarrow> 
    fst c \<in> Class (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues)) \<and> 
    snd c \<in> Class (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues))"
  proof
    fix c
    assume "c \<in> Inh (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues))"
    then have c_def: "c \<in> Inh Tmod"
      unfolding tmod_combine_def tmod_enum_field_def
      by simp
    have "fst c \<in> Class Tmod"
      using c_def assms(1) type_model.structure_inh_wellformed_fst_class
      by blast
    then show "fst c \<in> Class (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues))"
      unfolding tmod_combine_def
      by simp
    have "snd c \<in> Class Tmod"
      using c_def assms(1) type_model.structure_inh_wellformed_snd_class
      by blast
    then show "snd c \<in> Class (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues))"
      unfolding tmod_combine_def
      by simp
  qed
  fix c1 c2 A B
  assume "identity c1 A \<in> tmod_combine_prop Tmod (tmod_enum_field classtype name enumid enumvalues)"
  then have "identity c1 A \<in> Prop Tmod"
  proof (cases)
    case identity_property_tmod1
    then show ?thesis
      by blast
  next
    case identity_property_tmod2
    then show ?thesis
      unfolding tmod_enum_field_def
      by simp
  next
    case identity_property_both
    then show ?thesis
      unfolding tmod_enum_field_def
      by simp
  qed
  assume "identity c2 B \<in> tmod_combine_prop Tmod (tmod_enum_field classtype name enumid enumvalues)"
  then have "identity c2 B \<in> Prop Tmod"
  proof (cases)
    case identity_property_tmod1
    then show ?thesis
      by blast
  next
    case identity_property_tmod2
    then show ?thesis
      unfolding tmod_enum_field_def
      by simp
  next
    case identity_property_both
    then show ?thesis
      unfolding tmod_enum_field_def
      by simp
  qed
  assume c1_c2_neq: "c1 \<noteq> c2"
  assume not_extend_tmod: "\<not>\<exclamdown>c1 \<sqsubseteq>[Tmod] \<exclamdown>c2"
  assume "\<exclamdown>c1 \<sqsubseteq>[tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues)] \<exclamdown>c2"
  then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_rel_altdef (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues))"
    unfolding subtype_def
    using inh_wellformed_classes subtype_rel_alt
    by blast
  then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_tuple ` Type (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+ \<union> 
    subtype_conv proper proper ` (Inh (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_rel_altdef Tmod"
  proof (elim UnE)
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_tuple ` Type (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues))"
    then have "c1 = c2"
      unfolding subtype_tuple_def
      by blast
    then show ?thesis
      using c1_c2_neq
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper proper ` (Inh (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      unfolding tmod_combine_def tmod_enum_field_def
      by simp
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` (Inh (tmod_combine Tmod (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then have "\<exclamdown>c1 \<sqsubseteq>[Tmod] \<exclamdown>c2"
    unfolding subtype_def
    by (simp add: assms(1) subtype_rel_alt type_model.structure_inh_wellformed_classes)
  then show "A \<subseteq> B"
    using not_extend_tmod
    by blast
qed (simp_all add: assms tmod_enum_field_def)



section "Encoding of an enum-typed field in which the enum-type is encoded as node types in GROOVE"

definition tg_enum_as_node_types_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 't set \<Rightarrow> ('t list) type_graph" where
  "tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues = \<lparr>
    NT = {type (id_to_list classtype), type (id_to_list enumid)} \<union> type ` append (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues,
    ET = {(type (id_to_list classtype), edge [name], type (id_to_list enumid))},
    inh = {(type (id_to_list classtype), type (id_to_list classtype)), (type (id_to_list enumid), type (id_to_list enumid))} \<union> 
      (\<lambda>x. (type x, type x)) ` append (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues \<union>
      (\<lambda>x. (type x, type (id_to_list enumid))) ` append (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues,
    abs = {type (id_to_list enumid)},
    mult = (\<lambda>x. if x = (type (id_to_list classtype), edge [name], type (id_to_list enumid)) then (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1) else undefined),
    contains = {}
  \<rparr>"

lemma tg_enum_as_node_types_field_as_edge_type_correct:
  shows "type_graph (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
proof (intro type_graph.intro)
  fix n
  assume "n \<in> NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
  then have "n = type (id_to_list classtype) \<or> n = type (id_to_list enumid) \<or> n \<in> type ` append (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
    unfolding tg_enum_as_node_types_field_as_edge_type_def
    by simp
  then show "n \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
    using Lab\<^sub>t.rule_type_labels
    by fastforce
next
  fix s l t
  assume "(s, l, t) \<in> ET (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
  then have "(s, l, t) = (type (id_to_list classtype), edge [name], type (id_to_list enumid))"
    unfolding tg_enum_as_node_types_field_as_edge_type_def
    by simp
  then have "s \<in> {type (id_to_list classtype), type (id_to_list enumid)} \<union> type ` append (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues \<and> 
    l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> {type (id_to_list classtype), type (id_to_list enumid)} \<union> type ` append (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
  proof (intro conjI)
    assume "(s, l, t) = (type (id_to_list classtype), edge [name], type (id_to_list enumid))"
    then show "l \<in> Lab\<^sub>e \<union> Lab\<^sub>f"
      using Lab\<^sub>e.rule_edge_labels
      by fastforce
  qed (simp_all)
  then show "s \<in> NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<and> 
    l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
    unfolding tg_enum_as_node_types_field_as_edge_type_def
    by simp
next
  fix e
  assume "e \<in> ET (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
  then have "mult (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) e = (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1)"
    unfolding tg_enum_as_node_types_field_as_edge_type_def
    by simp
  then show "multiplicity_pair (mult (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) e)"
  proof (intro multiplicity_pair.intro)
    assume mult_e_def: "mult (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) e = (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1)"
    show "multiplicity (m_in (mult (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) e))"
      using mult_e_def
      by (intro multiplicity.intro) (simp_all)
    show "multiplicity (m_out (mult (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) e))"
      using mult_e_def
      by (intro multiplicity.intro) (simp_all)
  qed
next
  show inheritance_field: "Relation.Field (inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)) = 
    NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
    unfolding Relation.Field_def tg_enum_as_node_types_field_as_edge_type_def
    by fastforce
  show "Partial_order (inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))"
    unfolding partial_order_on_def preorder_on_def
  proof (intro conjI)
    show "Refl (inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))"
      unfolding refl_on_def
    proof (intro conjI)
      show "inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<subseteq> 
        Relation.Field (inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)) \<times> 
        Relation.Field (inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))"
        using FieldI1 FieldI2 inheritance_field
        by fastforce
    next
      have "\<And>x. x \<in> NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<Longrightarrow> 
        (x, x) \<in> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
        unfolding tg_enum_as_node_types_field_as_edge_type_def
        by fastforce
      then show "\<forall>x \<in> Relation.Field (inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)). 
        (x, x) \<in> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
        using inheritance_field
        by blast
    qed
  next
    show "trans (inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))"
      unfolding tg_enum_as_node_types_field_as_edge_type_def trans_def
      by fastforce
  next
    show "antisym (inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))"
      unfolding tg_enum_as_node_types_field_as_edge_type_def antisym_def
      by fastforce
  qed
qed (simp_all add: tg_enum_as_node_types_field_as_edge_type_def)

lemma tg_enum_as_node_types_field_as_edge_type_combine_correct:
  assumes "type_graph TG"
  assumes existing_node_types: "NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<subseteq> NT TG"
  assumes existing_inheritance: "inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<subseteq> inh TG"
  assumes abstract_maintained: "abs (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<subseteq> abs TG"
  assumes new_edge_type: "\<And>s l t. (s, type (id_to_list classtype)) \<in> inh TG \<or> (type (id_to_list classtype), s) \<in> inh TG \<Longrightarrow> l = edge [name] \<Longrightarrow> (s, l, t) \<notin> ET TG"
  shows "type_graph (tg_combine TG (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))"
proof (intro tg_combine_merge_correct)
  show "type_graph (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
    by (fact tg_enum_as_node_types_field_as_edge_type_correct)
next
  show "ET TG \<inter> ET (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) = {}"
    using existing_node_types
    unfolding tg_enum_as_node_types_field_as_edge_type_def
    by (simp add: assms(1) new_edge_type type_graph.validity_inh_node)
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume e2_def: "(s2, l, t2) \<in> ET TG"
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+ \<or> 
    (t2, t1) \<in> (inh TG \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+"
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+ - inh TG \<or> 
    (s2, s1) \<in> (inh TG \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+ - inh TG"
  then have "(s1, s2) \<in> inh TG - inh TG \<or> (s2, s1) \<in> inh TG - inh TG"
    by (simp add: Un_absorb2 assms(1) existing_inheritance type_graph.validity_inh_trans)
  then have "(s1, s2) \<in> {} \<or> (s2, s1) \<in> {}"
    by blast
  then show "s1 = s2 \<and> t1 = t2"
    by blast
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume e2_def: "(s2, l, t2) \<in> ET TG"
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+ \<or> 
    (s2, s1) \<in> (inh TG \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+"
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+ - inh TG \<or> 
    (t2, t1) \<in> (inh TG \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+ - inh TG"
  then have "(t1, t2) \<in> inh TG - inh TG \<or> (t2, t1) \<in> inh TG - inh TG"
    by (simp add: Un_absorb2 assms(1) existing_inheritance type_graph.validity_inh_trans)
  then have "(t1, t2) \<in> {} \<or> (t2, t1) \<in> {}"
    by blast
  then show "s1 = s2 \<and> t1 = t2"
    by blast
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume "(s2, l, t2) \<in> ET (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
  then have e2_def: "(s2, l, t2) = (type (id_to_list classtype), edge [name], type (id_to_list enumid))"
    unfolding tg_enum_as_node_types_field_as_edge_type_def
    by simp
  then have l_def: "l = edge [name]"
    by blast
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+ \<or> 
    (s2, s1) \<in> (inh TG \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+"
  then have "(s1, s2) \<in> inh TG \<or> (s2, s1) \<in> inh TG"
    by (simp add: Un_absorb2 assms(1) existing_inheritance type_graph.validity_inh_trans)
  then show "s1 = s2 \<and> t1 = t2"
    using e1_def e2_def new_edge_type
    by simp
next
  show "antisym ((inh TG \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+)"
    by (simp add: Un_absorb2 assms(1) existing_inheritance type_graph.validity_inh_antisym type_graph.validity_inh_trans)
qed (simp_all add: tg_enum_as_node_types_field_as_edge_type_def assms)


subsection "Transformation functions"

definition tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type :: "'t type_model \<Rightarrow> ('t list) type_graph" where
  "tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type Tmod = \<lparr>
    NT = type ` id_to_list ` (Class Tmod \<union> Enum Tmod) \<union> type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue Tmod,
    ET = (\<lambda>x. (type (id_to_list (fst (fst x))), edge [(snd (fst x))], (type (id_to_list (snd x))))) ` (Field Tmod \<times> Enum Tmod),
    inh = (\<lambda>x. (x, x)) ` type ` id_to_list ` (Class Tmod \<union> Enum Tmod) \<union>
      (\<lambda>x. (type x, type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue Tmod \<union>
      type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue Tmod \<times> type ` id_to_list ` Enum Tmod,
    abs = type ` id_to_list ` Enum Tmod,
    mult = (\<lambda>x. if x \<in> (\<lambda>x. (type (id_to_list (fst (fst x))), edge [(snd (fst x))], (type (id_to_list (snd x))))) ` (Field Tmod \<times> Enum Tmod) then (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1) else undefined),
    contains = {}
  \<rparr>"

lemma tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type_proj:
  shows "tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type (tmod_enum_field classtype name enumid enumvalues) = tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues"
proof-
  have "(\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues =
    (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
    by force
  then have enumvalue_proj: "LabDef.type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues =
    LabDef.type ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
    by simp
  then have nt_proj: "{LabDef.type (id_to_list enumid), LabDef.type (id_to_list classtype)} \<union> LabDef.type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues =
    {LabDef.type (id_to_list classtype), LabDef.type (id_to_list enumid)} \<union> LabDef.type ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
    by fastforce
  have "(\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues = 
    (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
    by force
  then have inh_proj1: "(\<lambda>x. (LabDef.type x, LabDef.type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues = 
    (\<lambda>x. (LabDef.type x, LabDef.type x)) ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
    by simp
  have inh_proj2: "LabDef.type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues \<times> {LabDef.type (id_to_list enumid)} =
    (\<lambda>x. (LabDef.type x, LabDef.type (id_to_list enumid))) ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
  proof
    show "LabDef.type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues \<times> {LabDef.type (id_to_list enumid)} \<subseteq> 
      (\<lambda>x. (LabDef.type x, LabDef.type (id_to_list enumid))) ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
    proof
      fix x
      assume "x \<in> LabDef.type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues \<times> {LabDef.type (id_to_list enumid)}"
      then show "x \<in> (\<lambda>x. (LabDef.type x, LabDef.type (id_to_list enumid))) ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
        by auto
    qed
  next
    show "(\<lambda>x. (LabDef.type x, LabDef.type (id_to_list enumid))) ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues \<subseteq> 
      LabDef.type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues \<times> {LabDef.type (id_to_list enumid)}"
    proof
      fix x
      assume "x \<in> (\<lambda>x. (LabDef.type x, LabDef.type (id_to_list enumid))) ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
      then show "x \<in> LabDef.type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues \<times> {LabDef.type (id_to_list enumid)}"
        using enumvalue_proj
        by auto
    qed
  qed
  have "(\<lambda>x. (LabDef.type x, LabDef.type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues \<union> 
    LabDef.type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues \<times> {LabDef.type (id_to_list enumid)} =
    (\<lambda>x. (LabDef.type x, LabDef.type x)) ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues \<union> 
    (\<lambda>x. (LabDef.type x, LabDef.type (id_to_list enumid))) ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
    using inh_proj1 inh_proj2
    by simp
  then have inh_proj: "{(LabDef.type (id_to_list enumid), LabDef.type (id_to_list enumid)), (LabDef.type (id_to_list classtype), LabDef.type (id_to_list classtype))} \<union> 
    (\<lambda>x. (LabDef.type x, LabDef.type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues \<union> 
    LabDef.type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair enumid ` enumvalues \<times> {LabDef.type (id_to_list enumid)} =
    {(LabDef.type (id_to_list classtype), LabDef.type (id_to_list classtype)), (LabDef.type (id_to_list enumid), LabDef.type (id_to_list enumid))} \<union> 
    (\<lambda>x. (LabDef.type x, LabDef.type x)) ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues \<union> 
    (\<lambda>x. (LabDef.type x, LabDef.type (id_to_list enumid))) ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
    by auto
  show "tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type (tmod_enum_field classtype name enumid enumvalues) = tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues"
    unfolding tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def tmod_enum_field_def
    using nt_proj inh_proj
    by simp
qed

lemma tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type_func:
  shows "tg_combine_mapping_function (tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type) 
    (tmod_enum_field classtype name enumid enumvalues) (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
proof (intro tg_combine_mapping_function.intro)
  show "tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type (tmod_enum_field classtype name enumid enumvalues) = tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues"
    by (fact tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type_proj)
next
  fix TmodX
  show "NT (tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type (tmod_enum_field classtype name enumid enumvalues)) \<subseteq> 
    NT (tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type (tmod_combine (tmod_enum_field classtype name enumid enumvalues) TmodX))"
  proof
    fix x
    assume "x \<in> NT (tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type (tmod_enum_field classtype name enumid enumvalues))"
    then show "x \<in> NT (tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type (tmod_combine (tmod_enum_field classtype name enumid enumvalues) TmodX))"
      unfolding tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type_def tmod_enum_field_def tg_enum_as_node_types_field_as_edge_type_def tmod_combine_def
      by auto
  qed
qed (auto simp add: tmod_enum_field_to_tg_enum_as_node_types_field_as_edge_type_def tmod_enum_field_def tg_enum_as_node_types_field_as_edge_type_def tmod_combine_def)

definition tg_enum_as_node_types_field_as_edge_type_to_tmod_enum_field :: "'t Id \<Rightarrow> 't Id \<Rightarrow> 't set \<Rightarrow> ('t list) type_graph \<Rightarrow> 't type_model" where
  "tg_enum_as_node_types_field_as_edge_type_to_tmod_enum_field classtype enumid enumvalues TG = \<lparr>
    Class = list_to_id ` unlabel ` {n \<in> NT TG. n = type (id_to_list classtype)},
    Enum = list_to_id ` unlabel ` {n \<in> NT TG. n = type (id_to_list enumid)},
    UserDataType = {},
    Field = (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET TG,
    FieldSig = (\<lambda>x. if x \<in> (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET TG then (enumtype enumid, \<^bold>1..\<^bold>1) else undefined),
    EnumValue = Pair enumid ` enumvalues,
    Inh = {},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tg_enum_as_node_types_field_as_edge_type_to_tmod_enum_field_proj:
  shows "tg_enum_as_node_types_field_as_edge_type_to_tmod_enum_field classtype enumid enumvalues (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) = 
    tmod_enum_field classtype name enumid enumvalues"
proof-
  have class_def: "{n. n = LabDef.type (id_to_list classtype) \<and> (n = LabDef.type (id_to_list classtype) \<or> 
      n = LabDef.type (id_to_list enumid) \<or> n \<in> LabDef.type ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues)} = 
    {LabDef.type (id_to_list classtype)}"
    by blast
  have enum_def: "{n. n = LabDef.type (id_to_list enumid) \<and> (n = LabDef.type (id_to_list classtype) \<or> 
      n = LabDef.type (id_to_list enumid) \<or> n \<in> LabDef.type ` (@) (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues)} = 
    {LabDef.type (id_to_list enumid)}"
    by blast
  show "tg_enum_as_node_types_field_as_edge_type_to_tmod_enum_field classtype enumid enumvalues (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) = 
    tmod_enum_field classtype name enumid enumvalues"
    unfolding tg_enum_as_node_types_field_as_edge_type_to_tmod_enum_field_def tmod_enum_field_def tg_enum_as_node_types_field_as_edge_type_def
    by (simp add: class_def enum_def id_to_list_inverse)
qed

lemma tg_enum_as_node_types_field_as_edge_type_to_tmod_enum_field_func:
  shows "tmod_combine_mapping_function (tg_enum_as_node_types_field_as_edge_type_to_tmod_enum_field classtype enumid enumvalues) 
    (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) (tmod_enum_field classtype name enumid enumvalues)"
proof (intro tmod_combine_mapping_function.intro)
  show "tg_enum_as_node_types_field_as_edge_type_to_tmod_enum_field classtype enumid enumvalues 
    (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) = tmod_enum_field classtype name enumid enumvalues"
    by (fact tg_enum_as_node_types_field_as_edge_type_to_tmod_enum_field_proj)
qed (auto simp add: tg_enum_as_node_types_field_as_edge_type_to_tmod_enum_field_def tmod_enum_field_def tg_enum_as_node_types_field_as_edge_type_def tg_combine_def id_to_list_inverse)



section "Encoding of an enum-typed field in which the enum-type is encoded as flags in GROOVE"

definition tg_enum_as_flags_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> ('t list) type_graph" where
  "tg_enum_as_flags_field_as_edge_type classtype name enumid = \<lparr>
    NT = {type (id_to_list classtype), type (id_to_list enumid)},
    ET = {(type (id_to_list classtype), edge [name], type (id_to_list enumid))},
    inh = {(type (id_to_list classtype), type (id_to_list classtype)), (type (id_to_list enumid), type (id_to_list enumid))},
    abs = {},
    mult = (\<lambda>x. if x = (type (id_to_list classtype), edge [name], type (id_to_list enumid)) then (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1) else undefined),
    contains = {}
  \<rparr>"

lemma tg_enum_as_flags_field_as_edge_type_correct:
  shows "type_graph (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
proof (intro type_graph.intro)
  fix n
  assume "n \<in> NT (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
  then have "n = type (id_to_list classtype) \<or> n = type (id_to_list enumid)"
    unfolding tg_enum_as_flags_field_as_edge_type_def
    by simp
  then show "n \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
    using Lab\<^sub>t.rule_type_labels
    by fastforce
next
  fix s l t
  assume "(s, l, t) \<in> ET (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
  then have "(s, l, t) = (type (id_to_list classtype), edge [name], type (id_to_list enumid))"
    unfolding tg_enum_as_flags_field_as_edge_type_def
    by simp
  then have "s \<in> {type (id_to_list classtype), type (id_to_list enumid)} \<and> 
    l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> {type (id_to_list classtype), type (id_to_list enumid)}"
  proof (intro conjI)
    assume "(s, l, t) = (type (id_to_list classtype), edge [name], type (id_to_list enumid))"
    then show "l \<in> Lab\<^sub>e \<union> Lab\<^sub>f"
      using Lab\<^sub>e.rule_edge_labels
      by fastforce
  qed (simp_all)
  then show "s \<in> NT (tg_enum_as_flags_field_as_edge_type classtype name enumid) \<and> 
    l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> NT (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
    unfolding tg_enum_as_flags_field_as_edge_type_def
    by simp
next
  fix e
  assume "e \<in> ET (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
  then have "mult (tg_enum_as_flags_field_as_edge_type classtype name enumid) e = (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1)"
    unfolding tg_enum_as_flags_field_as_edge_type_def
    by simp
  then show "multiplicity_pair (mult (tg_enum_as_flags_field_as_edge_type classtype name enumid) e)"
  proof (intro multiplicity_pair.intro)
    assume mult_e_def: "mult (tg_enum_as_flags_field_as_edge_type classtype name enumid) e = (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1)"
    show "multiplicity (m_in (mult (tg_enum_as_flags_field_as_edge_type classtype name enumid) e))"
      using mult_e_def
      by (intro multiplicity.intro) (simp_all)
    show "multiplicity (m_out (mult (tg_enum_as_flags_field_as_edge_type classtype name enumid) e))"
      using mult_e_def
      by (intro multiplicity.intro) (simp_all)
  qed
next
  show inheritance_field: "Relation.Field (inh (tg_enum_as_flags_field_as_edge_type classtype name enumid)) = 
    NT (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
    unfolding Relation.Field_def tg_enum_as_flags_field_as_edge_type_def
    by fastforce
  show "Partial_order (inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))"
    unfolding partial_order_on_def preorder_on_def
  proof (intro conjI)
    show "Refl (inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))"
      unfolding refl_on_def
    proof (intro conjI)
      show "inh (tg_enum_as_flags_field_as_edge_type classtype name enumid) \<subseteq> 
        Relation.Field (inh (tg_enum_as_flags_field_as_edge_type classtype name enumid)) \<times> 
        Relation.Field (inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))"
        using FieldI1 FieldI2 inheritance_field
        by fastforce
    next
      have "\<And>x. x \<in> NT (tg_enum_as_flags_field_as_edge_type classtype name enumid) \<Longrightarrow> 
        (x, x) \<in> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
        unfolding tg_enum_as_flags_field_as_edge_type_def
        by fastforce
      then show "\<forall>x \<in> Relation.Field (inh (tg_enum_as_flags_field_as_edge_type classtype name enumid)). 
        (x, x) \<in> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
        using inheritance_field
        by blast
    qed
  next
    show "trans (inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))"
      unfolding tg_enum_as_flags_field_as_edge_type_def trans_def
      by fastforce
  next
    show "antisym (inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))"
      unfolding tg_enum_as_flags_field_as_edge_type_def antisym_def
      by fastforce
  qed
qed (simp_all add: tg_enum_as_flags_field_as_edge_type_def)

lemma tg_enum_as_flags_field_as_edge_type_combine_correct:
  assumes "type_graph TG"
  assumes existing_node_types: "NT (tg_enum_as_flags_field_as_edge_type classtype name enumid) \<subseteq> NT TG"
  assumes existing_inheritance: "inh (tg_enum_as_flags_field_as_edge_type classtype name enumid) \<subseteq> inh TG"
  assumes new_edge_type: "\<And>s l t. (s, type (id_to_list classtype)) \<in> inh TG \<or> (type (id_to_list classtype), s) \<in> inh TG \<Longrightarrow> l = edge [name] \<Longrightarrow> (s, l, t) \<notin> ET TG"
  shows "type_graph (tg_combine TG (tg_enum_as_flags_field_as_edge_type classtype name enumid))"
proof (intro tg_combine_merge_correct)
  show "type_graph (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
    by (fact tg_enum_as_flags_field_as_edge_type_correct)
next
  show "ET TG \<inter> ET (tg_enum_as_flags_field_as_edge_type classtype name enumid) = {}"
    using existing_node_types
    unfolding tg_enum_as_flags_field_as_edge_type_def
    by (simp add: assms(1) new_edge_type type_graph.validity_inh_node)
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume e2_def: "(s2, l, t2) \<in> ET TG"
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+ \<or> 
    (t2, t1) \<in> (inh TG \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+"
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+ - inh TG \<or> 
    (s2, s1) \<in> (inh TG \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+ - inh TG"
  then have "(s1, s2) \<in> inh TG - inh TG \<or> (s2, s1) \<in> inh TG - inh TG"
    by (simp add: Un_absorb2 assms(1) existing_inheritance type_graph.validity_inh_trans)
  then have "(s1, s2) \<in> {} \<or> (s2, s1) \<in> {}"
    by blast
  then show "s1 = s2 \<and> t1 = t2"
    by blast
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume e2_def: "(s2, l, t2) \<in> ET TG"
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+ \<or> 
    (s2, s1) \<in> (inh TG \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+"
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+ - inh TG \<or> 
    (t2, t1) \<in> (inh TG \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+ - inh TG"
  then have "(t1, t2) \<in> inh TG - inh TG \<or> (t2, t1) \<in> inh TG - inh TG"
    by (simp add: Un_absorb2 assms(1) existing_inheritance type_graph.validity_inh_trans)
  then have "(t1, t2) \<in> {} \<or> (t2, t1) \<in> {}"
    by blast
  then show "s1 = s2 \<and> t1 = t2"
    by blast
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume "(s2, l, t2) \<in> ET (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
  then have e2_def: "(s2, l, t2) = (type (id_to_list classtype), edge [name], type (id_to_list enumid))"
    unfolding tg_enum_as_flags_field_as_edge_type_def
    by simp
  then have l_def: "l = edge [name]"
    by blast
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+ \<or> 
    (s2, s1) \<in> (inh TG \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+"
  then have "(s1, s2) \<in> inh TG \<or> (s2, s1) \<in> inh TG"
    by (simp add: Un_absorb2 assms(1) existing_inheritance type_graph.validity_inh_trans)
  then show "s1 = s2 \<and> t1 = t2"
    using e1_def e2_def new_edge_type
    by simp
next
  show "antisym ((inh TG \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+)"
    by (simp add: Un_absorb2 assms(1) existing_inheritance type_graph.validity_inh_antisym type_graph.validity_inh_trans)
qed (simp_all add: tg_enum_as_flags_field_as_edge_type_def assms)


subsection "Transformation functions"

definition tmod_enum_field_to_tg_enum_as_flags_field_as_edge_type :: "'t type_model \<Rightarrow> ('t list) type_graph" where
  "tmod_enum_field_to_tg_enum_as_flags_field_as_edge_type Tmod = \<lparr>
    NT = type ` id_to_list ` (Class Tmod \<union> Enum Tmod),
    ET = (\<lambda>x. (type (id_to_list (fst (fst x))), edge [(snd (fst x))], (type (id_to_list (snd x))))) ` (Field Tmod \<times> Enum Tmod),
    inh = (\<lambda>x. (x, x)) ` type ` id_to_list ` (Class Tmod \<union> Enum Tmod),
    abs = {},
    mult = (\<lambda>x. if x \<in> (\<lambda>x. (type (id_to_list (fst (fst x))), edge [(snd (fst x))], (type (id_to_list (snd x))))) ` (Field Tmod \<times> Enum Tmod) then (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1) else undefined),
    contains = {}
  \<rparr>"

lemma tmod_enum_field_to_tg_enum_as_flags_field_as_edge_type_proj:
  shows "tmod_enum_field_to_tg_enum_as_flags_field_as_edge_type (tmod_enum_field classtype name enumid enumvalues) = tg_enum_as_flags_field_as_edge_type classtype name enumid"
  unfolding tmod_enum_field_to_tg_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def tmod_enum_field_def
  by auto

lemma tmod_enum_field_to_tg_enum_as_flags_field_as_edge_type_func:
  shows "tg_combine_mapping_function (tmod_enum_field_to_tg_enum_as_flags_field_as_edge_type) 
    (tmod_enum_field classtype name enumid enumvalues) (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
  by (intro tg_combine_mapping_function.intro)
    (auto simp add: tmod_enum_field_to_tg_enum_as_flags_field_as_edge_type_def tmod_enum_field_def tg_enum_as_flags_field_as_edge_type_def tmod_combine_def)

definition tg_enum_as_flags_field_as_edge_type_to_tmod_enum_field :: "'t Id \<Rightarrow> 't Id \<Rightarrow> 't set \<Rightarrow> ('t list) type_graph \<Rightarrow> 't type_model" where
  "tg_enum_as_flags_field_as_edge_type_to_tmod_enum_field classtype enumid enumvalues TG = \<lparr>
    Class = list_to_id ` unlabel ` {n \<in> NT TG. n = type (id_to_list classtype)},
    Enum = list_to_id ` unlabel ` {n \<in> NT TG. n = type (id_to_list enumid)},
    UserDataType = {},
    Field = (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET TG,
    FieldSig = (\<lambda>x. if x \<in> (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET TG then (enumtype enumid, \<^bold>1..\<^bold>1) else undefined),
    EnumValue = Pair enumid ` enumvalues,
    Inh = {},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tg_enum_as_flags_field_as_edge_type_to_tmod_enum_field_proj:
  shows "tg_enum_as_flags_field_as_edge_type_to_tmod_enum_field classtype enumid enumvalues (tg_enum_as_flags_field_as_edge_type classtype name enumid) = 
    tmod_enum_field classtype name enumid enumvalues"
proof-
  have class_def: "{n. n = LabDef.type (id_to_list classtype) \<and> (n = LabDef.type (id_to_list classtype) \<or> n = LabDef.type (id_to_list enumid))} = 
    {LabDef.type (id_to_list classtype)}"
    by blast
  have enum_def: "{n. n = LabDef.type (id_to_list enumid) \<and> (n = LabDef.type (id_to_list classtype) \<or> n = LabDef.type (id_to_list enumid))} = 
    {LabDef.type (id_to_list enumid)}"
    by blast
  show "tg_enum_as_flags_field_as_edge_type_to_tmod_enum_field classtype enumid enumvalues (tg_enum_as_flags_field_as_edge_type classtype name enumid) = 
    tmod_enum_field classtype name enumid enumvalues"
    unfolding tg_enum_as_flags_field_as_edge_type_to_tmod_enum_field_def tmod_enum_field_def tg_enum_as_flags_field_as_edge_type_def
    by (simp add: class_def enum_def id_to_list_inverse)
qed

lemma tg_enum_as_flags_field_as_edge_type_to_tmod_enum_field_func:
  shows "tmod_combine_mapping_function (tg_enum_as_flags_field_as_edge_type_to_tmod_enum_field classtype enumid enumvalues) 
    (tg_enum_as_flags_field_as_edge_type classtype name enumid) (tmod_enum_field classtype name enumid enumvalues)"
proof (intro tmod_combine_mapping_function.intro)
  show "tg_enum_as_flags_field_as_edge_type_to_tmod_enum_field classtype enumid enumvalues 
    (tg_enum_as_flags_field_as_edge_type classtype name enumid) = tmod_enum_field classtype name enumid enumvalues"
    by (fact tg_enum_as_flags_field_as_edge_type_to_tmod_enum_field_proj)
qed (auto simp add: tg_enum_as_flags_field_as_edge_type_to_tmod_enum_field_def tmod_enum_field_def tg_enum_as_flags_field_as_edge_type_def tg_combine_def id_to_list_inverse)

end