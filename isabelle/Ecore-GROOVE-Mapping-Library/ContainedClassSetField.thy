theory ContainedClassSetField
  imports
    Main
    "Ecore-GROOVE-Mapping.Type_Model_Graph_Mapping"
    "Ecore-GROOVE-Mapping.Identifier_List"
begin

section "Definition of a type model which introduces a field typed by a set of contained objects."

definition tmod_contained_class_set_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> multiplicity \<Rightarrow> 't type_model" where
  "tmod_contained_class_set_field classtype name containedtype mul = \<lparr>
    Class = {classtype, containedtype},
    Enum = {},
    UserDataType = {},
    Field = {(classtype, name)},
    FieldSig = (\<lambda>x. if x = (classtype, name) then (setof \<exclamdown>containedtype, mul) else undefined),
    EnumValue = {},
    Inh = {},
    Prop = {containment (classtype, name)},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tmod_contained_class_set_field_correct:
  assumes valid_ns: "\<not>id_in_ns containedtype (Identifier classtype) \<and> \<not>id_in_ns classtype (Identifier containedtype)"
  assumes valid_mul: "multiplicity mul"
  shows "type_model (tmod_contained_class_set_field classtype name containedtype mul)"
proof (intro type_model.intro)
  fix f
  assume "f \<in> Field (tmod_contained_class_set_field classtype name containedtype mul)"
  then have "f = (classtype, name)"
    unfolding tmod_contained_class_set_field_def
    by simp
  then have "FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f = (setof \<exclamdown>containedtype, mul)"
    unfolding tmod_contained_class_set_field_def
    by simp
  then show "fst (FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f) \<in> Type (tmod_contained_class_set_field classtype name containedtype mul) \<and> 
    multiplicity (snd (FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f))"
  proof (intro conjI)
    assume "FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f = (setof \<exclamdown>containedtype, mul)"
    then have contained_type_def: "fst (FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f) = setof \<exclamdown>containedtype"
      by simp
    have "\<exclamdown>containedtype \<in> NonContainerType (tmod_contained_class_set_field classtype name containedtype mul)"
      unfolding NonContainerType_def ClassType_def
      by (simp add: ProperClassType.rule_proper_classes tmod_contained_class_set_field_def)
    then show "fst (FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f) \<in> Type (tmod_contained_class_set_field classtype name containedtype mul)"
      unfolding Type_def
      using contained_type_def
      by (simp add: ContainerType.rule_setof_type tmod_contained_class_set_field_def)
  next
    assume "FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f = (setof \<exclamdown>containedtype, mul)"
    then have snd_def: "snd (FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f) = mul"
      by simp
    then show "multiplicity (snd (FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f))"
      using valid_mul
      by simp
  qed
next
  fix p
  assume "p \<in> Prop (tmod_contained_class_set_field classtype name containedtype mul)"
  then have p_def: "p = containment (classtype, name)"
    unfolding tmod_contained_class_set_field_def
    by simp
  have "containment (classtype, name) \<in> Property (tmod_contained_class_set_field classtype name containedtype mul)"
  proof (intro Property.containment_property)
    have "(classtype, name) \<in> Attr (tmod_contained_class_set_field classtype name containedtype mul) \<Longrightarrow> False"
    proof-
      assume "(classtype, name) \<in> Attr (tmod_contained_class_set_field classtype name containedtype mul)"
      then have "Type_Model.type (tmod_contained_class_set_field classtype name containedtype mul) (classtype, name) \<in> AttrType (tmod_contained_class_set_field classtype name containedtype mul)"
        unfolding Attr_def
        by simp
      then have "setof \<exclamdown>containedtype \<in> AttrType (tmod_contained_class_set_field classtype name containedtype mul)"
        unfolding Type_Model.type_def tmod_contained_class_set_field_def
        by simp
      then show "False"
      proof (cases)
        case rule_setof_attributes
        then show ?thesis
          by (cases) (simp_all add: DataType_def)
      qed (simp_all add: DataType_def)
    qed
    then show "(classtype, name) \<in> Rel (tmod_contained_class_set_field classtype name containedtype mul)"
      unfolding Rel_def tmod_contained_class_set_field_def
      by fastforce
  qed
  then show "p \<in> Property (tmod_contained_class_set_field classtype name containedtype mul)"
    using p_def
    by simp
next
  fix x y
  assume "x \<in> Class (tmod_contained_class_set_field classtype name containedtype mul) \<union> 
    Enum (tmod_contained_class_set_field classtype name containedtype mul) \<union> 
    UserDataType (tmod_contained_class_set_field classtype name containedtype mul)"
  then have x_def: "x = classtype \<or> x = containedtype"
    unfolding tmod_contained_class_set_field_def
    by simp
  assume "y \<in> Class (tmod_contained_class_set_field classtype name containedtype mul) \<union> 
    Enum (tmod_contained_class_set_field classtype name containedtype mul) \<union> 
    UserDataType (tmod_contained_class_set_field classtype name containedtype mul)"
  then have y_def: "y = classtype \<or> y = containedtype"
    unfolding tmod_contained_class_set_field_def
    by simp
  show "\<not>id_in_ns x (Identifier y)"
    using x_def y_def valid_ns
    by fastforce
next
  have "asym {} \<and> irrefl {}"
    by (simp add: asym.intros irrefl_def)
  then show "asym (Inh (tmod_contained_class_set_field classtype name containedtype mul)) \<and> irrefl ((Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+)"
    unfolding tmod_contained_class_set_field_def
    by simp
next
  fix f
  assume assump: "f \<in> Field (tmod_contained_class_set_field classtype name containedtype mul) \<and> 
    Type_Model.type (tmod_contained_class_set_field classtype name containedtype mul) f \<in> DataType \<union> 
      EnumType (tmod_contained_class_set_field classtype name containedtype mul) \<union> 
      UserDataTypeType (tmod_contained_class_set_field classtype name containedtype mul) \<union> 
      ProperClassType (tmod_contained_class_set_field classtype name containedtype mul)"
  then have "f = (classtype, name)"
    unfolding tmod_contained_class_set_field_def
    by simp
  then have "Type_Model.type (tmod_contained_class_set_field classtype name containedtype mul) f = setof \<exclamdown>containedtype"
    unfolding Type_Model.type_def tmod_contained_class_set_field_def
    by simp
  then show "lower (tmod_contained_class_set_field classtype name containedtype mul) f = \<^bold>1"
    using assump
    by simp
next
  fix f
  assume assump: "f \<in> Field (tmod_contained_class_set_field classtype name containedtype mul) \<and> 
    Type_Model.type (tmod_contained_class_set_field classtype name containedtype mul) f \<in> NullableClassType (tmod_contained_class_set_field classtype name containedtype mul)"
  then have "f = (classtype, name)"
    unfolding tmod_contained_class_set_field_def
    by simp
  then have "Type_Model.type (tmod_contained_class_set_field classtype name containedtype mul) f = setof \<exclamdown>containedtype"
    unfolding Type_Model.type_def tmod_contained_class_set_field_def
    by simp
  then show "lower (tmod_contained_class_set_field classtype name containedtype mul) f = \<^bold>0"
    using assump
    by simp
next
  fix f
  assume assump: "f \<in> Field (tmod_contained_class_set_field classtype name containedtype mul) \<and> 
    Type_Model.type (tmod_contained_class_set_field classtype name containedtype mul) f \<in> NonContainerType (tmod_contained_class_set_field classtype name containedtype mul)"
  then have "f = (classtype, name)"
    unfolding tmod_contained_class_set_field_def
    by simp
  then have "Type_Model.type (tmod_contained_class_set_field classtype name containedtype mul) f = setof \<exclamdown>containedtype"
    unfolding Type_Model.type_def tmod_contained_class_set_field_def
    by simp
  then show "upper (tmod_contained_class_set_field classtype name containedtype mul) f = \<^bold>1"
    using assump
    by simp
qed (simp_all add: tmod_contained_class_set_field_def)

lemma tmod_contained_class_set_field_combine_correct:
  assumes "type_model Tmod"
  assumes existing_classes: "{classtype, containedtype} \<subseteq> Class Tmod"
  assumes new_field: "(classtype, name) \<notin> Field Tmod"
  assumes valid_ns: "\<not>id_in_ns containedtype (Identifier classtype) \<and> \<not>id_in_ns classtype (Identifier containedtype)"
  assumes valid_mul: "multiplicity mul"
  shows "type_model (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul))"
proof (intro tmod_combine_merge_correct)
  show "type_model (tmod_contained_class_set_field classtype name containedtype mul)"
    using valid_ns valid_mul
    by (fact tmod_contained_class_set_field_correct)
next
  fix c
  assume "c \<in> Class (tmod_contained_class_set_field classtype name containedtype mul)"
  then have "c \<in> Class Tmod"
    unfolding tmod_contained_class_set_field_def
    using existing_classes
    by fastforce
  then show "c \<notin> Enum Tmod \<and> c \<notin> UserDataType Tmod"
    using assms(1) type_model.property_class_disjoint
    by blast
next
  fix e
  assume "e \<in> Enum Tmod"
  then have "e \<noteq> classtype \<and> e \<noteq> containedtype"
    using assms(1) existing_classes type_model.property_enum_disjoint
    by blast
  then show "e \<notin> Class (tmod_contained_class_set_field classtype name containedtype mul) \<and> e \<notin> UserDataType (tmod_contained_class_set_field classtype name containedtype mul)"
    unfolding tmod_contained_class_set_field_def
    by simp
next
  fix x y
  assume x_def: "x \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
  assume "y \<in> Class (tmod_contained_class_set_field classtype name containedtype mul) \<union> Enum (tmod_contained_class_set_field classtype name containedtype mul) \<union> UserDataType (tmod_contained_class_set_field classtype name containedtype mul)"
  then have y_def: "y \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
    unfolding tmod_contained_class_set_field_def
    using existing_classes
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
  then show "irrefl ((Inh Tmod \<union> Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+)"
    unfolding tmod_contained_class_set_field_def
    by simp
next
  have inh_wellformed_classes: "\<And>c. c \<in> Inh (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul)) \<Longrightarrow> 
    fst c \<in> Class (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul)) \<and> snd c \<in> Class (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul))"
  proof
    fix c
    assume "c \<in> Inh (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul))"
    then have c_def: "c \<in> Inh Tmod"
      unfolding tmod_combine_def tmod_contained_class_set_field_def
      by simp
    have "fst c \<in> Class Tmod"
      using c_def assms(1) type_model.structure_inh_wellformed_fst_class
      by blast
    then show "fst c \<in> Class (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul))"
      unfolding tmod_combine_def
      by simp
    have "snd c \<in> Class Tmod"
      using c_def assms(1) type_model.structure_inh_wellformed_snd_class
      by blast
    then show "snd c \<in> Class (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul))"
      unfolding tmod_combine_def
      by simp
  qed
  fix c1 c2 A B
  assume "identity c1 A \<in> tmod_combine_prop Tmod (tmod_contained_class_set_field classtype name containedtype mul)"
  then have "identity c1 A \<in> Prop Tmod"
  proof (cases)
    case identity_property_tmod1
    then show ?thesis
      by blast
  next
    case identity_property_tmod2
    then show ?thesis
      unfolding tmod_contained_class_set_field_def
      by simp
  next
    case identity_property_both
    then show ?thesis
      unfolding tmod_contained_class_set_field_def
      by simp
  qed
  assume "identity c2 B \<in> tmod_combine_prop Tmod (tmod_contained_class_set_field classtype name containedtype mul)"
  then have "identity c2 B \<in> Prop Tmod"
  proof (cases)
    case identity_property_tmod1
    then show ?thesis
      by blast
  next
    case identity_property_tmod2
    then show ?thesis
      unfolding tmod_contained_class_set_field_def
      by simp
  next
    case identity_property_both
    then show ?thesis
      unfolding tmod_contained_class_set_field_def
      by simp
  qed
  assume c1_c2_neq: "c1 \<noteq> c2"
  assume not_extend_tmod: "\<not>\<exclamdown>c1 \<sqsubseteq>[Tmod] \<exclamdown>c2"
  assume "\<exclamdown>c1 \<sqsubseteq>[tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul)] \<exclamdown>c2"
  then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_rel_altdef (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul))"
    unfolding subtype_def
    using inh_wellformed_classes subtype_rel_alt
    by blast
  then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_tuple ` Type (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union> 
    subtype_conv proper proper ` (Inh (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_rel_altdef Tmod"
  proof (elim UnE)
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_tuple ` Type (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul))"
    then have "c1 = c2"
      unfolding subtype_tuple_def
      by blast
    then show ?thesis
      using c1_c2_neq
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper proper ` (Inh (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      unfolding tmod_combine_def tmod_contained_class_set_field_def
      by simp
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` (Inh (tmod_combine Tmod (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
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
qed (simp_all add: assms tmod_contained_class_set_field_def)



section "Encoding of a class-typed field as edge type in GROOVE"

definition tg_contained_class_set_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> multiplicity \<Rightarrow> ('t list) type_graph" where
  "tg_contained_class_set_field_as_edge_type classtype name containedtype mul = \<lparr>
    NT = {type (id_to_list classtype), type (id_to_list containedtype)},
    ET = {(type (id_to_list classtype), edge [name], type (id_to_list containedtype))},
    inh = {(type (id_to_list classtype), type (id_to_list classtype)), (type (id_to_list containedtype), type (id_to_list containedtype))},
    abs = {},
    mult = (\<lambda>x. if x = (type (id_to_list classtype), edge [name], type (id_to_list containedtype)) then (\<^bold>0..\<^bold>1, mul) else undefined),
    contains = {(type (id_to_list classtype), edge [name], type (id_to_list containedtype))}
  \<rparr>"

lemma tg_contained_class_set_field_as_edge_type_correct:
  assumes valid_mul: "multiplicity mul"
  shows "type_graph (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)"
proof (intro type_graph.intro)
  fix n
  assume "n \<in> NT (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)"
  then have "n = type (id_to_list classtype) \<or> n = type (id_to_list containedtype)"
    unfolding tg_contained_class_set_field_as_edge_type_def
    by simp
  then show "n \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
    using Lab\<^sub>t.rule_type_labels
    by fastforce
next
  fix s l t
  assume "(s, l, t) \<in> ET (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)"
  then have "(s, l, t) = (type (id_to_list classtype), edge [name], type (id_to_list containedtype))"
    unfolding tg_contained_class_set_field_as_edge_type_def
    by simp
  then have "s \<in> {type (id_to_list classtype), type (id_to_list containedtype)} \<and> l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> {type (id_to_list classtype), type (id_to_list containedtype)}"
  proof (intro conjI)
    assume "(s, l, t) = (type (id_to_list classtype), edge [name], type (id_to_list containedtype))"
    then show "l \<in> Lab\<^sub>e \<union> Lab\<^sub>f"
      using Lab\<^sub>e.rule_edge_labels
      by fastforce
  qed (simp_all)
  then show "s \<in> NT (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) \<and> l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> NT (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)"
    unfolding tg_contained_class_set_field_as_edge_type_def
    by simp
next
  show "Relation.Field (inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)) = NT (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)"
    unfolding Relation.Field_def tg_contained_class_set_field_as_edge_type_def
    by simp
next
  fix e
  assume "e \<in> ET (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)"
  then have "mult (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) e = (\<^bold>0..\<^bold>1, mul)"
    unfolding tg_contained_class_set_field_as_edge_type_def
    by simp
  then show "multiplicity_pair (mult (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) e)"
  proof (intro multiplicity_pair.intro)
    assume mult_e_def: "mult (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) e = (\<^bold>0..\<^bold>1, mul)"
    show "multiplicity (m_in (mult (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) e))"
      using mult_e_def
      by (intro multiplicity.intro) (simp_all)
    show "multiplicity (m_out (mult (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) e))"
      using valid_mul mult_e_def
      by simp
  qed
next
  show "Partial_order (inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))"
    unfolding tg_contained_class_set_field_as_edge_type_def partial_order_on_def preorder_on_def refl_on_def antisym_def trans_def
    by simp
qed (simp_all add: tg_contained_class_set_field_as_edge_type_def)

lemma tg_contained_class_set_field_as_edge_type_combine_correct:
  assumes "type_graph TG"
  assumes existing_node_types: "{type (id_to_list classtype), type (id_to_list containedtype)} \<subseteq> NT TG"
  assumes new_edge_type: "\<And>s l t. (s, type (id_to_list classtype)) \<in> inh TG \<or> (type (id_to_list classtype), s) \<in> inh TG \<Longrightarrow> l = edge [name] \<Longrightarrow> (s, l, t) \<notin> ET TG"
  assumes valid_mul: "multiplicity mul"
  shows "type_graph (tg_combine TG (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))"
proof (intro tg_combine_merge_correct)
  show "type_graph (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)"
    using valid_mul
    by (fact tg_contained_class_set_field_as_edge_type_correct)
next
  show "ET TG \<inter> ET (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) = {}"
    unfolding tg_contained_class_set_field_as_edge_type_def
    using assms(1) existing_node_types new_edge_type type_graph.validity_inh_node
    by fastforce
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume e2_def: "(s2, l, t2) \<in> ET TG"
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+ - inh TG \<or> (s2, s1) \<in> (inh TG \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+ - inh TG"
  then have "(s1, s2) \<in> (inh TG)\<^sup>+ - inh TG \<or> (s2, s1) \<in> (inh TG)\<^sup>+ - inh TG"
    using Un_absorb2 assms(1) type_graph.validity_inh_node existing_node_types insert_subset sup.orderI sup_bot.right_neutral tg_contained_class_set_field_as_edge_type_def type_graph.simps(3)
    by metis
  then have src_inh: "(s1, s2) \<in> inh TG - inh TG \<or> (s2, s1) \<in> inh TG - inh TG"
    by (simp add: assms(1) type_graph.validity_inh_trans)
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+ \<or> (t2, t1) \<in> (inh TG \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+"
  show "s1 = s2 \<and> t1 = t2"
    using src_inh
    by blast
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume e2_def: "(s2, l, t2) \<in> ET TG"
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+ \<or> (s2, s1) \<in> (inh TG \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+"
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+ - inh TG \<or> (t2, t1) \<in> (inh TG \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+ - inh TG"
  then have "(t1, t2) \<in> (inh TG)\<^sup>+ - inh TG \<or> (t2, t1) \<in> (inh TG)\<^sup>+ - inh TG"
    using Un_absorb2 assms(1) type_graph.validity_inh_node existing_node_types insert_subset sup.orderI sup_bot.right_neutral tg_contained_class_set_field_as_edge_type_def type_graph.simps(3)
    by metis
  then have tgt_inh: "(t1, t2) \<in> inh TG - inh TG \<or> (t2, t1) \<in> inh TG - inh TG"
    by (simp add: assms(1) type_graph.validity_inh_trans)
  show "s1 = s2 \<and> t1 = t2"
    using tgt_inh
    by blast
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume "(s2, l, t2) \<in> ET (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)"
  then have e2_def: "(s2, l, t2) = (type (id_to_list classtype), edge [name], type (id_to_list containedtype))"
    unfolding tg_contained_class_set_field_as_edge_type_def
    by simp
  then have l_def: "l = edge [name]"
    by blast
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+ \<or> (s2, s1) \<in> (inh TG \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+"
  then have "(s1, s2) \<in> (inh TG)\<^sup>+ \<or> (s2, s1) \<in> (inh TG)\<^sup>+"
    using Un_absorb2 assms(1) type_graph.validity_inh_node existing_node_types insert_subset sup.orderI sup_bot.right_neutral tg_contained_class_set_field_as_edge_type_def type_graph.simps(3)
    by metis
  then have src_inh: "(s1, s2) \<in> inh TG \<or> (s2, s1) \<in> inh TG"
    by (simp add: assms(1) type_graph.validity_inh_trans)
  then show "s1 = s2 \<and> t1 = t2"
    using e1_def e2_def new_edge_type
    by simp
next
  have "antisym ((inh TG)\<^sup>+)"
    by (simp add: assms(1) type_graph.validity_inh_antisym type_graph.validity_inh_trans)
  then show "antisym ((inh TG \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+)"
    using Un_absorb2 assms(1) type_graph.validity_inh_node existing_node_types insert_subset sup.orderI sup_bot.right_neutral tg_contained_class_set_field_as_edge_type_def type_graph.simps(3)
    by metis
qed (simp_all add: tg_contained_class_set_field_as_edge_type_def assms)


subsection "Transformation functions"

definition tmod_contained_class_set_field_to_tg_contained_class_set_field_as_edge_type :: "'t Id \<Rightarrow> multiplicity \<Rightarrow> 't type_model \<Rightarrow> ('t list) type_graph" where
  "tmod_contained_class_set_field_to_tg_contained_class_set_field_as_edge_type containedtype mul Tmod = \<lparr>
    NT = type ` id_to_list ` Class Tmod,
    ET = (\<lambda>x. (type (id_to_list (fst x)), edge [(snd x)], type (id_to_list containedtype))) ` Field Tmod,
    inh = (\<lambda>x. (x, x)) ` type ` id_to_list ` Class Tmod,
    abs = {},
    mult = (\<lambda>x. if x \<in> (\<lambda>x. (type (id_to_list (fst x)), edge [(snd x)], type (id_to_list containedtype))) ` Field Tmod then (\<^bold>0..\<^bold>1, mul) else undefined),
    contains = (\<lambda>x. (type (id_to_list (fst x)), edge [(snd x)], type (id_to_list containedtype))) ` Field Tmod
  \<rparr>"

lemma tmod_contained_class_set_field_to_tg_contained_class_set_field_as_edge_type_proj:
  shows "tmod_contained_class_set_field_to_tg_contained_class_set_field_as_edge_type containedtype mul (tmod_contained_class_set_field classtype name containedtype mul) = 
    tg_contained_class_set_field_as_edge_type classtype name containedtype mul"
  unfolding tmod_contained_class_set_field_to_tg_contained_class_set_field_as_edge_type_def tmod_contained_class_set_field_def tg_contained_class_set_field_as_edge_type_def
  by simp

lemma tmod_contained_class_set_field_to_tg_contained_class_set_field_as_edge_type_func:
  shows "tg_combine_mapping_function (tmod_contained_class_set_field_to_tg_contained_class_set_field_as_edge_type containedtype mul) 
    (tmod_contained_class_set_field classtype name containedtype mul) (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)"
  by (intro tg_combine_mapping_function.intro)
    (simp_all add: tmod_contained_class_set_field_to_tg_contained_class_set_field_as_edge_type_def tmod_contained_class_set_field_def tg_contained_class_set_field_as_edge_type_def tmod_combine_def)

definition tg_contained_class_set_field_as_edge_type_to_tmod_contained_class_set_field :: "'t Id \<Rightarrow> multiplicity \<Rightarrow> ('t list) type_graph \<Rightarrow> 't type_model" where
  "tg_contained_class_set_field_as_edge_type_to_tmod_contained_class_set_field containedtype mul TG = \<lparr>
    Class = list_to_id ` unlabel ` NT TG,
    Enum = {},
    UserDataType = {},
    Field = (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET TG,
    FieldSig = (\<lambda>x. if x \<in> (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET TG then (setof \<exclamdown>containedtype, mul) else undefined),
    EnumValue = {},
    Inh = {},
    Prop = containment ` (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET TG,
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tg_contained_class_set_field_as_edge_type_to_tmod_contained_class_set_field_proj:
  shows "tg_contained_class_set_field_as_edge_type_to_tmod_contained_class_set_field containedtype mul (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) = 
    tmod_contained_class_set_field classtype name containedtype mul"
  unfolding tg_contained_class_set_field_as_edge_type_to_tmod_contained_class_set_field_def tmod_contained_class_set_field_def tg_contained_class_set_field_as_edge_type_def
  by (simp add: id_to_list_inverse)

lemma tg_contained_class_set_field_as_edge_type_to_tmod_contained_class_set_field_func:
  shows "tmod_combine_mapping_function (tg_contained_class_set_field_as_edge_type_to_tmod_contained_class_set_field containedtype mul) 
    (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) (tmod_contained_class_set_field classtype name containedtype mul)"
  by (intro tmod_combine_mapping_function.intro)
    (simp_all add: tg_contained_class_set_field_as_edge_type_to_tmod_contained_class_set_field_def tmod_contained_class_set_field_def tg_contained_class_set_field_as_edge_type_def tg_combine_def id_to_list_inverse)

end