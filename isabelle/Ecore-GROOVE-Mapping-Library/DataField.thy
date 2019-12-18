theory DataField
  imports
    Main
    "Ecore-GROOVE-Mapping.Type_Model_Graph_Mapping"
    "Ecore-GROOVE-Mapping.Identifier_List"
begin

section "Definition of a type model which introduces a field typed by a data type."

definition tmod_data_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't TypeDef \<Rightarrow> 't type_model" where
  "tmod_data_field classtype name fieldtype = \<lparr>
    Class = {classtype},
    Enum = {},
    UserDataType = {},
    Field = {(classtype, name)},
    FieldSig = (\<lambda>x. if x = (classtype, name) then (fieldtype, \<^bold>1..\<^bold>1) else undefined),
    EnumValue = {},
    Inh = {},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tmod_data_field_correct: 
  assumes fieldtype_is_datatype: "fieldtype \<in> DataType"
  shows "type_model (tmod_data_field classtype name fieldtype)"
proof (intro type_model.intro)
  fix f
  assume "f \<in> Field (tmod_data_field classtype name fieldtype)"
  then have "f = (classtype, name)"
    unfolding tmod_data_field_def
    by simp
  then have "FieldSig (tmod_data_field classtype name fieldtype) f = (fieldtype, \<^bold>1..\<^bold>1)"
    unfolding tmod_data_field_def
    by simp
  then show "fst (FieldSig (tmod_data_field classtype name fieldtype) f) \<in> Type (tmod_data_field classtype name fieldtype) \<and> 
    multiplicity (snd (FieldSig (tmod_data_field classtype name fieldtype) f))"
  proof (intro conjI)
    assume "FieldSig (tmod_data_field classtype name fieldtype) f = (fieldtype, \<^bold>1..\<^bold>1)"
    then have "fst (FieldSig (tmod_data_field classtype name fieldtype) f) = fieldtype"
      by simp
    then show "fst (FieldSig (tmod_data_field classtype name fieldtype) f) \<in> Type (tmod_data_field classtype name fieldtype)"
      unfolding Type_def NonContainerType_def
      by (simp add: fieldtype_is_datatype)
  next
    assume "FieldSig (tmod_data_field classtype name fieldtype) f = (fieldtype, \<^bold>1..\<^bold>1)"
    then have snd_def: "snd (FieldSig (tmod_data_field classtype name fieldtype) f) = \<^bold>1..\<^bold>1"
      by simp
    then show "multiplicity (snd (FieldSig (tmod_data_field classtype name fieldtype) f))"
      by (intro multiplicity.intro) (simp_all)
  qed
next
  have "asym {} \<and> irrefl {}"
    by (simp add: asym.intros irrefl_def)
  then show "asym (Inh (tmod_data_field classtype name fieldtype)) \<and> irrefl ((Inh (tmod_data_field classtype name fieldtype))\<^sup>+)"
    unfolding tmod_data_field_def
    by simp
next
  fix f
  assume "f \<in> Field (tmod_data_field classtype name fieldtype) \<and> 
    Type_Model.type (tmod_data_field classtype name fieldtype) f \<in> DataType \<union> 
      EnumType (tmod_data_field classtype name fieldtype) \<union> 
      UserDataTypeType (tmod_data_field classtype name fieldtype) \<union> 
      ProperClassType (tmod_data_field classtype name fieldtype)"
  then have "f = (classtype, name)"
    unfolding tmod_data_field_def
    by simp
  then show "lower (tmod_data_field classtype name fieldtype) f = \<^bold>1"
    unfolding lower_def tmod_data_field_def
    by simp
next
  fix f
  assume assump: "f \<in> Field (tmod_data_field classtype name fieldtype) \<and> 
    Type_Model.type (tmod_data_field classtype name fieldtype) f \<in> NullableClassType (tmod_data_field classtype name fieldtype)"
  then have "f = (classtype, name)"
    unfolding tmod_data_field_def
    by simp
  then have "Type_Model.type (tmod_data_field classtype name fieldtype) f = fieldtype"
    unfolding Type_Model.type_def tmod_data_field_def
    by simp
  then have "Type_Model.type (tmod_data_field classtype name fieldtype) f \<in> DataType"
    using fieldtype_is_datatype
    by simp
  then show "lower (tmod_data_field classtype name fieldtype) f = \<^bold>0"
    using assump nullable_class_type_datatype_intersect
    by blast
next
  fix f
  assume "f \<in> Field (tmod_data_field classtype name fieldtype) \<and> 
    Type_Model.type (tmod_data_field classtype name fieldtype) f \<in> NonContainerType (tmod_data_field classtype name fieldtype)"
  then have "f = (classtype, name)"
    unfolding tmod_data_field_def
    by simp
  then show "upper (tmod_data_field classtype name fieldtype) f = \<^bold>1"
    unfolding upper_def tmod_data_field_def
    by simp
qed (simp_all add: tmod_data_field_def)

lemma tmod_data_field_combine_correct:
  assumes "type_model Tmod"
  assumes fieldtype_is_datatype: "fieldtype \<in> DataType"
  assumes existing_class: "classtype \<in> Class Tmod"
  assumes new_field: "(classtype, name) \<notin> Field Tmod"
  shows "type_model (tmod_combine Tmod (tmod_data_field classtype name fieldtype))"
proof (intro tmod_combine_merge_correct)
  show "type_model (tmod_data_field classtype name fieldtype)"
    using fieldtype_is_datatype
    by (fact tmod_data_field_correct)
next
  fix c
  assume "c \<in> Class (tmod_data_field classtype name fieldtype)"
  then have "c \<in> Class Tmod"
    unfolding tmod_data_field_def
    by (simp add: existing_class)
  then show "c \<notin> Enum Tmod \<and> c \<notin> UserDataType Tmod"
    using assms(1) type_model.property_class_disjoint
    by blast
next
  fix e
  assume "e \<in> Enum Tmod"
  then have "e \<noteq> classtype"
    using assms(1) existing_class type_model.property_enum_disjoint
    by blast
  then show "e \<notin> Class (tmod_data_field classtype name fieldtype) \<and> e \<notin> UserDataType (tmod_data_field classtype name fieldtype)"
    unfolding tmod_data_field_def
    by simp
next
  fix x y
  assume x_def: "x \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
  assume "y \<in> Class (tmod_data_field classtype name fieldtype) \<union> Enum (tmod_data_field classtype name fieldtype) \<union> UserDataType (tmod_data_field classtype name fieldtype)"
  then have y_def: "y \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
    unfolding tmod_data_field_def
    using existing_class
    by simp
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
  then show "irrefl ((Inh Tmod \<union> Inh (tmod_data_field classtype name fieldtype))\<^sup>+)"
    unfolding tmod_data_field_def
    by simp
next
  have inh_wellformed_classes: "\<And>c. c \<in> Inh (tmod_combine Tmod (tmod_data_field classtype name fieldtype)) \<Longrightarrow> 
    fst c \<in> Class (tmod_combine Tmod (tmod_data_field classtype name fieldtype)) \<and> snd c \<in> Class (tmod_combine Tmod (tmod_data_field classtype name fieldtype))"
  proof
    fix c
    assume "c \<in> Inh (tmod_combine Tmod (tmod_data_field classtype name fieldtype))"
    then have c_def: "c \<in> Inh Tmod"
      unfolding tmod_combine_def tmod_data_field_def
      by simp
    have "fst c \<in> Class Tmod"
      using c_def assms(1) type_model.structure_inh_wellformed_fst_class
      by blast
    then show "fst c \<in> Class (tmod_combine Tmod (tmod_data_field classtype name fieldtype))"
      unfolding tmod_combine_def
      by simp
    have "snd c \<in> Class Tmod"
      using c_def assms(1) type_model.structure_inh_wellformed_snd_class
      by blast
    then show "snd c \<in> Class (tmod_combine Tmod (tmod_data_field classtype name fieldtype))"
      unfolding tmod_combine_def
      by simp
  qed
  fix c1 c2 A B
  assume "identity c1 A \<in> tmod_combine_prop Tmod (tmod_data_field classtype name fieldtype)"
  then have "identity c1 A \<in> Prop Tmod"
  proof (cases)
    case identity_property_tmod1
    then show ?thesis
      by blast
  next
    case identity_property_tmod2
    then show ?thesis
      unfolding tmod_data_field_def
      by simp
  next
    case identity_property_both
    then show ?thesis
      unfolding tmod_data_field_def
      by simp
  qed
  assume "identity c2 B \<in> tmod_combine_prop Tmod (tmod_data_field classtype name fieldtype)"
  then have "identity c2 B \<in> Prop Tmod"
  proof (cases)
    case identity_property_tmod1
    then show ?thesis
      by blast
  next
    case identity_property_tmod2
    then show ?thesis
      unfolding tmod_data_field_def
      by simp
  next
    case identity_property_both
    then show ?thesis
      unfolding tmod_data_field_def
      by simp
  qed
  assume c1_c2_neq: "c1 \<noteq> c2"
  assume not_extend_tmod: "\<not>\<exclamdown>c1 \<sqsubseteq>[Tmod] \<exclamdown>c2"
  assume "\<exclamdown>c1 \<sqsubseteq>[tmod_combine Tmod (tmod_data_field classtype name fieldtype)] \<exclamdown>c2"
  then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_rel_altdef (tmod_combine Tmod (tmod_data_field classtype name fieldtype))"
    unfolding subtype_def
    using inh_wellformed_classes subtype_rel_alt
    by blast
  then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_tuple ` Type (tmod_combine Tmod (tmod_data_field classtype name fieldtype)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine Tmod (tmod_data_field classtype name fieldtype)))\<^sup>+ \<union> 
    subtype_conv proper proper ` (Inh (tmod_combine Tmod (tmod_data_field classtype name fieldtype)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine Tmod (tmod_data_field classtype name fieldtype)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine Tmod (tmod_data_field classtype name fieldtype)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_rel_altdef Tmod"
  proof (elim UnE)
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_tuple ` Type (tmod_combine Tmod (tmod_data_field classtype name fieldtype))"
    then have "c1 = c2"
      unfolding subtype_tuple_def
      by blast
    then show ?thesis
      using c1_c2_neq
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine Tmod (tmod_data_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper proper ` (Inh (tmod_combine Tmod (tmod_data_field classtype name fieldtype)))\<^sup>+"
    then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      unfolding tmod_combine_def tmod_data_field_def
      by simp
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine Tmod (tmod_data_field classtype name fieldtype))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` (Inh (tmod_combine Tmod (tmod_data_field classtype name fieldtype)))\<^sup>+"
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
qed (simp_all add: assms tmod_data_field_def)



section "Encoding of a string-typed field as edge type in GROOVE"

fun datatype_to_labdef :: "'t TypeDef \<Rightarrow> ('t list) LabDef" where
  "datatype_to_labdef TypeDef.boolean = LabDef.bool" |
  "datatype_to_labdef TypeDef.integer = LabDef.int" |
  "datatype_to_labdef TypeDef.real = LabDef.real" |
  "datatype_to_labdef TypeDef.string = LabDef.string" |
  "datatype_to_labdef _ = undefined"

fun labdef_to_datatype :: "('t list) LabDef \<Rightarrow> 't TypeDef" where
  "labdef_to_datatype LabDef.bool = TypeDef.boolean" |
  "labdef_to_datatype LabDef.int = TypeDef.integer" |
  "labdef_to_datatype LabDef.real = TypeDef.real" |
  "labdef_to_datatype LabDef.string = TypeDef.string" |
  "labdef_to_datatype _ = undefined"

definition tg_data_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't TypeDef \<Rightarrow> ('t list) type_graph" where
  "tg_data_field_as_edge_type classtype name fieldtype = \<lparr>
    NT = {type (id_to_list classtype), datatype_to_labdef fieldtype},
    ET = {(type (id_to_list classtype), edge [name], datatype_to_labdef fieldtype)},
    inh = {(type (id_to_list classtype), type (id_to_list classtype)), (datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)},
    abs = {},
    mult = (\<lambda>x. if x = (type (id_to_list classtype), edge [name], datatype_to_labdef fieldtype) then (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1) else undefined),
    contains = {}
  \<rparr>"

lemma tg_data_field_as_edge_type_correct:
  assumes fieldtype_is_datatype: "fieldtype \<in> DataType"
  shows "type_graph (tg_data_field_as_edge_type classtype name fieldtype)"
proof (intro type_graph.intro)
  fix n
  assume "n \<in> NT (tg_data_field_as_edge_type classtype name fieldtype)"
  then have "n = type (id_to_list classtype) \<or> n = datatype_to_labdef fieldtype"
    unfolding tg_data_field_as_edge_type_def
    by simp
  then have "n = type (id_to_list classtype) \<or> n = bool \<or> n = int \<or> n = real \<or> n = string"
    using fieldtype_is_datatype
    unfolding DataType_def
    by fastforce
  then show "n \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
    using Lab\<^sub>p_def Lab\<^sub>t.rule_type_labels
    by fastforce
next
  fix s l t
  assume "(s, l, t) \<in> ET (tg_data_field_as_edge_type classtype name fieldtype)"
  then have "(s, l, t) = (type (id_to_list classtype), edge [name], datatype_to_labdef fieldtype)"
    unfolding tg_data_field_as_edge_type_def
    by simp
  then have "s \<in> {type (id_to_list classtype), datatype_to_labdef fieldtype} \<and> l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> {type (id_to_list classtype), datatype_to_labdef fieldtype}"
  proof (intro conjI)
    assume "(s, l, t) = (type (id_to_list classtype), edge [name], datatype_to_labdef fieldtype)"
    then show "l \<in> Lab\<^sub>e \<union> Lab\<^sub>f"
      using Lab\<^sub>e.rule_edge_labels
      by fastforce
  qed (simp_all)
  then show "s \<in> NT (tg_data_field_as_edge_type classtype name fieldtype) \<and> l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> NT (tg_data_field_as_edge_type classtype name fieldtype)"
    unfolding tg_data_field_as_edge_type_def
    by simp
next
  show "Relation.Field (inh (tg_data_field_as_edge_type classtype name fieldtype)) = NT (tg_data_field_as_edge_type classtype name fieldtype)"
    unfolding Relation.Field_def tg_data_field_as_edge_type_def
    by simp
next
  fix e
  assume "e \<in> ET (tg_data_field_as_edge_type classtype name fieldtype)"
  then have "mult (tg_data_field_as_edge_type classtype name fieldtype) e = (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1)"
    unfolding tg_data_field_as_edge_type_def
    by simp
  then show "multiplicity_pair (mult (tg_data_field_as_edge_type classtype name fieldtype) e)"
  proof (intro multiplicity_pair.intro)
    assume mult_e_def: "mult (tg_data_field_as_edge_type classtype name fieldtype) e = (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1)"
    show "multiplicity (m_in (mult (tg_data_field_as_edge_type classtype name fieldtype) e))"
      using mult_e_def
      by (intro multiplicity.intro) (simp_all)
    show "multiplicity (m_out (mult (tg_data_field_as_edge_type classtype name fieldtype) e))"
      using mult_e_def
      by (intro multiplicity.intro) (simp_all)
  qed
next
  show "Partial_order (inh (tg_data_field_as_edge_type classtype name fieldtype))"
    unfolding tg_data_field_as_edge_type_def partial_order_on_def preorder_on_def refl_on_def antisym_def trans_def
    by simp
qed (simp_all add: tg_data_field_as_edge_type_def)

lemma tg_data_field_as_edge_type_combine_inh:
  assumes "type_graph TG"
  assumes fieldtype_is_datatype: "fieldtype \<in> DataType"
  assumes existing_node_type: "type (id_to_list classtype) \<in> NT TG"
  shows "(inh TG \<union> {(type (id_to_list classtype), type (id_to_list classtype)), (datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)})\<^sup>+ = 
    inh TG \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
proof
  show "(inh TG \<union> {(type (id_to_list classtype), type (id_to_list classtype)), (datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)})\<^sup>+ \<subseteq> 
    inh TG \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
  proof
    fix x
    assume "x \<in> (inh TG \<union> {(type (id_to_list classtype), type (id_to_list classtype)), (datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)})\<^sup>+"
    then show "x \<in> inh TG \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
    proof (induct x)
      case (Pair a b)
      then show ?case
      proof (induct)
        case (base y)
        then show ?case
          using assms(1) existing_node_type type_graph.validity_inh_node
          by fastforce
      next
        case (step y z)
        then show ?case
        proof (induct "datatype_to_labdef fieldtype \<in> NT TG")
          case True
          then have ay_def: "(a, y) \<in> inh TG"
            using assms(1) type_graph.validity_inh_node
            by fastforce
          have "(y, z) \<in> inh TG"
            using True.hyps assms(1) existing_node_type step.hyps(2) type_graph.validity_inh_node
            by fastforce
          then have "(a, z) \<in> inh TG"
            using assms(1) ay_def r_r_into_trancl type_graph.validity_inh_trans
            by fastforce
          then show ?case
            by simp
        next
          case False
          show ?case
            using step.hyps(3)
          proof (elim UnE)
            assume ay_def: "(a, y) \<in> inh TG"
            then have "y \<noteq> datatype_to_labdef fieldtype"
              using False.hyps assms(1) type_graph.structure_inheritance_wellformed_second_node
              by blast
            then have "(y, z) \<in> inh TG"
              using assms(1) existing_node_type step.hyps(2) type_graph.validity_inh_node
              by fastforce
            then have "(a, z) \<in> inh TG"
              using assms(1) ay_def r_r_into_trancl type_graph.validity_inh_trans
              by fastforce
            then show ?case
              by simp
          next
            assume "(a, y) \<in> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
            then have "(a, y) = (datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)"
              by simp
            then have "y = datatype_to_labdef fieldtype"
              by simp
            then have "(y, z) = (datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)"
              using False.hyps assms(1) step.hyps(2) type_graph.structure_inheritance_wellformed_first_node
              by fastforce
            then show ?case
              using step.hyps(3)
              by blast
          qed
        qed
      qed
    qed
  qed
next
  show "inh TG \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)} \<subseteq> 
    (inh TG \<union> {(type (id_to_list classtype), type (id_to_list classtype)), (datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)})\<^sup>+"
    by fastforce
qed

lemma tg_data_field_as_edge_type_combine_correct:
  assumes "type_graph TG"
  assumes fieldtype_is_datatype: "fieldtype \<in> DataType"
  assumes existing_node_type: "type (id_to_list classtype) \<in> NT TG"
  assumes new_edge_type: "\<And>s l t. (s, type (id_to_list classtype)) \<in> inh TG \<or> (type (id_to_list classtype), s) \<in> inh TG \<Longrightarrow> l = edge [name] \<Longrightarrow> (s, l, t) \<notin> ET TG"
  shows "type_graph (tg_combine TG (tg_data_field_as_edge_type classtype name fieldtype))"
proof (intro tg_combine_merge_correct)
  show "type_graph (tg_data_field_as_edge_type classtype name fieldtype)"
    using fieldtype_is_datatype
    by (fact tg_data_field_as_edge_type_correct)
next
  show "ET TG \<inter> ET (tg_data_field_as_edge_type classtype name fieldtype) = {}"
    unfolding tg_data_field_as_edge_type_def
    by (simp add: assms(1) existing_node_type new_edge_type type_graph.validity_inh_node)
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume e2_def: "(s2, l, t2) \<in> ET TG"
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+ - inh TG \<or> (s2, s1) \<in> (inh TG \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+ - inh TG"
  then have src_inh: "(s1, s2) \<in> inh TG \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)} - inh TG \<or> 
    (s2, s1) \<in> inh TG \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)} - inh TG"
    using assms(1) existing_node_type fieldtype_is_datatype tg_data_field_as_edge_type_combine_inh tg_data_field_as_edge_type_def type_graph.simps(3)
    by metis
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+ \<or> (t2, t1) \<in> (inh TG \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+"
  show "s1 = s2 \<and> t1 = t2"
    using assms(1) e1_def src_inh type_graph.structure_edges_wellformed type_graph.validity_inh_node
    by fastforce
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume e2_def: "(s2, l, t2) \<in> ET TG"
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+ \<or> (s2, s1) \<in> (inh TG \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+"
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+ - inh TG \<or> (t2, t1) \<in> (inh TG \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+ - inh TG"
  then have src_inh: "(t1, t2) \<in> inh TG \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)} - inh TG \<or> (t2, t1) \<in> inh TG \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)} - inh TG"
    using assms(1) existing_node_type fieldtype_is_datatype tg_data_field_as_edge_type_combine_inh tg_data_field_as_edge_type_def type_graph.simps(3)
    by metis
  show "s1 = s2 \<and> t1 = t2"
    using assms(1) e1_def src_inh type_graph.structure_edges_wellformed type_graph.validity_inh_node
    by fastforce
next
  fix l s1 t1 s2 t2
  assume e1_def: "(s1, l, t1) \<in> ET TG"
  assume "(s2, l, t2) \<in> ET (tg_data_field_as_edge_type classtype name fieldtype)"
  then have e2_def: "(s2, l, t2) = (type (id_to_list classtype), edge [name], datatype_to_labdef fieldtype)"
    unfolding tg_data_field_as_edge_type_def
    by simp
  then have l_def: "l = edge [name]"
    by blast
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+ \<or> (s2, s1) \<in> (inh TG \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+"
  then have "(s1, s2) \<in> inh TG \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)} \<or> (s2, s1) \<in> inh TG \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
    using assms(1) existing_node_type fieldtype_is_datatype tg_data_field_as_edge_type_combine_inh tg_data_field_as_edge_type_def type_graph.simps(3)
    by metis
  then have src_inh: "(s1, s2) \<in> inh TG \<or> (s2, s1) \<in> inh TG"
    using e2_def assms(1) existing_node_type refl_onD type_graph.structure_inheritance_wellformed type_graph.validity_inh_refl
    by fastforce
  then show "s1 = s2 \<and> t1 = t2"
    using e1_def e2_def new_edge_type
    by simp
next
  have "antisym (inh TG \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)})"
    using Un_empty_right Un_insert_right antisym_def assms(1) insert_iff pair_in_Id_conv type_graph.validity_inh_antisym
    by metis
  then show "antisym ((inh TG \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+)"
    using assms(1) existing_node_type fieldtype_is_datatype tg_data_field_as_edge_type_combine_inh tg_data_field_as_edge_type_def type_graph.simps(3)
    by metis
qed (simp_all add: tg_data_field_as_edge_type_def assms)


subsection "Transformation functions"

definition tmod_data_field_to_tg_data_field_as_edge_type :: "'t TypeDef \<Rightarrow> 't type_model \<Rightarrow> ('t list) type_graph" where
  "tmod_data_field_to_tg_data_field_as_edge_type fieldtype Tmod = \<lparr>
    NT = type ` id_to_list ` Class Tmod \<union> {datatype_to_labdef fieldtype},
    ET = (\<lambda>x. (type (id_to_list (fst x)), edge [(snd x)], datatype_to_labdef fieldtype)) ` Field Tmod,
    inh = (\<lambda>x. (x, x)) ` type ` id_to_list ` Class Tmod \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)},
    abs = {},
    mult = (\<lambda>x. if x \<in> (\<lambda>x. (type (id_to_list (fst x)), edge [(snd x)], datatype_to_labdef fieldtype)) ` Field Tmod then (\<^bold>0..\<^emph>, \<^bold>1..\<^bold>1) else undefined),
    contains = {}
  \<rparr>"

lemma tmod_data_field_to_tg_data_field_as_edge_type_proj:
  shows "tmod_data_field_to_tg_data_field_as_edge_type fieldtype (tmod_data_field classtype name fieldtype) = tg_data_field_as_edge_type classtype name fieldtype"
  unfolding tmod_data_field_to_tg_data_field_as_edge_type_def tmod_data_field_def tg_data_field_as_edge_type_def
  by auto

lemma tmod_data_field_to_tg_data_field_as_edge_type_func:
  shows "tg_combine_mapping_function (tmod_data_field_to_tg_data_field_as_edge_type fieldtype) (tmod_data_field classtype name fieldtype) (tg_data_field_as_edge_type classtype name fieldtype)"
  by (intro tg_combine_mapping_function.intro)
    (auto simp add: tmod_data_field_to_tg_data_field_as_edge_type_def tmod_data_field_def tg_data_field_as_edge_type_def tmod_combine_def)

definition tg_data_field_as_edge_type_to_tmod_data_field :: "'t TypeDef \<Rightarrow> ('t list) type_graph \<Rightarrow> 't type_model" where
  "tg_data_field_as_edge_type_to_tmod_data_field fieldtype TG = \<lparr>
    Class = list_to_id ` unlabel ` {n \<in> NT TG. n \<in> Lab\<^sub>t},
    Enum = {},
    UserDataType = {},
    Field = (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET TG,
    FieldSig = (\<lambda>x. if x \<in> (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET TG then (fieldtype, \<^bold>1..\<^bold>1) else undefined),
    EnumValue = {},
    Inh = {},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tg_data_field_as_edge_type_to_tmod_data_field_proj:
  assumes fieldtype_is_datatype: "fieldtype \<in> DataType"
  shows "tg_data_field_as_edge_type_to_tmod_data_field fieldtype (tg_data_field_as_edge_type classtype name fieldtype) = tmod_data_field classtype name fieldtype"
proof-
  have "{n. (n = type (id_to_list classtype) \<or> n = datatype_to_labdef fieldtype) \<and> n \<in> Lab\<^sub>t} = {type (id_to_list classtype)}"
  proof
    show "{n. (n = LabDef.type (id_to_list classtype) \<or> n = datatype_to_labdef fieldtype) \<and> n \<in> Lab\<^sub>t} \<subseteq> {LabDef.type (id_to_list classtype)}"
    proof
      fix x
      assume "x \<in> {n. (n = type (id_to_list classtype) \<or> n = datatype_to_labdef fieldtype) \<and> n \<in> Lab\<^sub>t}"
      then show "x \<in> {type (id_to_list classtype)}"
      proof
        assume "(x = LabDef.type (id_to_list classtype) \<or> x = datatype_to_labdef fieldtype) \<and> x \<in> Lab\<^sub>t"
        then show "x \<in> {LabDef.type (id_to_list classtype)}"
          using fieldtype_is_datatype
          unfolding DataType_def
          by fastforce
      qed
    qed
  next
    show "{type (id_to_list classtype)} \<subseteq> {n. (n = type (id_to_list classtype) \<or> n = datatype_to_labdef fieldtype) \<and> n \<in> Lab\<^sub>t}"
    proof
      fix x
      assume "x \<in> {type (id_to_list classtype)}"
      then show "x \<in> {n. (n = type (id_to_list classtype) \<or> n = datatype_to_labdef fieldtype) \<and> n \<in> Lab\<^sub>t}"
        by (simp add: Lab\<^sub>t.rule_type_labels)
    qed
  qed
  then show "tg_data_field_as_edge_type_to_tmod_data_field fieldtype (tg_data_field_as_edge_type classtype name fieldtype) = tmod_data_field classtype name fieldtype"
    unfolding tg_data_field_as_edge_type_to_tmod_data_field_def tmod_data_field_def tg_data_field_as_edge_type_def
    by (simp add: id_to_list_inverse)
qed

lemma tg_data_field_as_edge_type_to_tmod_data_field_func:
  assumes fieldtype_is_datatype: "fieldtype \<in> DataType"
  shows "tmod_combine_mapping_function (tg_data_field_as_edge_type_to_tmod_data_field fieldtype) (tg_data_field_as_edge_type classtype name fieldtype) (tmod_data_field classtype name fieldtype)"
proof (intro tmod_combine_mapping_function.intro)
  show "tg_data_field_as_edge_type_to_tmod_data_field fieldtype (tg_data_field_as_edge_type classtype name fieldtype) = tmod_data_field classtype name fieldtype"
    using fieldtype_is_datatype
    by (fact tg_data_field_as_edge_type_to_tmod_data_field_proj)
next
  fix TGX
  show "Class (tg_data_field_as_edge_type_to_tmod_data_field fieldtype (tg_data_field_as_edge_type classtype name fieldtype)) \<subseteq> 
    Class (tg_data_field_as_edge_type_to_tmod_data_field fieldtype (tg_combine (tg_data_field_as_edge_type classtype name fieldtype) TGX))"
  proof
    fix x
    assume "x \<in> Class (tg_data_field_as_edge_type_to_tmod_data_field fieldtype (tg_data_field_as_edge_type classtype name fieldtype))"
    then show "x \<in> Class (tg_data_field_as_edge_type_to_tmod_data_field fieldtype (tg_combine (tg_data_field_as_edge_type classtype name fieldtype) TGX))"
      unfolding tg_data_field_as_edge_type_to_tmod_data_field_def tmod_data_field_def tg_data_field_as_edge_type_def tg_combine_def
      by fastforce
  qed
qed (simp_all add: tg_data_field_as_edge_type_to_tmod_data_field_def tmod_data_field_def tg_data_field_as_edge_type_def tg_combine_def id_to_list_inverse)

end