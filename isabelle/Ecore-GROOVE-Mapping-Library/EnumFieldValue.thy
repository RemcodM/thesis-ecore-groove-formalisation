theory EnumFieldValue
  imports
    Main
    "Ecore-GROOVE-Mapping.Instance_Model_Graph_Mapping"
    EnumField
begin

section "Definition of an instance model which introduces values for a field typed by an enumeration type"

definition imod_enum_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 't set \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't) instance_model" where
  "imod_enum_field classtype name enumid enumvalues objects obids values = \<lparr>
    Tm = tmod_enum_field classtype name enumid enumvalues,
    Object = objects,
    ObjectClass = (\<lambda>x. if x \<in> objects then classtype else undefined),
    ObjectId = (\<lambda>x. if x \<in> objects then obids x else undefined),
    FieldValue = (\<lambda>x. if fst x \<in> objects \<and> snd x = (classtype, name) then enum (enumid, values (fst x)) else undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_enum_field_correct:
  assumes enum_class_neq: "classtype \<noteq> enumid"
  assumes valid_ns: "\<not>id_in_ns enumid (Identifier classtype) \<and> \<not>id_in_ns classtype (Identifier enumid)"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> o2 \<in> objects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes valid_values: "\<And>ob. ob \<in> objects \<Longrightarrow> values ob \<in> enumvalues"
  shows "instance_model (imod_enum_field classtype name enumid enumvalues objects obids values)"
proof (intro instance_model.intro)
  show "type_model (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
    unfolding imod_enum_field_def
    using tmod_enum_field_correct enum_class_neq valid_ns
    by simp
next
  fix ob f
  assume "ob \<notin> Object (imod_enum_field classtype name enumid enumvalues objects obids values) \<or> 
    f \<notin> type_model.Field (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
  then have "ob \<notin> objects \<or> f \<noteq> (classtype, name)"
    unfolding imod_enum_field_def tmod_enum_field_def
    by simp
  then show "FieldValue (imod_enum_field classtype name enumid enumvalues objects obids values) (ob, f) = undefined"
    unfolding imod_enum_field_def
    by fastforce
next
  fix ob f
  assume "ob \<in> Object (imod_enum_field classtype name enumid enumvalues objects obids values)"
  then have ob_def: "ob \<in> objects"
    unfolding imod_enum_field_def
    by simp
  then have ob_class_def: "ObjectClass (imod_enum_field classtype name enumid enumvalues objects obids values) ob = classtype"
    by (simp add: imod_enum_field_def)
  then have "\<exclamdown>(ObjectClass (imod_enum_field classtype name enumid enumvalues objects obids values) ob) \<in> 
    ProperClassType (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
    by (simp add: ProperClassType.rule_proper_classes imod_enum_field_def tmod_enum_field_def)
  then have ob_type_def: "\<exclamdown>(ObjectClass (imod_enum_field classtype name enumid enumvalues objects obids values) ob) \<in> 
    Type (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  assume "f \<in> type_model.Field (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_enum_field_def tmod_enum_field_def
    by simp
  then have "ObjectClass (imod_enum_field classtype name enumid enumvalues objects obids values) ob = 
    class (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) f"
    unfolding class_def
    by (simp add: ob_class_def)
  then have extend: "\<exclamdown>(ObjectClass (imod_enum_field classtype name enumid enumvalues objects obids values) ob) 
    \<sqsubseteq>[Tm (imod_enum_field classtype name enumid enumvalues objects obids values)] 
    \<exclamdown>(class (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) f)"
    unfolding subtype_def
    using ob_type_def subtype_rel.reflexivity
    by simp
  assume "\<not>\<exclamdown>(ObjectClass (imod_enum_field classtype name enumid enumvalues objects obids values) ob) 
    \<sqsubseteq>[Tm (imod_enum_field classtype name enumid enumvalues objects obids values)] 
    \<exclamdown>(class (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) f)"
  then show "FieldValue (imod_enum_field classtype name enumid enumvalues objects obids values) (ob, f) = unspecified"
    using extend
    by blast
next
  fix ob f
  assume "ob \<in> Object (imod_enum_field classtype name enumid enumvalues objects obids values)"
  then have ob_def: "ob \<in> objects"
    unfolding imod_enum_field_def
    by simp
  assume "f \<in> type_model.Field (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_enum_field_def tmod_enum_field_def
    by simp
  then have f_type: "Type_Model.type (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) f = enumtype enumid"
    unfolding Type_Model.type_def imod_enum_field_def tmod_enum_field_def
    by simp
  have f_lower: "lower (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) f = \<^bold>1"
    unfolding lower_def imod_enum_field_def tmod_enum_field_def
    using f_def
    by simp
  have f_upper: "upper (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) f = \<^bold>1"
    unfolding upper_def imod_enum_field_def tmod_enum_field_def
    using f_def
    by simp
  have value_def: "FieldValue (imod_enum_field classtype name enumid enumvalues objects obids values) (ob, f) = enum (enumid, values ob)"
    unfolding imod_enum_field_def
    using f_def ob_def
    by simp
  then have value_valid: "enum (enumid, values ob) :[imod_enum_field classtype name enumid enumvalues objects obids values] enumtype enumid"
    unfolding Valid_def
  proof (intro Valid_rel.valid_rule_enumvalues)
    show "(enumid, values ob) \<in> EnumValue (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
      unfolding imod_enum_field_def tmod_enum_field_def
      by (simp add: ob_def valid_values)
  next
    show "enumtype enumid \<in> EnumType (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
      unfolding imod_enum_field_def tmod_enum_field_def
      by (simp add: EnumType.rule_enum_types)
  qed
  then show "FieldValue (imod_enum_field classtype name enumid enumvalues objects obids values) (ob, f) 
    :[imod_enum_field classtype name enumid enumvalues objects obids values] 
    Type_Model.type (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) f"
    using value_def f_type
    by simp
  have values_are_literal_values: "enum (enumid, values ob) \<in> EnumValueValue (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
    using value_valid
    unfolding Valid_def
  proof (cases)
    case valid_rule_enumvalues
    then show ?thesis
      by (simp add: EnumValueValue.rule_enumvalue)
  qed (simp_all)
  then show "FieldValue (imod_enum_field classtype name enumid enumvalues objects obids values) (ob, f) \<in>
    Value (imod_enum_field classtype name enumid enumvalues objects obids values)"
    unfolding Value_def AtomValue_def
    by (simp add: value_def)
  have "validMul (imod_enum_field classtype name enumid enumvalues objects obids values) ((ob, f), enum (enumid, values ob))"
    unfolding validMul_def
  proof (intro conjI)
    show "snd ((ob, f), enum (enumid, values ob)) \<in> ContainerValue (imod_enum_field classtype name enumid enumvalues objects obids values) \<longrightarrow>
      lower (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) (snd (fst ((ob, f), enum (enumid, values ob)))) \<le> \<^bold>(length (contained_list (snd ((ob, f), enum (enumid, values ob))))) \<and>
      \<^bold>(length (contained_list (snd ((ob, f), enum (enumid, values ob))))) \<le> upper (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) (snd (fst ((ob, f), enum (enumid, values ob))))"
    proof
      assume "snd ((ob, f), enum (enumid, values ob)) \<in> ContainerValue (imod_enum_field classtype name enumid enumvalues objects obids values)"
      then have "enum (enumid, values ob) \<in> ContainerValue (imod_enum_field classtype name enumid enumvalues objects obids values)"
        by simp
      then show "lower (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) (snd (fst ((ob, f), enum (enumid, values ob)))) \<le> \<^bold>(length (contained_list (snd ((ob, f), enum (enumid, values ob))))) \<and>
        \<^bold>(length (contained_list (snd ((ob, f), enum (enumid, values ob))))) \<le> upper (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) (snd (fst ((ob, f), enum (enumid, values ob))))"
        by simp
    qed
  qed (simp_all add: value_valid f_type)
  then show "validMul (imod_enum_field classtype name enumid enumvalues objects obids values) ((ob, f), FieldValue (imod_enum_field classtype name enumid enumvalues objects obids values) (ob, f))"
    by (simp add: value_def)
qed (simp_all add: assms imod_enum_field_def tmod_enum_field_def)

lemma imod_enum_field_combine_correct:
  assumes "instance_model Imod"
  assumes existing_class: "classtype \<in> Class (Tm Imod)"
  assumes existing_enum: "enumid \<in> Enum (Tm Imod)"
  assumes existing_enum_values: "Pair enumid ` enumvalues \<subseteq> EnumValue (Tm Imod)"
  assumes new_field: "(classtype, name) \<notin> Field (Tm Imod)"
  assumes no_inh_classtype: "\<And>x. (x, classtype) \<notin> Inh (Tm Imod)"
  assumes existing_objects: "objects \<inter> Object Imod = objects"
  assumes all_objects: "\<And>ob. ob \<in> Object Imod \<Longrightarrow> ObjectClass Imod ob = classtype \<longleftrightarrow> ob \<in> objects"
  assumes ids_valid: "\<And>ob. ob \<in> objects \<Longrightarrow> ObjectId Imod ob = obids ob"
  assumes valid_values: "\<And>ob. ob \<in> objects \<Longrightarrow> values ob \<in> enumvalues"
  shows "instance_model (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values))"
proof (intro imod_combine_merge_no_containment_imod2_correct)
  show "instance_model (imod_enum_field classtype name enumid enumvalues objects obids values)"
  proof (intro imod_enum_field_correct)
    show "classtype \<noteq> enumid"
      using assms(1) instance_model.validity_type_model_consistent type_model.property_class_disjoint existing_class existing_enum
      by blast
  next
    show "\<not>id_in_ns enumid (Identifier classtype) \<and> \<not>id_in_ns classtype (Identifier enumid)"
      using assms(1) instance_model.validity_type_model_consistent type_model.property_namespace_restriction existing_class existing_enum
      by blast
  next
    fix o1 o2
    assume o1_object: "o1 \<in> objects"
    then have o1_def: "o1 \<in> Object Imod"
      using existing_objects
      by blast
    assume o2_object: "o2 \<in> objects"
    then have o2_def: "o2 \<in> Object Imod"
      using existing_objects
      by blast
    assume "obids o1 = obids o2"
    then have "ObjectId Imod o1 = ObjectId Imod o2"
      by (simp add: ids_valid o1_object o2_object)
    then show "o1 = o2"
      using assms(1) instance_model.property_object_id_uniqueness o1_def o2_def
      by fastforce
  qed (simp_all add: valid_values)
next
  fix ob
  assume "ob \<in> Object (imod_enum_field classtype name enumid enumvalues objects obids values)"
  then have ob_in_objects: "ob \<in> objects"
    unfolding imod_enum_field_def
    by simp
  then have "ObjectId (imod_enum_field classtype name enumid enumvalues objects obids values) ob = obids ob"
    unfolding imod_enum_field_def
    by simp
  then show "ObjectId Imod ob = ObjectId (imod_enum_field classtype name enumid enumvalues objects obids values) ob"
    by (simp add: ids_valid ob_in_objects)
next
  fix o1 o2
  assume "o1 \<in> Object Imod - Object (imod_enum_field classtype name enumid enumvalues objects obids values)"
  assume "o2 \<in> Object (imod_enum_field classtype name enumid enumvalues objects obids values) - Object Imod"
  then have "o2 \<in> objects - Object Imod"
    unfolding imod_enum_field_def
    by simp
  then have "o2 \<in> {}"
    using existing_objects
    by blast
  then show "o1 = o2"
    by blast
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    using tmod_enum_field_combine_correct assms(1) instance_model.validity_type_model_consistent 
    using existing_class existing_enum existing_enum_values new_field
    by metis
  fix ob f
  assume ob_def: "ob \<in> Object Imod"
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values)) ob = ObjectClass Imod ob"
    by (simp add: all_objects imod_combine_def imod_combine_object_class_def imod_enum_field_def)
  assume "f \<in> Field (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_enum_field_def tmod_enum_field_def
    by simp
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values))) f)"
  then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values))] \<exclamdown>classtype"
    unfolding class_def
    using ob_class_def f_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    unfolding subtype_def imod_enum_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have ob_class_is_classtype: "\<exclamdown>(ObjectClass Imod ob) = \<exclamdown>classtype"
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    then show ?thesis
      unfolding subtype_tuple_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then have ob_extends_classtype: "(ObjectClass Imod ob, classtype) \<in> (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
      unfolding subtype_conv_def
      by fastforce
    have "(ObjectClass Imod ob, classtype) \<notin> (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    proof
      assume "(ObjectClass Imod ob, classtype) \<in> (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
      then show "False"
      proof (cases)
        case base
        then show ?thesis
          unfolding tmod_enum_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      next
        case (step c)
        then show ?thesis
          unfolding tmod_enum_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      qed
    qed
    then show ?thesis
      using ob_extends_classtype
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then have ob_in_objects: "ob \<in> objects"
    using all_objects ob_def
    by blast
  have "\<exclamdown>classtype \<in> ProperClassType (tmod_enum_field classtype name enumid enumvalues)"
    unfolding tmod_enum_field_def
    by (simp add: ProperClassType.rule_proper_classes)
  then have "\<exclamdown>classtype \<in> Type (tmod_enum_field classtype name enumid enumvalues)"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  then show "ob \<in> Object (imod_enum_field classtype name enumid enumvalues objects obids values) \<and>
    \<exclamdown>(ObjectClass (imod_enum_field classtype name enumid enumvalues objects obids values) ob) 
    \<sqsubseteq>[Tm (imod_enum_field classtype name enumid enumvalues objects obids values)]
    \<exclamdown>(class (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) f)"
    unfolding imod_enum_field_def class_def subtype_def
    using ob_in_objects f_def
    by (simp add: subtype_rel.reflexivity)
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    using tmod_enum_field_combine_correct assms(1) instance_model.validity_type_model_consistent 
    using existing_class existing_enum existing_enum_values new_field
    by metis
  fix ob f
  assume "ob \<in> Object (imod_enum_field classtype name enumid enumvalues objects obids values)"
  then have ob_def: "ob \<in> objects"
    unfolding imod_enum_field_def
    by simp
  then have ob_in_imod: "ob \<in> Object Imod"
    using existing_objects
    by blast
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values)) ob = classtype"
    unfolding imod_combine_def imod_enum_field_def imod_combine_object_class_def
    using ob_def all_objects
    by simp
  assume f_def: "f \<in> Field (Tm Imod)"
  have "\<exclamdown>classtype \<in> ProperClassType (Tm Imod)"
    using existing_class
    by (simp add: ProperClassType.rule_proper_classes)
  then have classtype_is_type: "\<exclamdown>classtype \<in> Type (Tm Imod)"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values))) f)"
  then have "\<exclamdown>classtype \<sqsubseteq>[Tm (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values))] \<exclamdown>(fst f)"
    unfolding class_def
    using ob_class_def
    by simp
  then have "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    unfolding subtype_def imod_enum_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+ \<union>
    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
  proof (elim UnE)
    assume "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    then have "classtype = fst f"
      unfolding subtype_tuple_def
      by blast
    then have "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (Tm Imod)"
      unfolding subtype_tuple_def
      using classtype_is_type
      by blast
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by simp
  next
    assume "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then have "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
      unfolding subtype_conv_def tmod_combine_def tmod_enum_field_def
      by simp
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by simp
  next
    assume "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then have "\<exclamdown>classtype \<sqsubseteq>[Tm (Imod)] \<exclamdown>(fst f)"
    unfolding subtype_def
    by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
  then show "ob \<in> Object Imod \<and> \<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) f)"
    unfolding class_def
    using all_objects ob_def ob_in_imod
    by blast
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    using tmod_enum_field_combine_correct assms(1) instance_model.validity_type_model_consistent 
    using existing_class existing_enum existing_enum_values new_field
    by metis
  fix ob f
  assume ob_def: "ob \<in> Object Imod"
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values)) ob = ObjectClass Imod ob"
    unfolding imod_combine_def imod_enum_field_def imod_combine_object_class_def
    by (simp add: all_objects)
  then have "ObjectClass Imod ob \<in> Class (Tm Imod)"
    by (simp add: assms(1) instance_model.structure_object_class_wellformed ob_def)
  then have "\<exclamdown>(ObjectClass Imod ob) \<in> ProperClassType (Tm Imod)"
    by (fact ProperClassType.rule_proper_classes)
  then have ob_class_is_type: "\<exclamdown>(ObjectClass Imod ob) \<in> Type (Tm Imod)"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  assume f_def: "f \<in> Field (Tm Imod)"
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values))) f)"
  then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (imod_combine Imod (imod_enum_field classtype name enumid enumvalues objects obids values))] \<exclamdown>(fst f)"
    unfolding class_def
    using ob_class_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    unfolding subtype_def imod_enum_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+ \<union>
    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    then have "ObjectClass Imod ob = fst f"
      unfolding subtype_tuple_def
      by fastforce
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (Tm Imod)"
      unfolding subtype_tuple_def
      using ob_class_is_type
      by simp
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by simp
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
      unfolding subtype_conv_def tmod_combine_def tmod_enum_field_def
      by simp
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by simp
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then show "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (Imod)] \<exclamdown>(class (Tm Imod) f)"
    unfolding subtype_def class_def
    by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    using tmod_enum_field_combine_correct assms(1) instance_model.validity_type_model_consistent 
    using existing_class existing_enum existing_enum_values new_field
    by metis
  fix ob f
  assume "ob \<in> Object (imod_enum_field classtype name enumid enumvalues objects obids values)"
  then have ob_def: "ob \<in> objects"
    unfolding imod_enum_field_def
    by simp
  then have ob_class_def: "ObjectClass (imod_enum_field classtype name enumid enumvalues objects obids values) ob = classtype"
    unfolding imod_combine_def imod_enum_field_def imod_combine_object_class_def
    using ob_def all_objects
    by simp
  assume "f \<in> Field (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_enum_field_def tmod_enum_field_def
    by simp
  have "\<exclamdown>classtype \<in> ProperClassType (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
    unfolding imod_enum_field_def tmod_enum_field_def
    by (simp add: ProperClassType.rule_proper_classes)
  then have "\<exclamdown>classtype \<in> Type (Tm (imod_enum_field classtype name enumid enumvalues objects obids values))"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  then have "\<exclamdown>classtype \<sqsubseteq>[Tm (imod_enum_field classtype name enumid enumvalues objects obids values)] \<exclamdown>classtype"
    unfolding subtype_def
    by (simp add: subtype_rel.reflexivity)
  then show "\<exclamdown>(ObjectClass (imod_enum_field classtype name enumid enumvalues objects obids values) ob)
    \<sqsubseteq>[Tm (imod_enum_field classtype name enumid enumvalues objects obids values)]
    \<exclamdown>(class (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)) f)"
    unfolding imod_enum_field_def class_def
    by (simp add: f_def ob_def)
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_enum_field classtype name enumid enumvalues))"
    using tmod_enum_field_combine_correct assms(1) instance_model.validity_type_model_consistent 
    using existing_class existing_enum existing_enum_values new_field
    by metis
  then show "type_model (tmod_combine (Tm Imod) (Tm (imod_enum_field classtype name enumid enumvalues objects obids values)))"
    unfolding imod_enum_field_def
    by simp
qed (simp_all add: assms imod_enum_field_def tmod_enum_field_def)



section "Encoding of field values for an enumeration-typed field where the enumeration type is encoded as node types."

definition ig_enum_as_node_types_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> ('t \<Rightarrow> 't) \<Rightarrow>  'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values = \<lparr>
    TG = tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues,
    Id = obids ` objects \<union> enumids ` enumvalues,
    N = typed (type (id_to_list classtype)) ` objects \<union> (\<lambda>x. typed (type (id_to_list enumid @ [x])) (enumob x)) ` enumvalues,
    E = (\<lambda>x. (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid @ [values x])) (enumob (values x)))) ` objects,
    ident = (\<lambda>x. if x \<in> enumids ` enumvalues then typed (type (id_to_list enumid @ [(THE y. enumids y = x)])) (enumob (THE y. enumids y = x)) else 
       if x \<in> obids ` objects then typed (type (id_to_list classtype)) (THE y. obids y = x) else undefined)
  \<rparr>"

lemma ig_enum_as_node_types_field_as_edge_type_correct:
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_enum_ids: "\<And>ev1 ev2. ev1 \<in> enumvalues \<Longrightarrow> enumids ev1 = enumids ev2 \<Longrightarrow> ev1 = ev2"
  assumes unique_ids_set: "obids ` objects \<inter> enumids ` enumvalues = {}"
  assumes enum_class_neq: "id_to_list classtype \<noteq> id_to_list enumid"
  assumes enumvalues_class_neq: "id_to_list classtype \<notin> (\<lambda>x. id_to_list enumid @ [x]) ` enumvalues"
  assumes valid_values: "\<And>ob. ob \<in> objects \<Longrightarrow> values ob \<in> enumvalues"
  shows "instance_graph (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
proof (intro instance_graph.intro)
  fix n
  assume "n \<in> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have "n \<in> typed (type (id_to_list classtype)) ` objects \<union> (\<lambda>x. typed (type (id_to_list enumid @ [x])) (enumob x)) ` enumvalues"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  then have type_and_node_def: "type\<^sub>n n \<in> NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<and> n \<in> Node"
  proof
    assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
    then show "type\<^sub>n n \<in> NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<and> n \<in> Node"
    proof (intro conjI)
      assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
      then show "type\<^sub>n n \<in> NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
        unfolding tg_enum_as_node_types_field_as_edge_type_def
        by fastforce
    next
      assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
      then show "n \<in> Node"
        unfolding Node_def
        using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
        by fastforce
    qed
  next
    assume "n \<in> (\<lambda>x. typed (type (id_to_list enumid @ [x])) (enumob x)) ` enumvalues"
    then show "type\<^sub>n n \<in> NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<and> n \<in> Node"
    proof (intro conjI)
      assume "n \<in> (\<lambda>x. typed (type (id_to_list enumid @ [x])) (enumob x)) ` enumvalues"
      then show "type\<^sub>n n \<in> NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues)"
        unfolding tg_enum_as_node_types_field_as_edge_type_def
        by fastforce
    next
      assume "n \<in> (\<lambda>x. typed (type (id_to_list enumid @ [x])) (enumob x)) ` enumvalues"
      then show "n \<in> Node"
        unfolding Node_def
        using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
        by fastforce
    qed
  qed
  then show "type\<^sub>n n \<in> NT (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  show "n \<in> Node"
    by (simp add: type_and_node_def)
next
  fix s l t
  assume "(s, l, t) \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have edge_def: "(s, l, t) \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), 
    typed (type (id_to_list enumid @ [values x])) (enumob (values x)))) ` objects"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  show "s \<in> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) \<and> 
    l \<in> ET (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) \<and> 
    t \<in> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  proof (intro conjI)
    show "s \<in> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
      unfolding ig_enum_as_node_types_field_as_edge_type_def
      using edge_def
      by fastforce
  next
    have "l = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid))"
      using edge_def
      by blast
    then show "l \<in> ET (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
      unfolding ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def
      by simp
  next
    have "t \<in> (\<lambda>x. typed (type (id_to_list enumid @ [values x])) (enumob (values x))) ` objects"
      using edge_def
      by blast
    then show "t \<in> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
      unfolding ig_enum_as_node_types_field_as_edge_type_def
      using valid_values
      by fastforce
  qed
next
  fix i
  assume "i \<in> Id (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have "i \<in> obids ` objects \<or> i \<in> enumids ` enumvalues"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  then show "ident (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i \<in> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) \<and> 
    type\<^sub>n (ident (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i) \<in> Lab\<^sub>t"
  proof (elim disjE)
    assume i_in_id: "i \<in> obids ` objects"
    then show ?thesis
    proof (intro conjI)
      assume "i \<in> obids ` objects"
      then have "(THE y. obids y = i) \<in> objects"
      proof
        fix x
        assume i_def: "i = obids x"
        assume x_is_object: "x \<in> objects"
        have "(THE y. obids y = obids x) \<in> objects"
        proof (rule the1I2)
          show "\<exists>!y. obids y = obids x"
            using unique_ids x_is_object
            by metis
        next
          fix y
          assume "obids y = obids x"
          then show "y \<in> objects"
            using unique_ids x_is_object
            by metis
        qed
        then show "(THE y. obids y = i) \<in> objects"
          by (simp add: i_def)
      qed
      then have "typed (type (id_to_list classtype)) (THE y. obids y = i) \<in> typed (type (id_to_list classtype)) ` objects"
        by simp
      then show "ident (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i \<in> 
        N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
        unfolding ig_enum_as_node_types_field_as_edge_type_def
        using i_in_id unique_ids_set
        by fastforce
    next
      have "type\<^sub>n (typed (type (id_to_list classtype)) (THE y. obids y = i)) \<in> Lab\<^sub>t"
        by (simp add: Lab\<^sub>t.rule_type_labels)
      then show "type\<^sub>n (ident (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i) \<in> Lab\<^sub>t"
        unfolding ig_enum_as_node_types_field_as_edge_type_def
        using i_in_id unique_ids_set
        by fastforce
    qed
  next
    assume i_in_id: "i \<in> enumids ` enumvalues"
    then show ?thesis
    proof (intro conjI)
      assume "i \<in> enumids ` enumvalues"
      then have "(THE y. enumids y = i) \<in> enumvalues"
      proof
        fix x
        assume i_def: "i = enumids x"
        assume x_is_enum_value: "x \<in> enumvalues"
        have "(THE y. enumids y = enumids x) \<in> enumvalues"
        proof (rule the1I2)
          show "\<exists>!y. enumids y = enumids x"
            using unique_enum_ids x_is_enum_value
            by metis
        next
          fix y
          assume "enumids y = enumids x"
          then show "y \<in> enumvalues"
            using unique_enum_ids x_is_enum_value
            by metis
        qed
        then show "(THE y. enumids y = i) \<in> enumvalues"
          by (simp add: i_def)
      qed
      then have "typed (type (id_to_list enumid @ [(THE y. enumids y = i)])) (enumob (THE y. enumids y = i)) \<in> 
        (\<lambda>x. typed (type (id_to_list enumid @ [x])) (enumob x)) ` enumvalues"
        by simp
      then show "ident (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i \<in> 
        N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
        unfolding ig_enum_as_node_types_field_as_edge_type_def
        using i_in_id
        by simp
    next
      have "type\<^sub>n (typed (type (id_to_list enumid @ [(THE y. enumids y = i)])) (enumob (THE y. enumids y = i))) \<in> Lab\<^sub>t"
        by (simp add: Lab\<^sub>t.rule_type_labels)
      then show "type\<^sub>n (ident (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i) \<in> Lab\<^sub>t"
        unfolding ig_enum_as_node_types_field_as_edge_type_def
        using i_in_id
        by simp
    qed
  qed
next
  show "type_graph (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    using tg_enum_as_node_types_field_as_edge_type_correct
    by simp
next
  fix e
  assume "e \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), 
    typed (type (id_to_list enumid @ [values x])) (enumob (values x)))) ` objects"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  have type_n_def: "type\<^sub>n (src e) = type (id_to_list classtype)"
    using e_def
    by fastforce
  have type_e_def: "src (type\<^sub>e e) = type (id_to_list classtype)"
    using e_def
    by fastforce
  show "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
    unfolding ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def
    using type_n_def type_e_def
    by simp
next
  fix e
  assume "e \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), 
    typed (type (id_to_list enumid @ [values x])) (enumob (values x)))) ` objects"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  have "type\<^sub>n (tgt e) \<in> (\<lambda>x. type (id_to_list enumid @ [values x])) ` objects"
    using e_def
    by fastforce
  then have type_n_def: "type\<^sub>n (tgt e) \<in> (\<lambda>x. type (id_to_list enumid @ [x])) ` enumvalues"
    using valid_values
    by fastforce
  have type_e_def: "tgt (type\<^sub>e e) = type (id_to_list enumid)"
    using e_def
    by fastforce
  show "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
    unfolding ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def
    using type_n_def type_e_def
    by fastforce
next
  fix n
  assume "n \<in> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have "n \<in> typed (type (id_to_list classtype)) ` objects \<union> (\<lambda>x. typed (type (id_to_list enumid @ [x])) (enumob x)) ` enumvalues"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  then have "type\<^sub>n n = type (id_to_list classtype) \<or> type\<^sub>n n \<in> (\<lambda>x. type (id_to_list enumid @ [x])) ` enumvalues"
    by fastforce
  then have "type\<^sub>n n \<noteq> type (id_to_list enumid)"
    using enum_class_neq
    by fastforce
  then show "type\<^sub>n n \<notin> type_graph.abs (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
    unfolding ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def
    by simp
next
  fix et n
  assume "et \<in> ET (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid))"
    unfolding ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def
    by simp
  then have src_et_def: "src et = type (id_to_list classtype)"
    by simp
  have mult_et_def: "m_out (mult (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) et) = \<^bold>1..\<^bold>1"
    unfolding ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def
    by (simp add: et_def)
  assume "n \<in> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have n_def: "n \<in> typed (type (id_to_list classtype)) ` objects \<union> (\<lambda>x. typed (type (id_to_list enumid @ [x])) (enumob x)) ` enumvalues"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> inh (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
  then have "(type\<^sub>n n, src et) \<in> {(type (id_to_list classtype), type (id_to_list classtype)), (type (id_to_list enumid), type (id_to_list enumid))} \<union> 
      (\<lambda>x. (type x, type x)) ` append (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues \<union>
      (\<lambda>x. (type x, type (id_to_list enumid))) ` append (id_to_list enumid) ` (\<lambda>x. [x]) ` enumvalues"
    unfolding ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def
    by simp
  then have type_n_def: "type\<^sub>n n = type (id_to_list classtype)"
    using src_et_def enum_class_neq enumvalues_class_neq
    by fastforce
  have "n \<in> typed (type (id_to_list classtype)) ` objects"
    using n_def
  proof (elim UnE)
    assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
    then show ?thesis
      by simp
  next
    assume "n \<in> (\<lambda>x. typed (LabDef.type (id_to_list enumid @ [x])) (enumob x)) ` enumvalues"
    then have "type\<^sub>n n \<in> (\<lambda>x. type (id_to_list enumid @ [x])) ` enumvalues"
      by fastforce
    then have "type\<^sub>n n \<noteq> type (id_to_list classtype)"
      using enumvalues_class_neq
      by auto
    then show ?thesis
      using type_n_def
      by blast
  qed
  then have "card {e \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} in \<^bold>1..\<^bold>1"
  proof (elim imageE)
    fix x
    assume x_def: "x \<in> objects"
    assume n_def: "n = typed (LabDef.type (id_to_list classtype)) x"
    have "{e \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} = 
      {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid @ [values x])) (enumob (values x)))}"
    proof
      show "{e \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} \<subseteq> 
        {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid @ [values x])) (enumob (values x)))}"
      proof
        fix y
        assume "y \<in> {e \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et}"
        then show "y \<in> {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid @ [values x])) (enumob (values x)))}"
        proof
          assume "y \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) \<and> src y = n \<and> type\<^sub>e y = et"
          then show "y \<in> {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid @ [values x])) (enumob (values x)))}"
            unfolding ig_enum_as_node_types_field_as_edge_type_def
            using et_def n_def
            by fastforce
        qed
      qed
    next
      show "{(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid @ [values x])) (enumob (values x)))} \<subseteq> 
        {e \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et}"
      proof
        fix y
        assume "y \<in> {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid @ [values x])) (enumob (values x)))}"
        then have "y = (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid @ [values x])) (enumob (values x)))"
          by simp
        then show "y \<in> {e \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et}"
          unfolding ig_enum_as_node_types_field_as_edge_type_def
          using et_def n_def x_def
          by simp
      qed
    qed
    then have "card {e \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} = 1"
      by simp
    then show ?thesis
      unfolding within_multiplicity_def
      by simp
  qed
  then show "card {e \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} in 
    m_out (mult (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) et)"
    using mult_et_def
    by simp
next
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) p"
    unfolding ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def instance_graph_containment_proj_def pre_digraph.cycle_def pre_digraph.awalk_def
    by simp
qed (simp_all add: assms ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def)

lemma ig_enum_as_node_types_field_as_edge_type_combine_correct:
  assumes "instance_graph IG"
  assumes existing_node_types: "NT (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<subseteq> NT (TG IG)"
  assumes existing_inheritance: "inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<subseteq> inh (TG IG)"
  assumes abstract_maintained: "abs (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues) \<subseteq> abs (TG IG)"
  assumes new_edge_type: "\<And>s l t. (type (id_to_list classtype), s) \<in> inh (TG IG) \<Longrightarrow> l = LabDef.edge [name] \<Longrightarrow> (s, l, t) \<notin> ET (TG IG)"
  assumes no_inh_classtype: "\<And>x. (x, type (id_to_list classtype)) \<in> inh (TG IG) \<Longrightarrow> x = type (id_to_list classtype)"
  assumes existing_objects: "N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) \<subseteq> N IG"
  assumes all_objects: "\<And>n. n \<in> N IG \<Longrightarrow> type\<^sub>n n = type (id_to_list classtype) \<Longrightarrow> n \<in> typed (type (id_to_list classtype)) ` objects"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_enum_ids: "\<And>ev1 ev2. ev1 \<in> enumvalues \<Longrightarrow> enumids ev1 = enumids ev2 \<Longrightarrow> ev1 = ev2"
  assumes unique_ids_set: "obids ` objects \<inter> enumids ` enumvalues = {}"
  assumes existing_ids: "obids ` objects \<union> enumids ` enumvalues \<subseteq> Id IG"
  assumes valid_ids: "\<And>i. i \<in> obids ` objects \<union> enumids ` enumvalues \<Longrightarrow> ident IG i = ident (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i"
  assumes enum_class_neq: "id_to_list classtype \<noteq> id_to_list enumid"
  assumes enumvalues_class_neq: "id_to_list classtype \<notin> (\<lambda>x. id_to_list enumid @ [x]) ` enumvalues"
  assumes valid_values: "\<And>ob. ob \<in> objects \<Longrightarrow> values ob \<in> enumvalues"
  shows "instance_graph (ig_combine IG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
proof (intro ig_combine_merge_no_containment_imod2_correct)
  show "instance_graph (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
    by (intro ig_enum_as_node_types_field_as_edge_type_correct) (simp_all add: assms)
next
  have "type_graph (tg_combine (TG IG) (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))"
  proof (intro tg_enum_as_node_types_field_as_edge_type_combine_correct)
    fix s l t
    assume "(s, LabDef.type (id_to_list classtype)) \<in> inh (TG IG) \<or> (LabDef.type (id_to_list classtype), s) \<in> inh (TG IG)"
    then have s_def: "(LabDef.type (id_to_list classtype), s) \<in> inh (TG IG)"
      using no_inh_classtype
      by blast
    assume "l = LabDef.edge [name]"
    then show "(s, l, t) \<notin> ET (TG IG)"
      by (simp add: new_edge_type s_def)
  qed (simp_all add: assms instance_graph.validity_type_graph)
  then show "type_graph (tg_combine (TG IG) (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)))"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
next
  show "ET (TG IG) \<inter> ET (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) = {}"
    using existing_node_types
    unfolding ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def
    by (simp add: assms(1) instance_graph.validity_type_graph new_edge_type type_graph.validity_inh_node)
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have n_def: "n \<in> N IG"
    using existing_objects
    by blast
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG))\<^sup>+"
    using existing_inheritance
    by (simp add: Un_absorb2)
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  then show "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG) et)"
    using assms(1) et_def n_def instance_graph.validity_outgoing_mult
    by blast
next
  have instance_graph_valid: "instance_graph (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
    by (intro ig_enum_as_node_types_field_as_edge_type_correct) (simp_all add: assms)
  fix et n
  assume et_in_ig: "et \<in> ET (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid))"
    unfolding ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def
    by simp
  assume n_def: "n \<in> N IG \<union> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have "n \<in> N IG \<union> typed (type (id_to_list classtype)) ` objects \<union> (\<lambda>x. typed (type (id_to_list enumid @ [x])) (enumob x)) ` enumvalues"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG))\<^sup>+"
    using existing_inheritance
    by (simp add: Un_absorb2)
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  then have "(type\<^sub>n n, type (id_to_list classtype)) \<in> inh (TG IG)"
    using et_def
    by simp
  then have type_n_def: "type\<^sub>n n = type (id_to_list classtype)"
    using no_inh_classtype
    by simp
  then have edge_extend_def: "(type\<^sub>n n, type (id_to_list classtype)) \<in> inh (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
    unfolding ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def
    by simp
  have "n \<in> typed (type (id_to_list classtype)) ` objects"
    using type_n_def all_objects n_def existing_objects
    by blast
  then have "n \<in> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  then show "card {e \<in> E (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} in 
    m_out (mult (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) et)"
    using instance_graph_valid et_in_ig et_def edge_extend_def instance_graph.validity_outgoing_mult
    by fastforce
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have n_def: "n \<in> N IG"
    using existing_objects
    by blast
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (TG (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues))\<^sup>+"
    unfolding ig_enum_as_node_types_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG))\<^sup>+"
    using existing_inheritance
    by (simp add: Un_absorb2)
  then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  then show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG) et)"
    using assms(1) et_def n_def instance_graph.validity_ingoing_mult
    by blast
qed (simp_all add: ig_enum_as_node_types_field_as_edge_type_def tg_enum_as_node_types_field_as_edge_type_def assms)


subsection "Transformation functions"

definition imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> ('t \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values Imod = \<lparr>
    TG = tg_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues,
    Id = obids ` Object Imod \<union> enumids ` enumvalues,
    N = typed (type (id_to_list classtype)) ` Object Imod \<union> (\<lambda>x. typed (type (id_to_list enumid @ [x])) (enumob x)) ` enumvalues,
    E = (\<lambda>x. (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid @ [values x])) (enumob (values x)))) ` Object Imod,
    ident = (\<lambda>x. if x \<in> enumids ` enumvalues then typed (type (id_to_list enumid @ [(THE y. enumids y = x)])) (enumob (THE y. enumids y = x)) else
      if x \<in> obids ` Object Imod then typed (type (id_to_list classtype)) (THE y. obids y = x) else undefined)
  \<rparr>"

lemma imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type_proj:
  shows "imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values (imod_enum_field classtype name enumid enumvalues objects obids values) = 
    ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values"
  unfolding imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type_def ig_enum_as_node_types_field_as_edge_type_def imod_enum_field_def
  by auto

lemma imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type_func:
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_enum_ids: "\<And>ev1 ev2. ev1 \<in> enumvalues \<Longrightarrow> enumids ev1 = enumids ev2 \<Longrightarrow> ev1 = ev2"
  assumes unique_ids_set: "obids ` objects \<inter> enumids ` enumvalues = {}"
  shows "ig_combine_mapping_function (imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values)
    (imod_enum_field classtype name enumid enumvalues objects obids values) (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
proof (intro ig_combine_mapping_function.intro)
  fix ImodX i
  assume "i \<in> Id (imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values (imod_enum_field classtype name enumid enumvalues objects obids values))"
  then have "i \<in> obids ` Object (imod_enum_field classtype name enumid enumvalues objects obids values) \<union> enumids ` enumvalues"
    unfolding imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type_def
    by simp
  then show "ident (imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values (imod_enum_field classtype name enumid enumvalues objects obids values)) i =
    ident (imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values (imod_combine (imod_enum_field classtype name enumid enumvalues objects obids values) ImodX)) i"
    unfolding imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type_def imod_enum_field_def ig_enum_as_node_types_field_as_edge_type_def imod_combine_def
    by fastforce
qed(auto simp add: imod_enum_field_to_ig_enum_as_node_types_field_as_edge_type_def imod_enum_field_def ig_enum_as_node_types_field_as_edge_type_def imod_combine_def)

definition ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 't set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't list, 't) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values IG = \<lparr>
    Tm = tmod_enum_field classtype name enumid enumvalues,
    Object = nodeId ` src ` E IG,
    ObjectClass = (\<lambda>x. if x \<in> nodeId ` src ` E IG then classtype else undefined),
    ObjectId = (\<lambda>x. if x \<in> nodeId ` src ` E IG then obids x else undefined),
    FieldValue = (\<lambda>x. if fst x \<in> nodeId ` src ` E IG \<and> snd x = (classtype, name) then enum (enumid, values (fst x)) else undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field_proj:
  shows "ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values 
    (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) = 
    imod_enum_field classtype name enumid enumvalues objects obids values"
proof-
  have "nodeId ` (\<lambda>x. typed (LabDef.type (id_to_list classtype)) x) ` objects = objects"
    by force
  then have "nodeId ` fst ` (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) x, 
    (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list enumid)), 
    typed (LabDef.type (id_to_list enumid @ [values x])) (enumob (values x)))) ` objects = objects"
    by force
  then show "ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values 
    (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) = 
    imod_enum_field classtype name enumid enumvalues objects obids values"
    unfolding ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field_def imod_enum_field_def ig_enum_as_node_types_field_as_edge_type_def
    by simp
qed

lemma ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field_func:
  shows "imod_combine_mapping_function (ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values)
    (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) (imod_enum_field classtype name enumid enumvalues objects obids values)"
proof-
  have "nodeId ` (\<lambda>x. typed (LabDef.type (id_to_list classtype)) x) ` objects = objects"
    by force
  then have "nodeId ` fst ` (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) x, 
    (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list enumid)), 
    typed (LabDef.type (id_to_list enumid @ [values x])) (enumob (values x)))) ` objects = objects"
    by force
  then show "imod_combine_mapping_function (ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values)
    (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) (imod_enum_field classtype name enumid enumvalues objects obids values)"
  proof (intro imod_combine_mapping_function.intro)
    fix IGX
    show "Object (ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))
      \<subseteq> Object (ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values (ig_combine (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) IGX))"
    proof
      fix x
      assume "x \<in> Object (ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
      then have "x \<in> objects"
        unfolding ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field_def imod_enum_field_def ig_enum_as_node_types_field_as_edge_type_def ig_combine_def
        by fastforce
      then show "x \<in> Object (ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values (ig_combine (ig_enum_as_node_types_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) IGX))"
        unfolding ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field_def imod_enum_field_def ig_enum_as_node_types_field_as_edge_type_def ig_combine_def
        by force
    qed
  qed (auto simp add: ig_enum_as_node_types_field_as_edge_type_to_imod_enum_field_def imod_enum_field_def ig_enum_as_node_types_field_as_edge_type_def ig_combine_def)
qed



section "Encoding of field values for an enumeration-typed field where the enumeration type is encoded as node types."

definition ig_enum_as_flags_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> ('t \<Rightarrow> 't) \<Rightarrow>  'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values = \<lparr>
    TG = tg_enum_as_flags_field_as_edge_type classtype name enumid,
    Id = obids ` objects \<union> enumids ` enumvalues,
    N = typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list enumid)) ` enumob ` enumvalues,
    E = (\<lambda>x. (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid)) (enumob (values x)))) ` objects,
    ident = (\<lambda>x. if x \<in> enumids ` enumvalues then typed (type (id_to_list enumid)) (enumob (THE y. enumids y = x)) else 
       if x \<in> obids ` objects then typed (type (id_to_list classtype)) (THE y. obids y = x) else undefined)
  \<rparr>"

lemma ig_enum_as_flags_field_as_edge_type_correct:
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_enum_ids: "\<And>ev1 ev2. ev1 \<in> enumvalues \<Longrightarrow> enumids ev1 = enumids ev2 \<Longrightarrow> ev1 = ev2"
  assumes unique_ids_set: "obids ` objects \<inter> enumids ` enumvalues = {}"
  assumes enum_class_neq: "id_to_list classtype \<noteq> id_to_list enumid"
  assumes valid_values: "\<And>ob. ob \<in> objects \<Longrightarrow> values ob \<in> enumvalues"
  shows "instance_graph (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
proof (intro instance_graph.intro)
  fix n
  assume "n \<in> N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have "n \<in> typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list enumid)) ` enumob ` enumvalues"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  then have type_and_node_def: "type\<^sub>n n \<in> NT (tg_enum_as_flags_field_as_edge_type classtype name enumid) \<and> n \<in> Node"
  proof
    assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
    then show "type\<^sub>n n \<in> NT (tg_enum_as_flags_field_as_edge_type classtype name enumid) \<and> n \<in> Node"
    proof (intro conjI)
      assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
      then show "type\<^sub>n n \<in> NT (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
        unfolding tg_enum_as_flags_field_as_edge_type_def
        by fastforce
    next
      assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
      then show "n \<in> Node"
        unfolding Node_def
        using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
        by fastforce
    qed
  next
    assume "n \<in> typed (type (id_to_list enumid)) ` enumob ` enumvalues"
    then show "type\<^sub>n n \<in> NT (tg_enum_as_flags_field_as_edge_type classtype name enumid) \<and> n \<in> Node"
    proof (intro conjI)
      assume "n \<in> typed (type (id_to_list enumid)) ` enumob ` enumvalues"
      then show "type\<^sub>n n \<in> NT (tg_enum_as_flags_field_as_edge_type classtype name enumid)"
        unfolding tg_enum_as_flags_field_as_edge_type_def
        by fastforce
    next
      assume "n \<in> typed (type (id_to_list enumid)) ` enumob ` enumvalues"
      then show "n \<in> Node"
        unfolding Node_def
        using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
        by fastforce
    qed
  qed
  then show "type\<^sub>n n \<in> NT (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  show "n \<in> Node"
    by (simp add: type_and_node_def)
next
  fix s l t
  assume "(s, l, t) \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have edge_def: "(s, l, t) \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), 
    typed (type (id_to_list enumid)) (enumob (values x)))) ` objects"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  show "s \<in> N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) \<and> 
    l \<in> ET (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) \<and> 
    t \<in> N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  proof (intro conjI)
    show "s \<in> N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
      unfolding ig_enum_as_flags_field_as_edge_type_def
      using edge_def
      by fastforce
  next
    have "l = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid))"
      using edge_def
      by blast
    then show "l \<in> ET (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
      unfolding ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def
      by simp
  next
    have "t \<in> typed (type (id_to_list enumid)) ` enumob ` values ` objects"
      using edge_def
      by blast
    then show "t \<in> N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
      unfolding ig_enum_as_flags_field_as_edge_type_def
      using valid_values
      by fastforce
  qed
next
  fix i
  assume "i \<in> Id (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have "i \<in> obids ` objects \<or> i \<in> enumids ` enumvalues"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  then show "ident (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i \<in> N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) \<and> 
    type\<^sub>n (ident (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i) \<in> Lab\<^sub>t"
  proof (elim disjE)
    assume i_in_id: "i \<in> obids ` objects"
    then show ?thesis
    proof (intro conjI)
      assume "i \<in> obids ` objects"
      then have "(THE y. obids y = i) \<in> objects"
      proof
        fix x
        assume i_def: "i = obids x"
        assume x_is_object: "x \<in> objects"
        have "(THE y. obids y = obids x) \<in> objects"
        proof (rule the1I2)
          show "\<exists>!y. obids y = obids x"
            using unique_ids x_is_object
            by metis
        next
          fix y
          assume "obids y = obids x"
          then show "y \<in> objects"
            using unique_ids x_is_object
            by metis
        qed
        then show "(THE y. obids y = i) \<in> objects"
          by (simp add: i_def)
      qed
      then have "typed (type (id_to_list classtype)) (THE y. obids y = i) \<in> typed (type (id_to_list classtype)) ` objects"
        by simp
      then show "ident (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i \<in> 
        N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
        unfolding ig_enum_as_flags_field_as_edge_type_def
        using i_in_id unique_ids_set
        by fastforce
    next
      have "type\<^sub>n (typed (type (id_to_list classtype)) (THE y. obids y = i)) \<in> Lab\<^sub>t"
        by (simp add: Lab\<^sub>t.rule_type_labels)
      then show "type\<^sub>n (ident (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i) \<in> Lab\<^sub>t"
        unfolding ig_enum_as_flags_field_as_edge_type_def
        using i_in_id unique_ids_set
        by fastforce
    qed
  next
    assume i_in_id: "i \<in> enumids ` enumvalues"
    then show ?thesis
    proof (intro conjI)
      assume "i \<in> enumids ` enumvalues"
      then have "(THE y. enumids y = i) \<in> enumvalues"
      proof
        fix x
        assume i_def: "i = enumids x"
        assume x_is_enum_value: "x \<in> enumvalues"
        have "(THE y. enumids y = enumids x) \<in> enumvalues"
        proof (rule the1I2)
          show "\<exists>!y. enumids y = enumids x"
            using unique_enum_ids x_is_enum_value
            by metis
        next
          fix y
          assume "enumids y = enumids x"
          then show "y \<in> enumvalues"
            using unique_enum_ids x_is_enum_value
            by metis
        qed
        then show "(THE y. enumids y = i) \<in> enumvalues"
          by (simp add: i_def)
      qed
      then have "typed (type (id_to_list enumid)) (enumob (THE y. enumids y = i)) \<in> 
        (\<lambda>x. typed (type (id_to_list enumid)) (enumob x)) ` enumvalues"
        by simp
      then show "ident (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i \<in> 
        N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
        unfolding ig_enum_as_flags_field_as_edge_type_def
        using i_in_id
        by fastforce
    next
      have "type\<^sub>n (typed (type (id_to_list enumid)) (enumob (THE y. enumids y = i))) \<in> Lab\<^sub>t"
        by (simp add: Lab\<^sub>t.rule_type_labels)
      then show "type\<^sub>n (ident (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i) \<in> Lab\<^sub>t"
        unfolding ig_enum_as_flags_field_as_edge_type_def
        using i_in_id
        by simp
    qed
  qed
next
  show "type_graph (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    using tg_enum_as_flags_field_as_edge_type_correct
    by simp
next
  fix e
  assume "e \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), 
    typed (type (id_to_list enumid)) (enumob (values x)))) ` objects"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  have type_n_def: "type\<^sub>n (src e) = type (id_to_list classtype)"
    using e_def
    by fastforce
  have type_e_def: "src (type\<^sub>e e) = type (id_to_list classtype)"
    using e_def
    by fastforce
  show "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
    unfolding ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def
    using type_n_def type_e_def
    by simp
next
  fix e
  assume "e \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), 
    typed (type (id_to_list enumid)) (enumob (values x)))) ` objects"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  have type_n_def: "type\<^sub>n (tgt e) = type (id_to_list enumid)"
    using e_def
    by fastforce
  have type_e_def: "tgt (type\<^sub>e e) = type (id_to_list enumid)"
    using e_def
    by fastforce
  show "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
    unfolding ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def
    using type_n_def type_e_def
    by fastforce
next
  fix et n
  assume "et \<in> ET (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid))"
    unfolding ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def
    by simp
  then have src_et_def: "src et = type (id_to_list classtype)"
    by simp
  have mult_et_def: "m_out (mult (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) et) = \<^bold>1..\<^bold>1"
    unfolding ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def
    by (simp add: et_def)
  assume "n \<in> N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have n_def: "n \<in> typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list enumid)) ` enumob ` enumvalues"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> inh (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
  then have type_n_def: "type\<^sub>n n = type (id_to_list classtype)"
    unfolding ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def
    using src_et_def enum_class_neq
    by fastforce
  have "n \<in> typed (type (id_to_list classtype)) ` objects"
    using n_def
  proof (elim UnE)
    assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
    then show ?thesis
      by simp
  next
    assume "n \<in> typed (type (id_to_list enumid)) ` enumob ` enumvalues"
    then have "type\<^sub>n n = type (id_to_list enumid)"
      by fastforce
    then have "type\<^sub>n n \<noteq> type (id_to_list classtype)"
      using enum_class_neq
      by simp
    then show ?thesis
      using type_n_def
      by blast
  qed
  then have "card {e \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} in \<^bold>1..\<^bold>1"
  proof (elim imageE)
    fix x
    assume x_def: "x \<in> objects"
    assume n_def: "n = typed (LabDef.type (id_to_list classtype)) x"
    have "{e \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} = 
      {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid)) (enumob (values x)))}"
    proof
      show "{e \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} \<subseteq> 
        {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid)) (enumob (values x)))}"
      proof
        fix y
        assume "y \<in> {e \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et}"
        then show "y \<in> {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid)) (enumob (values x)))}"
        proof
          assume "y \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) \<and> src y = n \<and> type\<^sub>e y = et"
          then show "y \<in> {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid)) (enumob (values x)))}"
            unfolding ig_enum_as_flags_field_as_edge_type_def
            using et_def n_def
            by fastforce
        qed
      qed
    next
      show "{(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid)) (enumob (values x)))} \<subseteq> 
        {e \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et}"
      proof
        fix y
        assume "y \<in> {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid)) (enumob (values x)))}"
        then have "y = (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid)) (enumob (values x)))"
          by simp
        then show "y \<in> {e \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et}"
          unfolding ig_enum_as_flags_field_as_edge_type_def
          using et_def n_def x_def
          by simp
      qed
    qed
    then have "card {e \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} = 1"
      by simp
    then show ?thesis
      unfolding within_multiplicity_def
      by simp
  qed
  then show "card {e \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} in 
    m_out (mult (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) et)"
    using mult_et_def
    by simp
next
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) p"
    unfolding ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def instance_graph_containment_proj_def pre_digraph.cycle_def pre_digraph.awalk_def
    by simp
qed (simp_all add: assms ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def)

lemma ig_enum_as_flags_field_as_edge_type_combine_correct:
  assumes "instance_graph IG"
  assumes existing_node_types: "NT (tg_enum_as_flags_field_as_edge_type classtype name enumid) \<subseteq> NT (TG IG)"
  assumes existing_inheritance: "inh (tg_enum_as_flags_field_as_edge_type classtype name enumid) \<subseteq> inh (TG IG)"
  assumes abstract_maintained: "abs (tg_enum_as_flags_field_as_edge_type classtype name enumid) \<subseteq> abs (TG IG)"
  assumes new_edge_type: "\<And>s l t. (type (id_to_list classtype), s) \<in> inh (TG IG) \<Longrightarrow> l = LabDef.edge [name] \<Longrightarrow> (s, l, t) \<notin> ET (TG IG)"
  assumes no_inh_classtype: "\<And>x. (x, type (id_to_list classtype)) \<in> inh (TG IG) \<Longrightarrow> x = type (id_to_list classtype)"
  assumes existing_objects: "N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) \<subseteq> N IG"
  assumes all_objects: "\<And>n. n \<in> N IG \<Longrightarrow> type\<^sub>n n = type (id_to_list classtype) \<Longrightarrow> n \<in> typed (type (id_to_list classtype)) ` objects"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_enum_ids: "\<And>ev1 ev2. ev1 \<in> enumvalues \<Longrightarrow> enumids ev1 = enumids ev2 \<Longrightarrow> ev1 = ev2"
  assumes unique_ids_set: "obids ` objects \<inter> enumids ` enumvalues = {}"
  assumes existing_ids: "obids ` objects \<union> enumids ` enumvalues \<subseteq> Id IG"
  assumes valid_ids: "\<And>i. i \<in> obids ` objects \<union> enumids ` enumvalues \<Longrightarrow> ident IG i = ident (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) i"
  assumes enum_class_neq: "id_to_list classtype \<noteq> id_to_list enumid"
  assumes valid_values: "\<And>ob. ob \<in> objects \<Longrightarrow> values ob \<in> enumvalues"
  shows "instance_graph (ig_combine IG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
proof (intro ig_combine_merge_no_containment_imod2_correct)
  show "instance_graph (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
    by (intro ig_enum_as_flags_field_as_edge_type_correct) (simp_all add: assms)
next
  have "type_graph (tg_combine (TG IG) (tg_enum_as_flags_field_as_edge_type classtype name enumid))"
  proof (intro tg_enum_as_flags_field_as_edge_type_combine_correct)
    fix s l t
    assume "(s, LabDef.type (id_to_list classtype)) \<in> inh (TG IG) \<or> (LabDef.type (id_to_list classtype), s) \<in> inh (TG IG)"
    then have s_def: "(LabDef.type (id_to_list classtype), s) \<in> inh (TG IG)"
      using no_inh_classtype
      by blast
    assume "l = LabDef.edge [name]"
    then show "(s, l, t) \<notin> ET (TG IG)"
      by (simp add: new_edge_type s_def)
  qed (simp_all add: assms instance_graph.validity_type_graph)
  then show "type_graph (tg_combine (TG IG) (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)))"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
next
  show "ET (TG IG) \<inter> ET (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) = {}"
    using existing_node_types
    unfolding ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def
    by (simp add: assms(1) instance_graph.validity_type_graph new_edge_type type_graph.validity_inh_node)
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have n_def: "n \<in> N IG"
    using existing_objects
    by blast
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG))\<^sup>+"
    using existing_inheritance
    by (simp add: Un_absorb2)
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  then show "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG) et)"
    using assms(1) et_def n_def instance_graph.validity_outgoing_mult
    by blast
next
  have instance_graph_valid: "instance_graph (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
    by (intro ig_enum_as_flags_field_as_edge_type_correct) (simp_all add: assms)
  fix et n
  assume et_in_ig: "et \<in> ET (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid))"
    unfolding ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def
    by simp
  assume n_def: "n \<in> N IG \<union> N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have "n \<in> N IG \<union> typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list enumid)) ` enumob ` enumvalues"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG))\<^sup>+"
    using existing_inheritance
    by (simp add: Un_absorb2)
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  then have "(type\<^sub>n n, type (id_to_list classtype)) \<in> inh (TG IG)"
    using et_def
    by simp
  then have type_n_def: "type\<^sub>n n = type (id_to_list classtype)"
    using no_inh_classtype
    by simp
  then have edge_extend_def: "(type\<^sub>n n, type (id_to_list classtype)) \<in> inh (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
    unfolding ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def
    by simp
  have "n \<in> typed (type (id_to_list classtype)) ` objects"
    using type_n_def all_objects n_def existing_objects
    by blast
  then have "n \<in> N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  then show "card {e \<in> E (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values). src e = n \<and> type\<^sub>e e = et} in 
    m_out (mult (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)) et)"
    using instance_graph_valid et_in_ig et_def edge_extend_def instance_graph.validity_outgoing_mult
    by fastforce
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
  then have n_def: "n \<in> N IG"
    using existing_objects
    by blast
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (TG (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (tg_enum_as_flags_field_as_edge_type classtype name enumid))\<^sup>+"
    unfolding ig_enum_as_flags_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG))\<^sup>+"
    using existing_inheritance
    by (simp add: Un_absorb2)
  then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  then show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG) et)"
    using assms(1) et_def n_def instance_graph.validity_ingoing_mult
    by blast
qed (simp_all add: ig_enum_as_flags_field_as_edge_type_def tg_enum_as_flags_field_as_edge_type_def assms)


subsection "Transformation functions"

definition imod_enum_field_to_ig_enum_as_flags_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> ('t \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "imod_enum_field_to_ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values Imod = \<lparr>
    TG = tg_enum_as_flags_field_as_edge_type classtype name enumid,
    Id = obids ` Object Imod \<union> enumids ` enumvalues,
    N = typed (type (id_to_list classtype)) ` Object Imod \<union> typed (type (id_to_list enumid)) ` enumob ` enumvalues,
    E = (\<lambda>x. (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list enumid)), typed (type (id_to_list enumid)) (enumob (values x)))) ` Object Imod,
    ident = (\<lambda>x. if x \<in> enumids ` enumvalues then typed (type (id_to_list enumid)) (enumob (THE y. enumids y = x)) else
      if x \<in> obids ` Object Imod then typed (type (id_to_list classtype)) (THE y. obids y = x) else undefined)
  \<rparr>"

lemma imod_enum_field_to_ig_enum_as_flags_field_as_edge_type_proj:
  shows "imod_enum_field_to_ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values (imod_enum_field classtype name enumid enumvalues objects obids values) = 
    ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values"
  unfolding imod_enum_field_to_ig_enum_as_flags_field_as_edge_type_def ig_enum_as_flags_field_as_edge_type_def imod_enum_field_def
  by auto

lemma imod_enum_field_to_ig_enum_as_flags_field_as_edge_type_func:
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_enum_ids: "\<And>ev1 ev2. ev1 \<in> enumvalues \<Longrightarrow> enumids ev1 = enumids ev2 \<Longrightarrow> ev1 = ev2"
  assumes unique_ids_set: "obids ` objects \<inter> enumids ` enumvalues = {}"
  shows "ig_combine_mapping_function (imod_enum_field_to_ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values)
    (imod_enum_field classtype name enumid enumvalues objects obids values) (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values)"
proof (intro ig_combine_mapping_function.intro)
  fix ImodX i
  assume "i \<in> Id (imod_enum_field_to_ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values (imod_enum_field classtype name enumid enumvalues objects obids values))"
  then have "i \<in> obids ` Object (imod_enum_field classtype name enumid enumvalues objects obids values) \<union> enumids ` enumvalues"
    unfolding imod_enum_field_to_ig_enum_as_flags_field_as_edge_type_def
    by simp
  then show "ident (imod_enum_field_to_ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values (imod_enum_field classtype name enumid enumvalues objects obids values)) i =
    ident (imod_enum_field_to_ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids obids values (imod_combine (imod_enum_field classtype name enumid enumvalues objects obids values) ImodX)) i"
    unfolding imod_enum_field_to_ig_enum_as_flags_field_as_edge_type_def imod_enum_field_def ig_enum_as_flags_field_as_edge_type_def imod_combine_def
    by fastforce
qed(auto simp add: imod_enum_field_to_ig_enum_as_flags_field_as_edge_type_def imod_enum_field_def ig_enum_as_flags_field_as_edge_type_def imod_combine_def)

definition ig_enum_as_flags_field_as_edge_type_to_imod_enum_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 't set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't list, 't) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "ig_enum_as_flags_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values IG = \<lparr>
    Tm = tmod_enum_field classtype name enumid enumvalues,
    Object = nodeId ` src ` E IG,
    ObjectClass = (\<lambda>x. if x \<in> nodeId ` src ` E IG then classtype else undefined),
    ObjectId = (\<lambda>x. if x \<in> nodeId ` src ` E IG then obids x else undefined),
    FieldValue = (\<lambda>x. if fst x \<in> nodeId ` src ` E IG \<and> snd x = (classtype, name) then enum (enumid, values (fst x)) else undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_enum_as_flags_field_as_edge_type_to_imod_enum_field_proj:
  shows "ig_enum_as_flags_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values 
    (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) = 
    imod_enum_field classtype name enumid enumvalues objects obids values"
proof-
  have "nodeId ` (\<lambda>x. typed (LabDef.type (id_to_list classtype)) x) ` objects = objects"
    by force
  then have "nodeId ` fst ` (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) x, 
    (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list enumid)), 
    typed (LabDef.type (id_to_list enumid)) (enumob (values x)))) ` objects = objects"
    by force
  then show "ig_enum_as_flags_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values 
    (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) = 
    imod_enum_field classtype name enumid enumvalues objects obids values"
    unfolding ig_enum_as_flags_field_as_edge_type_to_imod_enum_field_def imod_enum_field_def ig_enum_as_flags_field_as_edge_type_def
    by simp
qed

lemma ig_enum_as_flags_field_as_edge_type_to_imod_enum_field_func:
  shows "imod_combine_mapping_function (ig_enum_as_flags_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values)
    (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) (imod_enum_field classtype name enumid enumvalues objects obids values)"
proof-
  have "nodeId ` (\<lambda>x. typed (LabDef.type (id_to_list classtype)) x) ` objects = objects"
    by force
  then have "nodeId ` fst ` (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) x, 
    (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list enumid)), 
    typed (LabDef.type (id_to_list enumid)) (enumob (values x)))) ` objects = objects"
    by force
  then show "imod_combine_mapping_function (ig_enum_as_flags_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values)
    (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) (imod_enum_field classtype name enumid enumvalues objects obids values)"
  proof (intro imod_combine_mapping_function.intro)
    fix IGX
    show "Object (ig_enum_as_flags_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))
      \<subseteq> Object (ig_enum_as_flags_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values (ig_combine (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) IGX))"
    proof
      fix x
      assume "x \<in> Object (ig_enum_as_flags_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values))"
      then have "x \<in> objects"
        unfolding ig_enum_as_flags_field_as_edge_type_to_imod_enum_field_def imod_enum_field_def ig_enum_as_flags_field_as_edge_type_def ig_combine_def
        by fastforce
      then show "x \<in> Object (ig_enum_as_flags_field_as_edge_type_to_imod_enum_field classtype name enumid enumvalues obids values (ig_combine (ig_enum_as_flags_field_as_edge_type classtype name enumid enumvalues enumob enumids objects obids values) IGX))"
        unfolding ig_enum_as_flags_field_as_edge_type_to_imod_enum_field_def imod_enum_field_def ig_enum_as_flags_field_as_edge_type_def ig_combine_def
        by force
    qed
  qed (auto simp add: ig_enum_as_flags_field_as_edge_type_to_imod_enum_field_def imod_enum_field_def ig_enum_as_flags_field_as_edge_type_def ig_combine_def)
qed

end