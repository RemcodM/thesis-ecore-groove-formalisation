theory DataFieldValue
  imports
    Main
    "Ecore-GROOVE-Mapping.Instance_Model_Graph_Mapping"
    DataField
begin

section "Definition of an instance model which introduces values for a field typed by a data type"

fun datatype_to_literalvalue_set :: "'t TypeDef \<Rightarrow> ('o, 't) ValueDef set" where
  "datatype_to_literalvalue_set TypeDef.boolean = BooleanValue" |
  "datatype_to_literalvalue_set TypeDef.integer = IntegerValue" |
  "datatype_to_literalvalue_set TypeDef.real = RealValue" |
  "datatype_to_literalvalue_set TypeDef.string = StringValue" |
  "datatype_to_literalvalue_set _ = undefined"

definition imod_data_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't TypeDef \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> ('o, 't) ValueDef) \<Rightarrow> ('o, 't) instance_model" where
  "imod_data_field classtype name fieldtype objects obids values = \<lparr>
    Tm = tmod_data_field classtype name fieldtype,
    Object = objects,
    ObjectClass = (\<lambda>x. if x \<in> objects then classtype else undefined),
    ObjectId = (\<lambda>x. if x \<in> objects then obids x else undefined),
    FieldValue = (\<lambda>x. if fst x \<in> objects \<and> snd x = (classtype, name) then values (fst x) else undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_data_field_correct:
  assumes fieldtype_is_datatype: "fieldtype \<in> DataType"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> o2 \<in> objects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes valid_values: "\<And>ob. ob \<in> objects \<Longrightarrow> values ob \<in> datatype_to_literalvalue_set fieldtype"
  shows "instance_model (imod_data_field classtype name fieldtype objects obids values)"
proof (intro instance_model.intro)
  show "type_model (Tm (imod_data_field classtype name fieldtype objects obids values))"
    unfolding imod_data_field_def
    using tmod_data_field_correct fieldtype_is_datatype
    by simp
next
  fix ob f
  assume "ob \<notin> Object (imod_data_field classtype name fieldtype objects obids values) \<or> f \<notin> type_model.Field (Tm (imod_data_field classtype name fieldtype objects obids values))"
  then have "ob \<notin> objects \<or> f \<noteq> (classtype, name)"
    unfolding imod_data_field_def tmod_data_field_def
    by simp
  then show "FieldValue (imod_data_field classtype name fieldtype objects obids values) (ob, f) = undefined"
    unfolding imod_data_field_def
    by fastforce
next
  fix ob f
  assume "ob \<in> Object (imod_data_field classtype name fieldtype objects obids values)"
  then have ob_def: "ob \<in> objects"
    unfolding imod_data_field_def
    by simp
  then have ob_class_def: "ObjectClass (imod_data_field classtype name fieldtype objects obids values) ob = classtype"
    by (simp add: imod_data_field_def)
  then have "\<exclamdown>(ObjectClass (imod_data_field classtype name fieldtype objects obids values) ob) \<in> 
    ProperClassType (Tm (imod_data_field classtype name fieldtype objects obids values))"
    by (simp add: ProperClassType.rule_proper_classes imod_data_field_def tmod_data_field_def)
  then have ob_type_def: "\<exclamdown>(ObjectClass (imod_data_field classtype name fieldtype objects obids values) ob) \<in> 
    Type (Tm (imod_data_field classtype name fieldtype objects obids values))"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  assume "f \<in> type_model.Field (Tm (imod_data_field classtype name fieldtype objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_data_field_def tmod_data_field_def
    by simp
  then have "ObjectClass (imod_data_field classtype name fieldtype objects obids values) ob = 
    class (Tm (imod_data_field classtype name fieldtype objects obids values)) f"
    unfolding class_def
    by (simp add: ob_class_def)
  then have extend: "\<exclamdown>(ObjectClass (imod_data_field classtype name fieldtype objects obids values) ob) 
    \<sqsubseteq>[Tm (imod_data_field classtype name fieldtype objects obids values)] 
    \<exclamdown>(class (Tm (imod_data_field classtype name fieldtype objects obids values)) f)"
    unfolding subtype_def
    using ob_type_def subtype_rel.reflexivity
    by simp
  assume "\<not>\<exclamdown>(ObjectClass (imod_data_field classtype name fieldtype objects obids values) ob) 
    \<sqsubseteq>[Tm (imod_data_field classtype name fieldtype objects obids values)] 
    \<exclamdown>(class (Tm (imod_data_field classtype name fieldtype objects obids values)) f)"
  then show "FieldValue (imod_data_field classtype name fieldtype objects obids values) (ob, f) = unspecified"
    using extend
    by blast
next
  fix ob f
  assume "ob \<in> Object (imod_data_field classtype name fieldtype objects obids values)"
  then have ob_def: "ob \<in> objects"
    unfolding imod_data_field_def
    by simp
  assume "f \<in> type_model.Field (Tm (imod_data_field classtype name fieldtype objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_data_field_def tmod_data_field_def
    by simp
  then have f_type: "Type_Model.type (Tm (imod_data_field classtype name fieldtype objects obids values)) f = fieldtype"
    unfolding Type_Model.type_def imod_data_field_def tmod_data_field_def
    by simp
  have f_lower: "lower (Tm (imod_data_field classtype name fieldtype objects obids values)) f = \<^bold>1"
    unfolding lower_def imod_data_field_def tmod_data_field_def
    using f_def
    by simp
  have f_upper: "upper (Tm (imod_data_field classtype name fieldtype objects obids values)) f = \<^bold>1"
    unfolding upper_def imod_data_field_def tmod_data_field_def
    using f_def
    by simp
  have value_def: "FieldValue (imod_data_field classtype name fieldtype objects obids values) (ob, f) = values ob"
    unfolding imod_data_field_def
    using f_def ob_def
    by simp
  have fieldvalue_cases: "fieldtype = TypeDef.boolean \<or> fieldtype = TypeDef.integer \<or> fieldtype = TypeDef.real \<or> fieldtype = TypeDef.string"
    using fieldtype_is_datatype
    unfolding DataType_def
    by blast
  then have value_valid: "values ob :[imod_data_field classtype name fieldtype objects obids values] fieldtype"
  proof (elim disjE)
    assume fieldtype_def: "fieldtype = TypeDef.boolean"
    then have "values ob \<in> BooleanValue"
      using datatype_to_literalvalue_set.simps(1) ob_def valid_values
      by blast
    then have "(TypeDef.boolean, values ob) \<in> Valid_rel (imod_data_field classtype name fieldtype objects obids values)"
      by (fact Valid_rel.valid_rule_booleans)
    then show ?thesis
      unfolding Valid_def
      by (simp add: fieldtype_def)
  next
    assume fieldtype_def: "fieldtype = TypeDef.integer"
    then have "values ob \<in> IntegerValue"
      using datatype_to_literalvalue_set.simps(2) ob_def valid_values
      by blast
    then have "(TypeDef.integer, values ob) \<in> Valid_rel (imod_data_field classtype name fieldtype objects obids values)"
      by (fact Valid_rel.valid_rule_integers)
    then show ?thesis
      unfolding Valid_def
      by (simp add: fieldtype_def)
  next
    assume fieldtype_def: "fieldtype = TypeDef.real"
    then have "values ob \<in> RealValue"
      using datatype_to_literalvalue_set.simps(3) ob_def valid_values
      by blast
    then have "(TypeDef.real, values ob) \<in> Valid_rel (imod_data_field classtype name fieldtype objects obids values)"
      by (fact Valid_rel.valid_rule_reals)
    then show ?thesis
      unfolding Valid_def
      by (simp add: fieldtype_def)
  next
    assume fieldtype_def: "fieldtype = TypeDef.string"
    then have "values ob \<in> StringValue"
      using datatype_to_literalvalue_set.simps(4) ob_def valid_values
      by blast
    then have "(TypeDef.string, values ob) \<in> Valid_rel (imod_data_field classtype name fieldtype objects obids values)"
      by (fact Valid_rel.valid_rule_strings)
    then show ?thesis
      unfolding Valid_def
      by (simp add: fieldtype_def)
  qed
  then show "FieldValue (imod_data_field classtype name fieldtype objects obids values) (ob, f) 
    :[imod_data_field classtype name fieldtype objects obids values] 
    Type_Model.type (Tm (imod_data_field classtype name fieldtype objects obids values)) f"
    using value_def f_type
    by simp
  have values_are_literal_values: "values ob \<in> LiteralValue"
    using fieldvalue_cases
  proof (elim disjE)
    assume fieldtype_def: "fieldtype = TypeDef.boolean"
    then have "values ob \<in> BooleanValue"
      using datatype_to_literalvalue_set.simps(1) ob_def valid_values
      by blast
    then show ?thesis
      unfolding LiteralValue_def
      by simp
  next
    assume fieldtype_def: "fieldtype = TypeDef.integer"
    then have "values ob \<in> IntegerValue"
      using datatype_to_literalvalue_set.simps(2) ob_def valid_values
      by blast
    then show ?thesis
      unfolding LiteralValue_def
      by simp
  next
    assume fieldtype_def: "fieldtype = TypeDef.real"
    then have "values ob \<in> RealValue"
      using datatype_to_literalvalue_set.simps(3) ob_def valid_values
      by blast
    then show ?thesis
      unfolding LiteralValue_def
      by simp
  next
    assume fieldtype_def: "fieldtype = TypeDef.string"
    then have "values ob \<in> StringValue"
      using datatype_to_literalvalue_set.simps(4) ob_def valid_values
      by blast
    then show ?thesis
      unfolding LiteralValue_def
      by simp
  qed
  then show "FieldValue (imod_data_field classtype name fieldtype objects obids values) (ob, f) \<in>
    Value (imod_data_field classtype name fieldtype objects obids values)"
    unfolding Value_def AtomValue_def
    by (simp add: value_def)
  have "validMul (imod_data_field classtype name fieldtype objects obids values) ((ob, f), values ob)"
    unfolding validMul_def
  proof (intro conjI)
    show "snd ((ob, f), values ob) \<in> ContainerValue (imod_data_field classtype name fieldtype objects obids values) \<longrightarrow>
      lower (Tm (imod_data_field classtype name fieldtype objects obids values)) (snd (fst ((ob, f), values ob))) \<le> \<^bold>(length (contained_list (snd ((ob, f), values ob)))) \<and>
      \<^bold>(length (contained_list (snd ((ob, f), values ob)))) \<le> upper (Tm (imod_data_field classtype name fieldtype objects obids values)) (snd (fst ((ob, f), values ob)))"
    proof
      assume "snd ((ob, f), values ob) \<in> ContainerValue (imod_data_field classtype name fieldtype objects obids values)"
      then have "values ob \<in> ContainerValue (imod_data_field classtype name fieldtype objects obids values)"
        by simp
      then show "lower (Tm (imod_data_field classtype name fieldtype objects obids values)) (snd (fst ((ob, f), values ob))) \<le> \<^bold>(length (contained_list (snd ((ob, f), values ob)))) \<and>
        \<^bold>(length (contained_list (snd ((ob, f), values ob)))) \<le> upper (Tm (imod_data_field classtype name fieldtype objects obids values)) (snd (fst ((ob, f), values ob)))"
        using values_are_literal_values container_values_literal_values_intersect
        by blast
    qed
  qed (simp_all add: value_valid f_type)
  then show "validMul (imod_data_field classtype name fieldtype objects obids values) ((ob, f), FieldValue (imod_data_field classtype name fieldtype objects obids values) (ob, f))"
    by (simp add: value_def)
qed (simp_all add: assms imod_data_field_def tmod_data_field_def)

lemma imod_data_field_combine_correct:
  assumes "instance_model Imod"
  assumes fieldtype_is_datatype: "fieldtype \<in> DataType"
  assumes existing_class: "classtype \<in> Class (Tm Imod)"
  assumes new_field: "(classtype, name) \<notin> Field (Tm Imod)"
  assumes no_inh_classtype: "\<And>x. (x, classtype) \<notin> Inh (Tm Imod)"
  assumes existing_objects: "objects \<inter> Object Imod = objects"
  assumes all_objects: "\<And>ob. ob \<in> Object Imod \<Longrightarrow> ObjectClass Imod ob = classtype \<longleftrightarrow> ob \<in> objects"
  assumes ids_valid: "\<And>ob. ob \<in> objects \<Longrightarrow> ObjectId Imod ob = obids ob"
  assumes valid_values: "\<And>ob. ob \<in> objects \<Longrightarrow> values ob \<in> datatype_to_literalvalue_set fieldtype"
  shows "instance_model (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values))"
proof (intro imod_combine_merge_no_containment_imod2_correct)
  have "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> o2 \<in> objects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  proof-
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
  qed
  then show "instance_model (imod_data_field classtype name fieldtype objects obids values)"
    using fieldtype_is_datatype valid_values imod_data_field_correct
    by metis
next
  fix ob
  assume "ob \<in> Object (imod_data_field classtype name fieldtype objects obids values)"
  then have ob_in_objects: "ob \<in> objects"
    unfolding imod_data_field_def
    by simp
  then have "ObjectId (imod_data_field classtype name fieldtype objects obids values) ob = obids ob"
    unfolding imod_data_field_def
    by simp
  then show "ObjectId Imod ob = ObjectId (imod_data_field classtype name fieldtype objects obids values) ob"
    by (simp add: ids_valid ob_in_objects)
next
  fix o1 o2
  assume "o1 \<in> Object Imod - Object (imod_data_field classtype name fieldtype objects obids values)"
  assume "o2 \<in> Object (imod_data_field classtype name fieldtype objects obids values) - Object Imod"
  then have "o2 \<in> objects - Object Imod"
    unfolding imod_data_field_def
    by simp
  then have "o2 \<in> {}"
    using existing_objects
    by blast
  then show "o1 = o2"
    by blast
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    using tmod_data_field_combine_correct assms(1) instance_model.validity_type_model_consistent fieldtype_is_datatype existing_class new_field
    by metis
  fix ob f
  assume ob_def: "ob \<in> Object Imod"
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values)) ob = ObjectClass Imod ob"
    by (simp add: all_objects imod_combine_def imod_combine_object_class_def imod_data_field_def)
  assume "f \<in> Field (Tm (imod_data_field classtype name fieldtype objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_data_field_def tmod_data_field_def
    by simp
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values))) f)"
  then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values))] \<exclamdown>classtype"
    unfolding class_def
    using ob_class_def f_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    unfolding subtype_def imod_data_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have ob_class_is_classtype: "\<exclamdown>(ObjectClass Imod ob) = \<exclamdown>classtype"
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    then show ?thesis
      unfolding subtype_tuple_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
    then have ob_extends_classtype: "(ObjectClass Imod ob, classtype) \<in> (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
      unfolding subtype_conv_def
      by fastforce
    have "(ObjectClass Imod ob, classtype) \<notin> (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
    proof
      assume "(ObjectClass Imod ob, classtype) \<in> (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
      then show "False"
      proof (cases)
        case base
        then show ?thesis
          unfolding tmod_data_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      next
        case (step c)
        then show ?thesis
          unfolding tmod_data_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      qed
    qed
    then show ?thesis
      using ob_extends_classtype
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then have ob_in_objects: "ob \<in> objects"
    using all_objects ob_def
    by blast
  have "\<exclamdown>classtype \<in> ProperClassType (tmod_data_field classtype name fieldtype)"
    unfolding tmod_data_field_def
    by (simp add: ProperClassType.rule_proper_classes)
  then have "\<exclamdown>classtype \<in> Type (tmod_data_field classtype name fieldtype)"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  then show "ob \<in> Object (imod_data_field classtype name fieldtype objects obids values) \<and>
    \<exclamdown>(ObjectClass (imod_data_field classtype name fieldtype objects obids values) ob) 
    \<sqsubseteq>[Tm (imod_data_field classtype name fieldtype objects obids values)]
    \<exclamdown>(class (Tm (imod_data_field classtype name fieldtype objects obids values)) f)"
    unfolding imod_data_field_def class_def subtype_def
    using ob_in_objects f_def
    by (simp add: subtype_rel.reflexivity)
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    using tmod_data_field_combine_correct assms(1) instance_model.validity_type_model_consistent fieldtype_is_datatype existing_class new_field
    by metis
  fix ob f
  assume "ob \<in> Object (imod_data_field classtype name fieldtype objects obids values)"
  then have ob_def: "ob \<in> objects"
    unfolding imod_data_field_def
    by simp
  then have ob_in_imod: "ob \<in> Object Imod"
    using existing_objects
    by blast
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values)) ob = classtype"
    unfolding imod_combine_def imod_data_field_def imod_combine_object_class_def
    using ob_def all_objects
    by simp
  assume f_def: "f \<in> Field (Tm Imod)"
  have "\<exclamdown>classtype \<in> ProperClassType (Tm Imod)"
    using existing_class
    by (simp add: ProperClassType.rule_proper_classes)
  then have classtype_is_type: "\<exclamdown>classtype \<in> Type (Tm Imod)"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values))) f)"
  then have "\<exclamdown>classtype \<sqsubseteq>[Tm (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values))] \<exclamdown>(fst f)"
    unfolding class_def
    using ob_class_def
    by simp
  then have "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    unfolding subtype_def imod_data_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+ \<union>
    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
  proof (elim UnE)
    assume "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
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
    assume "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
    then have "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
      unfolding subtype_conv_def tmod_combine_def tmod_data_field_def
      by simp
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by simp
  next
    assume "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>classtype, \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
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
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    using tmod_data_field_combine_correct assms(1) instance_model.validity_type_model_consistent fieldtype_is_datatype existing_class new_field
    by metis
  fix ob f
  assume ob_def: "ob \<in> Object Imod"
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values)) ob = ObjectClass Imod ob"
    unfolding imod_combine_def imod_data_field_def imod_combine_object_class_def
    by (simp add: all_objects)
  then have "ObjectClass Imod ob \<in> Class (Tm Imod)"
    by (simp add: assms(1) instance_model.structure_object_class_wellformed ob_def)
  then have "\<exclamdown>(ObjectClass Imod ob) \<in> ProperClassType (Tm Imod)"
    by (fact ProperClassType.rule_proper_classes)
  then have ob_class_is_type: "\<exclamdown>(ObjectClass Imod ob) \<in> Type (Tm Imod)"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  assume f_def: "f \<in> Field (Tm Imod)"
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values))) f)"
  then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (imod_combine Imod (imod_data_field classtype name fieldtype objects obids values))] \<exclamdown>(fst f)"
    unfolding class_def
    using ob_class_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    unfolding subtype_def imod_data_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+ \<union>
    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
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
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
      unfolding subtype_conv_def tmod_combine_def tmod_data_field_def
      by simp
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by simp
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then show "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (Imod)] \<exclamdown>(class (Tm Imod) f)"
    unfolding subtype_def class_def
    by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    using tmod_data_field_combine_correct assms(1) instance_model.validity_type_model_consistent fieldtype_is_datatype existing_class new_field
    by metis
  fix ob f
  assume "ob \<in> Object (imod_data_field classtype name fieldtype objects obids values)"
  then have ob_def: "ob \<in> objects"
    unfolding imod_data_field_def
    by simp
  then have ob_class_def: "ObjectClass (imod_data_field classtype name fieldtype objects obids values) ob = classtype"
    unfolding imod_combine_def imod_data_field_def imod_combine_object_class_def
    using ob_def all_objects
    by simp
  assume "f \<in> Field (Tm (imod_data_field classtype name fieldtype objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_data_field_def tmod_data_field_def
    by simp
  have "\<exclamdown>classtype \<in> ProperClassType (Tm (imod_data_field classtype name fieldtype objects obids values))"
    unfolding imod_data_field_def tmod_data_field_def
    by (simp add: ProperClassType.rule_proper_classes)
  then have "\<exclamdown>classtype \<in> Type (Tm (imod_data_field classtype name fieldtype objects obids values))"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  then have "\<exclamdown>classtype \<sqsubseteq>[Tm (imod_data_field classtype name fieldtype objects obids values)] \<exclamdown>classtype"
    unfolding subtype_def
    by (simp add: subtype_rel.reflexivity)
  then show "\<exclamdown>(ObjectClass (imod_data_field classtype name fieldtype objects obids values) ob)
    \<sqsubseteq>[Tm (imod_data_field classtype name fieldtype objects obids values)]
    \<exclamdown>(class (Tm (imod_data_field classtype name fieldtype objects obids values)) f)"
    unfolding imod_data_field_def class_def
    by (simp add: f_def ob_def)
next
  have "type_model (tmod_combine (Tm Imod) (tmod_data_field classtype name fieldtype))"
    using tmod_data_field_combine_correct assms(1) instance_model.validity_type_model_consistent fieldtype_is_datatype existing_class new_field
    by metis
  then show "type_model (tmod_combine (Tm Imod) (Tm (imod_data_field classtype name fieldtype objects obids values)))"
    unfolding imod_data_field_def
    by simp
qed (simp_all add: assms imod_data_field_def tmod_data_field_def)



section "Encoding of a Class as Node Type in GROOVE"

fun literalvalue_to_labdef :: "('o, 't) ValueDef \<Rightarrow> ('o, 't list) NodeDef" where
  "literalvalue_to_labdef (ValueDef.bool b) = NodeDef.bool b" |
  "literalvalue_to_labdef (ValueDef.int i) = NodeDef.int i" |
  "literalvalue_to_labdef (ValueDef.real r) = NodeDef.real r" |
  "literalvalue_to_labdef (ValueDef.string s) = NodeDef.string s" |
  "literalvalue_to_labdef _ = undefined"

fun labdef_to_literalvalue :: "('o, 't list) NodeDef \<Rightarrow> ('o, 't) ValueDef" where
  "labdef_to_literalvalue (NodeDef.bool b) = ValueDef.bool b" |
  "labdef_to_literalvalue (NodeDef.int i) = ValueDef.int i" |
  "labdef_to_literalvalue (NodeDef.real r) = ValueDef.real r" |
  "labdef_to_literalvalue (NodeDef.string s) = ValueDef.string s" |
  "labdef_to_literalvalue _ = undefined"

definition ig_data_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't TypeDef \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> ('o, 't) ValueDef) \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "ig_data_field_as_edge_type classtype name fieldtype objects obids values = \<lparr>
    TG = tg_data_field_as_edge_type classtype name fieldtype,
    Id = obids ` objects,
    N = typed (type (id_to_list classtype)) ` objects \<union> literalvalue_to_labdef ` values ` objects,
    E = (\<lambda>x. (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))) ` objects,
    ident = (\<lambda>x. if x \<in> obids ` objects then typed (type (id_to_list classtype)) (THE y. obids y = x) else undefined)
  \<rparr>"

lemma ig_data_field_as_edge_type_correct:
  assumes fieldtype_is_datatype: "fieldtype \<in> DataType"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes valid_values: "\<And>ob. ob \<in> objects \<Longrightarrow> values ob \<in> datatype_to_literalvalue_set fieldtype"
  shows "instance_graph (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
proof (intro instance_graph.intro)
  fix n
  assume "n \<in> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
  then have "n \<in> typed (type (id_to_list classtype)) ` objects \<union> literalvalue_to_labdef ` values ` objects"
    unfolding ig_data_field_as_edge_type_def
    by simp
  then have type_and_node_def: "type\<^sub>n n \<in> NT (tg_data_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
  proof
    assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
    then show "type\<^sub>n n \<in> NT (tg_data_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
    proof (intro conjI)
      assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
      then show "type\<^sub>n n \<in> NT (tg_data_field_as_edge_type classtype name fieldtype)"
        unfolding tg_data_field_as_edge_type_def
        by fastforce
    next
      assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
      then show "n \<in> Node"
        unfolding Node_def
        using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
        by fastforce
    qed
  next
    assume "n \<in> literalvalue_to_labdef ` values ` objects"
    then show "type\<^sub>n n \<in> NT (tg_data_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
    proof (elim imageE)
      fix a b
      assume a_def: "a \<in> objects"
      assume b_def: "b = values a"
      assume "n = literalvalue_to_labdef b"
      then have n_def: "n = literalvalue_to_labdef (values a)"
        by (simp add: b_def)
      have fieldvalue_cases: "fieldtype = TypeDef.boolean \<or> fieldtype = TypeDef.integer \<or> fieldtype = TypeDef.real \<or> fieldtype = TypeDef.string"
        using fieldtype_is_datatype
        unfolding DataType_def
        by blast
      then show "type\<^sub>n n \<in> NT (tg_data_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
      proof (elim disjE)
        assume fieldtype_def: "fieldtype = TypeDef.boolean"
        then have "(values a) \<in> BooleanValue"
          using a_def datatype_to_literalvalue_set.simps(1) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> BooleanNode\<^sub>v"
          unfolding BooleanNode\<^sub>v_def
          by (induct rule: BooleanValue.induct) (simp_all)
        then have n_in_values: "n \<in> BooleanNode\<^sub>v"
          by (simp add: n_def)
        then have "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
        then show "type\<^sub>n n \<in> NT (tg_data_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
          unfolding tg_data_field_as_edge_type_def Node_def Node\<^sub>v_def
          by (simp add: n_in_values)
      next
        assume fieldtype_def: "fieldtype = TypeDef.integer"
        then have "(values a) \<in> IntegerValue"
          using a_def datatype_to_literalvalue_set.simps(2) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> IntegerNode\<^sub>v"
          by (induct rule: IntegerValue.induct) (simp add: IntegerNode\<^sub>v.rule_integer_nodes)
        then have n_in_values: "n \<in> IntegerNode\<^sub>v"
          by (simp add: n_def)
        then have "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
        then show "type\<^sub>n n \<in> NT (tg_data_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
          unfolding tg_data_field_as_edge_type_def Node_def Node\<^sub>v_def
          by (simp add: n_in_values)
      next
        assume fieldtype_def: "fieldtype = TypeDef.real"
        then have "(values a) \<in> RealValue"
          using a_def datatype_to_literalvalue_set.simps(3) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> RealNode\<^sub>v"
          by (induct rule: RealValue.induct) (simp add: RealNode\<^sub>v.rule_real_nodes)
        then have n_in_values: "n \<in> RealNode\<^sub>v"
          by (simp add: n_def)
        then have "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
        then show "type\<^sub>n n \<in> NT (tg_data_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
          unfolding tg_data_field_as_edge_type_def Node_def Node\<^sub>v_def
          by (simp add: n_in_values)
      next
        assume fieldtype_def: "fieldtype = TypeDef.string"
        then have "(values a) \<in> StringValue"
          using a_def datatype_to_literalvalue_set.simps(4) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> StringNode\<^sub>v"
          by (induct rule: StringValue.induct) (simp add: StringNode\<^sub>v.rule_string_nodes)
        then have n_in_values: "n \<in> StringNode\<^sub>v"
          by (simp add: n_def)
        then have "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
        then show "type\<^sub>n n \<in> NT (tg_data_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
          unfolding tg_data_field_as_edge_type_def Node_def Node\<^sub>v_def
          by (simp add: n_in_values)
      qed
    qed
  qed
  then show "type\<^sub>n n \<in> NT (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values))"
    unfolding ig_data_field_as_edge_type_def
    by simp
  show "n \<in> Node"
    by (simp add: type_and_node_def)
next
  fix s l t
  assume "(s, l, t) \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
  then have edge_def: "(s, l, t) \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))) ` objects"
    unfolding ig_data_field_as_edge_type_def
    by simp
  show "s \<in> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values) \<and> 
    l \<in> ET (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values)) \<and> 
    t \<in> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
  proof (intro conjI)
    show "s \<in> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
      unfolding ig_data_field_as_edge_type_def
      using edge_def
      by fastforce
  next
    have "l = (type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype)"
      using edge_def
      by blast
    then show "l \<in> ET (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values))"
      unfolding ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def
      by simp
  next
    show "t \<in> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
      unfolding ig_data_field_as_edge_type_def
      using edge_def
      by fastforce
  qed
next
  fix i
  assume "i \<in> Id (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
  then have i_in_id: "i \<in> obids ` objects"
    unfolding ig_data_field_as_edge_type_def
    by simp
  then show "ident (ig_data_field_as_edge_type classtype name fieldtype objects obids values) i \<in> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values) \<and> 
    type\<^sub>n (ident (ig_data_field_as_edge_type classtype name fieldtype objects obids values) i) \<in> Lab\<^sub>t"
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
    then show "ident (ig_data_field_as_edge_type classtype name fieldtype objects obids values) i \<in> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
      unfolding ig_data_field_as_edge_type_def
      using i_in_id
      by simp
  next
    have "type\<^sub>n (typed (type (id_to_list classtype)) (THE y. obids y = i)) \<in> Lab\<^sub>t"
      by (simp add: Lab\<^sub>t.rule_type_labels)
    then show "type\<^sub>n (ident (ig_data_field_as_edge_type classtype name fieldtype objects obids values) i) \<in> Lab\<^sub>t"
      unfolding ig_data_field_as_edge_type_def
      using i_in_id
      by simp
  qed
next
  show "type_graph (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values))"
    unfolding ig_data_field_as_edge_type_def
    using fieldtype_is_datatype tg_data_field_as_edge_type_correct
    by simp
next
  fix e
  assume "e \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))) ` objects"
    unfolding ig_data_field_as_edge_type_def
    by simp
  have type_n_def: "type\<^sub>n (src e) = type (id_to_list classtype)"
    using e_def
    by fastforce
  have type_e_def: "src (type\<^sub>e e) = type (id_to_list classtype)"
    using e_def
    by fastforce
  have "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> {(type (id_to_list classtype), type (id_to_list classtype)), (datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
    using type_n_def type_e_def
    by blast
  then show "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values))"
    unfolding ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def
    by simp
next
  fix e
  assume "e \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))) ` objects"
    unfolding ig_data_field_as_edge_type_def
    by simp
  have type_n_def: "type\<^sub>n (tgt e) = datatype_to_labdef fieldtype"
    using e_def
  proof (elim imageE)
    fix x
    assume x_in_objects: "x \<in> objects"
    assume e_def: "e = (typed (LabDef.type (id_to_list classtype)) x, (LabDef.type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))"
    have "fieldtype = TypeDef.boolean \<or> fieldtype = TypeDef.integer \<or> fieldtype = TypeDef.real \<or> fieldtype = TypeDef.string"
      using fieldtype_is_datatype
      unfolding DataType_def
      by blast
    then show ?thesis
    proof (elim disjE)
      assume fieldtype_def: "fieldtype = TypeDef.boolean"
      then have "(values x) \<in> BooleanValue"
        using x_in_objects datatype_to_literalvalue_set.simps(1) valid_values
        by blast
      then have "literalvalue_to_labdef (values x) \<in> BooleanNode\<^sub>v"
        unfolding BooleanNode\<^sub>v_def
        by (induct rule: BooleanValue.induct) (simp_all)
      then have n_in_values: "tgt e \<in> BooleanNode\<^sub>v"
        by (simp add: e_def)
      then show "type\<^sub>n (tgt e) = datatype_to_labdef fieldtype"
        by (simp add: fieldtype_def)
    next
      assume fieldtype_def: "fieldtype = TypeDef.integer"
      then have "(values x) \<in> IntegerValue"
        using x_in_objects datatype_to_literalvalue_set.simps(2) valid_values
        by blast
      then have "literalvalue_to_labdef (values x) \<in> IntegerNode\<^sub>v"
        by (induct rule: IntegerValue.induct) (simp add: IntegerNode\<^sub>v.rule_integer_nodes)
      then have n_in_values: "(tgt e) \<in> IntegerNode\<^sub>v"
        by (simp add: e_def)
      then show "type\<^sub>n (tgt e) = datatype_to_labdef fieldtype"
        by (simp add: fieldtype_def)
    next
      assume fieldtype_def: "fieldtype = TypeDef.real"
      then have "(values x) \<in> RealValue"
        using x_in_objects datatype_to_literalvalue_set.simps(3) valid_values
        by blast
      then have "literalvalue_to_labdef (values x) \<in> RealNode\<^sub>v"
        by (induct rule: RealValue.induct) (simp add: RealNode\<^sub>v.rule_real_nodes)
      then have n_in_values: "(tgt e) \<in> RealNode\<^sub>v"
        by (simp add: e_def)
      then show "type\<^sub>n (tgt e) = datatype_to_labdef fieldtype"
        by (simp add: fieldtype_def)
    next
      assume fieldtype_def: "fieldtype = TypeDef.string"
      then have "(values x) \<in> StringValue"
        using x_in_objects datatype_to_literalvalue_set.simps(4) valid_values
        by blast
      then have "literalvalue_to_labdef (values x) \<in> StringNode\<^sub>v"
        by (induct rule: StringValue.induct) (simp add: StringNode\<^sub>v.rule_string_nodes)
      then have n_in_values: "(tgt e) \<in> StringNode\<^sub>v"
        by (simp add: e_def)
      then show "type\<^sub>n (tgt e) = datatype_to_labdef fieldtype"
        by (simp add: fieldtype_def)
    qed
  qed
  have type_e_def: "tgt (type\<^sub>e e) = datatype_to_labdef fieldtype"
    using e_def
    by fastforce
  have "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> {(type (id_to_list classtype), type (id_to_list classtype)), (datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
    using type_n_def type_e_def
    by blast
  then show "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values))"
    unfolding ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def
    by simp
next
  fix et n
  assume "et \<in> ET (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype)"
    unfolding ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def
    by simp
  then have src_et_def: "src et = type (id_to_list classtype)"
    by simp
  have mult_et_def: "m_out (mult (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values)) et) = \<^bold>1..\<^bold>1"
    unfolding ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def
    by (simp add: et_def)
  assume "n \<in> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
  then have n_def: "n \<in> typed (type (id_to_list classtype)) ` objects \<union> literalvalue_to_labdef ` values ` objects"
    unfolding ig_data_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> inh (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values))"
  then have "(type\<^sub>n n, src et) \<in> {(type (id_to_list classtype), type (id_to_list classtype)), (datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
    unfolding ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def
    by simp
  then have type_n_def: "type\<^sub>n n = type (id_to_list classtype)"
    using src_et_def
    by fastforce
  have "n \<in> typed (type (id_to_list classtype)) ` objects"
    using n_def
  proof (elim UnE)
    assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
    then show "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
      by simp
  next
    assume "n \<in> literalvalue_to_labdef ` values ` objects"
    then show "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
    proof (elim imageE)
      fix a b
      assume a_def: "a \<in> objects"
      assume b_def: "b = values a"
      assume "n = literalvalue_to_labdef b"
      then have n_def: "n = literalvalue_to_labdef (values a)"
        by (simp add: b_def)
      have fieldvalue_cases: "fieldtype = TypeDef.boolean \<or> fieldtype = TypeDef.integer \<or> fieldtype = TypeDef.real \<or> fieldtype = TypeDef.string"
        using fieldtype_is_datatype
        unfolding DataType_def
        by blast
      then show ?thesis
      proof (elim disjE)
        assume fieldtype_def: "fieldtype = TypeDef.boolean"
        then have "(values a) \<in> BooleanValue"
          using a_def datatype_to_literalvalue_set.simps(1) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> BooleanNode\<^sub>v"
          unfolding BooleanNode\<^sub>v_def
          by (induct rule: BooleanValue.induct) (simp_all)
        then have n_in_values: "n \<in> BooleanNode\<^sub>v"
          by (simp add: n_def)
        then have "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
        then have "type\<^sub>n n = LabDef.bool"
          by (simp add: fieldtype_def)
        then show ?thesis
          using type_n_def
          by simp
      next
        assume fieldtype_def: "fieldtype = TypeDef.integer"
        then have "(values a) \<in> IntegerValue"
          using a_def datatype_to_literalvalue_set.simps(2) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> IntegerNode\<^sub>v"
          by (induct rule: IntegerValue.induct) (simp add: IntegerNode\<^sub>v.rule_integer_nodes)
        then have n_in_values: "n \<in> IntegerNode\<^sub>v"
          by (simp add: n_def)
        then have "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
        then have "type\<^sub>n n = LabDef.int"
          by (simp add: fieldtype_def)
        then show ?thesis
          using type_n_def
          by simp
      next
        assume fieldtype_def: "fieldtype = TypeDef.real"
        then have "(values a) \<in> RealValue"
          using a_def datatype_to_literalvalue_set.simps(3) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> RealNode\<^sub>v"
          by (induct rule: RealValue.induct) (simp add: RealNode\<^sub>v.rule_real_nodes)
        then have n_in_values: "n \<in> RealNode\<^sub>v"
          by (simp add: n_def)
        then have "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
        then have "type\<^sub>n n = LabDef.real"
          by (simp add: fieldtype_def)
        then show ?thesis
          using type_n_def
          by simp
      next
        assume fieldtype_def: "fieldtype = TypeDef.string"
        then have "(values a) \<in> StringValue"
          using a_def datatype_to_literalvalue_set.simps(4) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> StringNode\<^sub>v"
          by (induct rule: StringValue.induct) (simp add: StringNode\<^sub>v.rule_string_nodes)
        then have n_in_values: "n \<in> StringNode\<^sub>v"
          by (simp add: n_def)
        then have "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
        then have "type\<^sub>n n = LabDef.string"
          by (simp add: fieldtype_def)
        then show ?thesis
          using type_n_def
          by simp
      qed
    qed
  qed
  then have "card {e \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values). src e = n \<and> type\<^sub>e e = et} in \<^bold>1..\<^bold>1"
  proof (elim imageE)
    fix x
    assume x_def: "x \<in> objects"
    assume n_def: "n = typed (LabDef.type (id_to_list classtype)) x"
    have "{e \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values). src e = n \<and> type\<^sub>e e = et} = 
      {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))}"
    proof
      show "{e \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values). src e = n \<and> type\<^sub>e e = et} \<subseteq> 
        {(typed (LabDef.type (id_to_list classtype)) x, (LabDef.type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))}"
      proof
        fix y
        assume "y \<in> {e \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values). src e = n \<and> type\<^sub>e e = et}"
        then show "y \<in> {(typed (LabDef.type (id_to_list classtype)) x, (LabDef.type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))}"
        proof
          assume "y \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values) \<and> src y = n \<and> type\<^sub>e y = et"
          then show "y \<in> {(typed (LabDef.type (id_to_list classtype)) x, (LabDef.type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))}"
            unfolding ig_data_field_as_edge_type_def
            using et_def n_def
            by fastforce
        qed
      qed
    next
      show "{(typed (LabDef.type (id_to_list classtype)) x, (LabDef.type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))} \<subseteq> 
        {e \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values). src e = n \<and> type\<^sub>e e = et}"
      proof
        fix y
        assume "y \<in> {(typed (LabDef.type (id_to_list classtype)) x, (LabDef.type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))}"
        then have "y = (typed (LabDef.type (id_to_list classtype)) x, (LabDef.type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))"
          by simp
        then show "y \<in> {e \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values). src e = n \<and> type\<^sub>e e = et}"
          unfolding ig_data_field_as_edge_type_def
          using et_def n_def x_def
          by simp
      qed
    qed
    then have "card {e \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values). src e = n \<and> type\<^sub>e e = et} = 1"
      by simp
    then show ?thesis
      unfolding within_multiplicity_def
      by simp
  qed
  then show "card {e \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values). src e = n \<and> type\<^sub>e e = et} in 
    m_out (mult (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values)) et)"
    using mult_et_def
    by simp
next
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj (ig_data_field_as_edge_type classtype name fieldtype objects obids values)) p"
    unfolding ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def instance_graph_containment_proj_def pre_digraph.cycle_def pre_digraph.awalk_def
    by simp
qed (simp_all add: assms ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def)

lemma ig_data_field_as_edge_type_combine_correct:
  assumes "instance_graph IG"
  assumes fieldtype_is_datatype: "fieldtype \<in> DataType"
  assumes existing_node_type: "type (id_to_list classtype) \<in> NT (TG IG)"
  assumes new_edge_type: "\<And>s l t. (type (id_to_list classtype), s) \<in> inh (TG IG) \<Longrightarrow> l = LabDef.edge [name] \<Longrightarrow> (s, l, t) \<notin> ET (TG IG)"
  assumes no_inh_classtype: "\<And>x. (x, type (id_to_list classtype)) \<in> inh (TG IG) \<Longrightarrow> x = type (id_to_list classtype)"
  assumes existing_objects: "typed (type (id_to_list classtype)) ` objects \<subseteq> N IG"
  assumes all_objects: "\<And>n. n \<in> N IG \<Longrightarrow> type\<^sub>n n = type (id_to_list classtype) \<Longrightarrow> n \<in> typed (type (id_to_list classtype)) ` objects"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes existing_ids: "obids ` objects \<subseteq> Id IG"
  assumes valid_ids: "\<And>i. i \<in> obids ` objects \<Longrightarrow> ident IG i = ident (ig_data_field_as_edge_type classtype name fieldtype objects obids values) i"
  assumes valid_values: "\<And>ob. ob \<in> objects \<Longrightarrow> values ob \<in> datatype_to_literalvalue_set fieldtype"
  assumes value_edges_outgoing: "\<And>s l t. (s, l, t) \<in> ET (TG IG) \<Longrightarrow> (datatype_to_labdef fieldtype, s) \<in> inh (TG IG) \<Longrightarrow> 
    Multiplicity.lower (m_out (mult (TG IG) (s, l, t))) = \<^bold>0"
  assumes value_edges_ingoing: "\<And>s l t. (s, l, t) \<in> ET (TG IG) \<Longrightarrow> (datatype_to_labdef fieldtype, t) \<in> inh (TG IG) \<Longrightarrow> 
    Multiplicity.lower (m_in (mult (TG IG) (s, l, t))) = \<^bold>0"
  shows "instance_graph (ig_combine IG (ig_data_field_as_edge_type classtype name fieldtype objects obids values))"
proof (intro ig_combine_merge_no_containment_imod2_correct)
  show "instance_graph (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
    using fieldtype_is_datatype unique_ids valid_values ig_data_field_as_edge_type_correct
    by metis
next
  have "type_graph (tg_combine (TG IG) (tg_data_field_as_edge_type classtype name fieldtype))"
  proof (intro tg_data_field_as_edge_type_combine_correct)
    fix s l t
    assume "(s, LabDef.type (id_to_list classtype)) \<in> inh (TG IG) \<or> (LabDef.type (id_to_list classtype), s) \<in> inh (TG IG)"
    then have s_def: "(LabDef.type (id_to_list classtype), s) \<in> inh (TG IG)"
      using no_inh_classtype
      by blast
    assume "l = LabDef.edge [name]"
    then show "(s, l, t) \<notin> ET (TG IG)"
      by (simp add: new_edge_type s_def)
  qed (simp_all add: assms(1) existing_node_type fieldtype_is_datatype instance_graph.validity_type_graph new_edge_type)
  then show "type_graph (tg_combine (TG IG) (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values)))"
    unfolding ig_data_field_as_edge_type_def
    by simp
next
  show "ET (TG IG) \<inter> ET (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values)) = {}"
    unfolding ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def
    by (simp add: assms(1) existing_node_type instance_graph.validity_type_graph new_edge_type type_graph.validity_inh_node)
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
  then have "n \<in> N IG \<union> typed (type (id_to_list classtype)) ` objects \<union> literalvalue_to_labdef ` values ` objects"
    unfolding ig_data_field_as_edge_type_def
    by simp
  then have n_def: "n \<in> N IG \<union> literalvalue_to_labdef ` values ` objects"
    using existing_objects
    by blast
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+"
    unfolding ig_data_field_as_edge_type_def
    by simp
  then have edge_extend_def: "(type\<^sub>n n, src et) \<in> inh (TG IG) \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
    using tg_data_field_as_edge_type_combine_inh fieldtype_is_datatype existing_node_type assms(1) instance_graph.validity_type_graph
    using tg_data_field_as_edge_type_def type_graph.select_convs(3)
    by metis
  show "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG) et)"
  proof (induct "datatype_to_labdef fieldtype \<in> NT (TG IG)")
    case True
    then have edge_extend_def: "(type\<^sub>n n, src et) \<in> inh (TG IG)"
      using assms(1) edge_extend_def instance_graph.validity_type_graph type_graph.validity_inh_node
      by fastforce
    show ?case
      using n_def
    proof (elim UnE)
      assume "n \<in> N IG"
      then show ?thesis
        using assms(1) et_def edge_extend_def instance_graph.validity_outgoing_mult
        by blast
    next
      assume "n \<in> literalvalue_to_labdef ` values ` objects"
      then have "type\<^sub>n n = datatype_to_labdef fieldtype"
      proof (elim imageE)
        fix a b
        assume a_def: "a \<in> objects"
        assume b_def: "b = values a"
        assume "n = literalvalue_to_labdef b"
        then have n_def: "n = literalvalue_to_labdef (values a)"
          by (simp add: b_def)
        have fieldvalue_cases: "fieldtype = TypeDef.boolean \<or> fieldtype = TypeDef.integer \<or> fieldtype = TypeDef.real \<or> fieldtype = TypeDef.string"
          using fieldtype_is_datatype
          unfolding DataType_def
          by blast
        then show ?thesis
        proof (elim disjE)
          assume fieldtype_def: "fieldtype = TypeDef.boolean"
          then have "(values a) \<in> BooleanValue"
            using a_def datatype_to_literalvalue_set.simps(1) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> BooleanNode\<^sub>v"
            unfolding BooleanNode\<^sub>v_def
            by (induct rule: BooleanValue.induct) (simp_all)
          then have n_in_values: "n \<in> BooleanNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.integer"
          then have "(values a) \<in> IntegerValue"
            using a_def datatype_to_literalvalue_set.simps(2) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> IntegerNode\<^sub>v"
            by (induct rule: IntegerValue.induct) (simp add: IntegerNode\<^sub>v.rule_integer_nodes)
          then have n_in_values: "n \<in> IntegerNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.real"
          then have "(values a) \<in> RealValue"
            using a_def datatype_to_literalvalue_set.simps(3) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> RealNode\<^sub>v"
            by (induct rule: RealValue.induct) (simp add: RealNode\<^sub>v.rule_real_nodes)
          then have n_in_values: "n \<in> RealNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.string"
          then have "(values a) \<in> StringValue"
            using a_def datatype_to_literalvalue_set.simps(4) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> StringNode\<^sub>v"
            by (induct rule: StringValue.induct) (simp add: StringNode\<^sub>v.rule_string_nodes)
          then have n_in_values: "n \<in> StringNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        qed
      qed
      then have "(datatype_to_labdef fieldtype, src et) \<in> inh (TG IG)"
        using edge_extend_def
        by simp
      then have "Multiplicity.lower (m_out (mult (TG IG) et)) = \<^bold>0"
        using value_edges_outgoing et_def src_def eq_fst_iff prod_cases3
        by metis
      then show ?thesis
      proof (induct "n \<in> N IG")
        case True
        then show ?case
          using assms(1) et_def edge_extend_def instance_graph.validity_outgoing_mult
          by blast
      next
        case False
        have "{e \<in> E IG. src e = n \<and> type\<^sub>e e = et} = {}"
        proof
          show "{e \<in> E IG. src e = n \<and> type\<^sub>e e = et} \<subseteq> {}"
          proof
            fix x
            assume "x \<in> {e \<in> E IG. src e = n \<and> type\<^sub>e e = et}"
            then show "x \<in> {}"
            proof
              assume assump: "x \<in> E IG \<and> src x = n \<and> type\<^sub>e x = et"
              then have "src x \<in> N IG"
                using assms(1) instance_graph.structure_edges_wellformed_alt
                by blast
              then show "x \<in> {}"
                using False.hyps assump
                by blast
            qed
          qed
        next
          show "{} \<subseteq> {e \<in> E IG. src e = n \<and> type\<^sub>e e = et}"
            by simp
        qed
        then have "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} = 0"
          using card_empty
          by metis
        then show ?case
          unfolding within_multiplicity_def
          using False.prems less_eq_\<M>.elims(3)
          by fastforce
      qed
    qed
  next
    case False
    then have src_et_not_fieldtype: "src et \<noteq> datatype_to_labdef fieldtype"
      using assms(1) et_def instance_graph.validity_type_graph type_graph.structure_edges_wellformed_src_node_alt
      by metis
    show ?case
      using n_def
    proof (elim UnE)
      assume n_def: "n \<in> N IG"
      then have "type\<^sub>n n \<noteq> datatype_to_labdef fieldtype"
        using False.hyps assms(1) instance_graph.validity_node_typed
        by fastforce
      then have "(type\<^sub>n n, src et) \<in> inh (TG IG)"
        using edge_extend_def
        by blast
      then show ?thesis
        using assms(1) n_def et_def instance_graph.validity_outgoing_mult
        by blast
    next
      assume "n \<in> literalvalue_to_labdef ` values ` objects"
      then have "type\<^sub>n n = datatype_to_labdef fieldtype"
      proof (elim imageE)
        fix a b
        assume a_def: "a \<in> objects"
        assume b_def: "b = values a"
        assume "n = literalvalue_to_labdef b"
        then have n_def: "n = literalvalue_to_labdef (values a)"
          by (simp add: b_def)
        have fieldvalue_cases: "fieldtype = TypeDef.boolean \<or> fieldtype = TypeDef.integer \<or> fieldtype = TypeDef.real \<or> fieldtype = TypeDef.string"
          using fieldtype_is_datatype
          unfolding DataType_def
          by blast
        then show ?thesis
        proof (elim disjE)
          assume fieldtype_def: "fieldtype = TypeDef.boolean"
          then have "(values a) \<in> BooleanValue"
            using a_def datatype_to_literalvalue_set.simps(1) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> BooleanNode\<^sub>v"
            unfolding BooleanNode\<^sub>v_def
            by (induct rule: BooleanValue.induct) (simp_all)
          then have n_in_values: "n \<in> BooleanNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.integer"
          then have "(values a) \<in> IntegerValue"
            using a_def datatype_to_literalvalue_set.simps(2) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> IntegerNode\<^sub>v"
            by (induct rule: IntegerValue.induct) (simp add: IntegerNode\<^sub>v.rule_integer_nodes)
          then have n_in_values: "n \<in> IntegerNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.real"
          then have "(values a) \<in> RealValue"
            using a_def datatype_to_literalvalue_set.simps(3) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> RealNode\<^sub>v"
            by (induct rule: RealValue.induct) (simp add: RealNode\<^sub>v.rule_real_nodes)
          then have n_in_values: "n \<in> RealNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.string"
          then have "(values a) \<in> StringValue"
            using a_def datatype_to_literalvalue_set.simps(4) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> StringNode\<^sub>v"
            by (induct rule: StringValue.induct) (simp add: StringNode\<^sub>v.rule_string_nodes)
          then have n_in_values: "n \<in> StringNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        qed
      qed
      then have "(type\<^sub>n n, src et) \<in> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
        using False.hyps edge_extend_def assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node
        by fastforce
      then have "src et = datatype_to_labdef fieldtype"
        by blast
      then show ?thesis
        using src_et_not_fieldtype
        by blast
    qed
  qed
next
  have instance_graph_valid: "instance_graph (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
    using fieldtype_is_datatype unique_ids valid_values ig_data_field_as_edge_type_correct
    by metis
  fix et n
  assume et_in_ig: "et \<in> ET (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype)"
    unfolding ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def
    by simp
  assume "n \<in> N IG \<union> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
  then have n_def: "n \<in> N IG \<union> typed (type (id_to_list classtype)) ` objects \<union> literalvalue_to_labdef ` values ` objects"
    unfolding ig_data_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+"
    unfolding ig_data_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG) \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
    using tg_data_field_as_edge_type_combine_inh fieldtype_is_datatype existing_node_type assms(1) instance_graph.validity_type_graph
    using tg_data_field_as_edge_type_def type_graph.select_convs(3)
    by metis
  then have "(type\<^sub>n n, type (id_to_list classtype)) \<in> inh (TG IG)"
    using assms(1) et_def existing_node_type instance_graph.validity_type_graph type_graph.validity_inh_node
    by fastforce
  then have type_n_def: "type\<^sub>n n = type (id_to_list classtype)"
    using no_inh_classtype
    by simp
  then have edge_extend_def: "(type\<^sub>n n, type (id_to_list classtype)) \<in> inh (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values))"
    unfolding ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def
    by simp
  have "n \<in> typed (type (id_to_list classtype)) ` objects \<union> literalvalue_to_labdef ` values ` objects"
    using type_n_def all_objects n_def
    by fastforce
  then show "card {e \<in> E (ig_data_field_as_edge_type classtype name fieldtype objects obids values). src e = n \<and> type\<^sub>e e = et} in 
    m_out (mult (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values)) et)"
  proof (elim UnE)
    assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
    then have "n \<in> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
      unfolding ig_data_field_as_edge_type_def
      by simp
    then show ?thesis
      using edge_extend_def et_in_ig et_def instance_graph_valid instance_graph.validity_outgoing_mult
      by fastforce
  next
    have fieldvalue_cases: "fieldtype = TypeDef.boolean \<or> fieldtype = TypeDef.integer \<or> fieldtype = TypeDef.real \<or> fieldtype = TypeDef.string"
      using fieldtype_is_datatype
      unfolding DataType_def
      by blast
    assume "n \<in> literalvalue_to_labdef ` values ` objects"
    then have "type\<^sub>n n = datatype_to_labdef fieldtype"
    proof (elim imageE)
      fix a b
      assume a_def: "a \<in> objects"
      assume b_def: "b = values a"
      assume "n = literalvalue_to_labdef b"
      then have n_def: "n = literalvalue_to_labdef (values a)"
        by (simp add: b_def)
      show ?thesis
        using fieldvalue_cases
      proof (elim disjE)
        assume fieldtype_def: "fieldtype = TypeDef.boolean"
        then have "(values a) \<in> BooleanValue"
          using a_def datatype_to_literalvalue_set.simps(1) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> BooleanNode\<^sub>v"
          unfolding BooleanNode\<^sub>v_def
          by (induct rule: BooleanValue.induct) (simp_all)
        then have n_in_values: "n \<in> BooleanNode\<^sub>v"
          by (simp add: n_def)
        then show "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
      next
        assume fieldtype_def: "fieldtype = TypeDef.integer"
        then have "(values a) \<in> IntegerValue"
          using a_def datatype_to_literalvalue_set.simps(2) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> IntegerNode\<^sub>v"
          by (induct rule: IntegerValue.induct) (simp add: IntegerNode\<^sub>v.rule_integer_nodes)
        then have n_in_values: "n \<in> IntegerNode\<^sub>v"
          by (simp add: n_def)
        then show "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
      next
        assume fieldtype_def: "fieldtype = TypeDef.real"
        then have "(values a) \<in> RealValue"
          using a_def datatype_to_literalvalue_set.simps(3) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> RealNode\<^sub>v"
          by (induct rule: RealValue.induct) (simp add: RealNode\<^sub>v.rule_real_nodes)
        then have n_in_values: "n \<in> RealNode\<^sub>v"
          by (simp add: n_def)
        then show "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
      next
        assume fieldtype_def: "fieldtype = TypeDef.string"
        then have "(values a) \<in> StringValue"
          using a_def datatype_to_literalvalue_set.simps(4) valid_values
          by blast
        then have "literalvalue_to_labdef (values a) \<in> StringNode\<^sub>v"
          by (induct rule: StringValue.induct) (simp add: StringNode\<^sub>v.rule_string_nodes)
        then have n_in_values: "n \<in> StringNode\<^sub>v"
          by (simp add: n_def)
        then show "type\<^sub>n n = datatype_to_labdef fieldtype"
          by (simp add: fieldtype_def)
      qed
    qed
    then show ?thesis
      using type_n_def fieldvalue_cases
      by fastforce
  qed
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
  then have "n \<in> N IG \<union> typed (type (id_to_list classtype)) ` objects \<union> literalvalue_to_labdef ` values ` objects"
    unfolding ig_data_field_as_edge_type_def
    by simp
  then have n_def: "n \<in> N IG \<union> literalvalue_to_labdef ` values ` objects"
    using existing_objects
    by blast
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (TG (ig_data_field_as_edge_type classtype name fieldtype objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (tg_data_field_as_edge_type classtype name fieldtype))\<^sup>+"
    unfolding ig_data_field_as_edge_type_def
    by simp
  then have edge_extend_def: "(type\<^sub>n n, tgt et) \<in> inh (TG IG) \<union> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
    using tg_data_field_as_edge_type_combine_inh fieldtype_is_datatype existing_node_type assms(1) instance_graph.validity_type_graph
    using tg_data_field_as_edge_type_def type_graph.select_convs(3)
    by metis
  show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG) et)"
  proof (induct "datatype_to_labdef fieldtype \<in> NT (TG IG)")
    case True
    then have edge_extend_def: "(type\<^sub>n n, tgt et) \<in> inh (TG IG)"
      using assms(1) edge_extend_def instance_graph.validity_type_graph type_graph.validity_inh_node
      by fastforce
    show ?case
      using n_def
    proof (elim UnE)
      assume "n \<in> N IG"
      then show ?thesis
        using assms(1) et_def edge_extend_def instance_graph.validity_ingoing_mult
        by blast
    next
      assume "n \<in> literalvalue_to_labdef ` values ` objects"
      then have "type\<^sub>n n = datatype_to_labdef fieldtype"
      proof (elim imageE)
        fix a b
        assume a_def: "a \<in> objects"
        assume b_def: "b = values a"
        assume "n = literalvalue_to_labdef b"
        then have n_def: "n = literalvalue_to_labdef (values a)"
          by (simp add: b_def)
        have fieldvalue_cases: "fieldtype = TypeDef.boolean \<or> fieldtype = TypeDef.integer \<or> fieldtype = TypeDef.real \<or> fieldtype = TypeDef.string"
          using fieldtype_is_datatype
          unfolding DataType_def
          by blast
        then show ?thesis
        proof (elim disjE)
          assume fieldtype_def: "fieldtype = TypeDef.boolean"
          then have "(values a) \<in> BooleanValue"
            using a_def datatype_to_literalvalue_set.simps(1) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> BooleanNode\<^sub>v"
            unfolding BooleanNode\<^sub>v_def
            by (induct rule: BooleanValue.induct) (simp_all)
          then have n_in_values: "n \<in> BooleanNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.integer"
          then have "(values a) \<in> IntegerValue"
            using a_def datatype_to_literalvalue_set.simps(2) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> IntegerNode\<^sub>v"
            by (induct rule: IntegerValue.induct) (simp add: IntegerNode\<^sub>v.rule_integer_nodes)
          then have n_in_values: "n \<in> IntegerNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.real"
          then have "(values a) \<in> RealValue"
            using a_def datatype_to_literalvalue_set.simps(3) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> RealNode\<^sub>v"
            by (induct rule: RealValue.induct) (simp add: RealNode\<^sub>v.rule_real_nodes)
          then have n_in_values: "n \<in> RealNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.string"
          then have "(values a) \<in> StringValue"
            using a_def datatype_to_literalvalue_set.simps(4) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> StringNode\<^sub>v"
            by (induct rule: StringValue.induct) (simp add: StringNode\<^sub>v.rule_string_nodes)
          then have n_in_values: "n \<in> StringNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        qed
      qed
      then have "(datatype_to_labdef fieldtype, tgt et) \<in> inh (TG IG)"
        using edge_extend_def
        by simp
      then have "Multiplicity.lower (m_in (mult (TG IG) et)) = \<^bold>0"
        using value_edges_ingoing et_def tgt_def eq_snd_iff prod_cases3
        by metis
      then show ?thesis
      proof (induct "n \<in> N IG")
        case True
        then show ?case
          using assms(1) et_def edge_extend_def instance_graph.validity_ingoing_mult
          by blast
      next
        case False
        have "{e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} = {}"
        proof
          show "{e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} \<subseteq> {}"
          proof
            fix x
            assume "x \<in> {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et}"
            then show "x \<in> {}"
            proof
              assume assump: "x \<in> E IG \<and> tgt x = n \<and> type\<^sub>e x = et"
              then have "tgt x \<in> N IG"
                using assms(1) instance_graph.structure_edges_wellformed_alt
                by blast
              then show "x \<in> {}"
                using False.hyps assump
                by blast
            qed
          qed
        next
          show "{} \<subseteq> {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et}"
            by simp
        qed
        then have "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} = 0"
          using card_empty
          by metis
        then show ?case
          unfolding within_multiplicity_def
          using False.prems less_eq_\<M>.elims(3)
          by fastforce
      qed
    qed
  next
    case False
    then have tgt_et_not_fieldtype: "tgt et \<noteq> datatype_to_labdef fieldtype"
      using assms(1) et_def instance_graph.validity_type_graph type_graph.structure_edges_wellformed_tgt_node_alt
      by metis
    show ?case
      using n_def
    proof (elim UnE)
      assume n_def: "n \<in> N IG"
      then have "type\<^sub>n n \<noteq> datatype_to_labdef fieldtype"
        using False.hyps assms(1) instance_graph.validity_node_typed
        by fastforce
      then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG)"
        using edge_extend_def
        by blast
      then show ?thesis
        using assms(1) n_def et_def instance_graph.validity_ingoing_mult
        by blast
    next
      assume "n \<in> literalvalue_to_labdef ` values ` objects"
      then have "type\<^sub>n n = datatype_to_labdef fieldtype"
      proof (elim imageE)
        fix a b
        assume a_def: "a \<in> objects"
        assume b_def: "b = values a"
        assume "n = literalvalue_to_labdef b"
        then have n_def: "n = literalvalue_to_labdef (values a)"
          by (simp add: b_def)
        have fieldvalue_cases: "fieldtype = TypeDef.boolean \<or> fieldtype = TypeDef.integer \<or> fieldtype = TypeDef.real \<or> fieldtype = TypeDef.string"
          using fieldtype_is_datatype
          unfolding DataType_def
          by blast
        then show ?thesis
        proof (elim disjE)
          assume fieldtype_def: "fieldtype = TypeDef.boolean"
          then have "(values a) \<in> BooleanValue"
            using a_def datatype_to_literalvalue_set.simps(1) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> BooleanNode\<^sub>v"
            unfolding BooleanNode\<^sub>v_def
            by (induct rule: BooleanValue.induct) (simp_all)
          then have n_in_values: "n \<in> BooleanNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.integer"
          then have "(values a) \<in> IntegerValue"
            using a_def datatype_to_literalvalue_set.simps(2) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> IntegerNode\<^sub>v"
            by (induct rule: IntegerValue.induct) (simp add: IntegerNode\<^sub>v.rule_integer_nodes)
          then have n_in_values: "n \<in> IntegerNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.real"
          then have "(values a) \<in> RealValue"
            using a_def datatype_to_literalvalue_set.simps(3) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> RealNode\<^sub>v"
            by (induct rule: RealValue.induct) (simp add: RealNode\<^sub>v.rule_real_nodes)
          then have n_in_values: "n \<in> RealNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        next
          assume fieldtype_def: "fieldtype = TypeDef.string"
          then have "(values a) \<in> StringValue"
            using a_def datatype_to_literalvalue_set.simps(4) valid_values
            by blast
          then have "literalvalue_to_labdef (values a) \<in> StringNode\<^sub>v"
            by (induct rule: StringValue.induct) (simp add: StringNode\<^sub>v.rule_string_nodes)
          then have n_in_values: "n \<in> StringNode\<^sub>v"
            by (simp add: n_def)
          then show "type\<^sub>n n = datatype_to_labdef fieldtype"
            by (simp add: fieldtype_def)
        qed
      qed
      then have "(type\<^sub>n n, tgt et) \<in> {(datatype_to_labdef fieldtype, datatype_to_labdef fieldtype)}"
        using False.hyps edge_extend_def assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node
        by fastforce
      then have "tgt et = datatype_to_labdef fieldtype"
        by blast
      then show ?thesis
        using tgt_et_not_fieldtype
        by blast
    qed
  qed
qed (simp_all add: ig_data_field_as_edge_type_def tg_data_field_as_edge_type_def assms)


subsection "Transformation functions"

definition imod_data_field_to_ig_data_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't TypeDef \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> ('o, 't) ValueDef) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "imod_data_field_to_ig_data_field_as_edge_type classtype name fieldtype obids values Imod = \<lparr>
    TG = tg_data_field_as_edge_type classtype name fieldtype,
    Id = obids ` Object Imod,
    N = typed (type (id_to_list classtype)) ` Object Imod \<union> literalvalue_to_labdef ` values ` Object Imod,
    E = (\<lambda>x. (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))) ` Object Imod,
    ident = (\<lambda>x. if x \<in> obids ` Object Imod then typed (type (id_to_list classtype)) (THE y. obids y = x) else undefined)
  \<rparr>"

lemma imod_data_field_to_ig_data_field_as_edge_type_proj:
  shows "imod_data_field_to_ig_data_field_as_edge_type classtype name fieldtype obids values (imod_data_field classtype name fieldtype objects obids values) = 
    ig_data_field_as_edge_type classtype name fieldtype objects obids values"
  unfolding imod_data_field_to_ig_data_field_as_edge_type_def ig_data_field_as_edge_type_def imod_data_field_def
  by simp

lemma imod_data_field_to_ig_data_field_as_edge_type_func:
  shows "ig_combine_mapping_function (imod_data_field_to_ig_data_field_as_edge_type classtype name fieldtype obids values)
    (imod_data_field classtype name fieldtype objects obids values) (ig_data_field_as_edge_type classtype name fieldtype objects obids values)"
  by (intro ig_combine_mapping_function.intro)
    (auto simp add: imod_data_field_to_ig_data_field_as_edge_type_def imod_data_field_def ig_data_field_as_edge_type_def imod_combine_def)

definition ig_data_field_as_edge_type_to_imod_data_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't TypeDef \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> ('o, 't) ValueDef) \<Rightarrow> ('o, 't list, 't) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "ig_data_field_as_edge_type_to_imod_data_field classtype name fieldtype obids values IG = \<lparr>
    Tm = tmod_data_field classtype name fieldtype,
    Object = nodeId ` src ` E IG,
    ObjectClass = (\<lambda>x. if x \<in> nodeId ` src ` E IG then classtype else undefined),
    ObjectId = (\<lambda>x. if x \<in> nodeId ` src ` E IG then obids x else undefined),
    FieldValue = (\<lambda>x. if fst x \<in> nodeId ` src ` E IG \<and> snd x = (classtype, name) then values (fst x) else undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_data_field_as_edge_type_to_imod_data_field_proj:
  shows "ig_data_field_as_edge_type_to_imod_data_field classtype name fieldtype obids values (ig_data_field_as_edge_type classtype name fieldtype objects obids values) = 
    imod_data_field classtype name fieldtype objects obids values"
proof-
  have "nodeId ` (\<lambda>x. typed (LabDef.type (id_to_list classtype)) x) ` objects = objects"
    by force
  then have "nodeId ` fst ` (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) x, (LabDef.type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))) ` objects = objects"
    by force
  then show "ig_data_field_as_edge_type_to_imod_data_field classtype name fieldtype obids values (ig_data_field_as_edge_type classtype name fieldtype objects obids values) = 
    imod_data_field classtype name fieldtype objects obids values"
    unfolding ig_data_field_as_edge_type_to_imod_data_field_def imod_data_field_def ig_data_field_as_edge_type_def
    by simp
qed

lemma ig_data_field_as_edge_type_to_imod_data_field_func:
  shows "imod_combine_mapping_function (ig_data_field_as_edge_type_to_imod_data_field classtype name fieldtype obids values)
    (ig_data_field_as_edge_type classtype name fieldtype objects obids values) (imod_data_field classtype name fieldtype objects obids values)"
proof-
  have "nodeId ` (\<lambda>x. typed (LabDef.type (id_to_list classtype)) x) ` objects = objects"
    by force
  then have "nodeId ` fst ` (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) x, (LabDef.type (id_to_list classtype), LabDef.edge [name], datatype_to_labdef fieldtype), literalvalue_to_labdef (values x))) ` objects = objects"
    by force
  then show "imod_combine_mapping_function (ig_data_field_as_edge_type_to_imod_data_field classtype name fieldtype obids values)
    (ig_data_field_as_edge_type classtype name fieldtype objects obids values) (imod_data_field classtype name fieldtype objects obids values)"
  proof (intro imod_combine_mapping_function.intro)
    fix IGX
    show "Object (ig_data_field_as_edge_type_to_imod_data_field classtype name fieldtype obids values (ig_data_field_as_edge_type classtype name fieldtype objects obids values))
      \<subseteq> Object (ig_data_field_as_edge_type_to_imod_data_field classtype name fieldtype obids values (ig_combine (ig_data_field_as_edge_type classtype name fieldtype objects obids values) IGX))"
    proof
      fix x
      assume "x \<in> Object (ig_data_field_as_edge_type_to_imod_data_field classtype name fieldtype obids values (ig_data_field_as_edge_type classtype name fieldtype objects obids values))"
      then have "x \<in> objects"
        unfolding ig_data_field_as_edge_type_to_imod_data_field_def imod_data_field_def ig_data_field_as_edge_type_def ig_combine_def
        by fastforce
      then show "x \<in> Object (ig_data_field_as_edge_type_to_imod_data_field classtype name fieldtype obids values (ig_combine (ig_data_field_as_edge_type classtype name fieldtype objects obids values) IGX))"
        unfolding ig_data_field_as_edge_type_to_imod_data_field_def imod_data_field_def ig_data_field_as_edge_type_def ig_combine_def
        by force
    qed
  qed (auto simp add: ig_data_field_as_edge_type_to_imod_data_field_def imod_data_field_def ig_data_field_as_edge_type_def ig_combine_def)
qed

end