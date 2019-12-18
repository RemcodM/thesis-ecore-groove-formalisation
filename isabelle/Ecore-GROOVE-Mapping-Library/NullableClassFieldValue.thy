theory NullableClassFieldValue
  imports
    Main
    "Ecore-GROOVE-Mapping.Instance_Model_Graph_Mapping"
    NullableClassField
begin

section "Definition of an instance model which introduces values for a field typed by a class that can be nullable"

definition imod_nullable_class_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 'o set \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 'o) \<Rightarrow> ('o, 't) instance_model" where
  "imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values = \<lparr>
    Tm = tmod_nullable_class_field classtype name fieldtype,
    Object = nilobjects \<union> valobjects \<union> values ` valobjects,
    ObjectClass = (\<lambda>x. if x \<in> nilobjects \<union> valobjects then classtype else if x \<in> values ` valobjects then fieldtype else undefined),
    ObjectId = (\<lambda>x. if x \<in> nilobjects \<union> valobjects \<union> values ` valobjects then obids x else undefined),
    FieldValue = (\<lambda>x. if fst x \<in> nilobjects \<and> snd x = (classtype, name) then nil else 
      if fst x \<in> valobjects \<and> snd x = (classtype, name) then obj (values (fst x)) else
      if fst x \<in> values ` valobjects \<and> snd x = (classtype, name) then unspecified else undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_nullable_class_field_correct:
  assumes valid_ns: "\<not>id_in_ns fieldtype (Identifier classtype) \<and> \<not>id_in_ns classtype (Identifier fieldtype)"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> nilobjects \<union> valobjects \<union> values ` valobjects \<Longrightarrow> 
    o2 \<in> nilobjects \<union> valobjects \<union> values ` valobjects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_value: "valobjects \<inter> nilobjects = {}"
  assumes all_objects: "classtype = fieldtype \<Longrightarrow> values ` valobjects \<subseteq> nilobjects \<union> valobjects"
  assumes no_objects: "classtype \<noteq> fieldtype \<Longrightarrow> values ` valobjects \<inter> (nilobjects \<union> valobjects) = {}"
  shows "instance_model (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
proof (intro instance_model.intro)
  fix ob
  assume "ob \<in> Object (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
  then have "ob \<in> nilobjects \<union> valobjects \<union> values ` valobjects"
    unfolding imod_nullable_class_field_def
    by simp
  then have "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob = classtype \<or>
    ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob = fieldtype"
    unfolding imod_nullable_class_field_def
    by fastforce
  then show "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob \<in> 
    Class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
    unfolding imod_nullable_class_field_def tmod_nullable_class_field_def
    by simp
next
  show "type_model (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
    unfolding imod_nullable_class_field_def
    using tmod_nullable_class_field_correct valid_ns
    by simp
next
  fix ob f
  assume "ob \<notin> Object (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) \<or> 
    f \<notin> type_model.Field (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
  then have "ob \<notin> nilobjects \<union> valobjects \<union> values ` valobjects \<or> f \<noteq> (classtype, name)"
    unfolding imod_nullable_class_field_def tmod_nullable_class_field_def
    by simp
  then show "FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f) = undefined"
    unfolding imod_nullable_class_field_def
    by auto
next
  fix ob f
  assume "ob \<in> Object (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
  then have ob_def: "ob \<in> nilobjects \<union> valobjects \<union> values ` valobjects"
    unfolding imod_nullable_class_field_def
    by simp
  assume "f \<in> type_model.Field (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_nullable_class_field_def tmod_nullable_class_field_def
    by simp
  assume no_inh: "\<not>\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) 
    \<sqsubseteq>[Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)] 
    \<exclamdown>(class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f)"
  show "FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f) = unspecified"
    using ob_def
  proof (elim UnE)
    assume "ob \<in> nilobjects"
    then have ob_class_def: "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob = classtype"
      unfolding imod_nullable_class_field_def
      by simp
    then have "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) \<in> 
      ProperClassType (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
      by (simp add: ProperClassType.rule_proper_classes imod_nullable_class_field_def tmod_nullable_class_field_def)
    then have ob_type_def: "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) \<in> 
      Type (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
      unfolding Type_def NonContainerType_def ClassType_def
      by blast
    have "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob = 
      class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f"
      unfolding class_def
      by (simp add: f_def ob_class_def)
    then have "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) 
      \<sqsubseteq>[Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)] 
      \<exclamdown>(class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f)"
      unfolding subtype_def
      using ob_type_def subtype_rel.reflexivity
      by simp
    then show ?thesis
      using no_inh
      by blast
  next
    assume "ob \<in> valobjects"
    then have ob_class_def: "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob = classtype"
      unfolding imod_nullable_class_field_def
      by simp
    then have "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) \<in> 
      ProperClassType (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
      by (simp add: ProperClassType.rule_proper_classes imod_nullable_class_field_def tmod_nullable_class_field_def)
    then have ob_type_def: "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) \<in> 
      Type (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
      unfolding Type_def NonContainerType_def ClassType_def
      by blast
    have "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob = 
      class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f"
      unfolding class_def
      by (simp add: f_def ob_class_def)
    then have "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) 
      \<sqsubseteq>[Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)] 
      \<exclamdown>(class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f)"
      unfolding subtype_def
      using ob_type_def subtype_rel.reflexivity
      by simp
    then show ?thesis
      using no_inh
      by blast
  next
    assume "ob \<in> values ` valobjects"
    then show ?thesis
    proof (induct "classtype = fieldtype")
      case True
      then have ob_class_def: "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob = classtype"
        unfolding imod_nullable_class_field_def
        by simp
      then have "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) \<in> 
        ProperClassType (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
        by (simp add: ProperClassType.rule_proper_classes imod_nullable_class_field_def tmod_nullable_class_field_def)
      then have ob_type_def: "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) \<in> 
        Type (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
        unfolding Type_def NonContainerType_def ClassType_def
        by blast
      have "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob = 
        class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f"
        unfolding class_def
        by (simp add: f_def ob_class_def)
      then have "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) 
        \<sqsubseteq>[Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)] 
        \<exclamdown>(class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f)"
        unfolding subtype_def
        using ob_type_def subtype_rel.reflexivity
        by simp
      then show ?case
        using no_inh
        by blast
    next
      case False
      then show ?case
        unfolding imod_nullable_class_field_def
        using no_objects f_def
        by auto
    qed
  qed
next
  have type_model_correct: "type_model (tmod_nullable_class_field classtype name fieldtype)"
    using tmod_nullable_class_field_correct valid_ns
    by metis
  fix ob f
  assume "ob \<in> Object (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
  then have ob_cases: "ob \<in> nilobjects \<union> valobjects \<union> values ` valobjects"
    unfolding imod_nullable_class_field_def
    by simp
  assume "f \<in> type_model.Field (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_nullable_class_field_def tmod_nullable_class_field_def
    by simp
  then have f_type: "Type_Model.type (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f = \<questiondown>fieldtype"
    unfolding Type_Model.type_def imod_nullable_class_field_def tmod_nullable_class_field_def
    by simp
  have f_lower: "lower (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f = \<^bold>0"
    unfolding lower_def imod_nullable_class_field_def tmod_nullable_class_field_def
    using f_def
    by simp
  have f_upper: "upper (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f = \<^bold>1"
    unfolding upper_def imod_nullable_class_field_def tmod_nullable_class_field_def
    using f_def
    by simp
  assume "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob)
    \<sqsubseteq>[Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)]
    \<exclamdown>(class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f)"
  then have "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob)
    \<sqsubseteq>[tmod_nullable_class_field classtype name fieldtype] \<exclamdown>(fst f)"
    unfolding imod_nullable_class_field_def class_def
    by simp
  then have "(\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob), \<exclamdown>(fst f)) \<in> 
    subtype_rel_altdef (tmod_nullable_class_field classtype name fieldtype)"
    using subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_correct
    by blast
  then have ob_def: "ob \<in> nilobjects \<union> valobjects"
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob), \<exclamdown>(fst f)) \<in> 
      subtype_tuple ` Type (tmod_nullable_class_field classtype name fieldtype)"
    then have eq: "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob = fst f"
      by (simp add: image_iff subtype_tuple_def)
    show ?thesis
      using ob_cases
    proof (elim UnE)
      assume "ob \<in> nilobjects"
      then show ?thesis
        by simp
    next
      assume "ob \<in> valobjects"
      then show ?thesis
        by simp
    next
      assume "ob \<in> values ` valobjects"
      then show ?thesis
      proof (induct "classtype = fieldtype")
        case True
        then show ?case
          using all_objects
          by fastforce
      next
        case False
        then have "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob = fieldtype"
          unfolding imod_nullable_class_field_def
          using no_objects
          by fastforce
        then show ?case
          using False.hyps eq f_def
          by simp
      qed
    qed
  next
    assume "(\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob), \<exclamdown>(fst f)) \<in> 
      subtype_conv nullable nullable ` (Inh (tmod_nullable_class_field classtype name fieldtype))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob), \<exclamdown>(fst f)) \<in> 
      subtype_conv proper proper ` (Inh (tmod_nullable_class_field classtype name fieldtype))\<^sup>+"
    then show ?thesis
      unfolding tmod_nullable_class_field_def
      by auto
  next
    assume "(\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob), \<exclamdown>(fst f)) \<in> 
      subtype_conv proper nullable ` subtype_tuple ` Class (tmod_nullable_class_field classtype name fieldtype)"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob), \<exclamdown>(fst f)) \<in>
      subtype_conv proper nullable ` (Inh (tmod_nullable_class_field classtype name fieldtype))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then have value_def: "FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f) = obj (values ob) \<or>
    FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f) = nil"
    unfolding imod_nullable_class_field_def
    using f_def
    by fastforce
  have value_valid: "FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f) 
    :[imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values] \<questiondown>fieldtype"
    using ob_def
  proof (elim UnE)
    assume value_def: "ob \<in> nilobjects"
    have "nil :[imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values] \<questiondown>fieldtype"
      unfolding Valid_def
    proof (intro Valid_rel.valid_rule_nullable_classes)
      show "\<questiondown>fieldtype \<in> NullableClassType (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
        unfolding imod_nullable_class_field_def tmod_nullable_class_field_def 
        by (simp add: NullableClassType.rule_nullable_classes)
    qed
    then show ?thesis
      unfolding imod_nullable_class_field_def
      using value_def unique_value f_def
      by fastforce
  next
    assume value_def: "ob \<in> valobjects"
    have "obj (values ob) :[imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values] \<questiondown>fieldtype"
      unfolding Valid_def
    proof (intro Valid_rel.valid_rule_proper_classes)
      show "values ob \<in> Object (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
        unfolding imod_nullable_class_field_def
        by (simp add: value_def)
    next
      show "\<questiondown>fieldtype \<in> ClassType (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
        unfolding ClassType_def imod_nullable_class_field_def tmod_nullable_class_field_def 
        by (simp add: NullableClassType.rule_nullable_classes)
    next
      have subtype_def: "\<exclamdown>fieldtype \<sqsubseteq>[Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)] \<questiondown>fieldtype"
        unfolding subtype_def
      proof (intro subtype_rel.nullable_proper_classes)
        show "fieldtype \<in> Class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
          unfolding imod_nullable_class_field_def tmod_nullable_class_field_def
          by simp
      qed
      have "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (values ob) = fieldtype"
        unfolding imod_nullable_class_field_def
        using no_objects value_def
        by auto
      then show "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (values ob)) 
        \<sqsubseteq>[Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)]
        \<questiondown>fieldtype"
        by (simp add: local.subtype_def)
    qed
    then show ?thesis
      unfolding imod_nullable_class_field_def
      using value_def unique_value f_def
      by fastforce
  qed
  then show "FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f) 
    :[imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values] 
    Type_Model.type (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f"
    using value_def f_type
    by simp
  have values_are_class_values: "FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f) \<in> 
    ClassValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
    using value_valid
    unfolding Valid_def
  proof (cases)
    case (valid_rule_proper_classes v)
    then show ?thesis
      unfolding ClassValue_def
      by (simp add: ProperClassValue.rule_proper_objects)
  next
    case valid_rule_nullable_classes
    then show ?thesis
      unfolding ClassValue_def
      by blast
  next
    case valid_rule_userdata_values
    then show ?thesis
      using valid_type_nullable_classes_values_unique value_valid
      by blast
  next
    case valid_rule_bags
    then show ?thesis
      using valid_type_nullable_classes_values_unique value_valid
      by blast
  next
    case valid_rule_sets
    then show ?thesis
      using valid_type_nullable_classes_values_unique value_valid
      by blast
  next
    case valid_rule_seqs
    then show ?thesis
      using valid_type_nullable_classes_values_unique value_valid
      by blast
  next
    case valid_rule_ords
    then show ?thesis 
      using valid_type_nullable_classes_values_unique value_valid
      by blast
  qed
  then show "FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f) \<in>
    Value (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
    unfolding Value_def AtomValue_def
    by (simp add: value_def)
  have "validMul (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ((ob, f), 
    FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f))"
    unfolding validMul_def
  proof (intro conjI)
    show "snd ((ob, f), FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f)) \<in> 
      ContainerValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) \<longrightarrow>
      lower (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) (snd (fst ((ob, f), FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f)))) \<le> 
      \<^bold>(length (contained_list (snd ((ob, f), FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f))))) \<and>
      \<^bold>(length (contained_list (snd ((ob, f), FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f))))) \<le> 
      upper (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) (snd (fst ((ob, f), FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f))))"
    proof
      assume "snd ((ob, f), FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f)) \<in> 
        ContainerValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
      then have "FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f) \<in> 
        ContainerValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
        by simp
      then show "lower (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) (snd (fst ((ob, f), FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f)))) \<le> 
        \<^bold>(length (contained_list (snd ((ob, f), FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f))))) \<and>
        \<^bold>(length (contained_list (snd ((ob, f), FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f))))) \<le> 
        upper (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) (snd (fst ((ob, f), FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f))))"
        using values_are_class_values container_values_class_values_intersect
        by blast
    qed
  qed (simp_all add: value_valid f_type)
  then show "validMul (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ((ob, f), FieldValue (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ob, f))"
    by (simp add: value_def)
qed (simp_all add: assms imod_nullable_class_field_def tmod_nullable_class_field_def)

lemma imod_nullable_class_field_combine_correct:
  assumes "instance_model Imod"
  assumes existing_classes: "{classtype, fieldtype} \<subseteq> Class (Tm Imod)"
  assumes new_field: "(classtype, name) \<notin> Field (Tm Imod)"
  assumes valid_ns: "\<not>id_in_ns fieldtype (Identifier classtype) \<and> \<not>id_in_ns classtype (Identifier fieldtype)"
  assumes no_inh_classtype: "\<And>x. (x, classtype) \<notin> Inh (Tm Imod)"
  assumes no_objects: "classtype \<noteq> fieldtype \<Longrightarrow> values ` valobjects \<inter> (nilobjects \<union> valobjects) = {}"
  assumes existing_objects: "(nilobjects \<union> valobjects \<union> values ` valobjects) \<inter> Object Imod = valobjects \<union> nilobjects \<union> values ` valobjects"
  assumes all_objects: "\<And>ob. ob \<in> Object Imod \<Longrightarrow> ObjectClass Imod ob = classtype \<longleftrightarrow> ob \<in> nilobjects \<union> valobjects"
  assumes classes_valid: "\<And>ob. ob \<in> nilobjects \<union> valobjects \<union> values ` valobjects \<Longrightarrow> 
    ObjectClass Imod ob = ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob"
  assumes ids_valid: "\<And>ob. ob \<in> nilobjects \<union> valobjects \<union> values ` valobjects \<Longrightarrow> ObjectId Imod ob = obids ob"
  assumes unique_value: "valobjects \<inter> nilobjects = {}"
  shows "instance_model (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
proof (intro imod_combine_merge_no_containment_imod2_correct)
  show "instance_model (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
  proof (intro imod_nullable_class_field_correct)
    fix o1 o2
    assume o1_object: "o1 \<in> nilobjects \<union> valobjects \<union> values ` valobjects"
    then have o1_def: "o1 \<in> Object Imod"
      using existing_objects
      by blast
    assume o2_object: "o2 \<in> nilobjects \<union> valobjects \<union> values ` valobjects"
    then have o2_def: "o2 \<in> Object Imod"
      using existing_objects
      by blast
    assume "obids o1 = obids o2"
    then have "ObjectId Imod o1 = ObjectId Imod o2"
      using ids_valid o1_object o2_object
      by simp
    then show "o1 = o2"
      using assms(1) instance_model.property_object_id_uniqueness o1_def o2_def
      by fastforce
  next
    assume classtype_fieldtype_eq: "classtype = fieldtype"
    show "values ` valobjects \<subseteq> nilobjects \<union> valobjects"
    proof
      fix x
      assume x_def: "x \<in> values ` valobjects"
      then have "ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) x = classtype"
        unfolding imod_nullable_class_field_def
        using classtype_fieldtype_eq
        by simp
      then have ob_class_def: "ObjectClass Imod x = classtype"
        using classes_valid x_def
        by simp
      have "x \<in> Object Imod"
        using existing_objects x_def
        by blast
      then show "x \<in> nilobjects \<union> valobjects"
        using all_objects ob_class_def
        by simp
    qed
  qed (simp_all add: assms)
next
  fix ob
  assume "ob \<in> Object (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
  then have ob_in_objects: "ob \<in> nilobjects \<union> valobjects \<union> values ` valobjects"
    unfolding imod_nullable_class_field_def
    by simp
  then have "ObjectId (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob = obids ob"
    unfolding imod_nullable_class_field_def
    by simp
  then show "ObjectId Imod ob = ObjectId (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob"
    using ids_valid ob_in_objects
    by simp
next
  fix o1 o2
  assume "o1 \<in> Object Imod - Object (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
  assume "o2 \<in> Object (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) - Object Imod"
  then have "o2 \<in> nilobjects \<union> valobjects \<union> values ` valobjects - Object Imod"
    unfolding imod_nullable_class_field_def
    by simp
  then have "o2 \<in> {}"
    using existing_objects
    by blast
  then show "o1 = o2"
    by blast
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    using assms(1) instance_model.validity_type_model_consistent existing_classes new_field valid_ns
    by (intro tmod_nullable_class_field_combine_correct) (simp_all)
  fix ob f
  assume ob_def: "ob \<in> Object Imod"
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob = ObjectClass Imod ob"
    by (simp add: classes_valid imod_combine_def imod_combine_object_class_def imod_nullable_class_field_def)
  assume "f \<in> Field (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_nullable_class_field_def tmod_nullable_class_field_def
    by simp
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))) f)"
  then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))] \<exclamdown>classtype"
    unfolding class_def
    using ob_class_def f_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    unfolding subtype_def imod_nullable_class_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have ob_class_is_classtype: "\<exclamdown>(ObjectClass Imod ob) = \<exclamdown>classtype"
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    then show ?thesis
      unfolding subtype_tuple_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then have ob_extends_classtype: "(ObjectClass Imod ob, classtype) \<in> (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
      unfolding subtype_conv_def
      by fastforce
    have "(ObjectClass Imod ob, classtype) \<notin> (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    proof
      assume "(ObjectClass Imod ob, classtype) \<in> (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
      then show "False"
      proof (cases)
        case base
        then show ?thesis
          unfolding tmod_nullable_class_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      next
        case (step c)
        then show ?thesis
          unfolding tmod_nullable_class_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      qed
    qed
    then show ?thesis
      using ob_extends_classtype
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then have ob_in_objects: "ob \<in> nilobjects \<union> valobjects"
    using all_objects ob_def
    by blast
  have "\<exclamdown>classtype \<in> ProperClassType (tmod_nullable_class_field classtype name fieldtype)"
    unfolding tmod_nullable_class_field_def
    by (simp add: ProperClassType.rule_proper_classes)
  then have "\<exclamdown>classtype \<in> Type (tmod_nullable_class_field classtype name fieldtype)"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  then show "ob \<in> Object (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) \<and>
    \<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) 
    \<sqsubseteq>[Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)]
    \<exclamdown>(class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f)"
    unfolding imod_nullable_class_field_def class_def subtype_def
    using ob_in_objects f_def
    by (simp add: subtype_rel.reflexivity)
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    using assms(1) instance_model.validity_type_model_consistent existing_classes new_field valid_ns
    by (intro tmod_nullable_class_field_combine_correct) (simp_all)
  fix ob f
  assume "ob \<in> Object (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
  then have ob_def: "ob \<in> nilobjects \<union> valobjects \<union> values ` valobjects"
    unfolding imod_nullable_class_field_def
    by simp
  then have ob_in_imod: "ob \<in> Object Imod"
    using existing_objects
    by blast
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob = ObjectClass Imod ob"
    using ob_def classes_valid
    unfolding imod_combine_def imod_nullable_class_field_def imod_combine_object_class_def
    by simp
  have "ObjectClass Imod ob \<in> Class (Tm Imod)"
    by (simp add: assms(1) instance_model.structure_object_class_wellformed ob_in_imod)
  then have "\<exclamdown>(ObjectClass Imod ob) \<in> ProperClassType (Tm Imod)"
    by (simp add: ProperClassType.rule_proper_classes)
  then have object_class_is_type: "\<exclamdown>(ObjectClass Imod ob) \<in> Type (Tm Imod)"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  assume f_def: "f \<in> Field (Tm Imod)"
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))) f)"
  then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))] \<exclamdown>(fst f)"
    unfolding class_def
    using ob_class_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    unfolding subtype_def imod_nullable_class_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+ \<union>
    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    then have "ObjectClass Imod ob = fst f"
      unfolding subtype_tuple_def
      by fastforce
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (Tm Imod)"
      unfolding subtype_tuple_def
      using object_class_is_type
      by fastforce
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by simp
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
      unfolding subtype_conv_def tmod_combine_def tmod_nullable_class_field_def
      by simp
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by simp
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (Imod)] \<exclamdown>(fst f)"
    unfolding subtype_def
    by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
  then show "ob \<in> Object Imod \<and> \<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) f)"
    unfolding class_def
    using ob_in_imod
    by blast
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    using assms(1) instance_model.validity_type_model_consistent existing_classes new_field valid_ns
    by (intro tmod_nullable_class_field_combine_correct) (simp_all)
  fix ob f
  assume ob_def: "ob \<in> Object Imod"
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob = ObjectClass Imod ob"
    using classes_valid
    unfolding imod_combine_def imod_nullable_class_field_def imod_combine_object_class_def
    by simp
  then have "ObjectClass Imod ob \<in> Class (Tm Imod)"
    by (simp add: assms(1) instance_model.structure_object_class_wellformed ob_def)
  then have "\<exclamdown>(ObjectClass Imod ob) \<in> ProperClassType (Tm Imod)"
    by (fact ProperClassType.rule_proper_classes)
  then have ob_class_is_type: "\<exclamdown>(ObjectClass Imod ob) \<in> Type (Tm Imod)"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  assume f_def: "f \<in> Field (Tm Imod)"
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))) f)"
  then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))] \<exclamdown>(fst f)"
    unfolding class_def
    using ob_class_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    unfolding subtype_def imod_nullable_class_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+ \<union>
    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
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
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
      unfolding subtype_conv_def tmod_combine_def tmod_nullable_class_field_def
      by simp
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by simp
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then show "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (Imod)] \<exclamdown>(class (Tm Imod) f)"
    unfolding subtype_def class_def
    by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    using assms(1) instance_model.validity_type_model_consistent existing_classes new_field valid_ns
    by (intro tmod_nullable_class_field_combine_correct) (simp_all)
  fix ob f
  assume "ob \<in> Object (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
  then have ob_def: "ob \<in> nilobjects \<union> valobjects \<union> values ` valobjects"
    unfolding imod_nullable_class_field_def
    by simp
  assume "f \<in> Field (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_nullable_class_field_def tmod_nullable_class_field_def
    by simp
  have "\<exclamdown>classtype \<in> ProperClassType (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
    unfolding imod_nullable_class_field_def tmod_nullable_class_field_def
    by (simp add: ProperClassType.rule_proper_classes)
  then have "\<exclamdown>classtype \<in> Type (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  then have classtype_extend: "\<exclamdown>classtype \<sqsubseteq>[Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)] \<exclamdown>classtype"
    unfolding subtype_def
    by (simp add: subtype_rel.reflexivity)
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))) f)"
  then have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values))] \<exclamdown>classtype"
    unfolding class_def
    using f_def
    by simp
  then have "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob), \<exclamdown>classtype) \<in> 
    subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    unfolding subtype_def imod_nullable_class_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob) = \<exclamdown>classtype"
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob), \<exclamdown>classtype) \<in> 
      subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    then show ?thesis
      unfolding subtype_tuple_def
      by fastforce
  next
    assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob), \<exclamdown>classtype) \<in> 
      subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob), \<exclamdown>classtype) \<in> 
      subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then have ob_extends_classtype: "(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob, classtype) \<in> 
      (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
      unfolding subtype_conv_def
      by fastforce
    have "(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob, classtype) \<notin> 
      (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    proof
      assume "(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob, classtype) \<in> 
        (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
      then show "False"
      proof (cases)
        case base
        then show ?thesis
          unfolding tmod_nullable_class_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      next
        case (step c)
        then show ?thesis
          unfolding tmod_nullable_class_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      qed
    qed
    then show ?thesis
      using ob_extends_classtype
      by blast
  next
    assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob), \<exclamdown>classtype) \<in> 
      subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) ob), \<exclamdown>classtype) \<in> 
      subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then have "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob) = \<exclamdown>classtype"
    using existing_objects classes_valid ob_def
    unfolding imod_nullable_class_field_def imod_combine_def imod_combine_object_class_def
    by fastforce
  then show "\<exclamdown>(ObjectClass (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) ob)
    \<sqsubseteq>[Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)]
    \<exclamdown>(class (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)) f)"
    unfolding class_def
    using f_def classtype_extend
    by simp
next
  have "type_model (tmod_combine (Tm Imod) (tmod_nullable_class_field classtype name fieldtype))"
    using assms(1) instance_model.validity_type_model_consistent existing_classes new_field valid_ns
    by (intro tmod_nullable_class_field_combine_correct) (simp_all)
  then show "type_model (tmod_combine (Tm Imod) (Tm (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)))"
    unfolding imod_nullable_class_field_def
    by simp
qed (simp_all add: assms imod_nullable_class_field_def tmod_nullable_class_field_def)



section "Encoding of a class-typed field as edge type in GROOVE"

definition ig_nullable_class_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 'o set \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 'o) \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values = \<lparr>
    TG = tg_nullable_class_field_as_edge_type classtype name fieldtype,
    Id = obids ` nilobjects \<union> obids ` valobjects \<union> obids ` values ` valobjects,
    N = typed (type (id_to_list classtype)) ` nilobjects \<union> typed (type (id_to_list classtype)) ` valobjects \<union> typed (type (id_to_list fieldtype)) ` values ` valobjects,
    E = (\<lambda>x. (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), typed (type (id_to_list fieldtype)) (values x))) ` valobjects,
    ident = (\<lambda>x. if x \<in> obids ` nilobjects \<union> obids ` valobjects then typed (type (id_to_list classtype)) (THE y. obids y = x) else 
      if x \<in> obids ` values ` valobjects then typed (type (id_to_list fieldtype)) (THE y. obids y = x) else undefined)
  \<rparr>"

lemma ig_nullable_class_field_as_edge_type_correct:
  assumes unique_ids: "\<And>o1 o2. o1 \<in> nilobjects \<union> valobjects \<union> values ` valobjects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_value: "valobjects \<inter> nilobjects = {}"
  assumes all_objects: "classtype = fieldtype \<Longrightarrow> values ` valobjects \<subseteq> nilobjects \<union> valobjects"
  assumes no_objects: "classtype \<noteq> fieldtype \<Longrightarrow> values ` valobjects \<inter> (nilobjects \<union> valobjects) = {}"
  shows "instance_graph (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
proof (intro instance_graph.intro)
  fix n
  assume "n \<in> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  then have "n \<in> typed (type (id_to_list classtype)) ` nilobjects \<union> typed (type (id_to_list classtype)) ` valobjects \<union> typed (type (id_to_list fieldtype)) ` values ` valobjects"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  then have type_and_node_def: "type\<^sub>n n \<in> NT (tg_nullable_class_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
  proof (elim UnE)
    assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` nilobjects"
    then show "type\<^sub>n n \<in> NT (tg_nullable_class_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
    proof (intro conjI)
      assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` nilobjects"
      then show "type\<^sub>n n \<in> NT (tg_nullable_class_field_as_edge_type classtype name fieldtype)"
        unfolding tg_nullable_class_field_as_edge_type_def
        by fastforce
    next
      assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` nilobjects"
      then show "n \<in> Node"
        unfolding Node_def
        using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
        by fastforce
    qed
  next
    assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` valobjects"
    then show "type\<^sub>n n \<in> NT (tg_nullable_class_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
    proof (intro conjI)
      assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` valobjects"
      then show "type\<^sub>n n \<in> NT (tg_nullable_class_field_as_edge_type classtype name fieldtype)"
        unfolding tg_nullable_class_field_as_edge_type_def
        by fastforce
    next
      assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` valobjects"
      then show "n \<in> Node"
        unfolding Node_def
        using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
        by fastforce
    qed
  next
    assume "n \<in> typed (LabDef.type (id_to_list fieldtype)) ` values ` valobjects"
    then show "type\<^sub>n n \<in> NT (tg_nullable_class_field_as_edge_type classtype name fieldtype) \<and> n \<in> Node"
    proof (intro conjI)
      assume "n \<in> typed (LabDef.type (id_to_list fieldtype)) ` values ` valobjects"
      then show "type\<^sub>n n \<in> NT (tg_nullable_class_field_as_edge_type classtype name fieldtype)"
        unfolding tg_nullable_class_field_as_edge_type_def
        by fastforce
    next
      assume "n \<in> typed (LabDef.type (id_to_list fieldtype)) ` values ` valobjects"
      then show "n \<in> Node"
        unfolding Node_def
        using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
        by fastforce
    qed
  qed
  then show "type\<^sub>n n \<in> NT (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values))"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  show "n \<in> Node"
    by (simp add: type_and_node_def)
next
  fix s l t
  assume "(s, l, t) \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  then have edge_def: "(s, l, t) \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), 
    typed (type (id_to_list fieldtype)) (values x))) ` valobjects"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  show "s \<in> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) \<and> 
    l \<in> ET (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)) \<and> 
    t \<in> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  proof (intro conjI)
    show "s \<in> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
      unfolding ig_nullable_class_field_as_edge_type_def
      using edge_def
      by fastforce
  next
    have "l = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype))"
      using edge_def
      by blast
    then show "l \<in> ET (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values))"
      unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
      by simp
  next
    show "t \<in> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
      unfolding ig_nullable_class_field_as_edge_type_def
      using edge_def
      by fastforce
  qed
next
  fix i
  assume "i \<in> Id (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  then have i_in_id: "i \<in> obids ` nilobjects \<union> obids ` valobjects \<union> obids ` values ` valobjects"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  then show "ident (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) i \<in> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) \<and> 
    type\<^sub>n (ident (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) i) \<in> Lab\<^sub>t"
  proof (elim UnE)
    assume i_in_id: "i \<in> obids ` nilobjects"
    then show ?thesis
    proof (intro conjI)
      assume "i \<in> obids ` nilobjects"
      then have "(THE y. obids y = i) \<in> nilobjects"
      proof
        fix x
        assume i_def: "i = obids x"
        assume x_is_object: "x \<in> nilobjects"
        have "(THE y. obids y = obids x) \<in> nilobjects"
        proof (rule the1I2)
          show "\<exists>!y. obids y = obids x"
            using Un_iff unique_ids x_is_object
            by metis
        next
          fix y
          assume "obids y = obids x"
          then show "y \<in> nilobjects"
            using Un_iff unique_ids x_is_object
            by metis
        qed
        then show "(THE y. obids y = i) \<in> nilobjects"
          by (simp add: i_def)
      qed
      then have "typed (type (id_to_list classtype)) (THE y. obids y = i) \<in> typed (type (id_to_list classtype)) ` nilobjects"
        by simp
      then show "ident (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) i \<in> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
        unfolding ig_nullable_class_field_as_edge_type_def
        using i_in_id
        by simp
    next
      have "type\<^sub>n (typed (type (id_to_list classtype)) (THE y. obids y = i)) \<in> Lab\<^sub>t"
        by (simp add: Lab\<^sub>t.rule_type_labels)
      then show "type\<^sub>n (ident (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) i) \<in> Lab\<^sub>t"
        unfolding ig_nullable_class_field_as_edge_type_def
        using i_in_id
        by simp
    qed
  next
    assume i_in_id: "i \<in> obids ` valobjects"
    then show ?thesis
    proof (intro conjI)
      assume "i \<in> obids ` valobjects"
      then have "(THE y. obids y = i) \<in> valobjects"
      proof
        fix x
        assume i_def: "i = obids x"
        assume x_is_object: "x \<in> valobjects"
        have "(THE y. obids y = obids x) \<in> valobjects"
        proof (rule the1I2)
          show "\<exists>!y. obids y = obids x"
            using Un_iff unique_ids x_is_object
            by metis
        next
          fix y
          assume "obids y = obids x"
          then show "y \<in> valobjects"
            using Un_iff unique_ids x_is_object
            by metis
        qed
        then show "(THE y. obids y = i) \<in> valobjects"
          by (simp add: i_def)
      qed
      then have "typed (type (id_to_list classtype)) (THE y. obids y = i) \<in> typed (type (id_to_list classtype)) ` valobjects"
        by simp
      then show "ident (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) i \<in> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
        unfolding ig_nullable_class_field_as_edge_type_def
        using i_in_id
        by simp
    next
      have "type\<^sub>n (typed (type (id_to_list classtype)) (THE y. obids y = i)) \<in> Lab\<^sub>t"
        by (simp add: Lab\<^sub>t.rule_type_labels)
      then show "type\<^sub>n (ident (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) i) \<in> Lab\<^sub>t"
        unfolding ig_nullable_class_field_as_edge_type_def
        using i_in_id
        by simp
    qed
  next
    assume i_in_id: "i \<in> obids ` values ` valobjects"
    then show ?thesis
    proof (intro conjI)
      assume "i \<in> obids ` values ` valobjects"
      then have "(THE y. obids y = i) \<in> values ` valobjects"
      proof
        fix x
        assume i_def: "i = obids x"
        assume x_is_object: "x \<in> values ` valobjects"
        have "(THE y. obids y = obids x) \<in> values ` valobjects"
        proof (rule the1I2)
          show "\<exists>!y. obids y = obids x"
            using Un_iff unique_ids x_is_object
            by metis
        next
          fix y
          assume "obids y = obids x"
          then show "y \<in> values ` valobjects"
            using Un_iff unique_ids x_is_object
            by metis
        qed
        then show "(THE y. obids y = i) \<in> values ` valobjects"
          by (simp add: i_def)
      qed
      then have "typed (type (id_to_list fieldtype)) (THE y. obids y = i) \<in> typed (type (id_to_list fieldtype)) ` values ` valobjects"
        by simp
      then show "ident (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) i \<in> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
      proof (induct "classtype = fieldtype")
        case True
        then have "typed (type (id_to_list fieldtype)) (THE y. obids y = i) \<in> typed (type (id_to_list fieldtype)) ` valobjects \<union> typed (type (id_to_list fieldtype)) ` nilobjects"
          using all_objects
          by blast
        then show ?case
          unfolding ig_nullable_class_field_as_edge_type_def
          using True.hyps i_in_id
          by fastforce
      next
        case False
        then have "i \<notin> obids ` nilobjects \<union> obids ` valobjects"
          using no_objects unique_ids i_in_id
          by blast
        then show ?case
          unfolding ig_nullable_class_field_as_edge_type_def
          using False.prems i_in_id
          by simp
      qed
    next
      have "type\<^sub>n (typed (type (id_to_list classtype)) (THE y. obids y = i)) \<in> Lab\<^sub>t \<and> type\<^sub>n (typed (type (id_to_list fieldtype)) (THE y. obids y = i)) \<in> Lab\<^sub>t"
        by (simp add: Lab\<^sub>t.rule_type_labels)
      then show "type\<^sub>n (ident (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) i) \<in> Lab\<^sub>t"
        unfolding ig_nullable_class_field_as_edge_type_def
        using i_in_id
        by simp
    qed
  qed
next
  show "type_graph (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values))"
    unfolding ig_nullable_class_field_as_edge_type_def
    using tg_nullable_class_field_as_edge_type_correct
    by simp
next
  fix e
  assume "e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), 
    typed (type (id_to_list fieldtype)) (values x))) ` valobjects"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  have type_n_def: "type\<^sub>n (src e) = type (id_to_list classtype)"
    using e_def
    by fastforce
  have type_e_def: "src (type\<^sub>e e) = type (id_to_list classtype)"
    using e_def
    by fastforce
  have "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> {(type (id_to_list classtype), type (id_to_list classtype)), (type (id_to_list fieldtype), type (id_to_list fieldtype))}"
    using type_n_def type_e_def
    by blast
  then show "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values))"
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
    by simp
next
  fix e
  assume "e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) x, 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), 
    typed (type (id_to_list fieldtype)) (values x))) ` valobjects"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  have type_n_def: "type\<^sub>n (tgt e) = type (id_to_list fieldtype)"
    using e_def
    by fastforce
  have type_e_def: "tgt (type\<^sub>e e) = type (id_to_list fieldtype)"
    using e_def
    by fastforce
  have "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> {(type (id_to_list classtype), type (id_to_list classtype)), (type (id_to_list fieldtype), type (id_to_list fieldtype))}"
    using type_n_def type_e_def
    by blast
  then show "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values))"
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
    by simp
next
  fix et n
  assume "et \<in> ET (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype))"
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
    by simp
  then have src_et_def: "src et = type (id_to_list classtype)"
    by simp
  have mult_et_def: "m_out (mult (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)) et) = \<^bold>0..\<^bold>1"
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
    by (simp add: et_def)
  assume "n \<in> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  then have n_def: "n \<in> typed (type (id_to_list classtype)) ` nilobjects \<union> typed (type (id_to_list classtype)) ` valobjects \<union> typed (type (id_to_list fieldtype)) ` values ` valobjects"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> inh (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values))"
  then have "(type\<^sub>n n, src et) \<in> {(type (id_to_list classtype), type (id_to_list classtype)), (type (id_to_list fieldtype), type (id_to_list fieldtype))}"
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
    by simp
  then have type_n_def: "type\<^sub>n n = type (id_to_list classtype)"
    using src_et_def
    by fastforce
  then have "n \<in> typed (type (id_to_list classtype)) ` nilobjects \<union> typed (type (id_to_list classtype)) ` valobjects"
  proof (induct "classtype = fieldtype")
    case True
    then show ?case
      using n_def all_objects
      by fastforce
  next
    case False
    then have "type (id_to_list classtype) \<noteq> type (id_to_list fieldtype)"
      using LabDef.inject(1) id_to_list_inverse
      by metis
    then show ?case
      using False.prems n_def
      by fastforce
  qed
  then have "card {e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et} in \<^bold>0..\<^bold>1"
  proof (elim UnE)
    assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` nilobjects"
    then show ?thesis
    proof (elim imageE)
      fix x
      assume x_def: "x \<in> nilobjects"
      assume n_def: "n = typed (LabDef.type (id_to_list classtype)) x"
      then have n_not_def: "n \<notin> typed (LabDef.type (id_to_list classtype)) ` valobjects"
        using x_def n_def unique_value
        by blast
      have "{e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et} = {}"
      proof
        show "{e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et} \<subseteq> {}"
        proof
          fix y
          assume "y \<in> {e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et}"
          then show "y \<in> {}"
          proof
            assume "y \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) \<and> src y = n \<and> type\<^sub>e y = et"
            then show "y \<in> {}"
              unfolding ig_nullable_class_field_as_edge_type_def
              using et_def n_not_def
              by fastforce
          qed
        qed
      next
        show "{} \<subseteq> {e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et}"
          by simp
      qed
      then have "card {e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et} = 0"
        using card_empty
        by metis
      then show ?thesis
        unfolding within_multiplicity_def
        by simp
    qed
  next
    assume "n \<in> typed (LabDef.type (id_to_list classtype)) ` valobjects"
    then show ?thesis
    proof (elim imageE)
      fix x
      assume x_def: "x \<in> valobjects"
      assume n_def: "n = typed (LabDef.type (id_to_list classtype)) x"
      have "{e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et} = 
        {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), typed (type (id_to_list fieldtype)) (values x))}"
      proof
        show "{e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et} \<subseteq> 
          {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), typed (type (id_to_list fieldtype)) (values x))}"
        proof
          fix y
          assume "y \<in> {e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et}"
          then show "y \<in> {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), typed (type (id_to_list fieldtype)) (values x))}"
          proof
            assume "y \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) \<and> src y = n \<and> type\<^sub>e y = et"
            then show "y \<in> {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), typed (type (id_to_list fieldtype)) (values x))}"
              unfolding ig_nullable_class_field_as_edge_type_def
              using et_def n_def
              by fastforce
          qed
        qed
      next
        show "{(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), typed (type (id_to_list fieldtype)) (values x))} \<subseteq> 
          {e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et}"
        proof
          fix y
          assume "y \<in> {(typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), typed (type (id_to_list fieldtype)) (values x))}"
          then have "y = (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), typed (type (id_to_list fieldtype)) (values x))"
            by simp
          then show "y \<in> {e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et}"
            unfolding ig_nullable_class_field_as_edge_type_def
            using et_def n_def x_def
            by simp
        qed
      qed
      then have "card {e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et} = 1"
        by simp
      then show ?thesis
        unfolding within_multiplicity_def
        by simp
    qed
  qed
  then show "card {e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et} in 
    m_out (mult (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)) et)"
    using mult_et_def
    by simp
next
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)) p"
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def instance_graph_containment_proj_def pre_digraph.cycle_def pre_digraph.awalk_def
    by simp
qed (simp_all add: assms ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def)

lemma ig_nullable_class_field_as_edge_type_combine_correct:
  assumes "instance_graph IG"
  assumes existing_node_types: "{type (id_to_list classtype), type (id_to_list fieldtype)} \<subseteq> NT (TG IG)"
  assumes new_edge_type: "\<And>s l t. (type (id_to_list classtype), s) \<in> inh (TG IG) \<Longrightarrow> l = LabDef.edge [name] \<Longrightarrow> (s, l, t) \<notin> ET (TG IG)"
  assumes no_inh_classtype: "\<And>x. (x, type (id_to_list classtype)) \<in> inh (TG IG) \<Longrightarrow> x = type (id_to_list classtype)"
  assumes existing_objects: "N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) \<subseteq> N IG"
  assumes all_objects: "\<And>n. n \<in> N IG \<Longrightarrow> type\<^sub>n n = type (id_to_list classtype) \<Longrightarrow> 
    n \<in> typed (type (id_to_list classtype)) ` nilobjects \<union> typed (type (id_to_list classtype)) ` valobjects"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> nilobjects \<union> valobjects \<union> values ` valobjects \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_value: "valobjects \<inter> nilobjects = {}"
  assumes no_objects: "classtype \<noteq> fieldtype \<Longrightarrow> values ` valobjects \<inter> (nilobjects \<union> valobjects) = {}"
  assumes existing_ids: "obids ` nilobjects \<union> obids ` valobjects \<union> obids ` values ` valobjects \<subseteq> Id IG"
  assumes valid_ids: "\<And>i. i \<in> obids ` nilobjects \<union> obids ` valobjects \<union> obids ` values ` valobjects \<Longrightarrow> 
    ident IG i = ident (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) i"
  shows "instance_graph (ig_combine IG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values))"
proof (intro ig_combine_merge_no_containment_imod2_correct)
  show "instance_graph (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  proof (intro ig_nullable_class_field_as_edge_type_correct)
    assume classtype_fieldtype_eq: "classtype = fieldtype"
    show "values ` valobjects \<subseteq> nilobjects \<union> valobjects"
    proof
      fix x
      assume "x \<in> values ` valobjects"
      then have "typed (type (id_to_list classtype)) x \<in> 
        N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
        unfolding ig_nullable_class_field_as_edge_type_def
        by (simp add: classtype_fieldtype_eq)
      then have "typed (type (id_to_list classtype)) x \<in> N IG"
        using existing_objects
        by blast
      then have "typed (type (id_to_list classtype)) x \<in> typed (type (id_to_list classtype)) ` nilobjects \<union> typed (type (id_to_list classtype)) ` valobjects"
        using all_objects
        by simp
      then show "x \<in> nilobjects \<union> valobjects"
        by blast
    qed
  qed (simp_all add: assms)
next
  have "type_graph (tg_combine (TG IG) (tg_nullable_class_field_as_edge_type classtype name fieldtype))"
    using existing_node_types 
  proof (intro tg_nullable_class_field_as_edge_type_combine_correct)
    fix s l t
    assume "(s, LabDef.type (id_to_list classtype)) \<in> inh (TG IG) \<or> (LabDef.type (id_to_list classtype), s) \<in> inh (TG IG)"
    then have s_def: "(LabDef.type (id_to_list classtype), s) \<in> inh (TG IG)"
      using no_inh_classtype
      by blast
    assume "l = LabDef.edge [name]"
    then show "(s, l, t) \<notin> ET (TG IG)"
      by (simp add: new_edge_type s_def)
  qed (simp_all add: assms(1) instance_graph.validity_type_graph new_edge_type)
  then show "type_graph (tg_combine (TG IG) (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)))"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
next
  show "ET (TG IG) \<inter> ET (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)) = {}"
    using existing_node_types
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
    by (simp add: assms(1) instance_graph.validity_type_graph new_edge_type type_graph.validity_inh_node)
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  then have n_def: "n \<in> N IG"
    using existing_objects
    by blast
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (tg_nullable_class_field_as_edge_type classtype name fieldtype))\<^sup>+"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG))\<^sup>+"
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
    using Un_absorb2 existing_node_types assms(1) insert_subset instance_graph.validity_type_graph sup.orderI sup_bot.right_neutral type_graph.select_convs(3) type_graph.validity_inh_node
    by metis
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  then show "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG) et)"
    using et_def n_def assms(1) instance_graph.validity_outgoing_mult
    by blast
next
  have instance_graph_valid: "instance_graph (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  proof (intro ig_nullable_class_field_as_edge_type_correct)
    assume classtype_fieldtype_eq: "classtype = fieldtype"
    show "values ` valobjects \<subseteq> nilobjects \<union> valobjects"
    proof
      fix x
      assume "x \<in> values ` valobjects"
      then have "typed (type (id_to_list classtype)) x \<in> 
        N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
        unfolding ig_nullable_class_field_as_edge_type_def
        by (simp add: classtype_fieldtype_eq)
      then have "typed (type (id_to_list classtype)) x \<in> N IG"
        using existing_objects
        by blast
      then have "typed (type (id_to_list classtype)) x \<in> typed (type (id_to_list classtype)) ` nilobjects \<union> typed (type (id_to_list classtype)) ` valobjects"
        using all_objects
        by simp
      then show "x \<in> nilobjects \<union> valobjects"
        by blast
    qed
  qed (simp_all add: assms)
  fix et n
  assume et_in_ig: "et \<in> ET (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype))"
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
    by simp
  assume n_set: "n \<in> N IG \<union> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  then have n_def: "n \<in> N IG \<union> typed (type (id_to_list classtype)) ` nilobjects \<union> typed (type (id_to_list classtype)) ` valobjects \<union> typed (type (id_to_list fieldtype)) ` values ` valobjects"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (tg_nullable_class_field_as_edge_type classtype name fieldtype))\<^sup>+"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG))\<^sup>+"
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
    using Un_absorb2 existing_node_types assms(1) insert_subset instance_graph.validity_type_graph sup.orderI sup_bot.right_neutral type_graph.select_convs(3) type_graph.validity_inh_node
    by metis
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  then have "(type\<^sub>n n, type (id_to_list classtype)) \<in> inh (TG IG)"
    using et_def
    by simp
  then have type_n_def: "type\<^sub>n n = type (id_to_list classtype)"
    using no_inh_classtype
    by simp
  then have edge_extend_def: "(type\<^sub>n n, type (id_to_list classtype)) \<in> inh (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values))"
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
    by simp
  have "n \<in> typed (type (id_to_list classtype)) ` nilobjects \<union> typed (type (id_to_list classtype)) ` valobjects"
    using all_objects existing_objects n_set type_n_def
    by blast
  then have "n \<in> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  then show "card {e \<in> E (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values). src e = n \<and> type\<^sub>e e = et} in 
    m_out (mult (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)) et)"
    using edge_extend_def et_def et_in_ig instance_graph_valid instance_graph.validity_outgoing_mult
    by fastforce
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  then have n_def: "n \<in> N IG"
    using existing_objects
    by blast
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (TG (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (tg_nullable_class_field_as_edge_type classtype name fieldtype))\<^sup>+"
    unfolding ig_nullable_class_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG))\<^sup>+"
    unfolding ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def
    using Un_absorb2 existing_node_types assms(1) insert_subset instance_graph.validity_type_graph sup.orderI sup_bot.right_neutral type_graph.select_convs(3) type_graph.validity_inh_node
    by metis
  then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  then show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG) et)"
    using et_def n_def assms(1) instance_graph.validity_ingoing_mult
    by blast
qed (simp_all add: ig_nullable_class_field_as_edge_type_def tg_nullable_class_field_as_edge_type_def assms)



subsection "Transformation functions"

definition imod_nullable_class_field_to_ig_nullable_class_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 'o set \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 'o) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "imod_nullable_class_field_to_ig_nullable_class_field_as_edge_type classtype name fieldtype nilobjects valobjects obids values Imod = \<lparr>
    TG = tg_nullable_class_field_as_edge_type classtype name fieldtype,
    Id = obids ` Object Imod,
    N = typed (type (id_to_list classtype)) ` {ob \<in> Object Imod. ob \<in> nilobjects \<union> valobjects} \<union> typed (type (id_to_list fieldtype)) ` {ob \<in> Object Imod. ob \<in> values ` valobjects},
    E = (\<lambda>x. (typed (type (id_to_list classtype)) x, (type (id_to_list classtype), LabDef.edge [name], type (id_to_list fieldtype)), typed (type (id_to_list fieldtype)) (values x))) ` {ob \<in> Object Imod. ob \<in> valobjects},
    ident = (\<lambda>x. if x \<in> obids ` nilobjects \<or> x \<in> obids ` valobjects then typed (type (id_to_list classtype)) (THE y. obids y = x) else 
      if x \<in> obids ` values ` valobjects then typed (type (id_to_list fieldtype)) (THE y. obids y = x) else undefined)
  \<rparr>"

lemma imod_nullable_class_field_to_ig_nullable_class_field_as_edge_type_proj:
  shows "imod_nullable_class_field_to_ig_nullable_class_field_as_edge_type classtype name fieldtype nilobjects valobjects obids values (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) = 
    ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values"
  unfolding imod_nullable_class_field_to_ig_nullable_class_field_as_edge_type_def ig_nullable_class_field_as_edge_type_def imod_nullable_class_field_def
  by auto

lemma imod_nullable_class_field_to_ig_nullable_class_field_as_edge_type_func:
  shows "ig_combine_mapping_function (imod_nullable_class_field_to_ig_nullable_class_field_as_edge_type classtype name fieldtype nilobjects valobjects obids values)
    (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values) (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values)"
  by (intro ig_combine_mapping_function.intro)
    (auto simp add: imod_nullable_class_field_to_ig_nullable_class_field_as_edge_type_def imod_nullable_class_field_def ig_nullable_class_field_as_edge_type_def imod_combine_def)

definition ig_nullable_class_field_as_edge_type_to_imod_nullable_class_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> 'o set \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 'o) \<Rightarrow> ('o, 't list, 't) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "ig_nullable_class_field_as_edge_type_to_imod_nullable_class_field classtype name fieldtype nilobjects valobjects obids values IG = \<lparr>
    Tm = tmod_nullable_class_field classtype name fieldtype,
    Object = nodeId ` N IG,
    ObjectClass = (\<lambda>x. if x \<in> nilobjects \<union> valobjects then classtype else 
      if x \<in> values ` valobjects then fieldtype else undefined),
    ObjectId = (\<lambda>x. if x \<in> nilobjects \<union> valobjects \<union> values ` valobjects then obids x else undefined),
    FieldValue = (\<lambda>x. if fst x \<in> nilobjects \<and> snd x = (classtype, name) then nil else 
      if fst x \<in> valobjects \<and> snd x = (classtype, name) then obj (values (fst x)) else
      if fst x \<in> values ` valobjects \<and> snd x = (classtype, name) then unspecified else undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_nullable_class_field_as_edge_type_to_imod_nullable_class_field_proj:
  shows "ig_nullable_class_field_as_edge_type_to_imod_nullable_class_field classtype name fieldtype nilobjects valobjects obids values (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) = 
    imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values"
proof-
  have "nodeId ` (typed (LabDef.type (id_to_list classtype)) ` nilobjects) = nilobjects"
    by force
  then have nilobjects_def: "\<And>x. x \<in> nilobjects \<Longrightarrow> 
    x \<in> nodeId ` (typed (LabDef.type (id_to_list classtype)) ` nilobjects \<union> typed (LabDef.type (id_to_list classtype)) ` valobjects \<union> typed (LabDef.type (id_to_list fieldtype)) ` values ` valobjects)"
    by blast
  have "nodeId ` (typed (LabDef.type (id_to_list classtype)) ` valobjects) = valobjects"
    by force
  then have valobjects_def: "\<And>x. x \<in> valobjects \<Longrightarrow> 
    x \<in> nodeId ` (typed (LabDef.type (id_to_list classtype)) ` nilobjects \<union> typed (LabDef.type (id_to_list classtype)) ` valobjects \<union> typed (LabDef.type (id_to_list fieldtype)) ` values ` valobjects)"
    by blast
  have "nodeId ` (typed (LabDef.type (id_to_list fieldtype)) ` values ` valobjects) = values ` valobjects"
    by force
  then have values_def: "\<And>x. x \<in> values ` valobjects \<Longrightarrow> 
    x \<in> nodeId ` (typed (LabDef.type (id_to_list classtype)) ` nilobjects \<union> typed (LabDef.type (id_to_list classtype)) ` valobjects \<union> typed (LabDef.type (id_to_list fieldtype)) ` values ` valobjects)"
    by blast
  show "ig_nullable_class_field_as_edge_type_to_imod_nullable_class_field classtype name fieldtype nilobjects valobjects obids values (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) = 
    imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values"
    unfolding ig_nullable_class_field_as_edge_type_to_imod_nullable_class_field_def imod_nullable_class_field_def ig_nullable_class_field_as_edge_type_def
    using nilobjects_def valobjects_def values_def
    by auto
qed

lemma ig_nullable_class_field_as_edge_type_to_imod_nullable_class_field_func:
  shows "imod_combine_mapping_function (ig_nullable_class_field_as_edge_type_to_imod_nullable_class_field classtype name fieldtype nilobjects valobjects obids values)
    (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) (imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values)"
proof (intro imod_combine_mapping_function.intro)
  show "ig_nullable_class_field_as_edge_type_to_imod_nullable_class_field classtype name fieldtype nilobjects valobjects obids values (ig_nullable_class_field_as_edge_type classtype name fieldtype valobjects nilobjects obids values) =
    imod_nullable_class_field classtype name fieldtype valobjects nilobjects obids values"
    by (fact ig_nullable_class_field_as_edge_type_to_imod_nullable_class_field_proj)
qed (auto simp add: ig_nullable_class_field_as_edge_type_to_imod_nullable_class_field_def imod_nullable_class_field_def ig_nullable_class_field_as_edge_type_def ig_combine_def)

end