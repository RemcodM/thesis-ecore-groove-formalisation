theory ContainedClassSetFieldValue
  imports
    Main
    "Ecore-GROOVE-Mapping.Instance_Model_Graph_Mapping"
    ContainedClassSetField
begin

section "Definition of an instance model which introduces values for a field typed by a class that can be nullable"

inductive_set sets_to_set :: "'a set set \<Rightarrow> 'a set"
  for A :: "'a set set"
  where
    rule_member: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> x \<Longrightarrow> y \<in> sets_to_set A"

definition imod_contained_class_set_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> multiplicity \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 'o list) \<Rightarrow> ('o, 't) instance_model" where
  "imod_contained_class_set_field classtype name containedtype mul objects obids values = \<lparr>
    Tm = tmod_contained_class_set_field classtype name containedtype mul,
    Object = objects \<union> sets_to_set (set ` values ` objects),
    ObjectClass = (\<lambda>x. if x \<in> objects then classtype else if x \<in> sets_to_set (set ` values ` objects) then containedtype else undefined),
    ObjectId = (\<lambda>x. if x \<in> objects \<union> sets_to_set (set ` values ` objects) then obids x else undefined),
    FieldValue = (\<lambda>x. if fst x \<in> objects \<and> snd x = (classtype, name) then setof (map obj (values (fst x))) else
      if fst x \<in> sets_to_set (set ` values ` objects) \<and> snd x = (classtype, name) then unspecified else undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_contained_class_set_field_correct:
  assumes valid_ns: "\<not>id_in_ns containedtype (Identifier classtype) \<and> \<not>id_in_ns classtype (Identifier containedtype)"
  assumes valid_mul: "multiplicity mul"
  assumes classtype_containedtype_neq: "classtype \<noteq> containedtype"
  assumes objects_unique: "objects \<inter> sets_to_set (set ` values ` objects) = {}"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<union> sets_to_set (set ` values ` objects) \<Longrightarrow> 
    o2 \<in> objects \<union> sets_to_set (set ` values ` objects) \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_sets: "\<And>ob. ob \<in> objects \<Longrightarrow> distinct (values ob)"
  assumes unique_across_sets: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> o2 \<in> objects \<Longrightarrow> o1 \<noteq> o2 \<Longrightarrow> set (values o1) \<inter> set (values o2) = {}"
  assumes valid_sets: "\<And>ob. ob \<in> objects \<Longrightarrow> length (values ob) in mul"
  shows "instance_model (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
proof (intro instance_model.intro)
  fix ob
  assume "ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
  then have "ob \<in> objects \<union> sets_to_set (set ` values ` objects)"
    unfolding imod_contained_class_set_field_def
    by simp
  then have "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob = classtype \<or>
    ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob = containedtype"
    unfolding imod_contained_class_set_field_def
    by fastforce
  then show "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob \<in> 
    Class (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
    by simp
next
  show "type_model (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    unfolding imod_contained_class_set_field_def
    using tmod_contained_class_set_field_correct valid_ns valid_mul
    by simp
next
  fix ob f
  assume "ob \<notin> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values) \<or> 
    f \<notin> type_model.Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
  then have "ob \<notin> objects \<union> sets_to_set (set ` values ` objects) \<or> f \<noteq> (classtype, name)"
    unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
    by simp
  then show "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f) = undefined"
    unfolding imod_contained_class_set_field_def
    by auto
next
  fix ob f
  assume "ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
  then have ob_def: "ob \<in> objects \<union> sets_to_set (set ` values ` objects)"
    unfolding imod_contained_class_set_field_def
    by simp
  assume "f \<in> type_model.Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
    by simp
  assume no_inh: "\<not>\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob) 
    \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] 
    \<exclamdown>(class (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) f)"
  show "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f) = unspecified"
    using ob_def
  proof (elim UnE)
    assume "ob \<in> objects"
    then have ob_class_def: "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob = classtype"
      unfolding imod_contained_class_set_field_def
      by simp
    then have "\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob) \<in> 
      ProperClassType (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
      by (simp add: ProperClassType.rule_proper_classes imod_contained_class_set_field_def tmod_contained_class_set_field_def)
    then have ob_type_def: "\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob) \<in> 
      Type (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
      unfolding Type_def NonContainerType_def ClassType_def
      by blast
    have "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob = 
      class (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) f"
      unfolding class_def
      by (simp add: f_def ob_class_def)
    then have "\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob) 
      \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] 
      \<exclamdown>(class (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) f)"
      unfolding subtype_def
      using ob_type_def subtype_rel.reflexivity
      by simp
    then show ?thesis
      using no_inh
      by blast
  next
    assume "ob \<in> sets_to_set (set ` values ` objects)"
    then show ?thesis
      unfolding imod_contained_class_set_field_def
      using objects_unique f_def
      by fastforce
  qed
next
  have type_model_correct: "type_model (tmod_contained_class_set_field classtype name containedtype mul)"
    using tmod_contained_class_set_field_correct valid_ns valid_mul
    by metis
  fix ob f
  assume "ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
  then have ob_cases: "ob \<in> objects \<union> sets_to_set (set ` values ` objects)"
    unfolding imod_contained_class_set_field_def
    by simp
  assume "f \<in> type_model.Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
    by simp
  then have f_type: "Type_Model.type (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) f = TypeDef.setof \<exclamdown>containedtype"
    unfolding Type_Model.type_def imod_contained_class_set_field_def tmod_contained_class_set_field_def
    by simp
  have f_lower: "lower (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) f = Multiplicity.lower mul"
    unfolding lower_def imod_contained_class_set_field_def tmod_contained_class_set_field_def
    using f_def
    by simp
  have f_upper: "upper (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) f = Multiplicity.upper mul"
    unfolding upper_def imod_contained_class_set_field_def tmod_contained_class_set_field_def
    using f_def
    by simp
  assume "\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob)
    \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)]
    \<exclamdown>(class (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) f)"
  then have "\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob)
    \<sqsubseteq>[tmod_contained_class_set_field classtype name containedtype mul] \<exclamdown>(fst f)"
    unfolding imod_contained_class_set_field_def class_def
    by simp
  then have "(\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob), \<exclamdown>(fst f)) \<in> 
    subtype_rel_altdef (tmod_contained_class_set_field classtype name containedtype mul)"
    using subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_correct
    by blast
  then have ob_def: "ob \<in> objects"
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob), \<exclamdown>(fst f)) \<in> 
      subtype_tuple ` Type (tmod_contained_class_set_field classtype name containedtype mul)"
    then have eq: "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob = fst f"
      by (simp add: image_iff subtype_tuple_def)
    show ?thesis
      using ob_cases
    proof (elim UnE)
      assume "ob \<in> objects"
      then show ?thesis
        by simp
    next
      assume "ob \<in> sets_to_set (set ` values ` objects)"
      then have ob_class_def: "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob = containedtype"
        unfolding imod_contained_class_set_field_def
        using objects_unique
        by auto
      then show ?thesis
        using eq classtype_containedtype_neq f_def
        by simp
    qed
  next
    assume "(\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob), \<exclamdown>(fst f)) \<in> 
      subtype_conv nullable nullable ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob), \<exclamdown>(fst f)) \<in> 
      subtype_conv proper proper ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
    then show ?thesis
      unfolding tmod_contained_class_set_field_def
      by auto
  next
    assume "(\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob), \<exclamdown>(fst f)) \<in> 
      subtype_conv proper nullable ` subtype_tuple ` Class (tmod_contained_class_set_field classtype name containedtype mul)"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob), \<exclamdown>(fst f)) \<in>
      subtype_conv proper nullable ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then have value_def: "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f) = setof (map obj (values (ob)))"
    unfolding imod_contained_class_set_field_def
    using f_def
    by fastforce
  have value_valid: "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f) 
    :[imod_contained_class_set_field classtype name containedtype mul objects obids values] TypeDef.setof \<exclamdown>containedtype"
    unfolding Valid_def
  proof (rule Valid_rel.valid_rule_sets)
    show "TypeDef.setof \<exclamdown>containedtype \<in> SetContainerType (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    proof (intro SetContainerType.rule_setof_all_type)
      show "\<exclamdown>containedtype \<in> Type (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
        unfolding Type_def NonContainerType_def ClassType_def
        by (simp add: ProperClassType.rule_proper_classes imod_contained_class_set_field_def tmod_contained_class_set_field_def)
    qed
  next
    have "setof (map obj (values ob)) \<in> SetContainerValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
    proof (induct "values ob = []")
      case True
      show ?case
      proof (rule SetContainerValue.rule_setof_container_values)
        show "map obj (values ob) \<in> ContainerValueList (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          using ContainerValueList.rule_empty_list True.hyps
          by simp
      qed
    next
      case False
      show ?case
      proof (rule SetContainerValue.rule_setof_atom_values)
        have "set (map obj (values ob)) \<subseteq> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
        proof
          fix x :: "('b, 'a) ValueDef"
          assume assump: "x \<in> set (map obj (values ob))"
          have "set (values ob) \<subseteq> sets_to_set (set ` values ` objects)"
          proof
            fix x
            assume "x \<in> set (values ob)"
            then show "x \<in> sets_to_set (set ` values ` objects)"
              using ob_def imageI sets_to_set.rule_member
              by metis
          qed
          then have "x \<in> obj ` sets_to_set (set ` values ` objects)"
            using assump
            by fastforce
          then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          proof
            fix y
            assume x_def: "x = obj y"
            assume y_def: "y \<in> sets_to_set (set ` values ` objects)"
            then have "obj y \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
            proof (intro ProperClassValue.rule_proper_objects)
              assume "y \<in> sets_to_set (set ` values ` objects)"
              then show "y \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                unfolding imod_contained_class_set_field_def
                by simp
            qed
            then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
              using x_def
              by blast
          qed
        qed
        then have "set (map obj (values ob)) \<subseteq> AtomValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          using proper_class_values_are_atom_values
          by blast
        then show "map obj (values ob) \<in> AtomValueList (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          using False.hyps list.map_disc_iff list_of_atom_values_in_atom_value_list_alt
          by metis
      qed
    qed
    then show "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f) \<in> 
      SetContainerValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      using distinct_map
      by (simp add: value_def)
  next
    have "inj_on obj (set (values ob))"
      unfolding inj_on_def
      by blast
    then have distinct_map_def: "distinct (map obj (values ob))"
      using unique_sets ob_def
      by (simp add: distinct_map)
    have "\<And>x1 x2. x1 \<in> set (map obj (values ob)) \<Longrightarrow> x2 \<in> set (map obj (values ob)) \<Longrightarrow> 
      x1 \<equiv>[imod_contained_class_set_field classtype name containedtype mul objects obids values] x2 \<Longrightarrow> x1 = x2"
    proof-
      fix x1 x2
      have set_in_sets: "set (values ob) \<subseteq> sets_to_set (set ` values ` objects)"
      proof
        fix x
        assume "x \<in> set (values ob)"
        then show "x \<in> sets_to_set (set ` values ` objects)"
          using ob_def imageI sets_to_set.rule_member
          by metis
      qed
      assume equiv: "x1 \<equiv>[imod_contained_class_set_field classtype name containedtype mul objects obids values] x2"
      assume "x1 \<in> set (map obj (values ob))"
      then have "x1 \<in> obj ` sets_to_set (set ` values ` objects)"
        using set_in_sets
        by fastforce
      then have x1_def: "x1 \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      proof
        fix y
        assume x_def: "x1 = obj y"
        assume y_def: "y \<in> sets_to_set (set ` values ` objects)"
        then have "obj y \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
        proof (intro ProperClassValue.rule_proper_objects)
          assume "y \<in> sets_to_set (set ` values ` objects)"
          then show "y \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
            unfolding imod_contained_class_set_field_def
            by simp
        qed
        then show "x1 \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          using x_def
          by blast
      qed
      assume "x2 \<in> set (map obj (values ob))"
      then have "x2 \<in> obj ` sets_to_set (set ` values ` objects)"
        using set_in_sets
        by fastforce
      then have x2_def: "x2 \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      proof
        fix y
        assume x_def: "x2 = obj y"
        assume y_def: "y \<in> sets_to_set (set ` values ` objects)"
        then have "obj y \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
        proof (intro ProperClassValue.rule_proper_objects)
          assume "y \<in> sets_to_set (set ` values ` objects)"
          then show "y \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
            unfolding imod_contained_class_set_field_def
            by simp
        qed
        then show "x2 \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          using x_def
          by blast
      qed
      show "x1 = x2"
        using equiv x1_def x2_def
      proof (induct)
        case (rule_atom_equiv v1 v2)
        then show ?case
          unfolding Value_def AtomValue_def ClassValue_def
          by blast
      qed (simp_all)
    qed
    then have "distinct_values (imod_contained_class_set_field classtype name containedtype mul objects obids values) (map obj (values ob))"
      using distinct_values_impl_distinct_rev distinct_map_def
      by blast
    then show "distinct_values (imod_contained_class_set_field classtype name containedtype mul objects obids values) 
      (contained_list (FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f)))"
      by (simp add: value_def)
  next
    have set_in_sets: "set (values ob) \<subseteq> sets_to_set (set ` values ` objects)"
    proof
      fix x
      assume "x \<in> set (values ob)"
      then show "x \<in> sets_to_set (set ` values ` objects)"
        using ob_def imageI sets_to_set.rule_member
        by metis
    qed
    fix x
    assume "x \<in> set (contained_list (FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f)))"
    then have "x \<in> set (map obj (values ob))"
      by (simp add: value_def)
    then have x_def: "x \<in> obj ` sets_to_set (set ` values ` objects)"
      using set_in_sets
      by fastforce
    then have x_class_value: "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
    proof
      fix y
      assume x_def: "x = obj y"
      assume y_def: "y \<in> sets_to_set (set ` values ` objects)"
      then have "obj y \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      proof (intro ProperClassValue.rule_proper_objects)
        assume "y \<in> sets_to_set (set ` values ` objects)"
        then show "y \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          unfolding imod_contained_class_set_field_def
          by simp
      qed
      then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
        using x_def
        by blast
    qed
    have "(\<exclamdown>containedtype, x) \<in> Valid_rel (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      using x_def
    proof (elim imageE)
      fix y
      assume x_def: "x = obj y"
      assume "y \<in> sets_to_set (set ` values ` objects)"
      then have "(\<exclamdown>containedtype, obj y) \<in> Valid_rel (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      proof (intro Valid_rel.valid_rule_proper_classes)
        assume "y \<in> sets_to_set (set ` values ` objects)"
        then show "y \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          by (simp add: imod_contained_class_set_field_def)
      next
        show "\<exclamdown>containedtype \<in> ClassType (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
          unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def ClassType_def
          by (simp add: ProperClassType.rule_proper_classes)
        then have containedtype_def: "\<exclamdown>containedtype \<in> Type (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
          unfolding Type_def NonContainerType_def
          by blast
        assume "y \<in> sets_to_set (set ` values ` objects)"
        then have "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) y = containedtype"
          unfolding imod_contained_class_set_field_def
          using objects_unique
          by fastforce
        then show "\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) y) 
          \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)]
          \<exclamdown>containedtype"
          using containedtype_def
          by (simp add: subtype_def subtype_rel.reflexivity)
      qed
      then show "(\<exclamdown>containedtype, x) \<in> Valid_rel (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
        using x_def
        by simp
    qed
    then show "(contained_type (TypeDef.setof \<exclamdown>containedtype), x) \<in> Valid_rel (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      by simp
  qed
  then show "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f) 
    :[imod_contained_class_set_field classtype name containedtype mul objects obids values] 
    Type_Model.type (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) f"
    using value_def f_type
    by simp
  have values_are_class_values: "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f) \<in> 
    SetContainerValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
    using value_valid
    unfolding Valid_def
    by (cases) (simp_all add: value_def)
  then show "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f) \<in>
    Value (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
    unfolding Value_def
    using set_container_values_are_container_values
    by blast
  have "validMul (imod_contained_class_set_field classtype name containedtype mul objects obids values) ((ob, f), 
    FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f))"
    unfolding validMul_def
  proof (intro conjI)
    show "snd ((ob, f), FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f)) \<in> 
      ContainerValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) \<longrightarrow>
      lower (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (snd (fst ((ob, f), FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f)))) \<le> 
      \<^bold>(length (contained_list (snd ((ob, f), FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f))))) \<and>
      \<^bold>(length (contained_list (snd ((ob, f), FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f))))) \<le> 
      upper (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (snd (fst ((ob, f), FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f))))"
    proof
      assume "snd ((ob, f), FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f)) \<in> 
        ContainerValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      then have "Multiplicity.lower mul \<le> \<^bold>(length (map obj (values ob))) \<and>
        \<^bold>(length (map obj (values ob))) \<le> Multiplicity.upper mul"
        using valid_sets ob_def
        unfolding within_multiplicity_def
        by simp
      then show "lower (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (snd (fst ((ob, f), FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f)))) \<le> 
        \<^bold>(length (contained_list (snd ((ob, f), FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f))))) \<and>
        \<^bold>(length (contained_list (snd ((ob, f), FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f))))) \<le> 
        upper (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (snd (fst ((ob, f), FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f))))"
        using f_lower f_upper value_def
        by simp
    qed
  qed (simp_all add: value_valid f_type)
  then show "validMul (imod_contained_class_set_field classtype name containedtype mul objects obids values) ((ob, f), FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ob, f))"
    by (simp add: value_def)
next
  have type_model_correct: "type_model (tmod_contained_class_set_field classtype name containedtype mul)"
    using tmod_contained_class_set_field_correct valid_ns valid_mul
    by metis
  have no_attr_type: "TypeDef.setof \<exclamdown>containedtype \<notin> AttrType (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
  proof
    assume "TypeDef.setof \<exclamdown>containedtype \<in> AttrType (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    then show "False"
      by (cases) (simp_all)
  qed
  have no_attr: "(classtype, name) \<notin> Attr (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
  proof
    have containedtype_def: "Type_Model.type (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (classtype, name) = TypeDef.setof \<exclamdown>containedtype"
      unfolding Type_Model.type_def imod_contained_class_set_field_def tmod_contained_class_set_field_def
      by simp
    assume "(classtype, name) \<in> Attr (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    then show "False"
      unfolding Attr_def
      using containedtype_def no_attr_type
      by simp
  qed
  have rel_def: "Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) = {(classtype, name)}"
  proof
    show "Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) \<subseteq> {(classtype, name)}"
    proof
      fix x
      assume "x \<in> Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
      then show "x \<in> {(classtype, name)}"
        unfolding Rel_def imod_contained_class_set_field_def tmod_contained_class_set_field_def
        by simp
    qed
  next
    show "{(classtype, name)} \<subseteq> Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    proof
      fix x
      assume "x \<in> {(classtype, name)}"
      then have "x = (classtype, name)"
        by simp
      then show "x \<in> Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
        using no_attr
        unfolding Rel_def imod_contained_class_set_field_def tmod_contained_class_set_field_def
        by simp
    qed
  qed
  have cr_def: "CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) = {(classtype, name)}"
  proof
    show "CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) \<subseteq> {(classtype, name)}"
    proof
      fix x
      assume "x \<in> CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
      then show "x \<in> {(classtype, name)}"
      proof (induct)
        case (rule_containment_relations r)
        then show ?case
          using rel_def
          unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
          by blast
      qed
    qed
  next
    show "{(classtype, name)} \<subseteq> CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    proof
      fix x
      assume "x \<in> {(classtype, name)}"
      then have x_def: "x = (classtype, name)"
        by simp
      show "x \<in> CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
      proof (rule CR.rule_containment_relations)
        show "x \<in> Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
          using x_def rel_def
          by simp
      next
        show "containment x \<in> Prop (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
          unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
          using x_def
          by simp
      qed
    qed
  qed
  fix p
  assume "p \<in> Prop (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
  then have p_def: "p = containment (classtype, name)"
    unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
    by simp
  have "imod_contained_class_set_field classtype name containedtype mul objects obids values \<Turnstile> containment (classtype, name)"
  proof (rule property_satisfaction.rule_property_containment)
    fix ob
    assume "ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
    then have ob_cases: "ob \<in> objects \<union> sets_to_set (set ` values ` objects)"
      unfolding imod_contained_class_set_field_def
      by simp
    then show "card (object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob) \<le> 1"
    proof (elim UnE)
      assume ob_def: "ob \<in> objects"
      have "object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob = {}"
      proof
        show "object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob \<subseteq> {}"
        proof
          fix x
          assume "x \<in> object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
          then show "x \<in> {}"
          proof (induct x)
            case (Pair a d)
            then show ?case
            proof (induct a)
              case (fields a b c)
              then show ?case
              proof (induct)
                case (rule_object_containment o1 r)
                then have r_def: "r = (classtype, name)"
                  using cr_def
                  by simp
                then have o1_cases: "o1 \<in> objects \<union> sets_to_set (set ` values ` objects)"
                  using rule_object_containment.hyps(1)
                  unfolding imod_contained_class_set_field_def
                  by simp
                then show ?case
                proof (elim UnE)
                  assume o1_def: "o1 \<in> objects"
                  then have o1_class_def: "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1 = classtype"
                    unfolding imod_contained_class_set_field_def
                    by simp
                  have value_def: "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r) = setof (map obj (values o1))"
                    unfolding imod_contained_class_set_field_def
                    using o1_def r_def
                    by simp
                  have set_in_sets: "set (values o1) \<subseteq> sets_to_set (set ` values ` objects)"
                  proof
                    fix x
                    assume "x \<in> set (values o1)"
                    then show "x \<in> sets_to_set (set ` values ` objects)"
                      using o1_def imageI sets_to_set.rule_member
                      by metis
                  qed
                  have "set (map obj (values o1)) \<subseteq> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                  proof
                    fix x :: "('b, 'a) ValueDef"
                    assume "x \<in> set (map obj (values o1))"
                    then have "x \<in> obj ` sets_to_set (set ` values ` objects)"
                      using set_in_sets
                      by fastforce
                    then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                    proof
                      fix y
                      assume x_def: "x = obj y"
                      assume y_def: "y \<in> sets_to_set (set ` values ` objects)"
                      then have "obj y \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                      proof (intro ProperClassValue.rule_proper_objects)
                        assume "y \<in> sets_to_set (set ` values ` objects)"
                        then show "y \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                          unfolding imod_contained_class_set_field_def
                          by simp
                      qed
                      then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                        using x_def
                        by blast
                    qed
                  qed
                  then have "set (map obj (values o1)) \<subseteq> AtomValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                    using proper_class_values_are_atom_values
                    by blast
                  then have "map obj (values o1) = [] \<or> map obj (values o1) \<in> AtomValueList (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                    using list.map_disc_iff list_of_atom_values_in_atom_value_list_alt
                    by metis
                  then have contained_values_def: "contained_values (FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r)) = map obj (values o1)"
                    using value_def atom_value_list_contained_values_setof_identity
                    by fastforce
                  have "obj ob \<notin> set (map obj (values o1))"
                  proof
                    have ob_not_in_sets: "ob \<notin> sets_to_set (set ` values ` objects)"
                      using ob_def objects_unique
                      by blast
                    assume "obj ob \<in> set (map obj (values o1))"
                    then have "ob \<in> set (values o1)"
                      by fastforce
                    then have "ob \<in> sets_to_set (set ` values ` objects)"
                      using set_in_sets
                      by blast
                    then show "False"
                      using ob_not_in_sets
                      by simp
                  qed
                  then show ?thesis
                    using contained_values_def rule_object_containment.hyps(4)
                    by metis
                next
                  assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
                  then have o1_class_def: "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1 = containedtype"
                    unfolding imod_contained_class_set_field_def
                    using objects_unique
                    by fastforce
                  have "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] \<exclamdown>classtype"
                  proof
                    assume "\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] \<exclamdown>classtype"
                    then have "\<exclamdown>containedtype \<sqsubseteq>[tmod_contained_class_set_field classtype name containedtype mul] \<exclamdown>classtype"
                      unfolding imod_contained_class_set_field_def class_def
                      by simp
                    then have "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_rel_altdef (tmod_contained_class_set_field classtype name containedtype mul)"
                      using subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_correct
                      by blast
                    then show "False"
                      unfolding subtype_rel_altdef_def
                    proof (elim UnE)
                      assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_tuple ` Type (tmod_contained_class_set_field classtype name containedtype mul)"
                      then have "classtype = containedtype"
                        by (simp add: image_iff subtype_tuple_def)
                      then show ?thesis
                        using classtype_containedtype_neq
                        by blast
                    next
                      assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv nullable nullable ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
                      then show ?thesis
                        unfolding subtype_conv_def
                        by blast
                    next
                      assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper proper ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
                      then show ?thesis
                        unfolding tmod_contained_class_set_field_def
                        by auto
                    next
                      assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_contained_class_set_field classtype name containedtype mul)"
                      then show ?thesis
                        unfolding subtype_conv_def
                        by blast
                    next
                      assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper nullable ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
                      then show ?thesis
                        unfolding subtype_conv_def
                        by blast
                    qed
                  qed
                  then have "r \<notin> Type_Model.fields (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) containedtype"
                    unfolding Type_Model.fields_def
                    using r_def
                    by simp
                  then show ?thesis
                    using o1_class_def rule_object_containment.hyps(3)
                    by simp
                qed
              qed
            qed
          qed
        qed
      next
        show "{} \<subseteq> object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
          by simp
      qed
      then show ?thesis
        using card_empty
        by simp
    next
      assume ob_def: "ob \<in> sets_to_set (set ` values ` objects)"
      then show ?thesis
      proof
        fix x y
        assume x_def: "x \<in> set ` values ` objects"
        assume y_def: "y \<in> x"
        assume "ob = y"
        then have "ob \<in> x"
          using y_def
          by simp
        then show ?thesis
          using x_def
        proof (elim imageE)
          fix i j
          assume j_def: "j \<in> objects"
          assume i_def: "i = values j"
          assume "x = set i"
          then have x_def: "x = set (values j)"
            by (simp add: i_def)
          assume "ob \<in> x"
          then have ob_def: "ob \<in> set (values j)"
            by (simp add: x_def)
          have "object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob \<subseteq> {((j, (classtype, name)), ob)}"
          proof
            fix x
            assume "x \<in> object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
            then show "x \<in> {((j, (classtype, name)), ob)}"
            proof (induct x)
              case (Pair a d)
              then show ?case
              proof (induct a)
                case (fields a b c)
                then show ?case
                proof (induct)
                  case (rule_object_containment o1 r)
                  then have r_def: "r = (classtype, name)"
                    using cr_def
                    by simp
                  then have o1_cases: "o1 \<in> objects \<union> sets_to_set (set ` values ` objects)"
                    using rule_object_containment.hyps(1)
                    unfolding imod_contained_class_set_field_def
                    by simp
                  then show ?case
                  proof (elim UnE)
                    assume o1_def: "o1 \<in> objects"
                    then have o1_class_def: "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1 = classtype"
                      unfolding imod_contained_class_set_field_def
                      by simp
                    have value_def: "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r) = setof (map obj (values o1))"
                      unfolding imod_contained_class_set_field_def
                      using o1_def r_def
                      by simp
                    have set_in_sets: "set (values o1) \<subseteq> sets_to_set (set ` values ` objects)"
                    proof
                      fix x
                      assume "x \<in> set (values o1)"
                      then show "x \<in> sets_to_set (set ` values ` objects)"
                        using o1_def imageI sets_to_set.rule_member
                        by metis
                    qed
                    have "set (map obj (values o1)) \<subseteq> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                    proof
                      fix x :: "('b, 'a) ValueDef"
                      assume "x \<in> set (map obj (values o1))"
                      then have "x \<in> obj ` sets_to_set (set ` values ` objects)"
                        using set_in_sets
                        by fastforce
                      then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                      proof
                        fix y
                        assume x_def: "x = obj y"
                        assume y_def: "y \<in> sets_to_set (set ` values ` objects)"
                        then have "obj y \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                        proof (intro ProperClassValue.rule_proper_objects)
                          assume "y \<in> sets_to_set (set ` values ` objects)"
                          then show "y \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                            unfolding imod_contained_class_set_field_def
                            by simp
                        qed
                        then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                          using x_def
                          by blast
                      qed
                    qed
                    then have "set (map obj (values o1)) \<subseteq> AtomValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                      using proper_class_values_are_atom_values
                      by blast
                    then have "map obj (values o1) = [] \<or> map obj (values o1) \<in> AtomValueList (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                      using list.map_disc_iff list_of_atom_values_in_atom_value_list_alt
                      by metis
                    then have contained_values_def: "contained_values (FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r)) = map obj (values o1)"
                      using value_def atom_value_list_contained_values_setof_identity
                      by fastforce
                    then have "obj ob \<in> set (map obj (values o1))"
                      using rule_object_containment.hyps(4)
                      by fastforce
                    then have ob_in_set_def: "ob \<in> set (values o1)"
                      using rule_object_containment.hyps(4)
                      by fastforce
                    show ?thesis
                    proof (induct "o1 = j")
                      case True
                      then show ?case
                        using r_def
                        by blast
                    next
                      case False
                      then show ?case
                        using j_def o1_def ob_in_set_def ob_def unique_across_sets
                        by blast
                    qed
                  next
                    assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
                    then have o1_class_def: "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1 = containedtype"
                      unfolding imod_contained_class_set_field_def
                      using objects_unique
                      by fastforce
                    have "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] \<exclamdown>classtype"
                    proof
                      assume "\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] \<exclamdown>classtype"
                      then have "\<exclamdown>containedtype \<sqsubseteq>[tmod_contained_class_set_field classtype name containedtype mul] \<exclamdown>classtype"
                        unfolding imod_contained_class_set_field_def class_def
                        by simp
                      then have "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_rel_altdef (tmod_contained_class_set_field classtype name containedtype mul)"
                        using subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_correct
                        by blast
                      then show "False"
                        unfolding subtype_rel_altdef_def
                      proof (elim UnE)
                        assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_tuple ` Type (tmod_contained_class_set_field classtype name containedtype mul)"
                        then have "classtype = containedtype"
                          by (simp add: image_iff subtype_tuple_def)
                        then show ?thesis
                          using classtype_containedtype_neq
                          by blast
                      next
                        assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv nullable nullable ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
                        then show ?thesis
                          unfolding subtype_conv_def
                          by blast
                      next
                        assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper proper ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
                        then show ?thesis
                          unfolding tmod_contained_class_set_field_def
                          by auto
                      next
                        assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_contained_class_set_field classtype name containedtype mul)"
                        then show ?thesis
                          unfolding subtype_conv_def
                          by blast
                      next
                        assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper nullable ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
                        then show ?thesis
                          unfolding subtype_conv_def
                          by blast
                      qed
                    qed
                    then have "r \<notin> Type_Model.fields (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) containedtype"
                      unfolding Type_Model.fields_def
                      using r_def
                      by simp
                    then show ?thesis
                      using o1_class_def rule_object_containment.hyps(3)
                      by simp
                  qed
                qed
              qed
            qed
          qed
          then have "object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob = {((j, classtype, name), ob)} \<or>
            object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob = {}"
            by blast
          then show ?thesis
            using card_empty
            by fastforce
        qed
      qed
    qed
  next
    have containment_relation_def: "\<And>x y. (x, y) \<in> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values) \<Longrightarrow> 
      x \<in> objects \<and> y \<in> sets_to_set (set ` values ` objects)"
    proof-
      fix x y
      assume "(x, y) \<in> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      then show "x \<in> objects \<and> y \<in> sets_to_set (set ` values ` objects)"
      proof (induct)
        case (rule_object_containment o1 o2 r)
        then have r_def: "r = (classtype, name)"
          using cr_def
          by simp
        then have o1_cases: "o1 \<in> objects \<union> sets_to_set (set ` values ` objects)"
          using rule_object_containment.hyps(1)
          unfolding imod_contained_class_set_field_def
          by simp
        then show ?case
        proof (elim UnE)
          assume o1_def: "o1 \<in> objects"
          then have o1_class_def: "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1 = classtype"
            unfolding imod_contained_class_set_field_def
            by simp
          have value_def: "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r) = setof (map obj (values o1))"
            unfolding imod_contained_class_set_field_def
            using o1_def r_def
            by simp
          have set_in_sets: "set (values o1) \<subseteq> sets_to_set (set ` values ` objects)"
          proof
            fix x
            assume "x \<in> set (values o1)"
            then show "x \<in> sets_to_set (set ` values ` objects)"
              using o1_def imageI sets_to_set.rule_member
              by metis
          qed
          have "set (map obj (values o1)) \<subseteq> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          proof
            fix x :: "('b, 'a) ValueDef"
            assume "x \<in> set (map obj (values o1))"
            then have "x \<in> obj ` sets_to_set (set ` values ` objects)"
              using set_in_sets
              by fastforce
            then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
            proof
              fix y
              assume x_def: "x = obj y"
              assume y_def: "y \<in> sets_to_set (set ` values ` objects)"
              then have "obj y \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
              proof (intro ProperClassValue.rule_proper_objects)
                assume "y \<in> sets_to_set (set ` values ` objects)"
                then show "y \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                  unfolding imod_contained_class_set_field_def
                  by simp
              qed
              then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                using x_def
                by blast
            qed
          qed
          then have "set (map obj (values o1)) \<subseteq> AtomValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
            using proper_class_values_are_atom_values
            by blast
          then have "map obj (values o1) = [] \<or> map obj (values o1) \<in> AtomValueList (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
            using list.map_disc_iff list_of_atom_values_in_atom_value_list_alt
            by metis
          then have contained_values_def: "contained_values (FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r)) = map obj (values o1)"
            using value_def atom_value_list_contained_values_setof_identity
            by fastforce
          then have "obj o2 \<in> set (map obj (values o1))"
            using rule_object_containment.hyps(4)
            by fastforce
          then have ob_in_set_def: "o2 \<in> set (values o1)"
            using rule_object_containment.hyps(4)
            by fastforce
          then have "o2 \<in> sets_to_set (set ` values ` objects)"
            using set_in_sets
            by blast
          then show ?thesis
            using o1_def
            by blast
        next
          assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
          then have o1_class_def: "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1 = containedtype"
            unfolding imod_contained_class_set_field_def
            using objects_unique
            by fastforce
          have "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] \<exclamdown>classtype"
          proof
            assume "\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] \<exclamdown>classtype"
            then have "\<exclamdown>containedtype \<sqsubseteq>[tmod_contained_class_set_field classtype name containedtype mul] \<exclamdown>classtype"
              unfolding imod_contained_class_set_field_def class_def
              by simp
            then have "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_rel_altdef (tmod_contained_class_set_field classtype name containedtype mul)"
              using subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_correct
              by blast
            then show "False"
              unfolding subtype_rel_altdef_def
            proof (elim UnE)
              assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_tuple ` Type (tmod_contained_class_set_field classtype name containedtype mul)"
              then have "classtype = containedtype"
                by (simp add: image_iff subtype_tuple_def)
              then show ?thesis
                using classtype_containedtype_neq
                by blast
            next
              assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv nullable nullable ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper proper ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
              then show ?thesis
                unfolding tmod_contained_class_set_field_def
                by auto
            next
              assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_contained_class_set_field classtype name containedtype mul)"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper nullable ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            qed
          qed
          then have "r \<notin> Type_Model.fields (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) containedtype"
            unfolding Type_Model.fields_def
            using r_def
            by simp
          then show ?thesis
            using o1_class_def rule_object_containment.hyps(3)
            by simp
        qed
      qed
    qed
    have "\<And>x. (x, x) \<notin> (object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values))\<^sup>+"
    proof
      fix x
      assume "(x, x) \<in> (object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values))\<^sup>+"
      then show "False"
      proof (cases)
        case base
        then show ?thesis
          using containment_relation_def objects_unique
          by blast
      next
        case (step c)
        then show ?thesis
          using disjoint_iff_not_equal tranclE containment_relation_def objects_unique
          by metis
      qed
    qed
    then show "irrefl ((object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values))\<^sup>+)"
      unfolding irrefl_def
      by simp
  qed
  then show "imod_contained_class_set_field classtype name containedtype mul objects obids values \<Turnstile> p"
    using p_def
    by simp
qed (simp_all add: assms imod_contained_class_set_field_def tmod_contained_class_set_field_def)

lemma imod_contained_class_set_field_combine_correct:
  assumes "instance_model Imod"
  assumes existing_classes: "{classtype, containedtype} \<subseteq> Class (Tm Imod)"
  assumes new_field: "(classtype, name) \<notin> Field (Tm Imod)"
  assumes valid_ns: "\<not>id_in_ns containedtype (Identifier classtype) \<and> \<not>id_in_ns classtype (Identifier containedtype)"
  assumes valid_mul: "multiplicity mul"
  assumes no_inh_classtype: "\<And>x. (x, classtype) \<notin> Inh (Tm Imod)"
  assumes classtype_containedtype_neq: "classtype \<noteq> containedtype"
  assumes no_fields_containedtype: "Type_Model.fields (Tm Imod) containedtype = {}"
  assumes objects_unique: "objects \<inter> sets_to_set (set ` values ` objects) = {}"
  assumes invalid_ids: "\<And>o1 o2. o1 \<in> Object Imod \<Longrightarrow> 
    o2 \<in> sets_to_set (set ` values ` objects) \<Longrightarrow> ObjectId Imod o1 \<noteq> obids o2"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> sets_to_set (set ` values ` objects) \<Longrightarrow> 
    o2 \<in> sets_to_set (set ` values ` objects) \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_sets: "\<And>ob. ob \<in> objects \<Longrightarrow> distinct (values ob)"
  assumes unique_across_sets: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> o2 \<in> objects \<Longrightarrow> o1 \<noteq> o2 \<Longrightarrow> set (values o1) \<inter> set (values o2) = {}"
  assumes valid_sets: "\<And>ob. ob \<in> objects \<Longrightarrow> length (values ob) in mul"
  assumes existing_objects: "(objects \<union> sets_to_set (set ` values ` objects)) \<inter> Object Imod = objects"
  assumes all_objects: "\<And>ob. ob \<in> Object Imod \<Longrightarrow> ObjectClass Imod ob = classtype \<longleftrightarrow> ob \<in> objects"
  assumes classes_valid: "\<And>ob. ob \<in> objects \<Longrightarrow> 
    ObjectClass Imod ob = ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
  assumes ids_valid: "\<And>ob. ob \<in> objects \<Longrightarrow> ObjectId Imod ob = obids ob"
  shows "instance_model (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
proof (intro imod_combine_merge_correct)
  fix ob
  assume ob_in_imod: "ob \<in> Object Imod"
  assume "ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
  then have "ob \<in> objects \<union> sets_to_set (set ` values ` objects)"
    unfolding imod_contained_class_set_field_def
    by simp
  then have ob_in_objects: "ob \<in> objects"
    using existing_objects ob_in_imod
    by blast
  then show "ObjectClass Imod ob = ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
    using classes_valid ob_in_objects
    by simp
next
  fix ob
  assume ob_in_imod: "ob \<in> Object Imod"
  assume "ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
  then have "ob \<in> objects \<union> sets_to_set (set ` values ` objects)"
    unfolding imod_contained_class_set_field_def
    by simp
  then have ob_in_objects: "ob \<in> objects"
    using existing_objects ob_in_imod
    by blast
  then have "ObjectId (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob = obids ob"
    unfolding imod_contained_class_set_field_def
    by simp
  then show "ObjectId Imod ob = ObjectId (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
    using ids_valid ob_in_objects
    by simp
next
  fix o1 o2
  assume "o1 \<in> Object Imod - Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
  then have "o1 \<in> Object Imod - (objects \<union> sets_to_set (set ` values ` objects))"
    unfolding imod_contained_class_set_field_def
    by simp
  then have o1_def: "o1 \<in> Object Imod - objects"
    using existing_objects
    by blast
  assume "o2 \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values) - Object Imod"
  then have "o2 \<in> objects \<union> sets_to_set (set ` values ` objects) - Object Imod"
    unfolding imod_contained_class_set_field_def
    by simp
  then have "o2 \<in> sets_to_set (set ` values ` objects)"
    using existing_objects
    by blast
  then have not_eq: "ObjectId Imod o1 \<noteq> ObjectId (imod_contained_class_set_field classtype name containedtype mul objects obids values) o2"
    unfolding imod_contained_class_set_field_def
    using invalid_ids o1_def
    by simp
  assume "ObjectId Imod o1 = ObjectId (imod_contained_class_set_field classtype name containedtype mul objects obids values) o2"
  then show "o1 = o2"
    using not_eq
    by simp
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    using assms(1) instance_model.validity_type_model_consistent existing_classes new_field valid_ns valid_mul
    by (intro tmod_contained_class_set_field_combine_correct) (simp_all)
  fix ob f
  assume ob_def: "ob \<in> Object Imod"
  then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob = 
    imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
    unfolding imod_combine_def imod_contained_class_set_field_def
    by simp
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob = ObjectClass Imod ob"
    unfolding imod_combine_object_class_def
    using existing_objects classes_valid
    by (simp add: imod_contained_class_set_field_def inf.commute ob_def)
  assume "f \<in> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
    by simp
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))) f)"
  then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>classtype"
    unfolding class_def
    using ob_class_def f_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have ob_class_is_classtype: "\<exclamdown>(ObjectClass Imod ob) = \<exclamdown>classtype"
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    then show ?thesis
      unfolding subtype_tuple_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    then have ob_extends_classtype: "(ObjectClass Imod ob, classtype) \<in> (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
      unfolding subtype_conv_def
      by fastforce
    have "(ObjectClass Imod ob, classtype) \<notin> (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    proof
      assume "(ObjectClass Imod ob, classtype) \<in> (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
      then show "False"
      proof (cases)
        case base
        then show ?thesis
          unfolding tmod_contained_class_set_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      next
        case (step c)
        then show ?thesis
          unfolding tmod_contained_class_set_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      qed
    qed
    then show ?thesis
      using ob_extends_classtype
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>classtype) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then have ob_in_objects: "ob \<in> objects"
    using all_objects ob_def
    by blast
  have "\<exclamdown>classtype \<in> ProperClassType (tmod_contained_class_set_field classtype name containedtype mul)"
    unfolding tmod_contained_class_set_field_def
    by (simp add: ProperClassType.rule_proper_classes)
  then have "\<exclamdown>classtype \<in> Type (tmod_contained_class_set_field classtype name containedtype mul)"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  then show "ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values) \<and>
    \<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob) 
    \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)]
    \<exclamdown>(class (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) f)"
    unfolding imod_contained_class_set_field_def class_def subtype_def
    using ob_in_objects f_def
    by (simp add: subtype_rel.reflexivity)
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    using assms(1) instance_model.validity_type_model_consistent existing_classes new_field valid_ns valid_mul
    by (intro tmod_contained_class_set_field_combine_correct) (simp_all)
  fix ob f
  assume "ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
  then have ob_def: "ob \<in> objects \<union> sets_to_set (set ` values ` objects)"
    unfolding imod_contained_class_set_field_def
    by simp
  then have ob_cases: "ob \<in> Object Imod \<union> sets_to_set (set ` values ` objects)"
    using existing_objects
    by blast
  assume f_def: "f \<in> Field (Tm Imod)"
  assume extend_def: "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))) f)"
  show "ob \<in> Object Imod \<and> \<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) f)"
    using ob_cases
  proof (elim UnE)
    assume ob_in_imod: "ob \<in> Object Imod"
    then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob = 
      imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
      unfolding imod_combine_def imod_contained_class_set_field_def
      by simp
    then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob = ObjectClass Imod ob"
      unfolding imod_combine_object_class_def
      using existing_objects classes_valid
      by (simp add: imod_contained_class_set_field_def inf.commute ob_in_imod)
    have "ObjectClass Imod ob \<in> Class (Tm Imod)"
      by (simp add: assms(1) instance_model.structure_object_class_wellformed ob_in_imod)
    then have "\<exclamdown>(ObjectClass Imod ob) \<in> ProperClassType (Tm Imod)"
      by (simp add: ProperClassType.rule_proper_classes)
    then have object_class_is_type: "\<exclamdown>(ObjectClass Imod ob) \<in> Type (Tm Imod)"
      unfolding Type_def NonContainerType_def ClassType_def
      by blast
    have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>(fst f)"
      using extend_def ob_class_def
      unfolding class_def
      by simp
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
      unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
      by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) \<union> 
      subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union>
      subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union>
      subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) \<union>
      subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
      unfolding subtype_rel_altdef_def
      by simp
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
    proof (elim UnE)
      assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
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
      assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    next
      assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
      then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
        unfolding subtype_conv_def tmod_combine_def tmod_contained_class_set_field_def
        by simp
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    next
      assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    next
      assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    qed
    then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (Imod)] \<exclamdown>(fst f)"
      unfolding subtype_def
      by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
    then show ?thesis
      unfolding class_def
      using ob_in_imod
      by blast
  next
    assume ob_def: "ob \<in> sets_to_set (set ` values ` objects)"
    then have "ob \<notin> Object Imod"
      using existing_objects objects_unique
      by auto
    then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob = containedtype"
      unfolding imod_combine_def imod_contained_class_set_field_def imod_combine_object_class_def
      using ob_def existing_objects
      by auto
    have "containedtype \<in> Class (Tm Imod)"
      using existing_classes
      by blast
    then have "\<exclamdown>containedtype \<in> ProperClassType (Tm Imod)"
      by (simp add: ProperClassType.rule_proper_classes)
    then have object_class_is_type: "\<exclamdown>containedtype \<in> Type (Tm Imod)"
      unfolding Type_def NonContainerType_def ClassType_def
      by blast
    have no_extend_imod: "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst f)"
    proof
      assume "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst f)"
      then have "f \<in> Type_Model.fields (Tm Imod) containedtype"
        unfolding Type_Model.fields_def
        using f_def
        by fastforce
      then show "False"
        by (simp add: no_fields_containedtype)
    qed
    have "\<not>\<exclamdown>containedtype \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)] \<exclamdown>(fst f)"
    proof
      assume "\<exclamdown>containedtype \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)] \<exclamdown>(fst f)"
      then have "(\<exclamdown>containedtype, \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
        unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
        by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
      then show "False"
        unfolding subtype_rel_altdef_def
      proof (elim UnE)
        assume "(\<exclamdown>containedtype, \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
        then have "\<exclamdown>containedtype = \<exclamdown>(fst f)"
          by (simp add: image_iff subtype_tuple_def)
        then have "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst f)"
          using object_class_is_type subtype_def subtype_rel.reflexivity
          by blast
        then show ?thesis
          using no_extend_imod
          by blast
      next
        assume "(\<exclamdown>containedtype, \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
        then show ?thesis
          unfolding subtype_conv_def
          by blast
      next
        assume "(\<exclamdown>containedtype, \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
        then have "(\<exclamdown>containedtype, \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
          unfolding tmod_combine_def tmod_contained_class_set_field_def
          by simp
        then have "(\<exclamdown>containedtype, \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
          unfolding subtype_rel_altdef_def
          by blast
        then have "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst f)"
          by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes)
        then show ?thesis
          using no_extend_imod
          by blast
      next
        assume "(\<exclamdown>containedtype, \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
        then show ?thesis
          unfolding subtype_conv_def
          by blast
      next
        assume "(\<exclamdown>containedtype, \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
        then show ?thesis
          unfolding subtype_conv_def
          by blast
      qed
    qed
    then have "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>(fst f)"
      unfolding imod_contained_class_set_field_def imod_combine_def
      by simp
    then show ?thesis
      using extend_def ob_class_def
      unfolding class_def
      by simp
  qed
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    using assms(1) instance_model.validity_type_model_consistent existing_classes new_field valid_ns valid_mul
    by (intro tmod_contained_class_set_field_combine_correct) (simp_all)
  fix ob f
  assume ob_def: "ob \<in> Object Imod"
  then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob = 
    imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
    unfolding imod_combine_def imod_contained_class_set_field_def
    by simp
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob = ObjectClass Imod ob"
    unfolding imod_combine_object_class_def
    using existing_objects classes_valid
    by (simp add: imod_contained_class_set_field_def inf.commute ob_def)
  then have "ObjectClass Imod ob \<in> Class (Tm Imod)"
    by (simp add: assms(1) instance_model.structure_object_class_wellformed ob_def)
  then have "\<exclamdown>(ObjectClass Imod ob) \<in> ProperClassType (Tm Imod)"
    by (fact ProperClassType.rule_proper_classes)
  then have ob_class_is_type: "\<exclamdown>(ObjectClass Imod ob) \<in> Type (Tm Imod)"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  assume f_def: "f \<in> Field (Tm Imod)"
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))) f)"
  then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>(fst f)"
    unfolding class_def
    using ob_class_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union>
    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
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
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
      unfolding subtype_conv_def tmod_combine_def tmod_contained_class_set_field_def
      by simp
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by simp
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then show "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm (Imod)] \<exclamdown>(class (Tm Imod) f)"
    unfolding subtype_def class_def
    by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
next
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    using assms(1) instance_model.validity_type_model_consistent existing_classes new_field valid_ns valid_mul
    by (intro tmod_contained_class_set_field_combine_correct) (simp_all)
  fix ob f
  assume "ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
  then have ob_def: "ob \<in> objects \<union> sets_to_set (set ` values ` objects)"
    unfolding imod_contained_class_set_field_def
    by simp
  assume "f \<in> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
  then have f_def: "f = (classtype, name)"
    unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
    by simp
  have "\<exclamdown>classtype \<in> ProperClassType (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
    by (simp add: ProperClassType.rule_proper_classes)
  then have "\<exclamdown>classtype \<in> Type (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    unfolding Type_def NonContainerType_def ClassType_def
    by blast
  then have classtype_extend: "\<exclamdown>classtype \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] \<exclamdown>classtype"
    unfolding subtype_def
    by (simp add: subtype_rel.reflexivity)
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))]
    \<exclamdown>(class (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))) f)"
  then have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob)
    \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>classtype"
    unfolding class_def
    using f_def
    by simp
  then have "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob), \<exclamdown>classtype) \<in> 
    subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
  then have object_class_def: "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob) = \<exclamdown>classtype"
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob), \<exclamdown>classtype) \<in> 
      subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    then show ?thesis
      unfolding subtype_tuple_def
      by fastforce
  next
    assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob), \<exclamdown>classtype) \<in> 
      subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob), \<exclamdown>classtype) \<in> 
      subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    then have ob_extends_classtype: "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob, classtype) \<in> 
      (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
      unfolding subtype_conv_def
      by fastforce
    have "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob, classtype) \<notin> 
      (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    proof
      assume "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob, classtype) \<in> 
        (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
      then show "False"
      proof (cases)
        case base
        then show ?thesis
          unfolding tmod_contained_class_set_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      next
        case (step c)
        then show ?thesis
          unfolding tmod_contained_class_set_field_def tmod_combine_def
          using no_inh_classtype
          by simp
      qed
    qed
    then show ?thesis
      using ob_extends_classtype
      by blast
  next
    assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob), \<exclamdown>classtype) \<in> 
      subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob), \<exclamdown>classtype) \<in> 
      subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  show "\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob)
    \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)]
    \<exclamdown>(class (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) f)"
    using ob_def
  proof (elim UnE)
    assume ob_def: "ob \<in> objects"
    then have "\<exclamdown>(ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob) = \<exclamdown>classtype"
      using existing_objects classes_valid
      unfolding imod_contained_class_set_field_def imod_combine_def imod_combine_object_class_def
      by fastforce
    then show ?thesis
      unfolding class_def
      using f_def classtype_extend
      by simp
  next
    assume ob_def: "ob \<in> sets_to_set (set ` values ` objects)"
    then have "ob \<notin> Object Imod"
      using existing_objects objects_unique
      by auto
    then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob = containedtype"
      unfolding imod_combine_def imod_contained_class_set_field_def imod_combine_object_class_def
      using ob_def existing_objects
      by auto
    then show ?thesis
      using classtype_containedtype_neq object_class_def
      by simp
  qed
next
  have "type_model (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    using assms(1) instance_model.validity_type_model_consistent existing_classes new_field valid_ns valid_mul
    by (intro tmod_contained_class_set_field_combine_correct) (simp_all)
  then show "type_model (tmod_combine (Tm Imod) (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)))"
    unfolding imod_contained_class_set_field_def
    by simp
next
  show instance_model_correct: "instance_model (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
  proof (intro imod_contained_class_set_field_correct)
    fix o1 o2
    assume o1_cases: "o1 \<in> objects \<union> sets_to_set (set ` values ` objects)"
    assume o2_cases: "o2 \<in> objects \<union> sets_to_set (set ` values ` objects)"
    assume ids_eq: "obids o1 = obids o2"
    then show "o1 = o2"
      using o1_cases o2_cases
    proof (elim UnE)
      assume o1_def: "o1 \<in> objects"
      then have o1_object: "o1 \<in> Object Imod"
        using existing_objects
        by blast
      have o1_id: "ObjectId Imod o1 = obids o1"
        using o1_def ids_valid
        by simp
      assume o2_def: "o2 \<in> objects"
      then have o2_object: "o2 \<in> Object Imod"
        using existing_objects
        by blast
      have o2_id: "ObjectId Imod o2 = obids o2"
        using o2_def ids_valid
        by simp
      show ?thesis
        using assms(1) instance_model.property_object_id_uniqueness o2_object o1_object o2_id o1_id ids_eq
        by metis
    next
      assume o1_def: "o1 \<in> objects"
      then have o1_object: "o1 \<in> Object Imod"
        using existing_objects
        by blast
      have o1_id: "ObjectId Imod o1 = obids o1"
        using o1_def ids_valid
        by simp
      assume o2_def: "o2 \<in> sets_to_set (set ` values ` objects)"
      then show ?thesis
        using o1_object o1_id ids_eq invalid_ids
        by metis
    next
      assume o2_def: "o2 \<in> objects"
      then have o2_object: "o2 \<in> Object Imod"
        using existing_objects
        by blast
      have o2_id: "ObjectId Imod o2 = obids o2"
        using o2_def ids_valid
        by simp
      assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
      then show ?thesis
        using o2_object o2_id ids_eq invalid_ids
        by metis
    next
      assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
      assume o2_def: "o2 \<in> sets_to_set (set ` values ` objects)"
      show ?thesis
        using o1_def o2_def ids_eq unique_ids
        by blast
    qed
  qed (simp_all add: assms)
  have type_model_correct: "type_model (tmod_contained_class_set_field classtype name containedtype mul)"
    using tmod_contained_class_set_field_correct valid_ns valid_mul
    by metis
  have no_attr_type: "TypeDef.setof \<exclamdown>containedtype \<notin> AttrType (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
  proof
    assume "TypeDef.setof \<exclamdown>containedtype \<in> AttrType (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    then show "False"
      by (cases) (simp_all)
  qed
  have no_attr: "(classtype, name) \<notin> Attr (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
  proof
    have containedtype_def: "Type_Model.type (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (classtype, name) = TypeDef.setof \<exclamdown>containedtype"
      unfolding Type_Model.type_def imod_contained_class_set_field_def tmod_contained_class_set_field_def
      by simp
    assume "(classtype, name) \<in> Attr (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    then show "False"
      unfolding Attr_def
      using containedtype_def no_attr_type
      by simp
  qed
  have rel_def: "Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) = {(classtype, name)}"
  proof
    show "Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) \<subseteq> {(classtype, name)}"
    proof
      fix x
      assume "x \<in> Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
      then show "x \<in> {(classtype, name)}"
        unfolding Rel_def imod_contained_class_set_field_def tmod_contained_class_set_field_def
        by simp
    qed
  next
    show "{(classtype, name)} \<subseteq> Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    proof
      fix x
      assume "x \<in> {(classtype, name)}"
      then have "x = (classtype, name)"
        by simp
      then show "x \<in> Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
        using no_attr
        unfolding Rel_def imod_contained_class_set_field_def tmod_contained_class_set_field_def
        by simp
    qed
  qed
  have cr_def_part: "CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) = {(classtype, name)}"
  proof
    show "CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) \<subseteq> {(classtype, name)}"
    proof
      fix x
      assume "x \<in> CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
      then show "x \<in> {(classtype, name)}"
      proof (induct)
        case (rule_containment_relations r)
        then show ?case
          using rel_def
          unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
          by blast
      qed
    qed
  next
    show "{(classtype, name)} \<subseteq> CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    proof
      fix x
      assume "x \<in> {(classtype, name)}"
      then have x_def: "x = (classtype, name)"
        by simp
      show "x \<in> CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
      proof (rule CR.rule_containment_relations)
        show "x \<in> Rel (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
          using x_def rel_def
          by simp
      next
        show "containment x \<in> Prop (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
          unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
          using x_def
          by simp
      qed
    qed
  qed
  have type_model_valid: "type_model (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
    using assms(1) instance_model.validity_type_model_consistent existing_classes new_field valid_ns valid_mul
    by (intro tmod_contained_class_set_field_combine_correct) (simp_all)
  have structure_fieldsig_wellformed_type: "\<And>f. f \<in> Field (Tm Imod) \<inter> Field (tmod_contained_class_set_field classtype name containedtype mul) \<Longrightarrow> 
    fst (FieldSig (Tm Imod) f) = fst (FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f)"
  proof-
    fix f
    assume f_in_both: "f \<in> Field (Tm Imod) \<inter> Field (tmod_contained_class_set_field classtype name containedtype mul)"
    then have "f \<in> Field (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
      unfolding tmod_combine_def
      by simp
    then have "fst (FieldSig (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) f) \<in> 
      Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
      using type_model_valid type_model.structure_fieldsig_wellformed_type
      by blast
    then have fst_in_type: "fst (tmod_combine_fieldsig (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul) f) \<in> 
      Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
      by (simp add: tmod_combine_def)
    then show "fst (FieldSig (Tm Imod) f) = fst (FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f)"
    proof (induct "fst (FieldSig (Tm Imod) f) = fst (FieldSig (tmod_contained_class_set_field classtype name containedtype mul) f)")
      case True
      then show ?case
        by simp
    next
      case False
      then have "fst (tmod_combine_fieldsig (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul) f) = TypeDef.invalid"
        unfolding tmod_combine_fieldsig_def
        using f_in_both 
        by simp
      then have "fst (tmod_combine_fieldsig (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul) f) \<notin> 
        Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
        by simp
      then show ?case
        using fst_in_type
        by simp
    qed
  qed
  have "CR (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) = 
    CR (Tm Imod) \<union> CR (tmod_contained_class_set_field classtype name containedtype mul)"
    using assms(1) instance_model.validity_type_model_consistent tmod_combine_containment_relation type_model_correct 
    using structure_fieldsig_wellformed_type type_model.structure_fieldsig_wellformed_type type_model.structure_properties_wellfomed
    by blast
  then have "CR (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))) = 
    CR (Tm Imod) \<union> CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    unfolding imod_combine_def imod_contained_class_set_field_def
    by simp
  then have cr_def: "CR (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))) = 
    CR (Tm Imod) \<union> {(classtype, name)}"
    using cr_def_part
    by simp
  have containments_relation_def: "object_containments_relation (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) = 
    object_containments_relation Imod \<union> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
  proof
    show "object_containments_relation (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) \<subseteq> 
      object_containments_relation Imod \<union> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
    proof
      fix x
      assume "x \<in> object_containments_relation (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
      then show "x \<in> object_containments_relation Imod \<union> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      proof (induct x)
        case (Pair a b)
        then show ?case
        proof (induct)
          case (rule_object_containment o1 o2 r)
          then have r_cases: "r \<in> CR (Tm Imod) \<union> {(classtype, name)}"
            using cr_def
            by blast
          have "o1 \<in> Object Imod \<union> objects \<union> sets_to_set (set ` values ` objects)"
            using rule_object_containment.hyps(1)
            unfolding imod_combine_def imod_contained_class_set_field_def
            by simp
          then have "o1 \<in> Object Imod \<union> sets_to_set (set ` values ` objects)"
            using existing_objects
            by blast
          then show ?case
            using r_cases
          proof (elim UnE)
            assume o1_def: "o1 \<in> Object Imod"
            then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
              imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
              unfolding imod_combine_def imod_contained_class_set_field_def
              by simp
            then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = ObjectClass Imod o1"
              unfolding imod_combine_object_class_def
              using existing_objects classes_valid
              by (simp add: imod_contained_class_set_field_def inf.commute o1_def)
            then have "ObjectClass Imod o1 \<in> Class (Tm Imod)"
              by (simp add: assms(1) instance_model.structure_object_class_wellformed o1_def)
            then have "\<exclamdown>(ObjectClass Imod o1) \<in> ProperClassType (Tm Imod)"
              by (fact ProperClassType.rule_proper_classes)
            then have o1_class_is_type: "\<exclamdown>(ObjectClass Imod o1) \<in> Type (Tm Imod)"
              unfolding Type_def NonContainerType_def ClassType_def
              by blast
            assume r_def: "r \<in> CR (Tm Imod)"
            then have r_field: "r \<in> Field (Tm Imod)"
              using containment_relations_are_fields
              by blast
            then have r_not_field: "r \<notin> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
              unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
              using new_field
              by fastforce
            have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1) 
              \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>(fst r)"
              using rule_object_containment.hyps(3)
              unfolding Type_Model.fields_def
              by fastforce
            then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
              using ob_class_def
              unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
              by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
            then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) \<union> 
              subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union>
              subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union>
              subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) \<union>
              subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              unfolding subtype_rel_altdef_def
              by simp
            then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod)"
            proof (elim UnE)
              assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
              then have "ObjectClass Imod o1 = fst r"
                unfolding subtype_tuple_def
                by fastforce
              then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (Tm Imod)"
                unfolding subtype_tuple_def
                using o1_class_is_type
                by simp
              then show ?thesis
                unfolding subtype_rel_altdef_def
                by simp
            next
              assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
                unfolding subtype_conv_def tmod_combine_def tmod_contained_class_set_field_def
                by simp
              then show ?thesis
                unfolding subtype_rel_altdef_def
                by simp
            next
              assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            qed
            then have "\<exclamdown>(ObjectClass Imod o1) \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
              by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes)
            then have r_in_fields: "r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod o1)"
              unfolding Type_Model.fields_def
              using r_field
              by fastforce
            have "FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r) = FieldValue Imod (o1, r)"
              unfolding imod_combine_def imod_combine_field_value_def
              using r_not_field r_field o1_def
              by simp
            then have "obj o2 \<in> set (contained_values (FieldValue Imod (o1, r)))"
              using rule_object_containment.hyps(4)
              by simp
            then show ?thesis
              using o1_def object_containments_relation.rule_object_containment r_def r_in_fields
              by fastforce
          next
            assume o1_def: "o1 \<in> Object Imod"
            then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
              imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
              unfolding imod_combine_def imod_contained_class_set_field_def
              by simp
            then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = ObjectClass Imod o1"
              unfolding imod_combine_object_class_def
              using existing_objects classes_valid
              by (simp add: imod_contained_class_set_field_def inf.commute o1_def)
            assume "r \<in> {(classtype, name)}"
            then have r_def: "r = (classtype, name)"
              by simp
            then have r_cr: "r \<in> CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
              using cr_def_part
              by simp
            have r_field: "r \<in> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
              unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
              by (simp add: r_def)
            have r_not_field: "r \<notin> Field (Tm Imod)"
              using r_def new_field
              by simp
            have "\<exclamdown>classtype \<in> ProperClassType (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
              unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
              by (simp add: ProperClassType.rule_proper_classes)
            then have "\<exclamdown>classtype \<in> Type (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
              unfolding Type_def NonContainerType_def ClassType_def
              by blast
            then have classtype_extend: "\<exclamdown>classtype \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] \<exclamdown>classtype"
              unfolding subtype_def
              by (simp add: subtype_rel.reflexivity)
            have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)
              \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>classtype"
              using rule_object_containment.hyps(3) r_def
              unfolding Type_Model.fields_def
              by blast
            then have "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
              subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
              unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
              by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
            then have object_class_def: "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1) = \<exclamdown>classtype"
              unfolding subtype_rel_altdef_def
            proof (elim UnE)
              assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
              then show ?thesis
                unfolding subtype_tuple_def
                by fastforce
            next
              assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              then have ob_extends_classtype: "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                unfolding subtype_conv_def
                by fastforce
              have "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<notin> 
                (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              proof
                assume "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                  (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                then show "False"
                proof (cases)
                  case base
                  then show ?thesis
                    unfolding tmod_contained_class_set_field_def tmod_combine_def
                    using no_inh_classtype
                    by simp
                next
                  case (step c)
                  then show ?thesis
                    unfolding tmod_contained_class_set_field_def tmod_combine_def
                    using no_inh_classtype
                    by simp
                qed
              qed
              then show ?thesis
                using ob_extends_classtype
                by blast
            next
              assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            qed
            then have o1_class_def: "ObjectClass Imod o1 = classtype"
              by (simp add: ob_class_def)
            then have o1_in_objects: "o1 \<in> objects"
              using all_objects o1_def
              by blast
            then have o1_def: "o1 \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
              unfolding imod_contained_class_set_field_def
              by simp
            then have "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1 = ObjectClass Imod o1"
              unfolding imod_contained_class_set_field_def
              by (simp add: o1_class_def o1_in_objects)
            then have r_in_fields: "r \<in> Type_Model.fields (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) 
              (ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1)"
              unfolding Type_Model.fields_def
              using classtype_extend o1_class_def r_def r_field
              by fastforce
            have "FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r) =
              FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r)"
              unfolding imod_combine_def imod_combine_field_value_def
              using r_not_field r_field o1_def
              by simp
            then have "obj o2 \<in> set (contained_values (FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r)))"
              using rule_object_containment.hyps(4)
              by metis
            then show ?thesis
              using o1_def object_containments_relation.rule_object_containment r_cr r_in_fields
              by fastforce
          next
            assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
            then have "o1 \<notin> Object Imod"
              using existing_objects objects_unique
              by auto
            then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = containedtype"
              unfolding imod_combine_def imod_contained_class_set_field_def imod_combine_object_class_def
              using o1_def existing_objects
              by auto
            assume r_def: "r \<in> CR (Tm Imod)"
            then have r_field: "r \<in> Field (Tm Imod)"
              using containment_relations_are_fields
              by blast
            have "containedtype \<in> Class (Tm Imod)"
              using existing_classes
              by blast
            then have "\<exclamdown>containedtype \<in> ProperClassType (Tm Imod)"
              by (simp add: ProperClassType.rule_proper_classes)
            then have object_class_is_type: "\<exclamdown>containedtype \<in> Type (Tm Imod)"
              unfolding Type_def NonContainerType_def ClassType_def
              by blast
            have no_extend_imod: "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
            proof
              assume "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
              then have "r \<in> Type_Model.fields (Tm Imod) containedtype"
                unfolding Type_Model.fields_def
                using r_field
                by fastforce
              then show "False"
                by (simp add: no_fields_containedtype)
            qed
            have "\<not>\<exclamdown>containedtype \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)] \<exclamdown>(fst r)"
            proof
              assume "\<exclamdown>containedtype \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)] \<exclamdown>(fst r)"
              then have "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
                by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
              then show "False"
                unfolding subtype_rel_altdef_def
              proof (elim UnE)
                assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                then have "\<exclamdown>containedtype = \<exclamdown>(fst r)"
                  by (simp add: image_iff subtype_tuple_def)
                then have "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                  using object_class_is_type subtype_def subtype_rel.reflexivity
                  by blast
                then show ?thesis
                  using no_extend_imod
                  by blast
              next
                assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                then show ?thesis
                  unfolding subtype_conv_def
                  by blast
              next
                assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                then have "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
                  unfolding tmod_combine_def tmod_contained_class_set_field_def
                  by simp
                then have "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod)"
                  unfolding subtype_rel_altdef_def
                  by blast
                then have "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                  by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes)
                then show ?thesis
                  using no_extend_imod
                  by blast
              next
                assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                then show ?thesis
                  unfolding subtype_conv_def
                  by blast
              next
                assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                then show ?thesis
                  unfolding subtype_conv_def
                  by blast
              qed
            qed
            then have "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>(fst r)"
              unfolding imod_contained_class_set_field_def imod_combine_def
              by simp
            then have "r \<notin> Type_Model.fields (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))) containedtype"
              unfolding Type_Model.fields_def
              by fastforce
            then show ?thesis
              using rule_object_containment.hyps(3) ob_class_def
              by simp
          next
            assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
            then have "o1 \<notin> Object Imod"
              using existing_objects objects_unique
              by auto
            then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = containedtype"
              unfolding imod_combine_def imod_contained_class_set_field_def imod_combine_object_class_def
              using o1_def existing_objects
              by auto
            assume "r \<in> {(classtype, name)}"
            then have r_def: "r = (classtype, name)"
              by simp
            then have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)
              \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>classtype"
              using rule_object_containment.hyps(3)
              unfolding Type_Model.fields_def
              by blast
            then have "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
              subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
              unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
              by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
            then have object_class_def: "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1) = \<exclamdown>classtype"
              unfolding subtype_rel_altdef_def
            proof (elim UnE)
              assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
              then show ?thesis
                unfolding subtype_tuple_def
                by fastforce
            next
              assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              then have ob_extends_classtype: "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                unfolding subtype_conv_def
                by fastforce
              have "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<notin> 
                (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              proof
                assume "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                  (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                then show "False"
                proof (cases)
                  case base
                  then show ?thesis
                    unfolding tmod_contained_class_set_field_def tmod_combine_def
                    using no_inh_classtype
                    by simp
                next
                  case (step c)
                  then show ?thesis
                    unfolding tmod_contained_class_set_field_def tmod_combine_def
                    using no_inh_classtype
                    by simp
                qed
              qed
              then show ?thesis
                using ob_extends_classtype
                by blast
            next
              assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            qed
            then show ?thesis
              using ob_class_def classtype_containedtype_neq
              by simp
          qed
        qed
      qed
    qed
  next
    show "object_containments_relation Imod \<union> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values) \<subseteq> 
      object_containments_relation (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    proof
      fix x
      assume "x \<in> object_containments_relation Imod \<union> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      then show "x \<in> object_containments_relation (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
      proof (elim UnE)
        assume "x \<in> object_containments_relation Imod"
        then show "x \<in> object_containments_relation (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
        proof (induct x)
          case (Pair a b)
          then show ?case
          proof (induct)
            case (rule_object_containment o1 o2 r)
            then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
              imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
              unfolding imod_combine_def imod_contained_class_set_field_def
              by simp
            then have o1_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = ObjectClass Imod o1"
              unfolding imod_combine_object_class_def
              using existing_objects classes_valid
              by (simp add: imod_contained_class_set_field_def inf.commute rule_object_containment.hyps(1))
            have r_field: "r \<in> Field (Tm Imod)"
              using rule_object_containment.hyps(2) containment_relations_are_fields
              by blast
            then have r_not_field: "r \<notin> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
              unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
              using new_field
              by fastforce
            have "o1 \<in> Object Imod \<union> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
              using rule_object_containment.hyps(1)
              by blast
            then have o1_def: "o1 \<in> Object (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
              unfolding imod_combine_def
              by simp
            have "r \<in> CR (Tm Imod) \<union> {(classtype, name)}"
              by (simp add: rule_object_containment.hyps(2))
            then have r_def: "r \<in> CR (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)))"
              by (simp add: cr_def)
            have "r \<in> Type_Model.fields (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) (ObjectClass Imod o1)"
              using rule_object_containment.hyps(3) tmod_combine_subtype_subset_tmod1
              unfolding Type_Model.fields_def tmod_combine_def
              by fastforce
            then have "r \<in> Type_Model.fields (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))
              (ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)"
              by (simp add: o1_class_def)
            then have r_in_fields: "r \<in> Type_Model.fields (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)))
              (ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)"
              unfolding imod_combine_def imod_contained_class_set_field_def
              by simp
            have "FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r) = FieldValue Imod (o1, r)"
              unfolding imod_combine_def imod_combine_field_value_def
              using r_not_field r_field rule_object_containment.hyps(1)
              by simp
            then have "obj o2 \<in> set (contained_values (FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r)))"
              using rule_object_containment.hyps(4)
              by simp
            then show ?case
              using o1_def object_containments_relation.rule_object_containment r_def r_in_fields
              by fastforce
          qed
        qed
      next
        assume "x \<in> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
        then show "x \<in> object_containments_relation (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
        proof (induct x)
          case (Pair a b)
          then show ?case
          proof (induct)
            case (rule_object_containment o1 o2 r)
            then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
              imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
              unfolding imod_combine_def imod_contained_class_set_field_def
              by simp
            then have o1_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
              ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
              using objects_unique existing_objects classes_valid rule_object_containment.hyps(1)
              unfolding imod_combine_object_class_def imod_contained_class_set_field_def
              by fastforce
            have r_field: "r \<in> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
              using rule_object_containment.hyps(2) containment_relations_are_fields
              by blast
            then have r_not_field: "r \<notin> Field (Tm Imod)"
              unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
              using new_field
              by fastforce
            have "o1 \<in> Object Imod \<union> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
              using rule_object_containment.hyps(1)
              by blast
            then have o1_def: "o1 \<in> Object (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
              unfolding imod_combine_def
              by simp
            have "r = (classtype, name)"
              using cr_def_part rule_object_containment.hyps(2)
              by simp
            then have "r \<in> CR (Tm Imod) \<union> {(classtype, name)}"
              by simp
            then have r_def: "r \<in> CR (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)))"
              by (simp add: cr_def)
            have "r \<in> Type_Model.fields (tmod_combine (Tm Imod) (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))) 
              (ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1)"
              using rule_object_containment.hyps(3) tmod_combine_subtype_subset_tmod2
              unfolding Type_Model.fields_def tmod_combine_def
              by fastforce
            then have "r \<in> Type_Model.fields (tmod_combine (Tm Imod) (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)))
              (ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)"
              by (simp add: o1_class_def)
            then have r_in_fields: "r \<in> Type_Model.fields (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)))
              (ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)"
              unfolding imod_combine_def
              by simp
            have "FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r) = 
              FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r)"
              unfolding imod_combine_def imod_combine_field_value_def
              using r_not_field r_field rule_object_containment.hyps(1)
              by simp
            then have "obj o2 \<in> set (contained_values (FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r)))"
              using rule_object_containment.hyps(4)
              by simp
            then show ?case
              using o1_def object_containments_relation.rule_object_containment r_def r_in_fields
              by fastforce
          qed
        qed
      qed
    qed
  qed
  have containments_imod_def: "\<And>x y. (x, y) \<in> object_containments_relation Imod \<Longrightarrow> x \<in> Object Imod \<and> y \<in> Object Imod"
  proof-
    fix x y
    assume "(x, y) \<in> object_containments_relation Imod"
    then show "x \<in> Object Imod \<and> y \<in> Object Imod"
    proof (induct)
      case (rule_object_containment o1 o2 r)
      then have "r \<in> Field (Tm Imod)"
        by simp
      then have value_def: "FieldValue Imod (o1, r) \<in> Value Imod"
        by (simp add: assms(1) instance_model.property_field_values_inside_domain rule_object_containment.hyps(1) rule_object_containment.hyps(3))
      then have "set (contained_values (FieldValue Imod (o1, r))) \<subseteq> Value Imod"
        unfolding Value_def
        using container_value_contained_values atom_values_contained_values_singleton
        by fastforce
      then have "obj o2 \<in> Value Imod"
        using value_def rule_object_containment.hyps(4)
        by blast
      then have "obj o2 \<in> ProperClassValue Imod"
        unfolding Value_def AtomValue_def ClassValue_def
        by simp
      then have "o2 \<in> Object Imod"
        using ProperClassValue.cases
        by blast
      then show ?case
        by (simp add: rule_object_containment.hyps(1))
    qed
  qed
  have containments_imod_irrefl: "irrefl ((object_containments_relation Imod)\<^sup>+)"
  proof (induct "\<exists>r. containment r \<in> Prop (Tm Imod)")
    case True
    then show ?case
      using assms(1) instance_model.validity_properties_satisfied property_satisfaction_containment_rev
      by metis
  next
    case False
    have "object_containments_relation Imod = {}"
    proof
      show "object_containments_relation Imod \<subseteq> {}"
      proof
        fix x
        assume "x \<in> object_containments_relation Imod"
        then show "x \<in> {}"
        proof (induct x)
          case (Pair a b)
          then show ?case
          proof (induct)
            case (rule_object_containment o1 o2 r)
            have "\<exists>r. containment r \<in> Prop (Tm Imod)"
              using rule_object_containment.hyps(2)
            proof (induct)
              case (rule_containment_relations r)
              then show ?case
                by blast
            qed
            then show ?case
              using False.hyps
              by simp
          qed
        qed
      qed
    next
      show "{} \<subseteq> object_containments_relation Imod"
        by simp
    qed
    then show ?case
      unfolding irrefl_def
      by simp
  qed
  have containments_block_def: "\<And>x y. (x, y) \<in> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values) \<Longrightarrow> 
      x \<in> objects \<and> y \<in> sets_to_set (set ` values ` objects)"
  proof-
    fix x y
    assume "(x, y) \<in> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
    then show "x \<in> objects \<and> y \<in> sets_to_set (set ` values ` objects)"
    proof (induct)
      case (rule_object_containment o1 o2 r)
      then have r_def: "r = (classtype, name)"
        using cr_def_part
        by simp
      then have o1_cases: "o1 \<in> objects \<union> sets_to_set (set ` values ` objects)"
        using rule_object_containment.hyps(1)
        unfolding imod_contained_class_set_field_def
        by simp
      then show ?case
      proof (elim UnE)
        assume o1_def: "o1 \<in> objects"
        then have o1_class_def: "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1 = classtype"
          unfolding imod_contained_class_set_field_def
          by simp
        have value_def: "FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r) = setof (map obj (values o1))"
          unfolding imod_contained_class_set_field_def
          using o1_def r_def
          by simp
        have set_in_sets: "set (values o1) \<subseteq> sets_to_set (set ` values ` objects)"
        proof
          fix x
          assume "x \<in> set (values o1)"
          then show "x \<in> sets_to_set (set ` values ` objects)"
            using o1_def imageI sets_to_set.rule_member
            by metis
        qed
        have "set (map obj (values o1)) \<subseteq> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
        proof
          fix x :: "('a, 'b) ValueDef"
          assume "x \<in> set (map obj (values o1))"
          then have "x \<in> obj ` sets_to_set (set ` values ` objects)"
            using set_in_sets
            by fastforce
          then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          proof
            fix y
            assume x_def: "x = obj y"
            assume y_def: "y \<in> sets_to_set (set ` values ` objects)"
            then have "obj y \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
            proof (intro ProperClassValue.rule_proper_objects)
              assume "y \<in> sets_to_set (set ` values ` objects)"
              then show "y \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                unfolding imod_contained_class_set_field_def
                by simp
            qed
            then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
              using x_def
              by blast
          qed
        qed
        then have "set (map obj (values o1)) \<subseteq> AtomValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          using proper_class_values_are_atom_values
          by blast
        then have "map obj (values o1) = [] \<or> map obj (values o1) \<in> AtomValueList (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
          using list.map_disc_iff list_of_atom_values_in_atom_value_list_alt
          by metis
        then have contained_values_def: "contained_values (FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r)) = map obj (values o1)"
          using value_def atom_value_list_contained_values_setof_identity
          by fastforce
        then have "obj o2 \<in> set (map obj (values o1))"
          using rule_object_containment.hyps(4)
          by fastforce
        then have ob_in_set_def: "o2 \<in> set (values o1)"
          using rule_object_containment.hyps(4)
          by fastforce
        then have "o2 \<in> sets_to_set (set ` values ` objects)"
          using set_in_sets
          by blast
        then show ?thesis
          using o1_def
          by blast
      next
        assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
        then have o1_class_def: "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1 = containedtype"
          unfolding imod_contained_class_set_field_def
          using objects_unique
          by fastforce
        have "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] \<exclamdown>classtype"
        proof
          assume "\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] \<exclamdown>classtype"
          then have "\<exclamdown>containedtype \<sqsubseteq>[tmod_contained_class_set_field classtype name containedtype mul] \<exclamdown>classtype"
            unfolding imod_contained_class_set_field_def class_def
            by simp
          then have "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_rel_altdef (tmod_contained_class_set_field classtype name containedtype mul)"
            using subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_correct
            by blast
          then show "False"
            unfolding subtype_rel_altdef_def
          proof (elim UnE)
            assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_tuple ` Type (tmod_contained_class_set_field classtype name containedtype mul)"
            then have "classtype = containedtype"
              by (simp add: image_iff subtype_tuple_def)
            then show ?thesis
              using classtype_containedtype_neq
              by blast
          next
            assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv nullable nullable ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
            then show ?thesis
              unfolding subtype_conv_def
              by blast
          next
            assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper proper ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
            then show ?thesis
              unfolding tmod_contained_class_set_field_def
              by auto
          next
            assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_contained_class_set_field classtype name containedtype mul)"
            then show ?thesis
              unfolding subtype_conv_def
              by blast
          next
            assume "(\<exclamdown>containedtype, \<exclamdown>classtype) \<in> subtype_conv proper nullable ` (Inh (tmod_contained_class_set_field classtype name containedtype mul))\<^sup>+"
            then show ?thesis
              unfolding subtype_conv_def
              by blast
          qed
        qed
        then have "r \<notin> Type_Model.fields (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) containedtype"
          unfolding Type_Model.fields_def
          using r_def
          by simp
        then show ?thesis
          using o1_class_def rule_object_containment.hyps(3)
          by simp
      qed
    qed
  qed
  have "imod_contained_class_set_field classtype name containedtype mul objects obids values \<Turnstile> containment (classtype, name)"
    using instance_model_correct instance_model.validity_properties_satisfied
    unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
    by fastforce
  then have containments_block_irrefl: "irrefl ((object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values))\<^sup>+)"
    using instance_model_correct property_satisfaction_containment_rev
    by metis
  have "\<And>x. (x, x) \<notin> (object_containments_relation Imod \<union> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values))\<^sup>+"
  proof
    fix x
    assume "(x, x) \<in> (object_containments_relation Imod \<union> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values))\<^sup>+"
    then show "False"
    proof (cases)
      case base
      then show ?thesis
        using containments_imod_irrefl containments_block_irrefl
        unfolding irrefl_def
        by blast
    next
      case (step c)
      then show ?thesis
      proof (elim UnE)
        assume c_x_def: "(c, x) \<in> object_containments_relation Imod"
        then have c_def: "c \<in> Object Imod"
          using containments_imod_def
          by simp
        have "(x, c) \<in> (object_containments_relation Imod)\<^sup>+"
          using step(1) c_def
        proof (induct)
          case (base y)
          then show ?case
            using containments_block_def existing_objects objects_unique
            by blast
        next
          case (step y z)
          then show ?case
            using containments_imod_def containments_block_def existing_objects objects_unique
            by fastforce
        qed
        then show ?thesis
          using c_x_def containments_imod_irrefl irrefl_def trancl_into_trancl2
          by metis
      next
        assume c_x_def: "(c, x) \<in> object_containments_relation (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
        then have x_def: "x \<in> sets_to_set (set ` values ` objects)"
          using containments_block_def
          by blast
        have c_def: "c \<in> objects"
          using c_x_def containments_block_def
          by simp
        then have c_def: "c \<in> Object Imod"
          using existing_objects
          by blast
        have "(x, c) \<in> (object_containments_relation Imod)\<^sup>+"
          using step(1) c_def
        proof (induct)
          case (base y)
          then show ?case
            using containments_block_def existing_objects objects_unique
            by blast
        next
          case (step y z)
          then show ?case
            using containments_imod_def containments_block_def existing_objects objects_unique
            by fastforce
        qed
        then have "x \<in> Object Imod"
          using containments_imod_def converse_tranclE
          by metis
        then show ?thesis
          using x_def objects_unique existing_objects
          by blast
      qed
    qed
  qed
  then show "irrefl ((object_containments_relation (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)))\<^sup>+)"
    unfolding irrefl_def
    using containments_relation_def
    by simp
  fix ob
  assume "ob \<in> Object Imod \<union> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
  then have "ob \<in> Object Imod \<union> objects \<union> sets_to_set (set ` values ` objects)"
    unfolding imod_contained_class_set_field_def
    by simp
  then have "ob \<in> Object Imod \<union> sets_to_set (set ` values ` objects)"
    using existing_objects
    by blast
  then show "card (object_containments (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob) \<le> 1"
  proof (elim UnE)
    assume ob_def: "ob \<in> Object Imod"
    have "object_containments (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob = object_containments Imod ob"
    proof
      show "object_containments (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob \<subseteq> object_containments Imod ob"
      proof
        fix x
        assume "x \<in> object_containments (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob"
        then show "x \<in> object_containments Imod ob"
        proof (induct x)
          case (Pair a d)
          then show ?case
          proof (induct a)
            case (fields a b c)
            then show ?case
            proof (induct)
              case (rule_object_containment o1 r)
              then have r_cases: "r \<in> CR (Tm Imod) \<union> {(classtype, name)}"
                using cr_def
                by blast
              have "o1 \<in> Object Imod \<union> objects \<union> sets_to_set (set ` values ` objects)"
                using rule_object_containment.hyps(1)
                unfolding imod_combine_def imod_contained_class_set_field_def
                by simp
              then have "o1 \<in> Object Imod \<union> sets_to_set (set ` values ` objects)"
                using existing_objects
                by blast
              then show ?case
                using r_cases
              proof (elim UnE)
                assume o1_def: "o1 \<in> Object Imod"
                then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
                  imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
                  unfolding imod_combine_def imod_contained_class_set_field_def
                  by simp
                then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = ObjectClass Imod o1"
                  unfolding imod_combine_object_class_def
                  using existing_objects classes_valid
                  by (simp add: imod_contained_class_set_field_def inf.commute o1_def)
                then have "ObjectClass Imod o1 \<in> Class (Tm Imod)"
                  by (simp add: assms(1) instance_model.structure_object_class_wellformed o1_def)
                then have "\<exclamdown>(ObjectClass Imod o1) \<in> ProperClassType (Tm Imod)"
                  by (fact ProperClassType.rule_proper_classes)
                then have o1_class_is_type: "\<exclamdown>(ObjectClass Imod o1) \<in> Type (Tm Imod)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by blast
                assume r_def: "r \<in> CR (Tm Imod)"
                then have r_field: "r \<in> Field (Tm Imod)"
                  using containment_relations_are_fields
                  by blast
                then have r_not_field: "r \<notin> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
                  unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
                  using new_field
                  by fastforce
                have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1) 
                  \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>(fst r)"
                  using rule_object_containment.hyps(3)
                  unfolding Type_Model.fields_def
                  by fastforce
                then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  using ob_class_def
                  unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
                  by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
                then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) \<union> 
                  subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union>
                  subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union>
                  subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) \<union>
                  subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  unfolding subtype_rel_altdef_def
                  by simp
                then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod)"
                proof (elim UnE)
                  assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then have "ObjectClass Imod o1 = fst r"
                    unfolding subtype_tuple_def
                    by fastforce
                  then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (Tm Imod)"
                    unfolding subtype_tuple_def
                    using o1_class_is_type
                    by simp
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
                    unfolding subtype_conv_def tmod_combine_def tmod_contained_class_set_field_def
                    by simp
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                qed
                then have "\<exclamdown>(ObjectClass Imod o1) \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                  by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes)
                then have r_in_fields: "r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod o1)"
                  unfolding Type_Model.fields_def
                  using r_field
                  by fastforce
                have "FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r) = FieldValue Imod (o1, r)"
                  unfolding imod_combine_def imod_combine_field_value_def
                  using r_not_field r_field o1_def
                  by simp
                then have "obj ob \<in> set (contained_values (FieldValue Imod (o1, r)))"
                  using rule_object_containment.hyps(4)
                  by simp
                then show ?thesis
                  by (simp add: o1_def object_containments.rule_object_containment r_def r_in_fields)
              next
                assume o1_def: "o1 \<in> Object Imod"
                then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
                  imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
                  unfolding imod_combine_def imod_contained_class_set_field_def
                  by simp
                then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = ObjectClass Imod o1"
                  unfolding imod_combine_object_class_def
                  using existing_objects classes_valid
                  by (simp add: imod_contained_class_set_field_def inf.commute o1_def)
                assume r_def: "r \<in> {(classtype, name)}"
                then have r_def: "r = (classtype, name)"
                  by simp
                have r_field: "r \<in> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
                  unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
                  by (simp add: r_def)
                have r_not_field: "r \<notin> Field (Tm Imod)"
                  using r_def new_field
                  by simp
                have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)
                  \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>classtype"
                  using rule_object_containment.hyps(3) r_def
                  unfolding Type_Model.fields_def
                  by blast
                then have "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                  subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
                  by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
                then have object_class_def: "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1) = \<exclamdown>classtype"
                  unfolding subtype_rel_altdef_def
                proof (elim UnE)
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then show ?thesis
                    unfolding subtype_tuple_def
                    by fastforce
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then have ob_extends_classtype: "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                    (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    unfolding subtype_conv_def
                    by fastforce
                  have "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<notin> 
                    (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  proof
                    assume "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                      (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    then show "False"
                    proof (cases)
                      case base
                      then show ?thesis
                        unfolding tmod_contained_class_set_field_def tmod_combine_def
                        using no_inh_classtype
                        by simp
                    next
                      case (step c)
                      then show ?thesis
                        unfolding tmod_contained_class_set_field_def tmod_combine_def
                        using no_inh_classtype
                        by simp
                    qed
                  qed
                  then show ?thesis
                    using ob_extends_classtype
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                qed
                then have "ObjectClass Imod o1 = classtype"
                  by (simp add: ob_class_def)
                then have o1_def: "o1 \<in> objects"
                  using all_objects o1_def
                  by blast
                then have "o1 \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                  unfolding imod_contained_class_set_field_def
                  by simp
                then have "FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r) = 
                  FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r)"
                  unfolding imod_combine_def imod_combine_field_value_def
                  using r_not_field r_field
                  by simp
                then have value_def: "FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r) = 
                  setof (map obj (values o1))"
                  unfolding imod_contained_class_set_field_def
                  using o1_def r_def
                  by simp
                have set_in_sets: "set (values o1) \<subseteq> sets_to_set (set ` values ` objects)"
                proof
                  fix x
                  assume "x \<in> set (values o1)"
                  then show "x \<in> sets_to_set (set ` values ` objects)"
                    using o1_def imageI sets_to_set.rule_member
                    by metis
                qed
                have "set (map obj (values o1)) \<subseteq> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                proof
                  fix x :: "('a, 'b) ValueDef"
                  assume "x \<in> set (map obj (values o1))"
                  then have "x \<in> obj ` sets_to_set (set ` values ` objects)"
                    using set_in_sets
                    by fastforce
                  then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                  proof
                    fix y
                    assume x_def: "x = obj y"
                    assume y_def: "y \<in> sets_to_set (set ` values ` objects)"
                    then have "obj y \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                    proof (intro ProperClassValue.rule_proper_objects)
                      assume "y \<in> sets_to_set (set ` values ` objects)"
                      then show "y \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                        unfolding imod_contained_class_set_field_def
                        by simp
                    qed
                    then show "x \<in> ProperClassValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                      using x_def
                      by blast
                  qed
                qed
                then have "set (map obj (values o1)) \<subseteq> AtomValue (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                  using proper_class_values_are_atom_values
                  by blast
                then have "map obj (values o1) = [] \<or> map obj (values o1) \<in> AtomValueList (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                  using list.map_disc_iff list_of_atom_values_in_atom_value_list_alt
                  by metis
                then have contained_values_def: "contained_values (FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r)) = map obj (values o1)"
                  using value_def atom_value_list_contained_values_setof_identity
                  by fastforce
                have "obj ob \<notin> set (map obj (values o1))"
                proof
                  have ob_not_in_sets: "ob \<notin> sets_to_set (set ` values ` objects)"
                    using ob_def existing_objects objects_unique
                    by blast
                  assume "obj ob \<in> set (map obj (values o1))"
                  then have "ob \<in> set (values o1)"
                    by fastforce
                  then have "ob \<in> sets_to_set (set ` values ` objects)"
                    using set_in_sets
                    by blast
                  then show "False"
                    using ob_not_in_sets
                    by simp
                qed
                then show ?thesis
                  using contained_values_def rule_object_containment.hyps(4)
                  by metis
              next
                assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
                then have "o1 \<notin> Object Imod"
                  using existing_objects objects_unique
                  by auto
                then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = containedtype"
                  unfolding imod_combine_def imod_contained_class_set_field_def imod_combine_object_class_def
                  using o1_def existing_objects
                  by auto
                assume r_def: "r \<in> CR (Tm Imod)"
                then have r_field: "r \<in> Field (Tm Imod)"
                  using containment_relations_are_fields
                  by blast
                have "containedtype \<in> Class (Tm Imod)"
                  using existing_classes
                  by blast
                then have "\<exclamdown>containedtype \<in> ProperClassType (Tm Imod)"
                  by (simp add: ProperClassType.rule_proper_classes)
                then have object_class_is_type: "\<exclamdown>containedtype \<in> Type (Tm Imod)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by blast
                have no_extend_imod: "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                proof
                  assume "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                  then have "r \<in> Type_Model.fields (Tm Imod) containedtype"
                    unfolding Type_Model.fields_def
                    using r_field
                    by fastforce
                  then show "False"
                    by (simp add: no_fields_containedtype)
                qed
                have "\<not>\<exclamdown>containedtype \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)] \<exclamdown>(fst r)"
                proof
                  assume "\<exclamdown>containedtype \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)] \<exclamdown>(fst r)"
                  then have "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                    unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
                    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
                  then show "False"
                    unfolding subtype_rel_altdef_def
                  proof (elim UnE)
                    assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                    then have "\<exclamdown>containedtype = \<exclamdown>(fst r)"
                      by (simp add: image_iff subtype_tuple_def)
                    then have "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                      using object_class_is_type subtype_def subtype_rel.reflexivity
                      by blast
                    then show ?thesis
                      using no_extend_imod
                      by blast
                  next
                    assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    then have "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
                      unfolding tmod_combine_def tmod_contained_class_set_field_def
                      by simp
                    then have "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod)"
                      unfolding subtype_rel_altdef_def
                      by blast
                    then have "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                      by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes)
                    then show ?thesis
                      using no_extend_imod
                      by blast
                  next
                    assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  qed
                qed
                then have "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>(fst r)"
                  unfolding imod_contained_class_set_field_def imod_combine_def
                  by simp
                then have "r \<notin> Type_Model.fields (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))) containedtype"
                  unfolding Type_Model.fields_def
                  by fastforce
                then show ?thesis
                  using rule_object_containment.hyps(3) ob_class_def
                  by simp
              next
                assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
                then have "o1 \<notin> Object Imod"
                  using existing_objects objects_unique
                  by auto
                then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = containedtype"
                  unfolding imod_combine_def imod_contained_class_set_field_def imod_combine_object_class_def
                  using o1_def existing_objects
                  by auto
                assume "r \<in> {(classtype, name)}"
                then have r_def: "r = (classtype, name)"
                  by simp
                then have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)
                  \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>classtype"
                  using rule_object_containment.hyps(3)
                  unfolding Type_Model.fields_def
                  by blast
                then have "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                  subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
                  by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
                then have object_class_def: "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1) = \<exclamdown>classtype"
                  unfolding subtype_rel_altdef_def
                proof (elim UnE)
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then show ?thesis
                    unfolding subtype_tuple_def
                    by fastforce
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then have ob_extends_classtype: "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                    (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    unfolding subtype_conv_def
                    by fastforce
                  have "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<notin> 
                    (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  proof
                    assume "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                      (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    then show "False"
                    proof (cases)
                      case base
                      then show ?thesis
                        unfolding tmod_contained_class_set_field_def tmod_combine_def
                        using no_inh_classtype
                        by simp
                    next
                      case (step c)
                      then show ?thesis
                        unfolding tmod_contained_class_set_field_def tmod_combine_def
                        using no_inh_classtype
                        by simp
                    qed
                  qed
                  then show ?thesis
                    using ob_extends_classtype
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                qed
                then show ?thesis
                  using ob_class_def classtype_containedtype_neq
                  by simp
              qed
            qed
          qed
        qed
      qed
    next
      show "object_containments Imod ob \<subseteq> object_containments (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob"
      proof
        fix x
        assume "x \<in> object_containments Imod ob"
        then show "x \<in> object_containments (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob"
        proof (induct x)
          case (Pair a d)
          then show ?case
          proof (induct a)
            case (fields a b c)
            then show ?case
            proof (induct)
              case (rule_object_containment o1 r)
              then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
                imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
                unfolding imod_combine_def imod_contained_class_set_field_def
                by simp
              then have o1_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = ObjectClass Imod o1"
                unfolding imod_combine_object_class_def
                using existing_objects classes_valid
                by (simp add: imod_contained_class_set_field_def inf.commute rule_object_containment.hyps(1))
              have r_field: "r \<in> Field (Tm Imod)"
                using rule_object_containment.hyps(2) containment_relations_are_fields
                by blast
              then have r_not_field: "r \<notin> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
                unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
                using new_field
                by fastforce
              have "o1 \<in> Object Imod \<union> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                using rule_object_containment.hyps(1)
                by blast
              then have o1_def: "o1 \<in> Object (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
                unfolding imod_combine_def
                by simp
              have "r \<in> CR (Tm Imod) \<union> {(classtype, name)}"
                by (simp add: rule_object_containment.hyps(2))
              then have r_def: "r \<in> CR (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)))"
                by (simp add: cr_def)
              have "r \<in> Type_Model.fields (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) (ObjectClass Imod o1)"
                using rule_object_containment.hyps(3) tmod_combine_subtype_subset_tmod1
                unfolding Type_Model.fields_def tmod_combine_def
                by fastforce
              then have "r \<in> Type_Model.fields (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))
                (ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)"
                by (simp add: o1_class_def)
              then have r_in_fields: "r \<in> Type_Model.fields (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)))
                (ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)"
                unfolding imod_combine_def imod_contained_class_set_field_def
                by simp
              have "FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r) = FieldValue Imod (o1, r)"
                unfolding imod_combine_def imod_combine_field_value_def
                using r_not_field r_field rule_object_containment.hyps(1)
                by simp
              then have "obj ob \<in> set (contained_values (FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r)))"
                using rule_object_containment.hyps(4)
                by simp
              then show ?case
                by (simp add: o1_def object_containments.rule_object_containment r_def r_in_fields)
            qed
          qed
        qed
      qed
    qed
    then show ?thesis
    proof (induct "\<exists>r. containment r \<in> Prop (Tm Imod)")
      case True
      then show ?case
        using ob_def assms(1) instance_model.validity_properties_satisfied property_satisfaction_containment_rev
        by metis
    next
      case False
      have "object_containments Imod ob = {}"
      proof
        show "object_containments Imod ob \<subseteq> {}"
        proof
          fix x
          assume "x \<in> object_containments Imod ob"
          then show "x \<in> {}"
          proof (induct x)
            case (Pair a d)
            then show ?case
            proof (induct a)
              case (fields a b c)
              then show ?case
              proof (induct)
                case (rule_object_containment o1 r)
                have "\<exists>r. containment r \<in> Prop (Tm Imod)"
                  using rule_object_containment.hyps(2)
                proof (induct)
                  case (rule_containment_relations r)
                  then show ?case
                    by blast
                qed
                then show ?case
                  using False.hyps
                  by simp
              qed
            qed
          qed
        qed
      next
        show "{} \<subseteq> object_containments Imod ob"
          by simp
      qed
      then show ?case
        using False.prems card_empty
        by simp
    qed
  next
    assume ob_def: "ob \<in> sets_to_set (set ` values ` objects)"
    then have ob_altdef: "ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
      unfolding imod_contained_class_set_field_def
      by simp
    have containments_eq: "object_containments (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob = 
      object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
    proof
      show "object_containments (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob \<subseteq> 
        object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
      proof
        fix x
        assume "x \<in> object_containments (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob"
        then show "x \<in> object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
        proof (induct x)
          case (Pair a d)
          then show ?case
          proof (induct a)
            case (fields a b c)
            then show ?case
            proof (induct)
              case (rule_object_containment o1 r)
              then have r_cases: "r \<in> CR (Tm Imod) \<union> {(classtype, name)}"
                using cr_def
                by blast
              have "o1 \<in> Object Imod \<union> objects \<union> sets_to_set (set ` values ` objects)"
                using rule_object_containment.hyps(1)
                unfolding imod_combine_def imod_contained_class_set_field_def
                by simp
              then have "o1 \<in> Object Imod \<union> sets_to_set (set ` values ` objects)"
                using existing_objects
                by blast
              then show ?case
                using r_cases
              proof (elim UnE)
                assume o1_def: "o1 \<in> Object Imod"
                then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
                  imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
                  unfolding imod_combine_def imod_contained_class_set_field_def
                  by simp
                then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = ObjectClass Imod o1"
                  unfolding imod_combine_object_class_def
                  using existing_objects classes_valid
                  by (simp add: imod_contained_class_set_field_def inf.commute o1_def)
                then have "ObjectClass Imod o1 \<in> Class (Tm Imod)"
                  by (simp add: assms(1) instance_model.structure_object_class_wellformed o1_def)
                then have "\<exclamdown>(ObjectClass Imod o1) \<in> ProperClassType (Tm Imod)"
                  by (fact ProperClassType.rule_proper_classes)
                then have o1_class_is_type: "\<exclamdown>(ObjectClass Imod o1) \<in> Type (Tm Imod)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by blast
                assume r_def: "r \<in> CR (Tm Imod)"
                then have r_field: "r \<in> Field (Tm Imod)"
                  using containment_relations_are_fields
                  by blast
                then have r_not_field: "r \<notin> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
                  unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
                  using new_field
                  by fastforce
                have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1) 
                  \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>(fst r)"
                  using rule_object_containment.hyps(3)
                  unfolding Type_Model.fields_def
                  by fastforce
                then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  using ob_class_def
                  unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
                  by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
                then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) \<union> 
                  subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union>
                  subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+ \<union>
                  subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)) \<union>
                  subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  unfolding subtype_rel_altdef_def
                  by simp
                then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod)"
                proof (elim UnE)
                  assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then have "ObjectClass Imod o1 = fst r"
                    unfolding subtype_tuple_def
                    by fastforce
                  then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (Tm Imod)"
                    unfolding subtype_tuple_def
                    using o1_class_is_type
                    by simp
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then have "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
                    unfolding subtype_conv_def tmod_combine_def tmod_contained_class_set_field_def
                    by simp
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                qed
                then have "\<exclamdown>(ObjectClass Imod o1) \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                  by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes)
                then have r_in_fields: "r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod o1)"
                  unfolding Type_Model.fields_def
                  using r_field
                  by fastforce
                have "FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r) = FieldValue Imod (o1, r)"
                  unfolding imod_combine_def imod_combine_field_value_def
                  using r_not_field r_field o1_def
                  by simp
                then have value_def: "obj ob \<in> set (contained_values (FieldValue Imod (o1, r)))"
                  using rule_object_containment.hyps(4)
                  by simp
                have "FieldValue Imod (o1, r) \<in> Value Imod"
                  by (simp add: assms(1) instance_model.property_field_values_inside_domain o1_def r_field r_in_fields)
                then have "set (contained_values (FieldValue Imod (o1, r))) \<subseteq> Value Imod"
                  unfolding Value_def
                  using container_value_contained_values atom_values_contained_values_singleton
                  by fastforce
                then have "obj ob \<in> Value Imod"
                  using value_def
                  by blast
                then have "obj ob \<in> ProperClassValue Imod"
                  unfolding Value_def AtomValue_def ClassValue_def
                  by simp
                then have "ob \<in> Object Imod"
                  using ProperClassValue.cases
                  by blast
                then show ?thesis
                  using ob_def existing_objects objects_unique
                  by blast
              next
                assume o1_def: "o1 \<in> Object Imod"
                then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
                  imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
                  unfolding imod_combine_def imod_contained_class_set_field_def
                  by simp
                then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = ObjectClass Imod o1"
                  unfolding imod_combine_object_class_def
                  using existing_objects classes_valid
                  by (simp add: imod_contained_class_set_field_def inf.commute o1_def)
                assume "r \<in> {(classtype, name)}"
                then have r_def: "r = (classtype, name)"
                  by simp
                then have r_cr: "r \<in> CR (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
                  using cr_def_part
                  by simp
                have r_field: "r \<in> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
                  unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
                  by (simp add: r_def)
                have r_not_field: "r \<notin> Field (Tm Imod)"
                  using r_def new_field
                  by simp
                have "\<exclamdown>classtype \<in> ProperClassType (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
                  unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
                  by (simp add: ProperClassType.rule_proper_classes)
                then have "\<exclamdown>classtype \<in> Type (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by blast
                then have classtype_extend: "\<exclamdown>classtype \<sqsubseteq>[Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)] \<exclamdown>classtype"
                  unfolding subtype_def
                  by (simp add: subtype_rel.reflexivity)
                have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)
                  \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>classtype"
                  using rule_object_containment.hyps(3) r_def
                  unfolding Type_Model.fields_def
                  by blast
                then have "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                  subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
                  by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
                then have object_class_def: "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1) = \<exclamdown>classtype"
                  unfolding subtype_rel_altdef_def
                proof (elim UnE)
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then show ?thesis
                    unfolding subtype_tuple_def
                    by fastforce
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then have ob_extends_classtype: "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                    (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    unfolding subtype_conv_def
                    by fastforce
                  have "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<notin> 
                    (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  proof
                    assume "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                      (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    then show "False"
                    proof (cases)
                      case base
                      then show ?thesis
                        unfolding tmod_contained_class_set_field_def tmod_combine_def
                        using no_inh_classtype
                        by simp
                    next
                      case (step c)
                      then show ?thesis
                        unfolding tmod_contained_class_set_field_def tmod_combine_def
                        using no_inh_classtype
                        by simp
                    qed
                  qed
                  then show ?thesis
                    using ob_extends_classtype
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                qed
                then have o1_class_def: "ObjectClass Imod o1 = classtype"
                  by (simp add: ob_class_def)
                then have o1_in_objects: "o1 \<in> objects"
                  using all_objects o1_def
                  by blast
                then have o1_def: "o1 \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                  unfolding imod_contained_class_set_field_def
                  by simp
                then have "ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1 = ObjectClass Imod o1"
                  unfolding imod_contained_class_set_field_def
                  by (simp add: o1_class_def o1_in_objects)
                then have r_in_fields: "r \<in> Type_Model.fields (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)) 
                  (ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1)"
                  unfolding Type_Model.fields_def
                  using classtype_extend o1_class_def r_def r_field
                  by fastforce
                have "FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r) =
                  FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r)"
                  unfolding imod_combine_def imod_combine_field_value_def
                  using r_not_field r_field o1_def
                  by simp
                then have "obj ob \<in> set (contained_values (FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r)))"
                  using rule_object_containment.hyps(4)
                  by metis
                then show ?thesis
                  by (simp add: o1_def object_containments.rule_object_containment r_cr r_in_fields)
              next
                assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
                then have "o1 \<notin> Object Imod"
                  using existing_objects objects_unique
                  by auto
                then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = containedtype"
                  unfolding imod_combine_def imod_contained_class_set_field_def imod_combine_object_class_def
                  using o1_def existing_objects
                  by auto
                assume r_def: "r \<in> CR (Tm Imod)"
                then have r_field: "r \<in> Field (Tm Imod)"
                  using containment_relations_are_fields
                  by blast
                have "containedtype \<in> Class (Tm Imod)"
                  using existing_classes
                  by blast
                then have "\<exclamdown>containedtype \<in> ProperClassType (Tm Imod)"
                  by (simp add: ProperClassType.rule_proper_classes)
                then have object_class_is_type: "\<exclamdown>containedtype \<in> Type (Tm Imod)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by blast
                have no_extend_imod: "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                proof
                  assume "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                  then have "r \<in> Type_Model.fields (Tm Imod) containedtype"
                    unfolding Type_Model.fields_def
                    using r_field
                    by fastforce
                  then show "False"
                    by (simp add: no_fields_containedtype)
                qed
                have "\<not>\<exclamdown>containedtype \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)] \<exclamdown>(fst r)"
                proof
                  assume "\<exclamdown>containedtype \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)] \<exclamdown>(fst r)"
                  then have "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                    unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
                    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
                  then show "False"
                    unfolding subtype_rel_altdef_def
                  proof (elim UnE)
                    assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                    then have "\<exclamdown>containedtype = \<exclamdown>(fst r)"
                      by (simp add: image_iff subtype_tuple_def)
                    then have "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                      using object_class_is_type subtype_def subtype_rel.reflexivity
                      by blast
                    then show ?thesis
                      using no_extend_imod
                      by blast
                  next
                    assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    then have "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
                      unfolding tmod_combine_def tmod_contained_class_set_field_def
                      by simp
                    then have "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod)"
                      unfolding subtype_rel_altdef_def
                      by blast
                    then have "\<exclamdown>containedtype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst r)"
                      by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes)
                    then show ?thesis
                      using no_extend_imod
                      by blast
                  next
                    assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>containedtype, \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  qed
                qed
                then have "\<not>\<exclamdown>containedtype \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>(fst r)"
                  unfolding imod_contained_class_set_field_def imod_combine_def
                  by simp
                then have "r \<notin> Type_Model.fields (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))) containedtype"
                  unfolding Type_Model.fields_def
                  by fastforce
                then show ?thesis
                  using rule_object_containment.hyps(3) ob_class_def
                  by simp
              next
                assume o1_def: "o1 \<in> sets_to_set (set ` values ` objects)"
                then have "o1 \<notin> Object Imod"
                  using existing_objects objects_unique
                  by auto
                then have ob_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = containedtype"
                  unfolding imod_combine_def imod_contained_class_set_field_def imod_combine_object_class_def
                  using o1_def existing_objects
                  by auto
                assume "r \<in> {(classtype, name)}"
                then have r_def: "r = (classtype, name)"
                  by simp
                then have "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)
                  \<sqsubseteq>[Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))] \<exclamdown>classtype"
                  using rule_object_containment.hyps(3)
                  unfolding Type_Model.fields_def
                  by blast
                then have "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                  subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  unfolding subtype_def imod_contained_class_set_field_def imod_combine_def
                  by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_valid)
                then have object_class_def: "\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1) = \<exclamdown>classtype"
                  unfolding subtype_rel_altdef_def
                proof (elim UnE)
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then show ?thesis
                    unfolding subtype_tuple_def
                    by fastforce
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then have ob_extends_classtype: "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                    (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    unfolding subtype_conv_def
                    by fastforce
                  have "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<notin> 
                    (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  proof
                    assume "(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1, classtype) \<in> 
                      (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                    then show "False"
                    proof (cases)
                      case base
                      then show ?thesis
                        unfolding tmod_contained_class_set_field_def tmod_combine_def
                        using no_inh_classtype
                        by simp
                    next
                      case (step c)
                      then show ?thesis
                        unfolding tmod_contained_class_set_field_def tmod_combine_def
                        using no_inh_classtype
                        by simp
                    qed
                  qed
                  then show ?thesis
                    using ob_extends_classtype
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul))"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1), \<exclamdown>classtype) \<in> 
                    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_contained_class_set_field classtype name containedtype mul)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                qed
                then show ?thesis
                  using ob_class_def classtype_containedtype_neq
                  by simp
              qed
            qed
          qed
        qed
      qed
    next
      show "object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob \<subseteq> 
        object_containments (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob"
      proof
        fix x
        assume "x \<in> object_containments (imod_contained_class_set_field classtype name containedtype mul objects obids values) ob"
        then show "x \<in> object_containments (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) ob"
        proof (induct x)
          case (Pair a d)
          then show ?case
          proof (induct a)
            case (fields a b c)
            then show ?case
            proof (induct)
              case (rule_object_containment o1 r)
              then have "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
                imod_combine_object_class Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
                unfolding imod_combine_def imod_contained_class_set_field_def
                by simp
              then have o1_class_def: "ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1 = 
                ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1"
                using objects_unique existing_objects classes_valid rule_object_containment.hyps(1)
                unfolding imod_combine_object_class_def imod_contained_class_set_field_def
                by fastforce
              have r_field: "r \<in> Field (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
                using rule_object_containment.hyps(2) containment_relations_are_fields
                by blast
              then have r_not_field: "r \<notin> Field (Tm Imod)"
                unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
                using new_field
                by fastforce
              have "o1 \<in> Object Imod \<union> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
                using rule_object_containment.hyps(1)
                by blast
              then have o1_def: "o1 \<in> Object (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
                unfolding imod_combine_def
                by simp
              have "r = (classtype, name)"
                using cr_def_part rule_object_containment.hyps(2)
                by simp
              then have "r \<in> CR (Tm Imod) \<union> {(classtype, name)}"
                by simp
              then have r_def: "r \<in> CR (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)))"
                by (simp add: cr_def)
              have "r \<in> Type_Model.fields (tmod_combine (Tm Imod) (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values))) 
                (ObjectClass (imod_contained_class_set_field classtype name containedtype mul objects obids values) o1)"
                using rule_object_containment.hyps(3) tmod_combine_subtype_subset_tmod2
                unfolding Type_Model.fields_def tmod_combine_def
                by fastforce
              then have "r \<in> Type_Model.fields (tmod_combine (Tm Imod) (Tm (imod_contained_class_set_field classtype name containedtype mul objects obids values)))
                (ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)"
                by (simp add: o1_class_def)
              then have r_in_fields: "r \<in> Type_Model.fields (Tm (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)))
                (ObjectClass (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) o1)"
                unfolding imod_combine_def
                by simp
              have "FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r) = 
                FieldValue (imod_contained_class_set_field classtype name containedtype mul objects obids values) (o1, r)"
                unfolding imod_combine_def imod_combine_field_value_def
                using r_not_field r_field rule_object_containment.hyps(1)
                by simp
              then have "obj ob \<in> set (contained_values (FieldValue (imod_combine Imod (imod_contained_class_set_field classtype name containedtype mul objects obids values)) (o1, r)))"
                using rule_object_containment.hyps(4)
                by simp
              then show ?case
                by (simp add: o1_def object_containments.rule_object_containment r_def r_in_fields)
            qed
          qed
        qed
      qed
    qed
    have "imod_contained_class_set_field classtype name containedtype mul objects obids values \<Turnstile> containment (classtype, name)"
      using instance_model_correct instance_model.validity_properties_satisfied
      unfolding imod_contained_class_set_field_def tmod_contained_class_set_field_def
      by fastforce
    then show ?thesis
      using property_satisfaction_containment_rev ob_altdef containments_eq
      by metis
  qed
qed (simp_all add: assms imod_contained_class_set_field_def tmod_contained_class_set_field_def)



section "Encoding of a class-typed field as edge type in GROOVE"

inductive_set values_to_pairs :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> ('a \<times> 'a) set"
  for A :: "'a set" and f :: "'a \<Rightarrow> 'a list"
  where
    rule_member: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> set (f x) \<Longrightarrow> (x, y) \<in> values_to_pairs A f"

lemma values_to_pairs_prod: "(x, y) \<in> values_to_pairs A f \<Longrightarrow> x \<in> A \<and> y \<in> set (f x)"
  using values_to_pairs.cases
  by metis

lemma values_to_pairs_fst: "x \<in> values_to_pairs A f \<Longrightarrow> fst x \<in> A"
  using prod.collapse values_to_pairs.cases
  by metis

lemma values_to_pairs_snd: "x \<in> values_to_pairs A f \<Longrightarrow> snd x \<in> sets_to_set (set ` f ` A)"
proof-
  fix x
  assume "x \<in> values_to_pairs A f"
  then show "snd x \<in> sets_to_set (set ` f ` A)"
  proof (induct x)
    case (Pair a b)
    then show ?case
    proof (induct)
      case (rule_member x y)
      then show ?case
        using sets_to_set.simps
        by fastforce
    qed
  qed
qed

lemma values_to_pairs_select: "x \<in> A \<Longrightarrow> snd ` {z \<in> values_to_pairs A f. fst z = x} = set (f x)"
proof
  show "snd ` {z \<in> values_to_pairs A f. fst z = x} \<subseteq> set (f x)"
  proof
    fix y
    assume "y \<in> snd ` {z \<in> values_to_pairs A f. fst z = x}"
    then show "y \<in> set (f x)"
    proof (elim imageE)
      fix z
      assume z_def: "z \<in> {z \<in> values_to_pairs A f. fst z = x}"
      assume y_def: "y = snd z"
      show "y \<in> set (f x)"
        using z_def
      proof
        assume z_def: "z \<in> values_to_pairs A f \<and> fst z = x"
        then have snd_z_def: "fst z = x"
          by simp
        have "z \<in> values_to_pairs A f"
          using z_def
          by simp
        then show "y \<in> set (f x)"
          using y_def snd_z_def
        proof (induct z)
          case (Pair a b)
          then show ?case
          proof (induct)
            case (rule_member a b)
            then show ?case
              by simp
          qed
        qed
      qed
    qed
  qed
next
  assume x_in_A: "x \<in> A"
  show "set (f x) \<subseteq> snd ` {z \<in> values_to_pairs A f. fst z = x}"
  proof
    fix y
    assume "y \<in> set (f x)"
    then show "y \<in> snd ` {z \<in> values_to_pairs A f. fst z = x}"
      using x_in_A
      by (simp add: image_iff values_to_pairs.simps)
  qed
qed

definition ig_contained_class_set_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> multiplicity \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 'o list) \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values = \<lparr>
    TG = tg_contained_class_set_field_as_edge_type classtype name containedtype mul,
    Id = obids ` objects \<union> obids ` sets_to_set (set ` values ` objects),
    N = typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects),
    E = (\<lambda>x. (typed (type (id_to_list classtype)) (fst x), (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype)), typed (type (id_to_list containedtype)) (snd x))) ` values_to_pairs objects values,
    ident = (\<lambda>x. if x \<in> obids ` objects then typed (type (id_to_list classtype)) (THE y. obids y = x) else 
      if x \<in> obids ` sets_to_set (set ` values ` objects) then typed (type (id_to_list containedtype)) (THE y. obids y = x) else undefined)
  \<rparr>"

lemma ig_contained_class_set_field_as_edge_type_correct:
  assumes valid_mul: "multiplicity mul"
  assumes classtype_containedtype_neq: "classtype \<noteq> containedtype"
  assumes objects_unique: "objects \<inter> sets_to_set (set ` values ` objects) = {}"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<union> sets_to_set (set ` values ` objects) \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_sets: "\<And>ob. ob \<in> objects \<Longrightarrow> distinct (values ob)"
  assumes unique_across_sets: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> o2 \<in> objects \<Longrightarrow> o1 \<noteq> o2 \<Longrightarrow> set (values o1) \<inter> set (values o2) = {}"
  assumes valid_sets: "\<And>ob. ob \<in> objects \<Longrightarrow> length (values ob) in mul"
  shows "instance_graph (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
proof (intro instance_graph.intro)
  fix n
  assume "n \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have "n \<in> typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  then have type_and_node_def: "type\<^sub>n n \<in> NT (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) \<and> n \<in> Node"
  proof (elim UnE)
    assume "n \<in> typed (type (id_to_list classtype)) ` objects"
    then show "type\<^sub>n n \<in> NT (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) \<and> n \<in> Node"
    proof (intro conjI)
      assume "n \<in> typed (type (id_to_list classtype)) ` objects"
      then show "type\<^sub>n n \<in> NT (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)"
        unfolding tg_contained_class_set_field_as_edge_type_def
        by fastforce
    next
      assume "n \<in> typed (type (id_to_list classtype)) ` objects"
      then show "n \<in> Node"
        unfolding Node_def
        using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
        by fastforce
    qed
  next
    assume "n \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    then show "type\<^sub>n n \<in> NT (tg_contained_class_set_field_as_edge_type classtype name containedtype mul) \<and> n \<in> Node"
    proof (intro conjI)
      assume "n \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
      then show "type\<^sub>n n \<in> NT (tg_contained_class_set_field_as_edge_type classtype name containedtype mul)"
        unfolding tg_contained_class_set_field_as_edge_type_def
        by fastforce
    next
      assume "n \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
      then show "n \<in> Node"
        unfolding Node_def
        using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
        by fastforce
    qed
  qed
  then show "type\<^sub>n n \<in> NT (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  show "n \<in> Node"
    by (simp add: type_and_node_def)
next
  fix s l t
  assume "(s, l, t) \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have edge_def: "(s, l, t) \<in> (\<lambda>x. (typed (type (id_to_list classtype)) (fst x), 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype)), 
    typed (type (id_to_list containedtype)) (snd x))) ` values_to_pairs objects values"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  show "s \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> 
    l \<in> ET (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)) \<and> 
    t \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  proof (intro conjI)
    have "s \<in> typed (type (id_to_list classtype)) ` fst ` values_to_pairs objects values"
      using edge_def
      by blast
    then have "s \<in> typed (type (id_to_list classtype)) ` objects"
      using values_to_pairs_fst
      by blast
    then show "s \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
      unfolding ig_contained_class_set_field_as_edge_type_def
      using edge_def
      by simp
  next
    have "l = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype))"
      using edge_def
      by blast
    then show "l \<in> ET (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
      unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
      by simp
  next
    have "t \<in> typed (type (id_to_list containedtype)) ` snd ` values_to_pairs objects values"
      using edge_def
      by blast
    then have "t \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
      using values_to_pairs_snd
      by blast
    then show "t \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
      unfolding ig_contained_class_set_field_as_edge_type_def
      using edge_def
      by simp
  qed
next
  fix i
  assume "i \<in> Id (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have i_in_id: "i \<in> obids ` objects \<union> obids ` sets_to_set (set ` values ` objects)"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  then show "ident (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) i \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> 
    type\<^sub>n (ident (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) i) \<in> Lab\<^sub>t"
  proof (elim UnE)
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
            using Un_iff unique_ids x_is_object
            by metis
        next
          fix y
          assume "obids y = obids x"
          then show "y \<in> objects"
            using Un_iff unique_ids x_is_object
            by metis
        qed
        then show "(THE y. obids y = i) \<in> objects"
          by (simp add: i_def)
      qed
      then have "typed (type (id_to_list classtype)) (THE y. obids y = i) \<in> typed (type (id_to_list classtype)) ` objects"
        by simp
      then show "ident (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) i \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
        unfolding ig_contained_class_set_field_as_edge_type_def
        using i_in_id
        by simp
    next
      have "type\<^sub>n (typed (type (id_to_list classtype)) (THE y. obids y = i)) \<in> Lab\<^sub>t"
        by (simp add: Lab\<^sub>t.rule_type_labels)
      then show "type\<^sub>n (ident (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) i) \<in> Lab\<^sub>t"
        unfolding ig_contained_class_set_field_as_edge_type_def
        using i_in_id
        by simp
    qed
  next
    assume i_in_id: "i \<in> obids ` sets_to_set (set ` values ` objects)"
    then show ?thesis
    proof (intro conjI)
      assume "i \<in> obids ` sets_to_set (set ` values ` objects)"
      then have "(THE y. obids y = i) \<in> sets_to_set (set ` values ` objects)"
      proof
        fix x
        assume i_def: "i = obids x"
        assume x_is_object: "x \<in> sets_to_set (set ` values ` objects)"
        have "(THE y. obids y = obids x) \<in> sets_to_set (set ` values ` objects)"
        proof (rule the1I2)
          show "\<exists>!y. obids y = obids x"
            using Un_iff unique_ids x_is_object
            by metis
        next
          fix y
          assume "obids y = obids x"
          then show "y \<in> sets_to_set (set ` values ` objects)"
            using Un_iff unique_ids x_is_object
            by metis
        qed
        then show "(THE y. obids y = i) \<in> sets_to_set (set ` values ` objects)"
          by (simp add: i_def)
      qed
      then have "typed (type (id_to_list containedtype)) (THE y. obids y = i) \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
        by simp
      then show "ident (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) i \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
        unfolding ig_contained_class_set_field_as_edge_type_def
        using i_in_id objects_unique unique_ids
        by auto
    next
      have "type\<^sub>n (typed (type (id_to_list classtype)) (THE y. obids y = i)) \<in> Lab\<^sub>t \<and> type\<^sub>n (typed (type (id_to_list containedtype)) (THE y. obids y = i)) \<in> Lab\<^sub>t"
        by (simp add: Lab\<^sub>t.rule_type_labels)
      then show "type\<^sub>n (ident (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) i) \<in> Lab\<^sub>t"
        unfolding ig_contained_class_set_field_as_edge_type_def
        using i_in_id
        by simp
    qed
  qed
next
  show "type_graph (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
    unfolding ig_contained_class_set_field_as_edge_type_def
    using tg_contained_class_set_field_as_edge_type_correct valid_mul
    by simp
next
  fix e
  assume "e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) (fst x), 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype)), 
    typed (type (id_to_list containedtype)) (snd x))) ` values_to_pairs objects values"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  have type_n_def: "type\<^sub>n (src e) = type (id_to_list classtype)"
    using e_def
    by fastforce
  have type_e_def: "src (type\<^sub>e e) = type (id_to_list classtype)"
    using e_def
    by fastforce
  have "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> {(type (id_to_list classtype), type (id_to_list classtype)), (type (id_to_list containedtype), type (id_to_list containedtype))}"
    using type_n_def type_e_def
    by blast
  then show "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by simp
next
  fix e
  assume "e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) (fst x), 
    (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype)), 
    typed (type (id_to_list containedtype)) (snd x))) ` values_to_pairs objects values"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  have type_n_def: "type\<^sub>n (tgt e) = type (id_to_list containedtype)"
    using e_def
    by fastforce
  have type_e_def: "tgt (type\<^sub>e e) = type (id_to_list containedtype)"
    using e_def
    by fastforce
  have "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> {(type (id_to_list classtype), type (id_to_list classtype)), (type (id_to_list containedtype), type (id_to_list containedtype))}"
    using type_n_def type_e_def
    by blast
  then show "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by simp
next
  have type_neq: "type (id_to_list classtype) \<noteq> type (id_to_list containedtype)"
    using classtype_containedtype_neq LabDef.inject(1) id_to_list_inverse
    by metis
  fix et n
  assume "et \<in> ET (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype))"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by simp
  then have src_et_def: "src et = type (id_to_list classtype)"
    by simp
  have mult_et_def: "m_out (mult (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)) et) = mul"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by (simp add: et_def)
  assume "n \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have n_def: "n \<in> typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> inh (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
  then have "(type\<^sub>n n, src et) \<in> {(type (id_to_list classtype), type (id_to_list classtype)), (type (id_to_list containedtype), type (id_to_list containedtype))}"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by simp
  then have type_n_def: "type\<^sub>n n = type (id_to_list classtype)"
    using src_et_def
    by fastforce
  then have n_def: "n \<in> typed (type (id_to_list classtype)) ` objects"
    using n_def type_neq
    by fastforce
  then have edges_def: "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). src e = n \<and> type\<^sub>e e = et} = 
    (\<lambda>x. (typed (type (id_to_list classtype)) (nodeId n), (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype)), typed (type (id_to_list containedtype)) x)) ` set (values (nodeId n))"
  proof (elim imageE)
    fix x
    assume x_def: "x \<in> objects"
    assume n_def: "n = typed (LabDef.type (id_to_list classtype)) x"
    then have nodeId_n: "nodeId n = x"
      by simp
    show ?thesis
    proof
      show "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). src e = n \<and> type\<^sub>e e = et}
        \<subseteq> (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) (nodeId n), 
          (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
          typed (LabDef.type (id_to_list containedtype)) x)) ` set (values (nodeId n))"
      proof
        fix y
        assume "y \<in> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). src e = n \<and> type\<^sub>e e = et}"
        then show "y \<in> (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) (nodeId n), 
          (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
          typed (LabDef.type (id_to_list containedtype)) x)) ` set (values (nodeId n))"
        proof
          assume "y \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> src y = n \<and> type\<^sub>e y = et"
          then have "y \<in> (\<lambda>z. (typed (LabDef.type (id_to_list classtype)) (fst z), 
            (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
            typed (LabDef.type (id_to_list containedtype)) (snd z))) ` {z \<in> values_to_pairs objects values. fst z = x}"
            unfolding ig_contained_class_set_field_as_edge_type_def
            using n_def
            by fastforce
          then have "y \<in> (\<lambda>z. (typed (LabDef.type (id_to_list classtype)) x, 
            (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
            typed (LabDef.type (id_to_list containedtype)) z)) ` snd ` {z \<in> values_to_pairs objects values. fst z = x}"
            by fastforce
          then have "y \<in> (\<lambda>z. (typed (LabDef.type (id_to_list classtype)) x, 
            (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
            typed (LabDef.type (id_to_list containedtype)) z)) ` set (values x)"
            by (simp add: values_to_pairs_select x_def)
          then show "y \<in> (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) (nodeId n), 
            (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
            typed (LabDef.type (id_to_list containedtype)) x)) ` set (values (nodeId n))"
            by (simp add: nodeId_n)
        qed
      qed
    next
      show "(\<lambda>x. (typed (LabDef.type (id_to_list classtype)) (nodeId n), 
        (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
        typed (LabDef.type (id_to_list containedtype)) x)) ` set (values (nodeId n))
        \<subseteq> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). src e = n \<and> type\<^sub>e e = et}"
      proof
        fix y
        assume "y \<in> (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) (nodeId n), 
          (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
          typed (LabDef.type (id_to_list containedtype)) x)) ` set (values (nodeId n))"
        then show "y \<in> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). src e = n \<and> type\<^sub>e e = et}"
        proof (elim imageE)
          fix z
          assume "y = (typed (LabDef.type (id_to_list classtype)) (nodeId n), 
            (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
            typed (LabDef.type (id_to_list containedtype)) z)"
          then have y_def: "y = (typed (LabDef.type (id_to_list classtype)) x, 
            (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
            typed (LabDef.type (id_to_list containedtype)) z)"
            using nodeId_n
            by blast
          assume "z \<in> set (values (nodeId n))"
          then have "z \<in> set (values x)"
            by (simp add: nodeId_n)
          then have z_def: "z \<in> snd ` {z \<in> values_to_pairs objects values. fst z = x}"
            by (simp add: values_to_pairs_select x_def)
          show ?thesis
          proof
            show "y \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> src y = n \<and> type\<^sub>e y = et"
            proof (intro conjI)
              have "y \<in> (\<lambda>z. (typed (LabDef.type (id_to_list classtype)) (fst z), 
                (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
                typed (LabDef.type (id_to_list containedtype)) (snd z))) ` {z \<in> values_to_pairs objects values. fst z = x}"
                using y_def z_def
                by blast
              then show "y \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
                unfolding ig_contained_class_set_field_as_edge_type_def
                by auto
            next
              show "src y = n"
                using y_def n_def
                by simp
            next
              show "type\<^sub>e y = et"
                using y_def et_def
                by simp
            qed
          qed
        qed
      qed
    qed
  qed
  have "length (values (nodeId n)) in mul"
    using n_def valid_sets
    by fastforce
  then have card_values_def: "card (set (values (nodeId n))) in mul"
    using unique_sets n_def distinct_card
    by fastforce
  have "inj_on (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) (nodeId n), 
    (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
    typed (LabDef.type (id_to_list containedtype)) x)) (set (values (nodeId n)))"
    unfolding inj_on_def
    by blast
  then have "card ((\<lambda>x. (typed (LabDef.type (id_to_list classtype)) (nodeId n), 
    (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
    typed (LabDef.type (id_to_list containedtype)) x)) ` set (values (nodeId n))) in mul"
    using card_image card_values_def
    by fastforce
  then show "card {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). src e = n \<and> type\<^sub>e e = et} in 
    m_out (mult (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)) et)"
    using edges_def mult_et_def
    by simp
next
  have type_neq: "type (id_to_list classtype) \<noteq> type (id_to_list containedtype)"
    using classtype_containedtype_neq LabDef.inject(1) id_to_list_inverse
    by metis
  fix et n
  assume "et \<in> ET (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype))"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by simp
  then have tgt_et_def: "tgt et = type (id_to_list containedtype)"
    by simp
  have mult_et_def: "m_in (mult (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)) et) = \<^bold>0..\<^bold>1"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by (simp add: et_def)
  assume "n \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have n_def: "n \<in> typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, tgt et) \<in> inh (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
  then have "(type\<^sub>n n, tgt et) \<in> {(type (id_to_list classtype), type (id_to_list classtype)), (type (id_to_list containedtype), type (id_to_list containedtype))}"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by simp
  then have type_n_def: "type\<^sub>n n = type (id_to_list containedtype)"
    using tgt_et_def
    by fastforce
  then have n_def: "n \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    using n_def type_neq
    by fastforce
  then have "card {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} \<le> 1"
  proof (elim imageE)
    fix x
    assume n_def: "n = typed (LabDef.type (id_to_list containedtype)) x"
    assume x_def: "x \<in> sets_to_set (set ` values ` objects)"
    then show ?thesis
      using n_def
    proof (induct)
      case (rule_member y z)
      then show ?case
      proof (elim imageE)
        fix i j
        assume n_def: "n = typed (LabDef.type (id_to_list containedtype)) z"
        assume j_def: "j \<in> objects"
        assume i_def: "i = values j"
        assume "y = set i"
        then have y_def: "y = set (values j)"
          by (simp add: i_def)
        assume "z \<in> y"
        then have z_def: "z \<in> set (values j)"
          by (simp add: y_def)
        have "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} \<subseteq> 
          {(typed (LabDef.type (id_to_list classtype)) j, 
          (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
          typed (LabDef.type (id_to_list containedtype)) z)}"
        proof
          fix k
          assume "k \<in> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et}"
          then show "k \<in> {(typed (LabDef.type (id_to_list classtype)) j, 
            (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
            typed (LabDef.type (id_to_list containedtype)) z)}"
          proof
            assume "k \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> tgt k = n \<and> type\<^sub>e k = et"
            then have "k = (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) (fst x), 
              (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
              typed (LabDef.type (id_to_list containedtype)) (snd x))) (j, z)"
              unfolding ig_contained_class_set_field_as_edge_type_def
              using unique_across_sets j_def z_def n_def values_to_pairs_prod
              by fastforce
            then have "k = (typed (LabDef.type (id_to_list classtype)) j, 
              (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
              typed (LabDef.type (id_to_list containedtype)) z)"
              by simp
            then show "k \<in> {(typed (LabDef.type (id_to_list classtype)) j, 
              (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
              typed (LabDef.type (id_to_list containedtype)) z)}"
              by blast
          qed
        qed
        then have "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} = {} \<or>
          {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} =
          {(typed (LabDef.type (id_to_list classtype)) j, 
          (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
          typed (LabDef.type (id_to_list containedtype)) z)}"
          by blast
        then show ?thesis
        proof (elim disjE)
          assume "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} = {}"
          then have "card {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} = 0"
            using card_empty
            by metis
          then show ?thesis
            by simp
        next
          assume "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} =
            {(typed (LabDef.type (id_to_list classtype)) j, 
            (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
            typed (LabDef.type (id_to_list containedtype)) z)}"
          then show ?thesis
            by simp
        qed
      qed
    qed
  qed
  then show "card {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} in 
    m_in (mult (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)) et)"
    using mult_et_def
    unfolding within_multiplicity_def
    by simp
next
  have type_neq: "type (id_to_list classtype) \<noteq> type (id_to_list containedtype)"
    using classtype_containedtype_neq LabDef.inject(1) id_to_list_inverse
    by metis
  fix n
  assume "n \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have n_def: "n \<in> typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  then show "card {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
    type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} \<le> 1"
  proof (elim UnE)
    assume n_def: "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
    then show ?thesis
    proof
      fix x
      assume n_def: "n = typed (LabDef.type (id_to_list classtype)) x"
      assume x_def: "x \<in> objects"
      have "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
        type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} = {}"
      proof
        show "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
          type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} \<subseteq> {}"
        proof
          fix y
          assume "y \<in> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
            type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))}"
          then show "y \<in> {}"
          proof
            assume "y \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> tgt y = n \<and> 
              type\<^sub>e y \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
            then show "y \<in> {}"
              unfolding ig_contained_class_set_field_as_edge_type_def
              using n_def type_neq
              by fastforce
          qed
        qed
      next
        show "{} \<subseteq> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
          type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))}"
          by simp
      qed
      then have "card {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
        type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} = 0"
        using card_empty
        by metis
      then show ?thesis
        by simp
    qed
  next
    assume n_def: "n \<in> typed (LabDef.type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    then show ?thesis
    proof (elim imageE)
      fix x
      assume n_def: "n = typed (LabDef.type (id_to_list containedtype)) x"
      assume x_def: "x \<in> sets_to_set (set ` values ` objects)"
      then show ?thesis
        using n_def
      proof (induct)
        case (rule_member y z)
        then show ?case
        proof (elim imageE)
          fix i j
          assume n_def: "n = typed (LabDef.type (id_to_list containedtype)) z"
          assume j_def: "j \<in> objects"
          assume i_def: "i = values j"
          assume "y = set i"
          then have y_def: "y = set (values j)"
            by (simp add: i_def)
          assume "z \<in> y"
          then have z_def: "z \<in> set (values j)"
            by (simp add: y_def)
          have "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
              type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} \<subseteq> 
            {(typed (LabDef.type (id_to_list classtype)) j, 
            (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
            typed (LabDef.type (id_to_list containedtype)) z)}"
          proof
            fix k
            assume "k \<in> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
              type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))}"
            then show "k \<in> {(typed (LabDef.type (id_to_list classtype)) j, 
              (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
              typed (LabDef.type (id_to_list containedtype)) z)}"
            proof
              assume "k \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> tgt k = n \<and> 
                type\<^sub>e k \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
              then have "k = (\<lambda>x. (typed (LabDef.type (id_to_list classtype)) (fst x), 
                (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
                typed (LabDef.type (id_to_list containedtype)) (snd x))) (j, z)"
                unfolding ig_contained_class_set_field_as_edge_type_def
                using unique_across_sets j_def z_def n_def values_to_pairs_prod
                by fastforce
              then have "k = (typed (LabDef.type (id_to_list classtype)) j, 
                (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
                typed (LabDef.type (id_to_list containedtype)) z)"
                by simp
              then show "k \<in> {(typed (LabDef.type (id_to_list classtype)) j, 
                (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
                typed (LabDef.type (id_to_list containedtype)) z)}"
                by blast
            qed
          qed
          then have "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
              type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} = {} \<or>
            {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
              type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} =
            {(typed (LabDef.type (id_to_list classtype)) j, 
            (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
            typed (LabDef.type (id_to_list containedtype)) z)}"
            by blast
          then show ?thesis
          proof (elim disjE)
            assume "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
              type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} = {}"
            then have "card {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
              type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} = 0"
              using card_empty
              by metis
            then show ?thesis
              by simp
          next
            assume "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
              type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} =
              {(typed (LabDef.type (id_to_list classtype)) j, 
              (LabDef.type (id_to_list classtype), LabDef.edge [name], LabDef.type (id_to_list containedtype)), 
              typed (LabDef.type (id_to_list containedtype)) z)}"
            then show ?thesis
              by simp
          qed
        qed
      qed
    qed
  qed
next
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)) p"
  proof (intro validity_containmentI)
    fix e
    assume "e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
    then have edge_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) (fst x), 
      (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype)), 
      typed (type (id_to_list containedtype)) (snd x))) ` values_to_pairs objects values"
      unfolding ig_contained_class_set_field_as_edge_type_def
      by simp
    show "src e \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> 
      tgt e \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
    proof (intro conjI)
      have "src e \<in> typed (type (id_to_list classtype)) ` fst ` values_to_pairs objects values"
        using edge_def
        by force
      then have "src e \<in> typed (type (id_to_list classtype)) ` objects"
        using values_to_pairs_fst
        by blast
      then show "src e \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
        unfolding ig_contained_class_set_field_as_edge_type_def
        using edge_def
        by simp
    next
      have "tgt e \<in> typed (type (id_to_list containedtype)) ` snd ` values_to_pairs objects values"
        using edge_def
        by force
      then have "tgt e \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
        using values_to_pairs_snd
        by blast
      then show "tgt e \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
        unfolding ig_contained_class_set_field_as_edge_type_def
        using edge_def
        by simp
    qed
  next
    have type_neq: "type (id_to_list classtype) \<noteq> type (id_to_list containedtype)"
      using classtype_containedtype_neq LabDef.inject(1) id_to_list_inverse
      by metis
    then have nodes_neq: "typed (type (id_to_list classtype)) ` objects \<inter> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects) = {}"
      by blast
    have containments_rel_def: "\<And>s t. (s, t) \<in> edge_to_tuple ` {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
      type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} \<Longrightarrow>
      s \<in> typed (type (id_to_list classtype)) ` objects \<and> t \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    proof (elim imageE)
      fix s t e
      assume e_def: "e \<in> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
        type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))}"
      assume s_t_def: "(s, t) = edge_to_tuple e"
      show "s \<in> typed (LabDef.type (id_to_list classtype)) ` objects \<and> t \<in> typed (LabDef.type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
        using e_def
      proof
        assume "e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> 
          type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
        then have edge_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) (fst x), 
          (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype)), 
          typed (type (id_to_list containedtype)) (snd x))) ` values_to_pairs objects values"
          unfolding ig_contained_class_set_field_as_edge_type_def
          by simp
        have "src e \<in> typed (type (id_to_list classtype)) ` fst ` values_to_pairs objects values"
          using edge_def
          by force
        then have "src e \<in> typed (type (id_to_list classtype)) ` objects"
          using values_to_pairs_fst
          by blast
        then have s_def: "s \<in> typed (type (id_to_list classtype)) ` objects"
          using s_t_def
          unfolding edge_to_tuple_def
          by blast
        have "tgt e \<in> typed (type (id_to_list containedtype)) ` snd ` values_to_pairs objects values"
          using edge_def
          by force
        then have tgt_e_def: "tgt e \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
          using values_to_pairs_snd
          by blast
        then have t_def: "t \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
          using s_t_def
          unfolding edge_to_tuple_def
          by blast
        show "s \<in> typed (LabDef.type (id_to_list classtype)) ` objects \<and> t \<in> typed (LabDef.type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
          using s_def t_def
          by blast
      qed
    qed
    have "\<And>x. (x, x) \<notin> (edge_to_tuple ` {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
      type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))})\<^sup>+"
    proof
      fix x
      assume "(x, x) \<in> (edge_to_tuple ` {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
        type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))})\<^sup>+"
      then show "False"
      proof (cases)
        case base
        then show ?thesis
          using containments_rel_def nodes_neq
          by blast
      next
        case (step c)
        have c_def: "c \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
          using step(1)
        proof (induct)
          case (base y)
          then show ?case
            using containments_rel_def
            by blast
        next
          case (step y z)
          then show ?case
            using containments_rel_def
            by blast
        qed
        have "c \<in> typed (type (id_to_list classtype)) ` objects"
          using step(2) containments_rel_def
          by blast
        then show ?thesis
          using c_def nodes_neq
          by blast
      qed
    qed
    then show "irrefl ((edge_to_tuple ` {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
      type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))})\<^sup>+)"
      unfolding irrefl_def
      by blast
  qed
qed (simp_all add: assms ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def)

lemma ig_contained_class_set_field_as_edge_type_combine_correct:
  assumes "instance_graph IG"
  assumes existing_node_types: "{type (id_to_list classtype), type (id_to_list containedtype)} \<subseteq> NT (TG IG)"
  assumes new_edge_type: "\<And>s l t. (type (id_to_list classtype), s) \<in> inh (TG IG) \<Longrightarrow> l = LabDef.edge [name] \<Longrightarrow> (s, l, t) \<notin> ET (TG IG)"
  assumes no_inh_classtype: "\<And>x. (x, type (id_to_list classtype)) \<in> inh (TG IG) \<Longrightarrow> x = type (id_to_list classtype)"
  assumes valid_mul: "multiplicity mul"
  assumes classtype_containedtype_neq: "classtype \<noteq> containedtype"
  assumes no_src_edges_containedtype: "\<And>s l t. (type (id_to_list containedtype), s) \<in> inh (TG IG) \<Longrightarrow> (s, l, t) \<notin> ET (TG IG)"
  assumes no_tgt_edges_containedtype: "\<And>s l t. (type (id_to_list containedtype), t) \<in> inh (TG IG) \<Longrightarrow> (s, l, t) \<notin> ET (TG IG)"
  assumes objects_unique: "objects \<inter> sets_to_set (set ` values ` objects) = {}"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<union> sets_to_set (set ` values ` objects) \<Longrightarrow> obids o1 = obids o2 \<Longrightarrow> o1 = o2"
  assumes unique_sets: "\<And>ob. ob \<in> objects \<Longrightarrow> distinct (values ob)"
  assumes unique_across_sets: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> o2 \<in> objects \<Longrightarrow> o1 \<noteq> o2 \<Longrightarrow> set (values o1) \<inter> set (values o2) = {}"
  assumes valid_sets: "\<And>ob. ob \<in> objects \<Longrightarrow> length (values ob) in mul"
  assumes existing_objects: "(typed (type (id_to_list classtype)) ` objects \<union> 
    typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)) \<inter> N IG = 
    typed (type (id_to_list classtype)) ` objects"
  assumes all_objects: "\<And>n. n \<in> N IG \<Longrightarrow> type\<^sub>n n = type (id_to_list classtype) \<Longrightarrow> 
    n \<in> typed (type (id_to_list classtype)) ` objects"
  assumes valid_ids: "\<And>i. i \<in> obids ` objects \<union> obids ` sets_to_set (set ` values ` objects) \<Longrightarrow> 
    ident IG i = ident (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) i"
  assumes existing_ids: "(obids ` objects \<union> obids ` sets_to_set (set ` values ` objects)) \<inter> Id IG = obids ` objects"
  shows "instance_graph (ig_combine IG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
proof (intro ig_combine_merge_correct)
  show "instance_graph (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
    by (intro ig_contained_class_set_field_as_edge_type_correct) (simp_all add: assms)
next
  have "type_graph (tg_combine (TG IG) (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))"
    using existing_node_types 
  proof (intro tg_contained_class_set_field_as_edge_type_combine_correct)
    fix s l t
    assume "(s, LabDef.type (id_to_list classtype)) \<in> inh (TG IG) \<or> (LabDef.type (id_to_list classtype), s) \<in> inh (TG IG)"
    then have s_def: "(LabDef.type (id_to_list classtype), s) \<in> inh (TG IG)"
      using no_inh_classtype
      by blast
    assume "l = LabDef.edge [name]"
    then show "(s, l, t) \<notin> ET (TG IG)"
      by (simp add: new_edge_type s_def)
  qed (simp_all add: assms(1) instance_graph.validity_type_graph new_edge_type valid_mul)
  then show "type_graph (tg_combine (TG IG) (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)))"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
next
  show "ET (TG IG) \<inter> ET (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)) = {}"
    using existing_node_types
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by (simp add: assms(1) instance_graph.validity_type_graph new_edge_type type_graph.validity_inh_node)
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have "n \<in> N IG \<union> typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  then have n_def: "n \<in> N IG \<union> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    using existing_objects
    by blast
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG))\<^sup>+"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    using Un_absorb2 existing_node_types assms(1) insert_subset instance_graph.validity_type_graph sup.orderI sup_bot.right_neutral type_graph.select_convs(3) type_graph.validity_inh_node
    by metis
  then have extend_def: "(type\<^sub>n n, src et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  show "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG) et)"
    using n_def
  proof (elim UnE)
    assume "n \<in> N IG"
    then show ?thesis
      using et_def extend_def assms(1) instance_graph.validity_outgoing_mult
      by blast
  next
    assume "n \<in> typed (LabDef.type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    then have "(LabDef.type (id_to_list containedtype), src et) \<in> inh (TG IG)"
      using extend_def
      by fastforce
    then have "et \<notin> ET (TG IG)"
      using no_src_edges_containedtype fst_conv prod_cases3 src_def
      by metis
    then show ?thesis
      using et_def
      by simp
  qed 
next
  have instance_graph_valid: "instance_graph (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
    by (intro ig_contained_class_set_field_as_edge_type_correct) (simp_all add: assms)
  have type_neq: "type (id_to_list classtype) \<noteq> type (id_to_list containedtype)"
    using classtype_containedtype_neq LabDef.inject(1) id_to_list_inverse
    by metis
  fix et n
  assume et_in_ig: "et \<in> ET (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype))"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by simp
  assume "n \<in> N IG \<union> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have n_def: "n \<in> N IG \<union> typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG))\<^sup>+"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
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
  then have edge_extend_def: "(type\<^sub>n n, type (id_to_list classtype)) \<in> inh (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by simp
  have "n \<in> N IG \<union> typed (type (id_to_list classtype)) ` objects"
    using n_def type_n_def type_neq
    by fastforce
  then have "n \<in> typed (type (id_to_list classtype)) ` objects"
    using all_objects existing_objects type_n_def
    by blast
  then have "n \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  then show "card {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). src e = n \<and> type\<^sub>e e = et} in 
    m_out (mult (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)) et)"
    using edge_extend_def et_def et_in_ig instance_graph_valid instance_graph.validity_outgoing_mult
    by fastforce
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have "n \<in> N IG \<union> typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  then have n_def: "n \<in> N IG \<union> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    using existing_objects
    by blast
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG))\<^sup>+"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    using Un_absorb2 existing_node_types assms(1) insert_subset instance_graph.validity_type_graph sup.orderI sup_bot.right_neutral type_graph.select_convs(3) type_graph.validity_inh_node
    by metis
  then have extend_def: "(type\<^sub>n n, tgt et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG) et)"
    using n_def
  proof (elim UnE)
    assume "n \<in> N IG"
    then show ?thesis
      using et_def extend_def assms(1) instance_graph.validity_ingoing_mult
      by blast
  next
    assume "n \<in> typed (LabDef.type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    then have "(LabDef.type (id_to_list containedtype), tgt et) \<in> inh (TG IG)"
      using extend_def
      by fastforce
    then have "et \<notin> ET (TG IG)"
      using no_tgt_edges_containedtype snd_conv prod_cases3 tgt_def
      by metis
    then show ?thesis
      using et_def
      by simp
  qed
next
  have instance_graph_valid: "instance_graph (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
    by (intro ig_contained_class_set_field_as_edge_type_correct) (simp_all add: assms)
  have type_neq: "type (id_to_list classtype) \<noteq> type (id_to_list containedtype)"
    using classtype_containedtype_neq LabDef.inject(1) id_to_list_inverse
    by metis
  fix et n
  assume et_in_ig: "et \<in> ET (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
  then have et_def: "et = (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype))"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    by simp
  assume "n \<in> N IG \<union> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have n_def: "n \<in> N IG \<union> typed (type (id_to_list classtype)) ` objects \<union> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)))\<^sup>+"
  then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (tg_contained_class_set_field_as_edge_type classtype name containedtype mul))\<^sup>+"
    unfolding ig_contained_class_set_field_as_edge_type_def
    by simp
  then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG))\<^sup>+"
    unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
    using Un_absorb2 existing_node_types assms(1) insert_subset instance_graph.validity_type_graph sup.orderI sup_bot.right_neutral type_graph.select_convs(3) type_graph.validity_inh_node
    by metis
  then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG)"
    by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
  then have extend_def: "(type\<^sub>n n, type (id_to_list containedtype)) \<in> inh (TG IG)"
    using et_def
    by simp
  show "card {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} in 
    m_in (mult (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)) et)"
    using n_def
  proof (elim UnE)
    assume n_def: "n \<in> N IG"
    have "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} = {}"
    proof
      show "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} \<subseteq> {}"
      proof
        fix x
        assume "x \<in> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et}"
        then show "x \<in> {}"
        proof
          assume assump: "x \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> tgt x = n \<and> type\<^sub>e x = et"
          then have "tgt x \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
            using instance_graph.structure_edges_wellformed_alt instance_graph_valid
            by blast
          then have "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
            unfolding ig_contained_class_set_field_as_edge_type_def
            using existing_objects n_def assump
            by auto
          then have type_n_def: "type\<^sub>n n = LabDef.type (id_to_list classtype)"
            by fastforce
          have "type\<^sub>n (tgt x) = LabDef.type (id_to_list containedtype)"
            using assump
            unfolding ig_contained_class_set_field_as_edge_type_def
            by fastforce
          then show "x \<in> {}"
            using assump type_n_def type_neq
            by simp
        qed
      qed
    next
      show "{} \<subseteq> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et}"
        by simp
    qed
    then have "card {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} = 0"
      using card_empty
      by metis
    then show ?thesis
      unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def within_multiplicity_def
      using et_def
      by simp
  next
    assume n_def: "n \<in> typed (LabDef.type (id_to_list classtype)) ` objects"
    then have type_n_def: "type\<^sub>n n = LabDef.type (id_to_list classtype)"
      by fastforce
    have "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} = {}"
    proof
      show "{e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} \<subseteq> {}"
      proof
        fix x
        assume "x \<in> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et}"
        then show "x \<in> {}"
        proof
          assume assump: "x \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> tgt x = n \<and> type\<^sub>e x = et"
          then have "type\<^sub>n (tgt x) = LabDef.type (id_to_list containedtype)"
            unfolding ig_contained_class_set_field_as_edge_type_def
            by fastforce
          then show "x \<in> {}"
            using assump type_n_def type_neq
            by simp
        qed
      qed
    next
      show "{} \<subseteq> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et}"
        by simp
    qed
    then have "card {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> type\<^sub>e e = et} = 0"
      using card_empty
      by metis
    then show ?thesis
      unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def within_multiplicity_def
      using et_def
      by simp
  next
    assume n_def: "n \<in> typed (LabDef.type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
    then have n_in_ig: "n \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
      unfolding ig_contained_class_set_field_as_edge_type_def
      by simp
    have "(type (id_to_list containedtype), type (id_to_list containedtype)) \<in> inh (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
      unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
      by simp
    then have "(type\<^sub>n n, tgt et) \<in> inh (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
      using n_def et_def
      by fastforce
    then show ?thesis
      using et_in_ig n_in_ig instance_graph_valid instance_graph.validity_ingoing_mult
      by blast
  qed
next
  have instance_graph_valid: "instance_graph (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
    by (intro ig_contained_class_set_field_as_edge_type_correct) (simp_all add: assms)
  have type_neq: "type (id_to_list classtype) \<noteq> type (id_to_list containedtype)"
    using classtype_containedtype_neq LabDef.inject(1) id_to_list_inverse
    by metis
  fix n
  assume n_both: "n \<in> N IG \<inter> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
  then have n_def: "n \<in> typed (type (id_to_list classtype)) ` objects"
    unfolding ig_contained_class_set_field_as_edge_type_def
    using existing_objects
    by auto
  have set_eq: "{e \<in> E IG \<union> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
    type\<^sub>e e \<in> contains (TG IG) \<union> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} =
    {e \<in> E IG. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG)}"
  proof
    show "{e \<in> E IG \<union> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
      type\<^sub>e e \<in> contains (TG IG) \<union> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))}
      \<subseteq> {e \<in> E IG. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG)}"
    proof
      fix x
      assume "x \<in> {e \<in> E IG \<union> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
        type\<^sub>e e \<in> contains (TG IG) \<union> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))}"
      then show "x \<in> {e \<in> E IG. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG)}"
      proof
        assume assump: "x \<in> E IG \<union> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> tgt x = n \<and> 
          type\<^sub>e x \<in> contains (TG IG) \<union> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
        then have "x \<in> E IG \<union> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
          by simp
        then show "x \<in> {e \<in> E IG. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG)}"
        proof (elim UnE)
          assume x_def: "x \<in> E IG"
          then have "type\<^sub>e x \<in> ET (TG IG)"
            using assms(1) instance_graph.structure_edges_wellformed_edge_type_alt
            by blast
          then have "type\<^sub>e x \<notin> ET (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
            unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
            using new_edge_type assms(1) instance_graph.validity_type_graph type_graph.structure_edges_wellformed_src_node type_graph.validity_inh_node
            by fastforce
          then have "type\<^sub>e x \<notin> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
            using instance_graph.validity_type_graph instance_graph_valid type_graph.structure_contains_wellformed
            by blast
          then show ?thesis
            using assump x_def
            by blast
        next
          assume "x \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
          then have "x \<in> (\<lambda>x. (typed (type (id_to_list classtype)) (fst x), 
            (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype)), 
            typed (type (id_to_list containedtype)) (snd x))) ` values_to_pairs objects values"
            unfolding ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def
            by simp
          then have tgt_type_def: "type\<^sub>n (tgt x) = type (id_to_list containedtype)"
            by fastforce
          have "type\<^sub>n n = type (id_to_list classtype)"
            using n_def
            by fastforce
          then show ?thesis
            using tgt_type_def type_neq assump
            by simp
        qed
      qed
    qed
  next
    show "{e \<in> E IG. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG)} \<subseteq>
      {e \<in> E IG \<union> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
      type\<^sub>e e \<in> contains (TG IG) \<union> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))}"
      by blast
  qed
  have "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG)} \<le> 1"
    using assms(1) n_both instance_graph.validity_contained_node
    by blast
  then show "card {e \<in> E IG \<union> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). tgt e = n \<and> 
    type\<^sub>e e \<in> contains (TG IG) \<union> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} \<le> 1"
    using set_eq
    by simp
next
  have instance_graph_valid: "instance_graph (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
    by (intro ig_contained_class_set_field_as_edge_type_correct) (simp_all add: assms)
  have type_neq: "type (id_to_list classtype) \<noteq> type (id_to_list containedtype)"
    using classtype_containedtype_neq LabDef.inject(1) id_to_list_inverse
    by metis
  then have nodes_neq: "typed (type (id_to_list classtype)) ` objects \<inter> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects) = {}"
    by blast
  then have nodes_ig_neq: "N IG \<inter> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects) = {}"
    using existing_objects
    by blast
  have containments_block_irrefl: "irrefl ((edge_to_tuple ` {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
    type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))})\<^sup>+)"
  proof (intro validity_containment_alt)
    fix e
    assume "e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
    then show "src e \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> 
      tgt e \<in> N (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
      using instance_graph_valid instance_graph.structure_edges_wellformed_src_node_alt instance_graph.structure_edges_wellformed_tgt_node_alt
      by blast
  next
    show "\<And>p. \<not>pre_digraph.cycle (instance_graph_containment_proj (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)) p"
      using instance_graph_valid instance_graph.validity_containment
      by blast
  qed
  have containments_block_def: "\<And>s t. (s, t) \<in> edge_to_tuple ` {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
    type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))} \<Longrightarrow>
    s \<in> typed (type (id_to_list classtype)) ` objects \<and> t \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
  proof (elim imageE)
    fix s t e
    assume e_def: "e \<in> {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
      type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))}"
    assume s_t_def: "(s, t) = edge_to_tuple e"
    show "s \<in> typed (LabDef.type (id_to_list classtype)) ` objects \<and> t \<in> typed (LabDef.type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
      using e_def
    proof
      assume "e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) \<and> 
        type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))"
      then have edge_def: "e \<in> (\<lambda>x. (typed (type (id_to_list classtype)) (fst x), 
        (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype)), 
        typed (type (id_to_list containedtype)) (snd x))) ` values_to_pairs objects values"
        unfolding ig_contained_class_set_field_as_edge_type_def
        by simp
      have "src e \<in> typed (type (id_to_list classtype)) ` fst ` values_to_pairs objects values"
        using edge_def
        by force
      then have "src e \<in> typed (type (id_to_list classtype)) ` objects"
        using values_to_pairs_fst
        by blast
      then have s_def: "s \<in> typed (type (id_to_list classtype)) ` objects"
        using s_t_def
        unfolding edge_to_tuple_def
        by blast
      have "tgt e \<in> typed (type (id_to_list containedtype)) ` snd ` values_to_pairs objects values"
        using edge_def
        by force
      then have tgt_e_def: "tgt e \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
        using values_to_pairs_snd
        by blast
      then have t_def: "t \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
        using s_t_def
        unfolding edge_to_tuple_def
        by blast
      show "s \<in> typed (LabDef.type (id_to_list classtype)) ` objects \<and> t \<in> typed (LabDef.type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
        using s_def t_def
        by blast
    qed
  qed
  have containments_ig_irrefl: "irrefl ((edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)})\<^sup>+)"
  proof (intro validity_containment_alt)
    fix e
    assume "e \<in> E IG"
    then show "src e \<in> N IG \<and> tgt e \<in> N IG"
      using assms(1) instance_graph.structure_edges_wellformed_src_node_alt instance_graph.structure_edges_wellformed_tgt_node_alt
      by blast
  next
    show "\<And>p. \<not>pre_digraph.cycle (instance_graph_containment_proj IG) p"
      using assms(1) instance_graph.validity_containment
      by blast
  qed
  have containments_ig_def: "\<And>s t. (s, t) \<in> edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)} \<Longrightarrow> s \<in> N IG \<and> t \<in> N IG"
  proof (elim imageE)
    fix s t e
    assume e_def: "e \<in> {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}"
    assume s_t_def: "(s, t) = edge_to_tuple e"
    show "s \<in> N IG \<and> t \<in> N IG"
      using e_def
    proof
      assume assump: "e \<in> E IG \<and> type\<^sub>e e \<in> contains (TG IG)"
      then have "src e \<in> N IG"
        using assms(1) instance_graph.structure_edges_wellformed_src_node_alt
        by blast
      then have s_def: "s \<in> N IG"
        using s_t_def
        unfolding edge_to_tuple_def
        by blast
      have "tgt e \<in> N IG"
        using assump assms(1) instance_graph.structure_edges_wellformed_tgt_node_alt
        by blast
      then have t_def: "t \<in> N IG"
        using s_t_def
        unfolding edge_to_tuple_def
        by blast
      show "s \<in> N IG \<and> t \<in> N IG"
        using s_def t_def
        by blast
    qed
  qed
  have "\<And>x. (x, x) \<notin> (edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)} \<union>
    edge_to_tuple ` {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
    type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))})\<^sup>+"
  proof
    fix x
    assume "(x, x) \<in> (edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)} \<union>
      edge_to_tuple ` {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
      type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))})\<^sup>+"
    then show "False"
    proof (cases)
      case base
      then show ?thesis
      proof (elim UnE)
        assume "(x, x) \<in> edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}"
        then show ?thesis
          using containments_ig_irrefl
          unfolding irrefl_def
          by blast
      next
        assume "(x, x) \<in> edge_to_tuple ` {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
          type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))}"
        then show ?thesis
          using containments_block_irrefl
          unfolding irrefl_def
          by blast
      qed
    next
      case (step c)
      then show ?thesis
      proof (elim UnE)
        assume c_x_def: "(c, x) \<in> edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}"
        then have c_def: "c \<in> N IG"
          using containments_ig_def
          by blast
        have "(x, c) \<in> (edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)})\<^sup>+"
          using step(1) c_def
        proof (induct)
          case (base y)
          then show ?case
            using containments_block_def nodes_ig_neq
            by blast
        next
          case (step y z)
          then have y_z_def: "(y, z) \<in> edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}"
            using containments_block_def nodes_ig_neq
            by blast
          then have "(x, y) \<in> (edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)})\<^sup>+"
            using containments_ig_def step(3)
            by blast
          then show ?case
            using y_z_def
            by simp
        qed
        then have "(x, x) \<in> (edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)})\<^sup>+"
          using c_x_def
          by simp
        then show ?thesis
          using containments_ig_irrefl irrefl_def
          by fastforce
      next
        assume assump: "(c, x) \<in> edge_to_tuple ` {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
          type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))}"
        then have x_def: "x \<in> typed (type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)"
          using containments_block_def
          by blast
        have "c \<in> typed (type (id_to_list classtype)) ` objects"
          using assump containments_block_def
          by blast
        then have c_def: "c \<in> N IG"
          using existing_objects
          by blast
        have "(x, c) \<in> (edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)})\<^sup>+"
          using step(1) c_def
        proof (induct)
          case (base y)
          then show ?case
            using containments_block_def nodes_ig_neq
            by blast
        next
          case (step y z)
          then have y_z_def: "(y, z) \<in> edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}"
            using containments_block_def nodes_ig_neq
            by blast
          then have "(x, y) \<in> (edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)})\<^sup>+"
            using containments_ig_def step(3)
            by blast
          then show ?case
            using y_z_def
            by simp
        qed
        then have "x \<in> N IG"
          using containments_ig_def
        proof (induct)
          case (base y)
          then show ?case
            by blast
        next
          case (step y z)
          then show ?case
            by blast
        qed
        then show ?thesis
          using x_def objects_unique existing_objects
          by blast
      qed
    qed
  qed
  then show "irrefl ((edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)} \<union>
    edge_to_tuple ` {e \<in> E (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values). 
    type\<^sub>e e \<in> contains (TG (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values))})\<^sup>+)"
    unfolding irrefl_def
    by simp
qed (simp_all add: ig_contained_class_set_field_as_edge_type_def tg_contained_class_set_field_as_edge_type_def assms)



subsection "Transformation functions"

definition imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> multiplicity \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 'o list) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values Imod = \<lparr>
    TG = tg_contained_class_set_field_as_edge_type classtype name containedtype mul,
    Id = obids ` Object Imod,
    N = typed (type (id_to_list classtype)) ` {ob \<in> Object Imod. ob \<in> objects} \<union> typed (type (id_to_list containedtype)) ` {ob \<in> Object Imod. ob \<in> sets_to_set (set ` values ` objects)},
    E = (\<lambda>x. (typed (type (id_to_list classtype)) (fst x), (type (id_to_list classtype), LabDef.edge [name], type (id_to_list containedtype)), typed (type (id_to_list containedtype)) (snd x))) ` values_to_pairs {ob \<in> Object Imod. ob \<in> objects} values,
    ident = (\<lambda>x. if x \<in> obids ` objects then typed (type (id_to_list classtype)) (THE y. obids y = x) else 
      if x \<in> obids ` sets_to_set (set ` values ` objects) then typed (type (id_to_list containedtype)) (THE y. obids y = x) else undefined)
  \<rparr>"

lemma imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type_proj:
  shows "imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values (imod_contained_class_set_field classtype name containedtype mul objects obids values) = 
    ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values"
proof-
  have "values_to_pairs {ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values). ob \<in> objects} values = values_to_pairs objects values"
  proof-
    have "{ob \<in> Object (imod_contained_class_set_field classtype name containedtype mul objects obids values). ob \<in> objects} = objects"
      unfolding imod_contained_class_set_field_def
      by auto
    then show ?thesis
      by simp
  qed
  then show "imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values (imod_contained_class_set_field classtype name containedtype mul objects obids values) = 
    ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values"
    unfolding imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type_def ig_contained_class_set_field_as_edge_type_def imod_contained_class_set_field_def
    by auto
qed
  

lemma imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type_func:
  shows "ig_combine_mapping_function (imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)
    (imod_contained_class_set_field classtype name containedtype mul objects obids values) (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values)"
proof (intro ig_combine_mapping_function.intro)
  show "imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values (imod_contained_class_set_field classtype name containedtype mul objects obids values) = 
    ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values"
    by (fact imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type_proj)
next
  fix ImodX
  show "E (imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values (imod_contained_class_set_field classtype name containedtype mul objects obids values))
    \<subseteq> E (imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values (imod_combine (imod_contained_class_set_field classtype name containedtype mul objects obids values) ImodX))"
  proof
    fix x
    have value_to_pairs_def: "values_to_pairs {ob. (ob \<in> objects \<or> ob \<in> sets_to_set (set ` values ` objects)) \<and> ob \<in> objects} values \<subseteq> 
      values_to_pairs {ob. (ob \<in> objects \<or> ob \<in> sets_to_set (set ` values ` objects) \<or> ob \<in> Object ImodX) \<and> ob \<in> objects} values"
    proof
      fix x
      assume "x \<in> values_to_pairs {ob. (ob \<in> objects \<or> ob \<in> sets_to_set (set ` values ` objects)) \<and> ob \<in> objects} values"
      then show "x \<in> values_to_pairs {ob. (ob \<in> objects \<or> ob \<in> sets_to_set (set ` values ` objects) \<or> ob \<in> Object ImodX) \<and> ob \<in> objects} values"
      proof (induct x)
        case (Pair a b)
        then show ?case
        proof (induct)
          case (rule_member x y)
          then have "x \<in> {ob. (ob \<in> objects \<or> ob \<in> sets_to_set (set ` values ` objects) \<or> ob \<in> Object ImodX) \<and> ob \<in> objects}"
            by simp
          then show ?case
            by (simp add: rule_member.hyps(2) values_to_pairs.rule_member)
        qed
      qed
    qed
    assume "x \<in> E (imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values (imod_contained_class_set_field classtype name containedtype mul objects obids values))"
    then show "x \<in> E (imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values (imod_combine (imod_contained_class_set_field classtype name containedtype mul objects obids values) ImodX))"
      unfolding imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type_def imod_contained_class_set_field_def ig_contained_class_set_field_as_edge_type_def imod_combine_def
      using value_to_pairs_def
      by auto
  qed
qed (auto simp add: imod_contained_class_set_field_to_ig_contained_class_set_field_as_edge_type_def imod_contained_class_set_field_def ig_contained_class_set_field_as_edge_type_def imod_combine_def)

definition ig_contained_class_set_field_as_edge_type_to_imod_contained_class_set_field :: "'t Id \<Rightarrow> 't \<Rightarrow> 't Id \<Rightarrow> multiplicity \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o \<Rightarrow> 'o list) \<Rightarrow> ('o, 't list, 't) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "ig_contained_class_set_field_as_edge_type_to_imod_contained_class_set_field classtype name containedtype mul objects obids values IG = \<lparr>
    Tm = tmod_contained_class_set_field classtype name containedtype mul,
    Object = nodeId ` N IG,
    ObjectClass = (\<lambda>x. if x \<in> objects then classtype else if x \<in> sets_to_set (set ` values ` objects) then containedtype else undefined),
    ObjectId = (\<lambda>x. if x \<in> objects \<union> sets_to_set (set ` values ` objects) then obids x else undefined),
    FieldValue = (\<lambda>x. if fst x \<in> objects \<and> snd x = (classtype, name) then setof (map obj (values (fst x))) else
      if fst x \<in> sets_to_set (set ` values ` objects) \<and> snd x = (classtype, name) then unspecified else undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_contained_class_set_field_as_edge_type_to_imod_contained_class_set_field_proj:
  shows "ig_contained_class_set_field_as_edge_type_to_imod_contained_class_set_field classtype name containedtype mul objects obids values (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) = 
    imod_contained_class_set_field classtype name containedtype mul objects obids values"
proof-
  have "nodeId ` (typed (LabDef.type (id_to_list classtype)) ` objects) = objects"
    by force
  then have objects_def: "\<And>x. x \<in> objects \<Longrightarrow> 
    x \<in> nodeId ` (typed (LabDef.type (id_to_list classtype)) ` objects \<union> typed (LabDef.type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects))"
    by blast
  have "nodeId ` (typed (LabDef.type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects)) = sets_to_set (set ` values ` objects)"
    by force
  then have values_def: "\<And>x. x \<in> sets_to_set (set ` values ` objects) \<Longrightarrow> 
    x \<in> nodeId ` (typed (LabDef.type (id_to_list classtype)) ` objects \<union> typed (LabDef.type (id_to_list containedtype)) ` sets_to_set (set ` values ` objects))"
    by blast
  show ?thesis
    unfolding ig_contained_class_set_field_as_edge_type_to_imod_contained_class_set_field_def imod_contained_class_set_field_def ig_contained_class_set_field_as_edge_type_def
    using objects_def values_def
    by auto
qed

lemma ig_contained_class_set_field_as_edge_type_to_imod_contained_class_set_field_func:
  shows "imod_combine_mapping_function (ig_contained_class_set_field_as_edge_type_to_imod_contained_class_set_field classtype name containedtype mul objects obids values)
    (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) (imod_contained_class_set_field classtype name containedtype mul objects obids values)"
proof (intro imod_combine_mapping_function.intro)
  show "ig_contained_class_set_field_as_edge_type_to_imod_contained_class_set_field classtype name containedtype mul objects obids values (ig_contained_class_set_field_as_edge_type classtype name containedtype mul objects obids values) =
    imod_contained_class_set_field classtype name containedtype mul objects obids values"
    by (fact ig_contained_class_set_field_as_edge_type_to_imod_contained_class_set_field_proj)
qed (auto simp add: ig_contained_class_set_field_as_edge_type_to_imod_contained_class_set_field_def imod_contained_class_set_field_def ig_contained_class_set_field_as_edge_type_def ig_combine_def)

end