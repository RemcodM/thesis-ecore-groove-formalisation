theory SubclassInstance
  imports
    Main
    "Ecore-GROOVE-Mapping.Instance_Model_Graph_Mapping"
    SubclassType
begin

section "Definition of an instance model which introduces an object typed by a regular subclass"

definition imod_subclass :: "'t Id \<Rightarrow> 't Id \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't) instance_model" where
  "imod_subclass name supertype objects fid = \<lparr>
    Tm = tmod_subclass name supertype,
    Object = objects,
    ObjectClass = (\<lambda>x. if x \<in> objects then name else undefined),
    ObjectId = (\<lambda>x. if x \<in> objects then fid x else undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_subclass_correct:
  assumes name_supertype_neq: "name \<noteq> supertype"
  assumes name_supertype_ns_valid: "\<not>id_in_ns name (Identifier supertype) \<and> \<not>id_in_ns supertype (Identifier name)"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> o2 \<in> objects \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  shows "instance_model (imod_subclass name supertype objects fid)"
proof (intro instance_model.intro)
  show "type_model (Tm (imod_subclass name supertype objects fid))"
    unfolding imod_subclass_def
    using tmod_subclass_correct assms
    by simp
qed (simp_all add: assms imod_subclass_def tmod_subclass_def)

lemma imod_subclass_combine_correct:
  assumes "instance_model Imod"
  assumes name_supertype_neq: "name \<noteq> supertype"
  assumes name_supertype_ns_valid: "\<not>id_in_ns name (Identifier supertype) \<and> \<not>id_in_ns supertype (Identifier name)"
  assumes combined_classes: "Class (Tm Imod) \<inter> {supertype, name} = {supertype}"
  assumes new_subclass: "name \<notin> Class (Tm Imod) \<union> Enum (Tm Imod) \<union> UserDataType (Tm Imod)"
  assumes name_namespace_valid: "\<And>x. x \<in> Class (Tm Imod) \<union> Enum (Tm Imod) \<union> UserDataType (Tm Imod) \<Longrightarrow> \<not>id_in_ns name (Identifier x) \<and> \<not>id_in_ns x (Identifier name)"
  assumes new_objects: "objects \<inter> Object Imod = {}"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> o2 \<in> objects \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  assumes new_ids: "\<And>o1 o2. o1 \<in> Object Imod \<Longrightarrow> o2 \<in> objects \<Longrightarrow> ObjectId Imod o1 \<noteq> fid o2"
  assumes no_fields_supertype: "Type_Model.fields (Tm Imod) supertype = {}"
  shows "instance_model (imod_combine Imod (imod_subclass name supertype objects fid))"
proof (intro imod_combine_merge_no_containment_imod2_correct)
  show "instance_model (imod_subclass name supertype objects fid)"
    using assms imod_subclass_correct
    by blast
next
  fix ob
  assume ob_in_imod: "ob \<in> Object Imod"
  assume "ob \<in> Object (imod_subclass name supertype objects fid)"
  then have "ob \<in> objects"
    unfolding imod_subclass_def
    by simp
  then show "ObjectClass Imod ob = ObjectClass (imod_subclass name supertype objects fid) ob"
    using new_objects ob_in_imod
    by blast
next
  fix ob
  assume ob_in_imod: "ob \<in> Object Imod"
  assume "ob \<in> Object (imod_subclass name supertype objects fid)"
  then have "ob \<in> objects"
    unfolding imod_subclass_def
    by simp
  then show "ObjectId Imod ob = ObjectId (imod_subclass name supertype objects fid) ob"
    using new_objects ob_in_imod
    by blast
next
  have type_model_correct: "type_model (tmod_combine (Tm Imod) (tmod_subclass name supertype))"
    using tmod_subclass_combine_correct assms instance_model.validity_type_model_consistent
    by metis
  fix ob f
  assume "ob \<in> Object (imod_subclass name supertype objects fid)"
  then have ob_def: "ob \<in> objects"
    by (simp add: imod_subclass_def)
  then have ob_type_def: "ObjectClass (imod_combine Imod (imod_subclass name supertype objects fid)) ob = name"
    unfolding imod_subclass_def imod_combine_def imod_combine_object_class_def
    using new_objects
    by auto
  assume f_in_field_tmod: "f \<in> Field (Tm Imod)"
  then have f_class_not_supertype: "fst f \<noteq> supertype"
  proof (induct "fst f = supertype")
    case True
    then have "\<exclamdown>(fst f) \<in> ProperClassType (Tm Imod)"
      using ProperClassType.simps assms(1) instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
      by blast
    then have "\<exclamdown>(fst f) \<in> Type (Tm Imod)"
      unfolding Type_def NonContainerType_def ClassType_def
      by blast
    then have "f \<in> Type_Model.fields (Tm Imod) supertype"
      unfolding Type_Model.fields_def subtype_def
      using True.hyps True.prems subtype_rel.reflexivity
      by fastforce
    then show ?case
      by (simp add: no_fields_supertype)
  next
    case False
    then show ?case
      by simp
  qed
  have supertype_not_inherits_f: "(supertype, fst f) \<notin> (Inh (Tm Imod) \<union> {(name, supertype)})\<^sup>+"
  proof-
    have "\<not>\<exclamdown>supertype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst f)"
    proof
      assume "\<exclamdown>supertype \<sqsubseteq>[Tm Imod] \<exclamdown>(fst f)"
      then have "f \<in> Type_Model.fields (Tm Imod) supertype"
        using f_in_field_tmod
        unfolding Type_Model.fields_def
        by fastforce
      then show "False"
        using no_fields_supertype
        by blast
    qed
    then have not_in_altdef: "(\<exclamdown>supertype, \<exclamdown>(fst f)) \<notin> subtype_rel_altdef (Tm Imod)"
      unfolding subtype_def
      by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
    have "(supertype, fst f) \<in> (Inh (Tm Imod))\<^sup>+ \<Longrightarrow> (\<exclamdown>supertype, \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
    proof-
      assume "(supertype, fst f) \<in> (Inh (Tm Imod))\<^sup>+"
      then have "(\<exclamdown>supertype, \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
        unfolding subtype_conv_def
        by force
      then show "(\<exclamdown>supertype, \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
        unfolding subtype_rel_altdef_def
        by blast
    qed
    then have not_in_inh: "(supertype, fst f) \<notin> (Inh (Tm Imod))\<^sup>+"
      using not_in_altdef
      by blast
    have "(supertype, fst f) \<in> (Inh (Tm Imod) \<union> {(name, supertype)})\<^sup>+ \<Longrightarrow> (supertype, fst f) \<in> (Inh (Tm Imod))\<^sup>+"
    proof-
      assume "(supertype, fst f) \<in> (Inh (Tm Imod) \<union> {(name, supertype)})\<^sup>+"
      then show "(supertype, fst f) \<in> (Inh (Tm Imod))\<^sup>+"
      proof (induct)
        case (base y)
        then show ?case
          using name_supertype_neq
          by blast
      next
        case (step y z)
        then show ?case
        proof (elim UnE)
          assume "(y, z) \<in> Inh (Tm Imod)"
          then show ?thesis
            using step.hyps(3)
            by fastforce
        next
          assume "(y, z) \<in> {(name, supertype)}"
          then show ?thesis
            using Pair_inject irrefl_def singletonD step.hyps tmod_combine_def tmod_subclass_def type_model_correct
            using trancl.trancl_into_trancl type_model.property_inh_wellformed_trancl_irrefl type_model.select_convs(7)
            by metis
        qed
      qed
    qed
    then show ?thesis
      using not_in_inh
      by blast
  qed
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_subclass name supertype objects fid)) ob) 
    \<sqsubseteq>[Tm (imod_combine Imod (imod_subclass name supertype objects fid))] 
    \<exclamdown>(class (Tm (imod_combine Imod (imod_subclass name supertype objects fid))) f)"
  then have name_extends_field_class: "\<exclamdown>name \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_subclass name supertype)] \<exclamdown>(fst f)"
    using ob_type_def
    unfolding class_def imod_combine_def imod_subclass_def
    by simp
  have "\<not>(\<exclamdown>name \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_subclass name supertype)] \<exclamdown>(fst f))"
  proof
    assume "\<exclamdown>name \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_subclass name supertype)] \<exclamdown>(fst f)"
    then have "(\<exclamdown>name, \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_subclass name supertype))"
      unfolding subtype_def
      by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_correct)
    then show "False"
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume "(\<exclamdown>name, \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_subclass name supertype))"
      then have "name = fst f"
        unfolding subtype_tuple_def
        by blast
      then show ?thesis
        using UnI1 assms(1) f_in_field_tmod instance_model.validity_type_model_consistent new_subclass type_model.structure_field_wellformed_class
        by metis
    next
      assume "(\<exclamdown>name, \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_subclass name supertype)))\<^sup>+"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    next
      assume "(\<exclamdown>name, \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_subclass name supertype)))\<^sup>+"
      then have "(name, fst f) \<in> (Inh (tmod_combine (Tm Imod) (tmod_subclass name supertype)))\<^sup>+"
        unfolding subtype_conv_def
        by fastforce
      then have name_subtype: "(name, fst f) \<in> (Inh (Tm Imod) \<union> {(name, supertype)})\<^sup>+"
        unfolding tmod_combine_def tmod_subclass_def
        by simp
      have name_inherits_supertype: "\<And>x. (name, x) \<in> Inh (Tm Imod) \<union> {(name, supertype)} \<Longrightarrow> x = supertype"
      proof (elim UnE)
        fix x
        assume "(name, x) \<in> Inh (Tm Imod)"
        then show "x = supertype"
          using UnI1 assms(1) instance_model.validity_type_model_consistent new_subclass type_model.structure_inh_wellformed_alt
          by metis
      next
        fix x
        assume "(name, x) \<in> {(name, supertype)}"
        then show "x = supertype"
          by simp
      qed
      have "(supertype, fst f) \<in> (Inh (Tm Imod) \<union> {(name, supertype)})\<^sup>+"
        using name_subtype
      proof (cases)
        case base
        then show ?thesis
          using f_class_not_supertype name_inherits_supertype
          by blast
      next
        case (step c)
        then show ?thesis
          using converse_tranclE f_class_not_supertype name_inherits_supertype name_subtype
          by metis
      qed
      then show ?thesis
        using supertype_not_inherits_f
        by blast
    next
      assume "(\<exclamdown>name, \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_subclass name supertype))"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    next
      assume "(\<exclamdown>name, \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_subclass name supertype)))\<^sup>+"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    qed
  qed
  then show "ob \<in> Object Imod \<and> \<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) f)"
    using name_extends_field_class
    by blast
next
  have type_model_correct: "type_model (tmod_combine (Tm Imod) (tmod_subclass name supertype))"
    using tmod_subclass_combine_correct assms instance_model.validity_type_model_consistent
    by metis
  fix ob f
  assume ob_in_imod: "ob \<in> Object Imod"
  then have ob_class_def: "ObjectClass (imod_combine Imod (imod_subclass name supertype objects fid)) ob = ObjectClass Imod ob"
    unfolding imod_combine_def imod_subclass_def imod_combine_object_class_def
    using new_objects
    by auto
  then have ob_class_not_name: "ObjectClass Imod ob \<noteq> name"
    using assms(1) instance_model.structure_object_class_wellformed new_subclass ob_in_imod
    by fastforce
  assume f_in_field: "f \<in> Field (Tm Imod)"
  then have f_class_in_imod: "fst f \<in> Class (Tm Imod)"
    by (simp add: assms(1) instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
  assume "\<exclamdown>(ObjectClass (imod_combine Imod (imod_subclass name supertype objects fid)) ob) 
    \<sqsubseteq>[Tm (imod_combine Imod (imod_subclass name supertype objects fid))] 
    \<exclamdown>(class (Tm (imod_combine Imod (imod_subclass name supertype objects fid))) f)"
  then have "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[tmod_combine (Tm Imod) (tmod_subclass name supertype)] \<exclamdown>(fst f)"
    using ob_class_def
    unfolding class_def imod_combine_def imod_subclass_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod) (tmod_subclass name supertype))"
    unfolding subtype_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes type_model_correct)
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> 
    subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_subclass name supertype)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_subclass name supertype)))\<^sup>+ \<union> 
    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_subclass name supertype)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_subclass name supertype)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_subclass name supertype)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod)"
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod) (tmod_subclass name supertype))"
    then have eq: "ObjectClass Imod ob = fst f"
      unfolding subtype_tuple_def
      by fastforce
    have "\<exclamdown>(ObjectClass Imod ob) \<in> ProperClassType (Tm Imod)"
      by (simp add: ProperClassType.rule_proper_classes assms(1) instance_model.structure_object_class_wellformed ob_in_imod)
    then have "\<exclamdown>(ObjectClass Imod ob) \<in> Type (Tm Imod)"
      unfolding Type_def NonContainerType_def ClassType_def
      by simp
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (Tm Imod)"
      by (simp add: eq subtype_tuple_def)
    then show ?thesis
      unfolding subtype_rel_altdef_def
      by simp
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod) (tmod_subclass name supertype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod) (tmod_subclass name supertype)))\<^sup>+"
    then have "(ObjectClass Imod ob, fst f) \<in> (Inh (tmod_combine (Tm Imod) (tmod_subclass name supertype)))\<^sup>+"
      unfolding subtype_conv_def
      by fastforce
    then have "(ObjectClass Imod ob, fst f) \<in> (Inh (Tm Imod) \<union> {(name, supertype)})\<^sup>+"
      unfolding tmod_combine_def tmod_subclass_def
      by simp
    then have "(ObjectClass Imod ob, fst f) \<in> (Inh (Tm Imod))\<^sup>+"
    proof (induct)
      case (base y)
      then show ?case
        by (simp add: ob_class_not_name)
    next
      case (step y z)
      then have "y \<noteq> name"
        using UnI1 assms(1) instance_model.validity_type_model_consistent new_subclass trancl.simps type_model.structure_inh_wellformed_alt
        by metis
      then show ?case
        using step.hyps(2) step.hyps(3)
        by simp
    qed
    then have "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod))\<^sup>+"
      unfolding subtype_conv_def
      by force
    then show ?thesis
      by (simp add: subtype_rel_altdef_def)
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod) (tmod_subclass name supertype))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod) (tmod_subclass name supertype)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then show "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) f)"
    unfolding class_def
    by (simp add: assms(1) instance_model.validity_type_model_consistent subtype_def subtype_rel_alt type_model.structure_inh_wellformed_classes)
next
  have "type_model (tmod_combine (Tm Imod) (tmod_subclass name supertype))"
    using tmod_subclass_combine_correct assms instance_model.validity_type_model_consistent
    by metis
  then show "type_model (tmod_combine (Tm Imod) (Tm (imod_subclass name supertype objects fid)))"
    unfolding imod_subclass_def
    by simp
qed (simp_all add: assms imod_subclass_def tmod_subclass_def)



section "Encoding of a Slass as Node Type in GROOVE"

definition ig_subclass_as_node_type :: "'t Id \<Rightarrow> 't Id \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "ig_subclass_as_node_type name supertype objects fid = \<lparr>
    TG = tg_subclass_as_node_type name supertype,
    Id = fid ` objects,
    N = typed (type (id_to_list name)) ` objects,
    E = {},
    ident = (\<lambda>x. if x \<in> fid ` objects then typed (type (id_to_list name)) (THE y. fid y = x) else undefined)
  \<rparr>"

lemma ig_subclass_as_node_type_correct: 
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  shows "instance_graph (ig_subclass_as_node_type name supertype objects fid)"
proof (intro instance_graph.intro)
  fix n
  assume "n \<in> N (ig_subclass_as_node_type name supertype objects fid)"
  then have "n \<in> typed (type (id_to_list name)) ` objects"
    unfolding ig_subclass_as_node_type_def
    by simp
  then have "n \<in> Node\<^sub>t"
    using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
    by fastforce
  then show "n \<in> Node"
    unfolding Node_def
    by simp
next
  fix i
  assume "i \<in> Id (ig_subclass_as_node_type name supertype objects fid)"
  then have i_in_id: "i \<in> fid ` objects"
    unfolding ig_subclass_as_node_type_def
    by simp
  then show "ident (ig_subclass_as_node_type name supertype objects fid) i \<in> N (ig_subclass_as_node_type name supertype objects fid) \<and> type\<^sub>n (ident (ig_subclass_as_node_type name supertype objects fid) i) \<in> Lab\<^sub>t"
  proof (intro conjI)
    assume "i \<in> fid ` objects"
    then have "(THE y. fid y = i) \<in> objects"
    proof
      fix x
      assume i_def: "i = fid x"
      assume x_is_object: "x \<in> objects"
      have "(THE y. fid y = fid x) \<in> objects"
      proof (rule the1I2)
        show "\<exists>!y. fid y = fid x"
          using unique_ids x_is_object
          by metis
      next
        fix y
        assume "fid y = fid x"
        then show "y \<in> objects"
          using unique_ids x_is_object
          by metis
      qed
      then show "(THE y. fid y = i) \<in> objects"
        by (simp add: i_def)
    qed
    then have "typed (type (id_to_list name)) (THE y. fid y = i) \<in> typed (type (id_to_list name)) ` objects"
      by simp
    then show "ident (ig_subclass_as_node_type name supertype objects fid) i \<in> N (ig_subclass_as_node_type name supertype objects fid)"
      unfolding ig_subclass_as_node_type_def
      using i_in_id
      by simp
  next
    have "type\<^sub>n (typed (type (id_to_list name)) (THE y. fid y = i)) = type (id_to_list name)"
      by simp
    then have "type\<^sub>n (typed (type (id_to_list name)) (THE y. fid y = i)) \<in> Lab\<^sub>t"
      by (simp add: Lab\<^sub>t.rule_type_labels)
    then show "type\<^sub>n (ident (ig_subclass_as_node_type name supertype objects fid) i) \<in> Lab\<^sub>t"
      unfolding ig_subclass_as_node_type_def
      using i_in_id
      by simp
  qed
next
  show "type_graph (TG (ig_subclass_as_node_type name supertype objects fid))"
    unfolding ig_subclass_as_node_type_def
    using tg_subclass_as_node_type_correct
    by simp
next
  fix n
  assume "n \<in> N (ig_subclass_as_node_type name supertype objects fid)"
  then have "n \<in> typed (type (id_to_list name)) ` objects"
    unfolding ig_subclass_as_node_type_def
    by simp
  then have "type\<^sub>n n = type (id_to_list name)"
    by auto
  then show "type\<^sub>n n \<in> NT (TG (ig_subclass_as_node_type name supertype objects fid))"
    unfolding ig_subclass_as_node_type_def tg_subclass_as_node_type_def
    by simp
next
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj (ig_subclass_as_node_type name supertype objects fid)) p"
    unfolding ig_subclass_as_node_type_def instance_graph_containment_proj_def pre_digraph.cycle_def pre_digraph.awalk_def
    by simp
qed (simp_all add: assms ig_subclass_as_node_type_def tg_subclass_as_node_type_def)

lemma ig_subclass_as_node_type_combine_correct:
  assumes "instance_graph IG"
  assumes name_supertype_neq: "name \<noteq> supertype"
  assumes combined_type: "NT (TG IG) \<inter> {type (id_to_list supertype), type (id_to_list name)} = {type (id_to_list supertype)}"
  assumes no_src_edge_types: "\<And>et. et \<in> ET (TG IG) \<Longrightarrow> (type (id_to_list supertype), src et) \<notin> inh (TG IG)"
  assumes no_tgt_edge_types: "\<And>et. et \<in> ET (TG IG) \<Longrightarrow> (type (id_to_list supertype), tgt et) \<notin> inh (TG IG)"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  assumes new_ids: "Id IG \<inter> fid ` objects = {}"
  shows "instance_graph (ig_combine IG (ig_subclass_as_node_type name supertype objects fid))"
proof (intro ig_combine_merge_no_containment_imod2_correct)
  show "instance_graph (ig_subclass_as_node_type name supertype objects fid)"
    using unique_ids
    by (fact ig_subclass_as_node_type_correct)
next
  fix i
  assume "i \<in> Id IG"
  then have i_not_in_ids: "i \<notin> fid ` objects"
    using new_ids
    by auto
  assume "i \<in> Id (ig_subclass_as_node_type name supertype objects fid)"
  then have "i \<in> fid ` objects"
    unfolding ig_subclass_as_node_type_def
    by simp
  then show "ident IG i = ident (ig_subclass_as_node_type name supertype objects fid) i"
    using i_not_in_ids
    by blast
next
  have "type_graph (tg_combine (TG IG) (tg_subclass_as_node_type name supertype))"
    using tg_subclass_as_node_type_combine_correct assms
    by (simp add: tg_subclass_as_node_type_combine_correct instance_graph.validity_type_graph)
  then show "type_graph (tg_combine (TG IG) (TG (ig_subclass_as_node_type name supertype objects fid)))"
    by (simp add: ig_subclass_as_node_type_def)
next
  have name_not_in_tg: "type (id_to_list name) \<notin> NT (TG IG)"
    using Int_insert_right_if1 doubleton_eq_iff id_to_list_inverse insert_absorb2 unlabel.simps(1) combined_type name_supertype_neq
    by metis
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  then have src_et_def: "src et \<in> NT (TG IG)"
    using assms(1) instance_graph.validity_type_graph type_graph.structure_edges_wellformed_alt
    by blast
  then have src_et_not_name: "src et \<noteq> type (id_to_list name)"
    using name_not_in_tg
    by fastforce
  have src_et_not_supertype: "src et \<noteq> type (id_to_list supertype)"
    using no_src_edge_types src_et_def assms(1) et_def instance_graph.validity_type_graph type_graph.validity_inh_node
    by metis
  have no_supertype_inh: "(type (id_to_list supertype), src et) \<notin> (inh (TG IG) \<union> 
    {(type (id_to_list name), type (id_to_list name)), 
    (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
  proof
    assume "(type (id_to_list supertype), src et) \<in> (inh (TG IG) \<union> 
      {(type (id_to_list name), type (id_to_list name)), 
      (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
    then show "False"
    proof (cases)
      case base
      then have "(LabDef.type (id_to_list supertype), src et) \<in> inh (TG IG)"
        using Pair_inject src_et_not_name
        by auto
      then show ?thesis
        using et_def no_src_edge_types
        by blast
    next
      case (step c)
      have "(LabDef.type (id_to_list supertype), c) \<in> (inh (TG IG))\<^sup>+"
        using step(1)
      proof (induct)
        case (base y)
        then show ?case
          using combined_type insertE name_not_in_tg
          by fastforce
      next
        case (step y z)
        then have "y \<in> NT (TG IG)"
          using assms(1) instance_graph.validity_type_graph trancl.simps type_graph.structure_inheritance_wellformed_second_node
          by metis
        then have "y \<noteq> type (id_to_list name)"
          using name_not_in_tg
          by blast
        then have "(y, z) \<in> inh (TG IG)"
          using step.hyps
          by simp
        then show ?case
          using step.hyps(3)
          by simp
      qed
      then have fst_tuple_def: "(LabDef.type (id_to_list supertype), c) \<in> inh (TG IG)"
        using assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans
        by fastforce
      then have "c \<in> NT (TG IG)"
        using assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_second_node
        by metis
      then have "c \<noteq> type (id_to_list name)"
        using name_not_in_tg
        by blast
      then have "(c, src et) \<in> inh (TG IG)"
        using step(2)
        by simp
      then show ?thesis
        using transE fst_tuple_def et_def no_src_edge_types assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans
        by metis
    qed
  qed
  assume "n \<in> N IG \<union> N (ig_subclass_as_node_type name supertype objects fid)"
  then have n_def: "n \<in> N IG \<union> typed (type (id_to_list name)) ` objects"
    by (simp add: ig_subclass_as_node_type_def)
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_subclass_as_node_type name supertype objects fid)))\<^sup>+"
  then have inh_unfold_def: "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> 
    {(type (id_to_list name), type (id_to_list name)), 
    (type (id_to_list supertype), type (id_to_list supertype)), 
    (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
    unfolding ig_subclass_as_node_type_def tg_subclass_as_node_type_def
    by simp
  have supertype_refl: "(type (id_to_list supertype), type (id_to_list supertype)) \<in> inh (TG IG)"
    using assms(1) combined_type instance_graph.validity_type_graph type_graph.validity_inh_node
    by fastforce
  then have inh_def: "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> 
    {(type (id_to_list name), type (id_to_list name)), 
    (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
    using inh_unfold_def
    by (simp add: insert_absorb)
  show "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG) et)"
    using n_def
  proof (elim UnE)
    assume n_in_ig: "n \<in> N IG"
    then have type_n_not_name: "type\<^sub>n n \<noteq> type (id_to_list name)"
      using IntI Un_insert_left Un_insert_right assms(1) combined_type id_to_list_inverse insertI1 
      using instance_graph.validity_node_typed name_supertype_neq singletonD sup_bot.right_neutral unlabel.simps(1)
      by metis
    have "(type\<^sub>n n, src et) \<in> (inh (TG IG))\<^sup>+"
      using inh_def
    proof (cases)
      case base
      then show ?thesis
        using type_n_not_name
        by simp
    next
      case (step c)
      have fst_tuple_def: "(type\<^sub>n n, c) \<in> (inh (TG IG))\<^sup>+"
        using step(1)
      proof (induct)
        case (base y)
        then show ?case
          using type_n_not_name
          by simp
      next
        case (step y z)
        then have "y \<in> NT (TG IG)"
          using assms(1) instance_graph.validity_type_graph trancl.simps type_graph.structure_inheritance_wellformed_second_node
          by metis
        then have "y \<noteq> type (id_to_list name)"
          using name_not_in_tg
          by blast
        then have "(y, z) \<in> inh (TG IG)"
          using step.hyps
          by simp
        then show ?case
          using step.hyps(3)
          by simp
      qed
      then have "c \<in> NT (TG IG)"
        using assms(1) instance_graph.validity_type_graph trancl.simps type_graph.structure_inheritance_wellformed_second_node
        by metis
      then have "c \<noteq> type (id_to_list name)"
        using name_not_in_tg
        by blast
      then have "(c, src et) \<in> inh (TG IG)"
        using step(2)
        by simp
      then show ?thesis
        using fst_tuple_def
        by simp
    qed
    then have "(type\<^sub>n n, src et) \<in> inh (TG IG)"
      using assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans
      by fastforce
    then show ?thesis
      using assms(1) instance_graph.validity_outgoing_mult n_in_ig et_def
      by blast
  next
    assume n_in_typed: "n \<in> typed (LabDef.type (id_to_list name)) ` objects"
    then have type_n_is_name: "type\<^sub>n n = type (id_to_list name)"
      by fastforce
    have name_inherits_supertype: "\<And>x. (type\<^sub>n n, x) \<in> (inh (TG IG) \<union> 
      {(type (id_to_list name), type (id_to_list name)), 
      (type (id_to_list name), type (id_to_list supertype))}) \<Longrightarrow> 
      x = type (id_to_list name) \<or> x = type (id_to_list supertype)"
    proof-
      fix x
      assume "(type\<^sub>n n, x) \<in> (inh (TG IG) \<union> 
        {(type (id_to_list name), type (id_to_list name)), 
        (type (id_to_list name), type (id_to_list supertype))})"
      then show "x = type (id_to_list name) \<or> x = type (id_to_list supertype)"
      proof (elim UnE)
        assume "(type\<^sub>n n, x) \<in> inh (TG IG)"
        then have "type\<^sub>n n \<in> NT (TG IG)"
          by (simp add: assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node)
        then show ?thesis
          using name_not_in_tg type_n_is_name
          by simp
      next
        assume "(type\<^sub>n n, x) \<in> {(type (id_to_list name), type (id_to_list name)), (type (id_to_list name), type (id_to_list supertype))}"
        then show ?thesis
          by blast
      qed
    qed
    have "(type\<^sub>n n, src et) \<notin> (inh (TG IG) \<union> 
      {(type (id_to_list name), type (id_to_list name)), 
      (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
    proof
      assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> 
        {(type (id_to_list name), type (id_to_list name)), 
        (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
      then show "False"
      proof (cases)
        case base
        then have "(type\<^sub>n n, src et) \<in> {(LabDef.type (id_to_list name), LabDef.type (id_to_list name)), (LabDef.type (id_to_list name), LabDef.type (id_to_list supertype))}"
          using assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node trancl.simps type_n_is_name name_not_in_tg
          by fastforce
        then show ?thesis
          using src_et_not_name src_et_not_supertype
          by blast
      next
        case (step c)
        then have snd_tuple_def: "(c, src et) \<in> inh (TG IG)"
          using src_et_not_name src_et_not_supertype
          by blast
        then have "c \<in> NT (TG IG)"
          using assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node
          by fastforce
        then have c_neq_name: "c \<noteq> type (id_to_list name)"
          using name_not_in_tg
          by blast
        have "(type (id_to_list supertype), c) \<in> (inh (TG IG) \<union> 
          {(type (id_to_list name), type (id_to_list name)), 
          (type (id_to_list name), type (id_to_list supertype))})\<^sup>+ \<or> c = type (id_to_list name)"
          using step(1)
        proof (induct)
          case (base y)
          then have "y = type (id_to_list name) \<or> y = type (id_to_list supertype)"
            using name_inherits_supertype
            by simp
          then show ?case
            using supertype_refl 
            by blast
        next
          case (step y z)
          then show ?case
          proof (elim disjE)
            assume "(LabDef.type (id_to_list supertype), y) \<in> 
              (inh (TG IG) \<union> {(LabDef.type (id_to_list name), LabDef.type (id_to_list name)), (LabDef.type (id_to_list name), LabDef.type (id_to_list supertype))})\<^sup>+"
            then show ?thesis
              using step.hyps(2) trancl.trancl_into_trancl
              by force
          next
            assume "y = LabDef.type (id_to_list name)"
            then show ?thesis
              using name_inherits_supertype step.hyps(2) supertype_refl type_n_is_name
              by fastforce
          qed
        qed
        then have "(type (id_to_list supertype), c) \<in> (inh (TG IG) \<union> 
          {(type (id_to_list name), type (id_to_list name)), 
          (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
          using c_neq_name
          by blast
        then have "(type (id_to_list supertype), src et) \<in> (inh (TG IG) \<union> 
          {(type (id_to_list name), type (id_to_list name)), 
          (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
          using snd_tuple_def
          by (simp add: trancl.trancl_into_trancl)
        then show ?thesis
          using no_supertype_inh
          by blast
      qed
    qed
    then show ?thesis
      using inh_def
      by blast
  qed
next
  have name_not_in_tg: "type (id_to_list name) \<notin> NT (TG IG)"
    using Int_insert_right_if1 doubleton_eq_iff id_to_list_inverse insert_absorb2 unlabel.simps(1) combined_type name_supertype_neq
    by metis
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  then have tgt_et_def: "tgt et \<in> NT (TG IG)"
    using assms(1) instance_graph.validity_type_graph type_graph.structure_edges_wellformed_alt
    by blast
  then have tgt_et_not_name: "tgt et \<noteq> type (id_to_list name)"
    using name_not_in_tg
    by fastforce
  have tgt_et_not_supertype: "tgt et \<noteq> type (id_to_list supertype)"
    using no_tgt_edge_types tgt_et_def assms(1) et_def instance_graph.validity_type_graph type_graph.validity_inh_node
    by metis
  have no_supertype_inh: "(type (id_to_list supertype), tgt et) \<notin> (inh (TG IG) \<union> 
    {(type (id_to_list name), type (id_to_list name)), 
    (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
  proof
    assume "(type (id_to_list supertype), tgt et) \<in> (inh (TG IG) \<union> 
      {(type (id_to_list name), type (id_to_list name)), 
      (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
    then show "False"
    proof (cases)
      case base
      then have "(LabDef.type (id_to_list supertype), tgt et) \<in> inh (TG IG)"
        using Pair_inject tgt_et_not_name
        by auto
      then show ?thesis
        using et_def no_tgt_edge_types
        by blast
    next
      case (step c)
      have "(LabDef.type (id_to_list supertype), c) \<in> (inh (TG IG))\<^sup>+"
        using step(1)
      proof (induct)
        case (base y)
        then show ?case
          using combined_type insertE name_not_in_tg
          by fastforce
      next
        case (step y z)
        then have "y \<in> NT (TG IG)"
          using assms(1) instance_graph.validity_type_graph trancl.simps type_graph.structure_inheritance_wellformed_second_node
          by metis
        then have "y \<noteq> type (id_to_list name)"
          using name_not_in_tg
          by blast
        then have "(y, z) \<in> inh (TG IG)"
          using step.hyps
          by simp
        then show ?case
          using step.hyps(3)
          by simp
      qed
      then have fst_tuple_def: "(LabDef.type (id_to_list supertype), c) \<in> inh (TG IG)"
        using assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans
        by fastforce
      then have "c \<in> NT (TG IG)"
        using assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_second_node
        by metis
      then have "c \<noteq> type (id_to_list name)"
        using name_not_in_tg
        by blast
      then have "(c, tgt et) \<in> inh (TG IG)"
        using step(2)
        by simp
      then show ?thesis
        using transE fst_tuple_def et_def no_tgt_edge_types assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans
        by metis
    qed
  qed
  assume "n \<in> N IG \<union> N (ig_subclass_as_node_type name supertype objects fid)"
  then have n_def: "n \<in> N IG \<union> typed (type (id_to_list name)) ` objects"
    by (simp add: ig_subclass_as_node_type_def)
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (TG (ig_subclass_as_node_type name supertype objects fid)))\<^sup>+"
  then have inh_unfold_def: "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> 
    {(type (id_to_list name), type (id_to_list name)), 
    (type (id_to_list supertype), type (id_to_list supertype)), 
    (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
    unfolding ig_subclass_as_node_type_def tg_subclass_as_node_type_def
    by simp
  have supertype_refl: "(type (id_to_list supertype), type (id_to_list supertype)) \<in> inh (TG IG)"
    using assms(1) combined_type instance_graph.validity_type_graph type_graph.validity_inh_node
    by fastforce
  then have inh_def: "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> 
    {(type (id_to_list name), type (id_to_list name)), 
    (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
    using inh_unfold_def
    by (simp add: insert_absorb)
  show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG) et)"
    using n_def
  proof (elim UnE)
    assume n_in_ig: "n \<in> N IG"
    then have type_n_not_name: "type\<^sub>n n \<noteq> type (id_to_list name)"
      using IntI Un_insert_left Un_insert_right assms(1) combined_type id_to_list_inverse insertI1 
      using instance_graph.validity_node_typed name_supertype_neq singletonD sup_bot.right_neutral unlabel.simps(1)
      by metis
    have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG))\<^sup>+"
      using inh_def
    proof (cases)
      case base
      then show ?thesis
        using type_n_not_name
        by simp
    next
      case (step c)
      have fst_tuple_def: "(type\<^sub>n n, c) \<in> (inh (TG IG))\<^sup>+"
        using step(1)
      proof (induct)
        case (base y)
        then show ?case
          using type_n_not_name
          by simp
      next
        case (step y z)
        then have "y \<in> NT (TG IG)"
          using assms(1) instance_graph.validity_type_graph trancl.simps type_graph.structure_inheritance_wellformed_second_node
          by metis
        then have "y \<noteq> type (id_to_list name)"
          using name_not_in_tg
          by blast
        then have "(y, z) \<in> inh (TG IG)"
          using step.hyps
          by simp
        then show ?case
          using step.hyps(3)
          by simp
      qed
      then have "c \<in> NT (TG IG)"
        using assms(1) instance_graph.validity_type_graph trancl.simps type_graph.structure_inheritance_wellformed_second_node
        by metis
      then have "c \<noteq> type (id_to_list name)"
        using name_not_in_tg
        by blast
      then have "(c, tgt et) \<in> inh (TG IG)"
        using step(2)
        by simp
      then show ?thesis
        using fst_tuple_def
        by simp
    qed
    then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG)"
      using assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans
      by fastforce
    then show ?thesis
      using assms(1) instance_graph.validity_ingoing_mult n_in_ig et_def
      by blast
  next
    assume n_in_typed: "n \<in> typed (LabDef.type (id_to_list name)) ` objects"
    then have type_n_is_name: "type\<^sub>n n = type (id_to_list name)"
      by fastforce
    have name_inherits_supertype: "\<And>x. (type\<^sub>n n, x) \<in> (inh (TG IG) \<union> 
      {(type (id_to_list name), type (id_to_list name)), 
      (type (id_to_list name), type (id_to_list supertype))}) \<Longrightarrow> 
      x = type (id_to_list name) \<or> x = type (id_to_list supertype)"
    proof-
      fix x
      assume "(type\<^sub>n n, x) \<in> (inh (TG IG) \<union> 
        {(type (id_to_list name), type (id_to_list name)), 
        (type (id_to_list name), type (id_to_list supertype))})"
      then show "x = type (id_to_list name) \<or> x = type (id_to_list supertype)"
      proof (elim UnE)
        assume "(type\<^sub>n n, x) \<in> inh (TG IG)"
        then have "type\<^sub>n n \<in> NT (TG IG)"
          by (simp add: assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node)
        then show ?thesis
          using name_not_in_tg type_n_is_name
          by simp
      next
        assume "(type\<^sub>n n, x) \<in> {(type (id_to_list name), type (id_to_list name)), (type (id_to_list name), type (id_to_list supertype))}"
        then show ?thesis
          by blast
      qed
    qed
    have "(type\<^sub>n n, tgt et) \<notin> (inh (TG IG) \<union> 
      {(type (id_to_list name), type (id_to_list name)), 
      (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
    proof
      assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> 
        {(type (id_to_list name), type (id_to_list name)), 
        (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
      then show "False"
      proof (cases)
        case base
        then have "(type\<^sub>n n, tgt et) \<in> {(LabDef.type (id_to_list name), LabDef.type (id_to_list name)), (LabDef.type (id_to_list name), LabDef.type (id_to_list supertype))}"
          using assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node trancl.simps type_n_is_name name_not_in_tg
          by fastforce
        then show ?thesis
          using tgt_et_not_name tgt_et_not_supertype
          by blast
      next
        case (step c)
        then have snd_tuple_def: "(c, tgt et) \<in> inh (TG IG)"
          using tgt_et_not_name tgt_et_not_supertype
          by blast
        then have "c \<in> NT (TG IG)"
          using assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node
          by fastforce
        then have c_neq_name: "c \<noteq> type (id_to_list name)"
          using name_not_in_tg
          by blast
        have "(type (id_to_list supertype), c) \<in> (inh (TG IG) \<union> 
          {(type (id_to_list name), type (id_to_list name)), 
          (type (id_to_list name), type (id_to_list supertype))})\<^sup>+ \<or> c = type (id_to_list name)"
          using step(1)
        proof (induct)
          case (base y)
          then have "y = type (id_to_list name) \<or> y = type (id_to_list supertype)"
            using name_inherits_supertype
            by simp
          then show ?case
            using supertype_refl 
            by blast
        next
          case (step y z)
          then show ?case
          proof (elim disjE)
            assume "(LabDef.type (id_to_list supertype), y) \<in> 
              (inh (TG IG) \<union> {(LabDef.type (id_to_list name), LabDef.type (id_to_list name)), (LabDef.type (id_to_list name), LabDef.type (id_to_list supertype))})\<^sup>+"
            then show ?thesis
              using step.hyps(2) trancl.trancl_into_trancl
              by force
          next
            assume "y = LabDef.type (id_to_list name)"
            then show ?thesis
              using name_inherits_supertype step.hyps(2) supertype_refl type_n_is_name
              by fastforce
          qed
        qed
        then have "(type (id_to_list supertype), c) \<in> (inh (TG IG) \<union> 
          {(type (id_to_list name), type (id_to_list name)), 
          (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
          using c_neq_name
          by blast
        then have "(type (id_to_list supertype), tgt et) \<in> (inh (TG IG) \<union> 
          {(type (id_to_list name), type (id_to_list name)), 
          (type (id_to_list name), type (id_to_list supertype))})\<^sup>+"
          using snd_tuple_def
          by (simp add: trancl.trancl_into_trancl)
        then show ?thesis
          using no_supertype_inh
          by blast
      qed
    qed
    then show ?thesis
      using inh_def
      by blast
  qed
qed (simp_all add: ig_subclass_as_node_type_def tg_subclass_as_node_type_def assms)


subsection "Transformation functions"

definition imod_subclass_to_ig_subclass_as_node_type :: "'t Id \<Rightarrow> 't Id \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "imod_subclass_to_ig_subclass_as_node_type name supertype fid Imod = \<lparr>
    TG = tg_subclass_as_node_type name supertype,
    Id = fid ` Object Imod,
    N = typed (type (id_to_list name)) ` Object Imod,
    E = {},
    ident = (\<lambda>x. if x \<in> fid ` Object Imod then typed (type (id_to_list name)) (THE y. fid y = x) else undefined)
  \<rparr>"

lemma imod_subclass_to_ig_subclass_as_node_type_proj:
  shows "imod_subclass_to_ig_subclass_as_node_type name supertype fid (imod_subclass name supertype objects fid) = ig_subclass_as_node_type name supertype objects fid"
  unfolding imod_subclass_to_ig_subclass_as_node_type_def ig_subclass_as_node_type_def imod_subclass_def
  by simp

lemma imod_subclass_to_ig_subclass_as_node_type_func:
  shows "ig_combine_mapping_function (imod_subclass_to_ig_subclass_as_node_type name supertype fid) (imod_subclass name supertype objects fid) (ig_subclass_as_node_type name supertype objects fid)"
  by (intro ig_combine_mapping_function.intro)
    (auto simp add: imod_subclass_to_ig_subclass_as_node_type_def imod_subclass_def ig_subclass_as_node_type_def imod_combine_def)

definition ig_subclass_as_node_type_to_imod_subclass :: "'t Id \<Rightarrow> 't Id \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't list, 't) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "ig_subclass_as_node_type_to_imod_subclass name supertype fid IG = \<lparr>
    Tm = tmod_subclass name supertype,
    Object = nodeId ` N IG,
    ObjectClass = (\<lambda>x. if x \<in> nodeId ` N IG then name else undefined),
    ObjectId = (\<lambda>x. if x \<in> nodeId ` N IG then fid x else undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_subclass_as_node_type_to_imod_subclass_proj:
  shows "ig_subclass_as_node_type_to_imod_subclass name supertype fid (ig_subclass_as_node_type name supertype objects fid) = imod_subclass name supertype objects fid"
proof-
  have "nodeId ` typed (LabDef.type (id_to_list name)) ` objects = objects"
    by force
  then show "ig_subclass_as_node_type_to_imod_subclass name supertype fid (ig_subclass_as_node_type name supertype objects fid) = imod_subclass name supertype objects fid"
    unfolding ig_subclass_as_node_type_to_imod_subclass_def imod_subclass_def ig_subclass_as_node_type_def
    by simp
qed

lemma ig_subclass_as_node_type_to_imod_subclass_func:
  shows "imod_combine_mapping_function (ig_subclass_as_node_type_to_imod_subclass name supertype fid) (ig_subclass_as_node_type name supertype objects fid) (imod_subclass name supertype objects fid)"
proof-
  have "nodeId ` typed (LabDef.type (id_to_list name)) ` objects = objects"
    by force
  then show "imod_combine_mapping_function (ig_subclass_as_node_type_to_imod_subclass name supertype fid) (ig_subclass_as_node_type name supertype objects fid) (imod_subclass name supertype objects fid)"
    by (intro imod_combine_mapping_function.intro)
      (auto simp add: ig_subclass_as_node_type_to_imod_subclass_def imod_subclass_def ig_subclass_as_node_type_def ig_combine_def)
qed

end