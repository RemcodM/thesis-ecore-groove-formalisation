theory ClassInstance
  imports
    Main
    "Ecore-GROOVE-Mapping.Instance_Model_Graph_Mapping"
    ClassType
begin

section "Definition of an instance model which introduces an object typed by a regular class"

definition imod_class :: "'t Id \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't) instance_model" where
  "imod_class name objects fid = \<lparr>
    Tm = tmod_class name,
    Object = objects,
    ObjectClass = (\<lambda>x. if x \<in> objects then name else undefined),
    ObjectId = (\<lambda>x. if x \<in> objects then fid x else undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_class_correct: 
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> o2 \<in> objects \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  shows "instance_model (imod_class name objects fid)"
proof (intro instance_model.intro)
  show "type_model (Tm (imod_class name objects fid))"
    unfolding imod_class_def
    using tmod_class_correct
    by simp
qed (simp_all add: assms imod_class_def tmod_class_def)

lemma imod_class_combine_correct:
  assumes "instance_model Imod"
  assumes new_class: "name \<notin> Class (Tm Imod) \<union> Enum (Tm Imod) \<union> UserDataType (Tm Imod)"
  assumes valid_identifier: "\<And>x. x \<in> Class (Tm Imod) \<union> Enum (Tm Imod) \<union> UserDataType (Tm Imod) \<Longrightarrow> \<not>id_in_ns name (Identifier x) \<and> \<not>id_in_ns x (Identifier name)"
  assumes new_objects: "objects \<inter> Object Imod = {}"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> o2 \<in> objects \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  assumes new_ids: "\<And>o1 o2. o1 \<in> Object Imod \<Longrightarrow> o2 \<in> objects \<Longrightarrow> ObjectId Imod o1 \<noteq> fid o2"
  shows "instance_model (imod_combine Imod (imod_class name objects fid))"
proof (intro imod_combine_distinct_correct)
  show "instance_model (imod_class name objects fid)"
    using unique_ids
    by (fact imod_class_correct)
next
  show "Class (Tm Imod) \<inter> Class (Tm (imod_class name objects fid)) = {}"
    unfolding imod_class_def tmod_class_def
    using new_class
    by simp
next
  fix ob
  assume "ob \<in> Object Imod"
  then have ob_not_in_objects: "ob \<notin> Object (imod_class name objects fid)"
    unfolding imod_class_def
    using new_objects
    by fastforce
  assume "ob \<in> Object (imod_class name objects fid)"
  then show "ObjectClass Imod ob = ObjectClass (imod_class name objects fid) ob"
    using ob_not_in_objects
    by blast
next
  fix o1 o2
  assume o1_def: "o1 \<in> Object Imod - Object (imod_class name objects fid)"
  assume "o2 \<in> Object (imod_class name objects fid) - Object Imod"
  then have o2_def: "o2 \<in> objects"
    unfolding imod_class_def
    by simp
  then have "ObjectId Imod o1 \<noteq> fid o2"
    using new_ids o1_def
    by simp
  then show "ObjectId Imod o1 \<noteq> ObjectId (imod_class name objects fid) o2"
    unfolding imod_class_def
    by (simp add: o2_def)
next
  have "type_model (tmod_combine (Tm Imod) (tmod_class name))"
    using tmod_class_combine_correct assms(1) instance_model.validity_type_model_consistent new_class valid_identifier
    by blast
  then show "type_model (tmod_combine (Tm Imod) (Tm (imod_class name objects fid)))"
    unfolding imod_class_def
    by simp
qed (simp_all add: assms imod_class_def tmod_class_def)



section "Encoding of a Class as Node Type in GROOVE"

definition ig_class_as_node_type :: "'t Id \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "ig_class_as_node_type name objects fid = \<lparr>
    TG = tg_class_as_node_type name,
    Id = fid ` objects,
    N = typed (type (id_to_list name)) ` objects,
    E = {},
    ident = (\<lambda>x. if x \<in> fid ` objects then typed (type (id_to_list name)) (THE y. fid y = x) else undefined)
  \<rparr>"

lemma ig_class_as_node_type_correct: 
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  shows "instance_graph (ig_class_as_node_type name objects fid)"
proof (intro instance_graph.intro)
  fix n
  assume "n \<in> N (ig_class_as_node_type name objects fid)"
  then have "n \<in> typed (type (id_to_list name)) ` objects"
    unfolding ig_class_as_node_type_def
    by simp
  then have "n \<in> Node\<^sub>t"
    using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
    by fastforce
  then show "n \<in> Node"
    unfolding Node_def
    by simp
next
  fix i
  assume "i \<in> Id (ig_class_as_node_type name objects fid)"
  then have i_in_id: "i \<in> fid ` objects"
    unfolding ig_class_as_node_type_def
    by simp
  then show "ident (ig_class_as_node_type name objects fid) i \<in> N (ig_class_as_node_type name objects fid) \<and> type\<^sub>n (ident (ig_class_as_node_type name objects fid) i) \<in> Lab\<^sub>t"
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
    then show "ident (ig_class_as_node_type name objects fid) i \<in> N (ig_class_as_node_type name objects fid)"
      unfolding ig_class_as_node_type_def
      using i_in_id
      by simp
  next
    have "type\<^sub>n (typed (type (id_to_list name)) (THE y. fid y = i)) = type (id_to_list name)"
      by simp
    then have "type\<^sub>n (typed (type (id_to_list name)) (THE y. fid y = i)) \<in> Lab\<^sub>t"
      by (simp add: Lab\<^sub>t.rule_type_labels)
    then show "type\<^sub>n (ident (ig_class_as_node_type name objects fid) i) \<in> Lab\<^sub>t"
      unfolding ig_class_as_node_type_def
      using i_in_id
      by simp
  qed
next
  show "type_graph (TG (ig_class_as_node_type name objects fid))"
    unfolding ig_class_as_node_type_def
    using tg_class_as_node_type_correct
    by simp
next
  fix n
  assume "n \<in> N (ig_class_as_node_type name objects fid)"
  then have "n \<in> typed (type (id_to_list name)) ` objects"
    unfolding ig_class_as_node_type_def
    by simp
  then have "type\<^sub>n n = type (id_to_list name)"
    by auto
  then show "type\<^sub>n n \<in> NT (TG (ig_class_as_node_type name objects fid))"
    unfolding ig_class_as_node_type_def tg_class_as_node_type_def
    by simp
next
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj (ig_class_as_node_type name objects fid)) p"
    unfolding ig_class_as_node_type_def instance_graph_containment_proj_def pre_digraph.cycle_def pre_digraph.awalk_def
    by simp
qed (simp_all add: assms ig_class_as_node_type_def tg_class_as_node_type_def)

lemma ig_class_as_node_type_combine_correct:
  assumes "instance_graph IG"
  assumes new_node_type: "type (id_to_list name) \<notin> NT (TG IG)"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> objects \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  assumes new_ids: "Id IG \<inter> fid ` objects = {}"
  shows "instance_graph (ig_combine IG (ig_class_as_node_type name objects fid))"
proof (intro ig_combine_distinct_correct)
  show "instance_graph (ig_class_as_node_type name objects fid)"
    using unique_ids
    by (fact ig_class_as_node_type_correct)
next
  fix i
  assume "i \<in> Id IG"
  then have i_not_in_ids: "i \<notin> fid ` objects"
    using new_ids
    by auto
  assume "i \<in> Id (ig_class_as_node_type name objects fid)"
  then have "i \<in> fid ` objects"
    unfolding ig_class_as_node_type_def
    by simp
  then show "ident IG i = ident (ig_class_as_node_type name objects fid) i"
    using i_not_in_ids
    by blast
qed (simp_all add: ig_class_as_node_type_def tg_class_as_node_type_def assms)


subsection "Transformation functions"

definition imod_class_to_ig_class_as_node_type :: "'t Id \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "imod_class_to_ig_class_as_node_type name fid Imod = \<lparr>
    TG = tg_class_as_node_type name,
    Id = fid ` Object Imod,
    N = typed (type (id_to_list name)) ` Object Imod,
    E = {},
    ident = (\<lambda>x. if x \<in> fid ` Object Imod then typed (type (id_to_list name)) (THE y. fid y = x) else undefined)
  \<rparr>"

lemma imod_class_to_ig_class_as_node_type_proj:
  shows "imod_class_to_ig_class_as_node_type name fid (imod_class name objects fid) = ig_class_as_node_type name objects fid"
  unfolding imod_class_to_ig_class_as_node_type_def ig_class_as_node_type_def imod_class_def
  by simp

lemma imod_class_to_ig_class_as_node_type_func:
  shows "ig_combine_mapping_function (imod_class_to_ig_class_as_node_type name fid) (imod_class name objects fid) (ig_class_as_node_type name objects fid)"
  by (intro ig_combine_mapping_function.intro)
    (auto simp add: imod_class_to_ig_class_as_node_type_def imod_class_def ig_class_as_node_type_def imod_combine_def)

definition ig_class_as_node_type_to_imod_class :: "'t Id \<Rightarrow> ('o \<Rightarrow> 't) \<Rightarrow> ('o, 't list, 't) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "ig_class_as_node_type_to_imod_class name fid IG = \<lparr>
    Tm = tmod_class name,
    Object = nodeId ` N IG,
    ObjectClass = (\<lambda>x. if x \<in> nodeId ` N IG then name else undefined),
    ObjectId = (\<lambda>x. if x \<in> nodeId ` N IG then fid x else undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_class_as_node_type_to_imod_class_proj:
  shows "ig_class_as_node_type_to_imod_class name fid (ig_class_as_node_type name objects fid) = imod_class name objects fid"
proof-
  have "nodeId ` typed (LabDef.type (id_to_list name)) ` objects = objects"
    by force
  then show "ig_class_as_node_type_to_imod_class name fid (ig_class_as_node_type name objects fid) = imod_class name objects fid"
    unfolding ig_class_as_node_type_to_imod_class_def imod_class_def ig_class_as_node_type_def
    by simp
qed

lemma ig_class_as_node_type_to_imod_class_func:
  shows "imod_combine_mapping_function (ig_class_as_node_type_to_imod_class name fid) (ig_class_as_node_type name objects fid) (imod_class name objects fid)"
proof-
  have "nodeId ` typed (LabDef.type (id_to_list name)) ` objects = objects"
    by force
  then show "imod_combine_mapping_function (ig_class_as_node_type_to_imod_class name fid) (ig_class_as_node_type name objects fid) (imod_class name objects fid)"
    by (intro imod_combine_mapping_function.intro)
      (auto simp add: ig_class_as_node_type_to_imod_class_def imod_class_def ig_class_as_node_type_def ig_combine_def)
qed

end