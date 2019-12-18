theory UserDataTypeInstance
  imports
    Main
    "Ecore-GROOVE-Mapping.Instance_Model_Graph_Mapping"
    UserDataTypeType
begin

section "Definition of an instance model belonging to the introduction of an user defined data type"

definition imod_userdatatype :: "'t Id \<Rightarrow> ('o, 't) instance_model" where
  "imod_userdatatype name = \<lparr>
    Tm = tmod_userdatatype name,
    Object = {},
    ObjectClass = (\<lambda>x. undefined),
    ObjectId = (\<lambda>x. undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_userdatatype_correct: "instance_model (imod_userdatatype name)"
proof (intro imod_empty_any_type_model_correct)
  show "type_model (Tm (imod_userdatatype name))"
    unfolding imod_userdatatype_def
    using tmod_userdatatype_correct
    by simp
qed (simp_all add: imod_userdatatype_def tmod_userdatatype_def)

lemma imod_userdatatype_combine_correct:
  assumes "instance_model Imod"
  assumes new_userdatatype: "name \<notin> Class (Tm Imod) \<union> Enum (Tm Imod) \<union> UserDataType (Tm Imod)"
  assumes valid_identifier: "\<And>x. x \<in> Class (Tm Imod) \<union> Enum (Tm Imod) \<union> UserDataType (Tm Imod) \<Longrightarrow> \<not>id_in_ns name (Identifier x) \<and> \<not>id_in_ns x (Identifier name)"
  shows "instance_model (imod_combine Imod (imod_userdatatype name))"
proof (intro imod_combine_distinct_correct)
  show "instance_model (imod_userdatatype name)"
    by (fact imod_userdatatype_correct)
next
  show "type_model (tmod_combine (Tm Imod) (Tm (imod_userdatatype name)))"
    unfolding imod_userdatatype_def
    using assms instance_model.select_convs(1) instance_model.validity_type_model_consistent tmod_userdatatype_combine_correct
    by metis
next
  show "UserDataType (Tm Imod) \<inter> UserDataType (Tm (imod_userdatatype name)) = {}"
    unfolding imod_userdatatype_def tmod_userdatatype_def
    using new_userdatatype
    by simp
qed (simp_all add: assms imod_userdatatype_def tmod_userdatatype_def)



section "Encoding of an user defined data type as Node Type in GROOVE"

definition ig_userdatatype_as_node_type :: "'t Id \<Rightarrow> 't \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "ig_userdatatype_as_node_type name data_edge = \<lparr>
    TG = tg_userdatatype_as_node_type name data_edge,
    Id = {},
    N = {},
    E = {},
    ident = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_userdatatype_as_node_type_correct: "instance_graph (ig_userdatatype_as_node_type name data_edge)"
proof (intro ig_empty_any_type_graph_correct)
  show "type_graph (TG (ig_userdatatype_as_node_type name data_edge))"
    unfolding ig_userdatatype_as_node_type_def
    using tg_userdatatype_as_node_type_correct
    by simp
qed (simp_all add: ig_userdatatype_as_node_type_def tg_userdatatype_as_node_type_def)

lemma ig_userdatatype_as_node_type_combine_correct:
  assumes "instance_graph IG"
  assumes combined_node_types: "NT (TG IG) \<inter> {type (id_to_list name), LabDef.string} \<subseteq> {LabDef.string}"
  shows "instance_graph (ig_combine IG (ig_userdatatype_as_node_type name data_edge))"
proof (intro ig_combine_merge_no_containment_imod2_correct)
  show "instance_graph (ig_userdatatype_as_node_type name data_edge)"
    by (fact ig_userdatatype_as_node_type_correct)
next
  show "ET (TG IG) \<inter> ET (TG (ig_userdatatype_as_node_type name data_edge)) = {}"
    unfolding ig_userdatatype_as_node_type_def tg_userdatatype_as_node_type_def
    using assms instance_graph.validity_type_graph type_graph.structure_edges_wellformed_src_node
    by fastforce
next
  have "type_graph (tg_combine (TG IG) (tg_userdatatype_as_node_type name data_edge))"
    using assms
    by (simp add: tg_userdatatype_as_node_type_combine_correct instance_graph.validity_type_graph)
  then show "type_graph (tg_combine (TG IG) (TG (ig_userdatatype_as_node_type name data_edge)))"
    unfolding ig_userdatatype_as_node_type_def
    by simp
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_userdatatype_as_node_type name data_edge)"
  then have n_def: "n \<in> N IG"
    unfolding ig_userdatatype_as_node_type_def
    by simp
  then have type_n_def: "type\<^sub>n n \<in> NT (TG IG)"
    using assms(1) instance_graph.validity_node_typed
    by blast
  then have type_n_not_name: "type\<^sub>n n \<noteq> type (id_to_list name)"
    using combined_node_types
    by fastforce
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_userdatatype_as_node_type name data_edge)))\<^sup>+"
  then have inh_unfold_def: "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> {(type (id_to_list name), type (id_to_list name)), (LabDef.string, LabDef.string)})\<^sup>+"
    unfolding ig_userdatatype_as_node_type_def tg_userdatatype_as_node_type_def
    by simp
  show "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG) et)"
  proof (induct "LabDef.string \<in> NT (TG IG)")
    case True
    then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> {(type (id_to_list name), type (id_to_list name))})\<^sup>+"
      using IntD2 Un_insert_right inf_sup_absorb insert_absorb
      using inh_unfold_def assms(1) instance_graph.validity_type_graph type_graph.validity_inh_node
      by metis
    then have "(type\<^sub>n n, src et) \<in> (inh (TG IG))\<^sup>+"
    proof (induct)
      case (base y)
      then show ?case
        using type_n_not_name
        by blast
    next
      case (step y z)
      then have "y \<in> NT (TG IG)"
        by (simp add: assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_second_node type_graph.validity_inh_trans)
      then have "y \<noteq> type (id_to_list name)"
        using combined_node_types
        by blast
      then have "(y, z) \<in> inh (TG IG)"
        using step.hyps(2)
        by blast
      then show ?case
        using step.hyps(3)
        by simp
    qed
    then have "(type\<^sub>n n, src et) \<in> inh (TG IG)"
      by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
    then show ?case
      using assms(1) instance_graph.validity_outgoing_mult et_def n_def
      by blast
  next
    case False
    then have combined_node_types_empty: "NT (TG IG) \<inter> {type (id_to_list name), LabDef.string} = {}"
      using combined_node_types
      by blast
    then have type_n_not_string: "type\<^sub>n n \<noteq> LabDef.string"
      using type_n_def
      by blast
    have "(type\<^sub>n n, src et) \<in> (inh (TG IG))\<^sup>+"
      using inh_unfold_def
    proof (induct)
      case (base y)
      then show ?case
        using type_n_not_name type_n_not_string
        by blast
    next
      case (step y z)
      then have "y \<in> NT (TG IG)"
        by (simp add: assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_second_node type_graph.validity_inh_trans)
      then have "y \<noteq> type (id_to_list name) \<and> y \<noteq> LabDef.string"
        using combined_node_types_empty
        by blast
      then have "(y, z) \<in> inh (TG IG)"
        using step.hyps(2)
        by blast
      then show ?case
        using step.hyps(3)
        by simp
    qed
    then have "(type\<^sub>n n, src et) \<in> inh (TG IG)"
      by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
    then show ?case
      using assms(1) instance_graph.validity_outgoing_mult et_def n_def
      by blast
  qed
next
  fix et n
  assume "et \<in> ET (TG (ig_userdatatype_as_node_type name data_edge))"
  then have et_def: "et = (type (id_to_list name), LabDef.edge [data_edge], LabDef.string)"
    unfolding ig_userdatatype_as_node_type_def tg_userdatatype_as_node_type_def
    by simp
  then have src_et_def: "src et = type (id_to_list name)"
    by simp
  assume "n \<in> N IG \<union> N (ig_userdatatype_as_node_type name data_edge)"
  then have n_def: "n \<in> N IG"
    unfolding ig_userdatatype_as_node_type_def
    by simp
  then have type_n_def: "type\<^sub>n n \<in> NT (TG IG)"
    using assms(1) instance_graph.validity_node_typed
    by blast
  then have type_n_not_name: "type\<^sub>n n \<noteq> type (id_to_list name)"
    using combined_node_types
    by fastforce
  have no_inh: "(type\<^sub>n n, src et) \<notin> (inh (TG IG) \<union> {(type (id_to_list name), type (id_to_list name)), (LabDef.string, LabDef.string)})\<^sup>+"
  proof
    assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> {(LabDef.type (id_to_list name), LabDef.type (id_to_list name)), (LabDef.string, LabDef.string)})\<^sup>+"
    then show "False"
    proof (cases)
      case base
      then have "(type\<^sub>n n, src et) = (type (id_to_list name), type (id_to_list name))"
        using src_et_def assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_second_node_alt combined_node_types
        by fastforce
      then show ?thesis
        using type_n_not_name
        by blast
    next
      case (step c)
      then have "(c, src et) = (type (id_to_list name), type (id_to_list name))"
        using src_et_def assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_second_node_alt combined_node_types
        by fastforce
      then have c_def: "c = type (id_to_list name)"
        by simp
      have "(inh (TG IG) \<union> {(LabDef.type (id_to_list name), LabDef.type (id_to_list name)), (LabDef.string, LabDef.string)})\<^sup>+ = 
        inh (TG IG) \<union> {(LabDef.type (id_to_list name), LabDef.type (id_to_list name)), (LabDef.string, LabDef.string)}"
        using assms(1) instance_graph.validity_type_graph tg_userdatatype_as_node_type_combine_inh tg_userdatatype_as_node_type_def type_graph.select_convs(3)
        by metis
      then have "(type\<^sub>n n, c) = (LabDef.type (id_to_list name), LabDef.type (id_to_list name))"
        using step(1) c_def assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_second_node_alt combined_node_types
        by fastforce
      then show ?thesis
        using type_n_not_name
        by blast
    qed
  qed
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh (TG (ig_userdatatype_as_node_type name data_edge)))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> {(type (id_to_list name), type (id_to_list name)), (LabDef.string, LabDef.string)})\<^sup>+"
    unfolding ig_userdatatype_as_node_type_def tg_userdatatype_as_node_type_def
    by simp
  then show "card {e \<in> E (ig_userdatatype_as_node_type name data_edge). src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG (ig_userdatatype_as_node_type name data_edge)) et)"
    using no_inh
    by blast
next
  fix et n
  assume et_def: "et \<in> ET (TG IG)"
  assume "n \<in> N IG \<union> N (ig_userdatatype_as_node_type name data_edge)"
  then have n_def: "n \<in> N IG"
    unfolding ig_userdatatype_as_node_type_def
    by simp
  then have type_n_def: "type\<^sub>n n \<in> NT (TG IG)"
    using assms(1) instance_graph.validity_node_typed
    by blast
  then have type_n_not_name: "type\<^sub>n n \<noteq> type (id_to_list name)"
    using combined_node_types
    by fastforce
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh (TG (ig_userdatatype_as_node_type name data_edge)))\<^sup>+"
  then have inh_unfold_def: "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> {(type (id_to_list name), type (id_to_list name)), (LabDef.string, LabDef.string)})\<^sup>+"
    unfolding ig_userdatatype_as_node_type_def tg_userdatatype_as_node_type_def
    by simp
  show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG) et)"
  proof (induct "LabDef.string \<in> NT (TG IG)")
    case True
    then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> {(type (id_to_list name), type (id_to_list name))})\<^sup>+"
      using IntD2 Un_insert_right inf_sup_absorb insert_absorb
      using inh_unfold_def assms(1) instance_graph.validity_type_graph type_graph.validity_inh_node
      by metis
    then have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG))\<^sup>+"
    proof (induct)
      case (base y)
      then show ?case
        using type_n_not_name
        by blast
    next
      case (step y z)
      then have "y \<in> NT (TG IG)"
        by (simp add: assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_second_node type_graph.validity_inh_trans)
      then have "y \<noteq> type (id_to_list name)"
        using combined_node_types
        by blast
      then have "(y, z) \<in> inh (TG IG)"
        using step.hyps(2)
        by blast
      then show ?case
        using step.hyps(3)
        by simp
    qed
    then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG)"
      by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
    then show ?case
      using assms(1) instance_graph.validity_ingoing_mult et_def n_def
      by blast
  next
    case False
    then have combined_node_types_empty: "NT (TG IG) \<inter> {type (id_to_list name), LabDef.string} = {}"
      using combined_node_types
      by blast
    then have type_n_not_string: "type\<^sub>n n \<noteq> LabDef.string"
      using type_n_def
      by blast
    have "(type\<^sub>n n, tgt et) \<in> (inh (TG IG))\<^sup>+"
      using inh_unfold_def
    proof (induct)
      case (base y)
      then show ?case
        using type_n_not_name type_n_not_string
        by blast
    next
      case (step y z)
      then have "y \<in> NT (TG IG)"
        by (simp add: assms(1) instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_second_node type_graph.validity_inh_trans)
      then have "y \<noteq> type (id_to_list name) \<and> y \<noteq> LabDef.string"
        using combined_node_types_empty
        by blast
      then have "(y, z) \<in> inh (TG IG)"
        using step.hyps(2)
        by blast
      then show ?case
        using step.hyps(3)
        by simp
    qed
    then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG)"
      by (simp add: assms(1) instance_graph.validity_type_graph type_graph.validity_inh_trans)
    then show ?case
      using assms(1) instance_graph.validity_ingoing_mult et_def n_def
      by blast
  qed
qed (simp_all add: ig_userdatatype_as_node_type_def tg_userdatatype_as_node_type_def assms)


subsection "Transformation functions"

definition imod_userdatatype_to_ig_userdatatype_as_node_type :: "'t Id \<Rightarrow> 't \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "imod_userdatatype_to_ig_userdatatype_as_node_type name data_edge Imod = \<lparr>
    TG = tg_userdatatype_as_node_type name data_edge,
    Id = {},
    N = {},
    E = {},
    ident = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_userdatatype_to_ig_userdatatype_as_node_type_proj:
  shows "imod_userdatatype_to_ig_userdatatype_as_node_type name data_edge (imod_userdatatype name) = ig_userdatatype_as_node_type name data_edge"
  unfolding imod_userdatatype_to_ig_userdatatype_as_node_type_def ig_userdatatype_as_node_type_def imod_userdatatype_def
  by simp

lemma imod_userdatatype_to_ig_userdatatype_as_node_type_func:
  shows "ig_combine_mapping_function (imod_userdatatype_to_ig_userdatatype_as_node_type name data_edge) (imod_userdatatype name) (ig_userdatatype_as_node_type name data_edge)"
  by (intro ig_combine_mapping_function.intro)
    (simp_all add: imod_userdatatype_to_ig_userdatatype_as_node_type_def imod_userdatatype_def ig_userdatatype_as_node_type_def imod_combine_def)

definition ig_userdatatype_as_node_type_to_imod_userdatatype :: "'t Id \<Rightarrow> ('o, 't list, 't) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "ig_userdatatype_as_node_type_to_imod_userdatatype name IG = \<lparr>
    Tm = tmod_userdatatype name,
    Object = {},
    ObjectClass = (\<lambda>x. undefined),
    ObjectId = (\<lambda>x. undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_userdatatype_as_node_type_to_imod_userdatatype_proj:
  shows "ig_userdatatype_as_node_type_to_imod_userdatatype name (ig_userdatatype_as_node_type name data_edge) = imod_userdatatype name"
  unfolding ig_userdatatype_as_node_type_to_imod_userdatatype_def imod_userdatatype_def ig_userdatatype_as_node_type_def
  by simp

lemma ig_userdatatype_as_node_type_to_imod_userdatatype_func:
  shows "imod_combine_mapping_function (ig_userdatatype_as_node_type_to_imod_userdatatype name) (ig_userdatatype_as_node_type name data_edge) (imod_userdatatype name)"
  by (intro imod_combine_mapping_function.intro)
      (simp_all add: ig_userdatatype_as_node_type_to_imod_userdatatype_def imod_userdatatype_def ig_userdatatype_as_node_type_def ig_combine_def)

end