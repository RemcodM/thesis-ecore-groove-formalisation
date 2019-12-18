theory EnumInstance
  imports
    Main
    "Ecore-GROOVE-Mapping.Instance_Model_Graph_Mapping"
    EnumType
begin

section "Definition of an instance model which introduces values for an enumeration type"

definition imod_enum :: "'t Id \<Rightarrow> 't set \<Rightarrow> ('o, 't) instance_model" where
  "imod_enum name values = \<lparr>
    Tm = tmod_enum name values,
    Object = {},
    ObjectClass = (\<lambda>x. undefined),
    ObjectId = (\<lambda>x. undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_enum_correct: "instance_model (imod_enum name values)"
proof (intro imod_empty_any_type_model_correct)
  show "type_model (Tm (imod_enum name values))"
    unfolding imod_enum_def
    using tmod_enum_correct
    by simp
qed (simp_all add: imod_enum_def tmod_enum_def)

lemma imod_enum_combine_correct:
  assumes "instance_model Imod"
  assumes new_enum: "name \<notin> Class (Tm Imod) \<union> Enum (Tm Imod) \<union> UserDataType (Tm Imod)"
  assumes valid_identifier: "\<And>x. x \<in> Class (Tm Imod) \<union> Enum (Tm Imod) \<union> UserDataType (Tm Imod) \<Longrightarrow> \<not>id_in_ns name (Identifier x) \<and> \<not>id_in_ns x (Identifier name)"
  shows "instance_model (imod_combine Imod (imod_enum name values))"
proof (intro imod_combine_distinct_correct)
  show "instance_model (imod_enum name values)"
    by (fact imod_enum_correct)
next
  show "type_model (tmod_combine (Tm Imod) (Tm (imod_enum name values)))"
    unfolding imod_enum_def
    using assms instance_model.select_convs(1) instance_model.validity_type_model_consistent tmod_enum_combine_correct
    by metis
next
  show "Enum (Tm Imod) \<inter> Enum (Tm (imod_enum name values)) = {}"
    unfolding imod_enum_def tmod_enum_def
    using new_enum
    by simp
qed (simp_all add: assms imod_enum_def tmod_enum_def)



section "Encoding of an enumeration type as Node Type in GROOVE"

definition ig_enum_as_node_types :: "'t Id \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> ('t \<Rightarrow> 't) \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "ig_enum_as_node_types name values fob fid = \<lparr>
    TG = tg_enum_as_node_types name values,
    Id = fid ` values,
    N = (\<lambda>x. typed (type (id_to_list name @ [x])) (fob x)) ` values,
    E = {},
    ident = (\<lambda>x. if x \<in> fid ` values then typed (type (id_to_list name @ [(THE y. fid y = x)])) (fob (THE y. fid y = x)) else undefined)
  \<rparr>"

lemma ig_enum_as_node_types_correct:
  assumes unique_ids: "\<And>o1 o2. o1 \<in> values \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  assumes unique_obs: "\<And>o1 o2. o1 \<in> values \<Longrightarrow> fob o1 = fob o2 \<Longrightarrow> o1 = o2"
  shows "instance_graph (ig_enum_as_node_types name values fob fid)"
proof (intro instance_graph.intro)
  fix n
  assume "n \<in> N (ig_enum_as_node_types name values fob fid)"
  then have "n \<in> (\<lambda>x. typed (type (id_to_list name @ [x])) (fob x)) ` values"
    unfolding ig_enum_as_node_types_def
    by simp
  then have "n \<in> Node\<^sub>t"
    using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
    by fastforce
  then show "n \<in> Node"
    unfolding Node_def
    by simp
next
  fix i
  assume "i \<in> Id (ig_enum_as_node_types name values fob fid)"
  then have i_in_id: "i \<in> fid ` values"
    unfolding ig_enum_as_node_types_def
    by simp
  then show "ident (ig_enum_as_node_types name values fob fid) i \<in> N (ig_enum_as_node_types name values fob fid) \<and> type\<^sub>n (ident (ig_enum_as_node_types name values fob fid) i) \<in> Lab\<^sub>t"
  proof (intro conjI)
    assume "i \<in> fid ` values"
    then have "(THE y. fid y = i) \<in> values"
    proof
      fix x
      assume i_def: "i = fid x"
      assume x_is_value: "x \<in> values"
      have "(THE y. fid y = fid x) \<in> values"
      proof (rule the1I2)
        show "\<exists>!y. fid y = fid x"
          using unique_ids x_is_value
          by metis
      next
        fix y
        assume "fid y = fid x"
        then show "y \<in> values"
          using unique_ids x_is_value
          by metis
      qed
      then show "(THE y. fid y = i) \<in> values"
        by (simp add: i_def)
    qed
    then have "typed (type (id_to_list name @ [(THE y. fid y = i)])) (fob (THE y. fid y = i)) \<in> (\<lambda>x. typed (type (id_to_list name @ [x])) (fob x)) ` values"
      by simp
    then show "ident (ig_enum_as_node_types name values fob fid) i \<in> N (ig_enum_as_node_types name values fob fid)"
      unfolding ig_enum_as_node_types_def
      using i_in_id
      by simp
  next
    have "type\<^sub>n (typed (type (id_to_list name @ [(THE y. fid y = i)])) (fob (THE y. fid y = i))) \<in> Lab\<^sub>t"
      by (simp add: Lab\<^sub>t.rule_type_labels)
    then show "type\<^sub>n (ident (ig_enum_as_node_types name values fob fid) i) \<in> Lab\<^sub>t"
      unfolding ig_enum_as_node_types_def
      using i_in_id
      by simp
  qed
next
  show "type_graph (TG (ig_enum_as_node_types name values fob fid))"
    unfolding ig_enum_as_node_types_def
    using tg_enum_as_node_types_correct
    by simp
next
  fix n
  assume "n \<in> N (ig_enum_as_node_types name values fob fid)"
  then have "n \<in> (\<lambda>x. typed (type (id_to_list name @ [x])) (fob x)) ` values"
    unfolding ig_enum_as_node_types_def
    by simp
  then have "type\<^sub>n n \<in> (\<lambda>x. type (id_to_list name @ [x])) ` values"
    by fastforce
  then have type_n_def: "type\<^sub>n n \<in> type ` append (id_to_list name) ` (\<lambda>x. [x]) ` values"
    by blast
  then show "type\<^sub>n n \<in> NT (TG (ig_enum_as_node_types name values fob fid))"
    unfolding ig_enum_as_node_types_def tg_enum_as_node_types_def
    by simp
  show "type\<^sub>n n \<notin> type_graph.abs (TG (ig_enum_as_node_types name values fob fid))"
    unfolding ig_enum_as_node_types_def tg_enum_as_node_types_def
    using type_n_def
    by fastforce
next
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj (ig_enum_as_node_types name values fob fid)) p"
    unfolding ig_enum_as_node_types_def instance_graph_containment_proj_def pre_digraph.cycle_def pre_digraph.awalk_def
    by simp
qed (simp_all add: assms ig_enum_as_node_types_def tg_enum_as_node_types_def)

lemma ig_enum_as_node_types_combine_correct:
  assumes "instance_graph IG"
  assumes new_enum_type: "type (id_to_list name) \<notin> NT (TG IG)"
  assumes new_value_types: "NT (TG IG) \<inter> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values = {}"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> values \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  assumes unique_obs: "\<And>o1 o2. o1 \<in> values \<Longrightarrow> fob o1 = fob o2 \<Longrightarrow> o1 = o2"
  assumes new_ids: "Id IG \<inter> fid ` values = {}"
  shows "instance_graph (ig_combine IG (ig_enum_as_node_types name values fob fid))"
proof (intro ig_combine_distinct_correct)
  show "instance_graph (ig_enum_as_node_types name values fob fid)"
    using unique_ids unique_obs
    by (fact ig_enum_as_node_types_correct)
next
  fix i
  assume "i \<in> Id IG"
  then have i_not_in_ids: "i \<notin> fid ` values"
    using new_ids
    by auto
  assume "i \<in> Id (ig_enum_as_node_types name values fob fid)"
  then have "i \<in> fid ` values"
    unfolding ig_enum_as_node_types_def
    by simp
  then show "ident IG i = ident (ig_enum_as_node_types name values fob fid) i"
    using i_not_in_ids
    by blast
qed (simp_all add: ig_enum_as_node_types_def tg_enum_as_node_types_def assms)


subsection "Transformation functions"

definition imod_enum_to_ig_enum_as_node_types :: "'t Id \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> ('t \<Rightarrow> 't) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "imod_enum_to_ig_enum_as_node_types name values fob fid Imod = \<lparr>
    TG = tg_enum_as_node_types name values,
    Id = fid ` values,
    N = (\<lambda>x. typed (type (id_to_list name @ [x])) (fob x)) ` values,
    E = {},
    ident = (\<lambda>x. if x \<in> fid ` values then typed (type (id_to_list name @ [(THE y. fid y = x)])) (fob (THE y. fid y = x)) else undefined)
  \<rparr>"

lemma imod_enum_to_ig_enum_as_node_types_proj:
  shows "imod_enum_to_ig_enum_as_node_types name values fob fid (imod_enum name values) = ig_enum_as_node_types name values fob fid"
  unfolding imod_enum_to_ig_enum_as_node_types_def ig_enum_as_node_types_def imod_enum_def
  by simp

lemma imod_enum_to_ig_enum_as_node_types_func:
  shows "ig_combine_mapping_function (imod_enum_to_ig_enum_as_node_types name values fob fid) (imod_enum name values) (ig_enum_as_node_types name values fob fid)"
  by (intro ig_combine_mapping_function.intro)
    (auto simp add: imod_enum_to_ig_enum_as_node_types_def imod_enum_def ig_enum_as_node_types_def imod_combine_def)

definition ig_enum_as_node_types_to_imod_enum :: "'t Id \<Rightarrow> 't set \<Rightarrow> ('o, 't list, 't) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "ig_enum_as_node_types_to_imod_enum name values IG = \<lparr>
    Tm = tmod_enum name values,
    Object = {},
    ObjectClass = (\<lambda>x. undefined),
    ObjectId = (\<lambda>x. undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_enum_as_node_types_to_imod_enum_proj:
  shows "ig_enum_as_node_types_to_imod_enum name values (ig_enum_as_node_types name values fob fid) = imod_enum name values"
  unfolding ig_enum_as_node_types_to_imod_enum_def imod_enum_def ig_enum_as_node_types_def
  by simp

lemma ig_enum_as_node_types_to_imod_enum_func:
  shows "imod_combine_mapping_function (ig_enum_as_node_types_to_imod_enum name values) (ig_enum_as_node_types name values fob fid) (imod_enum name values)"
  by (intro imod_combine_mapping_function.intro)
    (simp_all add: ig_enum_as_node_types_to_imod_enum_def imod_enum_def ig_enum_as_node_types_def ig_combine_def)



section "Encoding of an enumeration type as flags in GROOVE"

definition ig_enum_as_flags :: "'t Id \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> ('t \<Rightarrow> 't) \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "ig_enum_as_flags name values fob fid = \<lparr>
    TG = tg_enum_as_flags name values,
    Id = fid ` values,
    N = typed (type (id_to_list name)) ` fob ` values,
    E = (\<lambda>x. (typed (type (id_to_list name)) (fob x), (type (id_to_list name), flag [x], type (id_to_list name)), typed (type (id_to_list name)) (fob x))) ` values,
    ident = (\<lambda>x. if x \<in> fid ` values then typed (type (id_to_list name)) (fob (THE y. fid y = x)) else undefined)
  \<rparr>"

lemma ig_enum_as_flags_correct:
  assumes unique_ids: "\<And>o1 o2. o1 \<in> values \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  assumes unique_obs: "\<And>o1 o2. o1 \<in> values \<Longrightarrow> fob o1 = fob o2 \<Longrightarrow> o1 = o2"
  shows "instance_graph (ig_enum_as_flags name values fob fid)"
proof (intro instance_graph.intro)
  fix n
  assume "n \<in> N (ig_enum_as_flags name values fob fid)"
  then have "n \<in> typed (type (id_to_list name)) ` fob ` values"
    unfolding ig_enum_as_flags_def
    by simp
  then have "n \<in> Node\<^sub>t"
    using Lab\<^sub>t.rule_type_labels Node\<^sub>t.rule_typed_nodes
    by fastforce
  then show "n \<in> Node"
    unfolding Node_def
    by simp
next
  fix s l t
  assume "(s, l, t) \<in> E (ig_enum_as_flags name values fob fid)"
  then have edge_def: "(s, l, t) \<in> (\<lambda>x. (typed (type (id_to_list name)) (fob x), (type (id_to_list name), flag [x], type (id_to_list name)), typed (type (id_to_list name)) (fob x))) ` values"
    unfolding ig_enum_as_flags_def
    by simp
  then have "s \<in> typed (type (id_to_list name)) ` fob ` values \<and>
    l \<in> (\<lambda>x. (type (id_to_list name), x, type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values \<and>
    t \<in> typed (type (id_to_list name)) ` fob ` values"
  proof (intro conjI)
    assume "(s, l, t) \<in> (\<lambda>x. (typed (type (id_to_list name)) (fob x), (type (id_to_list name), flag [x], type (id_to_list name)), typed (type (id_to_list name)) (fob x))) ` values"
    then show "s \<in> typed (LabDef.type (id_to_list name)) ` fob ` values"
      by fastforce
  next
    assume "(s, l, t) \<in> (\<lambda>x. (typed (type (id_to_list name)) (fob x), (type (id_to_list name), flag [x], type (id_to_list name)), typed (type (id_to_list name)) (fob x))) ` values"
    then show "l \<in> (\<lambda>x. (LabDef.type (id_to_list name), x, LabDef.type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values"
      by fastforce
  next
    assume "(s, l, t) \<in> (\<lambda>x. (typed (type (id_to_list name)) (fob x), (type (id_to_list name), flag [x], type (id_to_list name)), typed (type (id_to_list name)) (fob x))) ` values"
    then show "t \<in> typed (LabDef.type (id_to_list name)) ` fob ` values"
      by fastforce
  qed
  then show "s \<in> N (ig_enum_as_flags name values fob fid) \<and>
    l \<in> ET (TG (ig_enum_as_flags name values fob fid)) \<and> 
    t \<in> N (ig_enum_as_flags name values fob fid)"
    unfolding ig_enum_as_flags_def tg_enum_as_flags_def
    by simp
next
  fix i
  assume "i \<in> Id (ig_enum_as_flags name values fob fid)"
  then have i_in_id: "i \<in> fid ` values"
    unfolding ig_enum_as_flags_def
    by simp
  then show "ident (ig_enum_as_flags name values fob fid) i \<in> N (ig_enum_as_flags name values fob fid) \<and> type\<^sub>n (ident (ig_enum_as_flags name values fob fid) i) \<in> Lab\<^sub>t"
  proof (intro conjI)
    assume "i \<in> fid ` values"
    then have "(THE y. fid y = i) \<in> values"
    proof
      fix x
      assume i_def: "i = fid x"
      assume x_is_value: "x \<in> values"
      have "(THE y. fid y = fid x) \<in> values"
      proof (rule the1I2)
        show "\<exists>!y. fid y = fid x"
          using unique_ids x_is_value
          by metis
      next
        fix y
        assume "fid y = fid x"
        then show "y \<in> values"
          using unique_ids x_is_value
          by metis
      qed
      then show "(THE y. fid y = i) \<in> values"
        by (simp add: i_def)
    qed
    then have "typed (type (id_to_list name)) (fob (THE y. fid y = i)) \<in> typed (type (id_to_list name)) ` fob ` values"
      by simp
    then show "ident (ig_enum_as_flags name values fob fid) i \<in> N (ig_enum_as_flags name values fob fid)"
      unfolding ig_enum_as_flags_def
      using i_in_id
      by simp
  next
    have "type\<^sub>n (typed (type (id_to_list name)) (fob (THE y. fid y = i))) \<in> Lab\<^sub>t"
      by (simp add: Lab\<^sub>t.rule_type_labels)
    then show "type\<^sub>n (ident (ig_enum_as_flags name values fob fid) i) \<in> Lab\<^sub>t"
      unfolding ig_enum_as_flags_def
      using i_in_id
      by simp
  qed
next
  show "type_graph (TG (ig_enum_as_flags name values fob fid))"
    unfolding ig_enum_as_flags_def
    using tg_enum_as_flags_correct
    by simp
next
  fix e
  assume "e \<in> E (ig_enum_as_flags name values fob fid)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list name)) (fob x), (type (id_to_list name), flag [x], type (id_to_list name)), typed (type (id_to_list name)) (fob x))) ` values"
    unfolding ig_enum_as_flags_def
    by simp
  have type_n_def: "type\<^sub>n (src e) = type (id_to_list name)"
    using e_def
    by fastforce
  have type_e_def: "src (type\<^sub>e e) = type (id_to_list name)"
    using e_def
    by fastforce
  show "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG (ig_enum_as_flags name values fob fid))"
    unfolding ig_enum_as_flags_def tg_enum_as_flags_def
    using type_n_def type_e_def
    by simp
next
  fix e
  assume "e \<in> E (ig_enum_as_flags name values fob fid)"
  then have e_def: "e \<in> (\<lambda>x. (typed (type (id_to_list name)) (fob x), (type (id_to_list name), flag [x], type (id_to_list name)), typed (type (id_to_list name)) (fob x))) ` values"
    unfolding ig_enum_as_flags_def
    by simp
  have type_n_def: "type\<^sub>n (tgt e) = type (id_to_list name)"
    using e_def
    by fastforce
  have type_e_def: "tgt (type\<^sub>e e) = type (id_to_list name)"
    using e_def
    by fastforce
  show "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG (ig_enum_as_flags name values fob fid))"
    unfolding ig_enum_as_flags_def tg_enum_as_flags_def
    using type_n_def type_e_def
    by simp
next
  fix n
  assume "n \<in> N (ig_enum_as_flags name values fob fid)"
  then have "n \<in> typed (type (id_to_list name)) ` fob ` values"
    unfolding ig_enum_as_flags_def
    by simp
  then have "type\<^sub>n n = type (id_to_list name)"
    by fastforce
  then show "type\<^sub>n n \<in> NT (TG (ig_enum_as_flags name values fob fid))"
    unfolding ig_enum_as_flags_def tg_enum_as_flags_def
    by simp
next
  fix et n
  assume "et \<in> ET (TG (ig_enum_as_flags name values fob fid))"
  then have et_def: "et \<in> (\<lambda>x. (type (id_to_list name), x, type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values"
    unfolding ig_enum_as_flags_def tg_enum_as_flags_def
    by simp
  then have mult_def: "m_out (mult (TG (ig_enum_as_flags name values fob fid)) et) = \<^bold>0..\<^bold>1"
    unfolding ig_enum_as_flags_def tg_enum_as_flags_def
    by simp
  assume "n \<in> N (ig_enum_as_flags name values fob fid)"
  then have n_def: "n \<in> typed (type (id_to_list name)) ` fob ` values"
    unfolding ig_enum_as_flags_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> inh (TG (ig_enum_as_flags name values fob fid))"
  then have inh_def: "type\<^sub>n n = type (id_to_list name) \<and> src et = type (id_to_list name)"
    unfolding ig_enum_as_flags_def tg_enum_as_flags_def
    by simp
  have "card {e \<in> E (ig_enum_as_flags name values fob fid). src e = n \<and> type\<^sub>e e = et} in \<^bold>0..\<^bold>1"
    using et_def n_def
  proof (elim imageE)
    fix x1 x2 x3 y1 y2
    assume x1_def: "x1 \<in> values"
    assume x2_def: "x2 = [x1]"
    assume "x3 = flag x2"
    then have x3_def: "x3 = flag [x1]"
      by (simp add: x2_def)
    assume "et = (type (id_to_list name), x3, type (id_to_list name))"
    then have et_def: "et = (type (id_to_list name), flag [x1], type (id_to_list name))"
      by (simp add: x3_def)
    assume y1_def: "y1 \<in> values" 
    assume y2_def: "y2 = fob y1"
    assume "n = typed (type (id_to_list name)) y2"
    then have n_def: "n = typed (type (id_to_list name)) (fob y1)"
      by (simp add: y2_def)
    show ?thesis
    proof (induct "x1 = y1")
      case True
      then have n_def: "n = typed (type (id_to_list name)) (fob x1)"
        using n_def
        by simp
      have "{e \<in> E (ig_enum_as_flags name values fob fid). src e = n \<and> type\<^sub>e e = et} = 
        {(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))}"
      proof
        show "{e \<in> E (ig_enum_as_flags name values fob fid). src e = n \<and> type\<^sub>e e = et} \<subseteq>
          {(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))}"
        proof
          fix x
          assume "x \<in> {e \<in> E (ig_enum_as_flags name values fob fid). src e = n \<and> type\<^sub>e e = et}"
          then show "x \<in> {(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))}"
          proof
            assume "x \<in> E (ig_enum_as_flags name values fob fid) \<and> src x = n \<and> type\<^sub>e x = et"
            then show "x \<in> {(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))}"
              unfolding ig_enum_as_flags_def
              using et_def n_def x1_def
              by fastforce
          qed
        qed
      next
        show "{(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))} \<subseteq>
          {e \<in> E (ig_enum_as_flags name values fob fid). src e = n \<and> type\<^sub>e e = et}"
        proof
          fix x
          assume "x \<in> {(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))}"
          then show "x \<in> {e \<in> E (ig_enum_as_flags name values fob fid). src e = n \<and> type\<^sub>e e = et}"
            unfolding ig_enum_as_flags_def
            using et_def n_def x1_def
            by simp
        qed
      qed
      then have "card {e \<in> E (ig_enum_as_flags name values fob fid). src e = n \<and> type\<^sub>e e = et} = 1"
        by simp
      then show ?case
        unfolding within_multiplicity_def
        by simp
    next
      case False
      then have "{e \<in> E (ig_enum_as_flags name values fob fid). src e = n \<and> type\<^sub>e e = et} = {}"
        unfolding ig_enum_as_flags_def
        using n_def et_def unique_obs
        by fastforce
      then have "card {e \<in> E (ig_enum_as_flags name values fob fid). src e = n \<and> type\<^sub>e e = et} = 0"
        using card_empty
        by metis
      then show ?case
        unfolding within_multiplicity_def
        by simp
    qed
  qed
  then show "card {e \<in> E (ig_enum_as_flags name values fob fid). src e = n \<and> type\<^sub>e e = et} in
    m_out (mult (TG (ig_enum_as_flags name values fob fid)) et)"
    using mult_def
    by simp
next
  fix et n
  assume "et \<in> ET (TG (ig_enum_as_flags name values fob fid))"
  then have et_def: "et \<in> (\<lambda>x. (type (id_to_list name), x, type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values"
    unfolding ig_enum_as_flags_def tg_enum_as_flags_def
    by simp
  then have mult_def: "m_in (mult (TG (ig_enum_as_flags name values fob fid)) et) = \<^bold>0..\<^bold>1"
    unfolding ig_enum_as_flags_def tg_enum_as_flags_def
    by simp
  assume "n \<in> N (ig_enum_as_flags name values fob fid)"
  then have n_def: "n \<in> typed (type (id_to_list name)) ` fob ` values"
    unfolding ig_enum_as_flags_def
    by simp
  assume "(type\<^sub>n n, tgt et) \<in> inh (TG (ig_enum_as_flags name values fob fid))"
  then have inh_def: "type\<^sub>n n = type (id_to_list name) \<and> tgt et = type (id_to_list name)"
    unfolding ig_enum_as_flags_def tg_enum_as_flags_def
    by simp
  have "card {e \<in> E (ig_enum_as_flags name values fob fid). tgt e = n \<and> type\<^sub>e e = et} in \<^bold>0..\<^bold>1"
    using et_def n_def
  proof (elim imageE)
    fix x1 x2 x3 y1 y2
    assume x1_def: "x1 \<in> values"
    assume x2_def: "x2 = [x1]"
    assume "x3 = flag x2"
    then have x3_def: "x3 = flag [x1]"
      by (simp add: x2_def)
    assume "et = (type (id_to_list name), x3, type (id_to_list name))"
    then have et_def: "et = (type (id_to_list name), flag [x1], type (id_to_list name))"
      by (simp add: x3_def)
    assume y1_def: "y1 \<in> values" 
    assume y2_def: "y2 = fob y1"
    assume "n = typed (type (id_to_list name)) y2"
    then have n_def: "n = typed (type (id_to_list name)) (fob y1)"
      by (simp add: y2_def)
    show ?thesis
    proof (induct "x1 = y1")
      case True
      then have n_def: "n = typed (type (id_to_list name)) (fob x1)"
        using n_def
        by simp
      have "{e \<in> E (ig_enum_as_flags name values fob fid). tgt e = n \<and> type\<^sub>e e = et} = 
        {(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))}"
      proof
        show "{e \<in> E (ig_enum_as_flags name values fob fid). tgt e = n \<and> type\<^sub>e e = et} \<subseteq>
          {(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))}"
        proof
          fix x
          assume "x \<in> {e \<in> E (ig_enum_as_flags name values fob fid). tgt e = n \<and> type\<^sub>e e = et}"
          then show "x \<in> {(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))}"
          proof
            assume "x \<in> E (ig_enum_as_flags name values fob fid) \<and> tgt x = n \<and> type\<^sub>e x = et"
            then show "x \<in> {(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))}"
              unfolding ig_enum_as_flags_def
              using et_def n_def x1_def
              by fastforce
          qed
        qed
      next
        show "{(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))} \<subseteq>
          {e \<in> E (ig_enum_as_flags name values fob fid). tgt e = n \<and> type\<^sub>e e = et}"
        proof
          fix x
          assume "x \<in> {(typed (type (id_to_list name)) (fob x1), (type (id_to_list name), flag [x1], type (id_to_list name)), typed (type (id_to_list name)) (fob x1))}"
          then show "x \<in> {e \<in> E (ig_enum_as_flags name values fob fid). tgt e = n \<and> type\<^sub>e e = et}"
            unfolding ig_enum_as_flags_def
            using et_def n_def x1_def
            by simp
        qed
      qed
      then have "card {e \<in> E (ig_enum_as_flags name values fob fid). tgt e = n \<and> type\<^sub>e e = et} = 1"
        by simp
      then show ?case
        unfolding within_multiplicity_def
        by simp
    next
      case False
      then have "{e \<in> E (ig_enum_as_flags name values fob fid). tgt e = n \<and> type\<^sub>e e = et} = {}"
        unfolding ig_enum_as_flags_def
        using n_def et_def unique_obs
        by fastforce
      then have "card {e \<in> E (ig_enum_as_flags name values fob fid). tgt e = n \<and> type\<^sub>e e = et} = 0"
        using card_empty
        by metis
      then show ?case
        unfolding within_multiplicity_def
        by simp
    qed
  qed
  then show "card {e \<in> E (ig_enum_as_flags name values fob fid). tgt e = n \<and> type\<^sub>e e = et} in
    m_in (mult (TG (ig_enum_as_flags name values fob fid)) et)"
    using mult_def
    by simp
next
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj (ig_enum_as_flags name values fob fid)) p"
    unfolding ig_enum_as_flags_def tg_enum_as_flags_def instance_graph_containment_proj_def 
    unfolding pre_digraph.cycle_def pre_digraph.awalk_def
    by simp
qed (simp_all add: assms ig_enum_as_flags_def tg_enum_as_flags_def)

lemma ig_enum_as_flags_combine_correct:
  assumes "instance_graph IG"
  assumes new_enum_type: "type (id_to_list name) \<notin> NT (TG IG)"
  assumes new_value_types: "NT (TG IG) \<inter> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values = {}"
  assumes unique_ids: "\<And>o1 o2. o1 \<in> values \<Longrightarrow> fid o1 = fid o2 \<Longrightarrow> o1 = o2"
  assumes unique_obs: "\<And>o1 o2. o1 \<in> values \<Longrightarrow> fob o1 = fob o2 \<Longrightarrow> o1 = o2"
  assumes new_ids: "Id IG \<inter> fid ` values = {}"
  shows "instance_graph (ig_combine IG (ig_enum_as_flags name values fob fid))"
proof (intro ig_combine_distinct_correct)
  show "instance_graph (ig_enum_as_flags name values fob fid)"
    using unique_ids unique_obs
    by (fact ig_enum_as_flags_correct)
next
  fix i
  assume "i \<in> Id IG"
  then have i_not_in_ids: "i \<notin> fid ` values"
    using new_ids
    by auto
  assume "i \<in> Id (ig_enum_as_flags name values fob fid)"
  then have "i \<in> fid ` values"
    unfolding ig_enum_as_flags_def
    by simp
  then show "ident IG i = ident (ig_enum_as_flags name values fob fid) i"
    using i_not_in_ids
    by blast
qed (simp_all add: ig_enum_as_flags_def tg_enum_as_flags_def assms)


subsection "Transformation functions"

definition imod_enum_to_ig_enum_as_flags :: "'t Id \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'o) \<Rightarrow> ('t \<Rightarrow> 't) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('o, 't list, 't) instance_graph" where
  "imod_enum_to_ig_enum_as_flags name values fob fid Imod = \<lparr>
    TG = tg_enum_as_flags name values,
    Id = fid ` values,
    N = typed (type (id_to_list name)) ` fob ` values,
    E = (\<lambda>x. (typed (type (id_to_list name)) (fob x), (type (id_to_list name), flag [x], type (id_to_list name)), typed (type (id_to_list name)) (fob x))) ` values,
    ident = (\<lambda>x. if x \<in> fid ` values then typed (type (id_to_list name)) (fob (THE y. fid y = x)) else undefined)
  \<rparr>"

lemma imod_enum_to_ig_enum_as_flags_proj:
  shows "imod_enum_to_ig_enum_as_flags name values fob fid (imod_enum name values) = ig_enum_as_flags name values fob fid"
  unfolding imod_enum_to_ig_enum_as_flags_def ig_enum_as_flags_def imod_enum_def
  by simp

lemma imod_enum_to_ig_enum_as_flags_func:
  shows "ig_combine_mapping_function (imod_enum_to_ig_enum_as_flags name values fob fid) (imod_enum name values) (ig_enum_as_flags name values fob fid)"
  by (intro ig_combine_mapping_function.intro)
    (auto simp add: imod_enum_to_ig_enum_as_flags_def imod_enum_def ig_enum_as_flags_def imod_combine_def)

definition ig_enum_as_flags_to_imod_enum :: "'t Id \<Rightarrow> 't set \<Rightarrow> ('o, 't list, 't) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "ig_enum_as_flags_to_imod_enum name values IG = \<lparr>
    Tm = tmod_enum name values,
    Object = {},
    ObjectClass = (\<lambda>x. undefined),
    ObjectId = (\<lambda>x. undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma ig_enum_as_flags_to_imod_enum_proj:
  shows "ig_enum_as_flags_to_imod_enum name values (ig_enum_as_flags name values fob fid) = imod_enum name values"
  unfolding ig_enum_as_flags_to_imod_enum_def imod_enum_def ig_enum_as_flags_def
  by simp

lemma ig_enum_as_flags_to_imod_enum_func:
  shows "imod_combine_mapping_function (ig_enum_as_flags_to_imod_enum name values) (ig_enum_as_flags name values fob fid) (imod_enum name values)"
  by (intro imod_combine_mapping_function.intro)
    (simp_all add: ig_enum_as_flags_to_imod_enum_def imod_enum_def ig_enum_as_flags_def ig_combine_def)

end