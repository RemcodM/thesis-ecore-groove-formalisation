theory SubclassType
  imports
    Main
    "Ecore-GROOVE-Mapping.Type_Model_Graph_Mapping"
    "Ecore-GROOVE-Mapping.Identifier_List"
begin

section "Definition of a type model which introduces a Class"

definition tmod_subclass :: "'t Id \<Rightarrow> 't Id \<Rightarrow> 't type_model" where
  "tmod_subclass name supertype = \<lparr>
    Class = {supertype, name},
    Enum = {},
    UserDataType = {},
    Field = {},
    FieldSig = (\<lambda>x. undefined),
    EnumValue = {},
    Inh = {(name, supertype)},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tmod_subclass_correct:
  assumes "name \<noteq> supertype"
  assumes "\<not>id_in_ns name (Identifier supertype) \<and> \<not>id_in_ns supertype (Identifier name)"
  shows "type_model (tmod_subclass name supertype)"
proof (intro type_model.intro)
  fix x y
  assume "x \<in> Class (tmod_subclass name supertype) \<union> 
    Enum (tmod_subclass name supertype) \<union> 
    UserDataType (tmod_subclass name supertype)"
  then have x_def: "x = supertype \<or> x = name"
    unfolding tmod_subclass_def
    by simp
  assume "y \<in> Class (tmod_subclass name supertype) \<union> 
    Enum (tmod_subclass name supertype) \<union> 
    UserDataType (tmod_subclass name supertype)"
  then have y_def: "y = supertype \<or> y = name"
    unfolding tmod_subclass_def
    by simp
  show "\<not>id_in_ns x (Identifier y)"
    using x_def y_def
    by (elim disjE) (simp_all add: assms)
next
  have "asym ({(name, supertype)}) \<and> irrefl (({(name, supertype)})\<^sup>+)"
  proof (intro conjI)
    have irrefl: "irrefl {(name, supertype)}"
      unfolding irrefl_def
      using assms
      by blast
    then show "irrefl ({(name, supertype)}\<^sup>+)"
      using irrefl_def tranclD tranclD2
      by fastforce
    show "asym {(name, supertype)}"
    proof (intro asymI)
      show "irrefl {(name, supertype)}"
        by (fact irrefl)
    next
      fix a b
      assume "(a, b) \<in> {(name, supertype)}"
      then show "(b, a) \<notin> {(name, supertype)}"
        using assms(1)
        by blast
    qed
  qed
  then show "asym (Inh (tmod_subclass name supertype)) \<and> irrefl ((Inh (tmod_subclass name supertype))\<^sup>+)"
    unfolding tmod_subclass_def
    by simp
qed (simp_all add: tmod_subclass_def)

lemma tmod_subclass_combine_correct:
  assumes "type_model Tmod"
  assumes name_supertype_neq: "name \<noteq> supertype"
  assumes name_supertype_ns_valid: "\<not>id_in_ns name (Identifier supertype) \<and> \<not>id_in_ns supertype (Identifier name)"
  assumes combined_classes: "Class Tmod \<inter> {supertype, name} = {supertype}"
  assumes new_subclass: "name \<notin> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
  assumes name_namespace_valid: "\<And>x. x \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod \<Longrightarrow> \<not>id_in_ns name (Identifier x) \<and> \<not>id_in_ns x (Identifier name)"
  shows "type_model (tmod_combine Tmod (tmod_subclass name supertype))"
proof (intro tmod_combine_merge_correct)
  show "type_model (tmod_subclass name supertype)"
    using name_supertype_neq name_supertype_ns_valid
    by (fact tmod_subclass_correct)
next
  fix c
  assume "c \<in> Class (tmod_subclass name supertype)"
  then have "c = name \<or> c = supertype"
    unfolding tmod_subclass_def
    by fastforce
  then show "c \<notin> Enum Tmod \<and> c \<notin> UserDataType Tmod"
    using Int_iff UnCI assms(1) combined_classes new_subclass singleton_iff type_model.property_class_disjoint
    by metis
next
  fix e
  assume "e \<in> Enum Tmod"
  then have "e \<noteq> supertype \<and> e \<noteq> name"
    using UnCI assms(1) combined_classes new_subclass singletonI sup_inf_absorb type_model.property_enum_disjoint
    by metis
  then show "e \<notin> Class (tmod_subclass name supertype) \<and> e \<notin> UserDataType (tmod_subclass name supertype)"
    unfolding tmod_subclass_def
    by simp
next
  fix x y
  assume x_def: "x \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
  assume "y \<in> Class (tmod_subclass name supertype) \<union> 
    Enum (tmod_subclass name supertype) \<union> 
    UserDataType (tmod_subclass name supertype)"
  then have y_def: "y = name \<or> y = supertype"
    unfolding tmod_subclass_def
    by fastforce
  then show "\<not>id_in_ns x (Identifier y)"
    using x_def y_def
  proof (elim disjE)
    assume y_supertype: "y = supertype"
    assume "y = name"
    then show ?thesis
      using name_supertype_neq y_supertype by blast
  next
    assume y_supertype: "y = supertype"
    assume "y = name"
    then show ?thesis
      using name_supertype_neq y_supertype by blast
  next
    assume "y = supertype"
    then have "y \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
      using combined_classes
      by blast
    then show ?thesis
      using assms type_model.property_namespace_restriction x_def
      by blast
  qed (simp_all add: assms)
next
  fix x y
  assume y_def: "y \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
  assume "x \<in> Class (tmod_subclass name supertype) \<union> 
    Enum (tmod_subclass name supertype) \<union> 
    UserDataType (tmod_subclass name supertype)"
  then have x_def: "x = name \<or> x = supertype"
    unfolding tmod_subclass_def
    by fastforce
  then show "\<not>id_in_ns x (Identifier y)"
    using x_def y_def
  proof (elim disjE)
    assume x_supertype: "x = supertype"
    assume "x = name"
    then show ?thesis
      using name_supertype_neq x_supertype by blast
  next
    assume x_supertype: "x = supertype"
    assume "x = name"
    then show ?thesis
      using name_supertype_neq x_supertype by blast
  next
    assume "x = supertype"
    then have "x \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
      using combined_classes
      by blast
    then show ?thesis
      using assms type_model.property_namespace_restriction y_def
      by blast
  qed (simp_all add: assms)
next
  have no_subtypes_name: "\<And>a b. (a, b) \<in> (Inh Tmod \<union> Inh (tmod_subclass name supertype))\<^sup>+ \<Longrightarrow> b \<noteq> name"
  proof-
    fix a b
    assume "(a, b) \<in> (Inh Tmod \<union> Inh (tmod_subclass name supertype))\<^sup>+"
    then show "b \<noteq> name"
    proof (induct)
      case (base y)
      then show ?case
      proof (elim UnE)
        assume "(a, y) \<in> Inh Tmod"
        then show ?thesis
          using UnI1 assms(1) new_subclass type_model.structure_inh_wellformed_alt
          by metis
      next
        assume "(a, y) \<in> Inh (tmod_subclass name supertype)"
        then show ?thesis
          unfolding tmod_subclass_def
          using name_supertype_neq
          by fastforce
      qed
    next
      case (step y z)
      then show ?case
      proof (elim UnE)
        assume "(y, z) \<in> Inh Tmod"
        then show ?thesis
          using UnI1 assms(1) new_subclass type_model.structure_inh_wellformed_alt
          by metis
      next
        assume "(y, z) \<in> Inh (tmod_subclass name supertype)"
        then show ?thesis
          unfolding tmod_subclass_def
          using name_supertype_neq
          by fastforce
      qed
    qed
  qed
  have only_name_added: "\<And>a b. (a, b) \<notin> (Inh Tmod)\<^sup>+ \<Longrightarrow> (a, b) \<in> (Inh Tmod \<union> Inh (tmod_subclass name supertype))\<^sup>+ \<Longrightarrow> a = name"
  proof-
    fix a b
    assume ab_not_inh_tmod: "(a, b) \<notin> (Inh Tmod)\<^sup>+"
    assume "(a, b) \<in> (Inh Tmod \<union> Inh (tmod_subclass name supertype))\<^sup>+"
    then show "a = name"
      using ab_not_inh_tmod
    proof (induct)
      case (base y)
      then have "(a, y) \<notin> Inh Tmod"
        by auto
      then show ?case
        using base.hyps
        unfolding tmod_subclass_def
        by simp
    next
      case (step y z)
      then show ?case
      proof (elim UnE)
        assume "(y, z) \<in> Inh Tmod"
        then show ?thesis
        proof (induct "(a, y) \<in> (Inh Tmod)\<^sup>+")
          case True
          then have "(a, z) \<in> (Inh Tmod)\<^sup>+"
            by simp
          then show ?case
            using step.prems
            by blast
        next
          case False
          then show ?case
            using step.hyps(3)
            by blast
        qed
      next
        assume "(y, z) \<in> Inh (tmod_subclass name supertype)"
        then have "(y, z) = (name, supertype)"
          unfolding tmod_subclass_def
          by simp
        then have y_def: "y = name"
          by simp
        then show ?thesis
          using no_subtypes_name step.hyps(1)
          by blast
      qed
    qed
  qed
  show "irrefl ((Inh Tmod \<union> Inh (tmod_subclass name supertype))\<^sup>+)"
  proof
    fix a
    have "\<And>a b. (a, b) \<in> (Inh Tmod \<union> Inh (tmod_subclass name supertype))\<^sup>+ \<Longrightarrow> a \<noteq> b"
    proof-
      fix a b
      assume "(a, b) \<in> (Inh Tmod \<union> Inh (tmod_subclass name supertype))\<^sup>+"
      then show "a \<noteq> b"
      proof (induct)
        case (base y)
        then show ?case
        proof (elim UnE)
          assume "(a, y) \<in> Inh Tmod"
          then show ?thesis
            using assms(1) type_model.property_inh_wellformed_irrefl_alt
            by blast
        next
          assume "(a, y) \<in> Inh (tmod_subclass name supertype)"
          then show ?thesis
            unfolding tmod_subclass_def
            by (simp add: name_supertype_neq)
        qed
      next
        case (step y z)
        then show ?case
        proof (elim UnE)
          assume "(y, z) \<in> Inh Tmod"
          then show ?thesis
          proof (induct "(a, y) \<in> (Inh Tmod)\<^sup>+")
            case True
            then have "(a, y) \<in> (Inh Tmod)\<^sup>+"
              by simp
            then have "(a, z) \<in> (Inh Tmod)\<^sup>+"
              using True.prems
              by auto
            then show ?case
              using assms(1) irrefl_def type_model.property_inh_wellformed_trancl_irrefl
              by metis
          next
            case False
            then have "(a, y) \<in> (Inh Tmod \<union> Inh (tmod_subclass name supertype))\<^sup>+ - (Inh Tmod)\<^sup>+"
              using step.hyps(1)
              by blast
            then have "a = name"
              using only_name_added
              by blast
            then show ?case
              using no_subtypes_name step.hyps(2)
              by blast
          qed
        next
          assume "(y, z) \<in> Inh (tmod_subclass name supertype)"
          then have "(y, z) = (name, supertype)"
            unfolding tmod_subclass_def
            by simp
          then have y_def: "y = name"
            by simp
          then show ?thesis
            using no_subtypes_name step.hyps(1)
            by blast
        qed
      qed
    qed
    then show "(a, a) \<notin> (Inh Tmod \<union> Inh (tmod_subclass name supertype))\<^sup>+"
      by blast
  qed
next
  have subtype_combined: "\<And>a b. a \<sqsubseteq>[tmod_combine Tmod (tmod_subclass name supertype)] b \<Longrightarrow> 
    a \<noteq> \<exclamdown>name \<Longrightarrow> a \<noteq> \<questiondown>name \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<sqsubseteq>[Tmod] b"
  proof-
    fix a b
    assume not_proper_name: "a \<noteq> \<exclamdown>name"
    assume not_nullable_name: "a \<noteq> \<questiondown>name"
    assume ab_not_eq: "a \<noteq> b"
    assume "a \<sqsubseteq>[tmod_combine Tmod (tmod_subclass name supertype)] b"
    then show "a \<sqsubseteq>[Tmod] b"
      unfolding subtype_def
      using not_proper_name not_nullable_name ab_not_eq
    proof (induct)
      case (transitivity t1 t2 t3)
      then show ?case
      proof (induct "t2 = \<exclamdown>name \<or> t2 = \<questiondown>name")
        case True
        then have t2_def: "t2 = \<exclamdown>name \<or> t2 = \<questiondown>name"
          by simp
        then have "t2 \<notin> ClassType Tmod"
          unfolding ClassType_def
        proof (elim disjE)
          assume "t2 = \<exclamdown>name"
          then show "t2 \<notin> ProperClassType Tmod \<union> NullableClassType Tmod"
            using ProperClassType.cases new_subclass
            by auto
        next
          assume "t2 = \<questiondown>name"
          then show "t2 \<notin> ProperClassType Tmod \<union> NullableClassType Tmod"
            using NullableClassType.cases new_subclass
            by auto
        qed
        then have "t2 \<notin> Type Tmod"
          unfolding Type_def NonContainerType_def ClassType_def
          using t2_def
          by fastforce
        then have "(t1, t2) \<notin> subtype_rel Tmod"
          using FieldI2 assms
          by fastforce
        then show ?case
        proof (induct "t1 = t2")
          case True
          then show ?case
            using t2_def transitivity.prems(1) transitivity.prems(2)
            by blast
        next
          case False
          then show ?case
            using transitivity.hyps(5) transitivity.prems(1) transitivity.prems(2) transitivity.prems(3)
            by blast
        qed
      next
        case False
        then show ?case
          using FieldI1 FieldI2 assms(1) subtype_rel.transitivity subtype_relation_field_alt
          by metis
      qed
    next
      case (reflexivity t1)
      then show ?case
        by simp
    next
      case (generalization_of_inheritance_nullable c1 c2)
      then show ?case
        by (simp add: subtype_rel.generalization_of_inheritance_nullable tmod_combine_def tmod_subclass_def)
    next
      case (generalization_of_inheritance_proper c1 c2)
      then show ?case
        by (simp add: subtype_rel.generalization_of_inheritance_proper tmod_combine_def tmod_subclass_def)
    next
      case (nullable_proper_classes c1)
      then have "c1 \<in> Class Tmod"
        unfolding tmod_combine_def tmod_subclass_def
        using combined_classes
        by fastforce
      then show ?case
        using subtype_rel.nullable_proper_classes
        by blast
    qed
  qed
  fix c1 c2 A B
  assume identity_c1: "identity c1 A \<in> tmod_combine_prop Tmod (tmod_subclass name supertype)"
  then have identity_c1_prop: "identity c1 A \<in> Prop Tmod"
    by (cases) (simp_all add: tmod_subclass_def)
  have identity_c1_class: "c1 \<notin> Class (tmod_subclass name supertype)"
    using identity_c1
    by (cases) (simp_all add: tmod_subclass_def)
  then have identity_c1_neq_name: "c1 \<noteq> name"
    by (simp add: tmod_subclass_def)
  assume identity_c2: "identity c2 B \<in> tmod_combine_prop Tmod (tmod_subclass name supertype)"
  then have identity_c2_prop: "identity c2 B \<in> Prop Tmod"
    by (cases) (simp_all add: tmod_subclass_def)
  have identity_c2_class: "c2 \<notin> Class (tmod_subclass name supertype)"
    using identity_c2
    by (cases) (simp_all add: tmod_subclass_def)
  then have identity_c2_neq_name: "c2 \<noteq> name"
    by (simp add: tmod_subclass_def)
  assume c1_c2_neq: "c1 \<noteq> c2"
  assume no_subtype_tmod: "\<not>\<exclamdown>c1 \<sqsubseteq>[Tmod] \<exclamdown>c2"
  assume "\<exclamdown>c1 \<sqsubseteq>[tmod_combine Tmod (tmod_subclass name supertype)] \<exclamdown>c2"
  then have "\<exclamdown>c1 \<sqsubseteq>[Tmod] \<exclamdown>c2"
    by (simp add: c1_c2_neq identity_c1_neq_name subtype_combined)
  then show "A \<subseteq> B"
    using no_subtype_tmod
    by blast
qed (simp_all add: assms tmod_subclass_def)



section "Encoding of a Class as Node Type in GROOVE"

definition tg_subclass_as_node_type :: "'t Id \<Rightarrow> 't Id \<Rightarrow> ('t list) type_graph" where
  "tg_subclass_as_node_type name supertype = \<lparr>
    NT = {type (id_to_list supertype), type (id_to_list name)},
    ET = {},
    inh = {(type (id_to_list name), type (id_to_list name)), 
      (type (id_to_list supertype), type (id_to_list supertype)), 
      (type (id_to_list name), type (id_to_list supertype))},
    abs = {},
    mult = (\<lambda>x. undefined),
    contains = {}
  \<rparr>"

lemma tg_subclass_as_node_type_correct: "type_graph (tg_subclass_as_node_type name supertype)"
proof (intro type_graph.intro)
  fix n
  assume "n \<in> NT (tg_subclass_as_node_type name supertype)"
  then have "n = type (id_to_list name) \<or> n = type (id_to_list supertype)"
    unfolding tg_subclass_as_node_type_def
    by auto
  then have "n \<in> Lab\<^sub>t"
    using Lab\<^sub>t.simps
    by blast
  then show "n \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
    by blast
next
  show relation_def: "Relation.Field (inh (tg_subclass_as_node_type name supertype)) = 
    NT (tg_subclass_as_node_type name supertype)"
    unfolding tg_subclass_as_node_type_def
    by auto
  show "Partial_order (inh (tg_subclass_as_node_type name supertype))"
    unfolding partial_order_on_def preorder_on_def
  proof (intro conjI)
    show "Refl (inh (tg_subclass_as_node_type name supertype))"
    proof
      show "inh (tg_subclass_as_node_type name supertype) \<subseteq> 
        Relation.Field (inh (tg_subclass_as_node_type name supertype)) \<times> 
        Relation.Field (inh (tg_subclass_as_node_type name supertype))"
        unfolding tg_subclass_as_node_type_def
        by simp
    next
      fix x
      assume "x \<in> Relation.Field (inh (tg_subclass_as_node_type name supertype))"
      then have "x \<in> NT (tg_subclass_as_node_type name supertype)"
        using relation_def
        by blast
      then show "(x, x) \<in> inh (tg_subclass_as_node_type name supertype)"
        unfolding tg_subclass_as_node_type_def
        by auto
    qed
  next
    show "trans (inh (tg_subclass_as_node_type name supertype))"
      unfolding trans_def tg_subclass_as_node_type_def
      by simp
  next
    show "antisym (inh (tg_subclass_as_node_type name supertype))"
      unfolding antisym_def tg_subclass_as_node_type_def
      by fastforce
  qed
qed (simp_all add: tg_subclass_as_node_type_def)

lemma tg_subclass_as_node_type_combine_correct:
  assumes "type_graph TG"
  assumes name_supertype_neq: "name \<noteq> supertype"
  assumes combined_type: "NT TG \<inter> {type (id_to_list supertype), type (id_to_list name)} = {type (id_to_list supertype)}"
  shows "type_graph (tg_combine TG (tg_subclass_as_node_type name supertype))"
proof (intro tg_combine_merge_correct)
  show "type_graph (tg_subclass_as_node_type name supertype)"
    by (fact tg_subclass_as_node_type_correct)
next
  fix l s1 t1 s2 t2
  have name_not_node: "type (id_to_list name) \<notin> NT TG"
    using Int_insert_right_if1 combined_type doubleton_eq_iff id_to_list_inverse insert_absorb2 name_supertype_neq unlabel.simps(1)
    by metis
  have not_name_impl_inh_tg: "\<And>a b. (a, b) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+ \<Longrightarrow> 
    a \<noteq> type (id_to_list name) \<Longrightarrow> (a, b) \<in> inh TG"
  proof-
    fix a b
    assume a_not_name: "a \<noteq> type (id_to_list name)"
    assume "(a, b) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+"
    then show "(a, b) \<in> inh TG"
      using a_not_name
    proof (induct)
      case (base y)
      have "(type (id_to_list supertype), type (id_to_list supertype)) \<in> inh TG"
        using assms(1) combined_type type_graph.validity_inh_node
        by fastforce
      then show ?case
        using base.hyps base.prems
        unfolding tg_subclass_as_node_type_def
        by auto
    next
      case (step y z)
      then show ?case
      proof (elim UnE)
        assume "(y, z) \<in> inh TG"
        then show ?thesis
          using assms(1) step.hyps(3) step.prems transE type_graph.validity_inh_trans
          by metis
      next
        have ay_in_tg: "(a, y) \<in> inh TG"
          by (simp add: step.hyps(3) step.prems)
        then have y_not_name: "y \<noteq> type (id_to_list name)"
          using assms(1) name_not_node type_graph.structure_inheritance_wellformed_second_node
          by blast
        assume "(y, z) \<in> inh (tg_subclass_as_node_type name supertype)"
        then have "(y, z) = (type (id_to_list supertype), type (id_to_list supertype))"
          unfolding tg_subclass_as_node_type_def
          using y_not_name
          by simp
        then have "(y, z) \<in> inh TG"
          using assms(1) ay_in_tg type_graph.structure_inheritance_wellformed_second_node type_graph.validity_inh_node
          by fastforce
        then show ?thesis
          using assms(1) ay_in_tg transE type_graph.validity_inh_trans
          by metis
      qed
    qed
  qed
  assume "(s1, l, t1) \<in> ET TG"
  then have s1_not_name: "s1 \<noteq> type (id_to_list name)"
    using assms name_not_node type_graph.structure_edges_wellformed_src_node
    by blast
  assume "(s2, l, t2) \<in> ET TG"
  then have s2_not_name: "s2 \<noteq> type (id_to_list name)"
    using assms name_not_node type_graph.structure_edges_wellformed_src_node
    by blast
  assume "(s1, s2) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+ - inh TG \<or>
    (s2, s1) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+ - inh TG"
  then show "s1 = s2 \<and> t1 = t2"
    using not_name_impl_inh_tg s1_not_name s2_not_name
    by blast
next
  fix l s1 t1 s2 t2
  have name_not_node: "type (id_to_list name) \<notin> NT TG"
    using Int_insert_right_if1 combined_type doubleton_eq_iff id_to_list_inverse insert_absorb2 name_supertype_neq unlabel.simps(1)
    by metis
  have not_name_impl_inh_tg: "\<And>a b. (a, b) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+ \<Longrightarrow> 
    a \<noteq> type (id_to_list name) \<Longrightarrow> (a, b) \<in> inh TG"
  proof-
    fix a b
    assume a_not_name: "a \<noteq> type (id_to_list name)"
    assume "(a, b) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+"
    then show "(a, b) \<in> inh TG"
      using a_not_name
    proof (induct)
      case (base y)
      have "(type (id_to_list supertype), type (id_to_list supertype)) \<in> inh TG"
        using assms(1) combined_type type_graph.validity_inh_node
        by fastforce
      then show ?case
        using base.hyps base.prems
        unfolding tg_subclass_as_node_type_def
        by auto
    next
      case (step y z)
      then show ?case
      proof (elim UnE)
        assume "(y, z) \<in> inh TG"
        then show ?thesis
          using assms(1) step.hyps(3) step.prems transE type_graph.validity_inh_trans
          by metis
      next
        have ay_in_tg: "(a, y) \<in> inh TG"
          by (simp add: step.hyps(3) step.prems)
        then have y_not_name: "y \<noteq> type (id_to_list name)"
          using assms(1) name_not_node type_graph.structure_inheritance_wellformed_second_node
          by blast
        assume "(y, z) \<in> inh (tg_subclass_as_node_type name supertype)"
        then have "(y, z) = (type (id_to_list supertype), type (id_to_list supertype))"
          unfolding tg_subclass_as_node_type_def
          using y_not_name
          by simp
        then have "(y, z) \<in> inh TG"
          using assms(1) ay_in_tg type_graph.structure_inheritance_wellformed_second_node type_graph.validity_inh_node
          by fastforce
        then show ?thesis
          using assms(1) ay_in_tg transE type_graph.validity_inh_trans
          by metis
      qed
    qed
  qed
  assume "(s1, l, t1) \<in> ET TG"
  then have t1_not_name: "t1 \<noteq> type (id_to_list name)"
    using assms name_not_node type_graph.structure_edges_wellformed_tgt_node
    by blast
  assume "(s2, l, t2) \<in> ET TG"
  then have t2_not_name: "t2 \<noteq> type (id_to_list name)"
    using assms name_not_node type_graph.structure_edges_wellformed_tgt_node
    by blast
  assume "(t1, t2) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+ - inh TG \<or>
    (t2, t1) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+ - inh TG"
  then show "s1 = s2 \<and> t1 = t2"
    using not_name_impl_inh_tg t1_not_name t2_not_name
    by blast
next
  have name_not_node: "type (id_to_list name) \<notin> NT TG"
    using Int_insert_right_if1 combined_type doubleton_eq_iff id_to_list_inverse insert_absorb2 name_supertype_neq unlabel.simps(1)
    by metis
  have not_name_impl_inh_tg: "\<And>a b. (a, b) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+ \<Longrightarrow> 
    a \<noteq> type (id_to_list name) \<Longrightarrow> (a, b) \<in> inh TG"
  proof-
    fix a b
    assume a_not_name: "a \<noteq> type (id_to_list name)"
    assume "(a, b) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+"
    then show "(a, b) \<in> inh TG"
      using a_not_name
    proof (induct)
      case (base y)
      have "(type (id_to_list supertype), type (id_to_list supertype)) \<in> inh TG"
        using assms(1) combined_type type_graph.validity_inh_node
        by fastforce
      then show ?case
        using base.hyps base.prems
        unfolding tg_subclass_as_node_type_def
        by auto
    next
      case (step y z)
      then show ?case
      proof (elim UnE)
        assume "(y, z) \<in> inh TG"
        then show ?thesis
          using assms(1) step.hyps(3) step.prems transE type_graph.validity_inh_trans
          by metis
      next
        have ay_in_tg: "(a, y) \<in> inh TG"
          by (simp add: step.hyps(3) step.prems)
        then have y_not_name: "y \<noteq> type (id_to_list name)"
          using assms(1) name_not_node type_graph.structure_inheritance_wellformed_second_node
          by blast
        assume "(y, z) \<in> inh (tg_subclass_as_node_type name supertype)"
        then have "(y, z) = (type (id_to_list supertype), type (id_to_list supertype))"
          unfolding tg_subclass_as_node_type_def
          using y_not_name
          by simp
        then have "(y, z) \<in> inh TG"
          using assms(1) ay_in_tg type_graph.structure_inheritance_wellformed_second_node type_graph.validity_inh_node
          by fastforce
        then show ?thesis
          using assms(1) ay_in_tg transE type_graph.validity_inh_trans
          by metis
      qed
    qed
  qed
  have inh_not_eq_impl_not_name: "\<And>a b. (a, b) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+ \<Longrightarrow> 
    a \<noteq> b \<Longrightarrow> b \<noteq> type (id_to_list name)"
  proof-
    fix a b
    assume ab_def: "(a, b) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+"
    assume ab_neq: "a \<noteq> b"
    show "b \<noteq> type (id_to_list name)"
      using ab_def ab_neq
    proof (induct)
      case (base y)
      then show ?case
      proof (elim UnE)
        assume "(a, y) \<in> inh TG"
        then show "y \<noteq> type (id_to_list name)"
          using assms(1) name_not_node type_graph.structure_inheritance_wellformed_second_node
          by blast
      next
        assume "(a, y) \<in> inh (tg_subclass_as_node_type name supertype)"
        then show "y \<noteq> type (id_to_list name)"
          unfolding tg_subclass_as_node_type_def
          using assms(1) base.hyps base.prems name_not_node not_name_impl_inh_tg 
          using type_graph.structure_inheritance_wellformed_second_node
          by blast
      qed
    next
      case (step y z)
      then show ?case
      proof (induct "y = type (id_to_list name)")
        case True
        then show ?case
          by auto
      next
        case False
        then have "(y, z) \<in> inh TG"
          using not_name_impl_inh_tg
          by blast
        then show ?case
          using assms(1) name_not_node type_graph.structure_inheritance_wellformed_second_node
          by blast
      qed
    qed
  qed
  show "antisym ((inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+)"
  proof
    fix x y
    assume xy_def: "(x, y) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+"
    assume "(y, x) \<in> (inh TG \<union> inh (tg_subclass_as_node_type name supertype))\<^sup>+"
    then show "x = y"
    proof (induct "x = type (id_to_list name)")
      case True
      then show ?case
        using inh_not_eq_impl_not_name
        by blast
    next
      case False
      then show ?case
        using antisymD assms(1) inh_not_eq_impl_not_name not_name_impl_inh_tg type_graph.validity_inh_antisym xy_def
        by metis
    qed
  qed
qed (simp_all add: tg_subclass_as_node_type_def assms)


subsection "Transformation functions"

definition tmod_subclass_to_tg_subclass_as_node_type :: "'t type_model \<Rightarrow> ('t list) type_graph" where
  "tmod_subclass_to_tg_subclass_as_node_type Tmod = \<lparr>
    NT = type ` id_to_list ` Class Tmod,
    ET = {},
    inh = {(i, j) \<in> type ` id_to_list ` Class Tmod \<times> type ` id_to_list ` Class Tmod. i = j} \<union> 
      (\<lambda>x. (type (id_to_list (fst x)), type (id_to_list (snd x)))) ` Inh Tmod,
    abs = {},
    mult = (\<lambda>x. undefined),
    contains = {}
  \<rparr>"

lemma tmod_subclass_to_tg_subclass_as_node_type_proj:
  shows "tmod_subclass_to_tg_subclass_as_node_type (tmod_subclass name supertype) = tg_subclass_as_node_type name supertype"
  unfolding tmod_subclass_to_tg_subclass_as_node_type_def tmod_subclass_def tg_subclass_as_node_type_def
  by auto

lemma tmod_subclass_to_tg_subclass_as_node_type_func:
  shows "tg_combine_mapping_function (tmod_subclass_to_tg_subclass_as_node_type) (tmod_subclass name supertype) (tg_subclass_as_node_type name supertype)"
  by (intro tg_combine_mapping_function.intro)
    (auto simp add: tmod_subclass_to_tg_subclass_as_node_type_def tmod_subclass_def tg_subclass_as_node_type_def tmod_combine_def)

definition tg_subclass_as_node_type_to_tmod_subclass :: "('t list) type_graph \<Rightarrow> 't type_model" where
  "tg_subclass_as_node_type_to_tmod_subclass TG = \<lparr>
    Class = list_to_id ` unlabel ` NT TG,
    Enum = {},
    UserDataType = {},
    Field = {},
    FieldSig = (\<lambda>x. undefined),
    EnumValue = {},
    Inh = (\<lambda>x. (list_to_id (unlabel (fst x)), list_to_id (unlabel (snd x)))) ` {(i, j) \<in> inh TG. i \<noteq> j},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tg_subclass_as_node_type_to_tmod_subclass_proj:
  assumes name_supertype_neq: "name \<noteq> supertype"
  shows "tg_subclass_as_node_type_to_tmod_subclass (tg_subclass_as_node_type name supertype) = tmod_subclass name supertype"
proof-
  have name_supertype_type_neq: "type (id_to_list name) \<noteq> type (id_to_list supertype)"
    using LabDef.inject(1) id_to_list_inverse name_supertype_neq
    by metis
  have Inh_proj: "(\<lambda>x. (list_to_id (unlabel (fst x)), list_to_id (unlabel (snd x)))) `
    {(i, j) \<in> inh (tg_subclass_as_node_type name supertype). i \<noteq> j} =
    {(name, supertype)}"
  proof
    show "(\<lambda>x. (list_to_id (unlabel (fst x)), list_to_id (unlabel (snd x)))) `
      {(i, j) \<in> inh (tg_subclass_as_node_type name supertype). i \<noteq> j} \<subseteq>
      {(name, supertype)}"
    proof
      fix x
      assume "x \<in> (\<lambda>x. (list_to_id (unlabel (fst x)), list_to_id (unlabel (snd x)))) `
        {(i, j) \<in> inh (tg_subclass_as_node_type name supertype). i \<noteq> j}"
      then have "x \<in> (\<lambda>x. (list_to_id (unlabel (fst x)), list_to_id (unlabel (snd x)))) `
        {(type (id_to_list name), type (id_to_list supertype))}"
        unfolding tg_subclass_as_node_type_def
        by auto
      then show "x \<in> {(name, supertype)}"
        by (simp add: id_to_list_inverse)
    qed
  next
    show "{(name, supertype)} \<subseteq>
      (\<lambda>x. (list_to_id (unlabel (fst x)), list_to_id (unlabel (snd x)))) `
      {(i, j) \<in> inh (tg_subclass_as_node_type name supertype). i \<noteq> j}"
    proof
      fix x
      assume "x \<in> {(name, supertype)}"
      then have x_def: "x \<in> (\<lambda>x. (list_to_id (unlabel (fst x)), list_to_id (unlabel (snd x)))) `
        {(type (id_to_list name), type (id_to_list supertype))}"
        by (simp add: id_to_list_inverse)
      have "{(type (id_to_list name), type (id_to_list supertype))} \<subseteq>
        {(i, j). (i, j) \<in> inh (tg_subclass_as_node_type name supertype) \<and> i \<noteq> j}"
        unfolding tg_subclass_as_node_type_def
        using name_supertype_type_neq
        by simp
      then show "x \<in> (\<lambda>x. (list_to_id (unlabel (fst x)), list_to_id (unlabel (snd x)))) `
        {(i, j). (i, j) \<in> inh (tg_subclass_as_node_type name supertype) \<and> i \<noteq> j}"
        using x_def
        by blast
    qed
  qed
  show "tg_subclass_as_node_type_to_tmod_subclass (tg_subclass_as_node_type name supertype) = tmod_subclass name supertype"
    unfolding tg_subclass_as_node_type_to_tmod_subclass_def tmod_subclass_def
    using Inh_proj
    unfolding tg_subclass_as_node_type_def
    by (simp_all add: id_to_list_inverse)
qed

lemma tg_subclass_as_node_type_to_tmod_subclass_func:
  assumes name_supertype_neq: "name \<noteq> supertype"
  shows "tmod_combine_mapping_function (tg_subclass_as_node_type_to_tmod_subclass) (tg_subclass_as_node_type name supertype) (tmod_subclass name supertype)"
proof (intro tmod_combine_mapping_function.intro)
  show "tg_subclass_as_node_type_to_tmod_subclass (tg_subclass_as_node_type name supertype) = tmod_subclass name supertype"
    using assms tg_subclass_as_node_type_to_tmod_subclass_proj
    by blast
next
  fix TGX
  show "Inh (tg_subclass_as_node_type_to_tmod_subclass (tg_subclass_as_node_type name supertype)) \<subseteq> 
    Inh (tg_subclass_as_node_type_to_tmod_subclass (tg_combine (tg_subclass_as_node_type name supertype) TGX))"
  proof
    fix x
    assume "x \<in> Inh (tg_subclass_as_node_type_to_tmod_subclass (tg_subclass_as_node_type name supertype))"
    then show "x \<in> Inh (tg_subclass_as_node_type_to_tmod_subclass (tg_combine (tg_subclass_as_node_type name supertype) TGX))"
      unfolding tg_subclass_as_node_type_to_tmod_subclass_def tg_combine_def
      by auto
  qed
qed (simp_all add: tg_subclass_as_node_type_to_tmod_subclass_def tmod_subclass_def tg_subclass_as_node_type_def tg_combine_def id_to_list_inverse)

end