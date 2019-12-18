theory EnumType
  imports
    Main
    "Ecore-GROOVE-Mapping.Type_Model_Graph_Mapping"
    "Ecore-GROOVE-Mapping.Identifier_List"
begin

section "Definition of a type model which introduces a Class"

definition tmod_enum :: "'t Id \<Rightarrow> 't set \<Rightarrow> 't type_model" where
  "tmod_enum name values = \<lparr>
    Class = {},
    Enum = {name},
    UserDataType = {},
    Field = {},
    FieldSig = (\<lambda>x. undefined),
    EnumValue = Pair name ` values,
    Inh = {},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tmod_enum_correct: "type_model (tmod_enum name values)"
proof (intro type_model.intro)
  fix ev
  assume "ev \<in> EnumValue (tmod_enum name values)"
  then have "fst ev = name"
    unfolding tmod_enum_def
    by fastforce
  then show "fst ev \<in> Enum (tmod_enum name values)"
    unfolding tmod_enum_def
    by simp
next
  have "asym {} \<and> irrefl {}"
    by (simp add: asym.intros irrefl_def)
  then show "asym (Inh (tmod_enum name values)) \<and> irrefl ((Inh (tmod_enum name values))\<^sup>+)"
    unfolding tmod_enum_def
    by simp
qed (simp_all add: tmod_enum_def)

lemma tmod_enum_combine_correct:
  assumes "type_model Tmod"
  assumes new_enum: "name \<notin> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod"
  assumes "\<And>x. x \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod \<Longrightarrow> \<not>id_in_ns name (Identifier x) \<and> \<not>id_in_ns x (Identifier name)"
  shows "type_model (tmod_combine Tmod (tmod_enum name values))"
proof (intro tmod_combine_full_distinct_correct)
  show "type_model (tmod_enum name values)"
    by (fact tmod_enum_correct)
next
  show "(Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod) \<inter> (Class (tmod_enum name values) \<union> Enum (tmod_enum name values) \<union> UserDataType (tmod_enum name values)) = {}"
    unfolding tmod_enum_def
    using new_enum
    by simp
qed (simp_all add: assms tmod_enum_def)



section "Encoding of a Enum as Node Types in GROOVE"

definition tg_enum_as_node_types :: "'t Id \<Rightarrow> 't set \<Rightarrow> ('t list) type_graph" where
  "tg_enum_as_node_types name values = \<lparr>
    NT = {type (id_to_list name)} \<union> type ` append (id_to_list name) ` (\<lambda>x. [x]) ` values,
    ET = {},
    inh = {(type (id_to_list name), type (id_to_list name))} \<union> 
      (\<lambda>x. (type x, type x)) ` append (id_to_list name) ` (\<lambda>x. [x]) ` values \<union>
      (\<lambda>x. (type x, type (id_to_list name))) ` append (id_to_list name) ` (\<lambda>x. [x]) ` values,
    abs = {type (id_to_list name)},
    mult = (\<lambda>x. undefined),
    contains = {}
  \<rparr>"

lemma tg_enum_as_node_types_correct: "type_graph (tg_enum_as_node_types name values)"
proof (intro type_graph.intro)
  fix n
  assume "n \<in> NT (tg_enum_as_node_types name values)"
  then have "n \<in> Lab\<^sub>t"
    unfolding tg_enum_as_node_types_def
    using Lab\<^sub>t.simps
    by fastforce
  then show "n \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
    by blast
next
  show inheritance_field: "Relation.Field (inh (tg_enum_as_node_types name values)) = NT (tg_enum_as_node_types name values)"
  proof
    show "Relation.Field (inh (tg_enum_as_node_types name values)) \<subseteq> NT (tg_enum_as_node_types name values)"
    proof
      fix x
      assume "x \<in> Relation.Field (inh (tg_enum_as_node_types name values))"
      then show "x \<in> NT (tg_enum_as_node_types name values)"
        unfolding Relation.Field_def
      proof (elim UnE)
        assume "x \<in> Domain (inh (tg_enum_as_node_types name values))"
        then show "x \<in> NT (tg_enum_as_node_types name values)"
        proof
          fix b
          assume "(x, b) \<in> inh (tg_enum_as_node_types name values)"
          then show "x \<in> NT (tg_enum_as_node_types name values)"
            unfolding tg_enum_as_node_types_def
            by fastforce
        qed
      next
        assume "x \<in> Range (inh (tg_enum_as_node_types name values))"
        then show "x \<in> NT (tg_enum_as_node_types name values)"
        proof
          fix a
          assume "(a, x) \<in> inh (tg_enum_as_node_types name values)"
          then show "x \<in> NT (tg_enum_as_node_types name values)"
            unfolding tg_enum_as_node_types_def
            by fastforce
        qed
      qed
    qed
  next
    show "NT (tg_enum_as_node_types name values) \<subseteq> Relation.Field (inh (tg_enum_as_node_types name values))"
    proof
      fix x
      assume "x \<in> NT (tg_enum_as_node_types name values)"
      then have "x \<in> {type (id_to_list name)} \<union> type ` append (id_to_list name) ` (\<lambda>x. [x]) ` values"
        unfolding tg_enum_as_node_types_def
        by simp
      then show "x \<in> Relation.Field (inh (tg_enum_as_node_types name values))"
      proof (elim UnE)
        assume "x \<in> {type (id_to_list name)}"
        then show "x \<in> Relation.Field (inh (tg_enum_as_node_types name values))"
          unfolding tg_enum_as_node_types_def
          by simp
      next
        assume "x \<in> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
        then show "x \<in> Relation.Field (inh (tg_enum_as_node_types name values))"
          unfolding Relation.Field_def tg_enum_as_node_types_def
          by fastforce
      qed
    qed
  qed
  show "Partial_order (inh (tg_enum_as_node_types name values))"
    unfolding partial_order_on_def preorder_on_def
  proof (intro conjI)
    show "Refl (inh (tg_enum_as_node_types name values))"
      unfolding refl_on_def
    proof (intro conjI)
      show "inh (tg_enum_as_node_types name values) \<subseteq> Relation.Field (inh (tg_enum_as_node_types name values)) \<times> Relation.Field (inh (tg_enum_as_node_types name values))"
        using FieldI1 FieldI2 inheritance_field
        by fastforce
    next
      have "\<And>x. x \<in> NT (tg_enum_as_node_types name values) \<Longrightarrow> (x, x) \<in> inh (tg_enum_as_node_types name values)"
        unfolding tg_enum_as_node_types_def
        by fastforce
      then show "\<forall>x \<in> Relation.Field (inh (tg_enum_as_node_types name values)). (x, x) \<in> inh (tg_enum_as_node_types name values)"
        using inheritance_field
        by blast
    qed
  next
    show "trans (inh (tg_enum_as_node_types name values))"
      unfolding tg_enum_as_node_types_def trans_def
      by fastforce
  next
    show "antisym (inh (tg_enum_as_node_types name values))"
      unfolding tg_enum_as_node_types_def antisym_def
      by fastforce
  qed
qed (simp_all add: tg_enum_as_node_types_def)

lemma tg_enum_as_node_types_combine_correct:
  assumes "type_graph TG"
  assumes new_enum_type: "type (id_to_list name) \<notin> NT TG"
  assumes new_value_types: "NT TG \<inter> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values = {}"
  shows "type_graph (tg_combine TG (tg_enum_as_node_types name values))"
proof (intro tg_combine_distinct_correct)
  show "type_graph (tg_enum_as_node_types name values)"
    by (fact tg_enum_as_node_types_correct)
qed (simp_all add: tg_enum_as_node_types_def assms)


subsection "Transformation functions"

definition tmod_enum_to_tg_enum_as_node_types :: "'t type_model \<Rightarrow> ('t list) type_graph" where
  "tmod_enum_to_tg_enum_as_node_types Tmod = \<lparr>
    NT = type ` id_to_list ` Enum Tmod \<union> type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue Tmod,
    ET = {},
    inh = type ` id_to_list ` Enum Tmod \<times> type ` id_to_list ` Enum Tmod \<union>
      (\<lambda>x. (type x, type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue Tmod \<union>
      type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue Tmod \<times> type ` id_to_list ` Enum Tmod,
    abs = type ` id_to_list ` Enum Tmod,
    mult = (\<lambda>x. undefined),
    contains = {}
  \<rparr>"

lemma tmod_enum_to_tg_enum_as_node_types_proj:
  shows "tmod_enum_to_tg_enum_as_node_types (tmod_enum name values) = tg_enum_as_node_types name values"
proof-
  have nt_proj: "type ` id_to_list ` Enum (tmod_enum name values) \<union> 
    type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) = 
    {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
  proof
    show "type ` id_to_list ` Enum (tmod_enum name values) \<union> 
      type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<subseteq>
      {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
    proof
      fix x
      assume "x \<in> type ` id_to_list ` Enum (tmod_enum name values) \<union> 
        type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values)"
      then show "x \<in> {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
      proof (elim UnE)
        assume "x \<in> type ` id_to_list ` Enum (tmod_enum name values)"
        then show ?thesis
          unfolding tmod_enum_def
          by simp
      next
        assume "x \<in> type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values)"
        then show ?thesis
          unfolding tmod_enum_def
          by fastforce
      qed
    qed
  next
    show "{type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values \<subseteq>
      type ` id_to_list ` Enum (tmod_enum name values) \<union> 
      type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values)"
    proof
      fix x
      assume "x \<in> {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
      then show "x \<in> type ` id_to_list ` Enum (tmod_enum name values) \<union> 
        type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values)"
      proof (elim UnE)
        assume "x \<in> {type (id_to_list name)}"
        then show ?thesis
          unfolding tmod_enum_def
          by simp
      next
        assume "x \<in> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
        then have "x \<in> type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair name ` values"
        proof (elim imageE)
          fix a b c
          assume c_def: "c \<in> values"
          assume b_def: "b = [c]"
          assume "a = id_to_list name @ b"
          then have a_def: "a = id_to_list name @ [c]"
            by (simp add: b_def)
          assume "x = type a"
          then have x_def: "x = type (id_to_list name @ [c])"
            by (simp add: a_def)
          then show ?thesis
          proof
            show "id_to_list name @ [c] \<in> (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair name ` values"
              by (simp add: c_def image_iff)
          qed
        qed
        then show ?thesis
          unfolding tmod_enum_def
          by simp
      qed
    qed
  qed
  have inh_proj: "type ` id_to_list ` Enum (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values) \<union> 
    (\<lambda>x. (type x, type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<union>
    type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values) =
    {(type (id_to_list name), type (id_to_list name))} \<union> (\<lambda>x. (type x, type x)) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values \<union> 
    (\<lambda>x. (type x, type (id_to_list name))) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
  proof
    show "type ` id_to_list ` Enum (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values) \<union> 
      (\<lambda>x. (type x, type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<union>
      type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values) \<subseteq>
      {(type (id_to_list name), type (id_to_list name))} \<union> (\<lambda>x. (type x, type x)) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values \<union> 
      (\<lambda>x. (type x, type (id_to_list name))) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
    proof
      fix x
      assume "x \<in> type ` id_to_list ` Enum (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values) \<union> 
        (\<lambda>x. (type x, type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<union>
        type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values)"
      then show "x \<in> {(type (id_to_list name), type (id_to_list name))} \<union> 
        (\<lambda>x. (type x, type x)) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values \<union> 
        (\<lambda>x. (type x, type (id_to_list name))) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
      proof (elim UnE)
        assume "x \<in> type ` id_to_list ` Enum (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values)"
        then show ?thesis
          unfolding tmod_enum_def
          by simp
      next
        assume "x \<in> (\<lambda>x. (type x, type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values)"
        then show ?thesis
          unfolding tmod_enum_def
          by fastforce
      next
        assume "x \<in> type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values)"
        then show ?thesis
          unfolding tmod_enum_def
          by fastforce
      qed
    qed
  next
    show "{(type (id_to_list name), type (id_to_list name))} \<union> (\<lambda>x. (type x, type x)) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values \<union> 
      (\<lambda>x. (type x, type (id_to_list name))) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values \<subseteq>
      type ` id_to_list ` Enum (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values) \<union> 
      (\<lambda>x. (type x, type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<union>
      type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values)"
    proof
      fix x
      assume "x \<in> {(type (id_to_list name), type (id_to_list name))} \<union> 
        (\<lambda>x. (type x, type x)) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values \<union> 
        (\<lambda>x. (type x, type (id_to_list name))) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
      then show "x \<in> type ` id_to_list ` Enum (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values) \<union> 
        (\<lambda>x. (type x, type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<union>
        type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` EnumValue (tmod_enum name values) \<times> type ` id_to_list ` Enum (tmod_enum name values)"
      proof (elim UnE)
        assume "x \<in> {(type (id_to_list name), type (id_to_list name))}"
        then show ?thesis
          unfolding tmod_enum_def
          by simp
      next
        assume "x \<in> (\<lambda>x. (type x, type x)) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
        then have "x \<in> (\<lambda>x. (type x, type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair name ` values"
        proof (elim imageE)
          fix a b c
          assume c_def: "c \<in> values"
          assume b_def: "b = [c]"
          assume "a = id_to_list name @ b"
          then have a_def: "a = id_to_list name @ [c]"
            by (simp add: b_def)
          assume "x = (type a, type a)"
          then have x_def: "x = (type (id_to_list name @ [c]), type (id_to_list name @ [c]))"
            by (simp add: a_def)
          then show ?thesis
            by (simp add: c_def image_iff)
        qed
        then show ?thesis
          unfolding tmod_enum_def
          by simp
      next
        assume "x \<in> (\<lambda>x. (type x, type (id_to_list name))) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
        then have "x \<in> type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair name ` values \<times> type ` id_to_list ` {name}"
        proof (elim imageE)
          fix a b c
          assume c_def: "c \<in> values"
          assume b_def: "b = [c]"
          assume "a = id_to_list name @ b"
          then have a_def: "a = id_to_list name @ [c]"
            by (simp add: b_def)
          assume "x = (type a, type (id_to_list name))"
          then have x_def: "x = (type (id_to_list name @ [c]), type (id_to_list name))"
            by (simp add: a_def)
          then show ?thesis
            by (simp add: c_def image_iff)
        qed
        then show ?thesis
          unfolding tmod_enum_def
          by simp
      qed
    qed
  qed
  have abs_proj: "type ` id_to_list ` Enum (tmod_enum name values) = {type (id_to_list name)}"
    unfolding tmod_enum_def
    by fastforce
  show "tmod_enum_to_tg_enum_as_node_types (tmod_enum name values) = tg_enum_as_node_types name values"
    unfolding tmod_enum_to_tg_enum_as_node_types_def tg_enum_as_node_types_def
    using nt_proj inh_proj abs_proj
    by simp
qed

lemma tmod_enum_to_tg_enum_as_node_types_func:
  shows "tg_combine_mapping_function (tmod_enum_to_tg_enum_as_node_types) (tmod_enum name values) (tg_enum_as_node_types name values)"
proof (intro tg_combine_mapping_function.intro)
  show "tmod_enum_to_tg_enum_as_node_types (tmod_enum name values) = tg_enum_as_node_types name values"
    by (fact tmod_enum_to_tg_enum_as_node_types_proj)
next
  fix TmodX
  show "NT (tmod_enum_to_tg_enum_as_node_types (tmod_enum name values)) \<subseteq> NT (tmod_enum_to_tg_enum_as_node_types (tmod_combine (tmod_enum name values) TmodX))"
  proof
    fix x
    assume "x \<in> NT (tmod_enum_to_tg_enum_as_node_types (tmod_enum name values))"
    then have "x \<in> type ` id_to_list ` {name} \<union> type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair name ` values"
      unfolding tmod_enum_to_tg_enum_as_node_types_def tmod_enum_def
      by simp
    then show "x \<in> NT (tmod_enum_to_tg_enum_as_node_types (tmod_combine (tmod_enum name values) TmodX))"
    proof (elim UnE)
      assume "x \<in> type ` id_to_list ` {name}"
      then show ?thesis
        unfolding tmod_enum_to_tg_enum_as_node_types_def tmod_enum_def tmod_combine_def
        by simp
    next
      assume "x \<in> type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair name ` values"
      then show ?thesis
        unfolding tmod_enum_to_tg_enum_as_node_types_def tmod_enum_def tmod_combine_def
        by (simp add: image_Un)
    qed
  qed
next
  fix TmodX
  show "inh (tmod_enum_to_tg_enum_as_node_types (tmod_enum name values)) \<subseteq> inh (tmod_enum_to_tg_enum_as_node_types (tmod_combine (tmod_enum name values) TmodX))"
  proof
    fix x
    assume "x \<in> inh (tmod_enum_to_tg_enum_as_node_types (tmod_enum name values))"
    then have "x \<in> type ` id_to_list ` {name} \<times> type ` id_to_list ` {name} \<union> 
      (\<lambda>x. (type x, type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair name ` values \<union> 
      type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair name ` values \<times> type ` id_to_list ` {name}"
      unfolding tmod_enum_to_tg_enum_as_node_types_def tmod_enum_def
      by simp
    then show "x \<in> inh (tmod_enum_to_tg_enum_as_node_types (tmod_combine (tmod_enum name values) TmodX))"
    proof (elim UnE)
      assume "x \<in> type ` id_to_list ` {name} \<times> type ` id_to_list ` {name}"
      then show ?thesis
        unfolding tmod_enum_to_tg_enum_as_node_types_def tmod_enum_def tmod_combine_def
        by simp
    next
      assume "x \<in> (\<lambda>x. (type x, type x)) ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair name ` values"
      then show ?thesis
        unfolding tmod_enum_to_tg_enum_as_node_types_def tmod_enum_def tmod_combine_def
        by (simp add: image_Un)
    next
      assume "x \<in> type ` (\<lambda>x. id_to_list (fst x) @ [snd x]) ` Pair name ` values \<times> type ` id_to_list ` {name}"
      then show ?thesis
        unfolding tmod_enum_to_tg_enum_as_node_types_def tmod_enum_def tmod_combine_def
        by auto
    qed
  qed
qed (simp_all add: tmod_enum_to_tg_enum_as_node_types_def tmod_enum_def tg_enum_as_node_types_def tmod_combine_def)

definition tg_enum_as_node_types_to_tmod_enum :: "'t Id \<Rightarrow> ('t list) type_graph \<Rightarrow> 't type_model" where
  "tg_enum_as_node_types_to_tmod_enum name TG = \<lparr>
    Class = {},
    Enum = list_to_id ` unlabel ` {n \<in> NT TG. n = type (id_to_list name)},
    UserDataType = {},
    Field = {},
    FieldSig = (\<lambda>x. undefined),
    EnumValue = (\<lambda>x. (list_to_id (butlast x), last x)) ` unlabel ` {n \<in> NT TG. n \<noteq> type (id_to_list name)},
    Inh = {},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tg_enum_as_node_types_to_tmod_enum_proj:
  shows "tg_enum_as_node_types_to_tmod_enum name (tg_enum_as_node_types name values) = tmod_enum name values"
proof-
  have "list_to_id ` unlabel ` {n \<in> {type (id_to_list name)} \<union> type ` append (id_to_list name) ` (\<lambda>x. [x]) ` values. n = type (id_to_list name)} = {name}"
  proof
    show "list_to_id ` unlabel ` {n \<in> {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values. n = type (id_to_list name)} \<subseteq> {name}"
    proof
      fix x
      assume "x \<in> list_to_id ` unlabel ` {n \<in> {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values. n = type (id_to_list name)}"
      then have "x \<in> list_to_id ` unlabel ` {type (id_to_list name)}"
        by blast
      then show "x \<in> {name}"
        by (simp add: id_to_list_inverse)
    qed
  next
    show "{name} \<subseteq> list_to_id ` unlabel ` {n \<in> {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values. n = type (id_to_list name)}"
    proof
      fix x
      assume "x \<in> {name}"
      then have "x \<in> list_to_id ` unlabel ` {type (id_to_list name)}"
        by (simp add: id_to_list_inverse)
      then show "x \<in> list_to_id ` unlabel ` {n \<in> {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values. n = type (id_to_list name)}"
        by blast
    qed
  qed
  then have enum_proj: "list_to_id ` unlabel ` {n \<in> NT (tg_enum_as_node_types name values). n = type (id_to_list name)} = {name}"
    unfolding tg_enum_as_node_types_def
    by simp
  have enumvalue_proj: "(\<lambda>x. (list_to_id (butlast x), last x)) ` unlabel ` {n \<in> {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values. n \<noteq> type (id_to_list name)} = Pair name ` values"
  proof
    show "(\<lambda>x. (list_to_id (butlast x), last x)) ` unlabel ` {n \<in> {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values. n \<noteq> type (id_to_list name)} \<subseteq> Pair name ` values"
    proof
      fix x
      assume "x \<in> (\<lambda>x. (list_to_id (butlast x), last x)) ` unlabel ` {n \<in> {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values. n \<noteq> type (id_to_list name)}"
      then have "x \<in> (\<lambda>x. (list_to_id (butlast x), last x)) ` unlabel ` type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
        by blast
      then have "x \<in> (\<lambda>x. (list_to_id (butlast x), last x)) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
        by fastforce
      then have "x \<in> (\<lambda>x. (list_to_id (id_to_list name), x)) ` values"
        by fastforce
      then show "x \<in> Pair name ` values"
        by (simp add: id_to_list_inverse)
    qed
  next
    show "Pair name ` values \<subseteq> (\<lambda>x. (list_to_id (butlast x), last x)) ` unlabel ` {n \<in> {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values. n \<noteq> type (id_to_list name)}"
    proof
      fix x
      assume "x \<in> Pair name ` values"
      then have "x \<in> (\<lambda>x. (list_to_id (id_to_list name), x)) ` values"
        by (simp add: id_to_list_inverse)
      then have "x \<in> (\<lambda>x. (list_to_id (butlast x), last x)) ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
        by force
      then have "x \<in> (\<lambda>x. (list_to_id (butlast x), last x)) ` unlabel ` type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values"
        by force
      then show "x \<in> (\<lambda>x. (list_to_id (butlast x), last x)) ` unlabel ` {n \<in> {type (id_to_list name)} \<union> type ` (@) (id_to_list name) ` (\<lambda>x. [x]) ` values. n \<noteq> type (id_to_list name)}"
        by blast
    qed
  qed
  then have enumvalue_proj: "(\<lambda>x. (list_to_id (butlast x), last x)) ` unlabel ` {n \<in> NT (tg_enum_as_node_types name values). n \<noteq> type (id_to_list name)} = Pair name ` values"
    unfolding tg_enum_as_node_types_def
    by simp
  show "?thesis"
    unfolding tg_enum_as_node_types_to_tmod_enum_def tmod_enum_def
    using enum_proj enumvalue_proj
    by simp
qed

lemma tg_enum_as_node_types_to_tmod_enum_func:
  shows "tmod_combine_mapping_function (tg_enum_as_node_types_to_tmod_enum name) (tg_enum_as_node_types name values) (tmod_enum name values)"
proof (intro tmod_combine_mapping_function.intro)
  show "tg_enum_as_node_types_to_tmod_enum name (tg_enum_as_node_types name values) = tmod_enum name values"
    by (fact tg_enum_as_node_types_to_tmod_enum_proj)
next
  fix TGX
  show "Enum (tg_enum_as_node_types_to_tmod_enum name (tg_enum_as_node_types name values)) \<subseteq> Enum (tg_enum_as_node_types_to_tmod_enum name (tg_combine (tg_enum_as_node_types name values) TGX))"
  proof
    fix x
    assume "x \<in> Enum (tg_enum_as_node_types_to_tmod_enum name (tg_enum_as_node_types name values))"
    then have "x \<in> list_to_id ` unlabel ` {n \<in> NT (tg_enum_as_node_types name values). n = type (id_to_list name)}"
      unfolding tg_enum_as_node_types_to_tmod_enum_def
      by simp
    then show "x \<in> Enum (tg_enum_as_node_types_to_tmod_enum name (tg_combine (tg_enum_as_node_types name values) TGX))"
      unfolding tg_enum_as_node_types_to_tmod_enum_def tg_combine_def
      by fastforce
  qed
next
  fix TGX
  show "EnumValue (tg_enum_as_node_types_to_tmod_enum name (tg_enum_as_node_types name values)) \<subseteq> EnumValue (tg_enum_as_node_types_to_tmod_enum name (tg_combine (tg_enum_as_node_types name values) TGX))"
  proof
    fix x
    assume "x \<in> EnumValue (tg_enum_as_node_types_to_tmod_enum name (tg_enum_as_node_types name values))"
    then have "x \<in> (\<lambda>x. (list_to_id (butlast x), last x)) ` unlabel ` {n \<in> NT (tg_enum_as_node_types name values). n \<noteq> type (id_to_list name)}"
      unfolding tg_enum_as_node_types_to_tmod_enum_def
      by simp
    then show "x \<in> EnumValue (tg_enum_as_node_types_to_tmod_enum name (tg_combine (tg_enum_as_node_types name values) TGX))"
      unfolding tg_enum_as_node_types_to_tmod_enum_def tg_combine_def
      by fastforce
  qed
qed (simp_all add: tg_enum_as_node_types_to_tmod_enum_def tg_enum_as_node_types_def tmod_enum_def)



section "Encoding of a Enum as Flags in GROOVE"

definition tg_enum_as_flags :: "'t Id \<Rightarrow> 't set \<Rightarrow> ('t list) type_graph" where
  "tg_enum_as_flags name values = \<lparr>
    NT = {type (id_to_list name)},
    ET = (\<lambda>x. (type (id_to_list name), x, type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values,
    inh = {(type (id_to_list name), type (id_to_list name))},
    abs = {},
    mult = (\<lambda>x. (if x \<in> (\<lambda>x. (type (id_to_list name), x, type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values then (\<^bold>0..\<^bold>1, \<^bold>0..\<^bold>1) else undefined)),
    contains = {}
  \<rparr>"

lemma tg_enum_as_flags_correct: "type_graph (tg_enum_as_flags name values)"
proof (intro type_graph.intro)
  fix n
  assume "n \<in> NT (tg_enum_as_flags name values)"
  then show "n \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
    unfolding tg_enum_as_flags_def
    by (simp add: Lab\<^sub>t.rule_type_labels)
next
  fix s l t
  assume "(s, l, t) \<in> ET (tg_enum_as_flags name values)"
  then show "s \<in> NT (tg_enum_as_flags name values) \<and> l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> NT (tg_enum_as_flags name values)"
    unfolding tg_enum_as_flags_def
    using Lab\<^sub>f.simps
    by fastforce
next
  fix e
  assume e_in_edges: "e \<in> ET (tg_enum_as_flags name values)"
  have "multiplicity_pair (\<^bold>0..\<^bold>1, \<^bold>0..\<^bold>1)"
  proof (intro multiplicity_pair.intro)
    show "multiplicity (m_in (\<^bold>0..\<^bold>1, \<^bold>0..\<^bold>1))"
      by (intro multiplicity.intro) (simp_all)
    show "multiplicity (m_out (\<^bold>0..\<^bold>1, \<^bold>0..\<^bold>1))"
      by (intro multiplicity.intro) (simp_all)
  qed
  then show "multiplicity_pair (mult (tg_enum_as_flags name values) e)"
    using e_in_edges
    unfolding tg_enum_as_flags_def
    by simp
next
  fix l s1 t1 s2 t2
  assume edge1: "(s1, l, t1) \<in> ET (tg_enum_as_flags name values)"
  assume edge2: "(s2, l, t2) \<in> ET (tg_enum_as_flags name values)"
  show "s1 = s2 \<and> t1 = t2"
    using edge1 edge2
    unfolding tg_enum_as_flags_def
    by fastforce
next
  fix s l t
  assume "(s, l, t) \<in> ET (tg_enum_as_flags name values)"
  then show "s = t"
    unfolding tg_enum_as_flags_def
    by fastforce
next
  show "Partial_order (inh (tg_enum_as_flags name values))"
    unfolding tg_enum_as_flags_def
    using linear_order_on_def
    by fastforce
qed (simp_all add: tg_enum_as_flags_def)

lemma tg_enum_as_flags_combine_correct:
  assumes "type_graph TG"
  assumes new_enum_type: "type (id_to_list name) \<notin> NT TG"
  shows "type_graph (tg_combine TG (tg_enum_as_flags name values))"
proof (intro tg_combine_distinct_correct)
  show "type_graph (tg_enum_as_flags name values)"
    by (fact tg_enum_as_flags_correct)
qed (simp_all add: tg_enum_as_flags_def assms)


subsection "Transformation functions"

definition tmod_enum_to_tg_enum_as_flags :: "'t type_model \<Rightarrow> ('t list) type_graph" where
  "tmod_enum_to_tg_enum_as_flags Tmod = \<lparr>
    NT = type ` id_to_list ` Enum Tmod,
    ET = type ` id_to_list ` Enum Tmod \<times> flag ` (\<lambda>x. [snd x]) ` EnumValue Tmod \<times> type ` id_to_list ` Enum Tmod,
    inh = type ` id_to_list ` Enum Tmod \<times> type ` id_to_list ` Enum Tmod,
    abs = {},
    mult = (\<lambda>x. (
      if x \<in> type ` id_to_list ` Enum Tmod \<times> flag ` (\<lambda>x. [snd x]) ` EnumValue Tmod \<times> type ` id_to_list ` Enum Tmod then 
        (\<^bold>0..\<^bold>1, \<^bold>0..\<^bold>1)
      else 
        undefined)),
    contains = {}
  \<rparr>"

lemma tmod_enum_to_tg_enum_as_flags_proj:
  shows "tmod_enum_to_tg_enum_as_flags (tmod_enum name values) = tg_enum_as_flags name values"
proof-
  have et_proj: "type ` id_to_list ` Enum (tmod_enum name values) \<times>
    flag ` (\<lambda>x. [snd x]) ` EnumValue (tmod_enum name values) \<times>
    type ` id_to_list ` Enum (tmod_enum name values) =
    (\<lambda>x. (type (id_to_list name), x, type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values"
  proof
    show "type ` id_to_list ` Enum (tmod_enum name values) \<times>
      flag ` (\<lambda>x. [snd x]) ` EnumValue (tmod_enum name values) \<times>
      type ` id_to_list ` Enum (tmod_enum name values) \<subseteq>
      (\<lambda>x. (type (id_to_list name), x, type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values"
    proof
      fix x
      assume "x \<in> type ` id_to_list ` Enum (tmod_enum name values) \<times>
        flag ` (\<lambda>x. [snd x]) ` EnumValue (tmod_enum name values) \<times>
        type ` id_to_list ` Enum (tmod_enum name values)"
      then show "x \<in> (\<lambda>x. (type (id_to_list name), x, type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values"
        unfolding tmod_enum_def
        by fastforce
    qed
  next
    show "(\<lambda>x. (type (id_to_list name), x, type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values \<subseteq>
      type ` id_to_list ` Enum (tmod_enum name values) \<times>
      flag ` (\<lambda>x. [snd x]) ` EnumValue (tmod_enum name values) \<times>
      type ` id_to_list ` Enum (tmod_enum name values)"
    proof
      fix x
      assume "x \<in> (\<lambda>x. (type (id_to_list name), x, type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values"
      then have x_def: "x \<in> {type (id_to_list name)} \<times> flag ` (\<lambda>x. [x]) ` values \<times> {type (id_to_list name)}"
        by fastforce
      have "flag ` (\<lambda>x. [x]) ` values = flag ` (\<lambda>x. [snd x]) ` Pair name ` values"
      proof
        show "flag ` (\<lambda>x. [x]) ` values \<subseteq> flag ` (\<lambda>x. [snd x]) ` Pair name ` values"
        proof
          fix x
          assume "x \<in> flag ` (\<lambda>x. [x]) ` values"
          then show "x \<in> flag ` (\<lambda>x. [snd x]) ` Pair name ` values"
          proof (elim imageE)
            fix a b
            assume b_def: "b \<in> values"
            assume a_def: "a = [b]"
            assume "x = flag a"
            then have x_def: "x = flag ([b])"
              by (simp add: a_def)
            then show ?thesis
              by (simp add: b_def image_iff)
          qed
        qed
      next
        show "flag ` (\<lambda>x. [snd x]) ` Pair name ` values \<subseteq>
          flag ` (\<lambda>x. [x]) ` values"
        proof
          fix x
          assume "x \<in> flag ` (\<lambda>x. [snd x]) ` Pair name ` values"
          then show "x \<in> flag ` (\<lambda>x. [x]) ` values"
            by fastforce
        qed
      qed
      then have "x \<in> {type (id_to_list name)} \<times>
        flag ` (\<lambda>x. [snd x]) ` Pair name ` values \<times>
        {type (id_to_list name)}"
        using x_def
        by simp
      then show "x \<in> type ` id_to_list ` Enum (tmod_enum name values) \<times>
        flag ` (\<lambda>x. [snd x]) ` EnumValue (tmod_enum name values) \<times>
        type ` id_to_list ` Enum (tmod_enum name values)"
        unfolding tmod_enum_def
        by simp
    qed
  qed
  show ?thesis
    unfolding tmod_enum_to_tg_enum_as_flags_def tg_enum_as_flags_def
    using et_proj
    unfolding tmod_enum_def
    by simp
qed

lemma tmod_enum_to_tg_enum_as_flags_func:
  shows "tg_combine_mapping_function (tmod_enum_to_tg_enum_as_flags) (tmod_enum name values) (tg_enum_as_flags name values)"
proof (intro tg_combine_mapping_function.intro)
  show "tmod_enum_to_tg_enum_as_flags (tmod_enum name values) = tg_enum_as_flags name values"
    by (fact tmod_enum_to_tg_enum_as_flags_proj)
next
  fix TmodX
  show "ET (tmod_enum_to_tg_enum_as_flags (tmod_enum name values)) \<subseteq> 
    ET (tmod_enum_to_tg_enum_as_flags (tmod_combine (tmod_enum name values) TmodX))"
  proof
    fix x
    assume "x \<in> ET (tmod_enum_to_tg_enum_as_flags (tmod_enum name values))"
    then have "x \<in> {type (id_to_list name)} \<times> flag ` (\<lambda>x. [snd x]) ` Pair name ` values \<times> {type (id_to_list name)}"
      unfolding tmod_enum_to_tg_enum_as_flags_def tmod_enum_def
      by simp
    then show "x \<in> ET (tmod_enum_to_tg_enum_as_flags (tmod_combine (tmod_enum name values) TmodX))"
      unfolding tmod_enum_to_tg_enum_as_flags_def tmod_enum_def tmod_combine_def
      by auto
  qed
next
  fix TmodX e
  assume "e \<in> ET (tmod_enum_to_tg_enum_as_flags (tmod_enum name values))"
  then have e_def: "e \<in> {type (id_to_list name)} \<times> flag ` (\<lambda>x. [snd x]) ` Pair name ` values \<times> {type (id_to_list name)}"
    unfolding tmod_enum_to_tg_enum_as_flags_def tmod_enum_def
    by simp
  then have mult_def: "mult (tmod_enum_to_tg_enum_as_flags (tmod_enum name values)) e = (\<^bold>0..\<^bold>1, \<^bold>0..\<^bold>1)"
    unfolding tmod_enum_to_tg_enum_as_flags_def tmod_enum_def
    by simp
  have "mult (tmod_enum_to_tg_enum_as_flags (tmod_combine (tmod_enum name values) TmodX)) e = (\<^bold>0..\<^bold>1, \<^bold>0..\<^bold>1)"
    using e_def
    unfolding tmod_enum_to_tg_enum_as_flags_def tmod_enum_def tmod_combine_def
    by auto
  then show "mult (tmod_enum_to_tg_enum_as_flags (tmod_enum name values)) e =
    mult (tmod_enum_to_tg_enum_as_flags (tmod_combine (tmod_enum name values) TmodX)) e"
    using mult_def
    by simp
qed (simp_all add: tmod_enum_to_tg_enum_as_flags_def tmod_enum_def tg_enum_as_flags_def tmod_combine_def)

definition tg_enum_as_flags_to_tmod_enum :: "('t list) type_graph \<Rightarrow> 't type_model" where
  "tg_enum_as_flags_to_tmod_enum TG = \<lparr>
    Class = {},
    Enum = list_to_id ` unlabel ` NT TG,
    UserDataType = {},
    Field = {},
    FieldSig = (\<lambda>x. undefined),
    EnumValue = (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET TG,
    Inh = {},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tg_enum_as_flags_to_tmod_enum_proj:
  shows "tg_enum_as_flags_to_tmod_enum (tg_enum_as_flags name values) = tmod_enum name values"
proof-
  have et_proj: "(\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET (tg_enum_as_flags name values) = Pair name ` values"
  proof
    show "(\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET (tg_enum_as_flags name values) \<subseteq> Pair name ` values"
    proof
      fix x
      assume "x \<in> (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET (tg_enum_as_flags name values)"
      then have "x \<in> (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` 
        (\<lambda>x. (LabDef.type (id_to_list name), x, LabDef.type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values"
        unfolding tg_enum_as_flags_def
        by simp
      then have "x \<in> (\<lambda>x. (name, x)) ` values"
        using id_to_list_inverse
        by fastforce
      then show "x \<in> Pair name ` values"
        by simp
    qed
  next
    show "Pair name ` values \<subseteq> (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET (tg_enum_as_flags name values)"
    proof
      fix x
      assume "x \<in> Pair name ` values"
      then have "x \<in> (\<lambda>x. (name, x)) ` values"
        by simp
      then have "x \<in> (\<lambda>x. (list_to_id (id_to_list name), x)) ` values"
        using id_to_list_inverse
        by metis
      then have "x \<in> (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` 
        (\<lambda>x. (LabDef.type (id_to_list name), x, LabDef.type (id_to_list name))) ` flag ` (\<lambda>x. [x]) ` values"
        by force
      then show "x \<in> (\<lambda>x. (list_to_id (unlabel (src x)), last (unlabel (lab x)))) ` ET (tg_enum_as_flags name values)"
        unfolding tg_enum_as_flags_def
        by simp
    qed
  qed
  show "tg_enum_as_flags_to_tmod_enum (tg_enum_as_flags name values) = tmod_enum name values"
    unfolding tg_enum_as_flags_to_tmod_enum_def tmod_enum_def
    using et_proj
    unfolding tg_enum_as_flags_def
    by (simp add: id_to_list_inverse)
qed

lemma tg_enum_as_flags_to_tmod_enum_func:
  shows "tmod_combine_mapping_function (tg_enum_as_flags_to_tmod_enum) (tg_enum_as_flags name values) (tmod_enum name values)"
proof (intro tmod_combine_mapping_function.intro)
  show "tg_enum_as_flags_to_tmod_enum (tg_enum_as_flags name values) = tmod_enum name values"
    by (fact tg_enum_as_flags_to_tmod_enum_proj)
next
  fix TGX
  show "EnumValue (tg_enum_as_flags_to_tmod_enum (tg_enum_as_flags name values)) \<subseteq>
    EnumValue (tg_enum_as_flags_to_tmod_enum (tg_combine (tg_enum_as_flags name values) TGX))"
    unfolding tg_enum_as_flags_to_tmod_enum_def tg_combine_def
    by fastforce
qed (simp_all add: tg_enum_as_flags_to_tmod_enum_def tg_enum_as_flags_def tg_combine_def)

end