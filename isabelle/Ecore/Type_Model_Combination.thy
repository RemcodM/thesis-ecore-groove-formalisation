theory Type_Model_Combination
  imports 
    Main
    HOL.Transitive_Closure
    Multiplicity
    Type_Model
begin

section "Combining Type Models"


subsection "Definition of field signatures for combined type models"

definition tmod_combine_fieldsig :: "('nt) type_model \<Rightarrow> ('nt) type_model \<Rightarrow> 'nt Id \<times> 'nt \<Rightarrow> 'nt TypeDef \<times> multiplicity" where
  "tmod_combine_fieldsig Tmod1 Tmod2 field \<equiv> (
    if field \<in> Field Tmod1 \<inter> Field Tmod2 \<and> fst (FieldSig Tmod1 field) = fst (FieldSig Tmod2 field) then
      (fst (FieldSig Tmod1 field), snd (FieldSig Tmod1 field) \<sqinter> snd (FieldSig Tmod2 field))
    else if field \<in> Field Tmod1 \<inter> Field Tmod2 \<and> fst (FieldSig Tmod1 field) \<noteq> fst (FieldSig Tmod2 field) then
      (invalid, \<^emph>..\<^bold>0)
    else if field \<in> Field Tmod1 - Field Tmod2 then
      FieldSig Tmod1 field
    else if field \<in> Field Tmod2 - Field Tmod1 then
      FieldSig Tmod2 field
    else
      undefined)"

lemma tmod_combine_fieldsig_commute:
  shows "tmod_combine_fieldsig Tmod1 Tmod2 = tmod_combine_fieldsig Tmod2 Tmod1"
proof
  fix x
  show "tmod_combine_fieldsig Tmod1 Tmod2 x = tmod_combine_fieldsig Tmod2 Tmod1 x"
    unfolding tmod_combine_fieldsig_def
    by simp
qed

lemma tmod_combine_fieldsig_idemp:
  assumes structure_fieldsig_domain: "\<And>f. f \<notin> Field Tmod \<Longrightarrow> FieldSig Tmod f = undefined"
  shows "tmod_combine_fieldsig Tmod Tmod = FieldSig Tmod"
proof
  fix x
  show "tmod_combine_fieldsig Tmod Tmod x = FieldSig Tmod x"
    unfolding tmod_combine_fieldsig_def
    by (simp add: structure_fieldsig_domain)
qed


subsection "Definition of constant types for combined type models"

definition tmod_combine_const_type :: "('nt) type_model \<Rightarrow> ('nt) type_model \<Rightarrow> 'nt Id \<Rightarrow> 'nt TypeDef" where
  "tmod_combine_const_type Tmod1 Tmod2 c \<equiv> (
    if c \<in> Constant Tmod1 \<inter> Constant Tmod2 \<and> ConstType Tmod1 c = ConstType Tmod2 c then
      ConstType Tmod1 c
    else if c \<in> Constant Tmod1 \<inter> Constant Tmod2 \<and> ConstType Tmod1 c \<noteq> ConstType Tmod2 c then
      invalid
    else if c \<in> Constant Tmod1 - Constant Tmod2 then
      ConstType Tmod1 c
    else if c \<in> Constant Tmod2 - Constant Tmod1 then
      ConstType Tmod2 c
    else
      undefined)"

lemma tmod_combine_const_type_commute:
  shows "tmod_combine_const_type Tmod1 Tmod2 = tmod_combine_const_type Tmod2 Tmod1"
proof
  fix x
  show "tmod_combine_const_type Tmod1 Tmod2 x = tmod_combine_const_type Tmod2 Tmod1 x"
    unfolding tmod_combine_const_type_def
    by simp
qed

lemma tmod_combine_const_type_idemp:
  assumes structure_consttype_domain: "\<And>c. c \<notin> Constant Tmod \<Longrightarrow> ConstType Tmod c = undefined"
  shows "tmod_combine_const_type Tmod Tmod = ConstType Tmod"
proof
  fix x
  show "tmod_combine_const_type Tmod Tmod x = ConstType Tmod x"
    unfolding tmod_combine_const_type_def
    by (simp add: structure_consttype_domain)
qed


subsection "Definition of properties for combined type models"

inductive_set tmod_combine_prop :: "'nt type_model \<Rightarrow> 'nt type_model \<Rightarrow> 'nt PropertyDef set"
  for Tmod1 Tmod2 :: "'nt type_model"
  where
    abstract_property_tmod1: "abstract c \<in> Prop Tmod1 \<Longrightarrow> c \<notin> Class Tmod2 \<Longrightarrow> abstract c \<in> tmod_combine_prop Tmod1 Tmod2" |
    abstract_property_tmod2: "abstract c \<in> Prop Tmod2 \<Longrightarrow> c \<notin> Class Tmod1 \<Longrightarrow> abstract c \<in> tmod_combine_prop Tmod1 Tmod2" |
    abstract_property_both: "abstract c \<in> Prop Tmod1 \<Longrightarrow> abstract c \<in> Prop Tmod2 \<Longrightarrow> abstract c \<in> tmod_combine_prop Tmod1 Tmod2" |
    containment_property_tmod1: "containment r \<in> Prop Tmod1 \<Longrightarrow> containment r \<in> tmod_combine_prop Tmod1 Tmod2" |
    containment_property_tmod2: "containment r \<in> Prop Tmod2 \<Longrightarrow> containment r \<in> tmod_combine_prop Tmod1 Tmod2" |
    default_value_property_tmod1: "defaultValue f v \<in> Prop Tmod1 \<Longrightarrow> f \<notin> Field Tmod2 \<Longrightarrow> defaultValue f v \<in> tmod_combine_prop Tmod1 Tmod2" |
    default_value_property_tmod2: "defaultValue f v \<in> Prop Tmod2 \<Longrightarrow> f \<notin> Field Tmod1 \<Longrightarrow> defaultValue f v \<in> tmod_combine_prop Tmod1 Tmod2" |
    default_value_property_both: "defaultValue f v \<in> Prop Tmod1 \<Longrightarrow> defaultValue f v \<in> Prop Tmod2 \<Longrightarrow> defaultValue f v \<in> tmod_combine_prop Tmod1 Tmod2" |
    identity_property_tmod1: "identity c A \<in> Prop Tmod1 \<Longrightarrow> c \<notin> Class Tmod2 \<Longrightarrow> identity c A \<in> tmod_combine_prop Tmod1 Tmod2" |
    identity_property_tmod2: "identity c A \<in> Prop Tmod2 \<Longrightarrow> c \<notin> Class Tmod1 \<Longrightarrow> identity c A \<in> tmod_combine_prop Tmod1 Tmod2" |
    identity_property_both: "identity c A \<in> Prop Tmod1 \<Longrightarrow> identity c A \<in> Prop Tmod2 \<Longrightarrow> identity c A \<in> tmod_combine_prop Tmod1 Tmod2" |
    keyset_property_tmod1: "keyset r A \<in> Prop Tmod1 \<Longrightarrow> r \<notin> Field Tmod2 \<Longrightarrow> keyset r A \<in> tmod_combine_prop Tmod1 Tmod2" |
    keyset_property_tmod2: "keyset r A \<in> Prop Tmod2 \<Longrightarrow> r \<notin> Field Tmod1 \<Longrightarrow> keyset r A \<in> tmod_combine_prop Tmod1 Tmod2" |
    keyset_property_both: "keyset r A \<in> Prop Tmod1 \<Longrightarrow> keyset r A \<in> Prop Tmod2 \<Longrightarrow> keyset r A \<in> tmod_combine_prop Tmod1 Tmod2" |
    opposite_property_tmod1: "opposite r1 r2 \<in> Prop Tmod1 \<Longrightarrow> r1 \<notin> Field Tmod2 \<Longrightarrow> r2 \<notin> Field Tmod2 \<Longrightarrow> opposite r1 r2 \<in> tmod_combine_prop Tmod1 Tmod2" |
    opposite_property_tmod2: "opposite r1 r2 \<in> Prop Tmod2 \<Longrightarrow> r1 \<notin> Field Tmod1 \<Longrightarrow> r2 \<notin> Field Tmod1 \<Longrightarrow> opposite r1 r2 \<in> tmod_combine_prop Tmod1 Tmod2" |
    opposite_property_both: "opposite r1 r2 \<in> Prop Tmod1 \<Longrightarrow> opposite r1 r2 \<in> Prop Tmod2 \<Longrightarrow> opposite r1 r2 \<in> tmod_combine_prop Tmod1 Tmod2" |
    readonly_property_tmod1: "readonly f \<in> Prop Tmod1 \<Longrightarrow> f \<notin> Field Tmod2 \<Longrightarrow> readonly f \<in> tmod_combine_prop Tmod1 Tmod2" |
    readonly_property_tmod2: "readonly f \<in> Prop Tmod2 \<Longrightarrow> f \<notin> Field Tmod1 \<Longrightarrow> readonly f \<in> tmod_combine_prop Tmod1 Tmod2" |
    readonly_property_both: "readonly f \<in> Prop Tmod1 \<Longrightarrow> readonly f \<in> Prop Tmod2 \<Longrightarrow> readonly f \<in> tmod_combine_prop Tmod1 Tmod2"

lemma tmod_combine_prop_identity[simp]: "tmod_combine_prop tmod_empty Tmod = Prop Tmod"
proof
  show "tmod_combine_prop tmod_empty Tmod \<subseteq> Prop Tmod"
  proof
    fix x
    assume "x \<in> tmod_combine_prop tmod_empty Tmod"
    then show "x \<in> Prop Tmod"
      by (induct) (simp_all)
  qed
next
  show "Prop Tmod \<subseteq> tmod_combine_prop tmod_empty Tmod"
  proof
    fix x
    assume "x \<in> Prop Tmod"
    then show "x \<in> tmod_combine_prop tmod_empty Tmod"
    proof (induct x)
      case (abstract x)
      then show ?case
        by (simp add: tmod_combine_prop.abstract_property_tmod2)
    next
      case (containment x)
      then show ?case
        by (fact tmod_combine_prop.containment_property_tmod2)
    next
      case (defaultValue x1a x2a)
      then show ?case
        by (simp add: tmod_combine_prop.default_value_property_tmod2)
    next
      case (identity x)
      then show ?case
        by (simp add: tmod_combine_prop.identity_property_tmod2)
    next
      case (keyset x1a x2a)
      then show ?case
        by (simp add: tmod_combine_prop.keyset_property_tmod2)
    next
      case (opposite x1a x2a)
      then show ?case
        by (simp add: tmod_combine_prop.opposite_property_tmod2)
    next
      case (readonly x)
      then show ?case
        by (simp add: tmod_combine_prop.readonly_property_tmod2)
    qed
  qed
qed

lemma tmod_combine_prop_commute[simp]: "tmod_combine_prop Tmod1 Tmod2 = tmod_combine_prop Tmod2 Tmod1"
proof
  show "tmod_combine_prop Tmod1 Tmod2 \<subseteq> tmod_combine_prop Tmod2 Tmod1"
  proof
    fix x
    assume "x \<in> tmod_combine_prop Tmod1 Tmod2"
    then show "x \<in> tmod_combine_prop Tmod2 Tmod1"
      by (induct) (simp_all add: tmod_combine_prop.intros)
  qed
next
  show "tmod_combine_prop Tmod2 Tmod1 \<subseteq> tmod_combine_prop Tmod1 Tmod2"
  proof
    fix x
    assume "x \<in> tmod_combine_prop Tmod2 Tmod1"
    then show "x \<in> tmod_combine_prop Tmod1 Tmod2"
      by (induct) (simp_all add: tmod_combine_prop.intros)
  qed
qed

lemma tmod_combine_prop_idemp[simp]: "tmod_combine_prop Tmod1 Tmod1 = Prop Tmod1"
proof
  show "tmod_combine_prop Tmod1 Tmod1 \<subseteq> Prop Tmod1"
  proof
    fix x
    assume "x \<in> tmod_combine_prop Tmod1 Tmod1"
    then show "x \<in> Prop Tmod1"
      by (induct) (simp_all)
  qed
next
  show "Prop Tmod1 \<subseteq> tmod_combine_prop Tmod1 Tmod1"
  proof
    fix x
    assume "x \<in> Prop Tmod1"
    then show "x \<in> tmod_combine_prop Tmod1 Tmod1"
      by (induct x) (simp_all add: tmod_combine_prop.intros)
  qed
qed


subsection "Combination of type models"

definition tmod_combine :: "'nt type_model \<Rightarrow> 'nt type_model \<Rightarrow> 'nt type_model" where
  "tmod_combine Tmod1 Tmod2 \<equiv> \<lparr>
    Class = Class Tmod1 \<union> Class Tmod2,
    Enum = Enum Tmod1 \<union> Enum Tmod2,
    UserDataType = UserDataType Tmod1 \<union> UserDataType Tmod2,
    Field = Field Tmod1 \<union> Field Tmod2,
    FieldSig = tmod_combine_fieldsig Tmod1 Tmod2,
    EnumValue = EnumValue Tmod1 \<union> EnumValue Tmod2,
    Inh = Inh Tmod1 \<union> Inh Tmod2,
    Prop = tmod_combine_prop Tmod1 Tmod2,
    Constant = Constant Tmod1 \<union> Constant Tmod2,
    ConstType = tmod_combine_const_type Tmod1 Tmod2
  \<rparr>"

lemma tmod_combine_identity:
  assumes structure_fieldsig_domain: "\<And>f. f \<notin> Field Tmod \<Longrightarrow> FieldSig Tmod f = undefined"
  assumes structure_consttype_domain: "\<And>c. c \<notin> Constant Tmod \<Longrightarrow> ConstType Tmod c = undefined"
  shows "tmod_combine tmod_empty Tmod = truncate Tmod"
  unfolding truncate_def tmod_combine_def tmod_combine_fieldsig_def tmod_combine_const_type_def
  using structure_fieldsig_domain structure_consttype_domain tmod_combine_prop_identity
  by fastforce

lemma tmod_combine_identity_alt:
  assumes type_model_correct: "type_model Tmod"
  shows "tmod_combine tmod_empty Tmod = truncate Tmod"
  using tmod_combine_identity type_model.structure_consttype_domain type_model.structure_fieldsig_domain type_model_correct
  by blast

lemma tmod_combine_commute: "tmod_combine Tmod1 Tmod2 = tmod_combine Tmod2 Tmod1"
  using tmod_combine_const_type_commute tmod_combine_fieldsig_commute tmod_combine_prop_commute
  unfolding tmod_combine_def
  by blast

lemma tmod_combine_idemp: 
  assumes structure_fieldsig_domain: "\<And>f. f \<notin> Field Tmod \<Longrightarrow> FieldSig Tmod f = undefined"
  assumes structure_consttype_domain: "\<And>c. c \<notin> Constant Tmod \<Longrightarrow> ConstType Tmod c = undefined"
  shows "tmod_combine Tmod Tmod = truncate Tmod"
  unfolding truncate_def tmod_combine_def
  using tmod_combine_const_type_idemp tmod_combine_fieldsig_idemp assms
  by auto

lemma tmod_combine_idemp_alt: 
  assumes type_model_correct: "type_model Tmod"
  shows "tmod_combine Tmod Tmod = truncate Tmod"
proof (intro tmod_combine_idemp)
  show "\<And>f. f \<notin> type_model.Field Tmod \<Longrightarrow> FieldSig Tmod f = undefined"
    using type_model_correct type_model.structure_fieldsig_domain
    by blast
next
  show "\<And>c. c \<notin> Constant Tmod \<Longrightarrow> ConstType Tmod c = undefined"
    using type_model_correct type_model.structure_consttype_domain
    by blast
qed


subsection "Proofs related to the combination of two type models"

lemma tmod_combine_proper_class_type[simp]: 
  shows "ProperClassType (tmod_combine Tmod1 Tmod2) = ProperClassType Tmod1 \<union> ProperClassType Tmod2"
proof
  show "ProperClassType (tmod_combine Tmod1 Tmod2) \<subseteq> ProperClassType Tmod1 \<union> ProperClassType Tmod2"
  proof
    fix x
    assume "x \<in> ProperClassType (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> ProperClassType Tmod1 \<union> ProperClassType Tmod2"
    proof (induct)
      case (rule_proper_classes c)
      then show ?case
        using ProperClassType.rule_proper_classes UnE UnI1 UnI2 select_convs(1) tmod_combine_def
        by metis
    qed
  qed
next
  show "ProperClassType Tmod1 \<union> ProperClassType Tmod2 \<subseteq> ProperClassType (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> ProperClassType Tmod1 \<union> ProperClassType Tmod2"
    then show "x \<in> ProperClassType (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> ProperClassType Tmod1"
      then show "x \<in> ProperClassType (tmod_combine Tmod1 Tmod2)"
        using ProperClassType.simps Un_iff select_convs(1) tmod_combine_def
        by metis
    next
      assume "x \<in> ProperClassType Tmod2"
      then show "x \<in> ProperClassType (tmod_combine Tmod1 Tmod2)"
        using ProperClassType.simps Un_iff select_convs(1) tmod_combine_def
        by metis
    qed
  qed
qed

lemma tmod_combine_nullable_class_type[simp]: 
  shows "NullableClassType (tmod_combine Tmod1 Tmod2) = NullableClassType Tmod1 \<union> NullableClassType Tmod2"
proof
  show "NullableClassType (tmod_combine Tmod1 Tmod2) \<subseteq> NullableClassType Tmod1 \<union> NullableClassType Tmod2"
  proof
    fix x
    assume "x \<in> NullableClassType (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> NullableClassType Tmod1 \<union> NullableClassType Tmod2"
    proof (induct)
      case (rule_nullable_classes c)
      then show ?case
        using NullableClassType.rule_nullable_classes UnE UnI1 UnI2 select_convs(1) tmod_combine_def
        by metis
    qed
  qed
next
  show "NullableClassType Tmod1 \<union> NullableClassType Tmod2 \<subseteq> NullableClassType (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> NullableClassType Tmod1 \<union> NullableClassType Tmod2"
    then show "x \<in> NullableClassType (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> NullableClassType Tmod1"
      then show "x \<in> NullableClassType (tmod_combine Tmod1 Tmod2)"
        using NullableClassType.simps Un_iff select_convs(1) tmod_combine_def
        by metis
    next
      assume "x \<in> NullableClassType Tmod2"
      then show "x \<in> NullableClassType (tmod_combine Tmod1 Tmod2)"
        using NullableClassType.simps Un_iff select_convs(1) tmod_combine_def
        by metis
    qed
  qed
qed

lemma tmod_combine_class_type[simp]:
  shows "ClassType (tmod_combine Tmod1 Tmod2) = ClassType Tmod1 \<union> ClassType Tmod2"
  unfolding ClassType_def
  by auto

lemma tmod_combine_enum_type[simp]: 
  shows "EnumType (tmod_combine Tmod1 Tmod2) = EnumType Tmod1 \<union> EnumType Tmod2"
proof
  show "EnumType (tmod_combine Tmod1 Tmod2) \<subseteq> EnumType Tmod1 \<union> EnumType Tmod2"
  proof
    fix x
    assume "x \<in> EnumType (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> EnumType Tmod1 \<union> EnumType Tmod2"
    proof (induct)
      case (rule_enum_types e)
      then show ?case
        using EnumType.rule_enum_types UnE UnI1 UnI2 select_convs(2) tmod_combine_def
        by metis
    qed
  qed
next
  show "EnumType Tmod1 \<union> EnumType Tmod2 \<subseteq> EnumType (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> EnumType Tmod1 \<union> EnumType Tmod2"
    then show "x \<in> EnumType (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> EnumType Tmod1"
      then show "x \<in> EnumType (tmod_combine Tmod1 Tmod2)"
        using EnumType.simps Un_iff select_convs(2) tmod_combine_def
        by metis
    next
      assume "x \<in> EnumType Tmod2"
      then show "x \<in> EnumType (tmod_combine Tmod1 Tmod2)"
        using EnumType.simps Un_iff select_convs(2) tmod_combine_def
        by metis
    qed
  qed
qed

lemma tmod_combine_userdatatype_type[simp]: 
  shows "UserDataTypeType (tmod_combine Tmod1 Tmod2) = UserDataTypeType Tmod1 \<union> UserDataTypeType Tmod2"
proof
  show "UserDataTypeType (tmod_combine Tmod1 Tmod2) \<subseteq> UserDataTypeType Tmod1 \<union> UserDataTypeType Tmod2"
  proof
    fix x
    assume "x \<in> UserDataTypeType (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> UserDataTypeType Tmod1 \<union> UserDataTypeType Tmod2"
    proof (induct)
      case (rule_userdatatypes u)
      then show ?case
        using UserDataTypeType.rule_userdatatypes UnE UnI1 UnI2 select_convs(3) tmod_combine_def
        by metis
    qed
  qed
next
  show "UserDataTypeType Tmod1 \<union> UserDataTypeType Tmod2 \<subseteq> UserDataTypeType (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> UserDataTypeType Tmod1 \<union> UserDataTypeType Tmod2"
    then show "x \<in> UserDataTypeType (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> UserDataTypeType Tmod1"
      then show "x \<in> UserDataTypeType (tmod_combine Tmod1 Tmod2)"
        using UserDataTypeType.simps Un_iff select_convs(3) tmod_combine_def
        by metis
    next
      assume "x \<in> UserDataTypeType Tmod2"
      then show "x \<in> UserDataTypeType (tmod_combine Tmod1 Tmod2)"
        using UserDataTypeType.simps Un_iff select_convs(3) tmod_combine_def
        by metis
    qed
  qed
qed

lemma tmod_combine_non_container_type[simp]:
  shows "NonContainerType (tmod_combine Tmod1 Tmod2) = NonContainerType Tmod1 \<union> NonContainerType Tmod2"
  unfolding NonContainerType_def
  by auto

lemma tmod_combine_container_type[simp]:
  shows "ContainerType (tmod_combine Tmod1 Tmod2) = ContainerType Tmod1 \<union> ContainerType Tmod2"
proof
  show "ContainerType (tmod_combine Tmod1 Tmod2) \<subseteq> ContainerType Tmod1 \<union> ContainerType Tmod2"
  proof
    fix x
    assume "x \<in> ContainerType (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> ContainerType Tmod1 \<union> ContainerType Tmod2"
    proof (induct)
      case (rule_bagof_type t)
      then show ?case
        using ContainerType.rule_bagof_type 
        by auto
    next
      case (rule_setof_type t)
      then show ?case
        using ContainerType.rule_setof_type 
        by auto
    next
      case (rule_seqof_type t)
      then show ?case
        using ContainerType.rule_seqof_type 
        by auto
    next
      case (rule_ordof_type t)
      then show ?case
        using ContainerType.rule_ordof_type
        by auto
    next
      case (rule_bagof_container t)
      then show ?case
        using ContainerType.rule_bagof_container
        by blast
    next
      case (rule_setof_container t)
      then show ?case
        using ContainerType.rule_setof_container
        by blast
    next
      case (rule_seqof_container t)
      then show ?case
        using ContainerType.rule_seqof_container
        by blast
    next
      case (rule_ordof_container t)
      then show ?case
        using ContainerType.rule_ordof_container
        by blast
    qed
  qed
next
  show "ContainerType Tmod1 \<union> ContainerType Tmod2 \<subseteq> ContainerType (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> ContainerType Tmod1 \<union> ContainerType Tmod2"
    then show "x \<in> ContainerType (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> ContainerType Tmod1"
      then show "x \<in> ContainerType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_bagof_type t)
        then show ?case
          by (simp add: ContainerType.rule_bagof_type)
      next
        case (rule_setof_type t)
        then show ?case
          by (simp add: ContainerType.rule_setof_type)
      next
        case (rule_seqof_type t)
        then show ?case
          by (simp add: ContainerType.rule_seqof_type)
      next
        case (rule_ordof_type t)
        then show ?case
          by (simp add: ContainerType.rule_ordof_type)
      next
        case (rule_bagof_container t)
        then show ?case
          using ContainerType.rule_bagof_container
          by auto
      next
        case (rule_setof_container t)
        then show ?case
          using ContainerType.rule_setof_container
          by auto
      next
        case (rule_seqof_container t)
        then show ?case
          using ContainerType.rule_seqof_container
          by auto
      next
        case (rule_ordof_container t)
        then show ?case
          using ContainerType.rule_ordof_container
          by auto
      qed
    next
      assume "x \<in> ContainerType Tmod2"
      then show "x \<in> ContainerType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_bagof_type t)
        then show ?case
          by (simp add: ContainerType.rule_bagof_type)
      next
        case (rule_setof_type t)
        then show ?case
          by (simp add: ContainerType.rule_setof_type)
      next
        case (rule_seqof_type t)
        then show ?case
          by (simp add: ContainerType.rule_seqof_type)
      next
        case (rule_ordof_type t)
        then show ?case
          by (simp add: ContainerType.rule_ordof_type)
      next
        case (rule_bagof_container t)
        then show ?case
          using ContainerType.rule_bagof_container
          by auto
      next
        case (rule_setof_container t)
        then show ?case
          using ContainerType.rule_setof_container
          by auto
      next
        case (rule_seqof_container t)
        then show ?case
          using ContainerType.rule_seqof_container
          by auto
      next
        case (rule_ordof_container t)
        then show ?case
          using ContainerType.rule_ordof_container
          by auto
      qed
    qed
  qed
qed

lemma tmod_combine_type[simp]: "Type (tmod_combine Tmod1 Tmod2) = Type Tmod1 \<union> Type Tmod2"
  unfolding Type_def
  by auto

lemma tmod_combine_attr_type[simp]: "AttrType (tmod_combine Tmod1 Tmod2) = AttrType Tmod1 \<union> AttrType Tmod2"
proof
  show "AttrType (tmod_combine Tmod1 Tmod2) \<subseteq> AttrType Tmod1 \<union> AttrType Tmod2"
  proof
    fix x
    assume "x \<in> AttrType (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> AttrType Tmod1 \<union> AttrType Tmod2"
    proof (induct)
      case (rule_datatypes t)
      then show ?case
        by (simp add: AttrType.rule_datatypes)
    next
      case (rule_enum_types t)
      then show ?case
        using AttrType.rule_enum_types
        by auto
    next
      case (rule_userdatatypes t)
      then show ?case
        using AttrType.rule_userdatatypes
        by auto
    next
      case (rule_bagof_attributes t)
      then show ?case
        using AttrType.rule_bagof_attributes
        by blast
    next
      case (rule_setof_attributes t)
      then show ?case
        using AttrType.rule_setof_attributes
        by blast
    next
      case (rule_seqof_attributes t)
      then show ?case
        using AttrType.rule_seqof_attributes
        by blast
    next
      case (rule_ordof_attributes t)
      then show ?case
        using AttrType.rule_ordof_attributes
        by blast
    qed
  qed
next
  show "AttrType Tmod1 \<union> AttrType Tmod2 \<subseteq> AttrType (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> AttrType Tmod1 \<union> AttrType Tmod2"
    then show "x \<in> AttrType (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> AttrType Tmod1"
      then show "x \<in> AttrType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_datatypes t)
        then show ?case
          by (fact AttrType.rule_datatypes)
      next
        case (rule_enum_types t)
        then show ?case
          by (simp add: AttrType.rule_enum_types)
      next
        case (rule_userdatatypes t)
        then show ?case
          by (simp add: AttrType.rule_userdatatypes)
      next
        case (rule_bagof_attributes t)
        then show ?case
          using AttrType.rule_bagof_attributes
          by blast
      next
        case (rule_setof_attributes t)
        then show ?case
          using AttrType.rule_setof_attributes
          by blast
      next
        case (rule_seqof_attributes t)
        then show ?case
          using AttrType.rule_seqof_attributes
          by blast
      next
        case (rule_ordof_attributes t)
        then show ?case
          using AttrType.rule_ordof_attributes
          by blast
      qed
    next
      assume "x \<in> AttrType Tmod2"
      then show "x \<in> AttrType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_datatypes t)
        then show ?case
          by (fact AttrType.rule_datatypes)
      next
        case (rule_enum_types t)
        then show ?case
          by (simp add: AttrType.rule_enum_types)
      next
        case (rule_userdatatypes t)
        then show ?case
          by (simp add: AttrType.rule_userdatatypes)
      next
        case (rule_bagof_attributes t)
        then show ?case
          using AttrType.rule_bagof_attributes
          by blast
      next
        case (rule_setof_attributes t)
        then show ?case
          using AttrType.rule_setof_attributes
          by blast
      next
        case (rule_seqof_attributes t)
        then show ?case
          using AttrType.rule_seqof_attributes
          by blast
      next
        case (rule_ordof_attributes t)
        then show ?case
          using AttrType.rule_ordof_attributes
          by blast
      qed
    qed
  qed
qed

lemma tmod_combine_attr_type_preserved[simp]: "\<And>t. t \<in> AttrType Tmod1 \<Longrightarrow> t \<in> Type Tmod2 \<Longrightarrow> t \<in> AttrType Tmod2"
proof-
  fix t
  assume t_type_in_tmod2: "t \<in> Type Tmod2"
  assume "t \<in> AttrType Tmod1"
  then show "t \<in> AttrType Tmod2"
    using t_type_in_tmod2
  proof (induct)
    case (rule_datatypes t)
    then show ?case
      using AttrType.rule_datatypes
      by blast
  next
    case (rule_enum_types t)
    then show ?case
      using enum_type_member enums_are_not_relations_alt relation_member relations_altdef_eq 
      by blast
  next
    case (rule_userdatatypes t)
    then show ?case
      using userdatatype_type_member userdatatypes_are_not_relations_alt relation_member relations_altdef_eq 
      by blast
  next
    case (rule_bagof_attributes t)
    then show ?case
      using AttrType.rule_bagof_attributes relation_bags_have_relation_types_alt relation_member relations_altdef_eq relations_are_types
      by blast
  next
    case (rule_setof_attributes t)
    then show ?case
      using AttrType.rule_setof_attributes relation_sets_have_relation_types_alt relation_member relations_altdef_eq relations_are_types
      by blast
  next
    case (rule_seqof_attributes t)
    then show ?case
      using AttrType.rule_seqof_attributes relation_seqs_have_relation_types_alt relation_member relations_altdef_eq relations_are_types
      by blast
  next
    case (rule_ordof_attributes t)
    then show ?case
      using AttrType.rule_ordof_attributes relation_ords_have_relation_types_alt relation_member relations_altdef_eq relations_are_types
      by blast
  qed
qed

lemma tmod_combine_rel_type_alt[simp]: "RelType_altdef (tmod_combine Tmod1 Tmod2) = RelType_altdef Tmod1 \<union> RelType_altdef Tmod2"
proof
  show "RelType_altdef (tmod_combine Tmod1 Tmod2) \<subseteq> RelType_altdef Tmod1 \<union> RelType_altdef Tmod2"
  proof
    fix x
    assume "x \<in> RelType_altdef (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> RelType_altdef Tmod1 \<union> RelType_altdef Tmod2"
    proof (induct)
      case (rule_class_types t)
      then show ?case
        using RelType_altdef.rule_class_types
        by auto
    next
      case (rule_bagof_relations t)
      then show ?case
        using RelType_altdef.rule_bagof_relations
        by blast
    next
      case (rule_setof_relations t)
      then show ?case
        using RelType_altdef.rule_setof_relations
        by blast
    next
      case (rule_seqof_relations t)
      then show ?case
        using RelType_altdef.rule_seqof_relations 
        by blast
    next
      case (rule_ordof_relations t)
      then show ?case
        using RelType_altdef.rule_ordof_relations
        by blast
    qed
  qed
next
  show "RelType_altdef Tmod1 \<union> RelType_altdef Tmod2 \<subseteq> RelType_altdef (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> RelType_altdef Tmod1 \<union> RelType_altdef Tmod2"
    then show "x \<in> RelType_altdef (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> RelType_altdef Tmod1"
      then show "x \<in> RelType_altdef (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_class_types t)
        then show ?case
          by (simp add: RelType_altdef.rule_class_types)
      next
        case (rule_bagof_relations t)
        then show ?case
          using RelType_altdef.rule_bagof_relations
          by blast
      next
        case (rule_setof_relations t)
        then show ?case
          using RelType_altdef.rule_setof_relations
          by blast
      next
        case (rule_seqof_relations t)
        then show ?case
          using RelType_altdef.rule_seqof_relations
          by blast
      next
        case (rule_ordof_relations t)
        then show ?case
          using RelType_altdef.rule_ordof_relations
          by blast
      qed
    next
      assume "x \<in> RelType_altdef Tmod2"
      then show "x \<in> RelType_altdef (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_class_types t)
        then show ?case
          by (simp add: RelType_altdef.rule_class_types)
      next
        case (rule_bagof_relations t)
        then show ?case
          using RelType_altdef.rule_bagof_relations
          by blast
      next
        case (rule_setof_relations t)
        then show ?case
          using RelType_altdef.rule_setof_relations
          by blast
      next
        case (rule_seqof_relations t)
        then show ?case
          using RelType_altdef.rule_seqof_relations
          by blast
      next
        case (rule_ordof_relations t)
        then show ?case
          using RelType_altdef.rule_ordof_relations
          by blast
      qed
    qed
  qed
qed

lemma tmod_combine_rel_type[simp]: "RelType (tmod_combine Tmod1 Tmod2) = RelType Tmod1 \<union> RelType Tmod2"
  by auto

lemma tmod_combine_bag_container_type[simp]:
  shows "BagContainerType (tmod_combine Tmod1 Tmod2) = BagContainerType Tmod1 \<union> BagContainerType Tmod2"
proof
  show "BagContainerType (tmod_combine Tmod1 Tmod2) \<subseteq> BagContainerType Tmod1 \<union> BagContainerType Tmod2"
  proof
    fix x
    assume "x \<in> BagContainerType (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> BagContainerType Tmod1 \<union> BagContainerType Tmod2"
    proof (induct)
      case (rule_bagof_all_type t)
      then have "t \<in> Type Tmod1 \<union> Type Tmod2"
        by simp
      then show ?case
        using BagContainerType.rule_bagof_all_type
        by blast
    qed
  qed
next
  show "BagContainerType Tmod1 \<union> BagContainerType Tmod2 \<subseteq> BagContainerType (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> BagContainerType Tmod1 \<union> BagContainerType Tmod2"
    then show "x \<in> BagContainerType (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> BagContainerType Tmod1"
      then show "x \<in> BagContainerType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_bagof_all_type t)
        then show ?case
          by (simp add: BagContainerType.rule_bagof_all_type)
      qed
    next
      assume "x \<in> BagContainerType Tmod2"
      then show "x \<in> BagContainerType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_bagof_all_type t)
        then show ?case
          by (simp add: BagContainerType.rule_bagof_all_type)
      qed
    qed
  qed
qed

lemma tmod_combine_set_container_type[simp]:
  shows "SetContainerType (tmod_combine Tmod1 Tmod2) = SetContainerType Tmod1 \<union> SetContainerType Tmod2"
proof
  show "SetContainerType (tmod_combine Tmod1 Tmod2) \<subseteq> SetContainerType Tmod1 \<union> SetContainerType Tmod2"
  proof
    fix x
    assume "x \<in> SetContainerType (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> SetContainerType Tmod1 \<union> SetContainerType Tmod2"
    proof (induct)
      case (rule_setof_all_type t)
      then have "t \<in> Type Tmod1 \<union> Type Tmod2"
        by simp
      then show ?case
        using SetContainerType.rule_setof_all_type
        by blast
    qed
  qed
next
  show "SetContainerType Tmod1 \<union> SetContainerType Tmod2 \<subseteq> SetContainerType (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> SetContainerType Tmod1 \<union> SetContainerType Tmod2"
    then show "x \<in> SetContainerType (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> SetContainerType Tmod1"
      then show "x \<in> SetContainerType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_setof_all_type t)
        then show ?case
          by (simp add: SetContainerType.rule_setof_all_type)
      qed
    next
      assume "x \<in> SetContainerType Tmod2"
      then show "x \<in> SetContainerType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_setof_all_type t)
        then show ?case
          by (simp add: SetContainerType.rule_setof_all_type)
      qed
    qed
  qed
qed

lemma tmod_combine_seq_container_type[simp]:
  shows "SeqContainerType (tmod_combine Tmod1 Tmod2) = SeqContainerType Tmod1 \<union> SeqContainerType Tmod2"
proof
  show "SeqContainerType (tmod_combine Tmod1 Tmod2) \<subseteq> SeqContainerType Tmod1 \<union> SeqContainerType Tmod2"
  proof
    fix x
    assume "x \<in> SeqContainerType (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> SeqContainerType Tmod1 \<union> SeqContainerType Tmod2"
    proof (induct)
      case (rule_seqof_all_type t)
      then have "t \<in> Type Tmod1 \<union> Type Tmod2"
        by simp
      then show ?case
        using SeqContainerType.rule_seqof_all_type
        by blast
    qed
  qed
next
  show "SeqContainerType Tmod1 \<union> SeqContainerType Tmod2 \<subseteq> SeqContainerType (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> SeqContainerType Tmod1 \<union> SeqContainerType Tmod2"
    then show "x \<in> SeqContainerType (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> SeqContainerType Tmod1"
      then show "x \<in> SeqContainerType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_seqof_all_type t)
        then show ?case
          by (simp add: SeqContainerType.rule_seqof_all_type)
      qed
    next
      assume "x \<in> SeqContainerType Tmod2"
      then show "x \<in> SeqContainerType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_seqof_all_type t)
        then show ?case
          by (simp add: SeqContainerType.rule_seqof_all_type)
      qed
    qed
  qed
qed

lemma tmod_combine_ord_container_type[simp]:
  shows "OrdContainerType (tmod_combine Tmod1 Tmod2) = OrdContainerType Tmod1 \<union> OrdContainerType Tmod2"
proof
  show "OrdContainerType (tmod_combine Tmod1 Tmod2) \<subseteq> OrdContainerType Tmod1 \<union> OrdContainerType Tmod2"
  proof
    fix x
    assume "x \<in> OrdContainerType (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> OrdContainerType Tmod1 \<union> OrdContainerType Tmod2"
    proof (induct)
      case (rule_ordof_all_type t)
      then have "t \<in> Type Tmod1 \<union> Type Tmod2"
        by simp
      then show ?case
        using OrdContainerType.rule_ordof_all_type
        by blast
    qed
  qed
next
  show "OrdContainerType Tmod1 \<union> OrdContainerType Tmod2 \<subseteq> OrdContainerType (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> OrdContainerType Tmod1 \<union> OrdContainerType Tmod2"
    then show "x \<in> OrdContainerType (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> OrdContainerType Tmod1"
      then show "x \<in> OrdContainerType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_ordof_all_type t)
        then show ?case
          by (simp add: OrdContainerType.rule_ordof_all_type)
      qed
    next
      assume "x \<in> OrdContainerType Tmod2"
      then show "x \<in> OrdContainerType (tmod_combine Tmod1 Tmod2)"
      proof (induct)
        case (rule_ordof_all_type t)
        then show ?case
          by (simp add: OrdContainerType.rule_ordof_all_type)
      qed
    qed
  qed
qed

lemma tmod_combine_subtype_rel_subset_tmod1: "(t1, t2) \<in> subtype_rel Tmod1 \<Longrightarrow> (t1, t2) \<in> subtype_rel (tmod_combine Tmod1 Tmod2)"
proof-
  assume "(t1, t2) \<in> subtype_rel Tmod1"
  then show "(t1, t2) \<in> subtype_rel (tmod_combine Tmod1 Tmod2)"
  proof (induct)
    case (transitivity t1 t2 t3)
    then show ?case
      using Un_iff subtype_rel.transitivity tmod_combine_type
      by metis
  next
    case (reflexivity t1)
    then show ?case
      by (simp add: subtype_rel.reflexivity)
  next
    case (generalization_of_inheritance_nullable c1 c2)
    then show ?case
      by (simp add: subtype_rel.generalization_of_inheritance_nullable tmod_combine_def)
  next
    case (generalization_of_inheritance_proper c1 c2)
    then show ?case
      by (simp add: subtype_rel.generalization_of_inheritance_proper tmod_combine_def)
  next
    case (nullable_proper_classes c1)
    then show ?case
      by (simp add: subtype_rel.nullable_proper_classes tmod_combine_def)
  qed
qed

lemma tmod_combine_subtype_rel_subset_tmod2: "(t1, t2) \<in> subtype_rel Tmod2 \<Longrightarrow> (t1, t2) \<in> subtype_rel (tmod_combine Tmod1 Tmod2)"
  using tmod_combine_commute tmod_combine_subtype_rel_subset_tmod1
  by metis

lemma tmod_combine_subtype_subset_tmod1: "t1 \<sqsubseteq>[Tmod1] t2 \<Longrightarrow> t1 \<sqsubseteq>[tmod_combine Tmod1 Tmod2] t2"
  unfolding subtype_def
  by (fact tmod_combine_subtype_rel_subset_tmod1)

lemma tmod_combine_subtype_subset_tmod2: "t1 \<sqsubseteq>[Tmod2] t2 \<Longrightarrow> t1 \<sqsubseteq>[tmod_combine Tmod1 Tmod2] t2"
  unfolding subtype_def
  by (fact tmod_combine_subtype_rel_subset_tmod2)

lemma tmod_combine_type_func_field_tmod1[simp]: 
  shows "\<And>f. f \<in> Field Tmod1 \<Longrightarrow> f \<notin> Field Tmod2 \<Longrightarrow> type (tmod_combine Tmod1 Tmod2) f = type Tmod1 f"
proof-
  fix f
  assume f_in_field_tmod1: "f \<in> Field Tmod1"
  assume f_not_in_field_tmod2: "f \<notin> Field Tmod2"
  show "type (tmod_combine Tmod1 Tmod2) f = type Tmod1 f"
    using f_in_field_tmod1 f_not_in_field_tmod2
    unfolding type_def tmod_combine_def tmod_combine_fieldsig_def
    by simp
qed

lemma tmod_combine_type_func_field_tmod2[simp]:
  shows "\<And>f. f \<in> Field Tmod2 \<Longrightarrow> f \<notin> Field Tmod1 \<Longrightarrow> type (tmod_combine Tmod1 Tmod2) f = type Tmod2 f"
proof-
  fix f
  assume f_in_field_tmod2: "f \<in> Field Tmod2"
  assume f_not_in_field_tmod1: "f \<notin> Field Tmod1"
  show "type (tmod_combine Tmod1 Tmod2) f = type Tmod2 f"
    using f_in_field_tmod2 f_not_in_field_tmod1
    unfolding type_def tmod_combine_def tmod_combine_fieldsig_def
    by simp
qed

lemma tmod_combine_type_func_field_tmod1_tmod2[simp]: 
  shows "\<And>f. f \<in> Field Tmod1 \<inter> Field Tmod2 \<Longrightarrow> type Tmod1 f = type Tmod2 f \<Longrightarrow> type (tmod_combine Tmod1 Tmod2) f = type Tmod1 f"
proof-
  fix f
  assume f_in_tmods: "f \<in> Field Tmod1 \<inter> Field Tmod2"
  assume "type Tmod1 f = type Tmod2 f"
  then show "type (tmod_combine Tmod1 Tmod2) f = type Tmod1 f"
    unfolding type_def tmod_combine_def tmod_combine_fieldsig_def
    using f_in_tmods
    by simp
qed

lemma tmod_combine_type_func_field_tmods[simp]:
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field Tmod1 \<inter> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)"
  shows "\<And>f. f \<in> Field Tmod1 \<union> Field Tmod2 \<Longrightarrow> type (tmod_combine Tmod1 Tmod2) f = type Tmod1 f \<or> type (tmod_combine Tmod1 Tmod2) f = type Tmod2 f"
  using fieldsig_wellformed tmod_combine_type_func_field_tmod1_tmod2 tmod_combine_type_func_field_tmod1 tmod_combine_type_func_field_tmod2
  unfolding type_def
  by blast

lemma tmod_combine_type_func_field[simp]:
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field Tmod1 \<inter> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)"
  shows "\<And>f. f \<in> Field (tmod_combine Tmod1 Tmod2) \<Longrightarrow> type (tmod_combine Tmod1 Tmod2) f = type Tmod1 f \<or> type (tmod_combine Tmod1 Tmod2) f = type Tmod2 f"
proof-
  fix f
  assume "f \<in> Field (tmod_combine Tmod1 Tmod2)"
  then have "f \<in> Field Tmod1 \<union> Field Tmod2"
    unfolding tmod_combine_def
    by simp
  then show "type (tmod_combine Tmod1 Tmod2) f = type Tmod1 f \<or> type (tmod_combine Tmod1 Tmod2) f = type Tmod2 f"
    using fieldsig_wellformed tmod_combine_type_func_field_tmods
    by blast
qed

lemma tmod_combine_type_func_element_of_types[simp]:
  assumes fieldsig_wellformed_type_tmod1: "\<And>f. f \<in> Field Tmod1 \<Longrightarrow> fst (FieldSig Tmod1 f) \<in> Type Tmod1"
  assumes fieldsig_wellformed_type_tmod2: "\<And>f. f \<in> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod2 f) \<in> Type Tmod2"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field Tmod1 \<inter> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)"
  shows "\<And>f. f \<in> Field (tmod_combine Tmod1 Tmod2) \<Longrightarrow> type (tmod_combine Tmod1 Tmod2) f \<in> Type (tmod_combine Tmod1 Tmod2)"
proof-
  fix f
  assume "f \<in> Field (tmod_combine Tmod1 Tmod2)"
  then have field_in_tmods: "f \<in> Field Tmod1 \<inter> Field Tmod2 \<or> f \<in> Field Tmod1 - Field Tmod2 \<or> f \<in> Field Tmod2 - Field Tmod1"
    unfolding tmod_combine_def
    by auto
  then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1 \<union> Type Tmod2"
  proof (elim disjE)
    assume "f \<in> Field Tmod1 \<inter> Field Tmod2"
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1"
      using Int_iff fieldsig_wellformed fieldsig_wellformed_type_tmod1 tmod_combine_type_func_field_tmod1_tmod2 type_def
      by metis
    then show "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1 \<union> Type Tmod2"
      by blast
  next
    assume f_in_tmod1: "f \<in> Field Tmod1 - Field Tmod2"
    then have "type (tmod_combine Tmod1 Tmod2) f = type Tmod1 f"
      by simp
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1"
      using Diff_iff f_in_tmod1 fieldsig_wellformed_type_tmod1 type_def
      by metis
    then show "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1 \<union> Type Tmod2"
      by blast
  next
    assume f_in_tmod2: "f \<in> Field Tmod2 - Field Tmod1"
    then have "type (tmod_combine Tmod1 Tmod2) f = type Tmod2 f"
      by simp
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod2"
      using Diff_iff f_in_tmod2 fieldsig_wellformed_type_tmod2 type_def
      by metis
    then show "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1 \<union> Type Tmod2"
      by blast
  qed
  then show "type (tmod_combine Tmod1 Tmod2) f \<in> Type (tmod_combine Tmod1 Tmod2)"
    by simp
qed

lemma tmod_combine_attr[simp]:
  assumes fieldsig_wellformed_type_tmod1: "\<And>f. f \<in> Field Tmod1 \<Longrightarrow> fst (FieldSig Tmod1 f) \<in> Type Tmod1"
  assumes fieldsig_wellformed_type_tmod2: "\<And>f. f \<in> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod2 f) \<in> Type Tmod2"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field Tmod1 \<inter> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)"
  shows "Attr (tmod_combine Tmod1 Tmod2) = Attr Tmod1 \<union> Attr Tmod2"
proof
  show "Attr (tmod_combine Tmod1 Tmod2) \<subseteq> Attr Tmod1 \<union> Attr Tmod2"
  proof
    fix x
    assume "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> Attr Tmod1 \<union> Attr Tmod2"
      unfolding Attr_def
    proof
      assume "x \<in> Field (tmod_combine Tmod1 Tmod2) \<and> type (tmod_combine Tmod1 Tmod2) x \<in> AttrType (tmod_combine Tmod1 Tmod2)"
      then have "x \<in> Field Tmod1 \<union> Field Tmod2 \<and> type (tmod_combine Tmod1 Tmod2) x \<in> AttrType Tmod1 \<union> AttrType Tmod2"
        using simps(4) tmod_combine_attr_type tmod_combine_def
        by metis
      then show "x \<in> {f \<in> Field Tmod1. type Tmod1 f \<in> AttrType Tmod1} \<union> {f \<in> Field Tmod2. type Tmod2 f \<in> AttrType Tmod2}"
      proof
        assume type_x_attr_type: "type (tmod_combine Tmod1 Tmod2) x \<in> AttrType Tmod1 \<union> AttrType Tmod2"
        assume "x \<in> Field Tmod1 \<union> Field Tmod2"
        then have x_in_field_tmods: "x \<in> Field Tmod1 \<inter> Field Tmod2 \<or> x \<in> Field Tmod1 - Field Tmod2 \<or> x \<in> Field Tmod2 - Field Tmod1"
          by blast
        then have x_type_in_tmods: "type (tmod_combine Tmod1 Tmod2) x = type Tmod1 x \<or> type (tmod_combine Tmod1 Tmod2) x = type Tmod2 x"
          using fieldsig_wellformed tmod_combine_type_func_field_tmod1 tmod_combine_type_func_field_tmod2 tmod_combine_type_func_field_tmod1_tmod2
          unfolding type_def
          by blast
        show "x \<in> {f \<in> Field Tmod1. type Tmod1 f \<in> AttrType Tmod1} \<union> {f \<in> Field Tmod2. type Tmod2 f \<in> AttrType Tmod2}"
          using x_in_field_tmods
        proof (elim disjE)
          assume x_in_set: "x \<in> Field Tmod1 \<inter> Field Tmod2"
          then show "x \<in> {f \<in> Field Tmod1. type Tmod1 f \<in> AttrType Tmod1} \<union> {f \<in> Field Tmod2. type Tmod2 f \<in> AttrType Tmod2}"
            using x_type_in_tmods
          proof (elim disjE)
            assume x_type: "type (tmod_combine Tmod1 Tmod2) x = type Tmod1 x"
            then have "type (tmod_combine Tmod1 Tmod2) x \<in> Type Tmod1"
              using Int_iff fieldsig_wellformed_type_tmod1 type_def x_in_set
              by metis
            then have "type (tmod_combine Tmod1 Tmod2) x \<in> AttrType Tmod1"
              using type_x_attr_type Un_iff relations_altdef_rel_not_in_attr relations_and_attributes_are_types_alt tmod_combine_attr_type
              by metis
            then have "x \<in> {f \<in> Field Tmod1. type Tmod1 f \<in> AttrType Tmod1}"
              using x_in_set x_type 
              by auto
            then show "x \<in> {f \<in> Field Tmod1. type Tmod1 f \<in> AttrType Tmod1} \<union> {f \<in> Field Tmod2. type Tmod2 f \<in> AttrType Tmod2}"
              by simp
          next
            assume x_type: "type (tmod_combine Tmod1 Tmod2) x = type Tmod2 x"
            then have "type (tmod_combine Tmod1 Tmod2) x \<in> Type Tmod2"
              using Int_iff fieldsig_wellformed_type_tmod2 type_def x_in_set
              by metis
            then have "type (tmod_combine Tmod1 Tmod2) x \<in> AttrType Tmod2"
              using type_x_attr_type Un_iff relations_altdef_rel_not_in_attr relations_and_attributes_are_types_alt tmod_combine_attr_type
              by metis
            then have "x \<in> {f \<in> Field Tmod2. type Tmod2 f \<in> AttrType Tmod2}"
              using x_in_set x_type 
              by auto
            then show "x \<in> {f \<in> Field Tmod1. type Tmod1 f \<in> AttrType Tmod1} \<union> {f \<in> Field Tmod2. type Tmod2 f \<in> AttrType Tmod2}"
              by simp
          qed
        next
          assume x_in_set: "x \<in> Field Tmod1 - Field Tmod2"
          then have "type (tmod_combine Tmod1 Tmod2) x \<in> Type Tmod1"
            using Diff_iff fieldsig_wellformed_type_tmod1 tmod_combine_type_func_field_tmod1 type_def
            by metis
          then have "type (tmod_combine Tmod1 Tmod2) x \<in> AttrType Tmod1"
            using type_x_attr_type Un_iff relations_altdef_rel_not_in_attr relations_and_attributes_are_types_alt tmod_combine_attr_type
            by metis
          then have "x \<in> {f \<in> Field Tmod1. type Tmod1 f \<in> AttrType Tmod1}"
            using x_in_set
            by simp
          then show "x \<in> {f \<in> Field Tmod1. type Tmod1 f \<in> AttrType Tmod1} \<union> {f \<in> Field Tmod2. type Tmod2 f \<in> AttrType Tmod2}"
            by simp
        next
          assume x_in_set: "x \<in> Field Tmod2 - Field Tmod1"
          then have "type (tmod_combine Tmod1 Tmod2) x \<in> Type Tmod2"
            using Diff_iff fieldsig_wellformed_type_tmod2 tmod_combine_type_func_field_tmod2 type_def
            by metis
          then have "type (tmod_combine Tmod1 Tmod2) x \<in> AttrType Tmod2"
            using type_x_attr_type Un_iff relations_altdef_rel_not_in_attr relations_and_attributes_are_types_alt tmod_combine_attr_type
            by metis
          then have "x \<in> {f \<in> Field Tmod2. type Tmod2 f \<in> AttrType Tmod2}"
            using x_in_set
            by simp
          then show "x \<in> {f \<in> Field Tmod1. type Tmod1 f \<in> AttrType Tmod1} \<union> {f \<in> Field Tmod2. type Tmod2 f \<in> AttrType Tmod2}"
            by simp
        qed
      qed
    qed
  qed
next
  show "Attr Tmod1 \<union> Attr Tmod2 \<subseteq> Attr (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> Attr Tmod1 \<union> Attr Tmod2"
    then have "x \<in> Attr Tmod1 \<inter> Attr Tmod2 \<or> x \<in> Attr Tmod1 - Attr Tmod2 \<or> x \<in> Attr Tmod2 - Attr Tmod1"
      by blast
    then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
    proof (elim disjE)
      assume "x \<in> Attr Tmod1 \<inter> Attr Tmod2"
      then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
      proof
        assume x_in_attr1: "x \<in> Attr Tmod1"
        assume x_in_attr2: "x \<in> Attr Tmod2"
        have "x \<in> Field Tmod1 \<and> type Tmod1 x \<in> AttrType Tmod1 \<and> x \<in> Field Tmod2 \<and> type Tmod2 x \<in> AttrType Tmod2"
          using x_in_attr1 x_in_attr2
          unfolding Attr_def
          by blast
        then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
        proof (auto)
          assume x_in_tmod1: "x \<in> Field Tmod1"
          assume x_in_tmod2: "x \<in> Field Tmod2"
          assume x_type_in_attrtype1: "type Tmod1 x \<in> AttrType Tmod1"
          assume x_type_in_attrtype2: "type Tmod2 x \<in> AttrType Tmod2"
          have "type (tmod_combine Tmod1 Tmod2) x = type Tmod1 x \<or> type (tmod_combine Tmod1 Tmod2) x = type Tmod2 x"
            using Un_iff fieldsig_wellformed tmod_combine_type_func_field_tmods x_in_tmod2
            by metis
          then have "x \<in> {f \<in> Field Tmod1 \<union> Field Tmod2. type (tmod_combine Tmod1 Tmod2) f \<in> AttrType Tmod1 \<union> AttrType Tmod2}"
            using x_in_tmod1 x_type_in_attrtype1 x_type_in_attrtype2
            by auto
          then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
            using tmod_combine_attr_type
            unfolding Attr_def tmod_combine_def
            by auto
        qed
      qed
    next
      assume "x \<in> Attr Tmod1 - Attr Tmod2"
      then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
      proof
        assume "x \<in> Attr Tmod1"
        then have x_tmod1: "x \<in> Field Tmod1 \<and> type Tmod1 x \<in> AttrType Tmod1"
          unfolding Attr_def
          by blast
        assume "x \<notin> Attr Tmod2"
        then have x_tmod2: "x \<notin> Field Tmod2 \<or> type Tmod2 x \<notin> AttrType Tmod2"
          unfolding Attr_def
          by blast
        show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
          using x_tmod1 x_tmod2
        proof (auto)
          assume x_in_tmod1: "x \<in> Field Tmod1"
          assume x_not_in_tmod2: "x \<notin> Field Tmod2"
          assume x_type_in_attrtype1: "type Tmod1 x \<in> AttrType Tmod1"
          have "type (tmod_combine Tmod1 Tmod2) x = type Tmod1 x"
            by (simp add: x_in_tmod1 x_not_in_tmod2)
          then have "x \<in> {f \<in> Field Tmod1 \<union> Field Tmod2. type (tmod_combine Tmod1 Tmod2) f \<in> AttrType Tmod1 \<union> AttrType Tmod2}"
            using x_in_tmod1 x_type_in_attrtype1
            by auto
          then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
            using tmod_combine_attr_type
            unfolding Attr_def tmod_combine_def
            by auto
        next
          assume x_in_tmod1: "x \<in> Field Tmod1"
          assume x_type_in_attrtype1: "type Tmod1 x \<in> AttrType Tmod1"
          assume x_type_not_in_attrtype2: "type Tmod2 x \<notin> AttrType Tmod2"
          have "x \<in> {f \<in> Field Tmod1 \<union> Field Tmod2. type (tmod_combine Tmod1 Tmod2) f \<in> AttrType Tmod1 \<union> AttrType Tmod2}"
          proof (induct "x \<in> Field Tmod2")
            case True
            then have type_tmod1_tmod2_eq: "type Tmod1 x = type Tmod2 x"
              using Int_iff fieldsig_wellformed type_def x_in_tmod1
              by metis
            have "type Tmod2 x \<in> Type Tmod2"
              unfolding type_def
              using True.hyps fieldsig_wellformed_type_tmod2
              by blast
            then have "type Tmod2 x \<in> AttrType Tmod2"
              using x_type_in_attrtype1 type_tmod1_tmod2_eq tmod_combine_attr_type_preserved
              by metis
            then show ?case
              using x_type_not_in_attrtype2 
              by blast
          next
            case False
            then have "type (tmod_combine Tmod1 Tmod2) x = type Tmod1 x"
              using tmod_combine_type_func_field_tmod1 x_in_tmod1 
              by blast
            then show ?case
              by (simp add: x_in_tmod1 x_type_in_attrtype1)
          qed
          then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
            using tmod_combine_attr_type
            unfolding Attr_def tmod_combine_def
            by auto
        qed
      qed
    next
      assume "x \<in> Attr Tmod2 - Attr Tmod1"
      then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
      proof
        assume "x \<notin> Attr Tmod1"
        then have x_tmod1: "x \<notin> Field Tmod1 \<or> type Tmod1 x \<notin> AttrType Tmod1"
          unfolding Attr_def
          by blast
        assume "x \<in> Attr Tmod2"
        then have x_tmod2: "x \<in> Field Tmod2 \<and> type Tmod2 x \<in> AttrType Tmod2"
          unfolding Attr_def
          by blast
        show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
          using x_tmod1 x_tmod2
        proof (auto)
          assume x_not_in_tmod1: "x \<notin> Field Tmod1"
          assume x_in_tmod2: "x \<in> Field Tmod2"
          assume x_type_in_attrtype2: "type Tmod2 x \<in> AttrType Tmod2"
          have "type (tmod_combine Tmod1 Tmod2) x = type Tmod2 x"
            by (simp add: x_in_tmod2 x_not_in_tmod1)
          then have "x \<in> {f \<in> Field Tmod1 \<union> Field Tmod2. type (tmod_combine Tmod1 Tmod2) f \<in> AttrType Tmod1 \<union> AttrType Tmod2}"
            using x_in_tmod2 x_type_in_attrtype2
            by auto
          then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
            using tmod_combine_attr_type
            unfolding Attr_def tmod_combine_def
            by auto
        next
          assume x_in_tmod2: "x \<in> Field Tmod2"
          assume x_type_in_attrtype2: "type Tmod2 x \<in> AttrType Tmod2"
          assume x_type_not_in_attrtype1: "type Tmod1 x \<notin> AttrType Tmod1"
          have "x \<in> {f \<in> Field Tmod1 \<union> Field Tmod2. type (tmod_combine Tmod1 Tmod2) f \<in> AttrType Tmod1 \<union> AttrType Tmod2}"
          proof (induct "x \<in> Field Tmod1")
            case True
            then have type_tmod1_tmod2_eq: "type Tmod2 x = type Tmod1 x"
              using Int_iff fieldsig_wellformed type_def x_in_tmod2
              by metis
            have "type Tmod1 x \<in> Type Tmod1"
              unfolding type_def
              using True.hyps fieldsig_wellformed_type_tmod1
              by blast
            then have "type Tmod1 x \<in> AttrType Tmod1"
              using x_type_in_attrtype2 type_tmod1_tmod2_eq tmod_combine_attr_type_preserved
              by metis
            then show ?case
              using x_type_not_in_attrtype1
              by blast
          next
            case False
            then have "type (tmod_combine Tmod1 Tmod2) x = type Tmod2 x"
              using tmod_combine_type_func_field_tmod2 x_in_tmod2
              by blast
            then show ?case
              by (simp add: x_in_tmod2 x_type_in_attrtype2)
          qed
          then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
            using tmod_combine_attr_type
            unfolding Attr_def tmod_combine_def
            by auto
        qed
      qed
    qed
  qed
qed

lemma tmod_combine_rel[simp]:
  assumes fieldsig_wellformed_type_tmod1: "\<And>f. f \<in> Field Tmod1 \<Longrightarrow> fst (FieldSig Tmod1 f) \<in> Type Tmod1"
  assumes fieldsig_wellformed_type_tmod2: "\<And>f. f \<in> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod2 f) \<in> Type Tmod2"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field Tmod1 \<inter> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)"
  shows "Rel (tmod_combine Tmod1 Tmod2) = Rel Tmod1 \<union> Rel Tmod2"
proof
  have "(Field Tmod1 \<union> Field Tmod2) - (Attr Tmod1 \<union> Attr Tmod2) \<subseteq> (Field Tmod1 - Attr Tmod1) \<union> (Field Tmod2 - Attr Tmod2)"
    by blast
  then show "Rel (tmod_combine Tmod1 Tmod2) \<subseteq> Rel Tmod1 \<union> Rel Tmod2"
    unfolding Rel_def tmod_combine_def
    using fieldsig_wellformed_type_tmod1 fieldsig_wellformed_type_tmod2 fieldsig_wellformed tmod_combine_attr select_convs(4) tmod_combine_def
    by metis
next
  have "Rel_altdef Tmod1 \<union> Rel_altdef Tmod2 \<subseteq> Rel (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> Rel_altdef Tmod1 \<union> Rel_altdef Tmod2"
    then have "x \<in> Rel_altdef Tmod1 \<inter> Rel_altdef Tmod2 \<or> x \<in> Rel_altdef Tmod1 - Rel_altdef Tmod2 \<or> x \<in> Rel_altdef Tmod2 - Rel_altdef Tmod1"
      by blast
    then show "x \<in> Rel (tmod_combine Tmod1 Tmod2)"
    proof (elim disjE)
      assume "x \<in> Rel_altdef Tmod1 \<inter> Rel_altdef Tmod2"
      then have "x \<in> {f \<in> Field Tmod1. type Tmod1 f \<in> RelType Tmod1} \<inter> {f \<in> Field Tmod2. type Tmod2 f \<in> RelType Tmod2}"
        unfolding Rel_altdef_def
        by simp
      then have "x \<in> Field Tmod1 \<and> type Tmod1 x \<in> RelType Tmod1 \<and> x \<in> Field Tmod2 \<and> type Tmod2 x \<in> RelType Tmod2"
        by blast
      then have "x \<in> (Field Tmod1 \<union> Field Tmod2) - (Attr Tmod1 \<union> Attr Tmod2)"
        by (simp add: Attr_def RelType_def)
      then show "x \<in> Rel (tmod_combine Tmod1 Tmod2)"
        using tmod_combine_attr fieldsig_wellformed fieldsig_wellformed_type_tmod1 fieldsig_wellformed_type_tmod2
        unfolding Rel_def tmod_combine_def
        by auto
    next
      assume "x \<in> Rel_altdef Tmod1 - Rel_altdef Tmod2"
      then have "x \<in> {f \<in> Field Tmod1. type Tmod1 f \<in> RelType Tmod1} - {f \<in> Field Tmod2. type Tmod2 f \<in> RelType Tmod2}"
        unfolding Rel_altdef_def
        by simp
      then have x_in_tmod1_not_tmod2: "x \<in> Field Tmod1 \<and> type Tmod1 x \<in> RelType Tmod1 \<and> (x \<notin> Field Tmod2 \<or> type Tmod2 x \<notin> RelType Tmod2)"
        by blast
      then show "x \<in> Rel (tmod_combine Tmod1 Tmod2)"
      proof (auto)
        assume x_in_field_tmod1: "x \<in> Field Tmod1"
        assume x_not_in_field_tmod2: "x \<notin> Field Tmod2"
        assume x_type_reltype_tmod1: "type Tmod1 x \<in> RelType_altdef Tmod1"
        then have "x \<in> (Field Tmod1 \<union> Field Tmod2) - (Attr Tmod1 \<union> Attr Tmod2)"
          using x_in_field_tmod1 x_not_in_field_tmod2
          unfolding Attr_def
          by fastforce
        then show "x \<in> Rel (tmod_combine Tmod1 Tmod2)"
          using tmod_combine_attr fieldsig_wellformed fieldsig_wellformed_type_tmod1 fieldsig_wellformed_type_tmod2
          unfolding Rel_def tmod_combine_def
          by auto
      next
        assume x_in_field_tmod1: "x \<in> Field Tmod1"
        assume x_type_reltype_tmod1: "type Tmod1 x \<in> RelType_altdef Tmod1"
        assume x_type_not_reltype_tmod2: "type Tmod2 x \<notin> RelType_altdef Tmod2"
        then have "x \<in> (Field Tmod1 \<union> Field Tmod2) - (Attr Tmod1 \<union> Attr Tmod2)"
        proof (induct "x \<in> Field Tmod2")
          case True
          then have type_tmod1_tmod2_eq: "type Tmod2 x \<in> RelType Tmod2"
            unfolding type_def
            using Int_iff fieldsig_wellformed fieldsig_wellformed_type_tmod2 relation_member 
            using relations_altdef_rel_not_in_attr type_def x_in_field_tmod1 x_type_reltype_tmod1
            by metis
          then show ?case
            using x_type_not_reltype_tmod2
            by simp
        next
          case False
          then show ?case
            using x_in_field_tmod1 x_type_reltype_tmod1
            unfolding Attr_def
            by fastforce
        qed
        then show "x \<in> Rel (tmod_combine Tmod1 Tmod2)"
          using tmod_combine_attr fieldsig_wellformed fieldsig_wellformed_type_tmod1 fieldsig_wellformed_type_tmod2
          unfolding Rel_def tmod_combine_def
          by auto
      qed
    next
      assume "x \<in> Rel_altdef Tmod2 - Rel_altdef Tmod1"
      then have "x \<in> {f \<in> Field Tmod2. type Tmod2 f \<in> RelType Tmod2} - {f \<in> Field Tmod1. type Tmod1 f \<in> RelType Tmod1}"
        unfolding Rel_altdef_def
        by simp
      then have x_in_tmod2_not_tmod1: "x \<in> Field Tmod2 \<and> type Tmod2 x \<in> RelType Tmod2 \<and> (x \<notin> Field Tmod1 \<or> type Tmod1 x \<notin> RelType Tmod1)"
        by blast
      then show "x \<in> Rel (tmod_combine Tmod1 Tmod2)"
      proof (auto)
        assume x_not_in_field_tmod1: "x \<notin> Field Tmod1"
        assume x_in_field_tmod2: "x \<in> Field Tmod2"
        assume x_type_reltype_tmod2: "type Tmod2 x \<in> RelType_altdef Tmod2"
        then have "x \<in> (Field Tmod1 \<union> Field Tmod2) - (Attr Tmod1 \<union> Attr Tmod2)"
          using x_in_field_tmod2 x_not_in_field_tmod1
          unfolding Attr_def
          by fastforce
        then show "x \<in> Rel (tmod_combine Tmod1 Tmod2)"
          using tmod_combine_attr fieldsig_wellformed fieldsig_wellformed_type_tmod1 fieldsig_wellformed_type_tmod2
          unfolding Rel_def tmod_combine_def
          by auto
      next
        assume x_in_field_tmod2: "x \<in> Field Tmod2"
        assume x_type_not_reltype_tmod1: "type Tmod1 x \<notin> RelType_altdef Tmod1"
        assume x_type_reltype_tmod2: "type Tmod2 x \<in> RelType_altdef Tmod2"
        then have "x \<in> (Field Tmod1 \<union> Field Tmod2) - (Attr Tmod1 \<union> Attr Tmod2)"
        proof (induct "x \<in> Field Tmod1")
          case True
          then have type_tmod1_tmod2_eq: "type Tmod1 x \<in> RelType Tmod1"
            unfolding type_def
            using Int_iff fieldsig_wellformed fieldsig_wellformed_type_tmod1 relation_member 
            using relations_altdef_rel_not_in_attr type_def x_in_field_tmod2 x_type_reltype_tmod2
            by metis
          then show ?case
            using x_type_not_reltype_tmod1
            by simp
        next
          case False
          then show ?case
            using x_in_field_tmod2 x_type_reltype_tmod2
            unfolding Attr_def
            by fastforce
        qed
        then show "x \<in> Rel (tmod_combine Tmod1 Tmod2)"
          using tmod_combine_attr fieldsig_wellformed fieldsig_wellformed_type_tmod1 fieldsig_wellformed_type_tmod2
          unfolding Rel_def tmod_combine_def
          by auto
      qed
    qed
  qed
  then show "Rel Tmod1 \<union> Rel Tmod2 \<subseteq> Rel (tmod_combine Tmod1 Tmod2)"
    using fieldsig_wellformed_type_tmod1 fieldsig_wellformed_type_tmod2 rel_definition_alt
    by blast
qed

lemma tmod_combine_unique_container_of_class_type[simp]: 
  shows "UniqueContainerOfClassType (tmod_combine Tmod1 Tmod2) = UniqueContainerOfClassType Tmod1 \<union> UniqueContainerOfClassType Tmod2"
proof
  show "UniqueContainerOfClassType (tmod_combine Tmod1 Tmod2) \<subseteq> UniqueContainerOfClassType Tmod1 \<union> UniqueContainerOfClassType Tmod2"
  proof
    fix x
    assume "x \<in> UniqueContainerOfClassType (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> UniqueContainerOfClassType Tmod1 \<union> UniqueContainerOfClassType Tmod2"
    proof (induct)
      case (rule_setof_class_type t)
      then show ?case
        using UniqueContainerOfClassType.rule_setof_class_type
        by fastforce
    next
      case (rule_ordof_class_type t)
      then show ?case
        using UniqueContainerOfClassType.rule_ordof_class_type
        by fastforce
    qed
  qed
next
  show "UniqueContainerOfClassType Tmod1 \<union> UniqueContainerOfClassType Tmod2 \<subseteq> UniqueContainerOfClassType (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> UniqueContainerOfClassType Tmod1 \<union> UniqueContainerOfClassType Tmod2"
    then show "x \<in> UniqueContainerOfClassType (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> UniqueContainerOfClassType Tmod1"
      then show "x \<in> UniqueContainerOfClassType (tmod_combine Tmod1 Tmod2)"
        by (induct) (simp_all add: UniqueContainerOfClassType.simps)
    next
      assume "x \<in> UniqueContainerOfClassType Tmod2"
      then show "x \<in> UniqueContainerOfClassType (tmod_combine Tmod1 Tmod2)"
        by (induct) (simp_all add: UniqueContainerOfClassType.simps)
    qed
  qed
qed

lemma tmod_combine_containment_relation_subset_tmod1:
  assumes fieldsig_wellformed_type_tmod1: "\<And>f. f \<in> Field Tmod1 \<Longrightarrow> fst (FieldSig Tmod1 f) \<in> Type Tmod1"
  assumes fieldsig_wellformed_type_tmod2: "\<And>f. f \<in> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod2 f) \<in> Type Tmod2"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field Tmod1 \<inter> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)"
  shows "CR Tmod1 \<subseteq> CR (tmod_combine Tmod1 Tmod2)"
proof
  fix x
  assume "x \<in> CR Tmod1"
  then show "x \<in> CR (tmod_combine Tmod1 Tmod2)"
  proof (induct)
    case (rule_containment_relations r)
    then have r_in_combination: "r \<in> Rel (tmod_combine Tmod1 Tmod2)"
      using UnCI fieldsig_wellformed fieldsig_wellformed_type_tmod1 fieldsig_wellformed_type_tmod2 tmod_combine_rel
      by metis
    have "containment r \<in> tmod_combine_prop Tmod1 Tmod2"
      by (simp add: rule_containment_relations.hyps(2) tmod_combine_prop.containment_property_tmod1)
    then have "containment r \<in> Prop (tmod_combine Tmod1 Tmod2)"
      by (simp add: tmod_combine_def)
    then show ?case
      using CR.rule_containment_relations r_in_combination
      by blast
  qed
qed

lemma tmod_combine_containment_relation_subset_tmod2:
  assumes fieldsig_wellformed_type_tmod1: "\<And>f. f \<in> Field Tmod1 \<Longrightarrow> fst (FieldSig Tmod1 f) \<in> Type Tmod1"
  assumes fieldsig_wellformed_type_tmod2: "\<And>f. f \<in> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod2 f) \<in> Type Tmod2"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field Tmod1 \<inter> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)"
  shows "CR Tmod2 \<subseteq> CR (tmod_combine Tmod1 Tmod2)"
  using assms inf_aci(1) tmod_combine_commute tmod_combine_containment_relation_subset_tmod1
  by metis

lemma tmod_combine_containment_relation:
  assumes fieldsig_wellformed_type_tmod1: "\<And>f. f \<in> Field Tmod1 \<Longrightarrow> fst (FieldSig Tmod1 f) \<in> Type Tmod1"
  assumes fieldsig_wellformed_type_tmod2: "\<And>f. f \<in> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod2 f) \<in> Type Tmod2"
  assumes properties_wellformed_tmod1: "\<And>p. p \<in> Prop Tmod1 \<Longrightarrow> p \<in> Property Tmod1"
  assumes properties_wellformed_tmod2: "\<And>p. p \<in> Prop Tmod2 \<Longrightarrow> p \<in> Property Tmod2"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field Tmod1 \<inter> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)"
  shows "CR (tmod_combine Tmod1 Tmod2) = CR Tmod1 \<union> CR Tmod2"
proof
  show "CR (tmod_combine Tmod1 Tmod2) \<subseteq> CR Tmod1 \<union> CR Tmod2"
  proof
    fix x
    assume "x \<in> CR (tmod_combine Tmod1 Tmod2)"
    then show "x \<in> CR Tmod1 \<union> CR Tmod2"
    proof (induct)
      case (rule_containment_relations r)
      then have r_rel: "r \<in> Rel Tmod1 \<union> Rel Tmod2"
        using fieldsig_wellformed_type_tmod1 fieldsig_wellformed_type_tmod2 fieldsig_wellformed tmod_combine_rel
        by blast
      have "containment r \<in> tmod_combine_prop Tmod1 Tmod2"
        using rule_containment_relations.hyps(2) tmod_combine_def type_model.select_convs(8)
        by metis
      then have "containment r \<in> Prop Tmod1 \<or> containment r \<in> Prop Tmod2"
      proof (cases)
        case containment_property_tmod1
        then show ?thesis
          by simp
      next
        case containment_property_tmod2
        then show ?thesis
          by simp
      qed
      then show ?case
        using r_rel
      proof (elim disjE UnE)
        assume containment_in_tmod1: "containment r \<in> Prop Tmod1"
        assume relation_in_tmod1: "r \<in> Rel Tmod1"
        show ?thesis
          by (simp add: CR.rule_containment_relations containment_in_tmod1 relation_in_tmod1)
      next
        assume containment_in_tmod1: "containment r \<in> Prop Tmod1"
        then have "containment r \<in> Property Tmod1"
          using properties_wellformed_tmod1
          by blast
        then have relation_in_tmod1: "r \<in> Rel Tmod1"
        proof (cases)
          case containment_property
          then show ?thesis
            by simp
        qed
        show ?thesis
          by (simp add: CR.rule_containment_relations containment_in_tmod1 relation_in_tmod1)
      next
        assume containment_in_tmod2: "containment r \<in> Prop Tmod2"
        then have "containment r \<in> Property Tmod2"
          using properties_wellformed_tmod2
          by blast
        then have relation_in_tmod2: "r \<in> Rel Tmod2"
        proof (cases)
          case containment_property
          then show ?thesis
            by simp
        qed
        show ?thesis
          by (simp add: CR.rule_containment_relations containment_in_tmod2 relation_in_tmod2)
      next
        assume containment_in_tmod2: "containment r \<in> Prop Tmod2"
        assume relation_in_tmod2: "r \<in> Rel Tmod2"
        show ?thesis
          by (simp add: CR.rule_containment_relations containment_in_tmod2 relation_in_tmod2)
      qed
    qed
  qed
next
  show "CR Tmod1 \<union> CR Tmod2 \<subseteq> CR (tmod_combine Tmod1 Tmod2)"
  proof
    fix x
    assume "x \<in> CR Tmod1 \<union> CR Tmod2"
    then show "x \<in> CR (tmod_combine Tmod1 Tmod2)"
    proof (elim UnE)
      assume "x \<in> CR Tmod1"
      then show ?thesis
        using tmod_combine_containment_relation_subset_tmod1 fieldsig_wellformed_type_tmod1 fieldsig_wellformed_type_tmod2 fieldsig_wellformed
        by blast
    next
      assume "x \<in> CR Tmod2"
      then show ?thesis
        using tmod_combine_containment_relation_subset_tmod2 fieldsig_wellformed_type_tmod1 fieldsig_wellformed_type_tmod2 fieldsig_wellformed
        by blast
    qed
  qed
qed


subsection "Associativity of the combination of type models"

lemma tmod_combine_fieldsig_assoc: "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) = tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3"
proof
  fix f
  have f_tmod1_cases: "f \<in> Field Tmod1 \<or> f \<notin> Field Tmod1"
    by simp
  have f_tmod23_cases: "f \<in> Field (tmod_combine Tmod2 Tmod3) \<or> f \<notin> Field (tmod_combine Tmod2 Tmod3)"
    by simp
  show "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f"
    using f_tmod1_cases f_tmod23_cases
  proof (elim disjE)
    assume f_in_tmod1: "f \<in> Field Tmod1"
    then have f_in_tmod12: "f \<in> Field (tmod_combine Tmod1 Tmod2)"
      by (simp add: tmod_combine_def)
    assume f_in_tmod23: "f \<in> Field (tmod_combine Tmod2 Tmod3)"
    show "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f"
    proof (induct "f \<in> Field Tmod2")
      case True
      then show ?case
      proof (induct "f \<in> Field Tmod3")
        case True
        then show ?case
        proof (induct "fst (FieldSig (tmod_combine Tmod1 Tmod2) f) = fst (FieldSig Tmod3 f)")
          case True
          then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = (fst (FieldSig (tmod_combine Tmod1 Tmod2) f), snd (FieldSig (tmod_combine Tmod1 Tmod2) f) \<sqinter> snd (FieldSig Tmod3 f))"
            unfolding tmod_combine_fieldsig_def
            using f_in_tmod12
            by simp
          show ?case
            using True.hyps True.prems
          proof (induct "fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)")
            case True
            then have "FieldSig (tmod_combine Tmod1 Tmod2) f = tmod_combine_fieldsig Tmod1 Tmod2 f"
              by (simp add: tmod_combine_def)
            then have tmod12_def: "FieldSig (tmod_combine Tmod1 Tmod2) f = (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f))"
              unfolding tmod_combine_fieldsig_def
              using True.hyps True.prems(3) f_in_tmod1
              by simp
            then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = (fst (FieldSig Tmod1 f), (snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f)) \<sqinter> snd (FieldSig Tmod3 f))"
              by (simp add: tmod12_tmod3_def)
            have "fst (FieldSig Tmod1 f) = fst (FieldSig Tmod3 f)"
              using True.prems(1) tmod12_def
              by simp
            then have tmod2_f_is_tmod3_f: "fst (FieldSig Tmod2 f) = fst (FieldSig Tmod3 f)"
              using True.hyps
              by simp
            have "FieldSig (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig Tmod2 Tmod3 f"
              by (simp add: tmod_combine_def)
            then have tmod23_def: "FieldSig (tmod_combine Tmod2 Tmod3) f = (fst (FieldSig Tmod2 f), snd (FieldSig Tmod2 f) \<sqinter> snd (FieldSig Tmod3 f))"
              unfolding tmod_combine_fieldsig_def
              using True.prems(2) True.prems(3) tmod2_f_is_tmod3_f
              by simp
            then have "fst (FieldSig Tmod1 f) = fst (FieldSig (tmod_combine Tmod2 Tmod3) f)"
              using True.hyps
              by simp
            then have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig (tmod_combine Tmod2 Tmod3) f))"
              unfolding tmod_combine_fieldsig_def
              by (simp add: f_in_tmod1 f_in_tmod23)
            then have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> (snd (FieldSig Tmod2 f) \<sqinter> snd (FieldSig Tmod3 f)))"
              by (simp add: tmod23_def)
            then show ?case
              using mult_intersect_assoc tmod12_tmod3_def
              by simp
          next
            case False
            then show ?case
            proof (induct "fst (FieldSig Tmod2 f) = fst (FieldSig Tmod3 f)")
              case True
              then have "FieldSig (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig Tmod2 Tmod3 f"
                by (simp add: tmod_combine_def)
              then have tmod23_def: "FieldSig (tmod_combine Tmod2 Tmod3) f = (fst (FieldSig Tmod2 f), snd (FieldSig Tmod2 f) \<sqinter> snd (FieldSig Tmod3 f))"
                unfolding tmod_combine_fieldsig_def
                using True.hyps True.prems(3) True.prems(4)
                by simp
              then have "fst (FieldSig Tmod1 f) \<noteq> fst (FieldSig (tmod_combine Tmod2 Tmod3) f)"
                using False.hyps
                by simp
              then have tmod1_tmod23_def: "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (invalid, \<^emph>..\<^bold>0)"
                by (simp add: f_in_tmod1 f_in_tmod23 tmod_combine_fieldsig_def)
              have "FieldSig (tmod_combine Tmod1 Tmod2) f = tmod_combine_fieldsig Tmod1 Tmod2 f"
                by (simp add: tmod_combine_def)
              then have tmod12_def: "FieldSig (tmod_combine Tmod1 Tmod2) f = (invalid, \<^emph>..\<^bold>0)"
                unfolding tmod_combine_fieldsig_def
                using False.hyps True.prems(4) f_in_tmod1
                by simp
              then have "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = (invalid, (\<^emph>..\<^bold>0) \<sqinter> snd (FieldSig Tmod3 f))"
                by (simp add: tmod12_tmod3_def)
              then show ?case
                using mult_intersect_commute mult_intersect_invalid tmod1_tmod23_def
                by metis
            next
              case False
              have "FieldSig (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig Tmod2 Tmod3 f"
                by (simp add: tmod_combine_def)
              then have tmod23_def: "FieldSig (tmod_combine Tmod2 Tmod3) f = (invalid, \<^emph>..\<^bold>0)"
                unfolding tmod_combine_fieldsig_def
                using False.hyps True.prems(1) True.prems(2)
                by simp
              then have tmod1_tmod23_def: "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (invalid, (\<^emph>..\<^bold>0))"
                unfolding tmod_combine_fieldsig_def
                using Int_iff f_in_tmod1 f_in_tmod23 fst_conv mult_intersect_invalid snd_conv
                by metis
              have "FieldSig (tmod_combine Tmod1 Tmod2) f = tmod_combine_fieldsig Tmod1 Tmod2 f"
                by (simp add: tmod_combine_def)
              then have tmod12_def: "FieldSig (tmod_combine Tmod1 Tmod2) f = (invalid, \<^emph>..\<^bold>0)"
                unfolding tmod_combine_fieldsig_def
                using False.prems(1) True.prems(2) f_in_tmod1
                by simp
              then have "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = (invalid, (\<^emph>..\<^bold>0) \<sqinter> snd (FieldSig Tmod3 f))"
                by (simp add: tmod12_tmod3_def)
              then show ?case
                using mult_intersect_commute mult_intersect_invalid tmod1_tmod23_def
                by metis
            qed
          qed
        next
          case False
          then show ?case
          proof (induct "fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)")
            case True
            then have "FieldSig (tmod_combine Tmod1 Tmod2) f = tmod_combine_fieldsig Tmod1 Tmod2 f"
              by (simp add: tmod_combine_def)
            then have tmod12_def: "FieldSig (tmod_combine Tmod1 Tmod2) f = (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f))"
              unfolding tmod_combine_fieldsig_def
              using True.hyps True.prems(3) f_in_tmod1
              by simp
            then have "fst (FieldSig Tmod1 f) \<noteq> fst (FieldSig Tmod3 f)"
              using False.hyps
              by simp
            then have tmod2_f_is_not_tmod3_f: "fst (FieldSig Tmod2 f) \<noteq> fst (FieldSig Tmod3 f)"
              using True.hyps
              by simp
            have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = (invalid, \<^emph>..\<^bold>0)"
              unfolding tmod_combine_fieldsig_def
              using False.hyps True.prems(2) f_in_tmod12
              by simp
            have "FieldSig (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig Tmod2 Tmod3 f"
              by (simp add: tmod_combine_def)
            then have tmod23_def: "FieldSig (tmod_combine Tmod2 Tmod3) f = (invalid, \<^emph>..\<^bold>0)"
              unfolding tmod_combine_fieldsig_def
              using True.prems(2) True.prems(3) tmod2_f_is_not_tmod3_f
              by simp
            then have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (invalid, \<^emph>..\<^bold>0)"
              unfolding tmod_combine_fieldsig_def
              using Int_iff f_in_tmod1 f_in_tmod23 fst_conv mult_intersect_invalid snd_conv
              by metis
            then show ?case
              by (simp add: tmod12_tmod3_def)
          next
            case False
            then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = (invalid, \<^emph>..\<^bold>0)"
              unfolding tmod_combine_fieldsig_def
              using False.prems(1) f_in_tmod12
              by simp
            then show ?case
              using False.hyps False.prems
            proof (induct "fst (FieldSig Tmod2 f) = fst (FieldSig Tmod3 f)")
              case True
              have "FieldSig (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig Tmod2 Tmod3 f"
                by (simp add: tmod_combine_def)
              then have tmod23_def: "FieldSig (tmod_combine Tmod2 Tmod3) f = (fst (FieldSig Tmod2 f), snd (FieldSig Tmod2 f) \<sqinter> snd (FieldSig Tmod3 f))"
                unfolding tmod_combine_fieldsig_def
                using True.hyps True.prems(4) True.prems(5)
                by simp
              then have "fst (FieldSig Tmod1 f) \<noteq> fst (FieldSig (tmod_combine Tmod2 Tmod3) f)"
                using False.hyps
                by simp
              then have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (invalid, \<^emph>..\<^bold>0)"
                unfolding tmod_combine_fieldsig_def
                by (simp add: f_in_tmod1 f_in_tmod23)
              then show ?case
                by (simp add: tmod12_tmod3_def)
            next
              case False
              have "FieldSig (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig Tmod2 Tmod3 f"
                by (simp add: tmod_combine_def)
              then have tmod23_def: "FieldSig (tmod_combine Tmod2 Tmod3) f = (invalid, \<^emph>..\<^bold>0)"
                unfolding tmod_combine_fieldsig_def
                using False.hyps True.hyps True.prems
                by simp
              then have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (invalid, \<^emph>..\<^bold>0)"
                unfolding tmod_combine_fieldsig_def
                using Int_iff f_in_tmod1 f_in_tmod23 fst_conv mult_intersect_invalid snd_conv
                by metis
              then show ?case
                by (simp add: tmod12_tmod3_def)
            qed
          qed
        qed
      next
        case False
        then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = FieldSig (tmod_combine Tmod1 Tmod2) f"
          unfolding tmod_combine_fieldsig_def
          using f_in_tmod12
          by simp
        have "FieldSig (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig Tmod2 Tmod3 f"
          by (simp add: tmod_combine_def)
        then have tmod23_def: "FieldSig (tmod_combine Tmod2 Tmod3) f = FieldSig Tmod2 f"
          unfolding tmod_combine_fieldsig_def
          using False.hyps True.hyps
          by simp
        show ?case
        proof (induct "fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)")
          case True
          then have "FieldSig (tmod_combine Tmod1 Tmod2) f = tmod_combine_fieldsig Tmod1 Tmod2 f"
            by (simp add: tmod_combine_def)
          then have tmod12_def: "FieldSig (tmod_combine Tmod1 Tmod2) f = (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f))"
            unfolding tmod_combine_fieldsig_def
            using False.prems True.hyps f_in_tmod1
            by simp
          have "fst (FieldSig Tmod1 f) = fst (FieldSig (tmod_combine Tmod2 Tmod3) f)"
            using True.hyps tmod23_def
            by simp
          then have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig (tmod_combine Tmod2 Tmod3) f))"
            unfolding tmod_combine_fieldsig_def
            by (simp add: f_in_tmod1 f_in_tmod23)
          then have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f))"
            by (simp add: tmod23_def)
          then show ?case
            by (simp add: tmod12_def tmod12_tmod3_def)
        next
          case False
          then have "FieldSig (tmod_combine Tmod1 Tmod2) f = tmod_combine_fieldsig Tmod1 Tmod2 f"
            by (simp add: tmod_combine_def)
          then have tmod12_def: "FieldSig (tmod_combine Tmod1 Tmod2) f = (invalid, \<^emph>..\<^bold>0)"
            unfolding tmod_combine_fieldsig_def
            using False.hyps True.hyps f_in_tmod1
            by simp
          have "fst (FieldSig Tmod1 f) \<noteq> fst (FieldSig (tmod_combine Tmod2 Tmod3) f)"
            using False.hyps tmod23_def
            by simp
          then have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (invalid, \<^emph>..\<^bold>0)"
            unfolding tmod_combine_fieldsig_def
            by (simp add: f_in_tmod1 f_in_tmod23)
          then show ?case
            by (simp add: tmod12_def tmod12_tmod3_def)
        qed
      qed
    next
      case False
      then have f_in_tmod3: "f \<in> Field Tmod3"
        using Un_iff f_in_tmod23 select_convs(4) tmod_combine_def
        by metis
      then have f_in_tmod12_tmod3: "f \<in> Field (tmod_combine Tmod1 Tmod2) \<inter> Field Tmod3"
        by (simp add: f_in_tmod12)
      have f_in_tmod12_tmod3: "f \<in> Field Tmod1 \<inter> Field (tmod_combine Tmod2 Tmod3)"
        by (simp add: f_in_tmod1 f_in_tmod23)
      show ?case
        using False.hyps
      proof (induct "fst (FieldSig (tmod_combine Tmod1 Tmod2) f) = fst (FieldSig Tmod3 f)")
        case True
        then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = (fst (FieldSig (tmod_combine Tmod1 Tmod2) f), snd (FieldSig (tmod_combine Tmod1 Tmod2) f) \<sqinter> snd (FieldSig Tmod3 f))"
          unfolding tmod_combine_fieldsig_def
          using f_in_tmod12 f_in_tmod3
          by simp
        have "FieldSig (tmod_combine Tmod1 Tmod2) f = tmod_combine_fieldsig Tmod1 Tmod2 f"
          by (simp add: tmod_combine_def)
        then have tmod12_def: "FieldSig (tmod_combine Tmod1 Tmod2) f = FieldSig Tmod1 f"
          unfolding tmod_combine_fieldsig_def
          using False.hyps f_in_tmod1
          by simp
        then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod3 f))"
          by (simp add: tmod12_tmod3_def)
        have "FieldSig (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig Tmod2 Tmod3 f"
          by (simp add: tmod_combine_def)
        then have tmod23_def: "FieldSig (tmod_combine Tmod2 Tmod3) f = FieldSig Tmod3 f"
          unfolding tmod_combine_fieldsig_def
          using False.hyps f_in_tmod3
          by simp
        have "fst (FieldSig Tmod1 f) = fst (FieldSig Tmod3 f)"
          using True.hyps tmod12_def
          by simp
        then have "fst (FieldSig Tmod1 f) = fst (FieldSig (tmod_combine Tmod2 Tmod3) f)"
          by (simp add: tmod23_def)
        then have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig (tmod_combine Tmod2 Tmod3) f))"
          unfolding tmod_combine_fieldsig_def
          using f_in_tmod12_tmod3
          by simp
        then have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod3 f))"
          by (simp add: tmod23_def)
        then show ?case
          by (simp add: tmod12_tmod3_def)
      next
        case False
        then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = (invalid, \<^emph>..\<^bold>0)"
          unfolding tmod_combine_fieldsig_def
          using f_in_tmod12 f_in_tmod3
          by simp
        have "FieldSig (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig Tmod2 Tmod3 f"
          by (simp add: tmod_combine_def)
        then have tmod23_def: "FieldSig (tmod_combine Tmod2 Tmod3) f = FieldSig Tmod3 f"
          unfolding tmod_combine_fieldsig_def
          using False.prems f_in_tmod3
          by simp
        have "FieldSig (tmod_combine Tmod1 Tmod2) f = tmod_combine_fieldsig Tmod1 Tmod2 f"
          by (simp add: tmod_combine_def)
        then have tmod12_def: "FieldSig (tmod_combine Tmod1 Tmod2) f = FieldSig Tmod1 f"
          unfolding tmod_combine_fieldsig_def
          using False.prems f_in_tmod1
          by simp
        then have "fst (FieldSig Tmod1 f) \<noteq> fst (FieldSig Tmod3 f)"
          using False.hyps
          by simp
        then have "fst (FieldSig Tmod1 f) \<noteq> fst (FieldSig (tmod_combine Tmod2 Tmod3) f)"
          by (simp add: tmod23_def)
        then have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = (invalid, \<^emph>..\<^bold>0)"
          unfolding tmod_combine_fieldsig_def
          by (simp add: f_in_tmod1 f_in_tmod23)
        then show ?case
          by (simp add: tmod12_tmod3_def)
      qed
    qed
  next
    assume f_in_tmod1: "f \<in> Field Tmod1"
    then have f_in_tmod12: "f \<in> Field (tmod_combine Tmod1 Tmod2)"
      by (simp add: tmod_combine_def)
    assume f_not_in_tmod23: "f \<notin> Field (tmod_combine Tmod2 Tmod3)"
    then have f_not_in_tmod3: "f \<notin> Field Tmod3"
      by (simp add: tmod_combine_def)
    then have "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = FieldSig (tmod_combine Tmod1 Tmod2) f"
      unfolding tmod_combine_fieldsig_def
      using f_in_tmod12
      by simp
    then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = tmod_combine_fieldsig Tmod1 Tmod2 f"
      by (simp add: tmod_combine_def)
    have f_not_in_tmod2: "f \<notin> Field Tmod2"
      using Un_iff f_not_in_tmod23 select_convs(4) tmod_combine_def
      by metis
    then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = FieldSig Tmod1 f"
      using tmod12_tmod3_def
      unfolding tmod_combine_fieldsig_def
      by (simp add: f_in_tmod1)
    have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = FieldSig Tmod1 f"
      unfolding tmod_combine_fieldsig_def
      by (simp add: f_in_tmod1 f_not_in_tmod23) 
    then show "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f"
      using tmod12_tmod3_def
      by simp
  next
    assume f_not_in_tmod1: "f \<notin> Field Tmod1"
    assume f_in_tmod23: "f \<in> Field (tmod_combine Tmod2 Tmod3)"
    have "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = FieldSig (tmod_combine Tmod2 Tmod3) f"
      unfolding tmod_combine_fieldsig_def
      by (simp add: f_in_tmod23 f_not_in_tmod1)
    then have tmod1_tmod23_def: "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig Tmod2 Tmod3 f"
      by (simp add: tmod_combine_def)
    have "tmod_combine_fieldsig Tmod2 Tmod3 f = tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f"
    proof (induct "f \<in> Field Tmod2")
      case True
      then show ?case
      proof (induct "f \<in> Field Tmod3")
        case True
        then have f_in_tmod12_tmod3: "f \<in> Field (tmod_combine Tmod1 Tmod2) \<inter> Field Tmod3"
          using IntI Un_iff simps(4) tmod_combine_def
          by metis
        have f_in_tmod2_tmod3: "f \<in> Field Tmod2 \<inter> Field Tmod3"
          using True.hyps True.prems
          by blast
        have "tmod_combine_fieldsig Tmod1 Tmod2 f = FieldSig Tmod2 f"
          unfolding tmod_combine_fieldsig_def
          using True.prems f_not_in_tmod1
          by simp
        then have "FieldSig (tmod_combine Tmod1 Tmod2) f = FieldSig Tmod2 f"
          by (simp add: tmod_combine_def)
        then show ?case
          using True.hyps True.prems
        proof (induct "fst (FieldSig Tmod2 f) = fst (FieldSig Tmod3 f)")
          case True
          then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = (fst (FieldSig Tmod2 f), snd (FieldSig Tmod2 f) \<sqinter> snd (FieldSig Tmod3 f))"
            unfolding tmod_combine_fieldsig_def
            using f_in_tmod12_tmod3
            by simp
          then have "tmod_combine_fieldsig Tmod2 Tmod3 f = (fst (FieldSig Tmod2 f), snd (FieldSig Tmod2 f) \<sqinter> snd (FieldSig Tmod3 f))"
            unfolding tmod_combine_fieldsig_def
            using True.hyps f_in_tmod2_tmod3
            by simp
          then show ?case
            by (simp add: tmod12_tmod3_def)
        next
          case False
          then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = (invalid, \<^emph>..\<^bold>0)"
            unfolding tmod_combine_fieldsig_def
            using f_in_tmod12_tmod3
            by simp
          then have "tmod_combine_fieldsig Tmod2 Tmod3 f = (invalid, \<^emph>..\<^bold>0)"
            unfolding tmod_combine_fieldsig_def
            using False.hyps f_in_tmod2_tmod3
            by simp
          then show ?case
            by (simp add: tmod12_tmod3_def)
        qed
      next
        case False
        then have f_in_tmod12: "f \<in> Field (tmod_combine Tmod1 Tmod2)"
          using Un_iff simps(4) tmod_combine_def
          by metis
        then have "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = FieldSig (tmod_combine Tmod1 Tmod2) f"
          unfolding tmod_combine_fieldsig_def
          using False.hyps
          by simp
        then have tmod12_tmod3_def: "tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f = tmod_combine_fieldsig Tmod1 Tmod2 f"
          by (simp add: tmod_combine_def)
        then show ?case
          unfolding tmod_combine_fieldsig_def
          using tmod12_tmod3_def False.hyps f_not_in_tmod1
          by simp
      qed
    next
      case False
      then have f_not_in_tmod12: "f \<notin> Field (tmod_combine Tmod1 Tmod2)"
        using Un_iff f_not_in_tmod1 select_convs(4) tmod_combine_def
        by metis
      show ?case
        unfolding tmod_combine_fieldsig_def
        using False.hyps f_not_in_tmod12
        by simp
    qed
    then show "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f"
      by (simp add: tmod1_tmod23_def)
  next
    assume f_not_in_tmod1: "f \<notin> Field Tmod1"
    assume f_not_in_tmod23: "f \<notin> Field (tmod_combine Tmod2 Tmod3)"
    have f_not_in_tmod12: "f \<notin> Field (tmod_combine Tmod1 Tmod2)"
      using Un_iff f_not_in_tmod1 f_not_in_tmod23 simps(4) tmod_combine_def
      by metis
    have f_not_in_tmod3: "f \<notin> Field Tmod3"
      using Un_iff f_not_in_tmod23 select_convs(4) tmod_combine_def
      by metis
    show "tmod_combine_fieldsig Tmod1 (tmod_combine Tmod2 Tmod3) f = tmod_combine_fieldsig (tmod_combine Tmod1 Tmod2) Tmod3 f"
      unfolding tmod_combine_fieldsig_def
      using f_not_in_tmod1 f_not_in_tmod23 f_not_in_tmod12 f_not_in_tmod3
      by simp
  qed
qed

lemma tmod_combine_const_type_assoc: "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) = tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3"
proof
  fix c
  have c_tmod1_cases: "c \<in> Constant Tmod1 \<or> c \<notin> Constant Tmod1"
    by simp
  have c_tmod23_cases: "c \<in> Constant (tmod_combine Tmod2 Tmod3) \<or> c \<notin> Constant (tmod_combine Tmod2 Tmod3)"
    by simp
  show "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c"
    using c_tmod1_cases c_tmod23_cases
  proof (elim disjE)
    assume c_in_tmod1: "c \<in> Constant Tmod1"
    then have c_in_tmod12: "c \<in> Constant (tmod_combine Tmod1 Tmod2)"
      by (simp add: tmod_combine_def)
    assume c_in_tmod23: "c \<in> Constant (tmod_combine Tmod2 Tmod3)"
    show ?thesis
    proof (induct "c \<in> Constant Tmod2")
      case True
      then show ?case
      proof (induct "c \<in> Constant Tmod3")
        case True
        then show ?case
        proof (induct "ConstType (tmod_combine Tmod1 Tmod2) c = ConstType Tmod3 c")
          case True
          then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = ConstType (tmod_combine Tmod1 Tmod2) c"
            unfolding tmod_combine_const_type_def
            using c_in_tmod12
            by simp
          show ?case
            using True.hyps True.prems
          proof (induct "ConstType Tmod1 c = ConstType Tmod2 c")
            case True
            then have "ConstType (tmod_combine Tmod1 Tmod2) c = tmod_combine_const_type Tmod1 Tmod2 c"
              by (simp add: tmod_combine_def)
            then have tmod12_def: "ConstType (tmod_combine Tmod1 Tmod2) c = ConstType Tmod1 c"
              unfolding tmod_combine_const_type_def
              using True.hyps True.prems(3) c_in_tmod1
              by simp
            then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = ConstType Tmod1 c"
              by (simp add: tmod12_tmod3_def)
            have "ConstType Tmod1 c = ConstType Tmod3 c"
              using True.prems(1) tmod12_def
              by simp
            then have tmod2_c_is_tmod3_c: "ConstType Tmod2 c = ConstType Tmod3 c"
              using True.hyps
              by simp
            have "ConstType (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type Tmod2 Tmod3 c"
              by (simp add: tmod_combine_def)
            then have tmod23_def: "ConstType (tmod_combine Tmod2 Tmod3) c = ConstType Tmod2 c"
              unfolding tmod_combine_const_type_def
              using True.prems(2) True.prems(3) tmod2_c_is_tmod3_c
              by simp
            then have "ConstType Tmod1 c = ConstType (tmod_combine Tmod2 Tmod3) c"
              using True.hyps
              by simp
            then have "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = ConstType Tmod1 c"
              unfolding tmod_combine_const_type_def
              by (simp add: c_in_tmod1 c_in_tmod23)
            then show ?case
              by (simp add: tmod12_tmod3_def)
          next
            case False
            then show ?case
            proof (induct "ConstType Tmod2 c = ConstType Tmod3 c")
              case True
              then have "ConstType (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type Tmod2 Tmod3 c"
                by (simp add: tmod_combine_def)
              then have tmod23_def: "ConstType (tmod_combine Tmod2 Tmod3) c = ConstType Tmod2 c"
                unfolding tmod_combine_const_type_def
                using True.hyps True.prems(3) True.prems(4)
                by simp
              then have "ConstType Tmod1 c \<noteq> ConstType (tmod_combine Tmod2 Tmod3) c"
                using False.hyps
                by simp
              then have tmod1_tmod23_def: "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = invalid"
                by (simp add: c_in_tmod1 c_in_tmod23 tmod_combine_const_type_def)
              have "ConstType (tmod_combine Tmod1 Tmod2) c = tmod_combine_const_type Tmod1 Tmod2 c"
                by (simp add: tmod_combine_def)
              then have tmod12_def: "ConstType (tmod_combine Tmod1 Tmod2) c = invalid"
                unfolding tmod_combine_const_type_def
                using False.hyps True.prems(4) c_in_tmod1
                by simp
              then have "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = invalid"
                by (simp add: tmod12_tmod3_def)
              then show ?case
                by (simp add: tmod1_tmod23_def)
            next
              case False
              have "ConstType (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type Tmod2 Tmod3 c"
                by (simp add: tmod_combine_def)
              then have tmod23_def: "ConstType (tmod_combine Tmod2 Tmod3) c = invalid"
                unfolding tmod_combine_const_type_def
                using False.hyps True.prems(1) True.prems(2)
                by simp
              then have tmod1_tmod23_def: "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = invalid"
                unfolding tmod_combine_const_type_def
                using Int_iff c_in_tmod1 c_in_tmod23
                by metis
              have "ConstType (tmod_combine Tmod1 Tmod2) c = tmod_combine_const_type Tmod1 Tmod2 c"
                by (simp add: tmod_combine_def)
              then have tmod12_def: "ConstType (tmod_combine Tmod1 Tmod2) c = invalid"
                unfolding tmod_combine_const_type_def
                using False.prems(1) True.prems(2) c_in_tmod1
                by simp
              then have "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = invalid"
                by (simp add: tmod12_tmod3_def)
              then show ?case
                by (simp add: tmod1_tmod23_def)
            qed
          qed
        next
          case False
          then show ?case
          proof (induct "ConstType Tmod1 c = ConstType Tmod2 c")
            case True
            then have "ConstType (tmod_combine Tmod1 Tmod2) c = tmod_combine_const_type Tmod1 Tmod2 c"
              by (simp add: tmod_combine_def)
            then have tmod12_def: "ConstType (tmod_combine Tmod1 Tmod2) c = ConstType Tmod1 c"
              unfolding tmod_combine_const_type_def
              using True.hyps True.prems(3) c_in_tmod1
              by simp
            then have "ConstType Tmod1 c \<noteq> ConstType Tmod3 c"
              using False.hyps
              by simp
            then have tmod2_c_is_not_tmod3_c: "ConstType Tmod2 c \<noteq> ConstType Tmod3 c"
              using True.hyps
              by simp
            have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = invalid"
              unfolding tmod_combine_const_type_def
              using False.hyps True.prems(2) c_in_tmod12
              by simp
            have "ConstType (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type Tmod2 Tmod3 c"
              by (simp add: tmod_combine_def)
            then have tmod23_def: "ConstType (tmod_combine Tmod2 Tmod3) c = invalid"
              unfolding tmod_combine_const_type_def
              using True.prems(2) True.prems(3) tmod2_c_is_not_tmod3_c
              by simp
            then have "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = invalid"
              unfolding tmod_combine_const_type_def
              using Int_iff c_in_tmod1 c_in_tmod23
              by metis
            then show ?case
              by (simp add: tmod12_tmod3_def)
          next
            case False
            then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = invalid"
              unfolding tmod_combine_const_type_def
              using False.prems(1) c_in_tmod12
              by simp
            then show ?case
              using False.hyps False.prems
            proof (induct "ConstType Tmod2 c = ConstType Tmod3 c")
              case True
              have "ConstType (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type Tmod2 Tmod3 c"
                by (simp add: tmod_combine_def)
              then have tmod23_def: "ConstType (tmod_combine Tmod2 Tmod3) c = ConstType Tmod2 c"
                unfolding tmod_combine_const_type_def
                using True.hyps True.prems(4) True.prems(5)
                by simp
              then have "ConstType Tmod1 c \<noteq> ConstType (tmod_combine Tmod2 Tmod3) c"
                using False.hyps
                by simp
              then have "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = invalid"
                unfolding tmod_combine_const_type_def
                by (simp add: c_in_tmod1 c_in_tmod23)
              then show ?case
                by (simp add: tmod12_tmod3_def)
            next
              case False
              have "ConstType (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type Tmod2 Tmod3 c"
                by (simp add: tmod_combine_def)
              then have tmod23_def: "ConstType (tmod_combine Tmod2 Tmod3) c = invalid"
                unfolding tmod_combine_const_type_def
                using False.hyps True.hyps True.prems
                by simp
              then have "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = invalid"
                unfolding tmod_combine_const_type_def
                using Int_iff c_in_tmod1 c_in_tmod23
                by metis
              then show ?case
                by (simp add: tmod12_tmod3_def)
            qed
          qed
        qed
      next
        case False
        then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = ConstType (tmod_combine Tmod1 Tmod2) c"
          unfolding tmod_combine_const_type_def
          using c_in_tmod12
          by simp
        have "ConstType (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type Tmod2 Tmod3 c"
          by (simp add: tmod_combine_def)
        then have tmod23_def: "ConstType (tmod_combine Tmod2 Tmod3) c = ConstType Tmod2 c"
          unfolding tmod_combine_const_type_def
          using False.hyps True.hyps
          by simp
        show ?case
        proof (induct "ConstType Tmod1 c = ConstType Tmod2 c")
          case True
          then have "ConstType (tmod_combine Tmod1 Tmod2) c = tmod_combine_const_type Tmod1 Tmod2 c"
            by (simp add: tmod_combine_def)
          then have tmod12_def: "ConstType (tmod_combine Tmod1 Tmod2) c = ConstType Tmod1 c"
            unfolding tmod_combine_const_type_def
            using False.prems True.hyps c_in_tmod1
            by simp
          have "ConstType Tmod1 c = ConstType (tmod_combine Tmod2 Tmod3) c"
            using True.hyps tmod23_def
            by simp
          then have "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = ConstType Tmod1 c"
            unfolding tmod_combine_const_type_def
            by (simp add: c_in_tmod1 c_in_tmod23)
          then have "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = ConstType Tmod1 c"
            by (simp add: tmod23_def)
          then show ?case
            by (simp add: tmod12_def tmod12_tmod3_def)
        next
          case False
          then have "ConstType (tmod_combine Tmod1 Tmod2) c = tmod_combine_const_type Tmod1 Tmod2 c"
            by (simp add: tmod_combine_def)
          then have tmod12_def: "ConstType (tmod_combine Tmod1 Tmod2) c = invalid"
            unfolding tmod_combine_const_type_def
            using False.hyps True.hyps c_in_tmod1
            by simp
          have "ConstType Tmod1 c \<noteq> ConstType (tmod_combine Tmod2 Tmod3) c"
            using False.hyps tmod23_def
            by simp
          then have "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = invalid"
            unfolding tmod_combine_const_type_def
            by (simp add: c_in_tmod1 c_in_tmod23)
          then show ?case
            by (simp add: tmod12_def tmod12_tmod3_def)
        qed
      qed
    next
      case False
      then have c_in_tmod3: "c \<in> Constant Tmod3"
        using Un_iff c_in_tmod23 select_convs(9) tmod_combine_def
        by metis
      then have c_in_tmod12_tmod3: "c \<in> Constant (tmod_combine Tmod1 Tmod2) \<inter> Constant Tmod3"
        by (simp add: c_in_tmod12)
      have c_in_tmod12_tmod3: "c \<in> Constant Tmod1 \<inter> Constant (tmod_combine Tmod2 Tmod3)"
        by (simp add: c_in_tmod1 c_in_tmod23)
      show ?case
        using False.hyps
      proof (induct "ConstType (tmod_combine Tmod1 Tmod2) c = ConstType Tmod3 c")
        case True
        then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = ConstType (tmod_combine Tmod1 Tmod2) c"
          unfolding tmod_combine_const_type_def
          using c_in_tmod12 c_in_tmod3
          by simp
        have "ConstType (tmod_combine Tmod1 Tmod2) c = tmod_combine_const_type Tmod1 Tmod2 c"
          by (simp add: tmod_combine_def)
        then have tmod12_def: "ConstType (tmod_combine Tmod1 Tmod2) c = ConstType Tmod1 c"
          unfolding tmod_combine_const_type_def
          using False.hyps c_in_tmod1
          by simp
        then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = ConstType Tmod1 c"
          by (simp add: tmod12_tmod3_def)
        have "ConstType (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type Tmod2 Tmod3 c"
          by (simp add: tmod_combine_def)
        then have tmod23_def: "ConstType (tmod_combine Tmod2 Tmod3) c = ConstType Tmod3 c"
          unfolding tmod_combine_const_type_def
          using False.hyps c_in_tmod3
          by simp
        have "ConstType Tmod1 c = ConstType Tmod3 c"
          using True.hyps tmod12_def
          by simp
        then have "ConstType Tmod1 c = ConstType (tmod_combine Tmod2 Tmod3) c"
          by (simp add: tmod23_def)
        then have "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = ConstType Tmod1 c"
          unfolding tmod_combine_const_type_def
          using c_in_tmod12_tmod3
          by simp
        then show ?case
          by (simp add: tmod12_tmod3_def)
      next
        case False
        then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = invalid"
          unfolding tmod_combine_const_type_def
          using c_in_tmod12 c_in_tmod3
          by simp
        have "ConstType (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type Tmod2 Tmod3 c"
          by (simp add: tmod_combine_def)
        then have tmod23_def: "ConstType (tmod_combine Tmod2 Tmod3) c = ConstType Tmod3 c"
          unfolding tmod_combine_const_type_def
          using False.prems c_in_tmod3
          by simp
        have "ConstType (tmod_combine Tmod1 Tmod2) c = tmod_combine_const_type Tmod1 Tmod2 c"
          by (simp add: tmod_combine_def)
        then have tmod12_def: "ConstType (tmod_combine Tmod1 Tmod2) c = ConstType Tmod1 c"
          unfolding tmod_combine_const_type_def
          using False.prems c_in_tmod1
          by simp
        then have "ConstType Tmod1 c \<noteq> ConstType Tmod3 c"
          using False.hyps
          by simp
        then have "ConstType Tmod1 c \<noteq> ConstType (tmod_combine Tmod2 Tmod3) c"
          by (simp add: tmod23_def)
        then have "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = invalid"
          unfolding tmod_combine_const_type_def
          by (simp add: c_in_tmod1 c_in_tmod23)
        then show ?case
          by (simp add: tmod12_tmod3_def)
      qed
    qed
  next
    assume c_in_tmod1: "c \<in> Constant Tmod1"
    then have c_in_tmod12: "c \<in> Constant (tmod_combine Tmod1 Tmod2)"
      by (simp add: tmod_combine_def)
    assume c_not_in_tmod23: "c \<notin> Constant (tmod_combine Tmod2 Tmod3)"
    then have c_not_in_tmod3: "c \<notin> Constant Tmod3"
      by (simp add: tmod_combine_def)
    then have "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = ConstType (tmod_combine Tmod1 Tmod2) c"
      unfolding tmod_combine_const_type_def
      using c_in_tmod12
      by simp
    then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = tmod_combine_const_type Tmod1 Tmod2 c"
      by (simp add: tmod_combine_def)
    have c_not_in_tmod2: "c \<notin> Constant Tmod2"
      using Un_iff c_not_in_tmod23 select_convs(9) tmod_combine_def
      by metis
    then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = ConstType Tmod1 c"
      using tmod12_tmod3_def
      unfolding tmod_combine_const_type_def
      by (simp add: c_in_tmod1)
    have "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = ConstType Tmod1 c"
      unfolding tmod_combine_const_type_def
      by (simp add: c_in_tmod1 c_not_in_tmod23) 
    then show "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c"
      using tmod12_tmod3_def
      by simp
  next
    assume c_not_in_tmod1: "c \<notin> Constant Tmod1"
    assume c_in_tmod23: "c \<in> Constant (tmod_combine Tmod2 Tmod3)"
    have "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = ConstType (tmod_combine Tmod2 Tmod3) c"
      unfolding tmod_combine_const_type_def
      by (simp add: c_in_tmod23 c_not_in_tmod1)
    then have tmod1_tmod23_def: "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type Tmod2 Tmod3 c"
      by (simp add: tmod_combine_def)
    have "tmod_combine_const_type Tmod2 Tmod3 c = tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c"
    proof (induct "c \<in> Constant Tmod2")
      case True
      then show ?case
      proof (induct "c \<in> Constant Tmod3")
        case True
        then have c_in_tmod12_tmod3: "c \<in> Constant (tmod_combine Tmod1 Tmod2) \<inter> Constant Tmod3"
          using IntI Un_iff simps(9) tmod_combine_def
          by metis
        have c_in_tmod2_tmod3: "c \<in> Constant Tmod2 \<inter> Constant Tmod3"
          using True.hyps True.prems
          by blast
        have "tmod_combine_const_type Tmod1 Tmod2 c = ConstType Tmod2 c"
          unfolding tmod_combine_const_type_def
          using True.prems c_not_in_tmod1
          by simp
        then have "ConstType (tmod_combine Tmod1 Tmod2) c = ConstType Tmod2 c"
          by (simp add: tmod_combine_def)
        then show ?case
          using True.hyps True.prems
        proof (induct "ConstType Tmod2 c = ConstType Tmod3 c")
          case True
          then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = ConstType Tmod2 c"
            unfolding tmod_combine_const_type_def
            using c_in_tmod12_tmod3
            by simp
          then have "tmod_combine_const_type Tmod2 Tmod3 c = ConstType Tmod2 c"
            unfolding tmod_combine_const_type_def
            using True.hyps c_in_tmod2_tmod3
            by simp
          then show ?case
            by (simp add: tmod12_tmod3_def)
        next
          case False
          then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = invalid"
            unfolding tmod_combine_const_type_def
            using c_in_tmod12_tmod3
            by simp
          then have "tmod_combine_const_type Tmod2 Tmod3 c = invalid"
            unfolding tmod_combine_const_type_def
            using False.hyps c_in_tmod2_tmod3
            by simp
          then show ?case
            by (simp add: tmod12_tmod3_def)
        qed
      next
        case False
        then have c_in_tmod12: "c \<in> Constant (tmod_combine Tmod1 Tmod2)"
          using Un_iff simps(9) tmod_combine_def
          by metis
        then have "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = ConstType (tmod_combine Tmod1 Tmod2) c"
          unfolding tmod_combine_const_type_def
          using False.hyps
          by simp
        then have tmod12_tmod3_def: "tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c = tmod_combine_const_type Tmod1 Tmod2 c"
          by (simp add: tmod_combine_def)
        then show ?case
          unfolding tmod_combine_const_type_def
          using tmod12_tmod3_def False.hyps c_not_in_tmod1
          by simp
      qed
    next
      case False
      then have c_not_in_tmod12: "c \<notin> Constant (tmod_combine Tmod1 Tmod2)"
        using Un_iff c_not_in_tmod1 select_convs(9) tmod_combine_def
        by metis
      show ?case
        unfolding tmod_combine_const_type_def
        using False.hyps c_not_in_tmod12
        by simp
    qed
    then show "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c"
      by (simp add: tmod1_tmod23_def)
  next
    assume c_not_in_tmod1: "c \<notin> Constant Tmod1"
    assume c_not_in_tmod23: "c \<notin> Constant (tmod_combine Tmod2 Tmod3)"
    have c_not_in_tmod12: "c \<notin> Constant (tmod_combine Tmod1 Tmod2)"
      using Un_iff c_not_in_tmod1 c_not_in_tmod23 simps(9) tmod_combine_def
      by metis
    have c_not_in_tmod3: "c \<notin> Constant Tmod3"
      using Un_iff c_not_in_tmod23 select_convs(9) tmod_combine_def
      by metis
    show "tmod_combine_const_type Tmod1 (tmod_combine Tmod2 Tmod3) c = tmod_combine_const_type (tmod_combine Tmod1 Tmod2) Tmod3 c"
      unfolding tmod_combine_const_type_def
      using c_not_in_tmod1 c_not_in_tmod23 c_not_in_tmod12 c_not_in_tmod3
      by simp
  qed
qed

lemma tmod_combine_prop_assoc: "tmod_combine_prop Tmod1 (tmod_combine Tmod2 Tmod3) = tmod_combine_prop (tmod_combine Tmod1 Tmod2) Tmod3"
proof
  show "tmod_combine_prop Tmod1 (tmod_combine Tmod2 Tmod3) \<subseteq> tmod_combine_prop (tmod_combine Tmod1 Tmod2) Tmod3"
  proof
    fix x
    assume "x \<in> tmod_combine_prop Tmod1 (tmod_combine Tmod2 Tmod3)"
    then show "x \<in> tmod_combine_prop (tmod_combine Tmod1 Tmod2) Tmod3"
    proof (induct)
      case (abstract_property_tmod1 c)
      then show ?case
        using UnI1 UnI2 select_convs(8) simps(1) tmod_combine_def tmod_combine_prop.abstract_property_tmod1
        by metis
    next
      case (abstract_property_tmod2 c)
      then have "abstract c \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case abstract_property_tmod1
        then show ?thesis
          by (simp add: abstract_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.abstract_property_tmod2)
      next
        case abstract_property_tmod2
        then show ?thesis
          using Un_iff abstract_property_tmod2.hyps(2) simps(1) tmod_combine_def tmod_combine_prop.abstract_property_tmod2
          by metis
      next
        case abstract_property_both
        then show ?thesis
          by (simp add: abstract_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.abstract_property_both tmod_combine_prop.abstract_property_tmod2)
      qed
    next
      case (abstract_property_both c)
      then have "abstract c \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case abstract_property_tmod1
        then show ?thesis
          using abstract_property_both.hyps(1) select_convs(8) tmod_combine_def tmod_combine_prop.abstract_property_both tmod_combine_prop.abstract_property_tmod1
          by metis
      next
        case abstract_property_tmod2
        then show ?thesis
          by (simp add: abstract_property_both.hyps(1) tmod_combine_def tmod_combine_prop.abstract_property_both tmod_combine_prop.abstract_property_tmod1)
      next
        case abstract_property_both
        then show ?thesis
          by (simp add: abstract_property_both.hyps(1) tmod_combine_def tmod_combine_prop.abstract_property_both)
      qed
    next
      case (containment_property_tmod1 r)
      then show ?case
        using select_convs(8) tmod_combine_def tmod_combine_prop.containment_property_tmod1
        by metis
    next
      case (containment_property_tmod2 r)
      then have "containment r \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case containment_property_tmod1
        then show ?thesis
          by (simp add: tmod_combine_def tmod_combine_prop.containment_property_tmod2)
      next
        case containment_property_tmod2
        then show ?thesis
          by (fact tmod_combine_prop.containment_property_tmod2)
      qed
    next
      case (default_value_property_tmod1 f v)
      then show ?case
        using Un_iff select_convs(4) select_convs(8) tmod_combine_def tmod_combine_prop.default_value_property_tmod1
        by metis
    next
      case (default_value_property_tmod2 f v)
      then have "defaultValue f v \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case default_value_property_tmod1
        then show ?thesis
          by (simp add: default_value_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.default_value_property_tmod2)
      next
        case default_value_property_tmod2
        then show ?thesis
          by (simp add: default_value_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.default_value_property_tmod1)
      next
        case default_value_property_both
        then show ?thesis
          by (simp add: default_value_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.default_value_property_both tmod_combine_prop.default_value_property_tmod2)
      qed
    next
      case (default_value_property_both f v)
      then have "defaultValue f v \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case default_value_property_tmod1
        then show ?thesis
          by (simp add: default_value_property_both.hyps(1) tmod_combine_def tmod_combine_prop.default_value_property_both tmod_combine_prop.default_value_property_tmod2)
      next
        case default_value_property_tmod2
        then show ?thesis
          by (simp add: default_value_property_both.hyps(1) tmod_combine_def tmod_combine_prop.default_value_property_both tmod_combine_prop.default_value_property_tmod1)
      next
        case default_value_property_both
        then show ?thesis
          by (simp add: default_value_property_both.hyps(1) tmod_combine_def tmod_combine_prop.default_value_property_both)
      qed
    next
      case (identity_property_tmod1 c A)
      then show ?case
        using Un_iff select_convs(1) select_convs(8) tmod_combine_def tmod_combine_prop.identity_property_tmod1
        by metis
    next
      case (identity_property_tmod2 c A)
      then have "identity c A \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case identity_property_tmod1
        then show ?thesis
          by (simp add: identity_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.identity_property_tmod2)
      next
        case identity_property_tmod2
        then show ?thesis
          by (simp add: identity_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.identity_property_tmod1)
      next
        case identity_property_both
        then show ?thesis
          by (simp add: identity_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.identity_property_both tmod_combine_prop.identity_property_tmod2)
      qed
    next
      case (identity_property_both c A)
      then have "identity c A \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case identity_property_tmod1
        then show ?thesis
          by (simp add: identity_property_both.hyps(1) tmod_combine_def tmod_combine_prop.identity_property_both tmod_combine_prop.identity_property_tmod2)
      next
        case identity_property_tmod2
        then show ?thesis
          by (simp add: identity_property_both.hyps(1) tmod_combine_def tmod_combine_prop.identity_property_both tmod_combine_prop.identity_property_tmod1)
      next
        case identity_property_both
        then show ?thesis
          by (simp add: identity_property_both.hyps(1) tmod_combine_def tmod_combine_prop.identity_property_both)
      qed
    next
      case (keyset_property_tmod1 r A)
      then show ?case
        using Un_iff select_convs(4) select_convs(8) tmod_combine_def tmod_combine_prop.keyset_property_tmod1
        by metis
    next
      case (keyset_property_tmod2 r A)
      then have "keyset r A \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case keyset_property_tmod1
        then show ?thesis
          by (simp add: keyset_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.keyset_property_tmod2)
      next
        case keyset_property_tmod2
        then show ?thesis
          by (simp add: keyset_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.keyset_property_tmod1)
      next
        case keyset_property_both
        then show ?thesis
          by (simp add: keyset_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.keyset_property_both tmod_combine_prop.keyset_property_tmod2)
      qed
    next
      case (keyset_property_both r A)
      then have "keyset r A \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case keyset_property_tmod1
        then show ?thesis
          by (simp add: keyset_property_both.hyps(1) tmod_combine_def tmod_combine_prop.keyset_property_both tmod_combine_prop.keyset_property_tmod2)
      next
        case keyset_property_tmod2
        then show ?thesis
          by (simp add: keyset_property_both.hyps(1) tmod_combine_def tmod_combine_prop.keyset_property_both tmod_combine_prop.keyset_property_tmod1)
      next
        case keyset_property_both
        then show ?thesis
          by (simp add: keyset_property_both.hyps(1) tmod_combine_def tmod_combine_prop.keyset_property_both)
      qed
    next
      case (opposite_property_tmod1 r1 r2)
      then show ?case
        using Un_iff select_convs(4) select_convs(8) tmod_combine_def tmod_combine_prop.opposite_property_tmod1
        by metis
    next
      case (opposite_property_tmod2 r1 r2)
      then have "opposite r1 r2 \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case opposite_property_tmod1
        then show ?thesis
          by (simp add: opposite_property_tmod2.hyps(2) opposite_property_tmod2.hyps(3) tmod_combine_def tmod_combine_prop.opposite_property_tmod2)
      next
        case opposite_property_tmod2
        then show ?thesis
          by (simp add: opposite_property_tmod2.hyps(2) opposite_property_tmod2.hyps(3) tmod_combine_def tmod_combine_prop.opposite_property_tmod1)
      next
        case opposite_property_both
        then show ?thesis
          by (simp add: opposite_property_tmod2.hyps(2) opposite_property_tmod2.hyps(3) tmod_combine_def tmod_combine_prop.opposite_property_both tmod_combine_prop.opposite_property_tmod2)
      qed
    next
      case (opposite_property_both r1 r2)
      then have "opposite r1 r2 \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case opposite_property_tmod1
        then show ?thesis
          by (simp add: opposite_property_both.hyps(1) tmod_combine_def tmod_combine_prop.opposite_property_both tmod_combine_prop.opposite_property_tmod2)
      next
        case opposite_property_tmod2
        then show ?thesis
          by (simp add: opposite_property_both.hyps(1) tmod_combine_def tmod_combine_prop.opposite_property_both tmod_combine_prop.opposite_property_tmod1)
      next
        case opposite_property_both
        then show ?thesis
          by (simp add: opposite_property_both.hyps(1) tmod_combine_def tmod_combine_prop.opposite_property_both)
      qed
    next
      case (readonly_property_tmod1 f)
      then show ?case
        using Un_iff select_convs(4) select_convs(8) tmod_combine_def tmod_combine_prop.readonly_property_tmod1
        by metis
    next
      case (readonly_property_tmod2 f)
      then have "readonly f \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case readonly_property_tmod1
        then show ?thesis
          by (simp add: readonly_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.readonly_property_tmod2)
      next
        case readonly_property_tmod2
        then show ?thesis
          by (simp add: readonly_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.readonly_property_tmod1)
      next
        case readonly_property_both
        then show ?thesis
          by (simp add: readonly_property_tmod2.hyps(2) tmod_combine_def tmod_combine_prop.readonly_property_both tmod_combine_prop.readonly_property_tmod2)
      qed
    next
      case (readonly_property_both f)
      then have "readonly f \<in> tmod_combine_prop Tmod2 Tmod3"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case readonly_property_tmod1
        then show ?thesis
          by (simp add: readonly_property_both.hyps(1) tmod_combine_def tmod_combine_prop.readonly_property_both tmod_combine_prop.readonly_property_tmod2)
      next
        case readonly_property_tmod2
        then show ?thesis
          by (simp add: readonly_property_both.hyps(1) tmod_combine_def tmod_combine_prop.readonly_property_both tmod_combine_prop.readonly_property_tmod1)
      next
        case readonly_property_both
        then show ?thesis
          by (simp add: readonly_property_both.hyps(1) tmod_combine_def tmod_combine_prop.readonly_property_both)
      qed
    qed
  qed
next
  show "tmod_combine_prop (tmod_combine Tmod1 Tmod2) Tmod3 \<subseteq> tmod_combine_prop Tmod1 (tmod_combine Tmod2 Tmod3)"
  proof
    fix x
    assume "x \<in> tmod_combine_prop (tmod_combine Tmod1 Tmod2) Tmod3"
    then show "x \<in> tmod_combine_prop Tmod1 (tmod_combine Tmod2 Tmod3)"
    proof (induct)
      case (abstract_property_tmod1 c)
      then have "abstract c \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case abstract_property_tmod1
        then show ?thesis
          by (simp add: abstract_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.abstract_property_tmod1)
      next
        case abstract_property_tmod2
        then show ?thesis
          by (simp add: abstract_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.abstract_property_tmod1 tmod_combine_prop.abstract_property_tmod2)
      next
        case abstract_property_both
        then show ?thesis
          by (simp add: abstract_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.abstract_property_both tmod_combine_prop.abstract_property_tmod1)
      qed
    next
      case (abstract_property_tmod2 c)
      then show ?case
        by (simp add: tmod_combine_def tmod_combine_prop.abstract_property_tmod2)
    next
      case (abstract_property_both c)
      then have "abstract c \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case abstract_property_tmod1
        then show ?thesis
          by (simp add: abstract_property_both.hyps(2) tmod_combine_def tmod_combine_prop.abstract_property_both tmod_combine_prop.abstract_property_tmod2)
      next
        case abstract_property_tmod2
        then show ?thesis
          by (simp add: abstract_property_both.hyps(2) tmod_combine_def tmod_combine_prop.abstract_property_both tmod_combine_prop.abstract_property_tmod2)
      next
        case abstract_property_both
        then show ?thesis
          by (simp add: abstract_property_both.hyps(2) tmod_combine_def tmod_combine_prop.abstract_property_both)
      qed
    next
      case (containment_property_tmod1 r)
      then have "containment r \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case containment_property_tmod1
        then show ?thesis
          by (fact tmod_combine_prop.containment_property_tmod1)
      next
        case containment_property_tmod2
        then show ?thesis
          by (simp add: tmod_combine_def tmod_combine_prop.containment_property_tmod1 tmod_combine_prop.containment_property_tmod2)
      qed
    next
      case (containment_property_tmod2 r)
      then show ?case
        by (simp add: tmod_combine_def tmod_combine_prop.containment_property_tmod2)
    next
      case (default_value_property_tmod1 f v)
      then have "defaultValue f v \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case default_value_property_tmod1
        then show ?thesis
          by (simp add: default_value_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.default_value_property_tmod1)
      next
        case default_value_property_tmod2
        then show ?thesis
          by (simp add: default_value_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.default_value_property_tmod1 tmod_combine_prop.default_value_property_tmod2)
      next
        case default_value_property_both
        then show ?thesis
          by (simp add: default_value_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.default_value_property_both tmod_combine_prop.default_value_property_tmod1)
      qed
    next
      case (default_value_property_tmod2 f v)
      then show ?case
        by (simp add: tmod_combine_def tmod_combine_prop.default_value_property_tmod2)
    next
      case (default_value_property_both f v)
      then have "defaultValue f v \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case default_value_property_tmod1
        then show ?thesis
          by (simp add: default_value_property_both.hyps(2) tmod_combine_def tmod_combine_prop.default_value_property_both tmod_combine_prop.default_value_property_tmod2)
      next
        case default_value_property_tmod2
        then show ?thesis
          by (simp add: default_value_property_both.hyps(2) tmod_combine_def tmod_combine_prop.default_value_property_both tmod_combine_prop.default_value_property_tmod2)
      next
        case default_value_property_both
        then show ?thesis
          by (simp add: default_value_property_both.hyps(2) tmod_combine_def tmod_combine_prop.default_value_property_both)
      qed
    next
      case (identity_property_tmod1 c A)
      then have "identity c A \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case identity_property_tmod1
        then show ?thesis
          by (simp add: identity_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.identity_property_tmod1)
      next
        case identity_property_tmod2
        then show ?thesis
          by (simp add: identity_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.identity_property_tmod1 tmod_combine_prop.identity_property_tmod2)
      next
        case identity_property_both
        then show ?thesis
          by (simp add: identity_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.identity_property_both tmod_combine_prop.identity_property_tmod1)
      qed
    next
      case (identity_property_tmod2 c A)
      then show ?case
        by (simp add: tmod_combine_def tmod_combine_prop.identity_property_tmod2)
    next
      case (identity_property_both c A)
      then have "identity c A \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case identity_property_tmod1
        then show ?thesis
          by (simp add: identity_property_both.hyps(2) tmod_combine_def tmod_combine_prop.identity_property_both tmod_combine_prop.identity_property_tmod2)
      next
        case identity_property_tmod2
        then show ?thesis
          by (simp add: identity_property_both.hyps(2) tmod_combine_def tmod_combine_prop.identity_property_both tmod_combine_prop.identity_property_tmod2)
      next
        case identity_property_both
        then show ?thesis
          by (simp add: identity_property_both.hyps(2) tmod_combine_def tmod_combine_prop.identity_property_both)
      qed
    next
      case (keyset_property_tmod1 r A)
      then have "keyset r A \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case keyset_property_tmod1
        then show ?thesis
          by (simp add: keyset_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.keyset_property_tmod1)
      next
        case keyset_property_tmod2
        then show ?thesis
          by (simp add: keyset_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.keyset_property_tmod1 tmod_combine_prop.keyset_property_tmod2)
      next
        case keyset_property_both
        then show ?thesis
          by (simp add: keyset_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.keyset_property_both tmod_combine_prop.keyset_property_tmod1)
      qed
    next
      case (keyset_property_tmod2 r A)
      then show ?case
        by (simp add: tmod_combine_def tmod_combine_prop.keyset_property_tmod2)
    next
      case (keyset_property_both r A)
      then have "keyset r A \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case keyset_property_tmod1
        then show ?thesis
          by (simp add: keyset_property_both.hyps(2) tmod_combine_def tmod_combine_prop.keyset_property_both tmod_combine_prop.keyset_property_tmod2)
      next
        case keyset_property_tmod2
        then show ?thesis
          by (simp add: keyset_property_both.hyps(2) tmod_combine_def tmod_combine_prop.keyset_property_both tmod_combine_prop.keyset_property_tmod2)
      next
        case keyset_property_both
        then show ?thesis
          by (simp add: keyset_property_both.hyps(2) tmod_combine_def tmod_combine_prop.keyset_property_both)
      qed
    next
      case (opposite_property_tmod1 r1 r2)
      then have "opposite r1 r2 \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case opposite_property_tmod1
        then show ?thesis
          by (simp add: opposite_property_tmod1.hyps(2) opposite_property_tmod1.hyps(3) tmod_combine_def tmod_combine_prop.opposite_property_tmod1)
      next
        case opposite_property_tmod2
        then show ?thesis
          by (simp add: opposite_property_tmod1.hyps(2) opposite_property_tmod1.hyps(3) tmod_combine_def tmod_combine_prop.opposite_property_tmod1 tmod_combine_prop.opposite_property_tmod2)
      next
        case opposite_property_both
        then show ?thesis
          by (simp add: opposite_property_tmod1.hyps(2) opposite_property_tmod1.hyps(3) tmod_combine_def tmod_combine_prop.opposite_property_both tmod_combine_prop.opposite_property_tmod1)
      qed
    next
      case (opposite_property_tmod2 r1 r2)
      then show ?case
        by (simp add: tmod_combine_def tmod_combine_prop.opposite_property_tmod2)
    next
      case (opposite_property_both r1 r2)
      then have "opposite r1 r2 \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case opposite_property_tmod1
        then show ?thesis
          by (simp add: opposite_property_both.hyps(2) tmod_combine_def tmod_combine_prop.opposite_property_both tmod_combine_prop.opposite_property_tmod2)
      next
        case opposite_property_tmod2
        then show ?thesis
          by (simp add: opposite_property_both.hyps(2) tmod_combine_def tmod_combine_prop.opposite_property_both tmod_combine_prop.opposite_property_tmod2)
      next
        case opposite_property_both
        then show ?thesis
          by (simp add: opposite_property_both.hyps(2) tmod_combine_def tmod_combine_prop.opposite_property_both)
      qed
    next
      case (readonly_property_tmod1 f)
      then have "readonly f \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case readonly_property_tmod1
        then show ?thesis
          by (simp add: readonly_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.readonly_property_tmod1)
      next
        case readonly_property_tmod2
        then show ?thesis
          by (simp add: readonly_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.readonly_property_tmod1 tmod_combine_prop.readonly_property_tmod2)
      next
        case readonly_property_both
        then show ?thesis
          by (simp add: readonly_property_tmod1.hyps(2) tmod_combine_def tmod_combine_prop.readonly_property_both tmod_combine_prop.readonly_property_tmod1)
      qed
    next
      case (readonly_property_tmod2 f)
      then show ?case
        by (simp add: tmod_combine_def tmod_combine_prop.readonly_property_tmod2)
    next
      case (readonly_property_both f)
      then have "readonly f \<in> tmod_combine_prop Tmod1 Tmod2"
        by (simp add: tmod_combine_def)
      then show ?case
      proof (cases)
        case readonly_property_tmod1
        then show ?thesis
          by (simp add: readonly_property_both.hyps(2) tmod_combine_def tmod_combine_prop.readonly_property_both tmod_combine_prop.readonly_property_tmod2)
      next
        case readonly_property_tmod2
        then show ?thesis
          by (simp add: readonly_property_both.hyps(2) tmod_combine_def tmod_combine_prop.readonly_property_both tmod_combine_prop.readonly_property_tmod2)
      next
        case readonly_property_both
        then show ?thesis
          by (simp add: readonly_property_both.hyps(2) tmod_combine_def tmod_combine_prop.readonly_property_both)
      qed
    qed
  qed
qed

lemma tmod_combine_assoc: "tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3 = tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3)"
proof-
  have "\<And>Tmod12 Tmod23. Tmod12 = tmod_combine Tmod1 Tmod2 \<Longrightarrow> Tmod23 = tmod_combine Tmod2 Tmod3 \<Longrightarrow> tmod_combine Tmod12 Tmod3 = tmod_combine Tmod1 Tmod23"
  proof-
    fix Tmod12
    fix Tmod23
    assume tmod12_def: "Tmod12 = tmod_combine Tmod1 Tmod2"
    assume tmod23_def: "Tmod23 = tmod_combine Tmod2 Tmod3"
    show "tmod_combine Tmod12 Tmod3 = tmod_combine Tmod1 Tmod23"
      unfolding tmod_combine_def
    proof (simp)
      show "Class Tmod12 \<union> Class Tmod3 = Class Tmod1 \<union> Class Tmod23 \<and>
          Enum Tmod12 \<union> Enum Tmod3 = Enum Tmod1 \<union> Enum Tmod23 \<and>
          UserDataType Tmod12 \<union> UserDataType Tmod3 = UserDataType Tmod1 \<union> UserDataType Tmod23 \<and>
          type_model.Field Tmod12 \<union> Field Tmod3 = Field Tmod1 \<union> Field Tmod23 \<and>
          tmod_combine_fieldsig Tmod12 Tmod3 = tmod_combine_fieldsig Tmod1 Tmod23 \<and>
          EnumValue Tmod12 \<union> EnumValue Tmod3 = EnumValue Tmod1 \<union> EnumValue Tmod23 \<and>
          Inh Tmod12 \<union> Inh Tmod3 = Inh Tmod1 \<union> Inh Tmod23 \<and> 
          tmod_combine_prop Tmod12 Tmod3 = tmod_combine_prop Tmod1 Tmod23 \<and> 
          Constant Tmod12 \<union> Constant Tmod3 = Constant Tmod1 \<union> Constant Tmod23 \<and> 
          tmod_combine_const_type Tmod12 Tmod3 = tmod_combine_const_type Tmod1 Tmod23"
        using tmod12_def tmod23_def
      proof (intro conjI)
        show "tmod_combine_fieldsig Tmod12 Tmod3 = tmod_combine_fieldsig Tmod1 Tmod23"
          by (simp add: tmod12_def tmod23_def tmod_combine_fieldsig_assoc)
      next
        show "tmod_combine_prop Tmod12 Tmod3 = tmod_combine_prop Tmod1 Tmod23"
          using tmod12_def tmod23_def tmod_combine_prop_assoc
          by blast
      next
        show "tmod_combine_const_type Tmod12 Tmod3 = tmod_combine_const_type Tmod1 Tmod23"
          by (simp add: tmod12_def tmod23_def tmod_combine_const_type_assoc)
      qed (simp_all add: sup_assoc tmod_combine_def)
    qed
  qed
  then show ?thesis
    by blast
qed

lemma tmod_combine_idemp':
  assumes structure_fieldsig_domain: "\<And>f. f \<notin> Field Tmod2 \<Longrightarrow> FieldSig Tmod2 f = undefined"
  assumes structure_consttype_domain: "\<And>c. c \<notin> Constant Tmod2 \<Longrightarrow> ConstType Tmod2 c = undefined"
  shows "tmod_combine (tmod_combine Tmod1 Tmod2) Tmod2 = tmod_combine Tmod1 Tmod2"
proof-
  have "tmod_combine Tmod2 Tmod2 = truncate Tmod2"
  proof (intro tmod_combine_idemp)
    show "\<And>f. f \<notin> type_model.Field Tmod2 \<Longrightarrow> FieldSig Tmod2 f = undefined"
      using structure_fieldsig_domain
      by blast
  next
    show "\<And>c. c \<notin> Constant Tmod2 \<Longrightarrow> ConstType Tmod2 c = undefined"
      using structure_consttype_domain
      by blast
  qed
  then have second_type_model_idemp: "tmod_combine Tmod2 Tmod2 = Tmod2"
    unfolding truncate_def
    by simp
  then show ?thesis
    by (simp add: tmod_combine_assoc)
qed

lemma tmod_combine_idemp'_alt:
  assumes second_type_model_correct: "type_model Tmod2"
  shows "tmod_combine (tmod_combine Tmod1 Tmod2) Tmod2 = tmod_combine Tmod1 Tmod2"
proof (intro tmod_combine_idemp')
  show "\<And>f. f \<notin> type_model.Field Tmod2 \<Longrightarrow> FieldSig Tmod2 f = undefined"
    using second_type_model_correct type_model.structure_fieldsig_domain
    by blast
next
  show "\<And>c. c \<notin> Constant Tmod2 \<Longrightarrow> ConstType Tmod2 c = undefined"
    using second_type_model_correct type_model.structure_consttype_domain
    by blast
qed


section "Validity of a combination of type models"

lemma tmod_combine_correct[intro]:
  assumes tmod1_correct: "type_model Tmod1"
  assumes tmod2_correct: "type_model Tmod2"
  assumes structure_fieldsig_wellformed_type: "\<And>f. f \<in> Field Tmod1 \<inter> Field Tmod2 \<Longrightarrow> fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)"
  assumes structure_fieldsig_wellformed_multiplicity: "\<And>f. f \<in> Field Tmod1 \<inter> Field Tmod2 \<Longrightarrow> multiplicity (snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f))"
  assumes structure_consttype_wellformed_type: "\<And>c. c \<in> Constant Tmod1 \<inter> Constant Tmod2 \<Longrightarrow> ConstType Tmod1 c = ConstType Tmod2 c"
  assumes property_class_disjoint_tmod1: "\<And>c. c \<in> Class Tmod1 \<Longrightarrow> c \<notin> Enum Tmod2 \<and> c \<notin> UserDataType Tmod2"
  assumes property_class_disjoint_tmod2: "\<And>c. c \<in> Class Tmod2 \<Longrightarrow> c \<notin> Enum Tmod1 \<and> c \<notin> UserDataType Tmod1"
  assumes property_enum_disjoint_tmod1: "\<And>e. e \<in> Enum Tmod1 \<Longrightarrow> e \<notin> Class Tmod2 \<and> e \<notin> UserDataType Tmod2"
  assumes property_enum_disjoint_tmod2: "\<And>e. e \<in> Enum Tmod2 \<Longrightarrow> e \<notin> Class Tmod1 \<and> e \<notin> UserDataType Tmod1"
  assumes property_namespace_restriction_tmod12: "\<And>x y. x \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1 \<Longrightarrow> y \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2 \<Longrightarrow> \<not>id_in_ns x (Identifier y)"
  assumes property_namespace_restriction_tmod21: "\<And>x y. x \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2 \<Longrightarrow> y \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1 \<Longrightarrow> \<not>id_in_ns x (Identifier y)"
  assumes property_inh_wellformed_relation: "irrefl ((Inh Tmod1 \<union> Inh Tmod2)\<^sup>+)"
  assumes consistency_identity_valid: "\<And>c1 c2 A B. identity c1 A \<in> tmod_combine_prop Tmod1 Tmod2 \<Longrightarrow> identity c2 B \<in> tmod_combine_prop Tmod1 Tmod2 \<Longrightarrow> 
    c1 \<noteq> c2 \<Longrightarrow> \<not>(\<exclamdown>c1 \<sqsubseteq>[Tmod1] \<exclamdown>c2) \<Longrightarrow> \<not>(\<exclamdown>c1 \<sqsubseteq>[Tmod2] \<exclamdown>c2) \<Longrightarrow> \<exclamdown>c1 \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>c2 \<Longrightarrow> A \<subseteq> B"
  shows "type_model (tmod_combine Tmod1 Tmod2)"
proof (intro type_model.intro)
  fix f
  assume "f \<in> Field (tmod_combine Tmod1 Tmod2)"
  then have "f \<in> Field Tmod1 \<or> f \<in> Field Tmod2"
    unfolding tmod_combine_def
    by simp
  then have "fst f \<in> Class Tmod1 \<or> fst f \<in> Class Tmod2"
    using tmod1_correct tmod2_correct type_model.structure_field_wellformed_class by blast
  then show "fst f \<in> Class (tmod_combine Tmod1 Tmod2)"
    by (simp add: tmod_combine_def)
next
  fix f
  assume "f \<in> Field (tmod_combine Tmod1 Tmod2)"
  then show "fst (FieldSig (tmod_combine Tmod1 Tmod2) f) \<in> Type (tmod_combine Tmod1 Tmod2) \<and> multiplicity (snd (FieldSig (tmod_combine Tmod1 Tmod2) f))"
  proof (intro conjI)
    assume "f \<in> Field (tmod_combine Tmod1 Tmod2)"
    then show "fst (FieldSig (tmod_combine Tmod1 Tmod2) f) \<in> Type (tmod_combine Tmod1 Tmod2)"
      using structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_type_func_element_of_types type_def type_model.structure_fieldsig_wellformed_type
      by metis
  next
    assume "f \<in> Field (tmod_combine Tmod1 Tmod2)"
    then have "f \<in> Field Tmod1 \<union> Field Tmod2"
      by (simp add: tmod_combine_def)
    then have "f \<in> Field Tmod1 \<inter> Field Tmod2 \<or> f \<in> Field Tmod1 - Field Tmod2 \<or> f \<in> Field Tmod2 - Field Tmod1"
      by blast
    then show "multiplicity (snd (FieldSig (tmod_combine Tmod1 Tmod2) f))"
    proof (elim disjE)
      assume f_in_tmods: "f \<in> Field Tmod1 \<inter> Field Tmod2"
      then have "snd (FieldSig (tmod_combine Tmod1 Tmod2) f) = snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f)"
        by (simp add: structure_fieldsig_wellformed_type tmod_combine_def tmod_combine_fieldsig_def)
      then show "multiplicity (snd (FieldSig (tmod_combine Tmod1 Tmod2) f))"
        using f_in_tmods structure_fieldsig_wellformed_multiplicity 
        by simp
    next
      assume f_in_tmod1: "f \<in> Field Tmod1 - Field Tmod2"
      then have "FieldSig (tmod_combine Tmod1 Tmod2) f = FieldSig Tmod1 f"
        unfolding tmod_combine_def tmod_combine_fieldsig_def
        by simp
      then show "multiplicity (snd (FieldSig (tmod_combine Tmod1 Tmod2) f))"
        using f_in_tmod1 tmod1_correct type_model.structure_fieldsig_wellformed_multiplicity 
        by fastforce
    next
      assume f_in_tmod2: "f \<in> Field Tmod2 - Field Tmod1"
      then have "FieldSig (tmod_combine Tmod1 Tmod2) f = FieldSig Tmod2 f"
        unfolding tmod_combine_def tmod_combine_fieldsig_def
        by simp
      then show "multiplicity (snd (FieldSig (tmod_combine Tmod1 Tmod2) f))"
        using f_in_tmod2 tmod2_correct type_model.structure_fieldsig_wellformed_multiplicity 
        by fastforce
    qed
  qed
next
  fix f
  assume "f \<notin> Field (tmod_combine Tmod1 Tmod2)"
  then have "f \<notin> Field Tmod1 \<union> Field Tmod2"
    by (simp add: tmod_combine_def)
  then show "FieldSig (tmod_combine Tmod1 Tmod2) f = undefined"
    unfolding tmod_combine_def tmod_combine_fieldsig_def
    by simp
next
  fix ev
  assume "ev \<in> EnumValue (tmod_combine Tmod1 Tmod2)"
  then have "ev \<in> EnumValue Tmod1 \<or> ev \<in> EnumValue Tmod2"
    by (simp add: tmod_combine_def)
  then show "fst ev \<in> Enum (tmod_combine Tmod1 Tmod2)"
    using Un_iff simps(2) tmod1_correct tmod2_correct tmod_combine_def type_model.structure_enumvalue_wellformed_enum
    by metis
next
  fix c
  assume "c \<in> Inh (tmod_combine Tmod1 Tmod2)"
  then have "c \<in> Inh Tmod1 \<union> Inh Tmod2"
    by (simp add: tmod_combine_def)
  then have "fst c \<in> Class Tmod1 \<union> Class Tmod2 \<and> snd c \<in> Class Tmod1 \<union> Class Tmod2"
  proof (intro conjI)
    fix c
    assume "c \<in> Inh Tmod1 \<union> Inh Tmod2"
    then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
    proof (elim UnE)
      assume "c \<in> Inh Tmod1"
      then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
        by (simp add: tmod1_correct tmod_combine_def type_model.structure_inh_wellformed_fst_class)
    next
      assume "c \<in> Inh Tmod2"
      then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
        by (simp add: tmod2_correct tmod_combine_def type_model.structure_inh_wellformed_fst_class)
    qed
  next
    fix c
    assume "c \<in> Inh Tmod1 \<union> Inh Tmod2"
    then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
    proof (elim UnE)
      assume "c \<in> Inh Tmod1"
      then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
        by (simp add: tmod1_correct tmod_combine_def type_model.structure_inh_wellformed_snd_class)
    next
      assume "c \<in> Inh Tmod2"
      then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
        by (simp add: tmod2_correct tmod_combine_def type_model.structure_inh_wellformed_snd_class)
    qed
  qed
  then show "fst c \<in> Class (tmod_combine Tmod1 Tmod2) \<and> snd c \<in> Class (tmod_combine Tmod1 Tmod2)"
    unfolding tmod_combine_def
    by simp
next
  have inh_wellformed_classes: "\<And>c. c \<in> Inh (tmod_combine Tmod1 Tmod2) \<Longrightarrow> fst c \<in> Class (tmod_combine Tmod1 Tmod2) \<and> snd c \<in> Class (tmod_combine Tmod1 Tmod2)"
  proof-
    fix c
    assume "c \<in> Inh (tmod_combine Tmod1 Tmod2)"
    then have "c \<in> Inh Tmod1 \<union> Inh Tmod2"
      by (simp add: tmod_combine_def)
    then have "fst c \<in> Class Tmod1 \<union> Class Tmod2 \<and> snd c \<in> Class Tmod1 \<union> Class Tmod2"
    proof (intro conjI)
      fix c
      assume "c \<in> Inh Tmod1 \<union> Inh Tmod2"
      then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
      proof (elim UnE)
        assume "c \<in> Inh Tmod1"
        then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod1_correct tmod_combine_def type_model.structure_inh_wellformed_fst_class)
      next
        assume "c \<in> Inh Tmod2"
        then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod2_correct tmod_combine_def type_model.structure_inh_wellformed_fst_class)
      qed
    next
      fix c
      assume "c \<in> Inh Tmod1 \<union> Inh Tmod2"
      then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
      proof (elim UnE)
        assume "c \<in> Inh Tmod1"
        then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod1_correct tmod_combine_def type_model.structure_inh_wellformed_snd_class)
      next
        assume "c \<in> Inh Tmod2"
        then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod2_correct tmod_combine_def type_model.structure_inh_wellformed_snd_class)
      qed
    qed
    then show "fst c \<in> Class (tmod_combine Tmod1 Tmod2) \<and> snd c \<in> Class (tmod_combine Tmod1 Tmod2)"
      unfolding tmod_combine_def
      by simp
  qed
  fix p
  assume "p \<in> Prop (tmod_combine Tmod1 Tmod2)"
  then have "p \<in> tmod_combine_prop Tmod1 Tmod2"
    by (simp add: tmod_combine_def)
  then show "p \<in> Property (tmod_combine Tmod1 Tmod2)"
  proof (induct)
    case (abstract_property_tmod1 c)
    then have "c \<in> Class Tmod1"
      using properties_rev_impl_abstract tmod1_correct type_model.structure_properties_wellfomed
      by blast
    then have "c \<in> Class (tmod_combine Tmod1 Tmod2)"
      by (simp add: tmod_combine_def)
    then show ?case
      by (fact Property.abstract_property)
  next
    case (abstract_property_tmod2 c)
    then have "c \<in> Class Tmod2"
      using properties_rev_impl_abstract tmod2_correct type_model.structure_properties_wellfomed
      by blast
    then have "c \<in> Class (tmod_combine Tmod1 Tmod2)"
      by (simp add: tmod_combine_def)
    then show ?case
      by (fact Property.abstract_property)
  next
    case (abstract_property_both c)
    then have "c \<in> Class Tmod1"
      using properties_rev_impl_abstract tmod1_correct type_model.structure_properties_wellfomed
      by blast
    then have "c \<in> Class (tmod_combine Tmod1 Tmod2)"
      by (simp add: tmod_combine_def)
    then show ?case
      by (fact Property.abstract_property)
  next
    case (containment_property_tmod1 r)
    then have "r \<in> Rel Tmod1"
      using properties_rev_impl_containment tmod1_correct type_model.structure_properties_wellfomed 
      by blast
    then have "r \<in> Rel (tmod_combine Tmod1 Tmod2)"
      using Un_iff structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_rel type_model.structure_fieldsig_wellformed_type
      by metis
    then show ?case
      by (fact Property.containment_property)
  next
    case (containment_property_tmod2 r)
    then have "r \<in> Rel Tmod2"
      using properties_rev_impl_containment tmod2_correct type_model.structure_properties_wellfomed 
      by blast
    then have "r \<in> Rel (tmod_combine Tmod1 Tmod2)"
      using Un_iff structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_rel type_model.structure_fieldsig_wellformed_type
      by metis
    then show ?case
      by (fact Property.containment_property)
  next
    case (default_value_property_tmod1 f v)
    then have assump: "f \<in> Field Tmod1 \<and> v \<in> Constant Tmod1 \<and> ConstType Tmod1 v \<sqsubseteq>[Tmod1] (type Tmod1 f)"
      using properties_rev_impl_default_value tmod1_correct type_model.structure_properties_wellfomed 
      by blast
    then show ?case
    proof (intro Property.default_value_property)
      show "f \<in> Field (tmod_combine Tmod1 Tmod2)"
        by (simp add: assump tmod_combine_def)
    next
      show "v \<in> Constant (tmod_combine Tmod1 Tmod2)"
        by (simp add: assump tmod_combine_def)
    next
      have type_f_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod1 f)"
        unfolding type_def tmod_combine_def
        by (simp add: assump default_value_property_tmod1.hyps(2) tmod_combine_fieldsig_def)
      have v_in_constant2_cases: "v \<in> Constant Tmod2 \<or> v \<notin> Constant Tmod2"
        by simp
      have "ConstType (tmod_combine Tmod1 Tmod2) v = tmod_combine_const_type Tmod1 Tmod2 v"
        by (simp add: tmod_combine_def)
      then have "ConstType (tmod_combine Tmod1 Tmod2) v = ConstType Tmod1 v"
        using v_in_constant2_cases
      proof (elim disjE)
        assume v_in_constant2: "v \<in> Constant Tmod2"
        assume "ConstType (tmod_combine Tmod1 Tmod2) v = tmod_combine_const_type Tmod1 Tmod2 v"
        then show "ConstType (tmod_combine Tmod1 Tmod2) v = ConstType Tmod1 v"
          unfolding tmod_combine_const_type_def
          by (simp add: assump structure_consttype_wellformed_type v_in_constant2)
      next
        assume v_not_in_constant2: "v \<notin> Constant Tmod2"
        assume "ConstType (tmod_combine Tmod1 Tmod2) v = tmod_combine_const_type Tmod1 Tmod2 v"
        then show "ConstType (tmod_combine Tmod1 Tmod2) v = ConstType Tmod1 v"
          unfolding tmod_combine_const_type_def
          by (simp add: assump v_not_in_constant2)
      qed
      then show "ConstType (tmod_combine Tmod1 Tmod2) v \<sqsubseteq>[tmod_combine Tmod1 Tmod2] type (tmod_combine Tmod1 Tmod2) f"
        by (simp add: assump default_value_property_tmod1.hyps(2) tmod_combine_subtype_subset_tmod1)
    qed
  next
    case (default_value_property_tmod2 f v)
    then have assump: "f \<in> Field Tmod2 \<and> v \<in> Constant Tmod2 \<and> ConstType Tmod2 v \<sqsubseteq>[Tmod2] (type Tmod2 f)"
      using properties_rev_impl_default_value tmod2_correct type_model.structure_properties_wellfomed 
      by blast
    then show ?case
    proof (intro Property.default_value_property)
      show "f \<in> Field (tmod_combine Tmod1 Tmod2)"
        by (simp add: assump tmod_combine_def)
    next
      show "v \<in> Constant (tmod_combine Tmod1 Tmod2)"
        by (simp add: assump tmod_combine_def)
    next
      have type_f_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod2 f)"
        unfolding type_def tmod_combine_def
        by (simp add: assump default_value_property_tmod2.hyps(2) tmod_combine_fieldsig_def)
      have v_in_constant1_cases: "v \<in> Constant Tmod1 \<or> v \<notin> Constant Tmod1"
        by simp
      have "ConstType (tmod_combine Tmod1 Tmod2) v = tmod_combine_const_type Tmod1 Tmod2 v"
        by (simp add: tmod_combine_def)
      then have "ConstType (tmod_combine Tmod1 Tmod2) v = ConstType Tmod2 v"
        using v_in_constant1_cases
      proof (elim disjE)
        assume v_in_constant1: "v \<in> Constant Tmod1"
        assume "ConstType (tmod_combine Tmod1 Tmod2) v = tmod_combine_const_type Tmod1 Tmod2 v"
        then show "ConstType (tmod_combine Tmod1 Tmod2) v = ConstType Tmod2 v"
          unfolding tmod_combine_const_type_def
          by (simp add: assump structure_consttype_wellformed_type v_in_constant1)
      next
        assume v_not_in_constant1: "v \<notin> Constant Tmod1"
        assume "ConstType (tmod_combine Tmod1 Tmod2) v = tmod_combine_const_type Tmod1 Tmod2 v"
        then show "ConstType (tmod_combine Tmod1 Tmod2) v = ConstType Tmod2 v"
          unfolding tmod_combine_const_type_def
          by (simp add: assump v_not_in_constant1)
      qed
      then show "ConstType (tmod_combine Tmod1 Tmod2) v \<sqsubseteq>[tmod_combine Tmod1 Tmod2] type (tmod_combine Tmod1 Tmod2) f"
        by (simp add: assump default_value_property_tmod2.hyps(2) tmod_combine_subtype_subset_tmod2)
    qed
  next
    case (default_value_property_both f v)
    have assump1: "f \<in> Field Tmod1 \<and> v \<in> Constant Tmod1 \<and> ConstType Tmod1 v \<sqsubseteq>[Tmod1] (type Tmod1 f)"
      using default_value_property_both.hyps(1) properties_rev_impl_default_value tmod1_correct type_model.structure_properties_wellfomed 
      by blast
    have assump2: "f \<in> Field Tmod2 \<and> v \<in> Constant Tmod2 \<and> ConstType Tmod2 v \<sqsubseteq>[Tmod2] (type Tmod2 f)"
      using default_value_property_both.hyps(2) properties_rev_impl_default_value tmod2_correct type_model.structure_properties_wellfomed 
      by blast
    show ?case
    proof (intro Property.default_value_property)
      show "f \<in> Field (tmod_combine Tmod1 Tmod2)"
        unfolding tmod_combine_def 
        using assump1
        by simp
    next
      show "v \<in> Constant (tmod_combine Tmod1 Tmod2)"
        unfolding tmod_combine_def 
        using assump1
        by simp
    next
      have type_f_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod1 f)"
        unfolding type_def tmod_combine_def
        by (simp add: assump1 assump2 structure_fieldsig_wellformed_type tmod_combine_fieldsig_def)
      have "ConstType (tmod_combine Tmod1 Tmod2) v = tmod_combine_const_type Tmod1 Tmod2 v"
        by (simp add: tmod_combine_def)
      then have "ConstType (tmod_combine Tmod1 Tmod2) v = ConstType Tmod1 v"
        unfolding tmod_combine_const_type_def
        by (simp add: assump1 assump2 structure_consttype_wellformed_type)
      then show "ConstType (tmod_combine Tmod1 Tmod2) v \<sqsubseteq>[tmod_combine Tmod1 Tmod2] type (tmod_combine Tmod1 Tmod2) f"
        using assump1 tmod_combine_subtype_subset_tmod1 type_def type_f_def
        by metis
    qed
  next
    case (identity_property_tmod1 c A)
    then have "c \<in> Class Tmod1 \<and> A \<subseteq> fields Tmod1 c"
      using properties_rev_impl_identity tmod1_correct type_model.structure_properties_wellfomed
      by blast
    then show ?case
    proof (intro Property.identity_property)
      assume "c \<in> Class Tmod1 \<and> A \<subseteq> fields Tmod1 c"
      then show "c \<in> Class (tmod_combine Tmod1 Tmod2)"
        unfolding tmod_combine_def
        by simp
    next
      assume assump: "c \<in> Class Tmod1 \<and> A \<subseteq> fields Tmod1 c"
      then have "A \<subseteq> {(d, n). (d, n) \<in> Field Tmod1 \<and> \<exclamdown>c \<sqsubseteq>[Tmod1] \<exclamdown>d}"
        unfolding fields_def
        by simp
      then have a_tuple_def: "\<And>d n. (d, n) \<in> A \<Longrightarrow> (d, n) \<in> Field Tmod1 \<and> \<exclamdown>c \<sqsubseteq>[Tmod1] \<exclamdown>d"
        by blast
      show "A \<subseteq> fields (tmod_combine Tmod1 Tmod2) c"
        unfolding fields_def
      proof
        fix x
        assume x_in_a: "x \<in> A"
        have "x \<in> Field Tmod1"
          using x_in_a assump fields_of_class_are_fields by blast
        then have x_in_field: "x \<in> Field (tmod_combine Tmod1 Tmod2)"
          by (simp add: tmod_combine_def)
        have "\<exclamdown>c \<sqsubseteq>[Tmod1] \<exclamdown>(fst x)"
          using a_tuple_def eq_fst_iff x_in_a
          by metis
        then have x_subtype: "\<exclamdown>c \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(fst x)"
          by (fact tmod_combine_subtype_subset_tmod1)
        show "x \<in> {(d, n). (d, n) \<in> Field (tmod_combine Tmod1 Tmod2) \<and> \<exclamdown>c \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>d}"
          using x_in_field x_subtype
          by fastforce
      qed
    qed
  next
    case (identity_property_tmod2 c A)
    then have "c \<in> Class Tmod2 \<and> A \<subseteq> fields Tmod2 c"
      using properties_rev_impl_identity tmod2_correct type_model.structure_properties_wellfomed
      by blast
    then show ?case
    proof (intro Property.identity_property)
      assume "c \<in> Class Tmod2 \<and> A \<subseteq> fields Tmod2 c"
      then show "c \<in> Class (tmod_combine Tmod1 Tmod2)"
        unfolding tmod_combine_def
        by simp
    next
      assume assump: "c \<in> Class Tmod2 \<and> A \<subseteq> fields Tmod2 c"
      then have "A \<subseteq> {(d, n). (d, n) \<in> Field Tmod2 \<and> \<exclamdown>c \<sqsubseteq>[Tmod2] \<exclamdown>d}"
        unfolding fields_def
        by simp
      then have a_tuple_def: "\<And>d n. (d, n) \<in> A \<Longrightarrow> (d, n) \<in> Field Tmod2 \<and> \<exclamdown>c \<sqsubseteq>[Tmod2] \<exclamdown>d"
        by blast
      show "A \<subseteq> fields (tmod_combine Tmod1 Tmod2) c"
        unfolding fields_def
      proof
        fix x
        assume x_in_a: "x \<in> A"
        have "x \<in> Field Tmod2"
          using x_in_a assump fields_of_class_are_fields by blast
        then have x_in_field: "x \<in> Field (tmod_combine Tmod1 Tmod2)"
          by (simp add: tmod_combine_def)
        have "\<exclamdown>c \<sqsubseteq>[Tmod2] \<exclamdown>(fst x)"
          using a_tuple_def eq_fst_iff x_in_a
          by metis
        then have x_subtype: "\<exclamdown>c \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(fst x)"
          by (fact tmod_combine_subtype_subset_tmod2)
        show "x \<in> {(d, n). (d, n) \<in> Field (tmod_combine Tmod1 Tmod2) \<and> \<exclamdown>c \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>d}"
          using x_in_field x_subtype
          by fastforce
      qed
    qed
  next
    case (identity_property_both c A)
    then have "c \<in> Class Tmod1 \<and> A \<subseteq> fields Tmod1 c"
      using properties_rev_impl_identity tmod1_correct type_model.structure_properties_wellfomed
      by blast
    then show ?case
    proof (intro Property.identity_property)
      assume "c \<in> Class Tmod1 \<and> A \<subseteq> fields Tmod1 c"
      then show "c \<in> Class (tmod_combine Tmod1 Tmod2)"
        unfolding tmod_combine_def
        by simp
    next
      assume assump: "c \<in> Class Tmod1 \<and> A \<subseteq> fields Tmod1 c"
      then have "A \<subseteq> {(d, n). (d, n) \<in> Field Tmod1 \<and> \<exclamdown>c \<sqsubseteq>[Tmod1] \<exclamdown>d}"
        unfolding fields_def
        by simp
      then have a_tuple_def: "\<And>d n. (d, n) \<in> A \<Longrightarrow> (d, n) \<in> Field Tmod1 \<and> \<exclamdown>c \<sqsubseteq>[Tmod1] \<exclamdown>d"
        by blast
      show "A \<subseteq> fields (tmod_combine Tmod1 Tmod2) c"
        unfolding fields_def
      proof
        fix x
        assume x_in_a: "x \<in> A"
        have "x \<in> Field Tmod1"
          using x_in_a assump fields_of_class_are_fields by blast
        then have x_in_field: "x \<in> Field (tmod_combine Tmod1 Tmod2)"
          by (simp add: tmod_combine_def)
        have "\<exclamdown>c \<sqsubseteq>[Tmod1] \<exclamdown>(fst x)"
          using a_tuple_def eq_fst_iff x_in_a
          by metis
        then have x_subtype: "\<exclamdown>c \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(fst x)"
          by (fact tmod_combine_subtype_subset_tmod1)
        show "x \<in> {(d, n). (d, n) \<in> Field (tmod_combine Tmod1 Tmod2) \<and> \<exclamdown>c \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>d}"
          using x_in_field x_subtype
          by fastforce
      qed
    qed
  next
    case (keyset_property_tmod1 r A)
    then have assump: "r \<in> Rel Tmod1 \<and> A \<subseteq> Attr Tmod1 \<and> (\<forall>f. f \<in> A \<longrightarrow> (uncontainer (type Tmod1 r) \<sqsubseteq>[Tmod1] \<exclamdown>(class Tmod1 f))) \<and> type Tmod1 r \<in> UniqueContainerOfClassType Tmod1"
      using properties_rev_impl_keyset tmod1_correct type_model.structure_properties_wellfomed
      by blast
    then have r_in_field_tmod1: "r \<in> Field Tmod1"
      using Rel_def
      by fastforce
    show ?case
    proof (intro Property.keyset_property)
      have "r \<in> Rel Tmod1"
        using assump
        by blast
      then show "r \<in> Rel (tmod_combine Tmod1 Tmod2)"
        using Un_iff structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_rel type_model.structure_fieldsig_wellformed_type
        by metis
    next
      have "A \<subseteq> Attr Tmod1"
        using assump 
        by blast
      then have a_tuple_def: "\<And>f. f \<in> A \<Longrightarrow> f \<in> Field Tmod1 \<and> type Tmod1 f \<in> AttrType Tmod1"
        using Attr_def 
        by blast
      show "A \<subseteq> Attr (tmod_combine Tmod1 Tmod2)"
      proof
        fix x
        assume x_in_a: "x \<in> A"
        have x_in_field: "x \<in> Field Tmod1"
          using a_tuple_def x_in_a 
          by blast
        then have x_in_field_tmod12: "x \<in> Field (tmod_combine Tmod1 Tmod2)"
          by (simp add: tmod_combine_def)
        have x_is_attrtype: "type Tmod1 x \<in> AttrType Tmod1"
          using a_tuple_def x_in_a
          by blast
        have f_in_field2_cases: "x \<in> Field Tmod2 \<or> x \<notin> Field Tmod2"
          by simp
        have "type (tmod_combine Tmod1 Tmod2) x = fst (tmod_combine_fieldsig Tmod1 Tmod2 x)"
          unfolding type_def
          by (simp add: tmod_combine_def)
        then have "type (tmod_combine Tmod1 Tmod2) x = fst (FieldSig Tmod1 x)"
          using f_in_field2_cases
        proof (elim disjE)
          assume x_in_field2: "x \<in> Field Tmod2"
          assume "type (tmod_combine Tmod1 Tmod2) x = fst (tmod_combine_fieldsig Tmod1 Tmod2 x)"
          then show "type (tmod_combine Tmod1 Tmod2) x = fst (FieldSig Tmod1 x)"
            unfolding tmod_combine_fieldsig_def
            by (simp add: structure_fieldsig_wellformed_type x_in_field x_in_field2)
        next
          assume x_not_in_field2: "x \<notin> Field Tmod2"
          assume "type (tmod_combine Tmod1 Tmod2) x = fst (tmod_combine_fieldsig Tmod1 Tmod2 x)"
          then show "type (tmod_combine Tmod1 Tmod2) x = fst (FieldSig Tmod1 x)"
            unfolding tmod_combine_fieldsig_def
            by (simp add: x_in_field x_not_in_field2)
        qed
        then have "type (tmod_combine Tmod1 Tmod2) x \<in> AttrType (tmod_combine Tmod1 Tmod2)"
          using Un_iff tmod_combine_attr_type type_def x_is_attrtype
          by metis
        then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
          using x_in_field_tmod12
          using Attr_def
          by blast
      qed
    next
      have "\<And>f. f \<in> A \<Longrightarrow> uncontainer (type (tmod_combine Tmod1 Tmod2) r) \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(class (tmod_combine Tmod1 Tmod2) f)"
      proof-
        fix f
        assume "f \<in> A"
        then have uncontainer_extend: "uncontainer (type Tmod1 r) \<sqsubseteq>[Tmod1] \<exclamdown>(class Tmod1 f)"
          using assump 
          by blast
        have "type (tmod_combine Tmod1 Tmod2) r = fst (tmod_combine_fieldsig Tmod1 Tmod2 r)"
          unfolding type_def
          by (simp add: tmod_combine_def)
        then have "type (tmod_combine Tmod1 Tmod2) r = fst (FieldSig Tmod1 r)"
          unfolding tmod_combine_fieldsig_def
          by (simp add: keyset_property_tmod1.hyps(2) r_in_field_tmod1)
        then have "uncontainer (type Tmod1 r) = uncontainer (type (tmod_combine Tmod1 Tmod2) r)"
          unfolding type_def
          by simp
        then show "uncontainer (type (tmod_combine Tmod1 Tmod2) r) \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(class (tmod_combine Tmod1 Tmod2) f)"
          using class_def tmod_combine_subtype_subset_tmod1 uncontainer_extend
          by metis
      qed
      then show "\<forall>f. f \<in> A \<longrightarrow> uncontainer (type (tmod_combine Tmod1 Tmod2) r) \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(class (tmod_combine Tmod1 Tmod2) f)"
        by blast
    next
      have "type (tmod_combine Tmod1 Tmod2) r = fst (tmod_combine_fieldsig Tmod1 Tmod2 r)"
        unfolding type_def
        by (simp add: tmod_combine_def)
      then show "type (tmod_combine Tmod1 Tmod2) r \<in> UniqueContainerOfClassType (tmod_combine Tmod1 Tmod2)"
        using assump keyset_property_tmod1.hyps(2) r_in_field_tmod1 
        by simp
    qed
  next
    case (keyset_property_tmod2 r A)
    then have assump: "r \<in> Rel Tmod2 \<and> A \<subseteq> Attr Tmod2 \<and> (\<forall>f. f \<in> A \<longrightarrow> (uncontainer (type Tmod2 r) \<sqsubseteq>[Tmod2] \<exclamdown>(class Tmod2 f))) \<and> type Tmod2 r \<in> UniqueContainerOfClassType Tmod2"
      using properties_rev_impl_keyset tmod2_correct type_model.structure_properties_wellfomed
      by blast
    then have r_in_field_tmod2: "r \<in> Field Tmod2"
      using Rel_def
      by fastforce
    show ?case
    proof (intro Property.keyset_property)
      have "r \<in> Rel Tmod2"
        using assump
        by blast
      then show "r \<in> Rel (tmod_combine Tmod1 Tmod2)"
        using Un_iff structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_rel type_model.structure_fieldsig_wellformed_type
        by metis
    next
      have "A \<subseteq> Attr Tmod2"
        using assump 
        by blast
      then have a_tuple_def: "\<And>f. f \<in> A \<Longrightarrow> f \<in> Field Tmod2 \<and> type Tmod2 f \<in> AttrType Tmod2"
        using Attr_def 
        by blast
      show "A \<subseteq> Attr (tmod_combine Tmod1 Tmod2)"
      proof
        fix x
        assume x_in_a: "x \<in> A"
        have x_in_field: "x \<in> Field Tmod2"
          using a_tuple_def x_in_a 
          by blast
        then have x_in_field_tmod12: "x \<in> Field (tmod_combine Tmod1 Tmod2)"
          by (simp add: tmod_combine_def)
        have x_is_attrtype: "type Tmod2 x \<in> AttrType Tmod2"
          using a_tuple_def x_in_a
          by blast
        have f_in_field1_cases: "x \<in> Field Tmod1 \<or> x \<notin> Field Tmod1"
          by simp
        have "type (tmod_combine Tmod1 Tmod2) x = fst (tmod_combine_fieldsig Tmod1 Tmod2 x)"
          unfolding type_def
          by (simp add: tmod_combine_def)
        then have "type (tmod_combine Tmod1 Tmod2) x = fst (FieldSig Tmod2 x)"
          using f_in_field1_cases
        proof (elim disjE)
          assume x_in_field1: "x \<in> Field Tmod1"
          assume "type (tmod_combine Tmod1 Tmod2) x = fst (tmod_combine_fieldsig Tmod1 Tmod2 x)"
          then show "type (tmod_combine Tmod1 Tmod2) x = fst (FieldSig Tmod2 x)"
            unfolding tmod_combine_fieldsig_def
            by (simp add: structure_fieldsig_wellformed_type x_in_field x_in_field1)
        next
          assume x_not_in_field1: "x \<notin> Field Tmod1"
          assume "type (tmod_combine Tmod1 Tmod2) x = fst (tmod_combine_fieldsig Tmod1 Tmod2 x)"
          then show "type (tmod_combine Tmod1 Tmod2) x = fst (FieldSig Tmod2 x)"
            unfolding tmod_combine_fieldsig_def
            by (simp add: x_in_field x_not_in_field1)
        qed
        then have "type (tmod_combine Tmod1 Tmod2) x \<in> AttrType (tmod_combine Tmod1 Tmod2)"
          using Un_iff tmod_combine_attr_type type_def x_is_attrtype
          by metis
        then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
          using x_in_field_tmod12
          using Attr_def
          by blast
      qed
    next
      have "\<And>f. f \<in> A \<Longrightarrow> uncontainer (type (tmod_combine Tmod1 Tmod2) r) \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(class (tmod_combine Tmod1 Tmod2) f)"
      proof-
        fix f
        assume "f \<in> A"
        then have uncontainer_extend: "uncontainer (type Tmod2 r) \<sqsubseteq>[Tmod2] \<exclamdown>(class Tmod2 f)"
          using assump 
          by blast
        have "type (tmod_combine Tmod1 Tmod2) r = fst (tmod_combine_fieldsig Tmod1 Tmod2 r)"
          unfolding type_def
          by (simp add: tmod_combine_def)
        then have "type (tmod_combine Tmod1 Tmod2) r = fst (FieldSig Tmod2 r)"
          unfolding tmod_combine_fieldsig_def
          by (simp add: keyset_property_tmod2.hyps(2) r_in_field_tmod2)
        then have "uncontainer (type Tmod2 r) = uncontainer (type (tmod_combine Tmod1 Tmod2) r)"
          unfolding type_def
          by simp
        then show "uncontainer (type (tmod_combine Tmod1 Tmod2) r) \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(class (tmod_combine Tmod1 Tmod2) f)"
          using class_def tmod_combine_subtype_subset_tmod2 uncontainer_extend
          by metis
      qed
      then show "\<forall>f. f \<in> A \<longrightarrow> uncontainer (type (tmod_combine Tmod1 Tmod2) r) \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(class (tmod_combine Tmod1 Tmod2) f)"
        by blast
    next
      have "type (tmod_combine Tmod1 Tmod2) r = fst (tmod_combine_fieldsig Tmod1 Tmod2 r)"
        unfolding type_def
        by (simp add: tmod_combine_def)
      then show "type (tmod_combine Tmod1 Tmod2) r \<in> UniqueContainerOfClassType (tmod_combine Tmod1 Tmod2)"
        using assump keyset_property_tmod2.hyps(2) r_in_field_tmod2
        by simp
    qed
  next
    case (keyset_property_both r A)
    have assump1: "r \<in> Rel Tmod1 \<and> A \<subseteq> Attr Tmod1 \<and> (\<forall>f. f \<in> A \<longrightarrow> (uncontainer (type Tmod1 r) \<sqsubseteq>[Tmod1] \<exclamdown>(class Tmod1 f))) \<and> type Tmod1 r \<in> UniqueContainerOfClassType Tmod1"
      using keyset_property_both.hyps(1) properties_rev_impl_keyset tmod1_correct type_model.structure_properties_wellfomed
      by blast
    then have r_in_field_tmod1: "r \<in> Field Tmod1"
      using Rel_def
      by fastforce
    have assump2: "r \<in> Rel Tmod2 \<and> A \<subseteq> Attr Tmod2 \<and> (\<forall>f. f \<in> A \<longrightarrow> (uncontainer (type Tmod2 r) \<sqsubseteq>[Tmod2] \<exclamdown>(class Tmod2 f))) \<and> type Tmod2 r \<in> UniqueContainerOfClassType Tmod2"
      using keyset_property_both.hyps(2) properties_rev_impl_keyset tmod2_correct type_model.structure_properties_wellfomed
      by blast
    then have r_in_field_tmod2: "r \<in> Field Tmod2"
      using Rel_def
      by fastforce
    show ?case
    proof (intro Property.keyset_property)
      have "r \<in> Rel Tmod1"
        using assump1
        by blast
      then show "r \<in> Rel (tmod_combine Tmod1 Tmod2)"
        using Un_iff structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_rel type_model.structure_fieldsig_wellformed_type
        by metis
    next
      have "A \<subseteq> Attr Tmod1"
        using assump1
        by blast
      then have a_tuple_def1: "\<And>f. f \<in> A \<Longrightarrow> f \<in> Field Tmod1 \<and> type Tmod1 f \<in> AttrType Tmod1"
        using Attr_def 
        by blast
      have "A \<subseteq> Attr Tmod2"
        using assump2
        by blast
      then have a_tuple_def2: "\<And>f. f \<in> A \<Longrightarrow> f \<in> Field Tmod2 \<and> type Tmod2 f \<in> AttrType Tmod2"
        using Attr_def 
        by blast
      show "A \<subseteq> Attr (tmod_combine Tmod1 Tmod2)"
      proof
        fix x
        assume x_in_a: "x \<in> A"
        have x_in_field1: "x \<in> Field Tmod1"
          using a_tuple_def1 x_in_a 
          by blast
        have x_in_field2: "x \<in> Field Tmod2"
          using a_tuple_def2 x_in_a 
          by blast
        then have x_in_field_tmod12: "x \<in> Field (tmod_combine Tmod1 Tmod2)"
          by (simp add: tmod_combine_def)
        have x_is_attrtype: "type Tmod1 x \<in> AttrType Tmod1"
          using a_tuple_def1 x_in_a
          by blast
        have "type (tmod_combine Tmod1 Tmod2) x = fst (tmod_combine_fieldsig Tmod1 Tmod2 x)"
          unfolding type_def
          by (simp add: tmod_combine_def)
        then have "type (tmod_combine Tmod1 Tmod2) x = fst (FieldSig Tmod1 x)"
          unfolding tmod_combine_fieldsig_def
          by (simp add: structure_fieldsig_wellformed_type x_in_field1 x_in_field2)
        then have "type (tmod_combine Tmod1 Tmod2) x \<in> AttrType (tmod_combine Tmod1 Tmod2)"
          using Un_iff tmod_combine_attr_type type_def x_is_attrtype
          by metis
        then show "x \<in> Attr (tmod_combine Tmod1 Tmod2)"
          using x_in_field_tmod12
          using Attr_def
          by blast
      qed
    next
      have "\<And>f. f \<in> A \<Longrightarrow> uncontainer (type (tmod_combine Tmod1 Tmod2) r) \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(class (tmod_combine Tmod1 Tmod2) f)"
      proof-
        fix f
        assume "f \<in> A"
        then have uncontainer_extend: "uncontainer (type Tmod1 r) \<sqsubseteq>[Tmod1] \<exclamdown>(class Tmod1 f)"
          using assump1
          by blast
        have "type (tmod_combine Tmod1 Tmod2) r = fst (tmod_combine_fieldsig Tmod1 Tmod2 r)"
          unfolding type_def
          by (simp add: tmod_combine_def)
        then have "type (tmod_combine Tmod1 Tmod2) r = fst (FieldSig Tmod1 r)"
          unfolding tmod_combine_fieldsig_def
          by (simp add: r_in_field_tmod1 r_in_field_tmod2 structure_fieldsig_wellformed_type)
        then have "uncontainer (type Tmod1 r) = uncontainer (type (tmod_combine Tmod1 Tmod2) r)"
          unfolding type_def
          by simp
        then show "uncontainer (type (tmod_combine Tmod1 Tmod2) r) \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(class (tmod_combine Tmod1 Tmod2) f)"
          using class_def tmod_combine_subtype_subset_tmod1 uncontainer_extend
          by metis
      qed
      then show "\<forall>f. f \<in> A \<longrightarrow> uncontainer (type (tmod_combine Tmod1 Tmod2) r) \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>(class (tmod_combine Tmod1 Tmod2) f)"
        by blast
    next
      have "type (tmod_combine Tmod1 Tmod2) r = fst (tmod_combine_fieldsig Tmod1 Tmod2 r)"
        unfolding type_def
        by (simp add: tmod_combine_def)
      then show "type (tmod_combine Tmod1 Tmod2) r \<in> UniqueContainerOfClassType (tmod_combine Tmod1 Tmod2)"
        using Un_iff assump1 assump2 tmod_combine_type_func_field_tmods tmod_combine_unique_container_of_class_type r_in_field_tmod1 r_in_field_tmod2 structure_fieldsig_wellformed_type
        by metis
    qed
  next
    case (opposite_property_tmod1 r1 r2)
    then have assump: "r1 \<in> Rel Tmod1 \<and> r2 \<in> Rel Tmod1 \<and> r1 \<noteq> r2 \<and> 
        \<exclamdown>(class Tmod1 r1) = uncontainer (type Tmod1 r2) \<and> \<exclamdown>(class Tmod1 r2) = uncontainer (type Tmod1 r1) \<and> 
        type Tmod1 r1 \<notin> NonUniqueContainerType Tmod1 \<and> type Tmod1 r2 \<notin> NonUniqueContainerType Tmod1"
      using properties_rev_impl_opposite tmod1_correct type_model.structure_properties_wellfomed
      by blast
    show ?case
    proof (intro Property.opposite_property)
      show "r1 \<in> Rel (tmod_combine Tmod1 Tmod2)"
        using Un_iff assump structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_rel type_model.structure_fieldsig_wellformed_type
        by metis
    next
      show "r2 \<in> Rel (tmod_combine Tmod1 Tmod2)"
        using Un_iff assump structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_rel type_model.structure_fieldsig_wellformed_type
        by metis
    next
      show "r1 \<noteq> r2"
        using assump
        by blast
    next
      have "type (tmod_combine Tmod1 Tmod2) r2 = type Tmod1 r2"
        using Diff_iff Type_Model.Rel_def assump opposite_property_tmod1.hyps(3) tmod1_correct tmod2_correct tmod_combine_type_func_field_tmod1
        by metis
      then show "\<exclamdown>(class (tmod_combine Tmod1 Tmod2) r1) = uncontainer (type (tmod_combine Tmod1 Tmod2) r2)"
        using assump class_def
        by metis
    next
      have "type (tmod_combine Tmod1 Tmod2) r1 = type Tmod1 r1"
        using Diff_iff Type_Model.Rel_def assump opposite_property_tmod1.hyps(2) tmod1_correct tmod2_correct tmod_combine_type_func_field_tmod1
        by metis
      then show "\<exclamdown>(class (tmod_combine Tmod1 Tmod2) r2) = uncontainer (type (tmod_combine Tmod1 Tmod2) r1)"
        using assump class_def
        by metis
    next
      have type_combine_def: "type (tmod_combine Tmod1 Tmod2) r1 = type Tmod1 r1"
        using Diff_iff Type_Model.Rel_def assump opposite_property_tmod1.hyps(2) tmod1_correct tmod2_correct tmod_combine_type_func_field_tmod1
        by metis
      then have type_in_type_tmod1: "type (tmod_combine Tmod1 Tmod2) r1 \<in> Type Tmod1"
        using Diff_iff Type_Model.Rel_def assump tmod1_correct type_def type_model.structure_fieldsig_wellformed_type
        by metis
      have "type (tmod_combine Tmod1 Tmod2) r1 \<notin> NonUniqueContainerType Tmod1"
        using type_combine_def assump
        by metis
      then have "type (tmod_combine Tmod1 Tmod2) r1 \<in> NonContainerType Tmod1 \<union> UniqueContainerType Tmod1"
        using type_in_type_tmod1 unique_and_non_unique_containers_union
        unfolding Type_def
        by blast
      then have "type (tmod_combine Tmod1 Tmod2) r1 \<in> NonContainerType (tmod_combine Tmod1 Tmod2) \<union> UniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using Un_iff UniqueContainerType_def tmod_combine_non_container_type tmod_combine_ord_container_type tmod_combine_set_container_type
        by metis
      then show "type (tmod_combine Tmod1 Tmod2) r1 \<notin> NonUniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using IntI Un_iff container_type_non_container_type_intersect emptyE unique_and_non_unique_containers_distinct unique_and_non_unique_containers_union
        by metis
    next
      have type_combine_def: "type (tmod_combine Tmod1 Tmod2) r2 = type Tmod1 r2"
        using Diff_iff Type_Model.Rel_def assump opposite_property_tmod1.hyps(3) tmod1_correct tmod2_correct tmod_combine_type_func_field_tmod1
        by metis
      then have type_in_type_tmod1: "type (tmod_combine Tmod1 Tmod2) r2 \<in> Type Tmod1"
        using Diff_iff Type_Model.Rel_def assump tmod1_correct type_def type_model.structure_fieldsig_wellformed_type
        by metis
      have "type (tmod_combine Tmod1 Tmod2) r2 \<notin> NonUniqueContainerType Tmod1"
        using type_combine_def assump
        by metis
      then have "type (tmod_combine Tmod1 Tmod2) r2 \<in> NonContainerType Tmod1 \<union> UniqueContainerType Tmod1"
        using type_in_type_tmod1 unique_and_non_unique_containers_union
        unfolding Type_def
        by blast
      then have "type (tmod_combine Tmod1 Tmod2) r2 \<in> NonContainerType (tmod_combine Tmod1 Tmod2) \<union> UniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using Un_iff UniqueContainerType_def tmod_combine_non_container_type tmod_combine_ord_container_type tmod_combine_set_container_type
        by metis
      then show "type (tmod_combine Tmod1 Tmod2) r2 \<notin> NonUniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using IntI Un_iff container_type_non_container_type_intersect emptyE unique_and_non_unique_containers_distinct unique_and_non_unique_containers_union
        by metis
    qed
  next
    case (opposite_property_tmod2 r1 r2)
    then have assump: "r1 \<in> Rel Tmod2 \<and> r2 \<in> Rel Tmod2 \<and> r1 \<noteq> r2 \<and> 
        \<exclamdown>(class Tmod2 r1) = uncontainer (type Tmod2 r2) \<and> \<exclamdown>(class Tmod2 r2) = uncontainer (type Tmod2 r1) \<and> 
        type Tmod2 r1 \<notin> NonUniqueContainerType Tmod2 \<and> type Tmod2 r2 \<notin> NonUniqueContainerType Tmod2"
      using properties_rev_impl_opposite tmod2_correct type_model.structure_properties_wellfomed
      by blast
    show ?case
    proof (intro Property.opposite_property)
      show "r1 \<in> Rel (tmod_combine Tmod1 Tmod2)"
        using Un_iff assump structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_rel type_model.structure_fieldsig_wellformed_type
        by metis
    next
      show "r2 \<in> Rel (tmod_combine Tmod1 Tmod2)"
        using Un_iff assump structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_rel type_model.structure_fieldsig_wellformed_type
        by metis
    next
      show "r1 \<noteq> r2"
        using assump
        by blast
    next
      have "type (tmod_combine Tmod1 Tmod2) r2 = type Tmod2 r2"
        using Diff_iff Type_Model.Rel_def assump opposite_property_tmod2.hyps(3) tmod1_correct tmod2_correct tmod_combine_type_func_field_tmod2
        by metis
      then show "\<exclamdown>(class (tmod_combine Tmod1 Tmod2) r1) = uncontainer (type (tmod_combine Tmod1 Tmod2) r2)"
        using assump class_def
        by metis
    next
      have "type (tmod_combine Tmod1 Tmod2) r1 = type Tmod2 r1"
        using Diff_iff Type_Model.Rel_def assump opposite_property_tmod2.hyps(2) tmod1_correct tmod2_correct tmod_combine_type_func_field_tmod2
        by metis
      then show "\<exclamdown>(class (tmod_combine Tmod1 Tmod2) r2) = uncontainer (type (tmod_combine Tmod1 Tmod2) r1)"
        using assump class_def
        by metis
    next
      have type_combine_def: "type (tmod_combine Tmod1 Tmod2) r1 = type Tmod2 r1"
        using Diff_iff Type_Model.Rel_def assump opposite_property_tmod2.hyps(2) tmod1_correct tmod2_correct tmod_combine_type_func_field_tmod2
        by metis
      then have type_in_type_tmod2: "type (tmod_combine Tmod1 Tmod2) r1 \<in> Type Tmod2"
        using Diff_iff Type_Model.Rel_def assump tmod2_correct type_def type_model.structure_fieldsig_wellformed_type
        by metis
      have "type (tmod_combine Tmod1 Tmod2) r1 \<notin> NonUniqueContainerType Tmod2"
        using type_combine_def assump
        by metis
      then have "type (tmod_combine Tmod1 Tmod2) r1 \<in> NonContainerType Tmod2 \<union> UniqueContainerType Tmod2"
        using type_in_type_tmod2 unique_and_non_unique_containers_union
        unfolding Type_def
        by blast
      then have "type (tmod_combine Tmod1 Tmod2) r1 \<in> NonContainerType (tmod_combine Tmod1 Tmod2) \<union> UniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using Un_iff UniqueContainerType_def tmod_combine_non_container_type tmod_combine_ord_container_type tmod_combine_set_container_type
        by metis
      then show "type (tmod_combine Tmod1 Tmod2) r1 \<notin> NonUniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using IntI Un_iff container_type_non_container_type_intersect emptyE unique_and_non_unique_containers_distinct unique_and_non_unique_containers_union
        by metis
    next
      have type_combine_def: "type (tmod_combine Tmod1 Tmod2) r2 = type Tmod2 r2"
        using Diff_iff Type_Model.Rel_def assump opposite_property_tmod2.hyps(3) tmod1_correct tmod2_correct tmod_combine_type_func_field_tmod2
        by metis
      then have type_in_type_tmod2: "type (tmod_combine Tmod1 Tmod2) r2 \<in> Type Tmod2"
        using Diff_iff Type_Model.Rel_def assump tmod2_correct type_def type_model.structure_fieldsig_wellformed_type
        by metis
      have "type (tmod_combine Tmod1 Tmod2) r2 \<notin> NonUniqueContainerType Tmod2"
        using type_combine_def assump
        by metis
      then have "type (tmod_combine Tmod1 Tmod2) r2 \<in> NonContainerType Tmod2 \<union> UniqueContainerType Tmod2"
        using type_in_type_tmod2 unique_and_non_unique_containers_union
        unfolding Type_def
        by blast
      then have "type (tmod_combine Tmod1 Tmod2) r2 \<in> NonContainerType (tmod_combine Tmod1 Tmod2) \<union> UniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using Un_iff UniqueContainerType_def tmod_combine_non_container_type tmod_combine_ord_container_type tmod_combine_set_container_type
        by metis
      then show "type (tmod_combine Tmod1 Tmod2) r2 \<notin> NonUniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using IntI Un_iff container_type_non_container_type_intersect emptyE unique_and_non_unique_containers_distinct unique_and_non_unique_containers_union
        by metis
    qed
  next
    case (opposite_property_both r1 r2)
    have assump1: "r1 \<in> Rel Tmod1 \<and> r2 \<in> Rel Tmod1 \<and> r1 \<noteq> r2 \<and> 
        \<exclamdown>(class Tmod1 r1) = uncontainer (type Tmod1 r2) \<and> \<exclamdown>(class Tmod1 r2) = uncontainer (type Tmod1 r1) \<and> 
        type Tmod1 r1 \<notin> NonUniqueContainerType Tmod1 \<and> type Tmod1 r2 \<notin> NonUniqueContainerType Tmod1"
      using opposite_property_both.hyps(1) properties_rev_impl_opposite tmod1_correct type_model.structure_properties_wellfomed
      by blast
    have assump2: "r1 \<in> Rel Tmod2 \<and> r2 \<in> Rel Tmod2 \<and> r1 \<noteq> r2 \<and> 
        \<exclamdown>(class Tmod2 r1) = uncontainer (type Tmod2 r2) \<and> \<exclamdown>(class Tmod2 r2) = uncontainer (type Tmod2 r1) \<and> 
        type Tmod2 r1 \<notin> NonUniqueContainerType Tmod2 \<and> type Tmod2 r2 \<notin> NonUniqueContainerType Tmod2"
      using opposite_property_both.hyps(2) properties_rev_impl_opposite tmod2_correct type_model.structure_properties_wellfomed
      by blast
    have r1_in_both: "r1 \<in> Field Tmod1 \<inter> Field Tmod2"
      using Type_Model.Rel_def assump1 assump2
      by fastforce
    then have type_r1_eq: "type Tmod1 r1 = type Tmod2 r1"
      by (simp add: structure_fieldsig_wellformed_type type_def)
    have r2_in_both: "r2 \<in> Field Tmod1 \<inter> Field Tmod2"
      using Type_Model.Rel_def assump1 assump2
      by fastforce
    then have type_r2_eq: "type Tmod1 r2 = type Tmod2 r2"
      by (simp add: structure_fieldsig_wellformed_type type_def)
    show ?case
    proof (intro Property.opposite_property)
      show "r1 \<in> Rel (tmod_combine Tmod1 Tmod2)"
        using Un_iff assump1 structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_rel type_model.structure_fieldsig_wellformed_type
        by metis
    next
      show "r2 \<in> Rel (tmod_combine Tmod1 Tmod2)"
        using Un_iff assump1 structure_fieldsig_wellformed_type tmod1_correct tmod2_correct tmod_combine_rel type_model.structure_fieldsig_wellformed_type
        by metis
    next
      show "r1 \<noteq> r2"
        using assump1
        by blast
    next
      have "type (tmod_combine Tmod1 Tmod2) r2 = type Tmod1 r2"
        using r2_in_both tmod_combine_type_func_field_tmod1_tmod2 type_r2_eq
        by blast
      then show "\<exclamdown>(class (tmod_combine Tmod1 Tmod2) r1) = uncontainer (type (tmod_combine Tmod1 Tmod2) r2)"
        using assump1 class_def
        by metis
    next
      have "type (tmod_combine Tmod1 Tmod2) r1 = type Tmod1 r1"
        using r1_in_both tmod_combine_type_func_field_tmod1_tmod2 type_r1_eq
        by blast
      then show "\<exclamdown>(class (tmod_combine Tmod1 Tmod2) r2) = uncontainer (type (tmod_combine Tmod1 Tmod2) r1)"
        using assump1 class_def
        by metis
    next
      have type_combine_def: "type (tmod_combine Tmod1 Tmod2) r1 = type Tmod1 r1"
        using r1_in_both tmod_combine_type_func_field_tmod1_tmod2 type_r1_eq
        by blast
      then have type_in_type_tmod1: "type (tmod_combine Tmod1 Tmod2) r1 \<in> Type Tmod1"
        using IntD1 r1_in_both tmod1_correct type_def type_model.structure_fieldsig_wellformed_type
        by metis
      have "type (tmod_combine Tmod1 Tmod2) r1 \<notin> NonUniqueContainerType Tmod1"
        using type_combine_def assump1
        by metis
      then have "type (tmod_combine Tmod1 Tmod2) r1 \<in> NonContainerType Tmod1 \<union> UniqueContainerType Tmod1"
        using type_in_type_tmod1 unique_and_non_unique_containers_union
        unfolding Type_def
        by blast
      then have "type (tmod_combine Tmod1 Tmod2) r1 \<in> NonContainerType (tmod_combine Tmod1 Tmod2) \<union> UniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using Un_iff UniqueContainerType_def tmod_combine_non_container_type tmod_combine_ord_container_type tmod_combine_set_container_type
        by metis
      then show "type (tmod_combine Tmod1 Tmod2) r1 \<notin> NonUniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using IntI Un_iff container_type_non_container_type_intersect emptyE unique_and_non_unique_containers_distinct unique_and_non_unique_containers_union
        by metis
    next
      have type_combine_def: "type (tmod_combine Tmod1 Tmod2) r2 = type Tmod1 r2"
        using r2_in_both tmod_combine_type_func_field_tmod1_tmod2 type_r2_eq
        by blast
      then have type_in_type_tmod1: "type (tmod_combine Tmod1 Tmod2) r2 \<in> Type Tmod1"
        using IntD1 r2_in_both tmod1_correct type_def type_model.structure_fieldsig_wellformed_type
        by metis
      have "type (tmod_combine Tmod1 Tmod2) r2 \<notin> NonUniqueContainerType Tmod1"
        using type_combine_def assump1
        by metis
      then have "type (tmod_combine Tmod1 Tmod2) r2 \<in> NonContainerType Tmod1 \<union> UniqueContainerType Tmod1"
        using type_in_type_tmod1 unique_and_non_unique_containers_union
        unfolding Type_def
        by blast
      then have "type (tmod_combine Tmod1 Tmod2) r2 \<in> NonContainerType (tmod_combine Tmod1 Tmod2) \<union> UniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using Un_iff UniqueContainerType_def tmod_combine_non_container_type tmod_combine_ord_container_type tmod_combine_set_container_type
        by metis
      then show "type (tmod_combine Tmod1 Tmod2) r2 \<notin> NonUniqueContainerType (tmod_combine Tmod1 Tmod2)"
        using IntI Un_iff container_type_non_container_type_intersect emptyE unique_and_non_unique_containers_distinct unique_and_non_unique_containers_union
        by metis
    qed
  next
    case (readonly_property_tmod1 f)
    then have "f \<in> Field Tmod1"
      by (simp add: properties_rev_impl_readonly tmod1_correct type_model.structure_properties_wellfomed)
    then show ?case
      by (simp add: Property.readonly_property tmod_combine_def)
  next
    case (readonly_property_tmod2 f)
    then have "f \<in> Field Tmod2"
      by (simp add: properties_rev_impl_readonly tmod2_correct type_model.structure_properties_wellfomed)
    then show ?case
      by (simp add: Property.readonly_property tmod_combine_def)
  next
    case (readonly_property_both f)
    then have "f \<in> Field Tmod1"
      by (simp add: properties_rev_impl_readonly tmod1_correct type_model.structure_properties_wellfomed)
    then show ?case
      by (simp add: Property.readonly_property tmod_combine_def)
  qed
next
  fix c
  assume "c \<in> Constant (tmod_combine Tmod1 Tmod2)"
  then have "c \<in> Constant Tmod1 \<union> Constant Tmod2"
    by (simp add: tmod_combine_def)
  then have "c \<in> Constant Tmod1 \<inter> Constant Tmod2 \<or> c \<in> Constant Tmod1 - Constant Tmod2 \<or> c \<in> Constant Tmod2 - Constant Tmod1"
    by blast
  then have "tmod_combine_const_type Tmod1 Tmod2 c \<in> Type (tmod_combine Tmod1 Tmod2)"
  proof (elim disjE)
    assume "c \<in> Constant Tmod1 \<inter> Constant Tmod2"
    then show ?thesis
      unfolding tmod_combine_const_type_def
      by (simp add: structure_consttype_wellformed_type tmod2_correct type_model.structure_consttype_wellformed)
  next
    assume "c \<in> Constant Tmod1 - Constant Tmod2"
    then show ?thesis
      unfolding tmod_combine_const_type_def
      by (simp add: tmod1_correct type_model.structure_consttype_wellformed)
  next
    assume "c \<in> Constant Tmod2 - Constant Tmod1"
    then show ?thesis
      unfolding tmod_combine_const_type_def
      by (simp add: tmod2_correct type_model.structure_consttype_wellformed)
  qed
  then show "ConstType (tmod_combine Tmod1 Tmod2) c \<in> Type (tmod_combine Tmod1 Tmod2)"
    by (simp add: tmod_combine_def)
next
  fix c
  assume "c \<notin> Constant (tmod_combine Tmod1 Tmod2)"
  then have "c \<notin> Constant Tmod1 \<and> c \<notin> Constant Tmod2"
    by (simp add: tmod_combine_def)
  then show "ConstType (tmod_combine Tmod1 Tmod2) c = undefined"
    by (simp add: tmod_combine_const_type_def tmod_combine_def)
next
  fix c
  assume "c \<in> Class (tmod_combine Tmod1 Tmod2)"
  then have "c \<in> Class Tmod1 \<union> Class Tmod2"
    by (simp add: tmod_combine_def)
  then have "c \<notin> Enum Tmod1 \<and> c \<notin> Enum Tmod2 \<and> c \<notin> UserDataType Tmod1 \<and> c \<notin> UserDataType Tmod2"
  proof (elim UnE)
    assume "c \<in> Class Tmod1"
    then show "c \<notin> Enum Tmod1 \<and> c \<notin> Enum Tmod2 \<and> c \<notin> UserDataType Tmod1 \<and> c \<notin> UserDataType Tmod2"
    proof (intro conjI)
      assume "c \<in> Class Tmod1"
      then show "c \<notin> Enum Tmod1"
        using tmod1_correct type_model.property_class_disjoint
        by blast
    next
      assume "c \<in> Class Tmod1"
      then show "c \<notin> Enum Tmod2"
        by (simp add: property_class_disjoint_tmod1)
    next
      assume "c \<in> Class Tmod1"
      then show "c \<notin> UserDataType Tmod1"
        using tmod1_correct type_model.property_class_disjoint
        by blast
    next
      assume "c \<in> Class Tmod1"
      then show "c \<notin> UserDataType Tmod2"
        by (simp add: property_class_disjoint_tmod1)
    qed
  next
    assume "c \<in> Class Tmod2"
    then show "c \<notin> Enum Tmod1 \<and> c \<notin> Enum Tmod2 \<and> c \<notin> UserDataType Tmod1 \<and> c \<notin> UserDataType Tmod2"
    proof (intro conjI)
      assume "c \<in> Class Tmod2"
      then show "c \<notin> Enum Tmod1"
        by (simp add: property_class_disjoint_tmod2)
    next
      assume "c \<in> Class Tmod2"
      then show "c \<notin> Enum Tmod2"
        using tmod2_correct type_model.property_class_disjoint
        by blast
    next
      assume "c \<in> Class Tmod2"
      then show "c \<notin> UserDataType Tmod1"
        by (simp add: property_class_disjoint_tmod2)
    next
      assume "c \<in> Class Tmod2"
      then show "c \<notin> UserDataType Tmod2"
        using tmod2_correct type_model.property_class_disjoint
        by blast
    qed
  qed
  then show "c \<notin> Enum (tmod_combine Tmod1 Tmod2) \<and> c \<notin> UserDataType (tmod_combine Tmod1 Tmod2)"
    by (simp add: tmod_combine_def)
next
  fix c
  assume "c \<in> Enum (tmod_combine Tmod1 Tmod2)"
  then have "c \<in> Enum Tmod1 \<union> Enum Tmod2"
    by (simp add: tmod_combine_def)
  then have "c \<notin> Class Tmod1 \<and> c \<notin> Class Tmod2 \<and> c \<notin> UserDataType Tmod1 \<and> c \<notin> UserDataType Tmod2"
  proof (elim UnE)
    assume "c \<in> Enum Tmod1"
    then show "c \<notin> Class Tmod1 \<and> c \<notin> Class Tmod2 \<and> c \<notin> UserDataType Tmod1 \<and> c \<notin> UserDataType Tmod2"
    proof (intro conjI)
      assume "c \<in> Enum Tmod1"
      then show "c \<notin> Class Tmod1"
        using tmod1_correct type_model.property_enum_disjoint
        by blast
    next
      assume "c \<in> Enum Tmod1"
      then show "c \<notin> Class Tmod2"
        by (simp add: property_enum_disjoint_tmod1)
    next
      assume "c \<in> Enum Tmod1"
      then show "c \<notin> UserDataType Tmod1"
        using tmod1_correct type_model.property_enum_disjoint
        by blast
    next
      assume "c \<in> Enum Tmod1"
      then show "c \<notin> UserDataType Tmod2"
        by (simp add: property_enum_disjoint_tmod1)
    qed
  next
    assume "c \<in> Enum Tmod2"
    then show "c \<notin> Class Tmod1 \<and> c \<notin> Class Tmod2 \<and> c \<notin> UserDataType Tmod1 \<and> c \<notin> UserDataType Tmod2"
    proof (intro conjI)
      assume "c \<in> Enum Tmod2"
      then show "c \<notin> Class Tmod1"
        by (simp add: property_enum_disjoint_tmod2)
    next
      assume "c \<in> Enum Tmod2"
      then show "c \<notin> Class Tmod2"
        using tmod2_correct type_model.property_enum_disjoint
        by blast
    next
      assume "c \<in> Enum Tmod2"
      then show "c \<notin> UserDataType Tmod1"
        by (simp add: property_enum_disjoint_tmod2)
    next
      assume "c \<in> Enum Tmod2"
      then show "c \<notin> UserDataType Tmod2"
        using tmod2_correct type_model.property_enum_disjoint
        by blast
    qed
  qed
  then show "c \<notin> Class (tmod_combine Tmod1 Tmod2) \<and> c \<notin> UserDataType (tmod_combine Tmod1 Tmod2)"
    by (simp add: tmod_combine_def)
next
  fix c
  assume "c \<in> UserDataType (tmod_combine Tmod1 Tmod2)"
  then have "c \<in> UserDataType Tmod1 \<union> UserDataType Tmod2"
    by (simp add: tmod_combine_def)
  then have "c \<notin> Class Tmod1 \<and> c \<notin> Class Tmod2 \<and> c \<notin> Enum Tmod1 \<and> c \<notin> Enum Tmod2"
  proof (elim UnE)
    assume "c \<in> UserDataType Tmod1"
    then show "c \<notin> Class Tmod1 \<and> c \<notin> Class Tmod2 \<and> c \<notin> Enum Tmod1 \<and> c \<notin> Enum Tmod2"
    proof (intro conjI)
      assume "c \<in> UserDataType Tmod1"
      then show "c \<notin> Class Tmod1"
        using tmod1_correct type_model.property_userdatatype_disjoint
        by blast
    next
      assume "c \<in> UserDataType Tmod1"
      then show "c \<notin> Class Tmod2"
        using property_class_disjoint_tmod2 
        by blast
    next
      assume "c \<in> UserDataType Tmod1"
      then show "c \<notin> Enum Tmod1"
        using tmod1_correct type_model.property_userdatatype_disjoint
        by blast
    next
      assume "c \<in> UserDataType Tmod1"
      then show "c \<notin> Enum Tmod2"
        using property_enum_disjoint_tmod2 
        by blast
    qed
  next
    assume "c \<in> UserDataType Tmod2"
    then show "c \<notin> Class Tmod1 \<and> c \<notin> Class Tmod2 \<and> c \<notin> Enum Tmod1 \<and> c \<notin> Enum Tmod2"
    proof (intro conjI)
      assume "c \<in> UserDataType Tmod2"
      then show "c \<notin> Class Tmod1"
        using property_class_disjoint_tmod1
        by blast
    next
      assume "c \<in> UserDataType Tmod2"
      then show "c \<notin> Class Tmod2"
        using tmod2_correct type_model.property_userdatatype_disjoint
        by blast
    next
      assume "c \<in> UserDataType Tmod2"
      then show "c \<notin> Enum Tmod1"
        using property_enum_disjoint_tmod1
        by blast
    next
      assume "c \<in> UserDataType Tmod2"
      then show "c \<notin> Enum Tmod2"
        using tmod2_correct type_model.property_userdatatype_disjoint
        by blast
    qed
  qed
  then show "c \<notin> Class (tmod_combine Tmod1 Tmod2) \<and> c \<notin> Enum (tmod_combine Tmod1 Tmod2)"
    by (simp add: tmod_combine_def)
next
  fix x y
  assume "x \<in> Class (tmod_combine Tmod1 Tmod2) \<union> Enum (tmod_combine Tmod1 Tmod2) \<union> UserDataType (tmod_combine Tmod1 Tmod2)"
  then have x_in_tmod: "x \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1 \<or> x \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2"
    using Un_iff select_convs(1) select_convs(2) simps(3) tmod_combine_def
    by metis
  assume "y \<in> Class (tmod_combine Tmod1 Tmod2) \<union> Enum (tmod_combine Tmod1 Tmod2) \<union> UserDataType (tmod_combine Tmod1 Tmod2)"
  then have y_in_tmod: "y \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1 \<or> y \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2"
    using Un_iff select_convs(1) select_convs(2) simps(3) tmod_combine_def
    by metis
  show "\<not>id_in_ns x (Identifier y)"
    using x_in_tmod y_in_tmod
  proof (elim disjE)
    assume x_in_tmod1: "x \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1"
    assume y_in_tmod1: "y \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1"
    show "\<not>id_in_ns x (Identifier y)"
      using x_in_tmod1 y_in_tmod1 tmod1_correct type_model.property_namespace_restriction
      by blast
  next
    assume x_in_tmod1: "x \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1"
    assume y_in_tmod2: "y \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2"
    show "\<not>id_in_ns x (Identifier y)"
      using x_in_tmod1 y_in_tmod2 property_namespace_restriction_tmod12
      by blast
  next
    assume x_in_tmod2: "x \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2"
    assume y_in_tmod1: "y \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1"
    show "\<not>id_in_ns x (Identifier y)"
      using x_in_tmod2 y_in_tmod1 property_namespace_restriction_tmod21
      by blast
  next
    assume x_in_tmod2: "x \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2"
    assume y_in_tmod2: "y \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2"
    show "\<not>id_in_ns x (Identifier y)"
      using x_in_tmod2 y_in_tmod2 tmod2_correct type_model.property_namespace_restriction
      by blast
  qed
next
  show "asym (Inh (tmod_combine Tmod1 Tmod2)) \<and> irrefl ((Inh (tmod_combine Tmod1 Tmod2))\<^sup>+)"
  proof (intro conjI)
    have "asym (Inh Tmod1 \<union> Inh Tmod2)"
      using asym.intros irrefl_def property_inh_wellformed_relation r_r_into_trancl
      by metis
    then show "asym (Inh (tmod_combine Tmod1 Tmod2))"
      by (simp add: tmod_combine_def)
  next
    show "irrefl ((Inh (tmod_combine Tmod1 Tmod2))\<^sup>+)"
      by (simp add: property_inh_wellformed_relation tmod_combine_def)
  qed
next
  fix f
  assume assump: "f \<in> Field (tmod_combine Tmod1 Tmod2) \<and> 
            type (tmod_combine Tmod1 Tmod2) f \<in> DataType \<union> EnumType (tmod_combine Tmod1 Tmod2) \<union> 
            UserDataTypeType (tmod_combine Tmod1 Tmod2) \<union> ProperClassType (tmod_combine Tmod1 Tmod2)"
  then have type_f_in_types: "type (tmod_combine Tmod1 Tmod2) f \<in> DataType \<union> EnumType Tmod1 \<union> EnumType Tmod2 \<union> 
          UserDataTypeType Tmod1 \<union> UserDataTypeType Tmod2 \<union> ProperClassType Tmod1 \<union> ProperClassType Tmod2"
    using assump 
    by simp
  have types_distinct: "\<And>Tmod1 Tmod2. (EnumType Tmod1 \<union> UserDataTypeType Tmod1 \<union> ProperClassType Tmod1) \<inter> 
          (NullableClassType Tmod2 \<union> ContainerType Tmod2) = {}"
    using enum_type_nullable_class_type_intersect userdatatype_type_nullable_class_type_intersect nullable_class_type_proper_class_type_intersect
    using container_type_enum_type_intersect container_type_userdatatype_type_intersect container_type_proper_class_type_intersect
    by fast
  have "f \<in> Field Tmod1 \<union> Field Tmod2"
    using assump
    by (simp add: tmod_combine_def)
  then have "f \<in> Field Tmod1 \<inter> Field Tmod2 \<or> f \<in> Field Tmod1 - Field Tmod2 \<or> f \<in> Field Tmod2 - Field Tmod1"
    by blast
  then show "lower (tmod_combine Tmod1 Tmod2) f = \<^bold>1"
  proof (elim disjE)
    assume f_in_both: "f \<in> Field Tmod1 \<inter> Field Tmod2"
    have tmod2_type_def: "fst (FieldSig Tmod2 f) \<in> Type Tmod2"
      using Int_iff f_in_both tmod2_correct type_model.structure_fieldsig_wellformed
      by metis
    have "fst (tmod_combine_fieldsig Tmod1 Tmod2 f) = fst (FieldSig Tmod1 f)"
      using f_in_both
      by (simp add: structure_fieldsig_wellformed_type tmod_combine_fieldsig_def)
    then have type_tmod12_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod1 f)"
      by (simp add: tmod_combine_def type_def)
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1"
      using IntD1 f_in_both tmod1_correct type_model.structure_fieldsig_wellformed_type
      by metis
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> DataType \<union> EnumType Tmod1 \<union> UserDataTypeType Tmod1 \<union> ProperClassType Tmod1"
      unfolding Type_def NonContainerType_def ClassType_def
      using type_f_in_types types_distinct
      by blast
    then have tmod1_f_type_def: "fst (FieldSig Tmod1 f) \<in> DataType \<union> EnumType Tmod1 \<union> UserDataTypeType Tmod1 \<union> ProperClassType Tmod1"
      by (simp add: type_tmod12_def)
    then have tmod2_f_type_def: "fst (FieldSig Tmod2 f) \<in> DataType \<union> EnumType Tmod2 \<union> UserDataTypeType Tmod2 \<union> ProperClassType Tmod2"
    proof (elim UnE)
      assume "fst (FieldSig Tmod1 f) \<in> DataType"
      then show "fst (FieldSig Tmod2 f) \<in> DataType \<union> EnumType Tmod2 \<union> UserDataTypeType Tmod2 \<union> ProperClassType Tmod2"
        using f_in_both structure_fieldsig_wellformed_type
        by simp
    next
      assume "fst (FieldSig Tmod1 f) \<in> EnumType Tmod1"
      then have "fst (FieldSig Tmod2 f) \<in> EnumType Tmod1"
        using f_in_both structure_fieldsig_wellformed_type
        by simp
      then have "fst (FieldSig Tmod2 f) \<in> EnumType Tmod2"
        using tmod2_type_def
        unfolding Type_def NonContainerType_def
        using enum_type_datatype_intersect enum_type_class_type_intersect userdatatype_type_enum_type_intersect container_type_enum_type_intersect
        by fast
      then show "fst (FieldSig Tmod2 f) \<in> DataType \<union> EnumType Tmod2 \<union> UserDataTypeType Tmod2 \<union> ProperClassType Tmod2"
        by simp
    next
      assume "fst (FieldSig Tmod1 f) \<in> UserDataTypeType Tmod1"
      then have "fst (FieldSig Tmod2 f) \<in> UserDataTypeType Tmod1"
        using f_in_both structure_fieldsig_wellformed_type
        by simp
      then have "fst (FieldSig Tmod2 f) \<in> UserDataTypeType Tmod2"
        using tmod2_type_def
        unfolding Type_def NonContainerType_def
        using userdatatype_type_datatype_intersect userdatatype_type_class_type_intersect userdatatype_type_enum_type_intersect container_type_userdatatype_type_intersect
        by fast
      then show "fst (FieldSig Tmod2 f) \<in> DataType \<union> EnumType Tmod2 \<union> UserDataTypeType Tmod2 \<union> ProperClassType Tmod2"
        by simp
    next
      assume "fst (FieldSig Tmod1 f) \<in> ProperClassType Tmod1"
      then have "fst (FieldSig Tmod2 f) \<in> ProperClassType Tmod1"
        using f_in_both structure_fieldsig_wellformed_type
        by simp
      then have "fst (FieldSig Tmod2 f) \<in> ProperClassType Tmod2"
        using tmod2_type_def
        unfolding Type_def NonContainerType_def ClassType_def
        using proper_class_type_datatype_intersect nullable_class_type_proper_class_type_intersect enum_type_proper_class_type_intersect 
        using userdatatype_type_proper_class_type_intersect container_type_proper_class_type_intersect
        by fast
      then show "fst (FieldSig Tmod2 f) \<in> DataType \<union> EnumType Tmod2 \<union> UserDataTypeType Tmod2 \<union> ProperClassType Tmod2"
        by simp
    qed
    have lower_tmod1_f: "lower Tmod1 f = \<^bold>1"
      using f_in_both tmod1_f_type_def
      by (simp add: tmod1_correct type_model.consistency_lower_multiplicity_non_nullable type_def)
    have lower_tmod2_f: "lower Tmod2 f = \<^bold>1"
      using f_in_both tmod2_f_type_def
      by (simp add: tmod2_correct type_model.consistency_lower_multiplicity_non_nullable type_def)
    have "snd (tmod_combine_fieldsig Tmod1 Tmod2 f) = snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f)"
      unfolding tmod_combine_fieldsig_def
      using f_in_both structure_fieldsig_wellformed_type
      by simp
    then show "lower (tmod_combine Tmod1 Tmod2) f = \<^bold>1"
      using lower_tmod1_f lower_tmod2_f
      unfolding lower_def
      by (simp add: mult_intersect_def tmod_combine_def)
  next
    assume f_in_tmod1: "f \<in> Field Tmod1 - Field Tmod2"
    then have "fst (tmod_combine_fieldsig Tmod1 Tmod2 f) = fst (FieldSig Tmod1 f)"
      by (simp add: structure_fieldsig_wellformed_type tmod_combine_fieldsig_def)
    then have type_tmod12_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod1 f)"
      by (simp add: tmod_combine_def type_def)
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1"
      using DiffD1 f_in_tmod1 tmod1_correct type_model.structure_fieldsig_wellformed_type
      by metis
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> DataType \<union> EnumType Tmod1 \<union> UserDataTypeType Tmod1 \<union> ProperClassType Tmod1"
      unfolding Type_def NonContainerType_def ClassType_def
      using type_f_in_types types_distinct
      by blast
    then have lower_tmod_f: "lower Tmod1 f = \<^bold>1"
      using Diff_iff f_in_tmod1 tmod1_correct type_def type_model.consistency_lower_multiplicity_non_nullable type_tmod12_def
      by metis
    have "snd (tmod_combine_fieldsig Tmod1 Tmod2 f) = snd (FieldSig Tmod1 f)"
      unfolding tmod_combine_fieldsig_def
      using f_in_tmod1
      by simp
    then show "lower (tmod_combine Tmod1 Tmod2) f = \<^bold>1"
      using lower_tmod_f
      unfolding lower_def
      by (simp add: tmod_combine_def)
  next
    assume f_in_tmod2: "f \<in> Field Tmod2 - Field Tmod1"
    then have "fst (tmod_combine_fieldsig Tmod1 Tmod2 f) = fst (FieldSig Tmod2 f)"
      by (simp add: structure_fieldsig_wellformed_type tmod_combine_fieldsig_def)
    then have type_tmod12_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod2 f)"
      by (simp add: tmod_combine_def type_def)
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod2"
      using DiffD1 f_in_tmod2 tmod2_correct type_model.structure_fieldsig_wellformed_type
      by metis
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> DataType \<union> EnumType Tmod2 \<union> UserDataTypeType Tmod2 \<union> ProperClassType Tmod2"
      unfolding Type_def NonContainerType_def ClassType_def
      using type_f_in_types types_distinct
      by blast
    then have lower_tmod_f: "lower Tmod2 f = \<^bold>1"
      using Diff_iff f_in_tmod2 tmod2_correct type_def type_model.consistency_lower_multiplicity_non_nullable type_tmod12_def
      by metis
    have "snd (tmod_combine_fieldsig Tmod1 Tmod2 f) = snd (FieldSig Tmod2 f)"
      unfolding tmod_combine_fieldsig_def
      using f_in_tmod2
      by simp
    then show "lower (tmod_combine Tmod1 Tmod2) f = \<^bold>1"
      using lower_tmod_f
      unfolding lower_def
      by (simp add: tmod_combine_def)
  qed
next
  fix f
  assume assump: "f \<in> Field (tmod_combine Tmod1 Tmod2) \<and> type (tmod_combine Tmod1 Tmod2) f \<in> NullableClassType (tmod_combine Tmod1 Tmod2)"
  then have type_f_in_types: "type (tmod_combine Tmod1 Tmod2) f \<in> NullableClassType Tmod1 \<union> NullableClassType Tmod2"
    by simp
  have types_distinct: "\<And>Tmod1 Tmod2. NullableClassType Tmod1 \<inter> 
          (DataType \<union> ProperClassType Tmod2 \<union> EnumType Tmod2 \<union> UserDataTypeType Tmod2 \<union> ContainerType Tmod2) = {}"
    using nullable_class_type_datatype_intersect nullable_class_type_proper_class_type_intersect enum_type_nullable_class_type_intersect
    using userdatatype_type_nullable_class_type_intersect container_type_nullable_class_type_intersect
    by fast
  have "f \<in> Field Tmod1 \<union> Field Tmod2"
    using assump
    by (simp add: tmod_combine_def)
  then have "f \<in> Field Tmod1 \<inter> Field Tmod2 \<or> f \<in> Field Tmod1 - Field Tmod2 \<or> f \<in> Field Tmod2 - Field Tmod1"
    by blast
  then show "lower (tmod_combine Tmod1 Tmod2) f = \<^bold>0"
  proof (elim disjE)
    assume f_in_both: "f \<in> Field Tmod1 \<inter> Field Tmod2"
    have tmod2_type_def: "fst (FieldSig Tmod2 f) \<in> Type Tmod2"
      using Int_iff f_in_both tmod2_correct type_model.structure_fieldsig_wellformed
      by metis
    have "fst (tmod_combine_fieldsig Tmod1 Tmod2 f) = fst (FieldSig Tmod1 f)"
      using f_in_both
      by (simp add: structure_fieldsig_wellformed_type tmod_combine_fieldsig_def)
    then have type_tmod12_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod1 f)"
      by (simp add: tmod_combine_def type_def)
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1"
      using IntD1 f_in_both tmod1_correct type_model.structure_fieldsig_wellformed_type
      by metis
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> NullableClassType Tmod1"
      unfolding Type_def NonContainerType_def ClassType_def
      using type_f_in_types types_distinct
      by blast
    then have tmod1_f_type_def: "fst (FieldSig Tmod1 f) \<in> NullableClassType Tmod1"
      by (simp add: type_tmod12_def)
    then have "fst (FieldSig Tmod2 f) \<in> NullableClassType Tmod1"
      using f_in_both structure_fieldsig_wellformed_type
      by simp
    then have tmod2_f_type_def: "fst (FieldSig Tmod2 f) \<in> NullableClassType Tmod2"
      using tmod2_type_def types_distinct
      unfolding Type_def NonContainerType_def ClassType_def
      by blast
    have lower_tmod1_f: "lower Tmod1 f = \<^bold>0"
      using f_in_both tmod1_f_type_def
      by (simp add: tmod1_correct type_model.consistency_lower_multiplicity_nullable type_def)
    have lower_tmod2_f: "lower Tmod2 f = \<^bold>0"
      using f_in_both tmod2_f_type_def
      by (simp add: tmod2_correct type_model.consistency_lower_multiplicity_nullable type_def)
    have "snd (tmod_combine_fieldsig Tmod1 Tmod2 f) = snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f)"
      unfolding tmod_combine_fieldsig_def
      using f_in_both structure_fieldsig_wellformed_type
      by simp
    then show "lower (tmod_combine Tmod1 Tmod2) f = \<^bold>0"
      using lower_tmod1_f lower_tmod2_f
      unfolding lower_def
      by (simp add: mult_intersect_def tmod_combine_def)
  next
    assume f_in_tmod1: "f \<in> Field Tmod1 - Field Tmod2"
    then have "fst (tmod_combine_fieldsig Tmod1 Tmod2 f) = fst (FieldSig Tmod1 f)"
      by (simp add: structure_fieldsig_wellformed_type tmod_combine_fieldsig_def)
    then have type_tmod12_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod1 f)"
      by (simp add: tmod_combine_def type_def)
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1"
      using DiffD1 f_in_tmod1 tmod1_correct type_model.structure_fieldsig_wellformed_type
      by metis
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> NullableClassType Tmod1"
      unfolding Type_def NonContainerType_def ClassType_def
      using type_f_in_types types_distinct
      by blast
    then have lower_tmod_f: "lower Tmod1 f = \<^bold>0"
      using Diff_iff f_in_tmod1 tmod1_correct type_def type_model.consistency_lower_multiplicity_nullable type_tmod12_def
      by metis
    have "snd (tmod_combine_fieldsig Tmod1 Tmod2 f) = snd (FieldSig Tmod1 f)"
      unfolding tmod_combine_fieldsig_def
      using f_in_tmod1
      by simp
    then show "lower (tmod_combine Tmod1 Tmod2) f = \<^bold>0"
      using lower_tmod_f
      unfolding lower_def
      by (simp add: tmod_combine_def)
  next
    assume f_in_tmod2: "f \<in> Field Tmod2 - Field Tmod1"
    then have "fst (tmod_combine_fieldsig Tmod1 Tmod2 f) = fst (FieldSig Tmod2 f)"
      by (simp add: structure_fieldsig_wellformed_type tmod_combine_fieldsig_def)
    then have type_tmod12_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod2 f)"
      by (simp add: tmod_combine_def type_def)
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod2"
      using DiffD1 f_in_tmod2 tmod2_correct type_model.structure_fieldsig_wellformed_type
      by metis
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> NullableClassType Tmod2"
      unfolding Type_def NonContainerType_def ClassType_def
      using type_f_in_types types_distinct
      by blast
    then have lower_tmod_f: "lower Tmod2 f = \<^bold>0"
      using Diff_iff f_in_tmod2 tmod2_correct type_def type_model.consistency_lower_multiplicity_nullable type_tmod12_def
      by metis
    have "snd (tmod_combine_fieldsig Tmod1 Tmod2 f) = snd (FieldSig Tmod2 f)"
      unfolding tmod_combine_fieldsig_def
      using f_in_tmod2
      by simp
    then show "lower (tmod_combine Tmod1 Tmod2) f = \<^bold>0"
      using lower_tmod_f
      unfolding lower_def
      by (simp add: tmod_combine_def)
  qed
next
  fix f
  assume assump: "f \<in> Field (tmod_combine Tmod1 Tmod2) \<and> type (tmod_combine Tmod1 Tmod2) f \<in> NonContainerType (tmod_combine Tmod1 Tmod2)"
  then have type_f_in_types: "type (tmod_combine Tmod1 Tmod2) f \<in> NonContainerType Tmod1 \<union> NonContainerType Tmod2"
    by simp
  have "f \<in> Field Tmod1 \<union> Field Tmod2"
    using assump
    by (simp add: tmod_combine_def)
  then have "f \<in> Field Tmod1 \<inter> Field Tmod2 \<or> f \<in> Field Tmod1 - Field Tmod2 \<or> f \<in> Field Tmod2 - Field Tmod1"
    by blast
  then show "upper (tmod_combine Tmod1 Tmod2) f = \<^bold>1"
  proof (elim disjE)
    assume f_in_both: "f \<in> Field Tmod1 \<inter> Field Tmod2"
    have tmod2_type_def: "fst (FieldSig Tmod2 f) \<in> Type Tmod2"
      using Int_iff f_in_both tmod2_correct type_model.structure_fieldsig_wellformed
      by metis
    have "fst (tmod_combine_fieldsig Tmod1 Tmod2 f) = fst (FieldSig Tmod1 f)"
      using f_in_both
      by (simp add: structure_fieldsig_wellformed_type tmod_combine_fieldsig_def)
    then have type_tmod12_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod1 f)"
      by (simp add: tmod_combine_def type_def)
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1"
      using IntD1 f_in_both tmod1_correct type_model.structure_fieldsig_wellformed_type
      by metis
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> NonContainerType Tmod1"
      unfolding Type_def
      using type_f_in_types container_type_non_container_type_intersect
      by blast
    then have tmod1_f_type_def: "fst (FieldSig Tmod1 f) \<in> NonContainerType Tmod1"
      by (simp add: type_tmod12_def)
    then have "fst (FieldSig Tmod2 f) \<in> NonContainerType Tmod1"
      using f_in_both structure_fieldsig_wellformed_type
      by simp
    then have tmod2_f_type_def: "fst (FieldSig Tmod2 f) \<in> NonContainerType Tmod2"
      using tmod2_type_def container_type_non_container_type_intersect
      unfolding Type_def
      by blast
    have upper_tmod1_f: "upper Tmod1 f = \<^bold>1"
      using f_in_both tmod1_f_type_def
      by (simp add: tmod1_correct type_model.consistency_upper_multiplicity_non_container type_def)
    have upper_tmod2_f: "upper Tmod2 f = \<^bold>1"
      using f_in_both tmod2_f_type_def
      by (simp add: tmod2_correct type_model.consistency_upper_multiplicity_non_container type_def)
    have "snd (tmod_combine_fieldsig Tmod1 Tmod2 f) = snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f)"
      unfolding tmod_combine_fieldsig_def
      using f_in_both structure_fieldsig_wellformed_type
      by simp
    then show "upper (tmod_combine Tmod1 Tmod2) f = \<^bold>1"
      using upper_tmod1_f upper_tmod2_f
      unfolding upper_def
      by (simp add: mult_intersect_def tmod_combine_def)
  next
    assume f_in_tmod1: "f \<in> Field Tmod1 - Field Tmod2"
    then have "fst (tmod_combine_fieldsig Tmod1 Tmod2 f) = fst (FieldSig Tmod1 f)"
      by (simp add: structure_fieldsig_wellformed_type tmod_combine_fieldsig_def)
    then have type_tmod12_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod1 f)"
      by (simp add: tmod_combine_def type_def)
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod1"
      using DiffD1 f_in_tmod1 tmod1_correct type_model.structure_fieldsig_wellformed_type
      by metis
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> NonContainerType Tmod1"
      unfolding Type_def
      using type_f_in_types container_type_non_container_type_intersect
      by blast
    then have upper_tmod_f: "upper Tmod1 f = \<^bold>1"
      using Diff_iff f_in_tmod1 tmod1_correct type_def type_model.consistency_upper_multiplicity_non_container type_tmod12_def
      by metis
    have "snd (tmod_combine_fieldsig Tmod1 Tmod2 f) = snd (FieldSig Tmod1 f)"
      unfolding tmod_combine_fieldsig_def
      using f_in_tmod1
      by simp
    then show "upper (tmod_combine Tmod1 Tmod2) f = \<^bold>1"
      using upper_tmod_f
      unfolding upper_def
      by (simp add: tmod_combine_def)
  next
    assume f_in_tmod2: "f \<in> Field Tmod2 - Field Tmod1"
    then have "fst (tmod_combine_fieldsig Tmod1 Tmod2 f) = fst (FieldSig Tmod2 f)"
      by (simp add: structure_fieldsig_wellformed_type tmod_combine_fieldsig_def)
    then have type_tmod12_def: "type (tmod_combine Tmod1 Tmod2) f = fst (FieldSig Tmod2 f)"
      by (simp add: tmod_combine_def type_def)
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> Type Tmod2"
      using DiffD1 f_in_tmod2 tmod2_correct type_model.structure_fieldsig_wellformed_type
      by metis
    then have "type (tmod_combine Tmod1 Tmod2) f \<in> NonContainerType Tmod2"
      unfolding Type_def NonContainerType_def ClassType_def
      using type_f_in_types container_type_non_container_type_intersect
      by blast
    then have upper_tmod_f: "upper Tmod2 f = \<^bold>1"
      using Diff_iff f_in_tmod2 tmod2_correct type_def type_model.consistency_upper_multiplicity_non_container type_tmod12_def
      by metis
    have "snd (tmod_combine_fieldsig Tmod1 Tmod2 f) = snd (FieldSig Tmod2 f)"
      unfolding tmod_combine_fieldsig_def
      using f_in_tmod2
      by simp
    then show "upper (tmod_combine Tmod1 Tmod2) f = \<^bold>1"
      using upper_tmod_f
      unfolding upper_def
      by (simp add: tmod_combine_def)
  qed
next
  fix r1 r2
  assume assump: "containment r1 \<in> Prop (tmod_combine Tmod1 Tmod2) \<and> opposite r1 r2 \<in> Prop (tmod_combine Tmod1 Tmod2)"
  then have containment_rel: "containment r1 \<in> tmod_combine_prop Tmod1 Tmod2"
    by (simp add: tmod_combine_def)
  have opposite_rel: "opposite r1 r2 \<in> tmod_combine_prop Tmod1 Tmod2"
    using assump select_convs(8) tmod_combine_def
    by metis
  show "upper (tmod_combine Tmod1 Tmod2) r2 = \<^bold>1"
    using containment_rel
  proof (cases)
    case containment_property_tmod1
    show ?thesis
      using opposite_rel
    proof (cases)
      case opposite_property_tmod1
      then have "snd (tmod_combine_fieldsig Tmod1 Tmod2 r2) = snd (FieldSig Tmod1 r2)"
        unfolding tmod_combine_fieldsig_def
        by (simp add: tmod1_correct type_model.structure_fieldsig_domain)
      then have "upper (tmod_combine Tmod1 Tmod2) r2 = upper Tmod1 r2"
        unfolding upper_def
        by (simp add: tmod_combine_def)
      then show ?thesis
        using containment_property_tmod1 opposite_property_tmod1(1) 
        using tmod1_correct type_model.consistency_containment_upper
        by fastforce
    next
      case opposite_property_tmod2
      then show ?thesis
        using DiffD1 Rel_def containment_property_tmod1 properties_rev_impl_containment tmod1_correct type_model.structure_properties_wellfomed
        by metis
    next
      case opposite_property_both
      then have "r2 \<in> Rel Tmod1 \<and> r2 \<in> Rel Tmod2"
        using properties_rev_impl_opposite tmod1_correct tmod2_correct type_model.structure_properties_wellfomed
        by blast
      then have r2_in_fields: "r2 \<in> Field Tmod1 \<and> r2 \<in> Field Tmod2"
        by (simp add: Rel_def)
      have upper_tmod1: "upper Tmod1 r2 = \<^bold>1"
        using containment_property_tmod1 opposite_property_both(1) tmod1_correct type_model.consistency_containment_upper
        by blast
      have upper_tmod2: "upper Tmod2 r2 \<ge> \<^bold>1"
      proof-
        have "multiplicity (snd (FieldSig Tmod2 r2))"
          using r2_in_fields tmod2_correct type_model.structure_fieldsig_wellformed_multiplicity
          by blast
        then show "upper Tmod2 r2 \<ge> \<^bold>1"
          using upper_def multiplicity.upper_bound_valid_alt
          by metis
      qed
      have "snd (tmod_combine_fieldsig Tmod1 Tmod2 r2) = snd (FieldSig Tmod1 r2) \<sqinter> snd (FieldSig Tmod2 r2)"
        unfolding tmod_combine_fieldsig_def
        by (simp add: r2_in_fields structure_fieldsig_wellformed_type)
      then have "upper (tmod_combine Tmod1 Tmod2) r2 = Multiplicity.upper (snd (FieldSig Tmod1 r2) \<sqinter> snd (FieldSig Tmod2 r2))"
        unfolding upper_def
        by (simp add: tmod_combine_def)
      then show ?thesis
        using upper_tmod1 upper_tmod2
        unfolding upper_def
        by (simp add: min_def mult_intersect_def)
    qed
  next
    case containment_property_tmod2
    show ?thesis
      using opposite_rel
    proof (cases)
      case opposite_property_tmod1
      then show ?thesis
        using DiffD1 Rel_def containment_property_tmod2 properties_rev_impl_containment tmod2_correct type_model.structure_properties_wellfomed
        by metis
    next
      case opposite_property_tmod2
      then have "snd (tmod_combine_fieldsig Tmod1 Tmod2 r2) = snd (FieldSig Tmod2 r2)"
        unfolding tmod_combine_fieldsig_def
        by (simp add: tmod2_correct type_model.structure_fieldsig_domain)
      then have "upper (tmod_combine Tmod1 Tmod2) r2 = upper Tmod2 r2"
        unfolding upper_def
        by (simp add: tmod_combine_def)
      then show ?thesis
        using containment_property_tmod2 opposite_property_tmod2(1) 
        using tmod2_correct type_model.consistency_containment_upper
        by fastforce
    next
      case opposite_property_both
      then have "r2 \<in> Rel Tmod1 \<and> r2 \<in> Rel Tmod2"
        using properties_rev_impl_opposite tmod1_correct tmod2_correct type_model.structure_properties_wellfomed
        by blast
      then have r2_in_fields: "r2 \<in> Field Tmod1 \<and> r2 \<in> Field Tmod2"
        by (simp add: Rel_def)
      have upper_tmod1: "upper Tmod1 r2 \<ge> \<^bold>1"
      proof-
        have "multiplicity (snd (FieldSig Tmod1 r2))"
          using r2_in_fields tmod1_correct type_model.structure_fieldsig_wellformed_multiplicity
          by blast
        then show "upper Tmod1 r2 \<ge> \<^bold>1"
          using upper_def multiplicity.upper_bound_valid_alt
          by metis
      qed
      have upper_tmod2: "upper Tmod2 r2 = \<^bold>1"
        using containment_property_tmod2 opposite_property_both(2) tmod2_correct type_model.consistency_containment_upper
        by blast
      have "snd (tmod_combine_fieldsig Tmod1 Tmod2 r2) = snd (FieldSig Tmod1 r2) \<sqinter> snd (FieldSig Tmod2 r2)"
        unfolding tmod_combine_fieldsig_def
        by (simp add: r2_in_fields structure_fieldsig_wellformed_type)
      then have "upper (tmod_combine Tmod1 Tmod2) r2 = Multiplicity.upper (snd (FieldSig Tmod1 r2) \<sqinter> snd (FieldSig Tmod2 r2))"
        unfolding upper_def
        by (simp add: tmod_combine_def)
      then show ?thesis
        using upper_tmod1 upper_tmod2
        unfolding upper_def
        by (simp add: min_def mult_intersect_def)
    qed
  qed
next
  fix v1 v2 f
  assume assump: "defaultValue f v1 \<in> Prop (tmod_combine Tmod1 Tmod2) \<and> defaultValue f v2 \<in> Prop (tmod_combine Tmod1 Tmod2)"
  have default_value_v1: "defaultValue f v1 \<in> tmod_combine_prop Tmod1 Tmod2"
    using assump select_convs(8) tmod_combine_def
    by metis
  have default_value_v2: "defaultValue f v2 \<in> tmod_combine_prop Tmod1 Tmod2"
    using assump select_convs(8) tmod_combine_def
    by metis
  show "v1 = v2"
    using default_value_v1
  proof (cases)
    case default_value_property_tmod1
    have default_value_v1_tmod1: "defaultValue f v1 \<in> Prop Tmod1"
      by (fact default_value_property_tmod1(1))
    have f_not_field_tmod2: "f \<notin> Field Tmod2"
      by (fact default_value_property_tmod1(2))
    show ?thesis
      using default_value_v2
    proof (cases)
      case default_value_property_tmod1
      then show ?thesis
        using default_value_v1_tmod1 tmod1_correct type_model.consistency_defaultvalue_unique
        by blast
    next
      case default_value_property_tmod2
      then have "f \<in> Field Tmod2"
        using properties_rev_impl_default_value tmod2_correct type_model.structure_properties_wellfomed
        by blast
      then show ?thesis
        using f_not_field_tmod2
        by simp
    next
      case default_value_property_both
      then show ?thesis
        using default_value_v1_tmod1 tmod1_correct type_model.consistency_defaultvalue_unique
        by blast
    qed
  next
    case default_value_property_tmod2
    have default_value_v1_tmod2: "defaultValue f v1 \<in> Prop Tmod2"
      by (fact default_value_property_tmod2(1))
    have f_not_field_tmod1: "f \<notin> Field Tmod1"
      by (fact default_value_property_tmod2(2))
    show ?thesis
      using default_value_v2
    proof (cases)
      case default_value_property_tmod1
      then have "f \<in> Field Tmod1"
        using properties_rev_impl_default_value tmod1_correct type_model.structure_properties_wellfomed
        by blast
      then show ?thesis
        using f_not_field_tmod1
        by simp
    next
      case default_value_property_tmod2
      then show ?thesis
        using default_value_v1_tmod2 tmod2_correct type_model.consistency_defaultvalue_unique
        by blast
    next
      case default_value_property_both
      then show ?thesis
        using default_value_v1_tmod2 tmod2_correct type_model.consistency_defaultvalue_unique
        by blast
    qed
  next
    case default_value_property_both
    have default_value_v1_tmod1: "defaultValue f v1 \<in> Prop Tmod1"
      by (fact default_value_property_both(1))
    have default_value_v1_tmod2: "defaultValue f v1 \<in> Prop Tmod2"
      by (fact default_value_property_both(2))
    show ?thesis
      using default_value_v2
    proof (cases)
      case default_value_property_tmod1
      then show ?thesis
        using default_value_v1_tmod1 tmod1_correct type_model.consistency_defaultvalue_unique
        by blast
    next
      case default_value_property_tmod2
      then show ?thesis
        using default_value_v1_tmod2 tmod2_correct type_model.consistency_defaultvalue_unique
        by blast
    next
      case default_value_property_both
      then show ?thesis
        using default_value_v1_tmod1 tmod1_correct type_model.consistency_defaultvalue_unique
        by blast
    qed
  qed
next
  have inh_wellformed_classes: "\<And>c. c \<in> Inh (tmod_combine Tmod1 Tmod2) \<Longrightarrow> fst c \<in> Class (tmod_combine Tmod1 Tmod2) \<and> snd c \<in> Class (tmod_combine Tmod1 Tmod2)"
  proof-
    fix c
    assume "c \<in> Inh (tmod_combine Tmod1 Tmod2)"
    then have "c \<in> Inh Tmod1 \<union> Inh Tmod2"
      by (simp add: tmod_combine_def)
    then have "fst c \<in> Class Tmod1 \<union> Class Tmod2 \<and> snd c \<in> Class Tmod1 \<union> Class Tmod2"
    proof (intro conjI)
      fix c
      assume "c \<in> Inh Tmod1 \<union> Inh Tmod2"
      then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
      proof (elim UnE)
        assume "c \<in> Inh Tmod1"
        then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod1_correct tmod_combine_def type_model.structure_inh_wellformed_fst_class)
      next
        assume "c \<in> Inh Tmod2"
        then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod2_correct tmod_combine_def type_model.structure_inh_wellformed_fst_class)
      qed
    next
      fix c
      assume "c \<in> Inh Tmod1 \<union> Inh Tmod2"
      then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
      proof (elim UnE)
        assume "c \<in> Inh Tmod1"
        then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod1_correct tmod_combine_def type_model.structure_inh_wellformed_snd_class)
      next
        assume "c \<in> Inh Tmod2"
        then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod2_correct tmod_combine_def type_model.structure_inh_wellformed_snd_class)
      qed
    qed
    then show "fst c \<in> Class (tmod_combine Tmod1 Tmod2) \<and> snd c \<in> Class (tmod_combine Tmod1 Tmod2)"
      unfolding tmod_combine_def
      by simp
  qed
  fix A B c1 c2
  assume "identity c1 A \<in> Prop (tmod_combine Tmod1 Tmod2)"
  then have identity_c1: "identity c1 A \<in> tmod_combine_prop Tmod1 Tmod2"
    by (simp add: tmod_combine_def)
  assume "identity c2 B \<in> Prop (tmod_combine Tmod1 Tmod2)"
  then have identity_c2: "identity c2 B \<in> tmod_combine_prop Tmod1 Tmod2"
    by (simp add: tmod_combine_def)
  assume c1_extends_c2: "\<exclamdown>c1 \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>c2"
  then have c1_c2_in_subtype_rel: "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_rel_altdef (tmod_combine Tmod1 Tmod2)"
    unfolding subtype_def
    by (simp add: inh_wellformed_classes subtype_rel_alt)
  then have c1_in_class: "c1 \<in> Class Tmod1 \<or> c1 \<in> Class Tmod2"
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_tuple ` Type (tmod_combine Tmod1 Tmod2)"
    then have "\<exclamdown>c1 \<in> Type Tmod1 \<union> Type Tmod2"
      using Pair_inject imageE subtype_tuple_def tmod_combine_type
      by metis
    then have "\<exclamdown>c1 \<in> ProperClassType Tmod1 \<union> ProperClassType Tmod2"
      unfolding Type_def NonContainerType_def ClassType_def
      by simp
    then show "c1 \<in> Class Tmod1 \<or> c1 \<in> Class Tmod2"
      by (simp add: ProperClassType.simps)
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
    then show "c1 \<in> Class Tmod1 \<or> c1 \<in> Class Tmod2"
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper proper ` (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
    then have "(c1, c2) \<in> (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
      unfolding subtype_conv_def
      by auto
    then have "(c1, c2) \<in> (Inh Tmod1 \<union> Inh Tmod2)\<^sup>+"
      by (simp add: tmod_combine_def)
    then have "c1 \<in> fst ` (Inh Tmod1 \<union> Inh Tmod2)"
    proof (induct)
      case (base y)
      then show ?case
        by force
    next
      case (step y z)
      then show ?case
        by blast
    qed
    then show "c1 \<in> Class Tmod1 \<or> c1 \<in> Class Tmod2"
      using tmod1_correct tmod2_correct type_model.structure_inh_wellformed_classes
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine Tmod1 Tmod2)"
    then have "(c1, c2) \<in> subtype_tuple ` (Class Tmod1 \<union> Class Tmod2)"
      unfolding subtype_conv_def
      by blast
    then show "c1 \<in> Class Tmod1 \<or> c1 \<in> Class Tmod2"
      unfolding subtype_tuple_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
    then have "(c1, c2) \<in> (Inh Tmod1 \<union> Inh Tmod2)\<^sup>+"
      unfolding subtype_conv_def
      by auto
    then have "c1 \<in> fst ` (Inh Tmod1 \<union> Inh Tmod2)"
    proof (induct)
      case (base y)
      then show ?case
        by force
    next
      case (step y z)
      then show ?case
        by blast
    qed
    then show "c1 \<in> Class Tmod1 \<or> c1 \<in> Class Tmod2"
      using tmod1_correct tmod2_correct type_model.structure_inh_wellformed_classes
      by blast
  qed
  have c2_in_class: "c2 \<in> Class Tmod1 \<or> c2 \<in> Class Tmod2"
    using c1_c2_in_subtype_rel
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_tuple ` Type (tmod_combine Tmod1 Tmod2)"
    then have "\<exclamdown>c2 \<in> Type Tmod1 \<union> Type Tmod2"
      using Pair_inject imageE subtype_tuple_def tmod_combine_type
      by metis
    then have "\<exclamdown>c2 \<in> ProperClassType Tmod1 \<union> ProperClassType Tmod2"
      unfolding Type_def NonContainerType_def ClassType_def
      by simp
    then show "c2 \<in> Class Tmod1 \<or> c2 \<in> Class Tmod2"
      by (simp add: ProperClassType.simps)
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
    then show "c2 \<in> Class Tmod1 \<or> c2 \<in> Class Tmod2"
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper proper ` (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
    then have "(c1, c2) \<in> (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
      unfolding subtype_conv_def
      by auto
    then have "(c1, c2) \<in> (Inh Tmod1 \<union> Inh Tmod2)\<^sup>+"
      by (simp add: tmod_combine_def)
    then have "c2 \<in> snd ` (Inh Tmod1 \<union> Inh Tmod2)"
    proof (induct)
      case (base y)
      then show ?case
        by force
    next
      case (step y z)
      then show ?case
        by force
    qed
    then show "c2 \<in> Class Tmod1 \<or> c2 \<in> Class Tmod2"
      using tmod1_correct tmod2_correct type_model.structure_inh_wellformed_classes
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine Tmod1 Tmod2)"
    then show "c2 \<in> Class Tmod1 \<or> c2 \<in> Class Tmod2"
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
    then show "c2 \<in> Class Tmod1 \<or> c2 \<in> Class Tmod2"
      unfolding subtype_conv_def
      by blast
  qed
  have "\<exclamdown>c1 \<sqsubseteq>[Tmod1] \<exclamdown>c2 \<or> \<exclamdown>c1 \<sqsubseteq>[Tmod2] \<exclamdown>c2 \<or> \<not>(\<exclamdown>c1 \<sqsubseteq>[Tmod1] \<exclamdown>c2) \<and> \<not>(\<exclamdown>c1 \<sqsubseteq>[Tmod2] \<exclamdown>c2)"
    by blast
  then show "A \<subseteq> B"
  proof (elim disjE)
    assume c1_extends_c2_tmod1: "\<exclamdown>c1 \<sqsubseteq>[Tmod1] \<exclamdown>c2"
    then have c1_c2_classes: "c1 \<in> Class Tmod1 \<and> c2 \<in> Class Tmod1"
      unfolding subtype_def
    proof (cases)
      case (transitivity t2)
      have c1_in_proper_class_type: "\<exclamdown>c1 \<in> ProperClassType Tmod1"
        using transitivity(1)
        unfolding Type_def NonContainerType_def ClassType_def
        by simp
      have c2_in_proper_class_type: "\<exclamdown>c2 \<in> ProperClassType Tmod1"
        using transitivity(3)
        unfolding Type_def NonContainerType_def ClassType_def
        by simp
      show ?thesis
        using c1_in_proper_class_type c2_in_proper_class_type
        by (simp add: ProperClassType.simps)
    next
      case reflexivity
      then have "\<exclamdown>c1 \<in> ProperClassType Tmod1"
        unfolding Type_def NonContainerType_def ClassType_def
        by simp
      then show ?thesis
        by (simp add: ProperClassType.simps reflexivity(1))
    next
      case generalization_of_inheritance_proper
      then show ?thesis
        using tmod1_correct type_model.structure_inh_wellformed_classes
        by fastforce
    qed
    show ?thesis
      using identity_c1
    proof (cases)
      case identity_property_tmod1
      have identity_c1_tmod1: "identity c1 A \<in> Prop Tmod1"
        by (fact identity_property_tmod1(1))
      have c1_not_in_class_tmod2: "c1 \<notin> Class Tmod2"
        by (fact identity_property_tmod1(2))
      show ?thesis
        using identity_c2
      proof (cases)
        case identity_property_tmod1
        then show ?thesis
          using c1_extends_c2_tmod1 identity_c1_tmod1 tmod1_correct type_model.consistency_identity_valid
          by blast
      next
        case identity_property_tmod2
        then show ?thesis
          using c1_c2_classes
          by blast
      next
        case identity_property_both
        then show ?thesis
          using c1_extends_c2_tmod1 identity_c1_tmod1 tmod1_correct type_model.consistency_identity_valid
          by blast
      qed
    next
      case identity_property_tmod2
      then show ?thesis
        using c1_c2_classes
        by blast
    next
      case identity_property_both
      have identity_c1_tmod1: "identity c1 A \<in> Prop Tmod1"
        by (fact identity_property_both(1))
      have identity_c1_tmod2: "identity c1 A \<in> Prop Tmod2"
        by (fact identity_property_both(2))
      show ?thesis
        using identity_c2
      proof (cases)
        case identity_property_tmod1
        then show ?thesis
          using c1_extends_c2_tmod1 identity_c1_tmod1 tmod1_correct type_model.consistency_identity_valid
          by blast
      next
        case identity_property_tmod2
        then show ?thesis
          using c1_c2_classes
          by blast
      next
        case identity_property_both
        then show ?thesis
          using c1_extends_c2_tmod1 identity_c1_tmod1 tmod1_correct type_model.consistency_identity_valid
          by blast
      qed
    qed
  next
    assume c1_extends_c2_tmod2: "\<exclamdown>c1 \<sqsubseteq>[Tmod2] \<exclamdown>c2"
    then have c1_c2_classes: "c1 \<in> Class Tmod2 \<and> c2 \<in> Class Tmod2"
      unfolding subtype_def
    proof (cases)
      case (transitivity t2)
      have c1_in_proper_class_type: "\<exclamdown>c1 \<in> ProperClassType Tmod2"
        using transitivity(1)
        unfolding Type_def NonContainerType_def ClassType_def
        by simp
      have c2_in_proper_class_type: "\<exclamdown>c2 \<in> ProperClassType Tmod2"
        using transitivity(3)
        unfolding Type_def NonContainerType_def ClassType_def
        by simp
      show ?thesis
        using c1_in_proper_class_type c2_in_proper_class_type
        by (simp add: ProperClassType.simps)
    next
      case reflexivity
      then have "\<exclamdown>c1 \<in> ProperClassType Tmod2"
        unfolding Type_def NonContainerType_def ClassType_def
        by simp
      then show ?thesis
        by (simp add: ProperClassType.simps reflexivity(1))
    next
      case generalization_of_inheritance_proper
      then show ?thesis
        using tmod2_correct type_model.structure_inh_wellformed_classes
        by fastforce
    qed
    show ?thesis
      using identity_c1
    proof (cases)
      case identity_property_tmod1
      then show ?thesis
        using c1_c2_classes
        by blast
    next
      case identity_property_tmod2
      have identity_c1_tmod2: "identity c1 A \<in> Prop Tmod2"
        by (fact identity_property_tmod2(1))
      have c1_not_in_class_tmod1: "c1 \<notin> Class Tmod1"
        by (fact identity_property_tmod2(2))
      show ?thesis
        using identity_c2
      proof (cases)
        case identity_property_tmod1
        then show ?thesis
          using c1_c2_classes
          by blast
      next
        case identity_property_tmod2
        then show ?thesis
          using c1_extends_c2_tmod2 identity_c1_tmod2 tmod2_correct type_model.consistency_identity_valid
          by blast
      next
        case identity_property_both
        then show ?thesis
          using c1_extends_c2_tmod2 identity_c1_tmod2 tmod2_correct type_model.consistency_identity_valid
          by blast
      qed
    next
      case identity_property_both
      have identity_c1_tmod1: "identity c1 A \<in> Prop Tmod1"
        by (fact identity_property_both(1))
      have identity_c1_tmod2: "identity c1 A \<in> Prop Tmod2"
        by (fact identity_property_both(2))
      show ?thesis
        using identity_c2
      proof (cases)
        case identity_property_tmod1
        then show ?thesis
          using c1_c2_classes
          by blast
      next
        case identity_property_tmod2
        then show ?thesis
          using c1_extends_c2_tmod2 identity_c1_tmod2 tmod2_correct type_model.consistency_identity_valid
          by blast
      next
        case identity_property_both
        then show ?thesis
          using c1_extends_c2_tmod2 identity_c1_tmod2 tmod2_correct type_model.consistency_identity_valid
          by blast
      qed
    qed
  next
    assume c1_no_tmod_extend_c2: "\<not>(\<exclamdown>c1 \<sqsubseteq>[Tmod1] \<exclamdown>c2) \<and> \<not>(\<exclamdown>c1 \<sqsubseteq>[Tmod2] \<exclamdown>c2)"
    have "c1 = c2 \<or> c1 \<noteq> c2"
      by simp
    then show ?thesis
    proof (elim disjE)
      assume c1_c2_eq: "c1 = c2"
      then show ?thesis
        using c1_in_class
      proof (elim disjE)
        assume "c1 \<in> Class Tmod1"
        then have "\<exclamdown>c1 \<in> Type Tmod1"
          using ProperClassType.rule_proper_classes subsetD type_subset_proper_class_type
          by metis
        then have "\<exclamdown>c1 \<sqsubseteq>[Tmod1] \<exclamdown>c2"
          unfolding subtype_def
          using c1_c2_eq subtype_rel.reflexivity
          by blast
        then show ?thesis
          using c1_no_tmod_extend_c2
          by blast
      next
        assume "c1 \<in> Class Tmod2"
        then have "\<exclamdown>c1 \<in> Type Tmod2"
          using ProperClassType.rule_proper_classes subsetD type_subset_proper_class_type
          by metis
        then have "\<exclamdown>c1 \<sqsubseteq>[Tmod2] \<exclamdown>c2"
          unfolding subtype_def
          using c1_c2_eq subtype_rel.reflexivity
          by blast
        then show ?thesis
          using c1_no_tmod_extend_c2
          by blast
      qed
    next
      assume c1_c2_not_eq: "c1 \<noteq> c2"
      then show ?thesis
        using identity_c1 identity_c2 c1_no_tmod_extend_c2 c1_extends_c2 consistency_identity_valid
        by simp
    qed
  qed
next
  fix A1 A2 r
  assume assump: "keyset r A1 \<in> Prop (tmod_combine Tmod1 Tmod2) \<and> keyset r A2 \<in> Prop (tmod_combine Tmod1 Tmod2)"
  have keyset_a1: "keyset r A1 \<in> tmod_combine_prop Tmod1 Tmod2"
    using assump select_convs(8) tmod_combine_def
    by metis
  have keyset_a2: "keyset r A2 \<in> tmod_combine_prop Tmod1 Tmod2"
    using assump select_convs(8) tmod_combine_def
    by metis
  show "A1 = A2"
    using keyset_a1
  proof (cases)
    case keyset_property_tmod1
    have keyset_a1_tmod1: "keyset r A1 \<in> Prop Tmod1"
      by (fact keyset_property_tmod1(1))
    have r_not_in_field_tmod2: "r \<notin> Field Tmod2"
      by (fact keyset_property_tmod1(2))
    show ?thesis
      using keyset_a2
    proof (cases)
      case keyset_property_tmod1
      then show ?thesis
        using keyset_a1_tmod1 tmod1_correct type_model.consistency_keyset_unique
        by blast
    next
      case keyset_property_tmod2
      then have "r \<in> Field Tmod2"
        using DiffD1 Rel_def properties_rev_impl_keyset tmod2_correct type_model.structure_properties_wellfomed
        by metis
      then show ?thesis
        using r_not_in_field_tmod2
        by blast
    next
      case keyset_property_both
      then show ?thesis
        using keyset_a1_tmod1 tmod1_correct type_model.consistency_keyset_unique
        by blast
    qed
  next
    case keyset_property_tmod2
    have keyset_a1_tmod2: "keyset r A1 \<in> Prop Tmod2"
      by (fact keyset_property_tmod2(1))
    have r_not_in_field_tmod1: "r \<notin> Field Tmod1"
      by (fact keyset_property_tmod2(2))
    show ?thesis
      using keyset_a2
    proof (cases)
      case keyset_property_tmod1
      then have "r \<in> Field Tmod1"
        using DiffD1 Rel_def properties_rev_impl_keyset tmod1_correct type_model.structure_properties_wellfomed
        by metis
      then show ?thesis
        using r_not_in_field_tmod1
        by blast
    next
      case keyset_property_tmod2
      then show ?thesis
        using keyset_a1_tmod2 tmod2_correct type_model.consistency_keyset_unique
        by blast
    next
      case keyset_property_both
      then show ?thesis
        using keyset_a1_tmod2 tmod2_correct type_model.consistency_keyset_unique
        by blast
    qed
  next
    case keyset_property_both
    have keyset_a1_tmod1: "keyset r A1 \<in> Prop Tmod1"
      by (fact keyset_property_both(1))
    have keyset_a1_tmod2: "keyset r A1 \<in> Prop Tmod2"
      by (fact keyset_property_both(2))
    show ?thesis
      using keyset_a2
    proof (cases)
      case keyset_property_tmod1
      then show ?thesis
        using keyset_a1_tmod1 tmod1_correct type_model.consistency_keyset_unique
        by blast
    next
      case keyset_property_tmod2
      then show ?thesis
        using keyset_a1_tmod2 tmod2_correct type_model.consistency_keyset_unique
        by blast
    next
      case keyset_property_both
      then show ?thesis
        using keyset_a1_tmod1 tmod1_correct type_model.consistency_keyset_unique
        by blast
    qed
  qed
next
  fix r1 r2 r
  assume assump: "opposite r r1 \<in> Prop (tmod_combine Tmod1 Tmod2) \<and> opposite r r2 \<in> Prop (tmod_combine Tmod1 Tmod2)"
  have opposite_r1: "opposite r r1 \<in> tmod_combine_prop Tmod1 Tmod2"
    using assump select_convs(8) tmod_combine_def
    by metis
  have opposite_r2: "opposite r r2 \<in> tmod_combine_prop Tmod1 Tmod2"
    using assump select_convs(8) tmod_combine_def
    by metis
  show "r1 = r2"
    using opposite_r1
  proof (cases)
    case opposite_property_tmod1
    have opposite_r1_tmod1: "opposite r r1 \<in> Prop Tmod1"
      by (fact opposite_property_tmod1(1))
    have r_not_in_field_tmod2: "r \<notin> Field Tmod2"
      by (fact opposite_property_tmod1(2))
    have r1_not_in_field_tmod2: "r1 \<notin> Field Tmod2"
      by (fact opposite_property_tmod1(3))
    show ?thesis
      using opposite_r2
    proof (cases)
      case opposite_property_tmod1
      then show ?thesis
        using opposite_r1_tmod1 tmod1_correct type_model.consistency_opposite_unique
        by blast
    next
      case opposite_property_tmod2
      then have "r \<in> Field Tmod2"
        using Diff_iff Rel_def properties_rev_impl_opposite tmod2_correct type_model.structure_properties_wellfomed
        by metis
      then show ?thesis
        using r_not_in_field_tmod2
        by blast
    next
      case opposite_property_both
      then show ?thesis
        using opposite_r1_tmod1 tmod1_correct type_model.consistency_opposite_unique
        by blast
    qed
  next
    case opposite_property_tmod2
    have opposite_r1_tmod2: "opposite r r1 \<in> Prop Tmod2"
      by (fact opposite_property_tmod2(1))
    have r_not_in_field_tmod1: "r \<notin> Field Tmod1"
      by (fact opposite_property_tmod2(2))
    have r1_not_in_field_tmod1: "r1 \<notin> Field Tmod1"
      by (fact opposite_property_tmod2(3))
    show ?thesis
      using opposite_r2
    proof (cases)
      case opposite_property_tmod1
      then have "r \<in> Field Tmod1"
        using Diff_iff Rel_def properties_rev_impl_opposite tmod1_correct type_model.structure_properties_wellfomed
        by metis
      then show ?thesis
        using r_not_in_field_tmod1
        by blast
    next
      case opposite_property_tmod2
      then show ?thesis
        using opposite_r1_tmod2 tmod2_correct type_model.consistency_opposite_unique
        by blast
    next
      case opposite_property_both
      then show ?thesis
        using opposite_r1_tmod2 tmod2_correct type_model.consistency_opposite_unique
        by blast
    qed
  next
    case opposite_property_both
    have opposite_r1_tmod1: "opposite r r1 \<in> Prop Tmod1"
      by (fact opposite_property_both(1))
    have opposite_r1_tmod2: "opposite r r1 \<in> Prop Tmod2"
      by (fact opposite_property_both(2))
    show ?thesis
      using opposite_r2
    proof (cases)
      case opposite_property_tmod1
      then show ?thesis
        using opposite_r1_tmod1 tmod1_correct type_model.consistency_opposite_unique
        by blast
    next
      case opposite_property_tmod2
      then show ?thesis
        using opposite_r1_tmod2 tmod2_correct type_model.consistency_opposite_unique
        by blast
    next
      case opposite_property_both
      then show ?thesis
        using opposite_r1_tmod1 tmod1_correct type_model.consistency_opposite_unique
        by blast
    qed
  qed
next
  fix r1 r2
  assume "opposite r1 r2 \<in> Prop (tmod_combine Tmod1 Tmod2)"
  then have "opposite r1 r2 \<in> tmod_combine_prop Tmod1 Tmod2"
    by (simp add: tmod_combine_def)
  then have "opposite r2 r1 \<in> tmod_combine_prop Tmod1 Tmod2"
  proof (cases)
    case opposite_property_tmod1
    then have "opposite r2 r1 \<in> Prop Tmod1"
      using tmod1_correct type_model.consistency_opposite_sym
      by blast
    then show ?thesis
      using opposite_property_tmod1(2) opposite_property_tmod1(3) tmod_combine_prop.opposite_property_tmod1
      by blast
  next
    case opposite_property_tmod2
    then have "opposite r2 r1 \<in> Prop Tmod2"
      using tmod2_correct type_model.consistency_opposite_sym
      by blast
    then show ?thesis
      using opposite_property_tmod2(2) opposite_property_tmod2(3) tmod_combine_prop.opposite_property_tmod2
      by blast
  next
    case opposite_property_both
    then have "opposite r2 r1 \<in> Prop Tmod1 \<and> opposite r2 r1 \<in> Prop Tmod2"
      using tmod1_correct tmod2_correct type_model.consistency_opposite_sym
      by blast
    then show ?thesis
      using opposite_property_both(1) opposite_property_both(2) tmod_combine_prop.opposite_property_both
      by blast
  qed
  then show "opposite r2 r1 \<in> Prop (tmod_combine Tmod1 Tmod2)"
    by (simp add: tmod_combine_def)
qed

lemma tmod_combine_merge_correct[intro]:
  assumes tmod1_correct: "type_model Tmod1"
  assumes tmod2_correct: "type_model Tmod2"
  assumes combine_fields_distinct: "Field Tmod1 \<inter> Field Tmod2 = {}"
  assumes combine_constants_distinct: "Constant Tmod1 \<inter> Constant Tmod2 = {}"
  assumes property_class_disjoint_tmod1: "\<And>c. c \<in> Class Tmod1 \<Longrightarrow> c \<notin> Enum Tmod2 \<and> c \<notin> UserDataType Tmod2"
  assumes property_class_disjoint_tmod2: "\<And>c. c \<in> Class Tmod2 \<Longrightarrow> c \<notin> Enum Tmod1 \<and> c \<notin> UserDataType Tmod1"
  assumes property_enum_disjoint_tmod1: "\<And>e. e \<in> Enum Tmod1 \<Longrightarrow> e \<notin> Class Tmod2 \<and> e \<notin> UserDataType Tmod2"
  assumes property_enum_disjoint_tmod2: "\<And>e. e \<in> Enum Tmod2 \<Longrightarrow> e \<notin> Class Tmod1 \<and> e \<notin> UserDataType Tmod1"
  assumes property_namespace_restriction_tmod12: "\<And>x y. x \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1 \<Longrightarrow> y \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2 \<Longrightarrow> \<not>id_in_ns x (Identifier y)"
  assumes property_namespace_restriction_tmod21: "\<And>x y. x \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2 \<Longrightarrow> y \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1 \<Longrightarrow> \<not>id_in_ns x (Identifier y)"
  assumes property_inh_wellformed_relation: "irrefl ((Inh Tmod1 \<union> Inh Tmod2)\<^sup>+)"
  assumes consistency_identity_valid: "\<And>c1 c2 A B. identity c1 A \<in> tmod_combine_prop Tmod1 Tmod2 \<Longrightarrow> identity c2 B \<in> tmod_combine_prop Tmod1 Tmod2 \<Longrightarrow> 
    c1 \<noteq> c2 \<Longrightarrow> \<not>(\<exclamdown>c1 \<sqsubseteq>[Tmod1] \<exclamdown>c2) \<Longrightarrow> \<not>(\<exclamdown>c1 \<sqsubseteq>[Tmod2] \<exclamdown>c2) \<Longrightarrow> \<exclamdown>c1 \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>c2 \<Longrightarrow> A \<subseteq> B"
  shows "type_model (tmod_combine Tmod1 Tmod2)"
  by (intro tmod_combine_correct) (simp_all add: assms)

lemma tmod_combine_distinct_inh[simp]:
  assumes tmod1_correct: "type_model Tmod1"
  assumes tmod2_correct: "type_model Tmod2"
  assumes combine_classes_distinct: "Class Tmod1 \<inter> Class Tmod2 = {}"
  shows "(Inh Tmod1 \<union> Inh Tmod2)\<^sup>+ = (Inh Tmod1)\<^sup>+ \<union> (Inh Tmod2)\<^sup>+"
proof
  show "(Inh Tmod1 \<union> Inh Tmod2)\<^sup>+ \<subseteq> (Inh Tmod1)\<^sup>+ \<union> (Inh Tmod2)\<^sup>+"
  proof
    fix x
    assume "x \<in> (Inh Tmod1 \<union> Inh Tmod2)\<^sup>+"
    then show "x \<in> (Inh Tmod1)\<^sup>+ \<union> (Inh Tmod2)\<^sup>+"
    proof (induct x)
      case (fields a b c)
      then show ?case
      proof (induct)
        case (base y)
        then show ?case
          by blast
      next
        case (step y z)
        then show ?case
        proof (elim UnE)
          assume yz_tmod1: "(y, z) \<in> Inh Tmod1"
          assume ay_tmod1: "(a, y) \<in> (Inh Tmod1)\<^sup>+"
          show ?thesis
            using ay_tmod1 yz_tmod1
            by auto
        next
          assume "(y, z) \<in> Inh Tmod1"
          then have y_tmod1: "y \<in> Class Tmod1"
            using tmod1_correct type_model.structure_inh_wellformed_alt
            by blast
          assume "(a, y) \<in> (Inh Tmod2)\<^sup>+"
          then have y_tmod2: "y \<in> Class Tmod2"
            using tmod2_correct trancl.simps type_model.structure_inh_wellformed_alt
            by metis
          show ?thesis
            using y_tmod1 y_tmod2 combine_classes_distinct
            by blast
        next
          assume "(y, z) \<in> Inh Tmod2"
          then have y_tmod2: "y \<in> Class Tmod2"
            using tmod2_correct type_model.structure_inh_wellformed_alt
            by blast
          assume "(a, y) \<in> (Inh Tmod1)\<^sup>+"
          then have y_tmod1: "y \<in> Class Tmod1"
            using tmod1_correct trancl.simps type_model.structure_inh_wellformed_alt
            by metis
          show ?thesis
            using y_tmod2 y_tmod1 combine_classes_distinct
            by blast
        next
          assume yz_tmod2: "(y, z) \<in> Inh Tmod2"
          assume ay_tmod2: "(a, y) \<in> (Inh Tmod2)\<^sup>+"
          show ?thesis
            using Un_iff trancl.trancl_into_trancl ay_tmod2 yz_tmod2
            by metis
        qed
      qed
    qed
  qed
next
  show "(Inh Tmod1)\<^sup>+ \<union> (Inh Tmod2)\<^sup>+ \<subseteq> (Inh Tmod1 \<union> Inh Tmod2)\<^sup>+"
    by (simp add: subsetI trancl_mono)
qed

lemma tmod_combine_distinct_correct[intro]:
  assumes tmod1_correct: "type_model Tmod1"
  assumes tmod2_correct: "type_model Tmod2"
  assumes combine_classes_distinct: "Class Tmod1 \<inter> Class Tmod2 = {}"
  assumes combine_enums_distinct: "Enum Tmod1 \<inter> Enum Tmod2 = {}"
  assumes combine_userdatatypes_distinct: "UserDataType Tmod1 \<inter> UserDataType Tmod2 = {}"
  assumes combine_constants_distinct: "Constant Tmod1 \<inter> Constant Tmod2 = {}"
  assumes property_class_disjoint_tmod1: "\<And>c. c \<in> Class Tmod1 \<Longrightarrow> c \<notin> Enum Tmod2 \<and> c \<notin> UserDataType Tmod2"
  assumes property_class_disjoint_tmod2: "\<And>c. c \<in> Class Tmod2 \<Longrightarrow> c \<notin> Enum Tmod1 \<and> c \<notin> UserDataType Tmod1"
  assumes property_enum_disjoint_tmod1: "\<And>e. e \<in> Enum Tmod1 \<Longrightarrow> e \<notin> Class Tmod2 \<and> e \<notin> UserDataType Tmod2"
  assumes property_enum_disjoint_tmod2: "\<And>e. e \<in> Enum Tmod2 \<Longrightarrow> e \<notin> Class Tmod1 \<and> e \<notin> UserDataType Tmod1"
  assumes property_namespace_restriction_tmod12: "\<And>x y. x \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1 \<Longrightarrow> y \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2 \<Longrightarrow> \<not>id_in_ns x (Identifier y)"
  assumes property_namespace_restriction_tmod21: "\<And>x y. x \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2 \<Longrightarrow> y \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1 \<Longrightarrow> \<not>id_in_ns x (Identifier y)"
  shows "type_model (tmod_combine Tmod1 Tmod2)"
proof (intro tmod_combine_merge_correct)
  show "Field Tmod1 \<inter> Field Tmod2 = {}"
    using tmod1_correct tmod2_correct type_model.structure_field_wellformed_class combine_classes_distinct
    by blast
next
  have "irrefl ((Inh Tmod1)\<^sup>+ \<union> (Inh Tmod2)\<^sup>+)"
    using irrefl_def tmod1_correct tmod2_correct type_model.property_inh_wellformed_trancl_irrefl
    by auto
  then show "irrefl ((Inh Tmod1 \<union> Inh Tmod2)\<^sup>+)"
    by (simp add: combine_classes_distinct tmod1_correct tmod2_correct)
next
  have inh_wellformed_classes: "\<And>c. c \<in> Inh (tmod_combine Tmod1 Tmod2) \<Longrightarrow> fst c \<in> Class (tmod_combine Tmod1 Tmod2) \<and> snd c \<in> Class (tmod_combine Tmod1 Tmod2)"
  proof-
    fix c
    assume "c \<in> Inh (tmod_combine Tmod1 Tmod2)"
    then have "c \<in> Inh Tmod1 \<union> Inh Tmod2"
      by (simp add: tmod_combine_def)
    then have "fst c \<in> Class Tmod1 \<union> Class Tmod2 \<and> snd c \<in> Class Tmod1 \<union> Class Tmod2"
    proof (intro conjI)
      fix c
      assume "c \<in> Inh Tmod1 \<union> Inh Tmod2"
      then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
      proof (elim UnE)
        assume "c \<in> Inh Tmod1"
        then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod1_correct tmod_combine_def type_model.structure_inh_wellformed_fst_class)
      next
        assume "c \<in> Inh Tmod2"
        then show "fst c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod2_correct tmod_combine_def type_model.structure_inh_wellformed_fst_class)
      qed
    next
      fix c
      assume "c \<in> Inh Tmod1 \<union> Inh Tmod2"
      then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
      proof (elim UnE)
        assume "c \<in> Inh Tmod1"
        then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod1_correct tmod_combine_def type_model.structure_inh_wellformed_snd_class)
      next
        assume "c \<in> Inh Tmod2"
        then show "snd c \<in> Class Tmod1 \<union> Class Tmod2"
          by (simp add: tmod2_correct tmod_combine_def type_model.structure_inh_wellformed_snd_class)
      qed
    qed
    then show "fst c \<in> Class (tmod_combine Tmod1 Tmod2) \<and> snd c \<in> Class (tmod_combine Tmod1 Tmod2)"
      unfolding tmod_combine_def
      by simp
  qed
  fix c1 c2
  assume no_tmod1_extend: "\<not>(\<exclamdown>c1 \<sqsubseteq>[Tmod1] \<exclamdown>c2)"
  assume no_tmod2_extend: "\<not>(\<exclamdown>c1 \<sqsubseteq>[Tmod2] \<exclamdown>c2)"
  assume "\<exclamdown>c1 \<sqsubseteq>[tmod_combine Tmod1 Tmod2] \<exclamdown>c2"
  then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_rel_altdef (tmod_combine Tmod1 Tmod2)"
    unfolding subtype_def
    by (simp add: inh_wellformed_classes subtype_rel_alt)
  then have "\<exclamdown>c1 \<sqsubseteq>[Tmod1] \<exclamdown>c2 \<or> \<exclamdown>c1 \<sqsubseteq>[Tmod2] \<exclamdown>c2"
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume c1_c2_in_type: "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_tuple ` Type (tmod_combine Tmod1 Tmod2)"
    then have c1_c2_eq: "c1 = c2"
      unfolding subtype_tuple_def
      by blast
    have "\<exclamdown>c1 \<in> Type Tmod1 \<or> \<exclamdown>c1 \<in> Type Tmod2"
      using c1_c2_in_type tmod_combine_type
      unfolding subtype_tuple_def
      by blast
    then show ?thesis
      unfolding subtype_def
      using c1_c2_eq subtype_rel.reflexivity
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper proper ` (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
    then have "(c1, c2) \<in> (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
      unfolding subtype_conv_def
      by auto
    then have "(c1, c2) \<in> (Inh Tmod1 \<union> Inh Tmod2)\<^sup>+"
      by (simp add: tmod_combine_def)
    then have "(c1, c2) \<in> (Inh Tmod1)\<^sup>+ \<union> (Inh Tmod2)\<^sup>+"
      by (simp add: combine_classes_distinct tmod1_correct tmod2_correct)
    then show ?thesis
    proof (elim UnE)
      assume "(c1, c2) \<in> (Inh Tmod1)\<^sup>+"
      then have "\<exclamdown>c1 \<sqsubseteq>[Tmod1] \<exclamdown>c2"
      proof (induct)
        case (base y)
        then show ?case
          unfolding subtype_def
          by (fact subtype_rel.generalization_of_inheritance_proper)
      next
        case (step y z)
        then show ?case
          unfolding subtype_def
          using subtype_rel.generalization_of_inheritance_proper subtype_relation_transitive_alt tmod1_correct transE
          by metis
      qed
      then show ?thesis
        by simp
    next
      assume "(c1, c2) \<in> (Inh Tmod2)\<^sup>+"
      then have "\<exclamdown>c1 \<sqsubseteq>[Tmod2] \<exclamdown>c2"
      proof (induct)
        case (base y)
        then show ?case
          unfolding subtype_def
          by (fact subtype_rel.generalization_of_inheritance_proper)
      next
        case (step y z)
        then show ?case
          unfolding subtype_def
          using subtype_rel.generalization_of_inheritance_proper subtype_relation_transitive_alt tmod2_correct transE
          by metis
      qed
      then show ?thesis
        by simp
    qed
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine Tmod1 Tmod2)"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper nullable ` (Inh (tmod_combine Tmod1 Tmod2))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then show "\<And>A B. A \<subseteq> B"
    using no_tmod1_extend no_tmod2_extend
    by blast
qed (simp_all add: assms)

lemma tmod_combine_full_distinct_correct[intro]:
  assumes tmod1_correct: "type_model Tmod1"
  assumes tmod2_correct: "type_model Tmod2"
  assumes combine_types_distinct: "(Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1) \<inter> (Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2) = {}"
  assumes combine_constants_distinct: "Constant Tmod1 \<inter> Constant Tmod2 = {}"
  assumes property_namespace_restriction_tmod12: "\<And>x y. x \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1 \<Longrightarrow> y \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2 \<Longrightarrow> \<not>id_in_ns x (Identifier y)"
  assumes property_namespace_restriction_tmod21: "\<And>x y. x \<in> Class Tmod2 \<union> Enum Tmod2 \<union> UserDataType Tmod2 \<Longrightarrow> y \<in> Class Tmod1 \<union> Enum Tmod1 \<union> UserDataType Tmod1 \<Longrightarrow> \<not>id_in_ns x (Identifier y)"
  shows "type_model (tmod_combine Tmod1 Tmod2)"
proof (intro tmod_combine_distinct_correct)
  show "Class Tmod1 \<inter> Class Tmod2 = {}"
    using combine_types_distinct
    by blast
next
  show "Enum Tmod1 \<inter> Enum Tmod2 = {}"
    using combine_types_distinct
    by blast
next
  show "UserDataType Tmod1 \<inter> UserDataType Tmod2 = {}"
    using combine_types_distinct
    by blast
next
  fix c
  assume "c \<in> Class Tmod1"
  then show "c \<notin> Enum Tmod2 \<and> c \<notin> UserDataType Tmod2"
    using combine_types_distinct
    by blast
next
  fix c
  assume "c \<in> Class Tmod2"
  then show "c \<notin> Enum Tmod1 \<and> c \<notin> UserDataType Tmod1"
    using combine_types_distinct
    by blast
next
  fix e
  assume "e \<in> Enum Tmod1"
  then show "e \<notin> Class Tmod2 \<and> e \<notin> UserDataType Tmod2"
    using combine_types_distinct
    by blast
next
  fix e
  assume "e \<in> Enum Tmod2"
  then show "e \<notin> Class Tmod1 \<and> e \<notin> UserDataType Tmod1"
    using combine_types_distinct
    by blast
qed (simp_all add: assms)

end