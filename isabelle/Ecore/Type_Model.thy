theory Type_Model
  imports 
    Main
    HOL.Transitive_Closure
    Model_Namespace
    Multiplicity
begin

section "Type definitions"

datatype ('nt) TypeDef = boolean | integer | real | string | nullable "'nt Id" | proper "'nt Id" | enumtype "'nt Id" | userdatatype "'nt Id" | bagof "'nt TypeDef" | setof "'nt TypeDef" | seqof "'nt TypeDef" | ordof "'nt TypeDef" | invalid
datatype ('nt) PropertyDef = abstract "'nt Id" | containment "'nt Id \<times> 'nt" | defaultValue "'nt Id \<times> 'nt" "'nt Id" | identity "'nt Id" "('nt Id \<times> 'nt) set" | keyset "'nt Id \<times> 'nt" "('nt Id \<times> 'nt) set" | opposite "'nt Id \<times> 'nt" "'nt Id \<times> 'nt" | readonly "'nt Id \<times> 'nt"

notation
  nullable ("(\<questiondown>_)" [1000] 1000) and
  proper ("(\<exclamdown>_)" [1000] 1000)

fun contained_type :: "('nt) TypeDef \<Rightarrow> ('nt) TypeDef" where
  "contained_type (bagof x) = x" |
  "contained_type (setof x) = x" |
  "contained_type (seqof x) = x" |
  "contained_type (ordof x) = x" |
  "contained_type x = x"

fun uncontainer :: "('nt) TypeDef \<Rightarrow> ('nt) TypeDef" where
  "uncontainer (bagof x) = uncontainer x" |
  "uncontainer (setof x) = uncontainer x" |
  "uncontainer (seqof x) = uncontainer x" |
  "uncontainer (ordof x) = uncontainer x" |
  "uncontainer x = x"

lemma uncontainer_no_container[simp]: "uncontainer x \<noteq> bagof y \<and> uncontainer x \<noteq> setof y \<and> uncontainer x \<noteq> seqof y \<and> uncontainer x \<noteq> ordof y"
  by (induction x) simp_all



section "Type model tuple definition"

record ('nt) type_model =
  Class :: "'nt Id set"
  Enum :: "'nt Id set"
  UserDataType :: "'nt Id set"
  Field :: "('nt Id \<times> 'nt) set"
  FieldSig :: "('nt Id \<times> 'nt) \<Rightarrow> ('nt TypeDef) \<times> (multiplicity)"
  EnumValue :: "('nt Id \<times> 'nt) set"
  Inh :: "'nt Id rel"
  Prop :: "'nt PropertyDef set"
  Constant :: "'nt Id set"
  ConstType :: "'nt Id \<Rightarrow> ('nt TypeDef)"

inductive type_model_eq :: "('nt) type_model \<Rightarrow> ('nt) type_model \<Rightarrow> bool"
  for Tmod1 Tmod2 :: "('nt) type_model"
  where
    rule_equality: "\<lbrakk> Class Tmod1 = Class Tmod2; 
                      Enum Tmod1 = Enum Tmod2; 
                      UserDataType Tmod1 = UserDataType Tmod2; 
                      Field Tmod1 = Field Tmod2; 
                      FieldSig Tmod1 = FieldSig Tmod2; 
                      EnumValue Tmod1 = EnumValue Tmod2; 
                      Inh Tmod1 = Inh Tmod2; 
                      Prop Tmod1 = Prop Tmod2; 
                      Constant Tmod1 = Constant Tmod2; 
                      ConstType Tmod1 = ConstType Tmod2 \<rbrakk> \<Longrightarrow> type_model_eq Tmod1 Tmod2"



section "Definition of sets of valid types"


subsection "DataTypes"

definition DataType :: "'nt TypeDef set" where
  "DataType = {boolean, integer, real, string}"

lemma datatype_finite[simp]: "finite DataType"
  by (simp add: DataType_def)

lemma datatype_member[simp]: "x \<in> DataType \<Longrightarrow> x = boolean \<or> x = integer \<or> x = real \<or> x = string"
  by (simp add: DataType_def)

lemma datatype_contains_no_proper_classes[simp]: "proper x \<notin> DataType"
  using datatype_member by blast

lemma datatype_contains_no_nullable_classes[simp]: "nullable x \<notin> DataType"
  using datatype_member by blast

lemma datatype_contains_no_enumtypes[simp]: "enumtype x \<notin> DataType"
  using datatype_member by blast

lemma datatype_contains_no_userdatatypes[simp]: "userdatatype x \<notin> DataType"
  using datatype_member by blast

lemma datatype_contains_no_bags[simp]: "bagof x \<notin> DataType"
  using datatype_member by blast

lemma datatype_contains_no_sets[simp]: "setof x \<notin> DataType"
  using datatype_member by blast

lemma datatype_contains_no_seqs[simp]: "seqof x \<notin> DataType"
  using datatype_member by blast

lemma datatype_contains_no_ords[simp]: "ordof x \<notin> DataType"
  using datatype_member by blast

lemma datatype_not_invalid[simp]: "invalid \<notin> DataType"
  using datatype_member
  by blast

subsection "Classes"

subsubsection "Proper class types"

inductive_set ProperClassType :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_proper_classes: "c \<in> Class Tmod \<Longrightarrow> \<exclamdown>c \<in> ProperClassType Tmod"

lemma proper_class_type_member[simp]: "x \<in> ProperClassType Tmod \<Longrightarrow> \<exists>y. x = \<exclamdown>y"
  using ProperClassType.cases by blast

lemma proper_class_type_contains_no_booleans[simp]: "boolean \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_contains_no_integers[simp]: "integer \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_contains_no_reals[simp]: "real \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_contains_no_strings[simp]: "string \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_contains_no_nullable_classes[simp]: "\<questiondown>x \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_contains_no_enumtypes[simp]: "enumtype x \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_contains_no_userdatatypes[simp]: "userdatatype x \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_contains_no_bags[simp]: "bagof x \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_contains_no_sets[simp]: "setof x \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_contains_no_seqs[simp]: "seqof x \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_contains_no_ords[simp]: "ordof x \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_not_invalid[simp]: "invalid \<notin> ProperClassType Tmod"
  using proper_class_type_member by blast

lemma proper_class_type_truncate_eq: "ProperClassType Tmod = ProperClassType (truncate Tmod)"
proof
  show "ProperClassType Tmod \<subseteq> ProperClassType (truncate Tmod)"
  proof
    fix x
    assume "x \<in> ProperClassType Tmod"
    then show "x \<in> ProperClassType (truncate Tmod)"
    proof (induct)
      case (rule_proper_classes c)
      then show ?case
        unfolding truncate_def
        by (simp add: ProperClassType.rule_proper_classes)
    qed
  qed
next
  show "ProperClassType (truncate Tmod) \<subseteq> ProperClassType Tmod"
  proof
    fix x
    assume "x \<in> ProperClassType (truncate Tmod)"
    then show "x \<in> ProperClassType Tmod"
    proof (induct)
      case (rule_proper_classes c)
      then have "c \<in> Class Tmod"
        unfolding truncate_def
        by simp
      then show ?case
        by (fact ProperClassType.rule_proper_classes)
    qed
  qed
qed

lemma proper_class_type_datatype_intersect[simp]: "ProperClassType Tmod \<inter> DataType = {}"
  using datatype_member by fastforce

subsubsection "Nullable class types"

inductive_set NullableClassType :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_nullable_classes: "c \<in> Class Tmod \<Longrightarrow> \<questiondown>c \<in> NullableClassType Tmod"

lemma nullable_class_type_member[simp]: "x \<in> NullableClassType Tmod \<Longrightarrow> \<exists>y. x = \<questiondown>y"
  using NullableClassType.cases by blast

lemma nullable_class_type_contains_no_booleans[simp]: "boolean \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_contains_no_integers[simp]: "integer \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_contains_no_reals[simp]: "real \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_contains_no_strings[simp]: "string \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_contains_no_proper_classes[simp]: "\<exclamdown>x \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_contains_no_enumtypes[simp]: "enumtype x \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_contains_no_userdatatypes[simp]: "userdatatype x \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_contains_no_bags[simp]: "bagof x \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_contains_no_sets[simp]: "setof x \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_contains_no_seqs[simp]: "seqof x \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_contains_no_ords[simp]: "ordof x \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_not_invalid[simp]: "invalid \<notin> NullableClassType Tmod"
  using nullable_class_type_member by blast

lemma nullable_class_type_truncate_eq: "NullableClassType Tmod = NullableClassType (truncate Tmod)"
proof
  show "NullableClassType Tmod \<subseteq> NullableClassType (truncate Tmod)"
  proof
    fix x
    assume "x \<in> NullableClassType Tmod"
    then show "x \<in> NullableClassType (truncate Tmod)"
    proof (induct)
      case (rule_nullable_classes c)
      then show ?case
        unfolding truncate_def
        by (simp add: NullableClassType.rule_nullable_classes)
    qed
  qed
next
  show "NullableClassType (truncate Tmod) \<subseteq> NullableClassType Tmod"
  proof
    fix x
    assume "x \<in> NullableClassType (truncate Tmod)"
    then show "x \<in> NullableClassType Tmod"
    proof (induct)
      case (rule_nullable_classes c)
      then have "c \<in> Class Tmod"
        unfolding truncate_def
        by simp
      then show ?case
        by (fact NullableClassType.rule_nullable_classes)
    qed
  qed
qed

lemma nullable_class_type_datatype_intersect[simp]: "NullableClassType Tmod \<inter> DataType = {}"
  using datatype_member by fastforce

lemma nullable_class_type_proper_class_type_intersect[simp]: "NullableClassType Tmod1 \<inter> ProperClassType Tmod2 = {}"
  using proper_class_type_member by fastforce

subsubsection "Class types"

definition ClassType :: "'nt type_model \<Rightarrow> 'nt TypeDef set" where
  "ClassType Tmod = ProperClassType Tmod \<union> NullableClassType Tmod"

lemma class_type_member[simp]: "x \<in> ClassType Tmod \<Longrightarrow> \<exists>y. x = \<questiondown>y \<or> x = \<exclamdown>y"
  using ClassType_def nullable_class_type_member proper_class_type_member by fastforce

lemma class_type_contains_no_booleans[simp]: "boolean \<notin> ClassType Tmod"
  using class_type_member by blast

lemma class_type_contains_no_integers[simp]: "integer \<notin> ClassType Tmod"
  using class_type_member by blast

lemma class_type_contains_no_reals[simp]: "real \<notin> ClassType Tmod"
  using class_type_member by blast

lemma class_type_contains_no_strings[simp]: "string \<notin> ClassType Tmod"
  using class_type_member by blast

lemma class_type_contains_no_enumtypes[simp]: "enumtype x \<notin> ClassType Tmod"
  using class_type_member by blast

lemma class_type_contains_no_userdatatypes[simp]: "userdatatype x \<notin> ClassType Tmod"
  using class_type_member by blast

lemma class_type_contains_no_bags[simp]: "bagof x \<notin> ClassType Tmod"
  using class_type_member by blast

lemma class_type_contains_no_sets[simp]: "setof x \<notin> ClassType Tmod"
  using class_type_member by blast

lemma class_type_contains_no_seqs[simp]: "seqof x \<notin> ClassType Tmod"
  using class_type_member by blast

lemma class_type_contains_no_ords[simp]: "ordof x \<notin> ClassType Tmod"
  using class_type_member by blast

lemma class_type_not_invalid[simp]: "invalid \<notin> ClassType Tmod"
  using class_type_member by blast

lemma class_type_truncate_eq: "ClassType Tmod = ClassType (truncate Tmod)"
  unfolding ClassType_def
  using nullable_class_type_truncate_eq proper_class_type_truncate_eq
  by blast

lemma class_type_datatype_intersect[simp]: "ClassType Tmod \<inter> DataType = {}"
  using datatype_member by fastforce

lemma class_type_proper_class_type_intersect[simp]: "ClassType Tmod \<inter> ProperClassType Tmod = ProperClassType Tmod"
  by (simp add: ClassType_def Int_absorb1)

lemma class_type_nullable_class_type_intersect[simp]: "ClassType Tmod \<inter> NullableClassType Tmod = NullableClassType Tmod"
  by (simp add: ClassType_def Int_absorb1)

lemma class_type_subset_proper_class_type[simp]: "ProperClassType Tmod \<subseteq> ClassType Tmod"
  by (simp add: ClassType_def)

lemma class_type_subset_nullable_class_type[simp]: "NullableClassType Tmod \<subseteq> ClassType Tmod"
  by (simp add: ClassType_def)

lemma class_type_not_member[intro]: "\<lbrakk> x \<notin> ProperClassType Tmod; x \<notin> NullableClassType Tmod \<rbrakk> \<Longrightarrow> x \<notin> ClassType Tmod"
  by (simp add: ClassType_def)


subsection "Enums"

inductive_set EnumType :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_enum_types: "e \<in> Enum Tmod \<Longrightarrow> enumtype e \<in> EnumType Tmod"

lemma enum_type_member[simp]: "x \<in> EnumType Tmod \<Longrightarrow> \<exists>y. x = enumtype y"
  using EnumType.cases by blast

lemma enum_type_contains_no_booleans[simp]: "boolean \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_contains_no_integers[simp]: "integer \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_contains_no_reals[simp]: "real \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_contains_no_strings[simp]: "string \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_contains_no_proper_classes[simp]: "\<exclamdown>x \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_contains_no_nullable_classes[simp]: "\<questiondown>x \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_contains_no_userdatatypes[simp]: "userdatatype x \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_contains_no_bags[simp]: "bagof x \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_contains_no_sets[simp]: "setof x \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_contains_no_seqs[simp]: "seqof x \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_contains_no_ords[simp]: "ordof x \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_not_invalid[simp]: "invalid \<notin> EnumType Tmod"
  using enum_type_member by blast

lemma enum_type_truncate_eq: "EnumType Tmod = EnumType (truncate Tmod)"
proof
  show "EnumType Tmod \<subseteq> EnumType (truncate Tmod)"
  proof
    fix x
    assume "x \<in> EnumType Tmod"
    then show "x \<in> EnumType (truncate Tmod)"
    proof (induct)
      case (rule_enum_types e)
      then show ?case
        unfolding truncate_def
        by (simp add: EnumType.rule_enum_types)
    qed
  qed
next
  show "EnumType (truncate Tmod) \<subseteq> EnumType Tmod"
  proof
    fix x
    assume "x \<in> EnumType (truncate Tmod)"
    then show "x \<in> EnumType Tmod"
    proof (induct)
      case (rule_enum_types e)
      then have "e \<in> Enum Tmod"
        unfolding truncate_def
        by simp
      then show ?case
        by (fact EnumType.rule_enum_types)
    qed
  qed
qed

lemma enum_type_datatype_intersect[simp]: "EnumType Tmod \<inter> DataType = {}"
  using datatype_member by fastforce

lemma enum_type_proper_class_type_intersect[simp]: "EnumType Tmod1 \<inter> ProperClassType Tmod2 = {}"
  using proper_class_type_member by fastforce

lemma enum_type_nullable_class_type_intersect[simp]: "EnumType Tmod1 \<inter> NullableClassType Tmod2 = {}"
  using nullable_class_type_member by fastforce

lemma enum_type_class_type_intersect[simp]: "EnumType Tmod1 \<inter> ClassType Tmod2 = {}"
  using class_type_member by fastforce


subsection "User Data Types"

inductive_set UserDataTypeType :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_userdatatypes: "u \<in> UserDataType Tmod \<Longrightarrow> userdatatype u \<in> UserDataTypeType Tmod"

lemma userdatatype_type_member[simp]: "x \<in> UserDataTypeType Tmod \<Longrightarrow> \<exists>y. x = userdatatype y"
  using UserDataTypeType.cases by blast

lemma userdatatype_type_contains_no_booleans[simp]: "boolean \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_contains_no_integers[simp]: "integer \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_contains_no_reals[simp]: "real \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_contains_no_strings[simp]: "string \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_contains_no_proper_classes[simp]: "\<exclamdown>x \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_contains_no_nullable_classes[simp]: "\<questiondown>x \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_contains_no_enumtypes[simp]: "enumtype x \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_contains_no_bags[simp]: "bagof x \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_contains_no_sets[simp]: "setof x \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_contains_no_seqs[simp]: "seqof x \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_contains_no_ords[simp]: "ordof x \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_not_invalid[simp]: "invalid \<notin> UserDataTypeType Tmod"
  using userdatatype_type_member by blast

lemma userdatatype_type_truncate_eq: "UserDataTypeType Tmod = UserDataTypeType (truncate Tmod)"
proof
  show "UserDataTypeType Tmod \<subseteq> UserDataTypeType (truncate Tmod)"
  proof
    fix x
    assume "x \<in> UserDataTypeType Tmod"
    then show "x \<in> UserDataTypeType (truncate Tmod)"
    proof (induct)
      case (rule_userdatatypes u)
      then show ?case
        unfolding truncate_def
        by (simp add: UserDataTypeType.rule_userdatatypes)
    qed
  qed
next
  show "UserDataTypeType (truncate Tmod) \<subseteq> UserDataTypeType Tmod"
  proof
    fix x
    assume "x \<in> UserDataTypeType (truncate Tmod)"
    then show "x \<in> UserDataTypeType Tmod"
    proof (induct)
      case (rule_userdatatypes u)
      then have "u \<in> UserDataType Tmod"
        unfolding truncate_def
        by simp
      then show ?case
        by (fact UserDataTypeType.rule_userdatatypes)
    qed
  qed
qed

lemma userdatatype_type_datatype_intersect[simp]: "UserDataTypeType Tmod \<inter> DataType = {}"
  using datatype_member by fastforce

lemma userdatatype_type_proper_class_type_intersect[simp]: "UserDataTypeType Tmod1 \<inter> ProperClassType Tmod2 = {}"
  using proper_class_type_member by fastforce

lemma userdatatype_type_nullable_class_type_intersect[simp]: "UserDataTypeType Tmod1 \<inter> NullableClassType Tmod2 = {}"
  using nullable_class_type_member by fastforce

lemma userdatatype_type_class_type_intersect[simp]: "UserDataTypeType Tmod1 \<inter> ClassType Tmod2 = {}"
  using class_type_member by fastforce

lemma userdatatype_type_enum_type_intersect[simp]: "UserDataTypeType Tmod1 \<inter> EnumType Tmod2 = {}"
  using enum_type_member by fastforce


subsection "Non container types"

definition NonContainerType :: "'nt type_model \<Rightarrow> 'nt TypeDef set" where
  "NonContainerType Tmod = DataType \<union> ClassType Tmod \<union> EnumType Tmod \<union> UserDataTypeType Tmod"

lemma non_container_type_member[simp]: "x \<in> NonContainerType Tmod \<Longrightarrow> x = boolean \<or> x = integer \<or> x = real \<or> x = string \<or> (\<exists>y. x = \<exclamdown>y) \<or> (\<exists>y. x = \<questiondown>y) \<or> (\<exists>y. x = enumtype y) \<or> (\<exists>y. x = userdatatype y)"
  using NonContainerType_def datatype_member class_type_member enum_type_member userdatatype_type_member by fastforce

lemma non_container_type_contains_no_bags[simp]: "bagof x \<notin> NonContainerType Tmod"
  using non_container_type_member by blast

lemma non_container_type_contains_no_sets[simp]: "setof x \<notin> NonContainerType Tmod"
  using non_container_type_member by blast

lemma non_container_type_contains_no_seqs[simp]: "seqof x \<notin> NonContainerType Tmod"
  using non_container_type_member by blast

lemma non_container_type_contains_no_ords[simp]: "ordof x \<notin> NonContainerType Tmod"
  using non_container_type_member by blast

lemma non_container_type_not_invalid[simp]: "invalid \<notin> NonContainerType Tmod"
  using non_container_type_member by blast

lemma non_container_type_truncate_eq: "NonContainerType Tmod = NonContainerType (truncate Tmod)"
  unfolding NonContainerType_def
  using class_type_truncate_eq enum_type_truncate_eq userdatatype_type_truncate_eq
  by blast

lemma non_container_type_datatype_intersect[simp]: "NonContainerType Tmod \<inter> DataType = DataType"
  using NonContainerType_def by blast

lemma non_container_type_class_type_intersect[simp]: "NonContainerType Tmod \<inter> ClassType Tmod = ClassType Tmod"
  using NonContainerType_def by blast

lemma non_container_type_proper_class_type_intersect[simp]: "NonContainerType Tmod \<inter> ProperClassType Tmod = ProperClassType Tmod"
  using NonContainerType_def ClassType_def by blast

lemma non_container_type_nullable_class_type_intersect[simp]: "NonContainerType Tmod \<inter> NullableClassType Tmod = NullableClassType Tmod"
  using NonContainerType_def ClassType_def by blast

lemma non_container_type_enum_type_intersect[simp]: "NonContainerType Tmod \<inter> EnumType Tmod = EnumType Tmod"
  using NonContainerType_def by blast

lemma non_container_type_userdatatype_type_intersect[simp]: "NonContainerType Tmod \<inter> UserDataTypeType Tmod = UserDataTypeType Tmod"
  using NonContainerType_def by blast

lemma non_container_type_subset_datatype[simp]: "DataType \<subseteq> NonContainerType Tmod"
  by (simp add: inf.absorb_iff2)

lemma non_container_type_subset_class_type[simp]: "ClassType Tmod \<subseteq> NonContainerType Tmod"
  by (simp add: inf.absorb_iff2)

lemma non_container_type_subset_proper_class_type[simp]: "ProperClassType Tmod \<subseteq> NonContainerType Tmod"
  by (simp add: inf.absorb_iff2)

lemma non_container_type_subset_nullable_class_type[simp]: "NullableClassType Tmod \<subseteq> NonContainerType Tmod"
  by (simp add: inf.absorb_iff2)

lemma non_container_type_subset_enum_type[simp]: "EnumType Tmod \<subseteq> NonContainerType Tmod"
  by (simp add: inf.absorb_iff2)

lemma non_container_type_subset_userdatatype_type[simp]: "UserDataTypeType Tmod \<subseteq> NonContainerType Tmod"
  by (simp add: inf.absorb_iff2)

lemma non_container_type_not_member[intro]: "\<lbrakk> x \<notin> DataType; x \<notin> ClassType Tmod; x \<notin> EnumType Tmod; x \<notin> UserDataTypeType Tmod \<rbrakk> \<Longrightarrow> x \<notin> NonContainerType Tmod"
  by (simp add: NonContainerType_def)

lemma non_container_type_uncontainer_identity: "x \<in> NonContainerType Tmod \<Longrightarrow> uncontainer x = x"
  by (induct x) (simp_all)

subsection "Container types"

inductive_set ContainerType :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_bagof_type: "t \<in> NonContainerType Tmod \<Longrightarrow> bagof t \<in> ContainerType Tmod" |
    rule_setof_type: "t \<in> NonContainerType Tmod \<Longrightarrow> setof t \<in> ContainerType Tmod" |
    rule_seqof_type: "t \<in> NonContainerType Tmod \<Longrightarrow> seqof t \<in> ContainerType Tmod" |
    rule_ordof_type: "t \<in> NonContainerType Tmod \<Longrightarrow> ordof t \<in> ContainerType Tmod" |
    rule_bagof_container: "t \<in> ContainerType Tmod \<Longrightarrow> bagof t \<in> ContainerType Tmod" |
    rule_setof_container: "t \<in> ContainerType Tmod \<Longrightarrow> setof t \<in> ContainerType Tmod" |
    rule_seqof_container: "t \<in> ContainerType Tmod \<Longrightarrow> seqof t \<in> ContainerType Tmod" |
    rule_ordof_container: "t \<in> ContainerType Tmod \<Longrightarrow> ordof t \<in> ContainerType Tmod"

lemma container_type_member[simp]: "x \<in> ContainerType Tmod \<Longrightarrow> (\<exists>y. x = bagof y) \<or> (\<exists>y. x = setof y) \<or> (\<exists>y. x = seqof y) \<or> (\<exists>y. x = ordof y)"
  using ContainerType.simps by blast

lemma container_type_contains_no_booleans[simp]: "boolean \<notin> ContainerType Tmod"
  using container_type_member by blast

lemma container_type_contains_no_integers[simp]: "integer \<notin> ContainerType Tmod"
  using container_type_member by blast

lemma container_type_contains_no_reals[simp]: "real \<notin> ContainerType Tmod"
  using container_type_member by blast

lemma container_type_contains_no_strings[simp]: "string \<notin> ContainerType Tmod"
  using container_type_member by blast

lemma container_type_contains_no_proper_classes[simp]: "\<exclamdown>x \<notin> ContainerType Tmod"
  using container_type_member by blast

lemma container_type_contains_no_nullable_classes[simp]: "\<questiondown>x \<notin> ContainerType Tmod"
  using container_type_member by blast

lemma container_type_contains_no_enumtypes[simp]: "enumtype x \<notin> ContainerType Tmod"
  using container_type_member by blast

lemma container_type_contains_no_userdatatypes[simp]: "userdatatype x \<notin> ContainerType Tmod"
  using container_type_member by blast

lemma container_type_not_invalid[simp]: "invalid \<notin> ContainerType Tmod"
  using container_type_member by blast

lemma container_type_truncate_eq: "ContainerType Tmod = ContainerType (truncate Tmod)"
proof
  show "ContainerType Tmod \<subseteq> ContainerType (truncate Tmod)"
  proof
    fix x
    assume "x \<in> ContainerType Tmod"
    then show "x \<in> ContainerType (truncate Tmod)"
    proof (induct)
      case (rule_bagof_type t)
      then show ?case
        using ContainerType.rule_bagof_type non_container_type_truncate_eq
        by blast
    next
      case (rule_setof_type t)
      then show ?case
        using ContainerType.rule_setof_type non_container_type_truncate_eq
        by blast
    next
      case (rule_seqof_type t)
      then show ?case
        using ContainerType.rule_seqof_type non_container_type_truncate_eq
        by blast
    next
      case (rule_ordof_type t)
      then show ?case
        using ContainerType.rule_ordof_type non_container_type_truncate_eq
        by blast
    next
      case (rule_bagof_container t)
      then show ?case
        by (simp add: ContainerType.rule_bagof_container)
    next
      case (rule_setof_container t)
      then show ?case
        by (simp add: ContainerType.rule_setof_container)
    next
      case (rule_seqof_container t)
      then show ?case
        by (simp add: ContainerType.rule_seqof_container)
    next
      case (rule_ordof_container t)
      then show ?case
        by (simp add: ContainerType.rule_ordof_container)
    qed
  qed
next
  show "ContainerType (truncate Tmod) \<subseteq> ContainerType Tmod"
  proof
    fix x
    assume "x \<in> ContainerType (truncate Tmod)"
    then show "x \<in> ContainerType Tmod"
    proof (induct)
      case (rule_bagof_type t)
      then show ?case
        using ContainerType.rule_bagof_type non_container_type_truncate_eq
        by blast
    next
      case (rule_setof_type t)
      then show ?case
        using ContainerType.rule_setof_type non_container_type_truncate_eq
        by blast
    next
      case (rule_seqof_type t)
      then show ?case
        using ContainerType.rule_seqof_type non_container_type_truncate_eq
        by blast
    next
      case (rule_ordof_type t)
      then show ?case
        using ContainerType.rule_ordof_type non_container_type_truncate_eq
        by blast
    next
      case (rule_bagof_container t)
      then show ?case
        by (simp add: ContainerType.rule_bagof_container)
    next
      case (rule_setof_container t)
      then show ?case
        by (simp add: ContainerType.rule_setof_container)
    next
      case (rule_seqof_container t)
      then show ?case
        by (simp add: ContainerType.rule_seqof_container)
    next
      case (rule_ordof_container t)
      then show ?case
        by (simp add: ContainerType.rule_ordof_container)
    qed
  qed
qed

lemma container_type_datatype_intersect[simp]: "ContainerType Tmod \<inter> DataType = {}"
  using datatype_member by fastforce

lemma container_type_proper_class_type_intersect[simp]: "ContainerType Tmod1 \<inter> ProperClassType Tmod2 = {}"
  using proper_class_type_member by fastforce

lemma container_type_nullable_class_type_intersect[simp]: "ContainerType Tmod1 \<inter> NullableClassType Tmod2 = {}"
  using nullable_class_type_member by fastforce

lemma container_type_class_type_intersect[simp]: "ContainerType Tmod1 \<inter> ClassType Tmod2 = {}"
  using class_type_member by fastforce

lemma container_type_enum_type_intersect[simp]: "ContainerType Tmod1 \<inter> EnumType Tmod2 = {}"
  using enum_type_member by fastforce

lemma container_type_userdatatype_type_intersect[simp]: "ContainerType Tmod1 \<inter> UserDataTypeType Tmod2 = {}"
  using userdatatype_type_member by fastforce

lemma container_type_non_container_type_intersect[simp]: "ContainerType Tmod1 \<inter> NonContainerType Tmod2 = {}"
  using non_container_type_member by fastforce

lemma container_type_never_contains_invalid_type[simp]: "x \<in> ContainerType Tmod \<Longrightarrow> uncontainer x \<noteq> invalid"
proof-
  assume "x \<in> ContainerType Tmod"
  then show "uncontainer x \<noteq> invalid"
  proof (induct)
    case (rule_bagof_type t)
    then show ?case
      using non_container_type_uncontainer_identity
      by fastforce
  next
    case (rule_setof_type t)
    then show ?case
      using non_container_type_uncontainer_identity
      by fastforce
  next
    case (rule_seqof_type t)
    then show ?case
      using non_container_type_uncontainer_identity
      by fastforce
  next
    case (rule_ordof_type t)
    then show ?case
      using non_container_type_uncontainer_identity
      by fastforce
  qed (simp_all)
qed


subsection "Types"

definition Type :: "'nt type_model \<Rightarrow> 'nt TypeDef set" where
  "Type Tmod = NonContainerType Tmod \<union> ContainerType Tmod" 

lemma type_not_invalid[simp]: "invalid \<notin> Type Tmod"
  unfolding Type_def
  by simp

lemma type_truncate_eq: "Type Tmod = Type (truncate Tmod)"
  unfolding Type_def
  using container_type_truncate_eq non_container_type_truncate_eq
  by blast

lemma type_datatype_intersect[simp]: "Type Tmod \<inter> DataType = DataType"
  using Type_def NonContainerType_def by blast

lemma type_class_type_intersect[simp]: "Type Tmod \<inter> ClassType Tmod = ClassType Tmod"
  using Type_def NonContainerType_def by blast

lemma type_proper_class_type_intersect[simp]: "Type Tmod \<inter> ProperClassType Tmod = ProperClassType Tmod"
  using Type_def NonContainerType_def ClassType_def by blast

lemma type_nullable_class_type_intersect[simp]: "Type Tmod \<inter> NullableClassType Tmod = NullableClassType Tmod"
  using Type_def NonContainerType_def ClassType_def by blast

lemma type_enum_type_intersect[simp]: "Type Tmod \<inter> EnumType Tmod = EnumType Tmod"
  using Type_def NonContainerType_def by blast

lemma type_userdatatype_type_intersect[simp]: "Type Tmod \<inter> UserDataTypeType Tmod = UserDataTypeType Tmod"
  using Type_def NonContainerType_def by blast

lemma type_container_type_intersect[simp]: "Type Tmod \<inter> ContainerType Tmod = ContainerType Tmod"
  using Type_def by blast

lemma type_subset_datatype[simp]: "DataType \<subseteq> Type Tmod"
  by (simp add: inf.absorb_iff2)

lemma type_subset_class_type[simp]: "ClassType Tmod \<subseteq> Type Tmod"
  by (simp add: inf.absorb_iff2)

lemma type_subset_proper_class_type[simp]: "ProperClassType Tmod \<subseteq> Type Tmod"
  by (simp add: inf.absorb_iff2)

lemma type_subset_nullable_class_type[simp]: "NullableClassType Tmod \<subseteq> Type Tmod"
  by (simp add: inf.absorb_iff2)

lemma type_subset_enum_type[simp]: "EnumType Tmod \<subseteq> Type Tmod"
  by (simp add: inf.absorb_iff2)

lemma type_subset_userdatatype_type[simp]: "UserDataTypeType Tmod \<subseteq> Type Tmod"
  by (simp add: inf.absorb_iff2)

lemma type_subset_container_type[simp]: "ContainerType Tmod \<subseteq> Type Tmod"
  by (simp add: inf.absorb_iff2)

lemma type_not_member[intro]: "\<lbrakk> x \<notin> NonContainerType Tmod; x \<notin> ContainerType Tmod \<rbrakk> \<Longrightarrow> x \<notin> Type Tmod"
  by (simp add: Type_def)

lemma types_have_bagof_types[simp]: "t \<in> Type Tmod \<Longrightarrow> bagof t \<in> Type Tmod"
  using ContainerType.rule_bagof_container ContainerType.rule_bagof_type Type_def by blast

lemma types_have_setof_types[simp]: "t \<in> Type Tmod \<Longrightarrow> setof t \<in> Type Tmod"
  using ContainerType.rule_setof_container ContainerType.rule_setof_type Type_def by blast

lemma types_have_seqof_types[simp]: "t \<in> Type Tmod \<Longrightarrow> seqof t \<in> Type Tmod"
  using ContainerType.rule_seqof_container ContainerType.rule_seqof_type Type_def by blast

lemma types_have_ordof_types[simp]: "t \<in> Type Tmod \<Longrightarrow> ordof t \<in> Type Tmod"
  using ContainerType.rule_ordof_container ContainerType.rule_ordof_type Type_def by blast



section "Definition of strict subsets of type"


subsection "Attributes"

inductive_set AttrType :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_datatypes: "t \<in> DataType \<Longrightarrow> t \<in> AttrType Tmod" |
    rule_enum_types: "t \<in> EnumType Tmod \<Longrightarrow> t \<in> AttrType Tmod" |
    rule_userdatatypes: "t \<in> UserDataTypeType Tmod \<Longrightarrow> t \<in> AttrType Tmod" |
    rule_bagof_attributes: "t \<in> AttrType Tmod \<Longrightarrow> bagof t \<in> AttrType Tmod" |
    rule_setof_attributes: "t \<in> AttrType Tmod \<Longrightarrow> setof t \<in> AttrType Tmod" |
    rule_seqof_attributes: "t \<in> AttrType Tmod \<Longrightarrow> seqof t \<in> AttrType Tmod" |
    rule_ordof_attributes: "t \<in> AttrType Tmod \<Longrightarrow> ordof t \<in> AttrType Tmod"

lemma attribute_type_not_invalid[simp]: "invalid \<notin> AttrType Tmod"
proof-
  have "\<And>x. x \<in> AttrType Tmod \<Longrightarrow> x \<noteq> invalid"
  proof-
    fix x
    assume "x \<in> AttrType Tmod"
    then show "x \<noteq> invalid"
    proof (induct)
      case (rule_datatypes t)
      then show ?case
        by fastforce
    next
      case (rule_enum_types t)
      then show ?case
        by fastforce
    next
      case (rule_userdatatypes t)
      then show ?case
        by fastforce
    qed (simp_all)
  qed
  then show ?thesis
    by blast
qed

lemma attribute_type_truncate_eq: "AttrType Tmod = AttrType (truncate Tmod)"
proof
  show "AttrType Tmod \<subseteq> AttrType (truncate Tmod)"
  proof
    fix x
    assume "x \<in> AttrType Tmod"
    then show "x \<in> AttrType (truncate Tmod)"
    proof (induct)
      case (rule_datatypes t)
      then show ?case
        by (fact AttrType.rule_datatypes)
    next
      case (rule_enum_types t)
      then show ?case
        using AttrType.rule_enum_types enum_type_truncate_eq
        by blast
    next
      case (rule_userdatatypes t)
      then show ?case
        using AttrType.rule_userdatatypes userdatatype_type_truncate_eq
        by blast
    next
      case (rule_bagof_attributes t)
      then show ?case
        by (simp add: AttrType.rule_bagof_attributes)
    next
      case (rule_setof_attributes t)
      then show ?case
        by (simp add: AttrType.rule_setof_attributes)
    next
      case (rule_seqof_attributes t)
      then show ?case
        by (simp add: AttrType.rule_seqof_attributes)
    next
      case (rule_ordof_attributes t)
      then show ?case
        by (simp add: AttrType.rule_ordof_attributes)
    qed
  qed
next
  show "AttrType (truncate Tmod) \<subseteq> AttrType Tmod"
  proof
    fix x
    assume "x \<in> AttrType (truncate Tmod)"
    then show "x \<in> AttrType Tmod"
    proof (induct)
      case (rule_datatypes t)
      then show ?case
        by (fact AttrType.rule_datatypes)
    next
      case (rule_enum_types t)
      then show ?case
        using AttrType.rule_enum_types enum_type_truncate_eq
        by blast
    next
      case (rule_userdatatypes t)
      then show ?case
        using AttrType.rule_userdatatypes userdatatype_type_truncate_eq
        by blast
    next
      case (rule_bagof_attributes t)
      then show ?case
        by (simp add: AttrType.rule_bagof_attributes)
    next
      case (rule_setof_attributes t)
      then show ?case
        by (simp add: AttrType.rule_setof_attributes)
    next
      case (rule_seqof_attributes t)
      then show ?case
        by (simp add: AttrType.rule_seqof_attributes)
    next
      case (rule_ordof_attributes t)
      then show ?case
        by (simp add: AttrType.rule_ordof_attributes)
    qed
  qed
qed

lemma datatypes_are_attributes[simp]: "DataType \<subseteq> AttrType Tmod"
  by (simp add: AttrType.rule_datatypes subset_iff)

lemma classes_are_not_attributes[simp]: "x \<in> AttrType Tmod \<Longrightarrow> \<forall>y. x \<noteq> \<exclamdown>y \<and> x \<noteq> \<questiondown>y"
  by (induct rule: AttrType.induct) auto

lemma proper_classes_are_not_attributes_alt[simp]: "\<exclamdown>x \<notin> AttrType Tmod"
  using classes_are_not_attributes by blast

lemma nullable_classes_are_not_attributes_alt[simp]: "\<questiondown>x \<notin> AttrType Tmod"
  using classes_are_not_attributes by blast

lemma enums_are_attributes[simp]: "EnumType Tmod \<subseteq> AttrType Tmod"
  by (simp add: AttrType.rule_enum_types subset_iff)

lemma userdatatypes_are_attributes[simp]: "UserDataTypeType Tmod \<subseteq> AttrType Tmod"
  by (simp add: AttrType.rule_userdatatypes subset_iff)

lemma attribute_bags_have_attribute_types: "x \<in> AttrType Tmod \<Longrightarrow> x = bagof y \<Longrightarrow> y \<in> AttrType Tmod"
  by (induct rule: AttrType.induct) simp_all

lemma attribute_sets_have_attribute_types: "x \<in> AttrType Tmod \<Longrightarrow> x = setof y \<Longrightarrow> y \<in> AttrType Tmod"
  by (induct rule: AttrType.induct) simp_all

lemma attribute_seqs_have_attribute_types: "x \<in> AttrType Tmod \<Longrightarrow> x = seqof y \<Longrightarrow> y \<in> AttrType Tmod"
  by (induct rule: AttrType.induct) simp_all

lemma attribute_ords_have_attribute_types: "x \<in> AttrType Tmod \<Longrightarrow> x = ordof y \<Longrightarrow> y \<in> AttrType Tmod"
  by (induct rule: AttrType.induct) simp_all

lemma attribute_containers_have_no_classdefs[simp]: "x \<in> AttrType Tmod \<Longrightarrow> \<forall>y. uncontainer x \<noteq> \<exclamdown>y \<and> uncontainer x \<noteq> \<questiondown>y"
proof (induction x)
  case boolean
  then show ?case by simp
next
  case integer
  then show ?case by simp
next
  case real
  then show ?case by simp
next
  case string
  then show ?case by simp
next
  case (nullable x)
  then show ?case by simp
next
  case (proper x)
  then show ?case by simp
next
  case (enumtype x)
  then show ?case by simp
next
  case (userdatatype x)
  then show ?case by simp
next
  case (bagof x)
  then show ?case
    using attribute_bags_have_attribute_types by auto
next
  case (setof x)
  then show ?case
    using attribute_sets_have_attribute_types by auto
next
  case (seqof x)
  then show ?case
    using attribute_seqs_have_attribute_types by auto
next
  case (ordof x)
  then show ?case
    using attribute_ords_have_attribute_types by auto
next
  case invalid
  then show ?case by simp
qed

lemma attributes_are_types[simp]: "AttrType Tmod \<subseteq> Type Tmod"
proof
  fix x assume "x \<in> AttrType Tmod" then show "x \<in> Type Tmod"
  proof (induct)
  case (rule_datatypes t)
    then show ?case
      using type_subset_datatype by blast
  next
  case (rule_enum_types t)
    then show ?case
      using type_subset_enum_type by blast
  next
  case (rule_userdatatypes t)
    then show ?case
      using type_subset_userdatatype_type by blast
  next
    case (rule_bagof_attributes t)
    then show ?case
      by simp
  next
    case (rule_setof_attributes t)
    then show ?case
      by simp
  next
    case (rule_seqof_attributes t)
    then show ?case
      by simp
  next
    case (rule_ordof_attributes t)
    then show ?case
      by simp
  qed
qed


subsection "Relations"

definition RelType :: "'nt type_model \<Rightarrow> 'nt TypeDef set" where
  "RelType Tmod = Type Tmod - AttrType Tmod"

lemma rel_type_not_invalid[simp]: "invalid \<notin> RelType Tmod"
  unfolding RelType_def
  by simp

lemma attributes_and_relations_are_distinct[simp]: "RelType Tmod \<inter> AttrType Tmod = {}"
  by (simp add: RelType_def inf_commute)

lemma relations_are_types[simp]: "RelType Tmod \<subseteq> Type Tmod"
  using RelType_def by auto

lemma relations_and_attributes_eq_types[simp]: "RelType Tmod \<union> AttrType Tmod = Type Tmod"
  by (simp add: RelType_def Un_absorb1 sup_commute)

lemma relation_member[simp,intro]: "\<lbrakk> t \<in> Type Tmod; t \<notin> AttrType Tmod \<rbrakk> \<Longrightarrow> t \<in> RelType Tmod"
  by (simp add: RelType_def)

lemma proper_classes_are_relations[simp]: "ProperClassType Tmod \<subseteq> RelType Tmod"
proof
  fix x assume "x \<in> ProperClassType Tmod" then show "x \<in> RelType Tmod"
  proof (intro relation_member)
    assume "x \<in> ProperClassType Tmod" then show "x \<in> Type Tmod"
      using type_subset_proper_class_type by blast
    assume "x \<in> ProperClassType Tmod" then show "x \<notin> AttrType Tmod"
    proof (induct rule: ProperClassType.induct)
      case (rule_proper_classes c)
      then show ?case
        by simp
    qed
  qed
qed

lemma nullable_classes_are_relations[simp]: "NullableClassType Tmod \<subseteq> RelType Tmod"
proof
  fix x assume "x \<in> NullableClassType Tmod" then show "x \<in> RelType Tmod"
  proof (intro relation_member)
    assume "x \<in> NullableClassType Tmod" then show "x \<in> Type Tmod"
      using type_subset_nullable_class_type by blast
    assume "x \<in> NullableClassType Tmod" then show "x \<notin> AttrType Tmod"
    proof (induct rule: NullableClassType.induct)
      case (rule_nullable_classes c)
      then show ?case
        by simp
    qed
  qed
qed

lemma classes_are_relations[simp]: "ClassType Tmod \<subseteq> RelType Tmod"
  by (simp add: ClassType_def)

inductive_set RelType_altdef :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_class_types: "t \<in> ClassType Tmod \<Longrightarrow> t \<in> RelType_altdef Tmod" |
    rule_bagof_relations: "t \<in> RelType_altdef Tmod \<Longrightarrow> bagof t \<in> RelType_altdef Tmod" |
    rule_setof_relations: "t \<in> RelType_altdef Tmod \<Longrightarrow> setof t \<in> RelType_altdef Tmod" |
    rule_seqof_relations: "t \<in> RelType_altdef Tmod \<Longrightarrow> seqof t \<in> RelType_altdef Tmod" |
    rule_ordof_relations: "t \<in> RelType_altdef Tmod \<Longrightarrow> ordof t \<in> RelType_altdef Tmod"

lemma rel_type_alt_def_not_invalid[simp]: "invalid \<notin> RelType_altdef Tmod"
proof-
  have "\<And>x. x \<in> RelType_altdef Tmod \<Longrightarrow> x \<noteq> invalid"
  proof-
    fix x
    assume "x \<in> RelType_altdef Tmod"
    then show "x \<noteq> invalid"
    proof (induct)
      case (rule_class_types t)
      then show ?case
        by fastforce
    qed (simp_all)
  qed
  then show ?thesis
    by blast
qed

lemma rel_type_alt_def_truncate_eq: "RelType_altdef Tmod = RelType_altdef (truncate Tmod)"
proof
  show "RelType_altdef Tmod \<subseteq> RelType_altdef (truncate Tmod)"
  proof
    fix x
    assume "x \<in> RelType_altdef Tmod"
    then show "x \<in> RelType_altdef (truncate Tmod)"
    proof (induct)
      case (rule_class_types t)
      then show ?case
        using RelType_altdef.rule_class_types class_type_truncate_eq
        by blast
    next
      case (rule_bagof_relations t)
      then show ?case
        by (simp add: RelType_altdef.rule_bagof_relations)
    next
      case (rule_setof_relations t)
      then show ?case
        by (simp add: RelType_altdef.rule_setof_relations)
    next
      case (rule_seqof_relations t)
      then show ?case
        by (simp add: RelType_altdef.rule_seqof_relations)
    next
      case (rule_ordof_relations t)
      then show ?case
        by (simp add: RelType_altdef.rule_ordof_relations)
    qed
  qed
next
  show "RelType_altdef (truncate Tmod) \<subseteq> RelType_altdef Tmod"
  proof
    fix x
    assume "x \<in> RelType_altdef (truncate Tmod)"
    then show "x \<in> RelType_altdef Tmod"
    proof (induct)
      case (rule_class_types t)
      then show ?case
        using RelType_altdef.rule_class_types class_type_truncate_eq
        by blast
    next
      case (rule_bagof_relations t)
      then show ?case
        by (simp add: RelType_altdef.rule_bagof_relations)
    next
      case (rule_setof_relations t)
      then show ?case
        by (simp add: RelType_altdef.rule_setof_relations)
    next
      case (rule_seqof_relations t)
      then show ?case
        by (simp add: RelType_altdef.rule_seqof_relations)
    next
      case (rule_ordof_relations t)
      then show ?case
        by (simp add: RelType_altdef.rule_ordof_relations)
    qed
  qed
qed

lemma classes_are_relations_alt[simp]: "ClassType Tmod \<subseteq> RelType_altdef Tmod"
  by (simp add: RelType_altdef.rule_class_types subsetI)

lemma proper_classes_are_relations_alt[simp]: "ProperClassType Tmod \<subseteq> RelType_altdef Tmod"
  using ClassType_def classes_are_relations_alt by fastforce

lemma nullable_classes_are_relations_alt[simp]: "NullableClassType Tmod \<subseteq> RelType_altdef Tmod"
  using ClassType_def classes_are_relations_alt by fastforce

lemma booleans_are_not_relations_alt[simp]: "x \<in> RelType_altdef Tmod \<Longrightarrow> x \<noteq> boolean"
  by (induct rule: RelType_altdef.induct) auto

lemma integers_are_not_relations_alt[simp]: "x \<in> RelType_altdef Tmod \<Longrightarrow> x \<noteq> integer"
  by (induct rule: RelType_altdef.induct) auto

lemma reals_are_not_relations_alt[simp]: "x \<in> RelType_altdef Tmod \<Longrightarrow> x \<noteq> real"
  by (induct rule: RelType_altdef.induct) auto

lemma strings_are_not_relations_alt[simp]: "x \<in> RelType_altdef Tmod \<Longrightarrow> x \<noteq> string"
  by (induct rule: RelType_altdef.induct) auto

lemma enums_are_not_relations_alt[simp]: "x \<in> RelType_altdef Tmod \<Longrightarrow> \<forall>y. x \<noteq> enumtype y"
  by (induct rule: RelType_altdef.induct) auto

lemma userdatatypes_are_not_relations_alt[simp]: "x \<in> RelType_altdef Tmod \<Longrightarrow> \<forall>y. x \<noteq> userdatatype y"
  by (induct rule: RelType_altdef.induct) auto

lemma relation_bags_have_relation_types_alt: "x \<in> RelType_altdef Tmod \<Longrightarrow> x = bagof y \<Longrightarrow> y \<in> RelType_altdef Tmod"
  by (induct rule: RelType_altdef.induct) simp_all

lemma relation_sets_have_relation_types_alt: "x \<in> RelType_altdef Tmod \<Longrightarrow> x = setof y \<Longrightarrow> y \<in> RelType_altdef Tmod"
  by (induct rule: RelType_altdef.induct) simp_all

lemma relation_seqs_have_relation_types_alt: "x \<in> RelType_altdef Tmod \<Longrightarrow> x = seqof y \<Longrightarrow> y \<in> RelType_altdef Tmod"
  by (induct rule: RelType_altdef.induct) simp_all

lemma relation_ords_have_relation_types_alt: "x \<in> RelType_altdef Tmod \<Longrightarrow> x = ordof y \<Longrightarrow> y \<in> RelType_altdef Tmod"
  by (induct rule: RelType_altdef.induct) simp_all

lemma relation_containers_have_only_classdefs[simp]: "x \<in> RelType_altdef Tmod \<Longrightarrow> \<exists>y. uncontainer x = \<exclamdown>y \<or> uncontainer x = \<questiondown>y"
proof (induction x)
  case boolean
  then show ?case
    using booleans_are_not_relations_alt by blast
next
  case integer
  then show ?case
    using integers_are_not_relations_alt by blast
next
  case real
  then show ?case
    using reals_are_not_relations_alt by blast
next
  case string
  then show ?case
    using strings_are_not_relations_alt by blast
next
  case (nullable x)
  then show ?case
    by simp
next
  case (proper x)
  then show ?case
    by simp
next
  case (enumtype x)
  then show ?case
    using enums_are_not_relations_alt by blast
next
  case (userdatatype x)
  then show ?case
    using userdatatypes_are_not_relations_alt by blast
next
  case (bagof x)
  then show ?case
    by (simp add: relation_bags_have_relation_types_alt)
next
  case (setof x)
  then show ?case
    by (simp add: relation_sets_have_relation_types_alt)
next
  case (seqof x)
  then show ?case
    by (simp add: relation_seqs_have_relation_types_alt)
next
  case (ordof x)
  then show ?case
    by (simp add: relation_ords_have_relation_types_alt)
next
  case invalid
  then show ?case
    by simp
qed

lemma relations_and_attributes_are_types_alt[simp]: "RelType_altdef Tmod \<union> AttrType Tmod = Type Tmod"
proof
  show "RelType_altdef Tmod \<union> AttrType Tmod \<subseteq> Type Tmod"
  proof
    fix x assume "x \<in> RelType_altdef Tmod \<union> AttrType Tmod" then have "x \<in> RelType_altdef Tmod \<or> x \<in> AttrType Tmod"
      by simp
    then show "x \<in> Type Tmod"
    proof
      show "x \<in> RelType_altdef Tmod \<Longrightarrow> x \<in> Type Tmod"
      proof (induct rule: RelType_altdef.induct)
        case (rule_class_types t)
        then show ?case
          by (simp add: NonContainerType_def Type_def)
      next
        case (rule_bagof_relations t)
        then show ?case
          by simp
      next
        case (rule_setof_relations t)
        then show ?case
          by simp
      next
        case (rule_seqof_relations t)
        then show ?case
          by simp
      next
        case (rule_ordof_relations t)
        then show ?case
          by simp
      qed
      show "x \<in> AttrType Tmod \<Longrightarrow> x \<in> Type Tmod"
        using attributes_are_types by blast
    qed
  qed
  show "Type Tmod \<subseteq> RelType_altdef Tmod \<union> AttrType Tmod"
  proof
    fix x assume "x \<in> Type Tmod" then have "x \<in> RelType_altdef Tmod \<or> x \<in> AttrType Tmod"
      unfolding Type_def NonContainerType_def
    proof (elim UnE)
      show "x \<in> DataType \<Longrightarrow> x \<in> RelType_altdef Tmod \<or> x \<in> AttrType Tmod"
        by (simp add: AttrType.rule_datatypes)
      show "x \<in> ClassType Tmod \<Longrightarrow> x \<in> RelType_altdef Tmod \<or> x \<in> AttrType Tmod"
        by (simp add: RelType_altdef.rule_class_types)
      show "x \<in> EnumType Tmod \<Longrightarrow> x \<in> RelType_altdef Tmod \<or> x \<in> AttrType Tmod"
        by (simp add: AttrType.rule_enum_types)
      show "x \<in> UserDataTypeType Tmod \<Longrightarrow> x \<in> RelType_altdef Tmod \<or> x \<in> AttrType Tmod"
        by (simp add: AttrType.rule_userdatatypes)
      show "x \<in> ContainerType Tmod \<Longrightarrow> x \<in> RelType_altdef Tmod \<or> x \<in> AttrType Tmod"
      proof (induct rule: ContainerType.induct)
        case (rule_bagof_type t)
        then show ?case
          using AttrType.rule_datatypes AttrType.rule_enum_types AttrType.rule_bagof_attributes AttrType.rule_userdatatypes RelType_altdef.rule_class_types RelType_altdef.rule_bagof_relations non_container_type_not_member by blast
      next
        case (rule_setof_type t)
        then show ?case
          using AttrType.rule_datatypes AttrType.rule_enum_types AttrType.rule_setof_attributes AttrType.rule_userdatatypes RelType_altdef.rule_class_types RelType_altdef.rule_setof_relations non_container_type_not_member by blast
      next
        case (rule_seqof_type t)
        then show ?case
          using AttrType.rule_datatypes AttrType.rule_enum_types AttrType.rule_seqof_attributes AttrType.rule_userdatatypes RelType_altdef.rule_class_types RelType_altdef.rule_seqof_relations non_container_type_not_member by blast
      next
        case (rule_ordof_type t)
        then show ?case
          using AttrType.rule_datatypes AttrType.rule_enum_types AttrType.rule_ordof_attributes AttrType.rule_userdatatypes RelType_altdef.rule_class_types RelType_altdef.rule_ordof_relations non_container_type_not_member by blast
      next
        case (rule_bagof_container t)
        then show ?case
          using AttrType.rule_bagof_attributes RelType_altdef.rule_bagof_relations by blast
      next
        case (rule_setof_container t)
        then show ?case
          using AttrType.rule_setof_attributes RelType_altdef.rule_setof_relations by blast
      next
        case (rule_seqof_container t)
        then show ?case
          using AttrType.rule_seqof_attributes RelType_altdef.rule_seqof_relations by blast
      next
        case (rule_ordof_container t)
        then show ?case
          using AttrType.rule_ordof_attributes RelType_altdef.rule_ordof_relations by blast
      qed
    qed
    then show "x \<in> RelType_altdef Tmod \<union> AttrType Tmod"
      by blast
  qed
qed

lemma relations_altdef_rel_not_in_attr[simp]: "x \<in> RelType_altdef Tmod1 \<Longrightarrow> x \<notin> AttrType Tmod2"
proof (induct rule: RelType_altdef.induct)
  case (rule_class_types t)
  then show ?case
    using class_type_member classes_are_not_attributes by blast
next
  case (rule_bagof_relations t)
  then show ?case
    using attribute_containers_have_no_classdefs relation_containers_have_only_classdefs by fastforce
next
  case (rule_setof_relations t)
  then show ?case
    using attribute_containers_have_no_classdefs relation_containers_have_only_classdefs by fastforce
next
  case (rule_seqof_relations t)
  then show ?case                                                        
    using attribute_containers_have_no_classdefs relation_containers_have_only_classdefs by fastforce
next
  case (rule_ordof_relations t)
  then show ?case
    using attribute_containers_have_no_classdefs relation_containers_have_only_classdefs by fastforce
qed

lemma attributes_and_relations_are_distinct_alt[simp]: "RelType_altdef Tmod1 \<inter> AttrType Tmod2 = {}"
  by auto

lemma relations_altdef_eq: "RelType Tmod = RelType_altdef Tmod"
  using attributes_and_relations_are_distinct relations_and_attributes_eq_types attributes_and_relations_are_distinct_alt relations_and_attributes_are_types_alt
  by blast

lemma member_relations[simp]: "x \<in> RelType Tmod \<longleftrightarrow> x \<in> RelType_altdef Tmod"
  by (simp add: relations_altdef_eq)

lemma rel_type_truncate_eq: "RelType Tmod = RelType (truncate Tmod)"
  using rel_type_alt_def_truncate_eq relations_altdef_eq
  by blast


subsection "Container type sets"

inductive_set BagContainerType :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_bagof_all_type: "t \<in> Type Tmod \<Longrightarrow> bagof t \<in> BagContainerType Tmod"

lemma bag_types_are_container_types[simp]: "BagContainerType Tmod \<subseteq> ContainerType Tmod"
proof
  fix x assume "x \<in> BagContainerType Tmod" then show "x \<in> ContainerType Tmod"
  proof(induct)
    case (rule_bagof_all_type t)
    then show ?case unfolding Type_def
      using ContainerType.rule_bagof_container ContainerType.rule_bagof_type by blast
  qed
qed

lemma bag_types_are_types[simp]: "BagContainerType Tmod \<subseteq> Type Tmod"
  using bag_types_are_container_types type_subset_container_type by blast

lemma bag_types_typedef[simp]: "t \<in> BagContainerType Tmod \<Longrightarrow> \<exists>c. t = bagof c"
  using BagContainerType.cases by blast

lemma bag_container_type_not_invalid[simp]: "invalid \<notin> BagContainerType Tmod"
  using bag_types_typedef
  by blast

lemma bag_container_type_truncate_eq: "BagContainerType Tmod = BagContainerType (truncate Tmod)"
proof
  show "BagContainerType Tmod \<subseteq> BagContainerType (truncate Tmod)"
  proof
    fix x
    assume "x \<in> BagContainerType Tmod"
    then show "x \<in> BagContainerType (truncate Tmod)"
    proof (induct)
      case (rule_bagof_all_type t)
      then show ?case
        using BagContainerType.rule_bagof_all_type type_truncate_eq
        by blast
    qed
  qed
next
  show "BagContainerType (truncate Tmod) \<subseteq> BagContainerType Tmod"
  proof
    fix x
    assume "x \<in> BagContainerType (truncate Tmod)"
    then show "x \<in> BagContainerType Tmod"
    proof (induct)
      case (rule_bagof_all_type t)
      then show ?case
        using BagContainerType.rule_bagof_all_type type_truncate_eq
        by blast
    qed
  qed
qed

inductive_set SetContainerType :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_setof_all_type: "t \<in> Type Tmod \<Longrightarrow> setof t \<in> SetContainerType Tmod"

lemma set_types_are_container_types[simp]: "SetContainerType Tmod \<subseteq> ContainerType Tmod"
proof
  fix x assume "x \<in> SetContainerType Tmod" then show "x \<in> ContainerType Tmod"
  proof(induct)
    case (rule_setof_all_type t)
    then show ?case unfolding Type_def
      using ContainerType.rule_setof_container ContainerType.rule_setof_type by blast
  qed
qed

lemma set_types_are_types[simp]: "SetContainerType Tmod \<subseteq> Type Tmod"
  using set_types_are_container_types type_subset_container_type by blast

lemma set_types_typedef[simp]: "t \<in> SetContainerType Tmod \<Longrightarrow> \<exists>c. t = setof c"
  using SetContainerType.cases by blast

lemma set_container_type_not_invalid[simp]: "invalid \<notin> SetContainerType Tmod"
  using set_types_typedef
  by blast

lemma set_container_type_truncate_eq: "SetContainerType Tmod = SetContainerType (truncate Tmod)"
proof
  show "SetContainerType Tmod \<subseteq> SetContainerType (truncate Tmod)"
  proof
    fix x
    assume "x \<in> SetContainerType Tmod"
    then show "x \<in> SetContainerType (truncate Tmod)"
    proof (induct)
      case (rule_setof_all_type t)
      then show ?case
        using SetContainerType.rule_setof_all_type type_truncate_eq
        by blast
    qed
  qed
next
  show "SetContainerType (truncate Tmod) \<subseteq> SetContainerType Tmod"
  proof
    fix x
    assume "x \<in> SetContainerType (truncate Tmod)"
    then show "x \<in> SetContainerType Tmod"
    proof (induct)
      case (rule_setof_all_type t)
      then show ?case
        using SetContainerType.rule_setof_all_type type_truncate_eq
        by blast
    qed
  qed
qed

lemma set_types_bag_types_distinct[simp]: "x \<in> SetContainerType Tmod \<Longrightarrow> x \<notin> BagContainerType Tmod"
proof-
  fix x assume "x \<in> SetContainerType Tmod" then show "x \<notin> BagContainerType Tmod"
    using bag_types_typedef by (induct) auto
qed

lemma set_types_bag_types_distinct_intersect: "SetContainerType Tmod \<inter> BagContainerType Tmod = {}"
  by auto

inductive_set SeqContainerType :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_seqof_all_type: "t \<in> Type Tmod \<Longrightarrow> seqof t \<in> SeqContainerType Tmod"

lemma seq_types_are_container_types[simp]: "SeqContainerType Tmod \<subseteq> ContainerType Tmod"
proof
  fix x assume "x \<in> SeqContainerType Tmod" then show "x \<in> ContainerType Tmod"
  proof(induct)
    case (rule_seqof_all_type t)
    then show ?case unfolding Type_def
      using ContainerType.rule_seqof_container ContainerType.rule_seqof_type by blast
  qed
qed

lemma seq_types_are_types[simp]: "SeqContainerType Tmod \<subseteq> Type Tmod"
  using seq_types_are_container_types type_subset_container_type by blast

lemma seq_types_typedef[simp]: "t \<in> SeqContainerType Tmod \<Longrightarrow> \<exists>c. t = seqof c"
  using SeqContainerType.cases by blast

lemma seq_container_type_not_invalid[simp]: "invalid \<notin> SeqContainerType Tmod"
  using seq_types_typedef
  by blast

lemma seq_container_type_truncate_eq: "SeqContainerType Tmod = SeqContainerType (truncate Tmod)"
proof
  show "SeqContainerType Tmod \<subseteq> SeqContainerType (truncate Tmod)"
  proof
    fix x
    assume "x \<in> SeqContainerType Tmod"
    then show "x \<in> SeqContainerType (truncate Tmod)"
    proof (induct)
      case (rule_seqof_all_type t)
      then show ?case
        using SeqContainerType.rule_seqof_all_type type_truncate_eq
        by blast
    qed
  qed
next
  show "SeqContainerType (truncate Tmod) \<subseteq> SeqContainerType Tmod"
  proof
    fix x
    assume "x \<in> SeqContainerType (truncate Tmod)"
    then show "x \<in> SeqContainerType Tmod"
    proof (induct)
      case (rule_seqof_all_type t)
      then show ?case
        using SeqContainerType.rule_seqof_all_type type_truncate_eq
        by blast
    qed
  qed
qed

lemma seq_types_bag_types_distinct[simp]: "x \<in> SeqContainerType Tmod \<Longrightarrow> x \<notin> BagContainerType Tmod"
proof-
  fix x assume "x \<in> SeqContainerType Tmod" then show "x \<notin> BagContainerType Tmod"
    using bag_types_typedef by (induct) auto
qed

lemma seq_types_bag_types_distinct_intersect: "SeqContainerType Tmod \<inter> BagContainerType Tmod = {}"
  by auto

lemma seq_types_set_types_distinct[simp]: "x \<in> SeqContainerType Tmod \<Longrightarrow> x \<notin> SetContainerType Tmod"
proof-
  fix x assume "x \<in> SeqContainerType Tmod" then show "x \<notin> SetContainerType Tmod"
    using set_types_typedef by (induct) auto
qed

lemma seq_types_set_types_distinct_intersect: "SeqContainerType Tmod \<inter> SetContainerType Tmod = {}"
  by auto

inductive_set OrdContainerType :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_ordof_all_type: "t \<in> Type Tmod \<Longrightarrow> ordof t \<in> OrdContainerType Tmod"

lemma ord_types_are_container_types[simp]: "OrdContainerType Tmod \<subseteq> ContainerType Tmod"
proof
  fix x assume "x \<in> OrdContainerType Tmod" then show "x \<in> ContainerType Tmod"
  proof(induct)
    case (rule_ordof_all_type t)
    then show ?case unfolding Type_def
      using ContainerType.rule_ordof_container ContainerType.rule_ordof_type by blast
  qed
qed

lemma ord_types_are_types[simp]: "OrdContainerType Tmod \<subseteq> Type Tmod"
  using ord_types_are_container_types type_subset_container_type by blast

lemma ord_types_typedef[simp]: "t \<in> OrdContainerType Tmod \<Longrightarrow> \<exists>c. t = ordof c"
  using OrdContainerType.cases by blast

lemma ord_container_type_not_invalid[simp]: "invalid \<notin> OrdContainerType Tmod"
  using ord_types_typedef
  by blast

lemma ord_container_type_truncate_eq: "OrdContainerType Tmod = OrdContainerType (truncate Tmod)"
proof
  show "OrdContainerType Tmod \<subseteq> OrdContainerType (truncate Tmod)"
  proof
    fix x
    assume "x \<in> OrdContainerType Tmod"
    then show "x \<in> OrdContainerType (truncate Tmod)"
    proof (induct)
      case (rule_ordof_all_type t)
      then show ?case
        using OrdContainerType.rule_ordof_all_type type_truncate_eq
        by blast
    qed
  qed
next
  show "OrdContainerType (truncate Tmod) \<subseteq> OrdContainerType Tmod"
  proof
    fix x
    assume "x \<in> OrdContainerType (truncate Tmod)"
    then show "x \<in> OrdContainerType Tmod"
    proof (induct)
      case (rule_ordof_all_type t)
      then show ?case
        using OrdContainerType.rule_ordof_all_type type_truncate_eq
        by blast
    qed
  qed
qed

lemma ord_types_bag_types_distinct[simp]: "x \<in> OrdContainerType Tmod \<Longrightarrow> x \<notin> BagContainerType Tmod"
proof-
  fix x assume "x \<in> OrdContainerType Tmod" then show "x \<notin> BagContainerType Tmod"
    using bag_types_typedef by (induct) auto
qed

lemma ord_types_bag_types_distinct_intersect: "OrdContainerType Tmod \<inter> BagContainerType Tmod = {}"
  by auto

lemma ord_types_set_types_distinct[simp]: "x \<in> OrdContainerType Tmod \<Longrightarrow> x \<notin> SetContainerType Tmod"
proof-
  fix x assume "x \<in> OrdContainerType Tmod" then show "x \<notin> SetContainerType Tmod"
    using set_types_typedef by (induct) auto
qed

lemma ord_types_set_types_distinct_intersect: "OrdContainerType Tmod \<inter> SetContainerType Tmod = {}"
  by auto

lemma ord_types_seq_types_distinct[simp]: "x \<in> OrdContainerType Tmod \<Longrightarrow> x \<notin> SeqContainerType Tmod"
proof-
  fix x assume "x \<in> OrdContainerType Tmod" then show "x \<notin> SeqContainerType Tmod"
    using seq_types_typedef by (induct) auto
qed

lemma ord_types_seq_types_distinct_intersect: "OrdContainerType Tmod \<inter> SeqContainerType Tmod = {}"
  by auto

lemma all_container_types_in_container_type[simp]: "BagContainerType Tmod \<union> SetContainerType Tmod \<union> SeqContainerType Tmod \<union> OrdContainerType Tmod = ContainerType Tmod"
proof
  show "BagContainerType Tmod \<union> SetContainerType Tmod \<union> SeqContainerType Tmod \<union> OrdContainerType Tmod \<subseteq> ContainerType Tmod"
  proof
    fix x assume "x \<in> BagContainerType Tmod \<union> SetContainerType Tmod \<union> SeqContainerType Tmod \<union> OrdContainerType Tmod"
    then have "x \<in> BagContainerType Tmod \<or> x \<in> SetContainerType Tmod \<or> x \<in> SeqContainerType Tmod \<or> x \<in> OrdContainerType Tmod"
      by simp
    then show "x \<in> ContainerType Tmod"
    proof (elim disjE)
      show "x \<in> BagContainerType Tmod \<Longrightarrow> x \<in> ContainerType Tmod"
      proof (induct rule: BagContainerType.induct)
        case (rule_bagof_all_type t)
        then show ?case
          using ContainerType.rule_bagof_container ContainerType.rule_bagof_type type_not_member by blast
      qed
      show "x \<in> SetContainerType Tmod \<Longrightarrow> x \<in> ContainerType Tmod"
      proof (induct rule: SetContainerType.induct)
        case (rule_setof_all_type t)
        then show ?case
          using ContainerType.rule_setof_container ContainerType.rule_setof_type type_not_member by blast
      qed
      show "x \<in> SeqContainerType Tmod \<Longrightarrow> x \<in> ContainerType Tmod"
      proof (induct rule: SeqContainerType.induct)
        case (rule_seqof_all_type t)
        then show ?case
          using ContainerType.rule_seqof_container ContainerType.rule_seqof_type type_not_member by blast
      qed
      show "x \<in> OrdContainerType Tmod \<Longrightarrow> x \<in> ContainerType Tmod"
      proof (induct rule: OrdContainerType.induct)
        case (rule_ordof_all_type t)
        then show ?case
          using ContainerType.rule_ordof_container ContainerType.rule_ordof_type type_not_member by blast
      qed
    qed
  qed
  show "ContainerType Tmod \<subseteq> BagContainerType Tmod \<union> SetContainerType Tmod \<union> SeqContainerType Tmod \<union> OrdContainerType Tmod"
  proof
    fix x assume "x \<in> ContainerType Tmod" then show "x \<in> BagContainerType Tmod \<union> SetContainerType Tmod \<union> SeqContainerType Tmod \<union> OrdContainerType Tmod"
    proof (induct rule: ContainerType.induct)
      case (rule_bagof_type t)
      then show ?case
        by (simp add: BagContainerType.rule_bagof_all_type Type_def)
    next
      case (rule_setof_type t)
      then show ?case
        by (simp add: SetContainerType.rule_setof_all_type Type_def)
    next
      case (rule_seqof_type t)
      then show ?case
        by (simp add: SeqContainerType.rule_seqof_all_type Type_def)
    next
      case (rule_ordof_type t)
      then show ?case
        by (simp add: OrdContainerType.rule_ordof_all_type Type_def)
    next
      case (rule_bagof_container t)
      then show ?case
        by (simp add: BagContainerType.rule_bagof_all_type Type_def)
    next
      case (rule_setof_container t)
      then show ?case
        by (simp add: SetContainerType.rule_setof_all_type Type_def)
    next
      case (rule_seqof_container t)
      then show ?case
        by (simp add: SeqContainerType.rule_seqof_all_type Type_def)
    next
      case (rule_ordof_container t)
      then show ?case
        by (simp add: OrdContainerType.rule_ordof_all_type Type_def)
    qed
  qed
qed

definition NonUniqueContainerType :: "'nt type_model \<Rightarrow> 'nt TypeDef set" where
  "NonUniqueContainerType Tmod = BagContainerType Tmod \<union> SeqContainerType Tmod"

lemma bag_types_are_non_unique_containers[simp]: "BagContainerType Tmod \<subseteq> NonUniqueContainerType Tmod"
  by (simp add: NonUniqueContainerType_def)

lemma seq_types_are_non_unique_containers[simp]: "SeqContainerType Tmod \<subseteq> NonUniqueContainerType Tmod"
  by (simp add: NonUniqueContainerType_def)

lemma non_unique_container_types_are_types[simp]: "NonUniqueContainerType Tmod \<subseteq> Type Tmod"
  by (simp add: NonUniqueContainerType_def)

lemma non_unique_container_types_types_intersect[simp]: "NonUniqueContainerType Tmod \<inter> Type Tmod = NonUniqueContainerType Tmod"
  by (simp add: inf.absorb1)

lemma non_unique_container_type_not_invalid[simp]: "invalid \<notin> NonUniqueContainerType Tmod"
  by (simp add: NonUniqueContainerType_def)

lemma non_unique_container_type_truncate_eq: "NonUniqueContainerType Tmod = NonUniqueContainerType (truncate Tmod)"
  unfolding NonUniqueContainerType_def
  using bag_container_type_truncate_eq seq_container_type_truncate_eq
  by blast

definition UniqueContainerType :: "'nt type_model \<Rightarrow> 'nt TypeDef set" where
  "UniqueContainerType Tmod = SetContainerType Tmod \<union> OrdContainerType Tmod"

lemma set_types_are_unique_containers[simp]: "SetContainerType Tmod \<subseteq> UniqueContainerType Tmod"
  by (simp add: UniqueContainerType_def)

lemma ord_types_are_unique_containers[simp]: "OrdContainerType Tmod \<subseteq> UniqueContainerType Tmod"
  by (simp add: UniqueContainerType_def)

lemma unique_container_types_are_types[simp]: "UniqueContainerType Tmod \<subseteq> Type Tmod"
  by (simp add: UniqueContainerType_def)

lemma unique_container_types_types_intersect[simp]: "UniqueContainerType Tmod \<inter> Type Tmod = UniqueContainerType Tmod"
  by (simp add: inf.absorb1)

lemma unique_container_type_not_invalid[simp]: "invalid \<notin> UniqueContainerType Tmod"
  by (simp add: UniqueContainerType_def)

lemma unique_container_type_truncate_eq: "UniqueContainerType Tmod = UniqueContainerType (truncate Tmod)"
  unfolding UniqueContainerType_def
  using ord_container_type_truncate_eq set_container_type_truncate_eq
  by blast

lemma unique_and_non_unique_containers_distinct[simp]: "x \<in> NonUniqueContainerType Tmod \<Longrightarrow> x \<notin> UniqueContainerType Tmod"
  using NonUniqueContainerType_def UniqueContainerType_def seq_types_set_types_distinct set_types_bag_types_distinct by fastforce

lemma unique_and_non_unique_containers_intersection[simp]: "NonUniqueContainerType Tmod \<inter> UniqueContainerType Tmod = {}"
  by auto

lemma unique_and_non_unique_containers_union[simp]: "NonUniqueContainerType Tmod \<union> UniqueContainerType Tmod = ContainerType Tmod"
  using NonUniqueContainerType_def UniqueContainerType_def all_container_types_in_container_type by blast

definition UnorderedContainerType :: "'nt type_model \<Rightarrow> 'nt TypeDef set" where
  "UnorderedContainerType Tmod = BagContainerType Tmod \<union> SetContainerType Tmod"

lemma bag_types_are_unordered_containers[simp]: "BagContainerType Tmod \<subseteq> UnorderedContainerType Tmod"
  by (simp add: UnorderedContainerType_def)

lemma set_types_are_unordered_containers[simp]: "SetContainerType Tmod \<subseteq> UnorderedContainerType Tmod"
  by (simp add: UnorderedContainerType_def)

lemma unordered_container_types_are_types[simp]: "UnorderedContainerType Tmod \<subseteq> Type Tmod"
  by (simp add: UnorderedContainerType_def)

lemma unordered_container_type_not_invalid[simp]: "invalid \<notin> UnorderedContainerType Tmod"
  by (simp add: UnorderedContainerType_def)

lemma unordered_container_type_truncate_eq: "UnorderedContainerType Tmod = UnorderedContainerType (truncate Tmod)"
  unfolding UnorderedContainerType_def
  using bag_container_type_truncate_eq set_container_type_truncate_eq
  by blast

definition OrderedContainerType :: "'nt type_model \<Rightarrow> 'nt TypeDef set" where
  "OrderedContainerType Tmod = SeqContainerType Tmod \<union> OrdContainerType Tmod"

lemma seq_types_are_ordered_containers[simp]: "SeqContainerType Tmod \<subseteq> OrderedContainerType Tmod"
  by (simp add: OrderedContainerType_def)

lemma ord_types_are_ordered_containers[simp]: "OrdContainerType Tmod \<subseteq> OrderedContainerType Tmod"
  by (simp add: OrderedContainerType_def)

lemma ordered_container_types_are_types[simp]: "OrderedContainerType Tmod \<subseteq> Type Tmod"
  by (simp add: OrderedContainerType_def)

lemma ordered_container_type_not_invalid[simp]: "invalid \<notin> OrderedContainerType Tmod"
  by (simp add: OrderedContainerType_def)

lemma ordered_container_type_truncate_eq: "OrderedContainerType Tmod = OrderedContainerType (truncate Tmod)"
  unfolding OrderedContainerType_def
  using ord_container_type_truncate_eq seq_container_type_truncate_eq
  by blast

lemma ordered_and_unordered_containers_distinct[simp]: "x \<in> UnorderedContainerType Tmod \<Longrightarrow> x \<notin> OrderedContainerType Tmod"
  using OrderedContainerType_def UnorderedContainerType_def seq_types_bag_types_distinct seq_types_set_types_distinct by fastforce

lemma ordered_and_unordered_containers_intersection[simp]: "UnorderedContainerType Tmod \<inter> OrderedContainerType Tmod = {}"
  by auto

lemma ordered_and_unordered_containers_union[simp]: "UnorderedContainerType Tmod \<union> OrderedContainerType Tmod = ContainerType Tmod"
  using UnorderedContainerType_def OrderedContainerType_def all_container_types_in_container_type by blast



section "Definition of subtype relation"

inductive_set subtype_rel :: "'nt type_model \<Rightarrow> 'nt TypeDef rel"
  for Tmod :: "'nt type_model"
  where
    transitivity: "t1 \<in> Type Tmod \<Longrightarrow> t2 \<in> Type Tmod \<Longrightarrow> t3 \<in> Type Tmod \<Longrightarrow> (t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> (t2, t3) \<in> subtype_rel Tmod \<Longrightarrow> (t1, t3) \<in> subtype_rel Tmod" |
    reflexivity: "t1 \<in> Type Tmod \<Longrightarrow> (t1, t1) \<in> subtype_rel Tmod" |
    generalization_of_inheritance_nullable: "(c1, c2) \<in> Inh Tmod \<Longrightarrow> (\<questiondown>c1, \<questiondown>c2) \<in> subtype_rel Tmod" | 
    generalization_of_inheritance_proper: "(c1, c2) \<in> Inh Tmod \<Longrightarrow> (\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_rel Tmod" |
    nullable_proper_classes: "c1 \<in> Class Tmod \<Longrightarrow> (\<exclamdown>c1, \<questiondown>c1) \<in> subtype_rel Tmod"

definition subtype :: "'nt TypeDef \<Rightarrow> 'nt type_model \<Rightarrow> 'nt TypeDef \<Rightarrow> bool" where
  "subtype t1 Tmod t2 \<equiv> (t1, t2) \<in> subtype_rel Tmod"

notation subtype ("(_/ \<sqsubseteq>[_] _)" [52, 51, 52] 50)

lemma subtype_rel_truncate_eq: "subtype_rel Tmod = subtype_rel (truncate Tmod)"
proof
  show "subtype_rel Tmod \<subseteq> subtype_rel (truncate Tmod)"
  proof
    fix x
    assume "x \<in> subtype_rel Tmod"
    then show "x \<in> subtype_rel (truncate Tmod)"
    proof (induct x)
      case (Pair a b)
      then show ?case
      proof (induct)
        case (transitivity t1 t2 t3)
        then show ?case
          using subtype_rel.transitivity type_truncate_eq
          by blast
      next
        case (reflexivity t1)
        then show ?case
          using subtype_rel.reflexivity type_truncate_eq
          by blast
      next
        case (generalization_of_inheritance_nullable c1 c2)
        then show ?case
          unfolding truncate_def
          by (simp add: subtype_rel.generalization_of_inheritance_nullable)
      next
        case (generalization_of_inheritance_proper c1 c2)
        then show ?case
          unfolding truncate_def
          by (simp add: subtype_rel.generalization_of_inheritance_proper)
      next
        case (nullable_proper_classes c1)
        then show ?case
          unfolding truncate_def
          by (simp add: subtype_rel.nullable_proper_classes)
      qed
    qed
  qed
next
  show "subtype_rel (truncate Tmod) \<subseteq> subtype_rel Tmod"
  proof
    fix x
    assume "x \<in> subtype_rel (truncate Tmod)"
    then show "x \<in> subtype_rel Tmod"
    proof (induct x)
      case (Pair a b)
      then show ?case
      proof (induct)
        case (transitivity t1 t2 t3)
        then show ?case
          using subtype_rel.transitivity type_truncate_eq
          by blast
      next
        case (reflexivity t1)
        then show ?case
          using subtype_rel.reflexivity type_truncate_eq
          by blast
      next
        case (generalization_of_inheritance_nullable c1 c2)
        then show ?case
          unfolding truncate_def
          by (simp add: subtype_rel.generalization_of_inheritance_nullable)
      next
        case (generalization_of_inheritance_proper c1 c2)
        then show ?case
          unfolding truncate_def
          by (simp add: subtype_rel.generalization_of_inheritance_proper)
      next
        case (nullable_proper_classes c1)
        then show ?case
          unfolding truncate_def
          by (simp add: subtype_rel.nullable_proper_classes)
      qed
    qed
  qed
qed


subsection "Alternative definitions of subtype relation"

definition subtype_tuple :: "'a \<Rightarrow> 'a \<times> 'a" where
  "subtype_tuple a = (a, a)"

definition subtype_conv :: "('nt Id \<Rightarrow> 'nt TypeDef) \<Rightarrow> ('nt Id \<Rightarrow> 'nt TypeDef) \<Rightarrow> 'nt Id \<times> 'nt Id \<Rightarrow> 'nt TypeDef \<times> 'nt TypeDef" where
  "subtype_conv f1 f2 tup = (f1 (fst tup), f2 (snd tup))"

definition subtype_rel_altdef :: "'nt type_model \<Rightarrow> 'nt TypeDef rel" where
  "subtype_rel_altdef Tmod \<equiv> subtype_tuple ` Type Tmod \<union> 
    (subtype_conv nullable nullable) ` (Inh Tmod)\<^sup>+ \<union> 
    (subtype_conv proper proper) ` (Inh Tmod)\<^sup>+ \<union> 
    (subtype_conv proper nullable) ` subtype_tuple ` Class Tmod \<union>
    (subtype_conv proper nullable) ` (Inh Tmod)\<^sup>+"

lemma subtype_rel_alt_domain:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "Domain (subtype_rel_altdef Tmod) = Type Tmod"
proof
  have inh_wellformed_classes_alt: "\<And>c. c \<in> (Inh Tmod)\<^sup>+ \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
    using converse_tranclE fst_conv inh_wellformed_classes prod.exhaust_sel snd_conv tranclE
    by metis
  show "Domain (subtype_rel_altdef Tmod) \<subseteq> Type Tmod"
  proof
    fix x
    assume "x \<in> Domain (subtype_rel_altdef Tmod)"
    then show "x \<in> Type Tmod"
    proof
      fix b
      assume "(x, b) \<in> subtype_rel_altdef Tmod"
      then show "x \<in> Type Tmod"
        unfolding subtype_rel_altdef_def
      proof (elim UnE)
        assume "(x, b) \<in> subtype_tuple ` Type Tmod"
        then show "x \<in> Type Tmod"
          by (simp add: image_iff subtype_tuple_def)
      next
        assume "(x, b) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
        then show "x \<in> Type Tmod"
        proof
          fix xa
          assume tuple_is_xa: "(x, b) = subtype_conv nullable nullable xa"
          assume "xa \<in> (Inh Tmod)\<^sup>+"
          then have "fst (subtype_conv nullable nullable xa) \<in> Type Tmod"
            using NullableClassType.rule_nullable_classes fstI inh_wellformed_classes_alt subset_iff subtype_conv_def type_subset_nullable_class_type
            by metis
          then show "x \<in> Type Tmod"
            using fst_conv tuple_is_xa
            by metis
        qed
      next
        assume "(x, b) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
        then show "x \<in> Type Tmod"
        proof
          fix xa
          assume tuple_is_xa: "(x, b) = subtype_conv proper proper xa"
          assume "xa \<in> (Inh Tmod)\<^sup>+"
          then have "fst (subtype_conv proper proper xa) \<in> Type Tmod"
            using ProperClassType.rule_proper_classes fstI inh_wellformed_classes_alt subset_iff subtype_conv_def type_subset_proper_class_type
            by metis
          then show "x \<in> Type Tmod"
            using fst_conv tuple_is_xa
            by metis
        qed
      next
        assume "(x, b) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
        then show "x \<in> Type Tmod"
        proof
          fix xa
          assume tuple_is_xa: "(x, b) = subtype_conv proper nullable xa"
          assume "xa \<in> subtype_tuple ` Class Tmod"
          then have "fst (subtype_conv proper nullable xa) \<in> Type Tmod"
          proof
            fix x
            assume xa_is_x: "xa = subtype_tuple x"
            assume "x \<in> Class Tmod"
            then have "fst (subtype_conv proper nullable (subtype_tuple x)) \<in> Type Tmod"
              using ProperClassType.intros fstI rev_subsetD subtype_conv_def subtype_tuple_def type_subset_proper_class_type
              by metis
            then show "fst (subtype_conv proper nullable xa) \<in> Type Tmod"
              by (simp add: xa_is_x)
          qed
          then show "x \<in> Type Tmod"
            using fst_conv tuple_is_xa
            by metis
        qed
      next
        assume "(x, b) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
        then show "x \<in> Type Tmod"
        proof
          fix xa
          assume tuple_is_xa: "(x, b) = subtype_conv proper nullable xa"
          assume "xa \<in> (Inh Tmod)\<^sup>+"
          then have "fst (subtype_conv proper nullable xa) \<in> Type Tmod"
            using ProperClassType.rule_proper_classes fstI inh_wellformed_classes_alt subset_iff subtype_conv_def type_subset_proper_class_type
            by metis
          then show "x \<in> Type Tmod"
            using fst_conv tuple_is_xa
            by metis
        qed
      qed
    qed
  qed
next
  show "Type Tmod \<subseteq> Domain (subtype_rel_altdef Tmod)"
  proof
    fix x
    assume "x \<in> Type Tmod"
    then show "x \<in> Domain (subtype_rel_altdef Tmod)"
      unfolding subtype_rel_altdef_def subtype_tuple_def
      by auto
  qed
qed

lemma subtype_rel_alt_range:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "Range (subtype_rel_altdef Tmod) = Type Tmod"
proof
  have inh_wellformed_classes_alt: "\<And>c. c \<in> (Inh Tmod)\<^sup>+ \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
    using converse_tranclE fst_conv inh_wellformed_classes prod.exhaust_sel snd_conv tranclE
    by metis
  show "Range (subtype_rel_altdef Tmod) \<subseteq> Type Tmod"
  proof
    fix x
    assume "x \<in> Range (subtype_rel_altdef Tmod)"
    then show "x \<in> Type Tmod"
    proof
      fix a
      assume "(a, x) \<in> subtype_rel_altdef Tmod"
      then show "x \<in> Type Tmod"
        unfolding subtype_rel_altdef_def
      proof (elim UnE)
        assume "(a, x) \<in> subtype_tuple ` Type Tmod"
        then show "x \<in> Type Tmod"
          by (simp add: image_iff subtype_tuple_def)
      next
        assume "(a, x) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
        then show "x \<in> Type Tmod"
        proof
          fix xa
          assume tuple_is_xa: "(a, x) = subtype_conv nullable nullable xa"
          assume "xa \<in> (Inh Tmod)\<^sup>+"
          then have "snd (subtype_conv nullable nullable xa) \<in> Type Tmod"
            using NullableClassType.rule_nullable_classes inh_wellformed_classes_alt sndI subset_iff subtype_conv_def type_subset_nullable_class_type
            by metis
          then show "x \<in> Type Tmod"
            using snd_conv tuple_is_xa
            by metis
        qed
      next
        assume "(a, x) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
        then show "x \<in> Type Tmod"
        proof
          fix xa
          assume tuple_is_xa: "(a, x) = subtype_conv proper proper xa"
          assume "xa \<in> (Inh Tmod)\<^sup>+"
          then have "snd (subtype_conv proper proper xa) \<in> Type Tmod"
            using ProperClassType.rule_proper_classes inh_wellformed_classes_alt sndI subset_iff subtype_conv_def type_subset_proper_class_type
            by metis
          then show "x \<in> Type Tmod"
            using snd_conv tuple_is_xa
            by metis
        qed
      next
        assume "(a, x) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
        then show "x \<in> Type Tmod"
        proof
          fix xa
          assume tuple_is_xa: "(a, x) = subtype_conv proper nullable xa"
          assume "xa \<in> subtype_tuple ` Class Tmod"
          then have "snd (subtype_conv proper nullable xa) \<in> Type Tmod"
          proof
            fix x
            assume xa_is_x: "xa = subtype_tuple x"
            assume "x \<in> Class Tmod"
            then have "snd (subtype_conv proper nullable (subtype_tuple x)) \<in> Type Tmod"
              using NullableClassType.rule_nullable_classes sndI subsetCE subtype_conv_def subtype_tuple_def type_subset_nullable_class_type
              by metis
            then show "snd (subtype_conv proper nullable xa) \<in> Type Tmod"
              by (simp add: xa_is_x)
          qed
          then show "x \<in> Type Tmod"
            using snd_conv tuple_is_xa
            by metis
        qed
      next
        assume "(a, x) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
        then show "x \<in> Type Tmod"
        proof
          fix xa
          assume tuple_is_xa: "(a, x) = subtype_conv proper nullable xa"
          assume "xa \<in> (Inh Tmod)\<^sup>+"
          then have "snd (subtype_conv proper nullable xa) \<in> Type Tmod"
            using NullableClassType.rule_nullable_classes inh_wellformed_classes_alt sndI subset_iff subtype_conv_def type_subset_nullable_class_type
            by metis
          then show "x \<in> Type Tmod"
            using snd_conv tuple_is_xa
            by metis
        qed
      qed
    qed
  qed
next
  show "Type Tmod \<subseteq> Range (subtype_rel_altdef Tmod)"
  proof
    fix x
    assume "x \<in> Type Tmod"
    then show "x \<in> Range (subtype_rel_altdef Tmod)"
      unfolding subtype_rel_altdef_def subtype_tuple_def
      by auto
  qed
qed

lemma subtype_rel_alt_field:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "Relation.Field (subtype_rel_altdef Tmod) = Type Tmod"
  by (simp add: Relation.Field_def inh_wellformed_classes subtype_rel_alt_domain subtype_rel_alt_range)

lemma subtype_rel_alt_reflexive:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "Refl (subtype_rel_altdef Tmod)"
proof
  fix x
  show "subtype_rel_altdef Tmod \<subseteq> Relation.Field (subtype_rel_altdef Tmod) \<times> Relation.Field (subtype_rel_altdef Tmod)"
    by (simp add: FieldI1 FieldI2 subrelI)
  assume "x \<in> Relation.Field (subtype_rel_altdef Tmod)"
  then have "x \<in> Type Tmod"
    by (simp add: inh_wellformed_classes subtype_rel_alt_field)
  then show "(x, x) \<in> subtype_rel_altdef Tmod"
    unfolding subtype_rel_altdef_def subtype_tuple_def
    by simp
qed

lemma subtype_rel_alt_transitive: "trans (subtype_rel_altdef Tmod)"
proof
  fix x y z
  let ?subtype_rel_altdef_unfold = "subtype_tuple ` Type Tmod \<union> 
    subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+ \<union> 
    subtype_conv proper proper ` (Inh Tmod)\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class Tmod \<union>
    subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
  assume x_y_in_rel: "(x, y) \<in> subtype_rel_altdef Tmod"
  assume y_z_in_rel: "(y, z) \<in> subtype_rel_altdef Tmod"
  show "(x, z) \<in> subtype_rel_altdef Tmod"
    using x_y_in_rel
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(x, y) \<in> subtype_tuple ` Type Tmod"
    then show "(x, z) \<in> ?subtype_rel_altdef_unfold"
      using y_z_in_rel
      by (simp add: image_iff subtype_rel_altdef_def subtype_tuple_def)
  next
    assume "(x, y) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
    then show "(x, z) \<in> ?subtype_rel_altdef_unfold"
      using y_z_in_rel
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume x_y: "(x, y) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_tuple ` Type Tmod"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        by (simp add: image_iff subtype_tuple_def)
    next
      assume x_y: "(x, y) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      have "(x, z) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
        using x_y y_z
      proof (elim imageE)
        fix xa xaa
        assume xy_is_xa: "(x, y) = subtype_conv nullable nullable xa"
        assume xa_in_set: "xa \<in> (Inh Tmod)\<^sup>+"
        assume yz_is_xaa: "(y, z) = subtype_conv nullable nullable xaa"
        assume xaa_in_set: "xaa \<in> (Inh Tmod)\<^sup>+"
        have trans: "(fst xa, snd xaa) \<in> (Inh Tmod)\<^sup>+"
          using TypeDef.inject(1) eq_fst_iff eq_snd_iff subtype_conv_def trancl_trans xy_is_xa yz_is_xaa xa_in_set xaa_in_set
          by metis
        have "(x, z) = subtype_conv nullable nullable (fst xa, snd xaa)"
          using fst_conv snd_conv subtype_conv_def xy_is_xa yz_is_xaa
          by metis
        then show "(x, z) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
          using trans
          by simp
      qed
      then show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        by simp
    next
      assume x_y: "(x, y) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        unfolding subtype_conv_def
        by auto
    qed
  next
    assume "(x, y) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
    then show "(x, z) \<in> ?subtype_rel_altdef_unfold"
      using y_z_in_rel
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume x_y: "(x, y) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_tuple ` Type Tmod"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        by (simp add: image_iff subtype_tuple_def)
    next
      assume x_y: "(x, y) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      have "(x, z) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
        using x_y y_z
      proof (elim imageE)
        fix xa xaa
        assume xy_is_xa: "(x, y) = subtype_conv proper proper xa"
        assume xa_in_set: "xa \<in> (Inh Tmod)\<^sup>+"
        assume yz_is_xaa: "(y, z) = subtype_conv proper proper xaa"
        assume xaa_in_set: "xaa \<in> (Inh Tmod)\<^sup>+"
        have trans: "(fst xa, snd xaa) \<in> (Inh Tmod)\<^sup>+"
          using TypeDef.inject(2) eq_fst_iff eq_snd_iff subtype_conv_def trancl_trans xy_is_xa yz_is_xaa xa_in_set xaa_in_set
          by metis
        have "(x, z) = subtype_conv proper proper (fst xa, snd xaa)"
          using fst_conv snd_conv subtype_conv_def xy_is_xa yz_is_xaa
          by metis
        then show "(x, z) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
          using trans
          by simp
      qed
      then show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        by simp
    next
      assume x_y: "(x, y) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      have "(x, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
        using x_y y_z
      proof (elim imageE)
        fix xa xaa xb
        assume xy_is_xa: "(x, y) = subtype_conv proper proper xa"
        assume xa_in_set: "xa \<in> (Inh Tmod)\<^sup>+"
        assume yz_is_xaa: "(y, z) = subtype_conv proper nullable xaa"
        assume xaa_is_xb: "xaa = subtype_tuple xb"
        assume xb_is_class: "xb \<in> Class Tmod"
        have trans: "(fst xa, snd xaa) \<in> (Inh Tmod)\<^sup>+"
          using TypeDef.inject(2) fst_conv prod.collapse snd_conv subtype_conv_def subtype_tuple_def xa_in_set xaa_is_xb xy_is_xa yz_is_xaa
          by metis
        have "(x, z) = subtype_conv proper nullable (fst xa, snd xaa)"
          using fst_conv snd_conv subtype_conv_def xy_is_xa yz_is_xaa
          by metis
        then show "(x, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
          using trans
          by simp
      qed
      then show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        by simp
    next
      assume x_y: "(x, y) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      have "(x, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
        using x_y y_z
      proof (elim imageE)
        fix xa xaa
        assume xy_is_xa: "(x, y) = subtype_conv proper proper xa"
        assume xa_in_set: "xa \<in> (Inh Tmod)\<^sup>+"
        assume yz_is_xaa: "(y, z) = subtype_conv proper nullable xaa"
        assume xaa_in_set: "xaa \<in> (Inh Tmod)\<^sup>+"
        have trans: "(fst xa, snd xaa) \<in> (Inh Tmod)\<^sup>+"
          using TypeDef.inject(2) eq_fst_iff eq_snd_iff subtype_conv_def trancl_trans xy_is_xa yz_is_xaa xa_in_set xaa_in_set
          by metis
        have "(x, z) = subtype_conv proper nullable (fst xa, snd xaa)"
          using fst_conv snd_conv subtype_conv_def xy_is_xa yz_is_xaa
          by metis
        then show "(x, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
          using trans
          by simp
      qed
      then show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        by simp
    qed
  next
    assume "(x, y) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
    then show "(x, z) \<in> ?subtype_rel_altdef_unfold"
      using y_z_in_rel
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      assume y_z: "(y, z) \<in> subtype_tuple ` Type Tmod"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        by (simp add: image_iff subtype_tuple_def)
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      assume y_z: "(y, z) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      have "(x, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
        using x_y y_z
      proof (elim imageE)
        fix xa xaa xb
        assume xy_is_xa: "(x, y) = subtype_conv proper nullable xa"
        assume xa_is_xb: "xa = subtype_tuple xb"
        assume xb_in_set: "xb \<in> Class Tmod"
        assume yz_is_xaa: "(y, z) = subtype_conv nullable nullable xaa"
        assume xaa_in_set: "xaa \<in> (Inh Tmod)\<^sup>+"
        have trans: "(fst xa, snd xaa) \<in> (Inh Tmod)\<^sup>+"
          using TypeDef.inject(1) fst_conv prod.collapse snd_conv subtype_conv_def subtype_tuple_def xa_is_xb xaa_in_set xy_is_xa yz_is_xaa
          by metis
        have "(x, z) = subtype_conv proper nullable (fst xa, snd xaa)"
          using fst_conv snd_conv subtype_conv_def xy_is_xa yz_is_xaa
          by metis
        then show "(x, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
          using trans
          by simp
      qed
      then show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        by simp
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      assume y_z: "(y, z) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      assume y_z: "(y, z) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      assume y_z: "(y, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        unfolding subtype_conv_def
        by auto
    qed
  next
    assume "(x, y) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
    then show "(x, z) \<in> ?subtype_rel_altdef_unfold"
      using y_z_in_rel
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_tuple ` Type Tmod"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        by (simp add: image_iff subtype_tuple_def)
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      have "(x, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
        using x_y y_z
      proof (elim imageE)
        fix xa xaa
        assume xy_is_xa: "(x, y) = subtype_conv proper nullable xa"
        assume xa_in_set: "xa \<in> (Inh Tmod)\<^sup>+"
        assume yz_is_xaa: "(y, z) = subtype_conv nullable nullable xaa"
        assume xaa_in_set: "xaa \<in> (Inh Tmod)\<^sup>+"
        have trans: "(fst xa, snd xaa) \<in> (Inh Tmod)\<^sup>+"
          using TypeDef.inject(1) eq_fst_iff eq_snd_iff subtype_conv_def trancl_trans xy_is_xa yz_is_xaa xa_in_set xaa_in_set
          by metis
        have "(x, z) = subtype_conv proper nullable (fst xa, snd xaa)"
          using fst_conv snd_conv subtype_conv_def xy_is_xa yz_is_xaa
          by metis
        then show "(x, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
          using trans
          by simp
      qed
      then show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        by simp
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      assume y_z: "(y, z) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      show "(x, z) \<in> ?subtype_rel_altdef_unfold"
        using x_y y_z
        unfolding subtype_conv_def
        by auto
    qed
  qed
qed

lemma subtype_rel_alt_antisymmetric:
  assumes inh_wellformed_relation: "irrefl ((Inh Tmod)\<^sup>+)"
  shows "antisym (subtype_rel_altdef Tmod)"
proof
  fix x y
  assume y_x_in_rel: "(y, x) \<in> subtype_rel_altdef Tmod"
  assume x_y_in_rel: "(x, y) \<in> subtype_rel_altdef Tmod"
  then show "x = y"
    unfolding subtype_rel_altdef_def
  proof (elim UnE)
    assume "(x, y) \<in> subtype_tuple ` Type Tmod"
    then show "x = y"
      by (simp add: image_iff subtype_tuple_def)
  next
    assume "(x, y) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
    then show "x = y"
      using y_x_in_rel
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume "(y, x) \<in> subtype_tuple ` Type Tmod"
      then show "x = y"
        by (simp add: image_iff subtype_tuple_def)
    next
      assume x_y: "(x, y) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
      proof (elim imageE)
        fix xa xaa
        assume xy_is_xa: "(x, y) = subtype_conv nullable nullable xa"
        assume "xa \<in> (Inh Tmod)\<^sup>+"
        then have rev_xa_not_inh: "(snd xa, fst xa) \<notin> (Inh Tmod)\<^sup>+"
          by (metis inh_wellformed_relation irrefl_def prod.exhaust_sel trancl_trans)
        assume yx_is_xaa: "(y, x) = subtype_conv nullable nullable xaa"
        assume xaa_in_set: "xaa \<in> (Inh Tmod)\<^sup>+"
        then have xaa_is_xa_rev: "xaa = (snd xa, fst xa)"
          using TypeDef.inject(1) fst_conv prod.collapse snd_conv subtype_conv_def xy_is_xa yx_is_xaa
          by metis
        show "x = y"
          using rev_xa_not_inh xaa_in_set xaa_is_xa_rev by blast
      qed
    next
      assume x_y: "(x, y) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    qed
  next
    assume "(x, y) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
    then show "x = y"
      using y_x_in_rel
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume "(y, x) \<in> subtype_tuple ` Type Tmod"
      then show "x = y"
        by (simp add: image_iff subtype_tuple_def)
    next
      assume x_y: "(x, y) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
      proof (elim imageE)
        fix xa xaa
        assume xy_is_xa: "(x, y) = subtype_conv proper proper xa"
        assume "xa \<in> (Inh Tmod)\<^sup>+"
        then have rev_xa_not_inh: "(snd xa, fst xa) \<notin> (Inh Tmod)\<^sup>+"
          by (metis inh_wellformed_relation irrefl_def prod.exhaust_sel trancl_trans)
        assume yx_is_xaa: "(y, x) = subtype_conv proper proper xaa"
        assume xaa_in_set: "xaa \<in> (Inh Tmod)\<^sup>+"
        then have xaa_is_xa_rev: "xaa = (snd xa, fst xa)"
          using TypeDef.inject(2) fstI prod.collapse sndI subtype_conv_def xy_is_xa yx_is_xaa
          by metis
        show "x = y"
          using rev_xa_not_inh xaa_in_set xaa_is_xa_rev by blast
      qed
    next
      assume x_y: "(x, y) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    qed
  next
    assume "(x, y) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
    then show "x = y"
      using y_x_in_rel
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume "(y, x) \<in> subtype_tuple ` Type Tmod"
      then show "x = y"
        by (simp add: image_iff subtype_tuple_def)
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      assume y_x: "(y, x) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      assume y_x: "(y, x) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      assume y_x: "(y, x) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      assume y_x: "(y, x) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    qed
  next
    assume "(x, y) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
    then show "x = y"
      using y_x_in_rel
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume "(y, x) \<in> subtype_tuple ` Type Tmod"
      then show "x = y"
        by (simp add: image_iff subtype_tuple_def)
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    next
      assume x_y: "(x, y) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      assume y_x: "(y, x) \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      show "x = y"
        using x_y y_x
        unfolding subtype_conv_def
        by auto
    qed
  qed
qed

lemma subtype_rel_alt_partial_order:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  assumes inh_wellformed_relation: "irrefl ((Inh Tmod)\<^sup>+)"
  shows "Partial_order (subtype_rel_altdef Tmod)"
  unfolding partial_order_on_def preorder_on_def
  by (simp add: inh_wellformed_classes inh_wellformed_relation subtype_rel_alt_antisymmetric subtype_rel_alt_reflexive subtype_rel_alt_transitive)

lemma subtype_rel_alt_truncate_eq: "subtype_rel_altdef Tmod = subtype_rel_altdef (truncate Tmod)"
proof
  show "subtype_rel_altdef Tmod \<subseteq> subtype_rel_altdef (truncate Tmod)"
  proof
    fix x
    assume "x \<in> subtype_rel_altdef Tmod"
    then have "x \<in> subtype_tuple ` Type Tmod \<union> 
      subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+ \<union> 
      subtype_conv proper proper ` (Inh Tmod)\<^sup>+ \<union> 
      subtype_conv proper nullable ` subtype_tuple ` Class Tmod \<union> 
      subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      unfolding subtype_rel_altdef_def
      by simp
    then show "x \<in> subtype_rel_altdef (truncate Tmod)"
    proof (elim UnE)
      assume "x \<in> subtype_tuple ` Type Tmod"
      then have "x \<in> subtype_tuple ` Type (truncate Tmod)"
        using type_truncate_eq
        by blast
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    next
      assume "x \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      then have "x \<in> subtype_conv nullable nullable ` (Inh (truncate Tmod))\<^sup>+"
        unfolding truncate_def
        by simp
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    next
      assume "x \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      then have "x \<in> subtype_conv proper proper ` (Inh (truncate Tmod))\<^sup>+"
        unfolding truncate_def
        by simp
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    next
      assume "x \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      then have "x \<in> subtype_conv proper nullable ` subtype_tuple ` Class (truncate Tmod)"
        unfolding truncate_def
        by simp
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    next
      assume "x \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      then have "x \<in> subtype_conv proper nullable ` (Inh (truncate Tmod))\<^sup>+"
        unfolding truncate_def
        by simp
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    qed
  qed
next
  show "subtype_rel_altdef (truncate Tmod) \<subseteq> subtype_rel_altdef Tmod"
  proof
    fix x
    assume "x \<in> subtype_rel_altdef (truncate Tmod)"
    then have "x \<in> subtype_tuple ` Type (truncate Tmod) \<union> 
      subtype_conv nullable nullable ` (Inh (truncate Tmod))\<^sup>+ \<union> 
      subtype_conv proper proper ` (Inh (truncate Tmod))\<^sup>+ \<union> 
      subtype_conv proper nullable ` subtype_tuple ` Class (truncate Tmod) \<union> 
      subtype_conv proper nullable ` (Inh (truncate Tmod))\<^sup>+"
      unfolding subtype_rel_altdef_def
      by simp
    then show "x \<in> subtype_rel_altdef Tmod"
    proof (elim UnE)
      assume "x \<in> subtype_tuple ` Type (truncate Tmod)"
      then have "x \<in> subtype_tuple ` Type Tmod"
        using type_truncate_eq
        by blast
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    next
      assume "x \<in> subtype_conv nullable nullable ` (Inh (truncate Tmod))\<^sup>+"
      then have "x \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
        unfolding truncate_def
        by simp
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    next
      assume "x \<in> subtype_conv proper proper ` (Inh (truncate Tmod))\<^sup>+"
      then have "x \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
        unfolding truncate_def
        by simp
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    next
      assume "x \<in> subtype_conv proper nullable ` subtype_tuple ` Class (truncate Tmod)"
      then have "x \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
        unfolding truncate_def
        by simp
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    next
      assume "x \<in> subtype_conv proper nullable ` (Inh (truncate Tmod))\<^sup>+"
      then have "x \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
        unfolding truncate_def
        by simp
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    qed
  qed
qed

lemma subtype_rel_alt:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "subtype_rel Tmod = subtype_rel_altdef Tmod"
proof
  show "subtype_rel Tmod \<subseteq> subtype_rel_altdef Tmod"
  proof
    fix x
    assume "x \<in> subtype_rel Tmod"
    then show "x \<in> subtype_rel_altdef Tmod"
    proof (induct x)
      case (Pair a b)
      then show ?case
      proof (induct)
        case (transitivity t1 t2 t3)
        then show ?case
          using inh_wellformed_classes subtype_rel_alt_transitive transE
          by metis
      next
        case (reflexivity t1)
        then show ?case
          unfolding subtype_rel_altdef_def subtype_tuple_def
          by simp
      next
        case (generalization_of_inheritance_nullable c1 c2)
        then have "(c1, c2) \<in> (Inh Tmod)\<^sup>+"
          by simp
        then have "(\<questiondown>c1, \<questiondown>c2) \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
          unfolding subtype_conv_def
          by force
        then show ?case
          unfolding subtype_rel_altdef_def
          by simp
      next
        case (generalization_of_inheritance_proper c1 c2)
        then have "(c1, c2) \<in> (Inh Tmod)\<^sup>+"
          by simp
        then have "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
          unfolding subtype_conv_def
          by force
        then show ?case
          unfolding subtype_rel_altdef_def
          by simp
      next
        case (nullable_proper_classes c1)
        have subtype_conv_tuple: "(\<exclamdown>c1, \<questiondown>c1) = subtype_conv proper nullable (c1, c1)"
          unfolding subtype_conv_def
          by simp
        have "(c1, c1) \<in> subtype_tuple ` Class Tmod"
          unfolding subtype_tuple_def
          using nullable_proper_classes.hyps 
          by simp
        then have "(\<exclamdown>c1, \<questiondown>c1) \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
          using subtype_conv_tuple
          by simp
        then show ?case
          unfolding subtype_rel_altdef_def
          by simp
      qed
    qed
  qed
next
  show "subtype_rel_altdef Tmod \<subseteq> subtype_rel Tmod"
  proof
    fix x
    assume "x \<in> subtype_rel_altdef Tmod"
    then show "x \<in> subtype_rel Tmod"
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume "x \<in> subtype_tuple ` Type Tmod"
      then show "x \<in> subtype_rel Tmod"
        unfolding subtype_tuple_def
        using subtype_rel.reflexivity 
        by fastforce
    next
      assume "x \<in> subtype_conv nullable nullable ` (Inh Tmod)\<^sup>+"
      then show "x \<in> subtype_rel Tmod"
      proof
        fix xa
        assume x_is_xa: "x = subtype_conv nullable nullable xa"
        assume "xa \<in> (Inh Tmod)\<^sup>+"
        then have "subtype_conv nullable nullable xa \<in> subtype_rel Tmod"
        proof (induct xa)
          case (fields a b c)
          then show ?case
          proof (induct)
            case (base y)
            then show ?case
              by (simp add: subtype_conv_def subtype_rel.generalization_of_inheritance_nullable)
          next
            case (step y z)
            have a_class: "a \<in> Class Tmod"
              using converse_tranclE fst_conv inh_wellformed_classes step.hyps(1)
              by metis
            then have a_type: "\<questiondown>a \<in> Type Tmod"
              using NullableClassType.rule_nullable_classes rev_subsetD type_subset_nullable_class_type
              by metis
            have y_class: "y \<in> Class Tmod"
              using inh_wellformed_classes step.hyps(2) by fastforce
            then have y_type: "\<questiondown>y \<in> Type Tmod"
              using NullableClassType.rule_nullable_classes rev_subsetD type_subset_nullable_class_type
              by metis
            have z_class: "z \<in> Class Tmod"
              using inh_wellformed_classes step.hyps(2) by fastforce
            then have z_type: "\<questiondown>z \<in> Type Tmod"
              using NullableClassType.rule_nullable_classes rev_subsetD type_subset_nullable_class_type
              by metis
            show ?case
              unfolding subtype_conv_def
              using a_type fst_conv snd_conv step.hyps(2) step.hyps(3) subtype_conv_def subtype_rel.simps y_type z_type
              by metis
          qed
        qed
        then show "x \<in> subtype_rel Tmod"
          by (simp add: x_is_xa)
      qed
    next
      assume "x \<in> subtype_conv proper proper ` (Inh Tmod)\<^sup>+"
      then show "x \<in> subtype_rel Tmod"
      proof
        fix xa
        assume x_is_xa: "x = subtype_conv proper proper xa"
        assume "xa \<in> (Inh Tmod)\<^sup>+"
        then have "subtype_conv proper proper xa \<in> subtype_rel Tmod"
        proof (induct xa)
          case (fields a b c)
          then show ?case
          proof (induct)
            case (base y)
            then show ?case
              by (simp add: subtype_conv_def subtype_rel.generalization_of_inheritance_proper)
          next
            case (step y z)
            have a_class: "a \<in> Class Tmod"
              using converse_tranclE fst_conv inh_wellformed_classes step.hyps(1)
              by metis
            then have a_type: "\<exclamdown>a \<in> Type Tmod"
              using ProperClassType.intros subsetCE type_subset_proper_class_type
              by metis
            have y_class: "y \<in> Class Tmod"
              using inh_wellformed_classes step.hyps(2) by fastforce
            then have y_type: "\<exclamdown>y \<in> Type Tmod"
              using ProperClassType.intros subsetCE type_subset_proper_class_type
              by metis
            have z_class: "z \<in> Class Tmod"
              using inh_wellformed_classes step.hyps(2) by fastforce
            then have z_type: "\<exclamdown>z \<in> Type Tmod"
              using ProperClassType.intros subsetCE type_subset_proper_class_type
              by metis
            show ?case
              unfolding subtype_conv_def
              using a_type fst_conv snd_conv step.hyps(2) step.hyps(3) subtype_conv_def subtype_rel.simps y_type z_type
              by metis
          qed
        qed
        then show "x \<in> subtype_rel Tmod"
          by (simp add: x_is_xa)
      qed
    next
      assume "x \<in> subtype_conv proper nullable ` subtype_tuple ` Class Tmod"
      then show "x \<in> subtype_rel Tmod"
      proof
        fix xa
        assume x_is_xa: "x = subtype_conv proper nullable xa"
        assume "xa \<in> subtype_tuple ` Class Tmod"
        then have "subtype_conv proper nullable xa \<in> subtype_rel Tmod"
          unfolding subtype_conv_def
          using eq_snd_iff fstI imageE subtype_rel.nullable_proper_classes subtype_tuple_def
          by metis
        then show "x \<in> subtype_rel Tmod"
          by (simp add: x_is_xa)
      qed
    next
      assume "x \<in> subtype_conv proper nullable ` (Inh Tmod)\<^sup>+"
      then show "x \<in> subtype_rel Tmod"
      proof
        fix xa
        assume x_is_xa: "x = subtype_conv proper nullable xa"
        assume "xa \<in> (Inh Tmod)\<^sup>+"
        then have "subtype_conv proper nullable xa \<in> subtype_rel Tmod"
        proof (induct xa)
          case (fields a b c)
          then show ?case
          proof (induct)
            case (base y)
            have a_class: "a \<in> Class Tmod"
              using inh_wellformed_classes base.hyps by fastforce
            then have a_type_proper: "\<exclamdown>a \<in> Type Tmod"
              using ProperClassType.intros subsetCE type_subset_proper_class_type
              by metis
            have a_type_nullable: "\<questiondown>a \<in> Type Tmod"
              using NullableClassType.rule_nullable_classes a_class subsetCE type_subset_nullable_class_type
              by metis
            have y_class: "y \<in> Class Tmod"
              using inh_wellformed_classes base.hyps by fastforce
            then have y_type: "\<questiondown>y \<in> Type Tmod"
              using NullableClassType.rule_nullable_classes rev_subsetD type_subset_nullable_class_type
              by metis
            have aa_extend: "subtype_conv proper nullable (a, a) \<in> subtype_rel Tmod"
              using base.hyps fst_conv inh_wellformed_classes snd_conv subtype_conv_def subtype_rel.nullable_proper_classes
              by metis
            have ay_extend: "subtype_conv nullable nullable (a, y) \<in> subtype_rel Tmod"
              by (simp add: base.hyps subtype_conv_def subtype_rel.generalization_of_inheritance_nullable)
            then show ?case
              using a_class a_type_nullable a_type_proper fst_conv snd_conv subtype_conv_def subtype_rel.nullable_proper_classes subtype_rel.transitivity y_type
              by metis
          next
            case (step y z)
            have a_class: "a \<in> Class Tmod"
              using converse_tranclE fst_conv inh_wellformed_classes step.hyps(1)
              by metis
            then have a_type: "\<exclamdown>a \<in> Type Tmod"
              using ProperClassType.intros subsetCE type_subset_proper_class_type
              by metis
            have y_class: "y \<in> Class Tmod"
              using inh_wellformed_classes step.hyps(2) by fastforce
            then have y_type: "\<questiondown>y \<in> Type Tmod"
              using NullableClassType.rule_nullable_classes rev_subsetD type_subset_nullable_class_type
              by metis
            have z_class: "z \<in> Class Tmod"
              using inh_wellformed_classes step.hyps(2) by fastforce
            then have z_type: "\<questiondown>z \<in> Type Tmod"
              using NullableClassType.rule_nullable_classes rev_subsetD type_subset_nullable_class_type
              by metis
            then show ?case
              using a_type fst_conv snd_conv step.hyps(2) step.hyps(3) subtype_conv_def subtype_rel.generalization_of_inheritance_nullable subtype_rel.transitivity y_type
              by metis
          qed
        qed
        then show "x \<in> subtype_rel Tmod"
          by (simp add: x_is_xa)
      qed
    qed
  qed
qed


subsection "Domain and range of the subtype relation"

lemma subtype_relation_domain:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "Domain (subtype_rel Tmod) = Type Tmod"
  by (simp add: inh_wellformed_classes subtype_rel_alt subtype_rel_alt_domain)

lemma subtype_relation_range:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "Range (subtype_rel Tmod) = Type Tmod"
  by (simp add: inh_wellformed_classes subtype_rel_alt subtype_rel_alt_range)

lemma subtype_relation_field:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "Relation.Field (subtype_rel Tmod) = Type Tmod"
  by (simp add: inh_wellformed_classes subtype_rel_alt subtype_rel_alt_field)


subsection "Partial order lemma's on the subtype relation"

lemma subtype_relation_reflexive:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "Refl (subtype_rel Tmod)"
  by (simp add: inh_wellformed_classes subtype_rel_alt subtype_rel_alt_reflexive)

lemma subtype_relation_transitive:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "trans (subtype_rel Tmod)"
  by (simp add: inh_wellformed_classes subtype_rel_alt subtype_rel_alt_transitive)

lemma subtype_relation_antisymmetric:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  assumes inh_wellformed_relation: "irrefl ((Inh Tmod)\<^sup>+)"
  shows "antisym (subtype_rel Tmod)"
  by (simp add: inh_wellformed_classes inh_wellformed_relation subtype_rel_alt subtype_rel_alt_antisymmetric)

lemma subtype_relation_partial_order:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  assumes inh_wellformed_relation: "irrefl ((Inh Tmod)\<^sup>+)"
  shows "Partial_order (subtype_rel Tmod)"
  unfolding partial_order_on_def preorder_on_def
  by (simp add: inh_wellformed_classes inh_wellformed_relation subtype_relation_antisymmetric subtype_relation_reflexive subtype_relation_transitive)


subsection "Other lemma's on the subtype relation"

lemma subtype_relation_fst_no_class_equal: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> \<forall>x. t1 \<noteq> \<questiondown>x \<and> t1 \<noteq> \<exclamdown>x \<Longrightarrow> t1 = t2"
proof-
  fix t1 t2
  assume subtype_element: "(t1, t2) \<in> subtype_rel Tmod"
  assume no_class_type: "\<forall>x. t1 \<noteq> \<questiondown>x \<and> t1 \<noteq> \<exclamdown>x"
  show "t1 = t2"
    using subtype_element no_class_type
    by (induct) (simp_all)
qed

lemma subtype_fst_no_class_equal[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> \<forall>x. t1 \<noteq> \<questiondown>x \<and> t1 \<noteq> \<exclamdown>x \<Longrightarrow> t1 = t2"
  unfolding subtype_def
  by (fact subtype_relation_fst_no_class_equal)

lemma subtype_relation_snd_no_class_equal: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> \<forall>x. t2 \<noteq> \<questiondown>x \<and> t2 \<noteq> \<exclamdown>x \<Longrightarrow> t1 = t2"
proof-
  fix t1 t2
  assume subtype_element: "(t1, t2) \<in> subtype_rel Tmod"
  assume no_class_type: "\<forall>x. t2 \<noteq> \<questiondown>x \<and> t2 \<noteq> \<exclamdown>x"
  show "t1 = t2"
    using subtype_element no_class_type
    by (induct) (simp_all)
qed

lemma subtype_snd_no_class_equal[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> \<forall>x. t2 \<noteq> \<questiondown>x \<and> t2 \<noteq> \<exclamdown>x \<Longrightarrow> t1 = t2"
  unfolding subtype_def
  by (fact subtype_relation_snd_no_class_equal)

lemma subtype_relation_nullable_supertype_nullable: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> \<exists>x. t1 = \<questiondown>x \<Longrightarrow> \<exists>y. t2 = \<questiondown>y"
proof-
  fix t1 t2
  assume pair_in_subtype_relation: "(t1, t2) \<in> subtype_rel Tmod"
  assume fst_is_nullable_classtype: "\<exists>x. t1 = \<questiondown>x"
  show "\<exists>y. t2 = \<questiondown>y"
    using pair_in_subtype_relation fst_is_nullable_classtype
    by (induct) (simp_all)
qed

lemma subtype_nullable_supertype_nullable[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> \<exists>x. t1 = \<questiondown>x \<Longrightarrow> \<exists>y. t2 = \<questiondown>y"
  unfolding subtype_def
  by (fact subtype_relation_nullable_supertype_nullable)

lemma subtype_relation_no_nullable_extends_proper: "(\<questiondown>c1, \<exclamdown>c2) \<notin> subtype_rel Tmod"
  using subtype_relation_nullable_supertype_nullable by blast

lemma subtype_no_nullable_extends_proper[simp]: "\<not>(\<questiondown>c1 \<sqsubseteq>[Tmod] \<exclamdown>c2)"
  unfolding subtype_def
  by (fact subtype_relation_no_nullable_extends_proper)

lemma subtype_relation_only_proper_extends_proper: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> \<exists>x. t2 = \<exclamdown>x \<Longrightarrow> \<exists>y. t1 = \<exclamdown>y"
proof-
  fix t1 t2
  assume pair_in_subtype_relation: "(t1, t2) \<in> subtype_rel Tmod"
  assume snd_is_proper_classtype: "\<exists>x. t2 = \<exclamdown>x"
  show "\<exists>y. t1 = \<exclamdown>y"
    using pair_in_subtype_relation snd_is_proper_classtype
    by (induct) (simp_all)
qed

lemma subtype_only_proper_extends_proper[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> \<exists>x. t2 = \<exclamdown>x \<Longrightarrow> \<exists>y. t1 = \<exclamdown>y"
  unfolding subtype_def
  by (fact subtype_relation_only_proper_extends_proper)
  
lemma subtype_relation_datatypes_no_supertypes: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t1 \<in> DataType \<Longrightarrow> t1 = t2"
  using datatype_contains_no_nullable_classes datatype_contains_no_proper_classes subtype_relation_fst_no_class_equal 
  by blast

lemma subtype_datatypes_no_supertypes[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> t1 \<in> DataType \<Longrightarrow> t1 = t2"
  unfolding subtype_def
  by (fact subtype_relation_datatypes_no_supertypes)

lemma subtype_relation_datatypes_no_subtypes: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t2 \<in> DataType \<Longrightarrow> t1 = t2"
  using datatype_contains_no_nullable_classes datatype_contains_no_proper_classes subtype_relation_snd_no_class_equal 
  by blast

lemma subtype_datatypes_no_subtypes[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> t2 \<in> DataType \<Longrightarrow> t1 = t2"
  unfolding subtype_def
  by (fact subtype_relation_datatypes_no_subtypes)

lemma subtype_relation_nullable_supertypes:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t1 \<in> NullableClassType Tmod \<Longrightarrow> t2 \<in> NullableClassType Tmod"
proof-
  fix t1 t2
  assume pair_in_subtype_relation: "(t1, t2) \<in> subtype_rel Tmod"
  assume fst_is_nullable_classtype: "t1 \<in> NullableClassType Tmod"
  show "t2 \<in> NullableClassType Tmod"
    using pair_in_subtype_relation fst_is_nullable_classtype
  proof (induct)
    case (generalization_of_inheritance_nullable c1 c2)
    then show ?case
      using NullableClassType.rule_nullable_classes inh_wellformed_classes
      by fastforce
  qed (simp_all)
qed

lemma subtype_nullable_supertypes[simp]:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t1 \<in> NullableClassType Tmod \<Longrightarrow> t2 \<in> NullableClassType Tmod"
  unfolding subtype_def
  using inh_wellformed_classes subtype_relation_nullable_supertypes
  by blast

lemma subtype_relation_proper_subtypes:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t2 \<in> ProperClassType Tmod \<Longrightarrow> t1 \<in> ProperClassType Tmod"
proof-
  fix t1 t2
  assume pair_in_subtype_relation: "(t1, t2) \<in> subtype_rel Tmod"
  assume snd_is_proper_classtype: "t2 \<in> ProperClassType Tmod"
  show "t1 \<in> ProperClassType Tmod"
    using pair_in_subtype_relation snd_is_proper_classtype
  proof (induct)
    case (generalization_of_inheritance_proper c1 c2)
    then show ?case
      using ProperClassType.rule_proper_classes inh_wellformed_classes
      by fastforce
  qed (simp_all)
qed

lemma subtype_proper_subtypes[simp]: 
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> t2 \<in> ProperClassType Tmod \<Longrightarrow> t1 \<in> ProperClassType Tmod"
  unfolding subtype_def
  using inh_wellformed_classes subtype_relation_proper_subtypes
  by blast

lemma subtype_relation_enums_no_supertypes: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t1 \<in> EnumType Tmod \<Longrightarrow> t1 = t2"
  using enum_type_contains_no_nullable_classes enum_type_contains_no_proper_classes subtype_relation_fst_no_class_equal 
  by blast

lemma subtype_enums_no_supertypes[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> t1 \<in> EnumType Tmod \<Longrightarrow> t1 = t2"
  unfolding subtype_def
  by (fact subtype_relation_enums_no_supertypes)

lemma subtype_relation_enums_no_subtypes: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t2 \<in> EnumType Tmod \<Longrightarrow> t1 = t2"
  using enum_type_contains_no_nullable_classes enum_type_contains_no_proper_classes subtype_relation_snd_no_class_equal 
  by blast

lemma subtype_enums_no_subtypes[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> t2 \<in> EnumType Tmod \<Longrightarrow> t1 = t2"
  unfolding subtype_def
  by (fact subtype_relation_enums_no_subtypes)

lemma subtype_relation_userdatatypes_no_supertypes: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t1 \<in> UserDataTypeType Tmod \<Longrightarrow> t1 = t2"
  using subtype_relation_fst_no_class_equal userdatatype_type_contains_no_nullable_classes userdatatype_type_contains_no_proper_classes 
  by blast

lemma subtype_userdatatypes_no_supertypes[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> t1 \<in> UserDataTypeType Tmod \<Longrightarrow> t1 = t2"
  unfolding subtype_def
  by (fact subtype_relation_userdatatypes_no_supertypes)

lemma subtype_relation_userdatatypes_no_subtypes: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t2 \<in> UserDataTypeType Tmod \<Longrightarrow> t1 = t2"
  using subtype_relation_snd_no_class_equal userdatatype_type_contains_no_nullable_classes userdatatype_type_contains_no_proper_classes 
  by blast

lemma subtype_userdatatypes_no_subtypes[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> t2 \<in> UserDataTypeType Tmod \<Longrightarrow> t1 = t2"
  unfolding subtype_def
  by (fact subtype_relation_userdatatypes_no_subtypes)

lemma subtype_relation_noncontainertypes_supertypes:
  assumes inh_well42formed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t1 \<in> NonContainerType Tmod \<Longrightarrow> t2 \<in> NonContainerType Tmod"
  using FieldI2 assms container_type_contains_no_nullable_classes container_type_contains_no_proper_classes subtype_relation_field subtype_relation_snd_no_class_equal type_not_member
  by metis

lemma subtype_noncontainertypes_supertypes[simp]:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> t1 \<in> NonContainerType Tmod \<Longrightarrow> t2 \<in> NonContainerType Tmod"
  unfolding subtype_def
  using inh_wellformed_classes subtype_relation_noncontainertypes_supertypes
  by blast

lemma subtype_relation_noncontainertypes_subtypes:
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t2 \<in> NonContainerType Tmod \<Longrightarrow> t1 \<in> NonContainerType Tmod"
  using FieldI1 assms container_type_contains_no_nullable_classes container_type_contains_no_proper_classes subtype_relation_field subtype_relation_fst_no_class_equal type_not_member
  by metis

lemma subtype_noncontainertypes_subtypes[simp]: 
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  shows "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> t2 \<in> NonContainerType Tmod \<Longrightarrow> t1 \<in> NonContainerType Tmod"
  unfolding subtype_def
  using inh_wellformed_classes subtype_relation_noncontainertypes_subtypes
  by blast

lemma subtype_relation_containertypes_no_supertypes: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t1 \<in> ContainerType Tmod \<Longrightarrow> t1 = t2"
  using container_type_contains_no_nullable_classes container_type_contains_no_proper_classes subtype_relation_fst_no_class_equal 
  by blast

lemma subtype_containertypes_no_supertypes[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> t1 \<in> ContainerType Tmod \<Longrightarrow> t1 = t2"
  unfolding subtype_def
  by (fact subtype_relation_containertypes_no_supertypes)

lemma subtype_relation_containertypes_no_subtypes: "(t1, t2) \<in> subtype_rel Tmod \<Longrightarrow> t2 \<in> ContainerType Tmod \<Longrightarrow> t1 = t2"
  using container_type_contains_no_nullable_classes container_type_contains_no_proper_classes subtype_relation_snd_no_class_equal 
  by blast

lemma subtype_containertypes_no_subtypes[simp]: "t1 \<sqsubseteq>[Tmod] t2 \<Longrightarrow> t2 \<in> ContainerType Tmod \<Longrightarrow> t1 = t2"
  unfolding subtype_def
  by (fact subtype_relation_containertypes_no_subtypes)

lemma subtype_relation_fst_not_invalid: "\<And>t. (invalid, t) \<notin> subtype_rel Tmod"
proof-
  fix t
  have "\<And>x. (x, t) \<in> subtype_rel Tmod \<Longrightarrow> x \<noteq> invalid"
  proof-
    fix x
    assume "(x, t) \<in> subtype_rel Tmod"
    then show "x \<noteq> invalid"
    proof (induct)
      case (transitivity t1 t2 t3)
      then show ?case
        by simp
    next
      case (reflexivity t1)
      then show ?case
        by fastforce
    qed (simp_all)
  qed
  then show "(invalid, t) \<notin> subtype_rel Tmod"
    by blast
qed

lemma subtype_fst_not_invalid[simp]: "\<And>x. \<not>invalid \<sqsubseteq>[Tmod] x"
  unfolding subtype_def
  by (fact subtype_relation_fst_not_invalid)

lemma subtype_relation_snd_not_invalid: "\<And>t. (t, invalid) \<notin> subtype_rel Tmod"
proof-
  fix t
  have "\<And>x. (t, x) \<in> subtype_rel Tmod \<Longrightarrow> x \<noteq> invalid"
  proof-
    fix x
    assume "(t, x) \<in> subtype_rel Tmod"
    then show "x \<noteq> invalid"
    proof (induct)
      case (transitivity t1 t2 t3)
      then show ?case
        by simp
    next
      case (reflexivity t1)
      then show ?case
        by fastforce
    qed (simp_all)
  qed
  then show "(t, invalid) \<notin> subtype_rel Tmod"
    by blast
qed

lemma subtype_snd_not_invalid[simp]: "\<And>x. \<not>x \<sqsubseteq>[Tmod] invalid"
  unfolding subtype_def
  by (fact subtype_relation_snd_not_invalid)



section "Definition of fields, attributes and relations"

definition fields :: "'nt type_model \<Rightarrow> 'nt Id \<Rightarrow> ('nt Id \<times> 'nt) set" where
  "fields Tmod c \<equiv> {(d, n) \<in> Field Tmod. \<exclamdown>c \<sqsubseteq>[Tmod] \<exclamdown>d}"

definition "class" :: "'nt type_model \<Rightarrow> 'nt Id \<times> 'nt \<Rightarrow> 'nt Id" where
  "class Tmod f \<equiv> fst f"

definition type :: "'nt type_model \<Rightarrow> 'nt Id \<times> 'nt \<Rightarrow> 'nt TypeDef" where
  "type Tmod f \<equiv> fst (FieldSig Tmod f)"

definition lower :: "'nt type_model \<Rightarrow> 'nt Id \<times> 'nt \<Rightarrow> \<M>" where
  "lower Tmod f \<equiv> Multiplicity.lower (snd (FieldSig Tmod f))"

definition upper :: "'nt type_model \<Rightarrow> 'nt Id \<times> 'nt \<Rightarrow> \<M>" where
  "upper Tmod f \<equiv> Multiplicity.upper (snd (FieldSig Tmod f))"

definition Attr :: "'nt type_model \<Rightarrow> ('nt Id \<times> 'nt) set" where
  "Attr Tmod \<equiv> {f \<in> Field Tmod. type Tmod f \<in> AttrType Tmod}"

definition Rel :: "'nt type_model \<Rightarrow> ('nt Id \<times> 'nt) set" where
  "Rel Tmod \<equiv> Field Tmod - Attr Tmod"

definition Rel_altdef :: "'nt type_model \<Rightarrow> ('nt Id \<times> 'nt) set" where
  "Rel_altdef Tmod \<equiv> {f \<in> Field Tmod. type Tmod f \<in> RelType Tmod}"


subsection "Lemmas on fields, attributes and relations"

lemma fields_truncate_eq: "fields Tmod = fields (truncate Tmod)"
proof
  fix x
  show "fields Tmod x = fields (truncate Tmod) x"
  proof
    show "fields Tmod x \<subseteq> fields (truncate Tmod) x"
    proof
      fix xa
      assume "xa \<in> fields Tmod x"
      then show "xa \<in> fields (truncate Tmod) x"
      proof (induct xa)
        case (Pair a b)
        then have "(a, b) \<in> {(d, n). (d, n) \<in> Field Tmod \<and> \<exclamdown>x \<sqsubseteq>[Tmod] \<exclamdown>d}"
          unfolding fields_def
          by simp
        then have "(a, b) \<in> Field (truncate Tmod) \<and> \<exclamdown>x \<sqsubseteq>[Tmod] \<exclamdown>a"
          unfolding truncate_def
          by simp
        then have "(a, b) \<in> Field (truncate Tmod) \<and> \<exclamdown>x \<sqsubseteq>[truncate Tmod] \<exclamdown>a"
          using subtype_def subtype_rel_truncate_eq
          by blast
        then show ?case
          by (simp add: Type_Model.fields_def)
      qed
    qed
  next
    show "fields (truncate Tmod) x \<subseteq> fields Tmod x"
    proof
      fix xa
      assume "xa \<in> fields (truncate Tmod) x"
      then show "xa \<in> fields Tmod x"
      proof (induct xa)
        case (Pair a b)
        then have "(a, b) \<in> {(d, n). (d, n) \<in> Field (truncate Tmod) \<and> \<exclamdown>x \<sqsubseteq>[truncate Tmod] \<exclamdown>d}"
          unfolding fields_def
          by simp
        then have "(a, b) \<in> Field (truncate Tmod) \<and> \<exclamdown>x \<sqsubseteq>[Tmod] \<exclamdown>a"
          using subtype_def subtype_rel_truncate_eq
          by blast
        then have "(a, b) \<in> Field Tmod \<and> \<exclamdown>x \<sqsubseteq>[Tmod] \<exclamdown>a"
          unfolding truncate_def
          by simp
        then show ?case
          by (simp add: Type_Model.fields_def)
      qed
    qed
  qed
qed

lemma class_truncate_eq: "class Tmod = class (truncate Tmod)"
  unfolding class_def
  by simp

lemma type_func_truncate_eq: "type Tmod = type (truncate Tmod)"
proof
  fix x
  show "type Tmod x = type (truncate Tmod) x"
    unfolding type_def truncate_def
    by simp
qed

lemma lower_truncate_eq: "lower Tmod = lower (truncate Tmod)"
proof
  fix x
  show "lower Tmod x = lower (truncate Tmod) x"
    unfolding lower_def truncate_def
    by simp
qed

lemma upper_truncate_eq: "upper Tmod = upper (truncate Tmod)"
proof
  fix x
  show "upper Tmod x = upper (truncate Tmod) x"
    unfolding upper_def truncate_def
    by simp
qed

lemma attr_truncate_eq: "Attr Tmod = Attr (truncate Tmod)"
proof
  show "Attr Tmod \<subseteq> Attr (truncate Tmod)"
  proof
    fix x
    assume "x \<in> Attr Tmod"
    then have "x \<in> Field (truncate Tmod) \<and> type Tmod x \<in> AttrType Tmod"
      unfolding Attr_def truncate_def
      by simp
    then have "x \<in> Field (truncate Tmod) \<and> type (truncate Tmod) x \<in> AttrType Tmod"
      using type_func_truncate_eq
      by metis
    then have "x \<in> Field (truncate Tmod) \<and> type (truncate Tmod) x \<in> AttrType (truncate Tmod)"
      using attribute_type_truncate_eq
      by blast
    then show "x \<in> Attr (truncate Tmod)"
      by (simp add: Attr_def)
  qed
next
  show "Attr (truncate Tmod) \<subseteq> Attr Tmod"
  proof
    fix x
    assume "x \<in> Attr (truncate Tmod)"
    then have "x \<in> Field Tmod \<and> type (truncate Tmod) x \<in> AttrType (truncate Tmod)"
      unfolding Attr_def truncate_def
      by simp
    then have "x \<in> Field Tmod \<and> type Tmod x \<in> AttrType (truncate Tmod)"
      using type_func_truncate_eq
      by metis
    then have "x \<in> Field Tmod \<and> type Tmod x \<in> AttrType Tmod"
      using attribute_type_truncate_eq
      by blast
    then show "x \<in> Attr Tmod"
      by (simp add: Attr_def)
  qed
qed

lemma rel_truncate_eq: "Rel Tmod = Rel (truncate Tmod)"
  unfolding Rel_def
proof-
  have "Field Tmod - Attr Tmod = Field (truncate Tmod) - Attr Tmod"
    unfolding truncate_def
    by simp
  then show "Field Tmod - Attr Tmod = Field (truncate Tmod) - Attr (truncate Tmod)"
    using attr_truncate_eq
    by blast
qed

lemma rel_definition_alt[simp]:
  assumes fieldsig_wellformed_type: "\<And>f. f \<in> Field Tmod \<Longrightarrow> fst (FieldSig Tmod f) \<in> Type Tmod"
  shows "Rel Tmod = Rel_altdef Tmod"
  unfolding Rel_def Rel_altdef_def Attr_def RelType_def
proof
  show "Field Tmod - {f \<in> Field Tmod. type Tmod f \<in> AttrType Tmod} \<subseteq> {f \<in> Field Tmod. type Tmod f \<in> Type Tmod - AttrType Tmod}"
  proof
    fix x
    assume "x \<in> Field Tmod - {f \<in> Field Tmod. type Tmod f \<in> AttrType Tmod}"
    then show "x \<in> {f \<in> Field Tmod. type Tmod f \<in> Type Tmod - AttrType Tmod}"
      by (simp add: fieldsig_wellformed_type type_def)
  qed
next
  show "{f \<in> Field Tmod. type Tmod f \<in> Type Tmod - AttrType Tmod} \<subseteq> Field Tmod - {f \<in> Field Tmod. type Tmod f \<in> AttrType Tmod}"
  proof
    fix x
    assume "x \<in> {f \<in> Field Tmod. type Tmod f \<in> Type Tmod - AttrType Tmod}"
    then show "x \<in> Field Tmod - {f \<in> Field Tmod. type Tmod f \<in> AttrType Tmod}"
      by blast
  qed
qed

lemma rel_altdef_truncate_eq: "Rel_altdef Tmod = Rel_altdef (truncate Tmod)"
proof
  show "Rel_altdef Tmod \<subseteq> Rel_altdef (truncate Tmod)"
  proof
    fix x
    assume "x \<in> Rel_altdef Tmod"
    then have "x \<in> Field (truncate Tmod) \<and> type Tmod x \<in> RelType Tmod"
      unfolding Rel_altdef_def truncate_def
      by simp
    then have "x \<in> Field (truncate Tmod) \<and> type (truncate Tmod) x \<in> RelType Tmod"
      using type_func_truncate_eq
      by metis
    then have "x \<in> Field (truncate Tmod) \<and> type (truncate Tmod) x \<in> RelType (truncate Tmod)"
      using rel_type_truncate_eq
      by blast
    then show "x \<in> Rel_altdef (truncate Tmod)"
      by (simp add: Rel_altdef_def)
  qed
next
  show "Rel_altdef (truncate Tmod) \<subseteq> Rel_altdef Tmod"
  proof
    fix x
    assume "x \<in> Rel_altdef (truncate Tmod)"
    then have "x \<in> Field Tmod \<and> type (truncate Tmod) x \<in> RelType (truncate Tmod)"
      unfolding Rel_altdef_def truncate_def
      by simp
    then have "x \<in> Field Tmod \<and> type Tmod x \<in> RelType (truncate Tmod)"
      using type_func_truncate_eq
      by metis
    then have "x \<in> Field Tmod \<and> type Tmod x \<in> RelType Tmod"
      using rel_type_truncate_eq
      by blast
    then show "x \<in> Rel_altdef Tmod"
      by (simp add: Rel_altdef_def)
  qed
qed

lemma fields_of_class_are_fields[simp]: "r \<in> fields Tmod c \<Longrightarrow> r \<in> Field Tmod"
  unfolding fields_def
  by blast

lemma fields_of_class_subtype_field_class[simp]: "r \<in> fields Tmod c \<Longrightarrow> \<exclamdown>c \<sqsubseteq>[Tmod] \<exclamdown>(class Tmod r)"
  unfolding fields_def
proof-
  assume "r \<in> {(d, n). (d, n) \<in> Field Tmod \<and> \<exclamdown>c \<sqsubseteq>[Tmod] \<exclamdown>d}"
  then have "\<exclamdown>c \<sqsubseteq>[Tmod] \<exclamdown>(fst r)"
    by force
  then show ?thesis
    by (simp add: class_def)
qed



section "Type model properties"


subsection "Definitions used in properties"

inductive_set UniqueContainerOfClassType :: "'nt type_model \<Rightarrow> 'nt TypeDef set"
  for Tmod :: "'nt type_model"
  where
    rule_setof_class_type: "t \<in> ClassType Tmod \<Longrightarrow> setof t \<in> UniqueContainerOfClassType Tmod" |
    rule_ordof_class_type: "t \<in> ClassType Tmod \<Longrightarrow> ordof t \<in> UniqueContainerOfClassType Tmod"

lemma unique_container_of_class_types_truncate_eq: "UniqueContainerOfClassType Tmod = UniqueContainerOfClassType (truncate Tmod)"
proof
  show "UniqueContainerOfClassType Tmod \<subseteq> UniqueContainerOfClassType (truncate Tmod)"
  proof
    fix x
    assume "x \<in> UniqueContainerOfClassType Tmod"
    then show "x \<in> UniqueContainerOfClassType (truncate Tmod)"
    proof (induct)
      case (rule_setof_class_type t)
      then show ?case
        using UniqueContainerOfClassType.rule_setof_class_type class_type_truncate_eq
        by blast
    next
      case (rule_ordof_class_type t)
      then show ?case
        using UniqueContainerOfClassType.rule_ordof_class_type class_type_truncate_eq
        by blast
    qed
  qed
next
  show "UniqueContainerOfClassType (truncate Tmod) \<subseteq> UniqueContainerOfClassType Tmod"
  proof
    fix x
    assume "x \<in> UniqueContainerOfClassType (truncate Tmod)"
    then show "x \<in> UniqueContainerOfClassType Tmod"
    proof (induct)
      case (rule_setof_class_type t)
      then show ?case
        using UniqueContainerOfClassType.rule_setof_class_type class_type_truncate_eq
        by blast
    next
      case (rule_ordof_class_type t)
      then show ?case
        using UniqueContainerOfClassType.rule_ordof_class_type class_type_truncate_eq
        by blast
    qed
  qed
qed

lemma unique_container_of_class_types_are_relations: "UniqueContainerOfClassType Tmod \<subseteq> RelType Tmod"
proof
  fix x assume "x \<in> UniqueContainerOfClassType Tmod" then show "x \<in> RelType Tmod"
  proof (induct)
    case (rule_setof_class_type t)
    then show ?case
      by (simp add: RelType_altdef.rule_class_types RelType_altdef.rule_setof_relations)
  next
    case (rule_ordof_class_type t)
    then show ?case
      by (simp add: RelType_altdef.rule_class_types RelType_altdef.rule_ordof_relations)
  qed
qed

lemma unique_container_of_class_types_are_unique_containers: "UniqueContainerOfClassType Tmod \<subseteq> UniqueContainerType Tmod"
proof
  fix x assume "x \<in> UniqueContainerOfClassType Tmod" then show "x \<in> UniqueContainerType Tmod"
  proof (induct)
    case (rule_setof_class_type t)
    then show ?case 
      unfolding UniqueContainerType_def 
      using type_subset_class_type SetContainerType.rule_setof_all_type 
      by blast
  next
    case (rule_ordof_class_type t)
    then show ?case 
      unfolding UniqueContainerType_def 
      using type_subset_class_type OrdContainerType.rule_ordof_all_type 
      by blast
  qed
qed

lemma unique_container_of_class_types_are_container_types: "UniqueContainerOfClassType Tmod \<subseteq> ContainerType Tmod"
proof
  fix x assume "x \<in> UniqueContainerOfClassType Tmod" then show "x \<in> ContainerType Tmod"
  proof (induct)
    case (rule_setof_class_type t)
    then show ?case
      using ContainerType.rule_setof_type non_container_type_subset_class_type by blast
  next
    case (rule_ordof_class_type t)
    then show ?case
      using ContainerType.rule_ordof_type non_container_type_subset_class_type by blast
  qed
qed


subsection "Definition of set of valid properties"

inductive_set Property :: "('nt) type_model \<Rightarrow> ('nt PropertyDef) set"
  for Tmod :: "('nt) type_model"
  where
    abstract_property: "c \<in> Class Tmod \<Longrightarrow> abstract c \<in> Property Tmod" |
    containment_property: "r \<in> Rel Tmod \<Longrightarrow> containment r \<in> Property Tmod" |
    default_value_property: "f \<in> Field Tmod \<Longrightarrow> v \<in> Constant Tmod \<Longrightarrow> 
      ConstType Tmod v \<sqsubseteq>[Tmod] (type Tmod f) \<Longrightarrow> defaultValue f v \<in> Property Tmod" |
    identity_property: "c \<in> Class Tmod \<Longrightarrow> A \<subseteq> fields Tmod c \<Longrightarrow> identity c A \<in> Property Tmod" |
    keyset_property: "r \<in> Rel Tmod \<Longrightarrow> A \<subseteq> Attr Tmod \<Longrightarrow> 
      (\<forall>f. f \<in> A \<longrightarrow> (uncontainer (type Tmod r) \<sqsubseteq>[Tmod] \<exclamdown>(class Tmod f))) \<Longrightarrow>
      type Tmod r \<in> UniqueContainerOfClassType Tmod \<Longrightarrow> keyset r A \<in> Property Tmod" |
    opposite_property: "r1 \<in> Rel Tmod \<Longrightarrow> r2 \<in> Rel Tmod \<Longrightarrow> r1 \<noteq> r2 \<Longrightarrow> 
      \<exclamdown>(class Tmod r1) = uncontainer (type Tmod r2) \<Longrightarrow> \<exclamdown>(class Tmod r2) = uncontainer (type Tmod r1) \<Longrightarrow> 
      type Tmod r1 \<notin> NonUniqueContainerType Tmod \<Longrightarrow> type Tmod r2 \<notin> NonUniqueContainerType Tmod \<Longrightarrow> 
      opposite r1 r2 \<in> Property Tmod" |
    readonly_property: "f \<in> Field Tmod \<Longrightarrow> readonly f \<in> Property Tmod"

lemma properties_truncate_eq: "Property Tmod = Property (truncate Tmod)"
proof
  show "Property Tmod \<subseteq> Property (truncate Tmod)"
  proof
    fix x
    assume "x \<in> Property Tmod"
    then show "x \<in> Property (truncate Tmod)"
    proof (induct)
      case (abstract_property c)
      then show ?case
        unfolding truncate_def
        by (simp add: Property.abstract_property)
    next
      case (containment_property r)
      then show ?case
        using Property.containment_property rel_truncate_eq
        by blast
    next
      case (default_value_property f v)
      then have "ConstType Tmod v \<sqsubseteq>[truncate Tmod] type Tmod f"
        using subtype_def subtype_rel_truncate_eq
        by blast
      then have "ConstType Tmod v \<sqsubseteq>[truncate Tmod] type (truncate Tmod) f"
        using type_func_truncate_eq
        by metis
      then show ?case
        unfolding truncate_def
        by (simp add: Property.default_value_property default_value_property.hyps(1) default_value_property.hyps(2))
    next
      case (identity_property c A)
      then have "A \<subseteq> fields (truncate Tmod) c"
        using fields_truncate_eq
        by metis
      then show ?case
        unfolding truncate_def
        by (simp add: Property.identity_property identity_property.hyps(1))
    next
      case (keyset_property r A)
      then show ?case
        using Property.keyset_property attr_truncate_eq class_truncate_eq rel_truncate_eq subtype_def subtype_rel_truncate_eq type_func_truncate_eq unique_container_of_class_types_truncate_eq
        by metis
    next
      case (opposite_property r1 r2)
      then show ?case
        using Property.opposite_property class_truncate_eq non_unique_container_type_truncate_eq rel_truncate_eq type_func_truncate_eq
        by metis
    next
      case (readonly_property f)
      then show ?case
        unfolding truncate_def
        by (simp add: Property.readonly_property)
    qed
  qed
next
  show "Property (truncate Tmod) \<subseteq> Property Tmod"
  proof
    fix x
    assume "x \<in> Property (truncate Tmod)"
    then show "x \<in> Property Tmod"
    proof (induct)
      case (abstract_property c)
      then show ?case
        unfolding truncate_def
        by (simp add: Property.abstract_property)
    next
      case (containment_property r)
      then show ?case
        using Property.containment_property rel_truncate_eq
        by blast
    next
      case (default_value_property f v)
      then have "ConstType (truncate Tmod) v \<sqsubseteq>[Tmod] type (truncate Tmod) f"
        using subtype_def subtype_rel_truncate_eq
        by blast
      then have "ConstType (truncate Tmod) v \<sqsubseteq>[Tmod] type Tmod f"
        using type_func_truncate_eq
        by metis
      then show ?case
        using default_value_property.hyps(1) default_value_property.hyps(2)
        unfolding truncate_def
        by (simp add: Property.default_value_property)
    next
      case (identity_property c A)
      then have "A \<subseteq> fields Tmod c"
        using fields_truncate_eq
        by metis
      then show ?case
        using identity_property.hyps(1)
        unfolding truncate_def
        by (simp add: Property.identity_property)
    next
      case (keyset_property r A)
      then show ?case
        using Property.keyset_property attr_truncate_eq class_truncate_eq rel_truncate_eq subtype_def subtype_rel_truncate_eq type_func_truncate_eq unique_container_of_class_types_truncate_eq
        by metis
    next
      case (opposite_property r1 r2)
      then show ?case
        using Property.opposite_property class_truncate_eq non_unique_container_type_truncate_eq rel_truncate_eq type_func_truncate_eq
        by metis
    next
      case (readonly_property f)
      then show ?case
        unfolding truncate_def
        by (simp add: Property.readonly_property)
    qed
  qed
qed

lemma properties_rev_impl_abstract: "abstract c \<in> Property Tmod \<Longrightarrow> c \<in> Class Tmod"
proof-
  fix c
  assume "abstract c \<in> Property Tmod"
  then show "c \<in> Class Tmod"
  proof (cases)
    case abstract_property
    then show ?thesis
      by blast
  qed
qed

lemma properties_rev_impl_containment: "containment r \<in> Property Tmod \<Longrightarrow> r \<in> Rel Tmod"
proof-
  fix r
  assume "containment r \<in> Property Tmod"
  then show "r \<in> Rel Tmod"
  proof (cases)
    case containment_property
    then show ?thesis
      by blast
  qed
qed

lemma properties_rev_impl_default_value: "defaultValue f v \<in> Property Tmod \<Longrightarrow> f \<in> Field Tmod \<and> v \<in> Constant Tmod \<and> ConstType Tmod v \<sqsubseteq>[Tmod] (type Tmod f)"
proof-
  fix f v
  assume "defaultValue f v \<in> Property Tmod"
  then show "f \<in> Field Tmod \<and> v \<in> Constant Tmod \<and> ConstType Tmod v \<sqsubseteq>[Tmod] (type Tmod f)"
  proof (cases)
    case default_value_property
    then show ?thesis
      by blast
  qed
qed

lemma properties_rev_impl_identity: "identity c A \<in> Property Tmod \<Longrightarrow> c \<in> Class Tmod \<and> A \<subseteq> fields Tmod c"
proof-
  fix c A
  assume "identity c A \<in> Property Tmod"
  then show "c \<in> Class Tmod \<and> A \<subseteq> fields Tmod c"
  proof (cases)
    case identity_property
    then show ?thesis
      by blast
  qed
qed

lemma properties_rev_impl_keyset: "keyset r A \<in> Property Tmod \<Longrightarrow> r \<in> Rel Tmod \<and> A \<subseteq> Attr Tmod \<and> 
      (\<forall>f. f \<in> A \<longrightarrow> (uncontainer (type Tmod r) \<sqsubseteq>[Tmod] \<exclamdown>(class Tmod f))) \<and>
      type Tmod r \<in> UniqueContainerOfClassType Tmod"
proof-
  fix r A
  assume "keyset r A \<in> Property Tmod"
  then show "r \<in> Rel Tmod \<and> A \<subseteq> Attr Tmod \<and> 
      (\<forall>f. f \<in> A \<longrightarrow> (uncontainer (type Tmod r) \<sqsubseteq>[Tmod] \<exclamdown>(class Tmod f))) \<and>
      type Tmod r \<in> UniqueContainerOfClassType Tmod"
  proof (cases)
    case keyset_property
    then show ?thesis
      by blast
  qed
qed

lemma properties_rev_impl_opposite: "opposite r1 r2 \<in> Property Tmod \<Longrightarrow> r1 \<in> Rel Tmod \<and> r2 \<in> Rel Tmod \<and> r1 \<noteq> r2 \<and> 
      \<exclamdown>(class Tmod r1) = uncontainer (type Tmod r2) \<and> \<exclamdown>(class Tmod r2) = uncontainer (type Tmod r1) \<and> 
      type Tmod r1 \<notin> NonUniqueContainerType Tmod \<and> type Tmod r2 \<notin> NonUniqueContainerType Tmod"
proof-
  fix r1 r2
  assume "opposite r1 r2 \<in> Property Tmod"
  then show "r1 \<in> Rel Tmod \<and> r2 \<in> Rel Tmod \<and> r1 \<noteq> r2 \<and>
      \<exclamdown>(class Tmod r1) = uncontainer (type Tmod r2) \<and> \<exclamdown>(class Tmod r2) = uncontainer (type Tmod r1) \<and> 
      type Tmod r1 \<notin> NonUniqueContainerType Tmod \<and> type Tmod r2 \<notin> NonUniqueContainerType Tmod"
  proof (cases)
    case opposite_property
    then show ?thesis
      by blast
  qed
qed

lemma properties_rev_impl_readonly: "readonly f \<in> Property Tmod \<Longrightarrow> f \<in> Field Tmod"
proof-
  fix f
  assume "readonly f \<in> Property Tmod"
  then show "f \<in> Field Tmod"
  proof (cases)
    case readonly_property
    then show ?thesis
      by blast
  qed
qed


subsection "Definition of the set of containment relations"

inductive_set CR :: "'nt type_model \<Rightarrow> ('nt Id \<times> 'nt) set"
  for Tmod :: "'nt type_model"
  where
    rule_containment_relations: "r \<in> Rel Tmod \<Longrightarrow> containment r \<in> Prop Tmod \<Longrightarrow> r \<in> CR Tmod"

lemma containment_relations_are_relations: "CR Tmod \<subseteq> Rel Tmod"
proof
  fix x
  assume "x \<in> CR Tmod"
  then show "x \<in> Rel Tmod"
    by (induct) (simp_all)
qed

lemma containment_relations_are_fields: "CR Tmod \<subseteq> Field Tmod"
  using containment_relations_are_relations
  unfolding Rel_def
  by blast


section "Type model consistency"

locale type_model = fixes Tmod :: "('nt) type_model"
  assumes structure_field_wellformed_class: "\<And>f. f \<in> Field Tmod \<Longrightarrow> fst f \<in> Class Tmod"
  assumes structure_fieldsig_wellformed: "\<And>f. f \<in> Field Tmod \<Longrightarrow> fst (FieldSig Tmod f) \<in> Type Tmod \<and> multiplicity (snd (FieldSig Tmod f))"
  assumes structure_fieldsig_domain[simp]: "\<And>f. f \<notin> Field Tmod \<Longrightarrow> FieldSig Tmod f = undefined"
  assumes structure_enumvalue_wellformed_enum: "\<And>ev. ev \<in> EnumValue Tmod \<Longrightarrow> fst ev \<in> Enum Tmod"
  assumes structure_inh_wellformed_classes: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
  assumes structure_properties_wellfomed: "\<And>p. p \<in> Prop Tmod \<Longrightarrow> p \<in> Property Tmod"
  assumes structure_consttype_wellformed[simp]: "\<And>c. c \<in> Constant Tmod \<Longrightarrow> ConstType Tmod c \<in> Type Tmod"
  assumes structure_consttype_domain[simp]: "\<And>c. c \<notin> Constant Tmod \<Longrightarrow> ConstType Tmod c = undefined"
  assumes property_class_disjoint: "\<And>c. c \<in> Class Tmod \<Longrightarrow> c \<notin> Enum Tmod \<and> c \<notin> UserDataType Tmod"
  assumes property_enum_disjoint: "\<And>e. e \<in> Enum Tmod \<Longrightarrow> e \<notin> Class Tmod \<and> e \<notin> UserDataType Tmod"
  assumes property_userdatatype_disjoint: "\<And>u. u \<in> UserDataType Tmod \<Longrightarrow> u \<notin> Class Tmod \<and> u \<notin> Enum Tmod"
  assumes property_namespace_restriction: "\<And>x y. x \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod \<Longrightarrow> y \<in> Class Tmod \<union> Enum Tmod \<union> UserDataType Tmod \<Longrightarrow> \<not>id_in_ns x (Identifier y)"
  assumes property_inh_wellformed_relation: "asym (Inh Tmod) \<and> irrefl ((Inh Tmod)\<^sup>+)"
  assumes consistency_lower_multiplicity_non_nullable: "\<And>f. f \<in> Field Tmod \<and> type Tmod f \<in> DataType \<union> EnumType Tmod \<union> UserDataTypeType Tmod \<union> ProperClassType Tmod \<Longrightarrow> lower Tmod f = \<^bold>1"
  assumes consistency_lower_multiplicity_nullable[simp]: "\<And>f. f \<in> Field Tmod \<and> type Tmod f \<in> NullableClassType Tmod \<Longrightarrow> lower Tmod f = \<^bold>0"
  assumes consistency_upper_multiplicity_non_container: "\<And>f. f \<in> Field Tmod \<and> type Tmod f \<in> NonContainerType Tmod \<Longrightarrow> upper Tmod f = \<^bold>1"
  assumes consistency_containment_upper[simp]: "\<And>r1 r2. containment r1 \<in> Prop Tmod \<and> opposite r1 r2 \<in> Prop Tmod \<Longrightarrow> upper Tmod r2 = \<^bold>1"
  assumes consistency_defaultvalue_unique[simp]: "\<And>f. defaultValue f v1 \<in> Prop Tmod \<and> defaultValue f v2 \<in> Prop Tmod \<Longrightarrow> v1 = v2"
  assumes consistency_identity_valid[simp]: "\<And>c1 c2. identity c1 A \<in> Prop Tmod \<Longrightarrow> identity c2 B \<in> Prop Tmod \<Longrightarrow> \<exclamdown>c1 \<sqsubseteq>[Tmod] \<exclamdown>c2 \<Longrightarrow> A \<subseteq> B"
  assumes consistency_keyset_unique[simp]: "\<And>r. keyset r A1 \<in> Prop Tmod \<and> keyset r A2 \<in> Prop Tmod \<Longrightarrow> A1 = A2"
  assumes consistency_opposite_unique[simp]: "\<And>r. opposite r r1 \<in> Prop Tmod \<and> opposite r r2 \<in> Prop Tmod \<Longrightarrow> r1 = r2"
  assumes consistency_opposite_sym[simp]: "opposite r1 r2 \<in> Prop Tmod \<Longrightarrow> opposite r2 r1 \<in> Prop Tmod"

context type_model
begin

subsection "Lemmas on structure of a type model"

lemma structure_field_wellformed_class_alt[simp]: "\<And>c. (c, n) \<in> Field Tmod \<Longrightarrow> c \<in> Class Tmod"
  using structure_field_wellformed_class by auto

lemma structure_fieldsig_wellformed_type[simp]: "\<And>f. f \<in> Field Tmod \<Longrightarrow> fst (FieldSig Tmod f) \<in> Type Tmod"
  by (simp only: structure_fieldsig_wellformed)

lemma structure_fieldsig_wellformed_multiplicity[simp]: "\<And>f. f \<in> Field Tmod \<Longrightarrow> multiplicity (snd (FieldSig Tmod f))"
  by (simp only: structure_fieldsig_wellformed)

lemma structure_fieldsig_wellformed_alt[simp]: "\<And>f. f \<in> Field Tmod \<Longrightarrow> (t, m) = FieldSig Tmod f \<Longrightarrow> t \<in> Type Tmod \<and> multiplicity m"
proof
  fix f
  assume f_in_fields: "f \<in> type_model.Field Tmod"
  have "\<And>x1 x2. fst (x1, x2) = x1" by simp
  then show "(t, m) = FieldSig Tmod f \<Longrightarrow> t \<in> Type Tmod"
    using f_in_fields structure_fieldsig_wellformed_type
    by metis
  have "\<And>x1 x2. snd (x1, x2) = x2" by simp
  then show "(t, m) = FieldSig Tmod f \<Longrightarrow> multiplicity m"
    using f_in_fields structure_fieldsig_wellformed_multiplicity
    by metis
qed

lemma structure_fieldsig_wellformed_type_alt[simp]: "\<And>f. f \<in> Field Tmod \<Longrightarrow> (t, m) = FieldSig Tmod f \<Longrightarrow> t \<in> Type Tmod"
  by simp

lemma structure_fieldsig_wellformed_multiplicity_alt[simp]: "\<And>f. f \<in> Field Tmod \<Longrightarrow> (t, m) = FieldSig Tmod f \<Longrightarrow> multiplicity m"
  by simp

lemma structure_enumvalue_wellformed_alt[simp]: "\<And>e. (e, n) \<in> EnumValue Tmod \<Longrightarrow> e \<in> Enum Tmod"
  using structure_enumvalue_wellformed_enum by auto

lemma structure_inh_wellformed_fst_class: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod"
  by (simp only: structure_inh_wellformed_classes)

lemma structure_inh_wellformed_snd_class: "\<And>c. c \<in> Inh Tmod \<Longrightarrow> snd c \<in> Class Tmod"
  by (simp only: structure_inh_wellformed_classes)

lemma structure_inh_wellformed_alt: "\<And>c1 c2. (c1, c2) \<in> Inh Tmod \<Longrightarrow> c1 \<in> Class Tmod \<and> c2 \<in> Class Tmod"
  using structure_inh_wellformed_fst_class structure_inh_wellformed_snd_class by auto


subsection "Lemmas on the properties of a type model"

lemma property_class_enum_disjoint[simp]: "Class Tmod \<inter> Enum Tmod = {}"
  using property_class_disjoint by auto

lemma property_class_userdatatype_disjoint[simp]: "Class Tmod \<inter> UserDataType Tmod = {}"
  using property_class_disjoint by auto

lemma property_enum_userdatatype_disjoint[simp]: "Enum Tmod \<inter> UserDataType Tmod = {}"
  using property_enum_disjoint by auto

lemma property_inh_wellformed_asym[simp]: "asym (Inh Tmod)"
  by (simp add: property_inh_wellformed_relation)

lemma property_inh_wellformed_trancl_irrefl[simp]: "irrefl ((Inh Tmod)\<^sup>+)"
  by (simp only: property_inh_wellformed_relation)

lemma property_inh_wellformed_irrefl[simp]: "irrefl (Inh Tmod)"
  using asym.simps property_inh_wellformed_asym by blast

lemma property_inh_wellformed_irrefl_alt[simp]: "\<And>c. (c, c) \<notin> Inh Tmod"
  using asym.cases property_inh_wellformed_asym by blast


subsection "Lemmas on the consistency of a type model"

lemma consistency_lower_multiplicity_datatypes[simp]: "\<And>f. f \<in> Field Tmod \<and> type Tmod f \<in> DataType \<Longrightarrow> lower Tmod f = \<^bold>1"
  by (simp add: consistency_lower_multiplicity_non_nullable)

lemma consistency_lower_multiplicity_enumtype[simp]: "\<And>f. f \<in> Field Tmod \<and> type Tmod f \<in> EnumType Tmod \<Longrightarrow> lower Tmod f = \<^bold>1"
  by (simp add: consistency_lower_multiplicity_non_nullable)

lemma consistency_lower_multiplicity_userdatatypes[simp]: "\<And>f. f \<in> Field Tmod \<and> type Tmod f \<in> UserDataTypeType Tmod \<Longrightarrow> lower Tmod f = \<^bold>1"
  by (simp add: consistency_lower_multiplicity_non_nullable)

lemma consistency_lower_multiplicity_proper_classes[simp]: "\<And>f. f \<in> Field Tmod \<and> type Tmod f \<in> ProperClassType Tmod \<Longrightarrow> lower Tmod f = \<^bold>1"
  by (simp add: consistency_lower_multiplicity_non_nullable)

lemma consistency_identity_unique[simp]: "\<And>c. identity c A \<in> Prop Tmod \<and> identity c B \<in> Prop Tmod \<Longrightarrow> A = B"
proof
  fix c
  assume identities: "identity c A \<in> Prop Tmod \<and> identity c B \<in> Prop Tmod"
  have identity_a: "identity c A \<in> Prop Tmod"
    by (simp add: identities)
  have identity_b: "identity c B \<in> Prop Tmod"
    by (simp add: identities)
  have c_in_class_tmod: "c \<in> Class Tmod"
    using identities properties_rev_impl_identity structure_properties_wellfomed
    by blast
  have c_extends_c: "\<exclamdown>c \<sqsubseteq>[Tmod] \<exclamdown>c"
    by (simp add: ClassType_def NonContainerType_def ProperClassType.rule_proper_classes Type_def c_in_class_tmod subtype_def subtype_rel.reflexivity)
  show "A \<subseteq> B"
    using c_extends_c identity_a identity_b consistency_identity_valid
    by blast
  show "B \<subseteq> A"
    using c_extends_c identity_a identity_b consistency_identity_valid
    by blast
qed

end


subsection "Lemmas on the type sets"

lemma inh_fst_element_proper_class[simp]: "\<And>c1 c2. type_model Tmod \<Longrightarrow> (c1, c2) \<in> Inh Tmod \<Longrightarrow> \<exclamdown>c1 \<in> ProperClassType Tmod"
  by (simp add: ProperClassType.rule_proper_classes type_model.structure_inh_wellformed_alt)

lemma inh_snd_element_proper_class[simp]: "\<And>c1 c2. type_model Tmod \<Longrightarrow> (c1, c2) \<in> Inh Tmod \<Longrightarrow> \<exclamdown>c2 \<in> ProperClassType Tmod"
  by (simp add: ProperClassType.rule_proper_classes type_model.structure_inh_wellformed_alt)

lemma inh_fst_element_nullable_class[simp]: "\<And>c1 c2. type_model Tmod \<Longrightarrow> (c1, c2) \<in> Inh Tmod \<Longrightarrow> \<questiondown>c1 \<in> NullableClassType Tmod"
  by (simp add: NullableClassType.rule_nullable_classes type_model.structure_inh_wellformed_alt)

lemma inh_snd_element_nullable_class[simp]: "\<And>c1 c2. type_model Tmod \<Longrightarrow> (c1, c2) \<in> Inh Tmod \<Longrightarrow> \<questiondown>c2 \<in> NullableClassType Tmod"
  by (simp add: NullableClassType.rule_nullable_classes type_model.structure_inh_wellformed_alt)


subsection "Lemmas on the subtype relation of a consistent type model"

lemma subtype_relation_domain_alt[simp]:
  assumes valid_type_model: "type_model Tmod"
  shows "Domain (subtype_rel Tmod) = Type Tmod"
  by (simp add: subtype_relation_domain type_model.structure_inh_wellformed_classes valid_type_model)

lemma subtype_relation_range_alt[simp]:
  assumes valid_type_model: "type_model Tmod"
  shows "Range (subtype_rel Tmod) = Type Tmod"
  by (simp add: subtype_relation_range type_model.structure_inh_wellformed_classes valid_type_model)

lemma subtype_relation_field_alt[simp]:
  assumes valid_type_model: "type_model Tmod"
  shows "Relation.Field (subtype_rel Tmod) = Type Tmod"
  by (simp add: subtype_relation_field type_model.structure_inh_wellformed_classes valid_type_model)

lemma subtype_relation_reflexive_alt[simp]:
  assumes valid_type_model: "type_model Tmod"
  shows "Refl (subtype_rel Tmod)"
  using subtype_relation_reflexive type_model.structure_inh_wellformed_classes valid_type_model
  by blast

lemma subtype_relation_transitive_alt[simp]:
  assumes valid_type_model: "type_model Tmod"
  shows "trans (subtype_rel Tmod)"
  using subtype_relation_transitive type_model.structure_inh_wellformed_classes valid_type_model
  by blast

lemma subtype_relation_antisymmetric_alt[simp]:
  assumes valid_type_model: "type_model Tmod"
  shows "antisym (subtype_rel Tmod)"
proof (intro subtype_relation_antisymmetric)
  show "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
    using valid_type_model type_model.structure_inh_wellformed_classes
    by blast
  show "irrefl ((Inh Tmod)\<^sup>+)"
    using valid_type_model
    by (fact type_model.property_inh_wellformed_trancl_irrefl)
qed

lemma subtype_relation_partial_order_alt[simp]:
  assumes valid_type_model: "type_model Tmod"
  shows "Partial_order (subtype_rel Tmod)"
proof (intro subtype_relation_partial_order)
  show "\<And>c. c \<in> Inh Tmod \<Longrightarrow> fst c \<in> Class Tmod \<and> snd c \<in> Class Tmod"
    using valid_type_model type_model.structure_inh_wellformed_classes
    by blast
  show "irrefl ((Inh Tmod)\<^sup>+)"
    using valid_type_model
    by (fact type_model.property_inh_wellformed_trancl_irrefl)
qed

lemma inh_proper_classes_transitive[simp]: "\<And>c1 c2 c3. type_model Tmod \<Longrightarrow> (c1, c2) \<in> Inh Tmod \<Longrightarrow> (c2, c3) \<in> Inh Tmod \<Longrightarrow> \<exclamdown>c1 \<sqsubseteq>[Tmod] \<exclamdown>c3"
  unfolding subtype_def
proof-
  fix c1 c2 c3
  assume consistent_type_model: "type_model Tmod"
  assume c1_extends_c2: "(c1, c2) \<in> Inh Tmod"
  assume c2_extends_c3: "(c2, c3) \<in> Inh Tmod"
  have c1_subtype_c2: "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_rel Tmod"
    using c1_extends_c2 by (rule subtype_rel.generalization_of_inheritance_proper)
  have c2_subtype_c3: "(\<exclamdown>c2, \<exclamdown>c3) \<in> subtype_rel Tmod"
    using c2_extends_c3 by (rule subtype_rel.generalization_of_inheritance_proper)
  have c1_in_types: "\<exclamdown>c1 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def
    using c1_extends_c2 consistent_type_model 
    by simp
  have c2_in_types: "\<exclamdown>c2 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def
    using c1_extends_c2 consistent_type_model 
    by simp
  have c3_in_types: "\<exclamdown>c3 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def
    using c2_extends_c3 consistent_type_model 
    by simp
  show "(\<exclamdown>c1, \<exclamdown>c3) \<in> subtype_rel Tmod"
    using c1_in_types c1_subtype_c2 c2_in_types c2_subtype_c3 c3_in_types subtype_rel.transitivity by auto
qed

lemma inh_nullable_classes_transitive[simp]: "\<And>c1 c2 c3. type_model Tmod \<Longrightarrow> (c1, c2) \<in> Inh Tmod \<Longrightarrow> (c2, c3) \<in> Inh Tmod \<Longrightarrow> \<questiondown>c1 \<sqsubseteq>[Tmod] \<questiondown>c3"
  unfolding subtype_def
proof-
  fix c1 c2 c3
  assume consistent_type_model: "type_model Tmod"
  assume c1_extends_c2: "(c1, c2) \<in> Inh Tmod"
  assume c2_extends_c3: "(c2, c3) \<in> Inh Tmod"
  have c1_subtype_c2: "(\<questiondown>c1, \<questiondown>c2) \<in> subtype_rel Tmod"
    using c1_extends_c2 by (rule subtype_rel.generalization_of_inheritance_nullable)
  have c2_subtype_c3: "(\<questiondown>c2, \<questiondown>c3) \<in> subtype_rel Tmod"
    using c2_extends_c3 by (rule subtype_rel.generalization_of_inheritance_nullable)
  have c1_in_types: "\<questiondown>c1 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def
    using c1_extends_c2 consistent_type_model 
    by simp
  have c2_in_types: "\<questiondown>c2 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def
    using c1_extends_c2 consistent_type_model 
    by simp
  have c3_in_types: "\<questiondown>c3 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def
    using c2_extends_c3 consistent_type_model 
    by simp
  show "(\<questiondown>c1, \<questiondown>c3) \<in> subtype_rel Tmod"
    using c1_in_types c1_subtype_c2 c2_in_types c2_subtype_c3 c3_in_types subtype_rel.transitivity by auto
qed

lemma inh_proper_nullable_transitive[simp]: "\<And>c1 c2. type_model Tmod \<Longrightarrow> (c1, c2) \<in> Inh Tmod \<Longrightarrow> \<exclamdown>c1 \<sqsubseteq>[Tmod] \<questiondown>c2"
  unfolding subtype_def
proof-
  fix c1 c2
  assume consistent_type_model: "type_model Tmod"
  assume c1_extends_c2: "(c1, c2) \<in> Inh Tmod" 
  have c2_proper_nullable: "(\<exclamdown>c2, \<questiondown>c2) \<in> subtype_rel Tmod" 
    using c1_extends_c2 consistent_type_model subtype_rel.nullable_proper_classes type_model.structure_inh_wellformed_alt by blast
  have c1_subtype_c2: "(\<exclamdown>c1, \<exclamdown>c2) \<in> subtype_rel Tmod"
    using c1_extends_c2 by (rule subtype_rel.generalization_of_inheritance_proper)
  have proper_c1_in_types: "\<exclamdown>c1 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def 
    using c1_extends_c2 consistent_type_model 
    by simp
  have proper_c2_in_types: "\<exclamdown>c2 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def 
    using c1_extends_c2 consistent_type_model 
    by simp
  have nullable_c2_in_types: "\<questiondown>c2 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def 
    using c1_extends_c2 consistent_type_model 
    by simp
  show "(\<exclamdown>c1, \<questiondown>c2) \<in> subtype_rel Tmod"
    using proper_c1_in_types proper_c2_in_types nullable_c2_in_types c1_subtype_c2 c2_proper_nullable
    by (rule subtype_rel.transitivity)
qed

lemma inh_classes_transitive[simp]: "\<And>c1 c2 c3. type_model Tmod \<Longrightarrow> (c1, c2) \<in> Inh Tmod \<Longrightarrow> (c2, c3) \<in> Inh Tmod \<Longrightarrow> \<exclamdown>c1 \<sqsubseteq>[Tmod] \<questiondown>c3"
  unfolding subtype_def
proof-
  fix c1 c2 c3
  assume consistent_type_model: "type_model Tmod"
  assume c1_extends_c2: "(c1, c2) \<in> Inh Tmod"
  assume c2_extends_c3: "(c2, c3) \<in> Inh Tmod"
  have c1_subtype_c3: "(\<exclamdown>c1, \<exclamdown>c3) \<in> subtype_rel Tmod"
    using c1_extends_c2 c2_extends_c3 consistent_type_model inh_proper_classes_transitive subtype_def by blast
  have c2_subtype_nullable_c3: "(\<exclamdown>c2, \<questiondown>c3) \<in> subtype_rel Tmod"
    using c2_extends_c3 consistent_type_model inh_proper_nullable_transitive subtype_def by blast
  have proper_c1_in_types: "\<exclamdown>c1 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def 
    using c1_extends_c2 consistent_type_model 
    by simp
  have proper_c2_in_types: "\<exclamdown>c2 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def
    using c1_extends_c2 consistent_type_model 
    by simp
  have nullable_c2_in_types: "\<questiondown>c3 \<in> Type Tmod" 
    unfolding Type_def NonContainerType_def ClassType_def
    using c2_extends_c3 consistent_type_model
    by simp
  show "(\<exclamdown>c1, \<questiondown>c3) \<in> subtype_rel Tmod"
    using c1_extends_c2 c2_subtype_nullable_c3 nullable_c2_in_types proper_c1_in_types proper_c2_in_types subtype_rel.generalization_of_inheritance_proper subtype_rel.transitivity by blast
qed



section "Validity of trivial type models"

definition tmod_empty :: "('nt) type_model" where
  [simp]: "tmod_empty = \<lparr>
    Class = {},
    Enum = {},
    UserDataType = {},
    Field = {},
    FieldSig = (\<lambda>x. undefined),
    EnumValue = {},
    Inh = {},
    Prop = {},
    Constant = {},
    ConstType = (\<lambda>x. undefined)
  \<rparr>"

lemma tmod_empty_correct[simp]: "type_model tmod_empty"
  by (intro type_model.intro) (simp_all add: asym.intros irrefl_def)

end