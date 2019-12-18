theory Instance_Model
  imports 
    Main
    HOL.Complex
    Model_Namespace
    Type_Model
begin

section "Type definitions"

datatype ('o, 'nt) ValueDef = bool bool | int int | real real | string string | enum "'nt Id \<times> 'nt" | data string | obj 'o | nil | bagof "('o, 'nt) ValueDef list" | setof "('o, 'nt) ValueDef list" | seqof "('o, 'nt) ValueDef list" | ordof "('o, 'nt) ValueDef list" | unspecified | invalid

fun contained_list :: "('o, 'nt) ValueDef \<Rightarrow> ('o, 'nt) ValueDef list" where
  "contained_list (bagof xs) = xs" |
  "contained_list (setof xs) = xs" |
  "contained_list (seqof xs) = xs" |
  "contained_list (ordof xs) = xs" |
  "contained_list x = [x]"

fun contained_values :: "('o, 'nt) ValueDef \<Rightarrow> ('o, 'nt) ValueDef list" where
  "contained_values (bagof []) = []" |
  "contained_values (bagof (x#xs)) = contained_values x @ contained_values (bagof xs)" |
  "contained_values (setof []) = []" |
  "contained_values (setof (x#xs)) = contained_values x @ contained_values (setof xs)" |
  "contained_values (seqof []) = []" |
  "contained_values (seqof (x#xs)) = contained_values x @ contained_values (seqof xs)" |
  "contained_values (ordof []) = []" |
  "contained_values (ordof (x#xs)) = contained_values x @ contained_values (ordof xs)" |
  "contained_values x = [x]"


section "Instance model tuple definition"

record ('o, 'nt) instance_model =
  Tm :: "('nt) type_model"
  Object :: "'o set"
  ObjectClass :: "'o \<Rightarrow> 'nt Id"
  ObjectId :: "'o \<Rightarrow> 'nt"
  FieldValue :: "('o \<times> ('nt Id \<times> 'nt)) \<Rightarrow> ('o, 'nt) ValueDef"
  DefaultValue :: "'nt Id \<Rightarrow> ('o, 'nt) ValueDef"



section "Values"


subsection "Definitions of Literal Values"

subsubsection "Boolean Values"

inductive_set BooleanValue :: "('o, 'nt) ValueDef set"
  where
    rule_boolean_true: "bool True \<in> BooleanValue" |
    rule_boolean_false: "bool False \<in> BooleanValue"

lemma boolean_values_are_booleans[simp]: "x \<in> BooleanValue \<Longrightarrow> \<exists>y. x = bool y"
  using BooleanValue.cases by blast

lemma boolean_values_are_not_integers[simp]: "int x \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_reals[simp]: "real x \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_strings[simp]: "string x \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_enumvalues[simp]: "enum x \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_userdatavalues[simp]: "data x \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_objects[simp]: "obj x \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_nil[simp]: "nil \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_bags[simp]: "bagof x \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_sets[simp]: "setof x \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_seqs[simp]: "seqof x \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_ords[simp]: "ordof x \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_unspecified[simp]: "unspecified \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_are_not_invalid[simp]: "invalid \<notin> BooleanValue"
  using boolean_values_are_booleans by blast

lemma boolean_values_contained_list_singleton[simp]: "x \<in> BooleanValue \<Longrightarrow> contained_list x = [x]"
  by (induct rule: BooleanValue.induct) simp_all

lemma boolean_values_contained_values_singleton[simp]: "x \<in> BooleanValue \<Longrightarrow> contained_values x = [x]"
  by (induct rule: BooleanValue.induct) simp_all

subsubsection "Integer Values"

inductive_set IntegerValue :: "('o, 'nt) ValueDef set"
  where
    rule_integer: "\<And>i. int i \<in> IntegerValue"

lemma integer_values_are_integers[simp]: "x \<in> IntegerValue \<Longrightarrow> \<exists>y. x = int y"
  using IntegerValue.cases by blast

lemma integer_values_are_not_booleans[simp]: "bool x \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_reals[simp]: "real x \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_strings[simp]: "string x \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_enumvalues[simp]: "enum x \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_userdatavalues[simp]: "data x \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_objects[simp]: "obj x \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_nil[simp]: "nil \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_bags[simp]: "bagof x \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_sets[simp]: "setof x \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_seqs[simp]: "seqof x \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_ords[simp]: "ordof x \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_unspecified[simp]: "unspecified \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_are_not_invalid[simp]: "invalid \<notin> IntegerValue"
  using integer_values_are_integers by blast

lemma integer_values_boolean_values_intersect[simp]: "IntegerValue \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma integer_values_contained_list_singleton[simp]: "x \<in> IntegerValue \<Longrightarrow> contained_list x = [x]"
  by (induct rule: IntegerValue.induct) simp_all

lemma integer_values_contained_values_singleton[simp]: "x \<in> IntegerValue \<Longrightarrow> contained_values x = [x]"
  by (induct rule: IntegerValue.induct) simp_all

subsubsection "Real Values"

inductive_set RealValue :: "('o, 'nt) ValueDef set"
  where
    rule_real: "\<And>r. real r \<in> RealValue"

lemma real_values_are_reals[simp]: "x \<in> RealValue \<Longrightarrow> \<exists>y. x = real y"
  using RealValue.cases by blast

lemma real_values_are_not_booleans[simp]: "bool x \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_integers[simp]: "int x \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_strings[simp]: "string x \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_enumvalues[simp]: "enum x \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_userdatavalues[simp]: "data x \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_objects[simp]: "obj x \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_nil[simp]: "nil \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_bags[simp]: "bagof x \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_sets[simp]: "setof x \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_seqs[simp]: "seqof x \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_ords[simp]: "ordof x \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_unspecified[simp]: "unspecified \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_are_not_invalid[simp]: "invalid \<notin> RealValue"
  using real_values_are_reals by blast

lemma real_values_boolean_values_intersect[simp]: "RealValue \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma real_values_integer_values_intersect[simp]: "RealValue \<inter> IntegerValue = {}"
  using integer_values_are_integers by fastforce

lemma real_values_contained_list_singleton[simp]: "x \<in> RealValue \<Longrightarrow> contained_list x = [x]"
  by (induct rule: RealValue.induct) simp_all

lemma real_values_contained_values_singleton[simp]: "x \<in> RealValue \<Longrightarrow> contained_values x = [x]"
  by (induct rule: RealValue.induct) simp_all

subsubsection "String Values"

inductive_set StringValue :: "('o, 'nt) ValueDef set"
  where
    rule_string: "\<And>s. string s \<in> StringValue"

lemma string_values_are_strings[simp]: "x \<in> StringValue \<Longrightarrow> \<exists>y. x = string y"
  using StringValue.cases by blast

lemma string_values_are_not_booleans[simp]: "bool x \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_integers[simp]: "int x \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_reals[simp]: "real x \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_enumvalues[simp]: "enum x \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_userdatavalues[simp]: "data x \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_objects[simp]: "obj x \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_nil[simp]: "nil \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_bags[simp]: "bagof x \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_sets[simp]: "setof x \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_seqs[simp]: "seqof x \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_ords[simp]: "ordof x \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_unspecified[simp]: "unspecified \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_are_not_invalid[simp]: "invalid \<notin> StringValue"
  using string_values_are_strings by blast

lemma string_values_boolean_values_intersect[simp]: "StringValue \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma string_values_integer_values_intersect[simp]: "StringValue \<inter> IntegerValue = {}"
  using integer_values_are_integers by fastforce

lemma string_values_real_values_intersect[simp]: "StringValue \<inter> RealValue = {}"
  using real_values_are_reals by fastforce

lemma string_values_contained_list_singleton[simp]: "x \<in> StringValue \<Longrightarrow> contained_list x = [x]"
  by (induct rule: StringValue.induct) simp_all

lemma string_values_contained_values_singleton[simp]: "x \<in> StringValue \<Longrightarrow> contained_values x = [x]"
  by (induct rule: StringValue.induct) simp_all

subsubsection "Literal Values"

definition LiteralValue :: "('o, 'nt) ValueDef set" where
  "LiteralValue \<equiv> BooleanValue \<union> IntegerValue \<union> RealValue \<union> StringValue"

lemma boolean_values_are_literal_values[simp]: "BooleanValue \<subseteq> LiteralValue"
  by (simp add: LiteralValue_def le_supI1)

lemma integer_values_are_literal_values[simp]: "IntegerValue \<subseteq> LiteralValue"
  by (simp add: LiteralValue_def le_supI1)

lemma real_values_are_literal_values[simp]: "RealValue \<subseteq> LiteralValue"
  by (simp add: LiteralValue_def le_supI1)

lemma string_values_are_literal_values[simp]: "StringValue \<subseteq> LiteralValue"
  by (simp add: LiteralValue_def le_supI1)

lemma literal_value_members[simp]: "x \<in> LiteralValue \<Longrightarrow> (\<exists>y. x = bool y) \<or> (\<exists>y. x = int y) \<or> (\<exists>y. x = real y) \<or> (\<exists>y. x = string y)"
  unfolding LiteralValue_def
proof-
  assume "x \<in> BooleanValue \<union> IntegerValue \<union> RealValue \<union> StringValue"
  then show "(\<exists>y. x = bool y) \<or> (\<exists>y. x = int y) \<or> (\<exists>y. x = real y) \<or> (\<exists>y. x = string y)"
  proof (elim UnE)
    show "x \<in> BooleanValue \<Longrightarrow> (\<exists>y. x = bool y) \<or> (\<exists>y. x = ValueDef.int y) \<or> (\<exists>y. x = ValueDef.real y) \<or> (\<exists>y. x = ValueDef.string y)"
      by simp
    show "x \<in> IntegerValue \<Longrightarrow> (\<exists>y. x = bool y) \<or> (\<exists>y. x = ValueDef.int y) \<or> (\<exists>y. x = ValueDef.real y) \<or> (\<exists>y. x = ValueDef.string y)"
      by simp
    show "x \<in> RealValue \<Longrightarrow> (\<exists>y. x = bool y) \<or> (\<exists>y. x = ValueDef.int y) \<or> (\<exists>y. x = ValueDef.real y) \<or> (\<exists>y. x = ValueDef.string y)"
      by simp
    show "x \<in> StringValue \<Longrightarrow> (\<exists>y. x = bool y) \<or> (\<exists>y. x = ValueDef.int y) \<or> (\<exists>y. x = ValueDef.real y) \<or> (\<exists>y. x = ValueDef.string y)"
      by simp
  qed
qed

lemma no_enumvalues_in_literal_values[simp]: "enum x \<notin> LiteralValue"
  using literal_value_members by blast

lemma no_userdatatypes_in_literal_values[simp]: "data x \<notin> LiteralValue"
  using literal_value_members by blast

lemma no_objects_in_literal_values[simp]: "obj x \<notin> LiteralValue"
  using literal_value_members by blast

lemma no_nil_in_literal_values[simp]: "nil \<notin> LiteralValue"
  using literal_value_members by blast

lemma no_bags_in_literal_values[simp]: "bagof x \<notin> LiteralValue"
  using literal_value_members by blast

lemma no_sets_in_literal_values[simp]: "setof x \<notin> LiteralValue"
  using literal_value_members by blast

lemma no_seqs_in_literal_values[simp]: "seqof x \<notin> LiteralValue"
  using literal_value_members by blast

lemma no_ords_in_literal_values[simp]: "ordof x \<notin> LiteralValue"
  using literal_value_members by blast

lemma literal_values_are_not_unspecified[simp]: "unspecified \<notin> LiteralValue"
  using literal_value_members by blast

lemma literal_values_are_not_invalid[simp]: "invalid \<notin> LiteralValue"
  using literal_value_members by blast

lemma literal_values_boolean_values_intersect[simp]: "LiteralValue \<inter> BooleanValue = BooleanValue"
  using LiteralValue_def by auto

lemma literal_values_integer_values_intersect[simp]: "LiteralValue \<inter> IntegerValue = IntegerValue"
  using LiteralValue_def by auto

lemma literal_values_real_values_intersect[simp]: "LiteralValue \<inter> RealValue = RealValue"
  using LiteralValue_def by auto

lemma literal_values_string_values_intersect[simp]: "LiteralValue \<inter> StringValue = StringValue"
  using LiteralValue_def by auto

lemma literal_values_contained_list_singleton[simp]: "x \<in> LiteralValue \<Longrightarrow> contained_list x = [x]"
  unfolding LiteralValue_def
  by auto

lemma literal_values_contained_values_singleton[simp]: "x \<in> LiteralValue \<Longrightarrow> contained_values x = [x]"
  unfolding LiteralValue_def
  by auto


subsection "Definition of Class Values"

inductive_set ProperClassValue :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef set"
  for Imod :: "('o, 'nt) instance_model"
  where
    rule_proper_objects: "ob \<in> Object Imod \<Longrightarrow> obj ob \<in> ProperClassValue Imod"

lemma proper_class_values_are_proper_objects[simp]: "x \<in> ProperClassValue Imod \<Longrightarrow> \<exists>y. x = obj y"
  using ProperClassValue.cases by blast

lemma proper_class_values_are_not_booleans[simp]: "bool x \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_integers[simp]: "int x \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_reals[simp]: "real x \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_strings[simp]: "string x \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_enumvalues[simp]: "enum x \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_userdatavalues[simp]: "data x \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_nil[simp]: "nil \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_bags[simp]: "bagof x \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_sets[simp]: "setof x \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_seqs[simp]: "seqof x \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_ords[simp]: "ordof x \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_unspecified[simp]: "unspecified \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_are_not_invalid[simp]: "invalid \<notin> ProperClassValue Imod"
  using proper_class_values_are_proper_objects by blast

lemma proper_class_values_boolean_values_intersect[simp]: "ProperClassValue Imod \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma proper_class_values_integer_values_intersect[simp]: "ProperClassValue Imod \<inter> IntegerValue = {}"
  using integer_values_are_integers by fastforce

lemma proper_class_values_real_values_intersect[simp]: "ProperClassValue Imod \<inter> RealValue = {}"
  using real_values_are_reals by fastforce

lemma proper_class_values_string_values_intersect[simp]: "ProperClassValue Imod \<inter> StringValue = {}"
  using string_values_are_strings by fastforce

lemma proper_class_values_literal_values_intersect[simp]: "ProperClassValue Imod \<inter> LiteralValue = {}"
  using literal_value_members by fastforce

lemma proper_class_values_contained_list_singleton[simp]: "x \<in> ProperClassValue Imod \<Longrightarrow> contained_list x = [x]"
  by (induct rule: ProperClassValue.induct) simp_all

lemma proper_class_values_contained_values_singleton[simp]: "x \<in> ProperClassValue Imod \<Longrightarrow> contained_values x = [x]"
  by (induct rule: ProperClassValue.induct) simp_all

definition ClassValue :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef set" where
  "ClassValue Imod \<equiv> ProperClassValue Imod \<union> {nil}"

lemma proper_class_values_are_class_values[simp]: "ProperClassValue Imod \<subseteq> ClassValue Imod"
  using ClassValue_def by blast

lemma class_value_members[simp]: "x \<in> ClassValue Imod \<Longrightarrow> (\<exists>y. x = obj y) \<or> x = nil"
  unfolding ClassValue_def
proof-
  assume "x \<in> ProperClassValue Imod \<union> {nil}"
  then show "(\<exists>y. x = obj y) \<or> x = nil"
  proof (elim UnE)
    show "x \<in> ProperClassValue Imod \<Longrightarrow> (\<exists>y. x = obj y) \<or> x = nil"
      by simp
    show "x \<in> {nil} \<Longrightarrow> (\<exists>y. x = obj y) \<or> x = nil"
      by simp
  qed
qed

lemma class_values_are_not_booleans[simp]: "bool x \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_are_not_integers[simp]: "int x \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_are_not_reals[simp]: "real x \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_are_not_strings[simp]: "string x \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_are_not_enumvalues[simp]: "enum x \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_are_not_userdatavalues[simp]: "data x \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_are_not_bags[simp]: "bagof x \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_are_not_sets[simp]: "setof x \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_are_not_seqs[simp]: "seqof x \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_are_not_ords[simp]: "ordof x \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_are_not_unspecified[simp]: "unspecified \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_are_not_invalid[simp]: "invalid \<notin> ClassValue Imod"
  using class_value_members by blast

lemma class_values_boolean_values_intersect[simp]: "ClassValue Imod \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma class_values_integer_values_intersect[simp]: "ClassValue Imod \<inter> IntegerValue = {}"
  using integer_values_are_integers by fastforce

lemma class_values_real_values_intersect[simp]: "ClassValue Imod \<inter> RealValue = {}"
  using real_values_are_reals by fastforce

lemma class_values_string_values_intersect[simp]: "ClassValue Imod \<inter> StringValue = {}"
  using string_values_are_strings by fastforce

lemma class_values_literal_values_intersect[simp]: "ClassValue Imod \<inter> LiteralValue = {}"
  using literal_value_members by fastforce

lemma class_values_proper_class_values_intersect[simp]: "ClassValue Imod \<inter> ProperClassValue Imod = ProperClassValue Imod"
  using ClassValue_def by auto

lemma class_values_contained_list_singleton[simp]: "x \<in> ClassValue Imod \<Longrightarrow> contained_list x = [x]"
  unfolding ClassValue_def
  by auto

lemma class_values_contained_values_singleton[simp]: "x \<in> ClassValue Imod \<Longrightarrow> contained_values x = [x]"
  unfolding ClassValue_def
  by auto


subsection "Definitions of Atom Values"

subsubsection "Enum Values"

inductive_set EnumValueValue :: "('nt) type_model \<Rightarrow> ('o, 'nt) ValueDef set"
  for Tmod :: "('nt) type_model"
  where
    rule_enumvalue: "ev \<in> EnumValue Tmod \<Longrightarrow> enum ev \<in> EnumValueValue Tmod"

lemma enumvalues_values_are_enumvalues[simp]: "x \<in> EnumValueValue Tmod \<Longrightarrow> \<exists>y. x = enum y"
  using EnumValueValue.cases by blast

lemma enumvalues_values_are_not_booleans[simp]: "bool x \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_integers[simp]: "int x \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_reals[simp]: "real x \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_strings[simp]: "string x \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_userdatavalues[simp]: "data x \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_objects[simp]: "obj x \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_nil[simp]: "nil \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_bags[simp]: "bagof x \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_sets[simp]: "setof x \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_seqs[simp]: "seqof x \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_ords[simp]: "ordof x \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_unspecified[simp]: "unspecified \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_are_not_invalid[simp]: "invalid \<notin> EnumValueValue Tmod"
  using enumvalues_values_are_enumvalues by blast

lemma enumvalues_values_boolean_values_intersect[simp]: "EnumValueValue Tmod \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma enumvalues_values_integer_values_intersect[simp]: "EnumValueValue Tmod \<inter> IntegerValue = {}"
  using integer_values_are_integers by fastforce

lemma enumvalues_values_real_values_intersect[simp]: "EnumValueValue Tmod \<inter> RealValue = {}"
  using real_values_are_reals by fastforce

lemma enumvalues_values_string_values_intersect[simp]: "EnumValueValue Tmod \<inter> StringValue = {}"
  using string_values_are_strings by fastforce

lemma enumvalues_values_literal_values_intersect[simp]: "EnumValueValue Tmod \<inter> LiteralValue = {}"
  using literal_value_members by fastforce

lemma enumvalues_values_proper_class_values_intersect[simp]: "EnumValueValue Tmod \<inter> ProperClassValue Imod = {}"
  using proper_class_values_are_proper_objects by fastforce

lemma enumvalues_values_class_values_intersect[simp]: "EnumValueValue Tmod \<inter> ClassValue Imod = {}"
  using class_value_members by fastforce

lemma enumvalues_values_contained_list_singleton[simp]: "x \<in> EnumValueValue Tmod \<Longrightarrow> contained_list x = [x]"
  by (induct rule: EnumValueValue.induct) simp_all

lemma enumvalues_values_contained_values_singleton[simp]: "x \<in> EnumValueValue Tmod \<Longrightarrow> contained_values x = [x]"
  by (induct rule: EnumValueValue.induct) simp_all

subsubsection "User Data Values"

inductive_set UserDataValue :: "('o, 'nt) ValueDef set"
  where
    rule_userdatavalue: "\<And>s. data s \<in> UserDataValue"

lemma userdata_values_are_userdatavalues[simp]: "x \<in> UserDataValue \<Longrightarrow> \<exists>y. x = data y"
  using UserDataValue.cases by blast

lemma userdata_values_are_not_booleans[simp]: "bool x \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_integers[simp]: "int x \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_reals[simp]: "real x \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_strings[simp]: "string x \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_enumvalues[simp]: "enum x \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_objects[simp]: "obj x \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_nil[simp]: "nil \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_bags[simp]: "bagof x \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_sets[simp]: "setof x \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_seqs[simp]: "seqof x \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_ords[simp]: "ordof x \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_unspecified[simp]: "unspecified \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_are_not_invalid[simp]: "invalid \<notin> UserDataValue"
  using userdata_values_are_userdatavalues by blast

lemma userdata_values_boolean_values_intersect[simp]: "UserDataValue \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma userdata_values_integer_values_intersect[simp]: "UserDataValue \<inter> IntegerValue = {}"
  using integer_values_are_integers by fastforce

lemma userdata_values_real_values_intersect[simp]: "UserDataValue \<inter> RealValue = {}"
  using real_values_are_reals by fastforce

lemma userdata_values_string_values_intersect[simp]: "UserDataValue \<inter> StringValue = {}"
  using string_values_are_strings by fastforce

lemma userdata_values_literal_values_intersect[simp]: "UserDataValue \<inter> LiteralValue = {}"
  using literal_value_members by fastforce

lemma userdata_values_enumvalues_values_intersect[simp]: "UserDataValue \<inter> EnumValueValue Tmod = {}"
  using enumvalues_values_are_enumvalues by fastforce

lemma userdata_values_proper_class_values_intersect[simp]: "UserDataValue \<inter> ProperClassValue Imod = {}"
  using proper_class_values_are_proper_objects by fastforce

lemma userdata_values_class_values_intersect[simp]: "UserDataValue \<inter> ClassValue Imod = {}"
  using class_value_members by fastforce

lemma userdata_values_contained_list_singleton[simp]: "x \<in> UserDataValue \<Longrightarrow> contained_list x = [x]"
  by (induct rule: UserDataValue.induct) simp_all

lemma userdata_values_contained_values_singleton[simp]: "x \<in> UserDataValue \<Longrightarrow> contained_values x = [x]"
  by (induct rule: UserDataValue.induct) simp_all

subsubsection "Atom Values"

definition AtomValue :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef set" where
  "AtomValue Imod \<equiv> LiteralValue \<union> ClassValue Imod \<union> EnumValueValue (Tm Imod) \<union> UserDataValue"

lemma literal_values_are_atom_values[simp]: "LiteralValue \<subseteq> AtomValue Imod"
  by (simp add: AtomValue_def le_supI1)

lemma boolean_values_are_atom_values[simp]: "BooleanValue \<subseteq> AtomValue Imod"
  by (simp add: AtomValue_def le_supI1)

lemma integer_values_are_atom_values[simp]: "IntegerValue \<subseteq> AtomValue Imod"
  by (simp add: AtomValue_def le_supI1)

lemma real_values_are_atom_values[simp]: "RealValue \<subseteq> AtomValue Imod"
  by (simp add: AtomValue_def le_supI1)

lemma string_values_are_atom_values[simp]: "StringValue \<subseteq> AtomValue Imod"
  by (simp add: AtomValue_def le_supI1)

lemma class_values_are_atom_values[simp]: "ClassValue Imod \<subseteq> AtomValue Imod"
  by (simp add: AtomValue_def le_supI1)

lemma proper_class_values_are_atom_values[simp]: "ProperClassValue Imod \<subseteq> AtomValue Imod"
  using proper_class_values_are_class_values class_values_are_atom_values by fastforce

lemma enumvalues_values_are_atom_values[simp]: "EnumValueValue (Tm Imod) \<subseteq> AtomValue Imod"
  by (simp add: AtomValue_def le_supI1)

lemma userdata_values_are_atom_values[simp]: "UserDataValue \<subseteq> AtomValue Imod"
  by (simp add: AtomValue_def le_supI1)

lemma no_bags_in_atom_values[simp]: "bagof x \<notin> AtomValue Imod"
  by (simp add: AtomValue_def)

lemma no_sets_in_atom_values[simp]: "setof x \<notin> AtomValue Imod"
  by (simp add: AtomValue_def)

lemma no_seqs_in_atom_values[simp]: "seqof x \<notin> AtomValue Imod"
  by (simp add: AtomValue_def)

lemma no_ords_in_atom_values[simp]: "ordof x \<notin> AtomValue Imod"
  by (simp add: AtomValue_def)

lemma atom_values_are_not_unspecified[simp]: "unspecified \<notin> AtomValue Imod"
  by (simp add: AtomValue_def)

lemma atom_values_are_not_invalid[simp]: "invalid \<notin> AtomValue Imod"
  by (simp add: AtomValue_def)

lemma atom_values_literal_values_intersect[simp]: "AtomValue Imod \<inter> LiteralValue = LiteralValue"
  using AtomValue_def by auto

lemma atom_values_boolean_values_intersect[simp]: "AtomValue Imod \<inter> BooleanValue = BooleanValue"
  by (simp add: inf_absorb2)

lemma atom_values_integer_values_intersect[simp]: "AtomValue Imod \<inter> IntegerValue = IntegerValue"
  by (simp add: inf_absorb2)

lemma atom_values_real_values_intersect[simp]: "AtomValue Imod \<inter> RealValue = RealValue"
  by (simp add: inf_absorb2)

lemma atom_values_string_values_intersect[simp]: "AtomValue Imod \<inter> StringValue = StringValue"
  by (simp add: inf_absorb2)

lemma atom_values_class_values_intersect[simp]: "AtomValue Imod \<inter> ClassValue Imod = ClassValue Imod"
  using AtomValue_def by auto

lemma atom_values_proper_class_values_intersect[simp]: "AtomValue Imod \<inter> ProperClassValue Imod = ProperClassValue Imod"
  by (simp add: inf_absorb2)

lemma atom_values_enumvalues_values_intersect[simp]: "AtomValue Imod \<inter> EnumValueValue (Tm Imod) = EnumValueValue (Tm Imod)"
  using AtomValue_def by auto

lemma atom_values_userdata_values_intersect[simp]: "AtomValue Imod \<inter> UserDataValue = UserDataValue"
  using AtomValue_def by auto

lemma atom_values_contained_list_singleton[simp]: "x \<in> AtomValue Imod \<Longrightarrow> contained_list x = [x]"
  unfolding AtomValue_def
  by auto

lemma atom_values_contained_values_singleton[simp]: "x \<in> AtomValue Imod \<Longrightarrow> contained_values x = [x]"
  unfolding AtomValue_def
  by auto


subsection "Definitions of Container Values"

inductive_set AtomValueList :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef list set"
  for Imod :: "('o, 'nt) instance_model"
  where
    rule_fst_atom_element: "v \<in> AtomValue Imod \<Longrightarrow> [v] \<in> AtomValueList Imod" |
    rule_rec_atom_element: "l \<in> AtomValueList Imod \<Longrightarrow> v \<in> AtomValue Imod \<Longrightarrow> v#l \<in> AtomValueList Imod"

inductive_set ContainerValueList :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef list set"
  for Imod :: "('o, 'nt) instance_model"
  where
    rule_empty_list: "[] \<in> ContainerValueList Imod" |
    rule_append_bag_element: "v \<in> ContainerValueList Imod \<Longrightarrow> l \<in> AtomValueList Imod \<Longrightarrow> (bagof l)#v \<in> ContainerValueList Imod" |
    rule_append_set_element: "v \<in> ContainerValueList Imod \<Longrightarrow> l \<in> AtomValueList Imod \<Longrightarrow> (setof l)#v \<in> ContainerValueList Imod" |
    rule_append_seq_element: "v \<in> ContainerValueList Imod \<Longrightarrow> l \<in> AtomValueList Imod \<Longrightarrow> (seqof l)#v \<in> ContainerValueList Imod" |
    rule_append_ord_element: "v \<in> ContainerValueList Imod \<Longrightarrow> l \<in> AtomValueList Imod \<Longrightarrow> (ordof l)#v \<in> ContainerValueList Imod" |
    rule_wrap_bag_element: "v1 \<in> ContainerValueList Imod \<Longrightarrow> v2 \<in> ContainerValueList Imod \<Longrightarrow> (bagof v1)#v2 \<in> ContainerValueList Imod" |
    rule_wrap_set_element: "v1 \<in> ContainerValueList Imod \<Longrightarrow> v2 \<in> ContainerValueList Imod \<Longrightarrow> (setof v1)#v2 \<in> ContainerValueList Imod" |
    rule_wrap_seq_element: "v1 \<in> ContainerValueList Imod \<Longrightarrow> v2 \<in> ContainerValueList Imod \<Longrightarrow> (seqof v1)#v2 \<in> ContainerValueList Imod" |
    rule_wrap_ord_element: "v1 \<in> ContainerValueList Imod \<Longrightarrow> v2 \<in> ContainerValueList Imod \<Longrightarrow> (ordof v1)#v2 \<in> ContainerValueList Imod"

inductive_set ContainerValue :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef set"
  for Imod :: "('o, 'nt) instance_model"
  where
    rule_bagof_atom_values: "l \<in> AtomValueList Imod \<Longrightarrow> bagof l \<in> ContainerValue Imod" |
    rule_setof_atom_values: "l \<in> AtomValueList Imod \<Longrightarrow> setof l \<in> ContainerValue Imod" |
    rule_seqof_atom_values: "l \<in> AtomValueList Imod \<Longrightarrow> seqof l \<in> ContainerValue Imod" |
    rule_ordof_atom_values: "l \<in> AtomValueList Imod \<Longrightarrow> ordof l \<in> ContainerValue Imod" |
    rule_bagof_container_values: "l \<in> ContainerValueList Imod \<Longrightarrow> bagof l \<in> ContainerValue Imod" |
    rule_setof_container_values: "l \<in> ContainerValueList Imod \<Longrightarrow> setof l \<in> ContainerValue Imod" |
    rule_seqof_container_values: "l \<in> ContainerValueList Imod \<Longrightarrow> seqof l \<in> ContainerValue Imod" |
    rule_ordof_container_values: "l \<in> ContainerValueList Imod \<Longrightarrow> ordof l \<in> ContainerValue Imod"

lemma atom_value_list_members[simp]: "\<And>y. x \<in> AtomValueList Imod \<Longrightarrow> y \<in> set x \<Longrightarrow> y \<in> AtomValue Imod"
proof-
  fix x
  assume "x \<in> AtomValueList Imod"
  then show "\<And>y. y \<in> set x \<Longrightarrow> y \<in> AtomValue Imod"
  proof (induct)
    case (rule_fst_atom_element v)
    then show ?case
      by simp
  next
    case (rule_rec_atom_element l v)
    then show ?case
      by fastforce
  qed
qed

lemma atom_value_list_append[simp]: "x \<in> AtomValueList Imod \<Longrightarrow> y \<in> AtomValueList Imod \<Longrightarrow> x @ y \<in> AtomValueList Imod"
proof-
  assume x_in_atom_value_list: "x \<in> AtomValueList Imod"
  assume y_in_atom_value_list: "y \<in> AtomValueList Imod"
  show "x @ y \<in> AtomValueList Imod"
    using x_in_atom_value_list y_in_atom_value_list
  proof (induct x)
    case (rule_fst_atom_element v)
    then show ?case
      by (simp add: AtomValueList.rule_rec_atom_element)
  next
    case (rule_rec_atom_element l v)
    then show ?case
      by (simp add: AtomValueList.rule_rec_atom_element)
  qed
qed

lemma atom_value_list_left_append_invalid: "xs @ [x] \<notin> AtomValueList Imod \<Longrightarrow> y \<in> AtomValueList Imod \<Longrightarrow> xs @ [x] @ y \<notin> AtomValueList Imod"
proof-
  assume x_not_in_atom_value_list: "xs @ [x] \<notin> AtomValueList Imod"
  assume y_in_atom_value_list: "y \<in> AtomValueList Imod"
  show "xs @ [x] @ y \<notin> AtomValueList Imod"
    using x_not_in_atom_value_list y_in_atom_value_list
  proof (induct xs)
    case Nil
    then show ?case
      using AtomValueList.rule_fst_atom_element atom_value_list_members
      by fastforce
  next
    case (Cons xx xs)
    then show ?case
    proof (induct "xs @ [x] \<in> AtomValueList Imod")
      case True
      then have "xx \<notin> AtomValue Imod"
        using AtomValueList.rule_rec_atom_element
        by auto
      then show ?case
        by auto
    next
      case False
      then have "xs @ [x] @ y \<notin> AtomValueList Imod"
        by blast
      then show ?case
        using AtomValueList.simps append_Cons append_is_Nil_conv list.distinct(1) list.sel(3)
        by metis
    qed
  qed
qed

lemma atom_value_list_left_append_invalid_alt: "x # xs \<notin> AtomValueList Imod \<Longrightarrow> y \<in> AtomValueList Imod \<Longrightarrow> (x # xs) @ y \<notin> AtomValueList Imod"
  using append_assoc append_butlast_last_id atom_value_list_left_append_invalid list.distinct(1)
  by metis

lemma atom_value_list_right_append_invalid: "x \<in> AtomValueList Imod \<Longrightarrow> (y # ys) \<notin> AtomValueList Imod \<Longrightarrow> x @ (y # ys) \<notin> AtomValueList Imod"
proof-
  assume x_in_atom_value_list: "x \<in> AtomValueList Imod"
  assume y_not_in_atom_value_list: "(y # ys) \<notin> AtomValueList Imod"
  show "x @ (y # ys) \<notin> AtomValueList Imod"
    using x_in_atom_value_list y_not_in_atom_value_list
  proof (induct x)
    case (rule_fst_atom_element v)
    then show ?case
      using AtomValueList.simps
      by auto
  next
    case (rule_rec_atom_element l v)
    then show ?case
      using AtomValueList.simps append_Cons list.distinct(1) list.inject
      by metis
  qed
qed

lemma container_value_list_members[simp]: "\<And>y. x \<in> ContainerValueList Imod \<Longrightarrow> y \<in> set x \<Longrightarrow> contained_list y \<in> AtomValueList Imod \<or> contained_list y \<in> ContainerValueList Imod"
proof-
  fix x
  assume "x \<in> ContainerValueList Imod"
  then show "\<And>y. y \<in> set x \<Longrightarrow> contained_list y \<in> AtomValueList Imod \<or> contained_list y \<in> ContainerValueList Imod"
  proof (induct)
    case rule_empty_list
    then show ?case
      by simp
  next
    case (rule_append_bag_element v l)
    then show ?case
      by fastforce
  next
    case (rule_append_set_element v l)
    then show ?case
      by fastforce
  next
    case (rule_append_seq_element v l)
    then show ?case
      by fastforce
  next
    case (rule_append_ord_element v l)
    then show ?case
      by fastforce
  next
    case (rule_wrap_bag_element v1 v2)
    then show ?case
      by fastforce
  next
    case (rule_wrap_set_element v1 v2)
    then show ?case
      by fastforce
  next
    case (rule_wrap_seq_element v1 v2)
    then show ?case
      by fastforce
  next
    case (rule_wrap_ord_element v1 v2)
    then show ?case
      by fastforce
  qed
qed

lemma container_value_list_members_alt[simp]: "\<And>y. x \<in> ContainerValueList Imod \<Longrightarrow> y \<in> set x \<Longrightarrow> y \<in> ContainerValue Imod"
proof-
  fix x
  assume "x \<in> ContainerValueList Imod"
  then show "\<And>y. y \<in> set x \<Longrightarrow> y \<in> ContainerValue Imod"
  proof (induct)
    case rule_empty_list
    then show ?case
      by simp
  next
    case (rule_append_bag_element v l)
    then show ?case
      using ContainerValue.rule_bagof_atom_values
      by auto
  next
    case (rule_append_set_element v l)
    then show ?case
      using ContainerValue.rule_setof_atom_values
      by auto
  next
    case (rule_append_seq_element v l)
    then show ?case
      using ContainerValue.rule_seqof_atom_values
      by auto
  next
    case (rule_append_ord_element v l)
    then show ?case
      using ContainerValue.rule_ordof_atom_values
      by auto
  next
    case (rule_wrap_bag_element v1 v2)
    then show ?case
      using ContainerValue.rule_bagof_container_values
      by auto
  next
    case (rule_wrap_set_element v1 v2)
    then show ?case
      using ContainerValue.rule_setof_container_values
      by auto
  next
    case (rule_wrap_seq_element v1 v2)
    then show ?case
      using ContainerValue.rule_seqof_container_values
      by auto
  next
    case (rule_wrap_ord_element v1 v2)
    then show ?case
      using ContainerValue.rule_ordof_container_values
      by auto
  qed
qed

lemma container_value_list_append[simp]: "x \<in> ContainerValueList Imod \<Longrightarrow> y \<in> ContainerValueList Imod \<Longrightarrow> x @ y \<in> ContainerValueList Imod"
proof-
  assume x_in_container_value_list: "x \<in> ContainerValueList Imod"
  assume y_in_container_value_list: "y \<in> ContainerValueList Imod"
  show "x @ y \<in> ContainerValueList Imod"
    using x_in_container_value_list y_in_container_value_list
  proof (induct x)
    case rule_empty_list
    then show ?case
      by simp
  next
    case (rule_append_bag_element v l)
    then show ?case
      by (simp add: ContainerValueList.rule_append_bag_element)
  next
    case (rule_append_set_element v l)
    then show ?case
      by (simp add: ContainerValueList.rule_append_set_element)
  next
    case (rule_append_seq_element v l)
    then show ?case
      by (simp add: ContainerValueList.rule_append_seq_element)
  next
    case (rule_append_ord_element v l)
    then show ?case
      by (simp add: ContainerValueList.rule_append_ord_element)
  next
    case (rule_wrap_bag_element v1 v2)
    then show ?case
      by (simp add: ContainerValueList.rule_wrap_bag_element)
  next
    case (rule_wrap_set_element v1 v2)
    then show ?case
      by (simp add: ContainerValueList.rule_wrap_set_element)
  next
    case (rule_wrap_seq_element v1 v2)
    then show ?case
      by (simp add: ContainerValueList.rule_wrap_seq_element)
  next
    case (rule_wrap_ord_element v1 v2)
    then show ?case
      by (simp add: ContainerValueList.rule_wrap_ord_element)
  qed
qed

lemma container_value_list_left_append_invalid: "x \<notin> ContainerValueList Imod \<Longrightarrow> y \<in> ContainerValueList Imod \<Longrightarrow> x @ y \<notin> ContainerValueList Imod"
proof-
  assume x_not_in_container_value_list: "x \<notin> ContainerValueList Imod"
  assume y_in_container_value_list: "y \<in> ContainerValueList Imod"
  show "x @ y \<notin> ContainerValueList Imod"
    using x_not_in_container_value_list y_in_container_value_list
  proof (induct x)
    case Nil
    then show ?case
      by (simp add: ContainerValueList.rule_empty_list)
  next
    case (Cons x xs)
    then show ?case
    proof (induct "xs \<in> ContainerValueList Imod")
      case True
      then have x_singleton_no_container_value_list: "[x] \<notin> ContainerValueList Imod"
        using container_value_list_append
        by fastforce
      have "xs @ y \<in> ContainerValueList Imod"
        using True.hyps container_value_list_append y_in_container_value_list
        by blast
      then show ?case
        using x_singleton_no_container_value_list
      proof (induct "(x # xs) @ y \<in> ContainerValueList Imod")
        case True
        then have "(x # xs) @ y \<in> ContainerValueList Imod"
          by simp
        then show ?case
          using True.hyps
        proof (cases)
          case rule_empty_list
          then show ?thesis
            by simp
        next
          case (rule_append_bag_element v l)
          then show ?thesis
            using x_singleton_no_container_value_list
            by (simp add: ContainerValueList.rule_append_bag_element ContainerValueList.rule_empty_list)
        next
          case (rule_append_set_element v l)
          then show ?thesis
            using x_singleton_no_container_value_list
            by (simp add: ContainerValueList.rule_append_set_element ContainerValueList.rule_empty_list)
        next
          case (rule_append_seq_element v l)
          then show ?thesis
            using x_singleton_no_container_value_list
            by (simp add: ContainerValueList.rule_append_seq_element ContainerValueList.rule_empty_list)
        next
          case (rule_append_ord_element v l)
          then show ?thesis
            using x_singleton_no_container_value_list
            by (simp add: ContainerValueList.rule_append_ord_element ContainerValueList.rule_empty_list)
        next
          case (rule_wrap_bag_element v1 v2)
          then show ?thesis
            using x_singleton_no_container_value_list
            by (simp add: ContainerValueList.rule_wrap_bag_element ContainerValueList.rule_empty_list)
        next
          case (rule_wrap_set_element v1 v2)
          then show ?thesis
            using x_singleton_no_container_value_list
            by (simp add: ContainerValueList.rule_wrap_set_element ContainerValueList.rule_empty_list)
        next
          case (rule_wrap_seq_element v1 v2)
          then show ?thesis
            using x_singleton_no_container_value_list
            by (simp add: ContainerValueList.rule_wrap_seq_element ContainerValueList.rule_empty_list)
        next
          case (rule_wrap_ord_element v1 v2)
          then show ?thesis
            using x_singleton_no_container_value_list
            by (simp add: ContainerValueList.rule_wrap_ord_element ContainerValueList.rule_empty_list)
        qed
      next
        case False
        then show ?case
          by simp
      qed
    next
      case False
      then have "xs @ y \<notin> ContainerValueList Imod"
        by simp
      then show ?case
        using ContainerValueList.cases
        by auto
    qed
  qed
qed

lemma container_value_list_right_append_invalid: "x \<in> ContainerValueList Imod \<Longrightarrow> y \<notin> ContainerValueList Imod \<Longrightarrow> x @ y \<notin> ContainerValueList Imod"
proof-
  assume x_in_container_value_list: "x \<in> ContainerValueList Imod"
  assume y_not_in_container_value_list: "y \<notin> ContainerValueList Imod"
  show "x @ y \<notin> ContainerValueList Imod"
    using x_in_container_value_list y_not_in_container_value_list
  proof (induct x)
    case rule_empty_list
    then show ?case
      by simp
  next
    case (rule_append_bag_element v l)
    then show ?case
    proof (induct "(ValueDef.bagof l # v) @ y \<in> ContainerValueList Imod")
      case True
      then have "(ValueDef.bagof l # v) @ y \<in> ContainerValueList Imod"
        by simp
      then show ?case
      proof (cases)
        case rule_empty_list
        then show ?thesis
          by simp
      next
        case (rule_append_bag_element v l)
        then show ?thesis
          using rule_append_bag_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_set_element v l)
        then show ?thesis
          using rule_append_bag_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_seq_element v l)
        then show ?thesis
          using rule_append_bag_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_ord_element v l)
        then show ?thesis
          using rule_append_bag_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_bag_element v1 v2)
        then show ?thesis
          using rule_append_bag_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_set_element v1 v2)
        then show ?thesis
          using rule_append_bag_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_seq_element v1 v2)
        then show ?thesis
          using rule_append_bag_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_ord_element v1 v2)
        then show ?thesis
          using rule_append_bag_element.hyps(2) y_not_in_container_value_list
          by simp
      qed
    next
      case False
      then show ?case
        by simp
    qed
  next
    case (rule_append_set_element v l)
    then show ?case
    proof (induct "(ValueDef.setof l # v) @ y \<in> ContainerValueList Imod")
      case True
      then have "(ValueDef.setof l # v) @ y \<in> ContainerValueList Imod"
        by simp
      then show ?case
      proof (cases)
        case rule_empty_list
        then show ?thesis
          by simp
      next
        case (rule_append_bag_element v l)
        then show ?thesis
          using rule_append_set_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_set_element v l)
        then show ?thesis
          using rule_append_set_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_seq_element v l)
        then show ?thesis
          using rule_append_set_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_ord_element v l)
        then show ?thesis
          using rule_append_set_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_bag_element v1 v2)
        then show ?thesis
          using rule_append_set_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_set_element v1 v2)
        then show ?thesis
          using rule_append_set_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_seq_element v1 v2)
        then show ?thesis
          using rule_append_set_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_ord_element v1 v2)
        then show ?thesis
          using rule_append_set_element.hyps(2) y_not_in_container_value_list
          by simp
      qed
    next
      case False
      then show ?case
        by simp
    qed
  next
    case (rule_append_seq_element v l)
    then show ?case
    proof (induct "(ValueDef.seqof l # v) @ y \<in> ContainerValueList Imod")
      case True
      then have "(ValueDef.seqof l # v) @ y \<in> ContainerValueList Imod"
        by simp
      then show ?case
      proof (cases)
        case rule_empty_list
        then show ?thesis
          by simp
      next
        case (rule_append_bag_element v l)
        then show ?thesis
          using rule_append_seq_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_set_element v l)
        then show ?thesis
          using rule_append_seq_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_seq_element v l)
        then show ?thesis
          using rule_append_seq_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_ord_element v l)
        then show ?thesis
          using rule_append_seq_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_bag_element v1 v2)
        then show ?thesis
          using rule_append_seq_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_set_element v1 v2)
        then show ?thesis
          using rule_append_seq_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_seq_element v1 v2)
        then show ?thesis
          using rule_append_seq_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_ord_element v1 v2)
        then show ?thesis
          using rule_append_seq_element.hyps(2) y_not_in_container_value_list
          by simp
      qed
    next
      case False
      then show ?case
        by simp
    qed
  next
    case (rule_append_ord_element v l)
    then show ?case
    proof (induct "(ValueDef.ordof l # v) @ y \<in> ContainerValueList Imod")
      case True
      then have "(ValueDef.ordof l # v) @ y \<in> ContainerValueList Imod"
        by simp
      then show ?case
      proof (cases)
        case rule_empty_list
        then show ?thesis
          by simp
      next
        case (rule_append_bag_element v l)
        then show ?thesis
          using rule_append_ord_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_set_element v l)
        then show ?thesis
          using rule_append_ord_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_seq_element v l)
        then show ?thesis
          using rule_append_ord_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_append_ord_element v l)
        then show ?thesis
          using rule_append_ord_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_bag_element v1 v2)
        then show ?thesis
          using rule_append_ord_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_set_element v1 v2)
        then show ?thesis
          using rule_append_ord_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_seq_element v1 v2)
        then show ?thesis
          using rule_append_ord_element.hyps(2) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_ord_element v1 v2)
        then show ?thesis
          using rule_append_ord_element.hyps(2) y_not_in_container_value_list
          by simp
      qed
    next
      case False
      then show ?case
        by simp
    qed
  next
    case (rule_wrap_bag_element v1 v2)
    then show ?case
    proof (induct "(ValueDef.bagof v1 # v2) @ y \<in> ContainerValueList Imod")
      case True
      then have "(ValueDef.bagof v1 # v2) @ y \<in> ContainerValueList Imod"
        by simp
      then show ?case
      proof (cases)
        case rule_empty_list
        then show ?thesis
          by simp
      next
        case (rule_append_bag_element v l)
        then show ?thesis
          using rule_wrap_bag_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_set_element v l)
        then show ?thesis
          using rule_wrap_bag_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_seq_element v l)
        then show ?thesis
          using rule_wrap_bag_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_ord_element v l)
        then show ?thesis
          using rule_wrap_bag_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_bag_element v1 v2)
        then show ?thesis
          using rule_wrap_bag_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_set_element v1 v2)
        then show ?thesis
          using rule_wrap_bag_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_seq_element v1 v2)
        then show ?thesis
          using rule_wrap_bag_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_ord_element v1 v2)
        then show ?thesis
          using rule_wrap_bag_element.hyps(4) y_not_in_container_value_list
          by simp
      qed
    next
      case False
      then show ?case
        by simp
    qed
  next
    case (rule_wrap_set_element v1 v2)
    then show ?case
    proof (induct "(ValueDef.setof v1 # v2) @ y \<in> ContainerValueList Imod")
      case True
      then have "(ValueDef.setof v1 # v2) @ y \<in> ContainerValueList Imod"
        by simp
      then show ?case
      proof (cases)
        case rule_empty_list
        then show ?thesis
          by simp
      next
        case (rule_append_bag_element v l)
        then show ?thesis
          using rule_wrap_set_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_set_element v l)
        then show ?thesis
          using rule_wrap_set_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_seq_element v l)
        then show ?thesis
          using rule_wrap_set_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_ord_element v l)
        then show ?thesis
          using rule_wrap_set_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_bag_element v1 v2)
        then show ?thesis
          using rule_wrap_set_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_set_element v1 v2)
        then show ?thesis
          using rule_wrap_set_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_seq_element v1 v2)
        then show ?thesis
          using rule_wrap_set_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_ord_element v1 v2)
        then show ?thesis
          using rule_wrap_set_element.hyps(4) y_not_in_container_value_list
          by simp
      qed
    next
      case False
      then show ?case
        by simp
    qed
  next
    case (rule_wrap_seq_element v1 v2)
    then show ?case
    proof (induct "(ValueDef.seqof v1 # v2) @ y \<in> ContainerValueList Imod")
      case True
      then have "(ValueDef.seqof v1 # v2) @ y \<in> ContainerValueList Imod"
        by simp
      then show ?case
      proof (cases)
        case rule_empty_list
        then show ?thesis
          by simp
      next
        case (rule_append_bag_element v l)
        then show ?thesis
          using rule_wrap_seq_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_set_element v l)
        then show ?thesis
          using rule_wrap_seq_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_seq_element v l)
        then show ?thesis
          using rule_wrap_seq_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_ord_element v l)
        then show ?thesis
          using rule_wrap_seq_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_bag_element v1 v2)
        then show ?thesis
          using rule_wrap_seq_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_set_element v1 v2)
        then show ?thesis
          using rule_wrap_seq_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_seq_element v1 v2)
        then show ?thesis
          using rule_wrap_seq_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_ord_element v1 v2)
        then show ?thesis
          using rule_wrap_seq_element.hyps(4) y_not_in_container_value_list
          by simp
      qed
    next
      case False
      then show ?case
        by simp
    qed
  next
    case (rule_wrap_ord_element v1 v2)
    then show ?case
    proof (induct "(ValueDef.ordof v1 # v2) @ y \<in> ContainerValueList Imod")
      case True
      then have "(ValueDef.ordof v1 # v2) @ y \<in> ContainerValueList Imod"
        by simp
      then show ?case
      proof (cases)
        case rule_empty_list
        then show ?thesis
          by simp
      next
        case (rule_append_bag_element v l)
        then show ?thesis
          using rule_wrap_ord_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_set_element v l)
        then show ?thesis
          using rule_wrap_ord_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_seq_element v l)
        then show ?thesis
          using rule_wrap_ord_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_append_ord_element v l)
        then show ?thesis
          using rule_wrap_ord_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_bag_element v1 v2)
        then show ?thesis
          using rule_wrap_ord_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_set_element v1 v2)
        then show ?thesis
          using rule_wrap_ord_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_seq_element v1 v2)
        then show ?thesis
          using rule_wrap_ord_element.hyps(4) y_not_in_container_value_list
          by simp
      next
        case (rule_wrap_ord_element v1 v2)
        then show ?thesis
          using rule_wrap_ord_element.hyps(4) y_not_in_container_value_list
          by simp
      qed
    next
      case False
      then show ?case
        by simp
    qed
  qed
qed

lemma container_value_members[simp]: "x \<in> ContainerValue Imod \<Longrightarrow> (\<exists>y. x = bagof y) \<or> (\<exists>y. x = setof y) \<or> (\<exists>y. x = seqof y) \<or> (\<exists>y. x = ordof y)"
  by (induct rule: ContainerValue.induct) simp_all

lemma container_value_members_alt: "x \<in> ContainerValue Imod \<Longrightarrow> contained_list x \<in> ContainerValueList Imod \<or> contained_list x \<in> AtomValueList Imod"
proof-
  fix x
  assume "x \<in> ContainerValue Imod"
  then show "contained_list x \<in> ContainerValueList Imod \<or> contained_list x \<in> AtomValueList Imod"
    by (cases) (simp_all)
qed

lemma atom_value_list_bagof_contained_values: "x \<in> AtomValueList Imod \<Longrightarrow> y \<in> set (contained_values (bagof x)) \<Longrightarrow> y \<in> AtomValue Imod"
proof-
  fix a b
  assume a_in_atom_value_list: "a \<in> AtomValueList Imod"
  assume b_in_contained_values: "b \<in> set (contained_values (bagof a))"
  show "b \<in> AtomValue Imod"
    using a_in_atom_value_list b_in_contained_values
    by (induct) (auto)
qed

lemma atom_value_list_setof_contained_values: "x \<in> AtomValueList Imod \<Longrightarrow> y \<in> set (contained_values (setof x)) \<Longrightarrow> y \<in> AtomValue Imod"
proof-
  fix a b
  assume a_in_atom_value_list: "a \<in> AtomValueList Imod"
  assume b_in_contained_values: "b \<in> set (contained_values (setof a))"
  show "b \<in> AtomValue Imod"
    using a_in_atom_value_list b_in_contained_values
    by (induct) (auto)
qed

lemma atom_value_list_seqof_contained_values: "x \<in> AtomValueList Imod \<Longrightarrow> y \<in> set (contained_values (seqof x)) \<Longrightarrow> y \<in> AtomValue Imod"
proof-
  fix a b
  assume a_in_atom_value_list: "a \<in> AtomValueList Imod"
  assume b_in_contained_values: "b \<in> set (contained_values (seqof a))"
  show "b \<in> AtomValue Imod"
    using a_in_atom_value_list b_in_contained_values
    by (induct) (auto)
qed

lemma atom_value_list_ordof_contained_values: "x \<in> AtomValueList Imod \<Longrightarrow> y \<in> set (contained_values (ordof x)) \<Longrightarrow> y \<in> AtomValue Imod"
proof-
  fix a b
  assume a_in_atom_value_list: "a \<in> AtomValueList Imod"
  assume b_in_contained_values: "b \<in> set (contained_values (ordof a))"
  show "b \<in> AtomValue Imod"
    using a_in_atom_value_list b_in_contained_values
    by (induct) (auto)
qed

lemma atom_value_list_contained_values_bagof_identity: "x \<in> AtomValueList Imod \<Longrightarrow> contained_values (bagof x) = x"
proof-
  assume "x \<in> AtomValueList Imod"
  then show "contained_values (bagof x) = x"
  proof (induct x)
    case (rule_fst_atom_element v)
    then show ?case
      by simp
  next
    case (rule_rec_atom_element l v)
    then show ?case
      by simp
  qed
qed

lemma atom_value_list_contained_values_setof_identity: "x \<in> AtomValueList Imod \<Longrightarrow> contained_values (setof x) = x"
proof-
  assume "x \<in> AtomValueList Imod"
  then show "contained_values (setof x) = x"
  proof (induct x)
    case (rule_fst_atom_element v)
    then show ?case
      by simp
  next
    case (rule_rec_atom_element l v)
    then show ?case
      by simp
  qed
qed

lemma atom_value_list_contained_values_seqof_identity: "x \<in> AtomValueList Imod \<Longrightarrow> contained_values (seqof x) = x"
proof-
  assume "x \<in> AtomValueList Imod"
  then show "contained_values (seqof x) = x"
  proof (induct x)
    case (rule_fst_atom_element v)
    then show ?case
      by simp
  next
    case (rule_rec_atom_element l v)
    then show ?case
      by simp
  qed
qed

lemma atom_value_list_contained_values_ordof_identity: "x \<in> AtomValueList Imod \<Longrightarrow> contained_values (ordof x) = x"
proof-
  assume "x \<in> AtomValueList Imod"
  then show "contained_values (ordof x) = x"
  proof (induct x)
    case (rule_fst_atom_element v)
    then show ?case
      by simp
  next
    case (rule_rec_atom_element l v)
    then show ?case
      by simp
  qed
qed

lemma container_value_list_contained_values: "x \<in> ContainerValueList Imod \<Longrightarrow> 
  y \<in> set (contained_values (bagof x)) \<or> y \<in> set (contained_values (setof x)) \<or> y \<in> set (contained_values (seqof x)) \<or> y \<in> set (contained_values (ordof x)) \<Longrightarrow> 
  y \<in> ContainerValue Imod \<or> y \<in> AtomValue Imod"
proof-
  fix x y
  assume x_in_container_value_list: "x \<in> ContainerValueList Imod"
  assume y_in_contained_values: "y \<in> set (contained_values (bagof x)) \<or> y \<in> set (contained_values (setof x)) \<or> y \<in> set (contained_values (seqof x)) \<or> y \<in> set (contained_values (ordof x))"
  show "y \<in> ContainerValue Imod \<or> y \<in> AtomValue Imod"
    using x_in_container_value_list y_in_contained_values
  proof (induct)
    case rule_empty_list
    then show ?case
      by simp
  next
    case (rule_append_bag_element v l)
    then show ?case
      using atom_value_list_bagof_contained_values
      by fastforce
  next
    case (rule_append_set_element v l)
    then show ?case
      using atom_value_list_setof_contained_values
      by fastforce
  next
    case (rule_append_seq_element v l)
    then show ?case
      using atom_value_list_seqof_contained_values
      by fastforce
  next
    case (rule_append_ord_element v l)
    then show ?case
      using atom_value_list_ordof_contained_values
      by fastforce
  next
    case (rule_wrap_bag_element v1 v2)
    then show ?case
      by fastforce
  next
    case (rule_wrap_set_element v1 v2)
    then show ?case
      by fastforce
  next
    case (rule_wrap_seq_element v1 v2)
    then show ?case
      by fastforce
  next
    case (rule_wrap_ord_element v1 v2)
    then show ?case
      by fastforce
  qed
qed

lemma container_value_contained_values: "x \<in> ContainerValue Imod \<Longrightarrow> y \<in> set (contained_values x) \<Longrightarrow> y \<in> ContainerValue Imod \<or> y \<in> AtomValue Imod"
proof-
  fix a b
  assume a_in_container_value: "a \<in> ContainerValue Imod"
  assume b_in_contained_values: "b \<in> set (contained_values a)"
  show "b \<in> ContainerValue Imod \<or> b \<in> AtomValue Imod"
    using a_in_container_value b_in_contained_values
  proof (induct)
    case (rule_bagof_atom_values l)
    then show ?case
      using atom_value_list_bagof_contained_values
      by blast
  next
    case (rule_setof_atom_values l)
    then show ?case
      using atom_value_list_setof_contained_values
      by blast
  next
    case (rule_seqof_atom_values l)
    then show ?case
      using atom_value_list_seqof_contained_values
      by blast
  next
    case (rule_ordof_atom_values l)
    then show ?case
      using atom_value_list_ordof_contained_values
      by blast
  next
    case (rule_bagof_container_values l)
    then show ?case
      using container_value_list_contained_values
      by blast
  next
    case (rule_setof_container_values l)
    then show ?case
      using container_value_list_contained_values
      by blast
  next
    case (rule_seqof_container_values l)
    then show ?case
      using container_value_list_contained_values
      by blast
  next
    case (rule_ordof_container_values l)
    then show ?case
      using container_value_list_contained_values
      by blast
  qed
qed

lemma container_values_are_not_booleans[simp]: "bool x \<notin> ContainerValue Imod"
  using container_value_members by blast

lemma container_values_are_not_integers[simp]: "int x \<notin> ContainerValue Imod"
  using container_value_members by blast

lemma container_values_are_not_reals[simp]: "real x \<notin> ContainerValue Imod"
  using container_value_members by blast

lemma container_values_are_not_strings[simp]: "string x \<notin> ContainerValue Imod"
  using container_value_members by blast

lemma container_values_are_not_enumvalues[simp]: "enum x \<notin> ContainerValue Imod"
  using container_value_members by blast

lemma container_values_are_not_userdatavalues[simp]: "data x \<notin> ContainerValue Imod"
  using container_value_members by blast

lemma container_values_are_not_objects[simp]: "obj x \<notin> ContainerValue Imod"
  using container_value_members by blast

lemma container_values_are_not_nil[simp]: "nil \<notin> ContainerValue Imod"
  using container_value_members by blast

lemma container_values_are_not_unspecified[simp]: "unspecified \<notin> ContainerValue Imod"
  using container_value_members by blast

lemma container_values_are_not_invalid[simp]: "invalid \<notin> ContainerValue Imod"
  using container_value_members by blast

lemma container_values_boolean_values_intersect[simp]: "ContainerValue Imod \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma container_values_integer_values_intersect[simp]: "ContainerValue Imod \<inter> IntegerValue = {}"
  using integer_values_are_integers by fastforce

lemma container_values_real_values_intersect[simp]: "ContainerValue Imod \<inter> RealValue = {}"
  using real_values_are_reals by fastforce

lemma container_values_string_values_intersect[simp]: "ContainerValue Imod \<inter> StringValue = {}"
  using string_values_are_strings by fastforce

lemma container_values_literal_values_intersect[simp]: "ContainerValue Imod \<inter> LiteralValue = {}"
  using literal_value_members by fastforce

lemma container_values_enumvalues_values_intersect[simp]: "ContainerValue Imod1 \<inter> EnumValueValue Tmod2 = {}"
  using enumvalues_values_are_enumvalues by fastforce

lemma container_values_proper_class_values_intersect[simp]: "ContainerValue Imod1 \<inter> ProperClassValue Imod2 = {}"
  using proper_class_values_are_proper_objects by fastforce

lemma container_values_class_values_intersect[simp]: "ContainerValue Imod1 \<inter> ClassValue Imod2 = {}"
  using class_value_members by fastforce

lemma container_values_userdata_values_intersect[simp]: "ContainerValue Imod1 \<inter> UserDataValue = {}"
  using userdata_values_are_userdatavalues by fastforce

lemma container_values_atom_values_intersect[simp]: "ContainerValue Imod1 \<inter> AtomValue Imod2 = {}"
proof (intro Int_emptyI)
  fix x assume "x \<in> ContainerValue Imod1" then show "x \<in> AtomValue Imod2 \<Longrightarrow> False"
    by (induct) simp_all
qed

lemma atom_value_list_not_in_container_value_list: "x \<in> AtomValueList Imod1 \<Longrightarrow> x \<notin> ContainerValueList Imod2"
proof-
  assume x_in_atom_value_list: "x \<in> AtomValueList Imod1"
  then have "set x \<subseteq> AtomValue Imod1"
    by auto
  then have "\<And>y. y \<in> set x \<Longrightarrow> y \<notin> ContainerValue Imod2"
    using IntI UnCI container_values_atom_values_intersect empty_iff subset_Un_eq
    by metis
  then show ?thesis
    using AtomValueList.simps x_in_atom_value_list
    by fastforce
qed

lemma container_value_list_not_in_atom_value_list: "x \<in> ContainerValueList Imod1 \<Longrightarrow> x \<notin> AtomValueList Imod2"
proof-
  assume x_in_container_value_list: "x \<in> ContainerValueList Imod1"
  then have "set x \<subseteq> ContainerValue Imod1"
    by auto
  then have "\<And>y. y \<in> set x \<Longrightarrow> y \<notin> AtomValue Imod2"
    using IntI UnCI container_values_atom_values_intersect empty_iff subset_Un_eq
    by metis
  then show ?thesis
    using atom_value_list_not_in_container_value_list x_in_container_value_list
    by blast
qed

lemma atom_value_list_container_value_list_intersect[simp]: "AtomValueList Imod1 \<inter> ContainerValueList Imod2 = {}"
  by (simp add: atom_value_list_not_in_container_value_list subset_antisym subset_iff)


subsection "Set of Values"

definition Value :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef set" where
  "Value Imod \<equiv> AtomValue Imod \<union> ContainerValue Imod"

lemma values_are_not_unspecified[simp]: "unspecified \<notin> Value Imod"
  unfolding Value_def
  by simp

lemma values_are_not_invalid[simp]: "invalid \<notin> Value Imod"
  unfolding Value_def
  by simp

lemma atom_values_are_values[simp]: "AtomValue Imod \<subseteq> Value Imod"
  by (simp add: Value_def le_supI1)

lemma literal_values_are_values[simp]: "LiteralValue \<subseteq> Value Imod"
  by (simp add: Value_def le_supI1)

lemma boolean_values_are_values[simp]: "BooleanValue \<subseteq> Value Imod"
  by (simp add: Value_def le_supI1)

lemma integer_values_are_values[simp]: "IntegerValue \<subseteq> Value Imod"
  by (simp add: Value_def le_supI1)

lemma real_values_are_values[simp]: "RealValue \<subseteq> Value Imod"
  by (simp add: Value_def le_supI1)

lemma string_values_are_values[simp]: "StringValue \<subseteq> Value Imod"
  by (simp add: Value_def le_supI1)

lemma class_values_are_values[simp]: "ClassValue Imod \<subseteq> Value Imod"
  by (simp add: Value_def le_supI1)

lemma proper_class_values_are_values[simp]: "ProperClassValue Imod \<subseteq> Value Imod"
  using proper_class_values_are_class_values class_values_are_values by fastforce

lemma enumvalues_values_are_values[simp]: "EnumValueValue (Tm Imod) \<subseteq> Value Imod"
  by (simp add: Value_def le_supI1)

lemma userdata_values_are_values[simp]: "UserDataValue \<subseteq> Value Imod"
  by (simp add: Value_def le_supI1)

lemma container_values_are_values[simp]: "ContainerValue Imod \<subseteq> Value Imod"
  by (simp add: Value_def le_supI1)

lemma values_atom_values_intersect[simp]: "Value Imod \<inter> AtomValue Imod = AtomValue Imod"
  by (simp add: inf_absorb2)

lemma values_literal_values_intersect[simp]: "Value Imod \<inter> LiteralValue = LiteralValue"
  by (simp add: inf_absorb2)

lemma values_boolean_values_intersect[simp]: "Value Imod \<inter> BooleanValue = BooleanValue"
  by (simp add: inf_absorb2)

lemma values_integer_values_intersect[simp]: "Value Imod \<inter> IntegerValue = IntegerValue"
  by (simp add: inf_absorb2)

lemma values_real_values_intersect[simp]: "Value Imod \<inter> RealValue = RealValue"
  by (simp add: inf_absorb2)

lemma values_string_values_intersect[simp]: "Value Imod \<inter> StringValue = StringValue"
  by (simp add: inf_absorb2)

lemma values_class_values_intersect[simp]: "Value Imod \<inter> ClassValue Imod = ClassValue Imod"
  by (simp add: inf_absorb2)

lemma values_proper_class_values_intersect[simp]: "Value Imod \<inter> ProperClassValue Imod = ProperClassValue Imod"
  by (simp add: inf_absorb2)

lemma values_enumvalues_values_intersect[simp]: "Value Imod \<inter> EnumValueValue (Tm Imod) = EnumValueValue (Tm Imod)"
  by (simp add: inf_absorb2)

lemma values_userdata_values_intersect[simp]: "Value Imod \<inter> UserDataValue = UserDataValue"
  by (simp add: inf_absorb2)

lemma values_container_values_intersect[simp]: "Value Imod \<inter> ContainerValue Imod = ContainerValue Imod"
  by (simp add: inf_absorb2)

lemma list_of_atom_values_in_atom_value_list: "set (xs @ [x]) \<subseteq> AtomValue Imod \<Longrightarrow> (xs @ [x]) \<in> AtomValueList Imod"
proof-
  assume "set (xs @ [x]) \<subseteq> AtomValue Imod"
  then show "(xs @ [x]) \<in> AtomValueList Imod"
  proof (induct "xs")
    case Nil
    then show ?case
      by (simp add: AtomValueList.rule_fst_atom_element)
  next
    case (Cons a xs)
    then have "(a # (xs @ [x])) \<in> AtomValueList Imod"
    proof (intro AtomValueList.rule_rec_atom_element)
      have "set (xs @ [x]) \<subseteq> AtomValue Imod"
        using Cons.prems by simp
      then show "xs @ [x] \<in> AtomValueList Imod"
        using Cons.hyps by simp
    next
      show "a \<in> AtomValue Imod"
        using Cons.prems
        by simp
    qed
    then show ?case
      by simp
  qed
qed

lemma list_of_atom_values_in_atom_value_list_alt: "xs \<noteq> [] \<Longrightarrow> set xs \<subseteq> AtomValue Imod \<Longrightarrow> xs \<in> AtomValueList Imod"
proof-
  assume xs_not_empty: "xs \<noteq> []"
  assume "set xs \<subseteq> AtomValue Imod"
  then show "xs \<in> AtomValueList Imod"
    using xs_not_empty
  proof (induct "xs" rule: rev_induct)
    case Nil
    then show ?case
      by simp
  next
    case (snoc x xs)
    then show ?case
      using list_of_atom_values_in_atom_value_list
      by blast
  qed
qed

lemma list_of_container_values_in_container_value_list: "set xs \<subseteq> ContainerValue Imod \<Longrightarrow> xs \<in> ContainerValueList Imod"
proof-
  assume "set xs \<subseteq> ContainerValue Imod"
  then show "xs \<in> ContainerValueList Imod"
  proof (induct "xs")
    case Nil
    then show ?case
      by (simp add: ContainerValueList.rule_empty_list)
  next
    case (Cons x xs)
    then show ?case
    proof (induct x)
      case (bagof y)
      then have "y \<in> AtomValueList Imod \<or> y \<in> ContainerValueList Imod"
        using container_value_members_alt
        by fastforce
      then show ?case
      proof (elim disjE)
        assume "y \<in> AtomValueList Imod"
        then show ?thesis
        proof (intro rule_append_bag_element)
          show "xs \<in> ContainerValueList Imod"
            using Cons.hyps Cons.prems
            by simp
        qed (simp_all)
      next
        assume "y \<in> ContainerValueList Imod"
        then show ?thesis
        proof (intro rule_wrap_bag_element)
          show "xs \<in> ContainerValueList Imod"
            using Cons.hyps Cons.prems
            by simp
        qed (simp_all)
      qed
    next
      case (setof y)
      then have "y \<in> AtomValueList Imod \<or> y \<in> ContainerValueList Imod"
        using container_value_members_alt
        by fastforce
      then show ?case
      proof (elim disjE)
        assume "y \<in> AtomValueList Imod"
        then show ?thesis
        proof (intro rule_append_set_element)
          show "xs \<in> ContainerValueList Imod"
            using Cons.hyps Cons.prems
            by simp
        qed (simp_all)
      next
        assume "y \<in> ContainerValueList Imod"
        then show ?thesis
        proof (intro rule_wrap_set_element)
          show "xs \<in> ContainerValueList Imod"
            using Cons.hyps Cons.prems
            by simp
        qed (simp_all)
      qed
    next
      case (seqof y)
      then have "y \<in> AtomValueList Imod \<or> y \<in> ContainerValueList Imod"
        using container_value_members_alt
        by fastforce
      then show ?case
      proof (elim disjE)
        assume "y \<in> AtomValueList Imod"
        then show ?thesis
        proof (intro rule_append_seq_element)
          show "xs \<in> ContainerValueList Imod"
            using Cons.hyps Cons.prems
            by simp
        qed (simp_all)
      next
        assume "y \<in> ContainerValueList Imod"
        then show ?thesis
        proof (intro rule_wrap_seq_element)
          show "xs \<in> ContainerValueList Imod"
            using Cons.hyps Cons.prems
            by simp
        qed (simp_all)
      qed
    next
      case (ordof y)
      then have "y \<in> AtomValueList Imod \<or> y \<in> ContainerValueList Imod"
        using container_value_members_alt
        by fastforce
      then show ?case
      proof (elim disjE)
        assume "y \<in> AtomValueList Imod"
        then show ?thesis
        proof (intro rule_append_ord_element)
          show "xs \<in> ContainerValueList Imod"
            using Cons.hyps Cons.prems
            by simp
        qed (simp_all)
      next
        assume "y \<in> ContainerValueList Imod"
        then show ?thesis
        proof (intro rule_wrap_ord_element)
          show "xs \<in> ContainerValueList Imod"
            using Cons.hyps Cons.prems
            by simp
        qed (simp_all)
      qed
    qed (simp_all)
  qed
qed

lemma container_value_contained_values_alt: "x \<in> ContainerValue Imod \<Longrightarrow> y \<in> set (contained_values x) \<Longrightarrow> y \<in> Value Imod"
  unfolding Value_def
  using container_value_contained_values
  by blast


subsection "Container Value Sets"

subsubsection "Bag containers"

inductive_set BagContainerValue :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef set"
  for Imod :: "('o, 'nt) instance_model"
  where
    rule_bagof_atom_values: "l \<in> AtomValueList Imod \<Longrightarrow> bagof l \<in> BagContainerValue Imod" |
    rule_bagof_container_values: "l \<in> ContainerValueList Imod \<Longrightarrow> bagof l \<in> BagContainerValue Imod"

lemma bag_container_values_member: "x \<in> BagContainerValue Imod \<Longrightarrow> contained_list x \<in> AtomValueList Imod \<or> contained_list x \<in> ContainerValueList Imod"
proof-
  fix x
  assume "x \<in> BagContainerValue Imod"
  then show "contained_list x \<in> AtomValueList Imod \<or> contained_list x \<in> ContainerValueList Imod"
    by (induct) (simp_all)
qed

lemma bag_container_values_are_bags[simp]: "x \<in> BagContainerValue Imod \<Longrightarrow> \<exists>y. x = bagof y"
  using BagContainerValue.cases by blast

lemma bag_container_values_are_not_booleans[simp]: "bool x \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_are_not_integers[simp]: "int x \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_are_not_reals[simp]: "real x \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_are_not_strings[simp]: "string x \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_are_not_enumvalues[simp]: "enum x \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_are_not_userdatavalues[simp]: "data x \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_are_not_objects[simp]: "obj x \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_are_not_nil[simp]: "nil \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_are_not_sets[simp]: "setof x \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_are_not_seqs[simp]: "seqof x \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_are_not_ords[simp]: "ordof x \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_not_unspecified[simp]: "unspecified \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_not_invalid[simp]: "invalid \<notin> BagContainerValue Imod"
  using bag_container_values_are_bags by blast

lemma bag_container_values_boolean_values_intersect[simp]: "BagContainerValue Imod \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma bag_container_values_integer_values_intersect[simp]: "BagContainerValue Imod \<inter> IntegerValue = {}"
  using integer_values_are_integers by fastforce

lemma bag_container_values_real_values_intersect[simp]: "BagContainerValue Imod \<inter> RealValue = {}"
  using real_values_are_reals by fastforce

lemma bag_container_values_string_values_intersect[simp]: "BagContainerValue Imod \<inter> StringValue = {}"
  using string_values_are_strings by fastforce

lemma bag_container_values_literal_values_intersect[simp]: "BagContainerValue Imod \<inter> LiteralValue = {}"
  using literal_value_members by fastforce

lemma bag_container_values_enumvalues_values_intersect[simp]: "BagContainerValue Imod \<inter> EnumValueValue Tmod = {}"
  using enumvalues_values_are_enumvalues by fastforce

lemma bag_container_values_userdata_values_intersect[simp]: "BagContainerValue Imod \<inter> UserDataValue = {}"
  using userdata_values_are_userdatavalues by fastforce

lemma bag_container_values_proper_class_values_intersect[simp]: "BagContainerValue Imod \<inter> ProperClassValue Imod = {}"
  using proper_class_values_are_proper_objects by fastforce

lemma bag_container_values_class_values_intersect[simp]: "BagContainerValue Imod \<inter> ClassValue Imod = {}"
  using class_value_members by fastforce

lemma bag_container_values_atom_values_intersect[simp]: "BagContainerValue Imod \<inter> AtomValue Imod = {}"
  using bag_container_values_are_bags by fastforce

lemma bag_container_values_are_container_values[simp]: "BagContainerValue Imod \<subseteq> ContainerValue Imod"
proof
  fix x assume "x \<in> BagContainerValue Imod" then show "x \<in> ContainerValue Imod"
  proof (induct)
    case (rule_bagof_atom_values l)
    then show ?case by (rule ContainerValue.rule_bagof_atom_values)
  next
    case (rule_bagof_container_values l)
    then show ?case by (rule ContainerValue.rule_bagof_container_values)
  qed
qed

lemma bag_container_values_are_values[simp]: "BagContainerValue Imod \<subseteq> Value Imod"
  by (simp add: Value_def sup.coboundedI2)

lemma list_of_atom_values_in_bag_container_value: "set xs \<subseteq> AtomValue Imod \<Longrightarrow> bagof xs \<in> BagContainerValue Imod"
proof (induct xs)
  case Nil
  then show ?case
    by (simp add: BagContainerValue.rule_bagof_container_values ContainerValueList.rule_empty_list)
next
  case (Cons x xs)
  then show ?case
    using BagContainerValue.rule_bagof_atom_values list.distinct(1) list_of_atom_values_in_atom_value_list rev_exhaust
    by metis
qed

lemma list_of_container_values_in_bag_container_value: "set xs \<subseteq> ContainerValue Imod \<Longrightarrow> bagof xs \<in> BagContainerValue Imod"
  by (simp add: BagContainerValue.rule_bagof_container_values list_of_container_values_in_container_value_list)


subsubsection "Set containers"

inductive_set SetContainerValue :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef set"
  for Imod :: "('o, 'nt) instance_model"
  where
    rule_setof_atom_values: "l \<in> AtomValueList Imod \<Longrightarrow> setof l \<in> SetContainerValue Imod" |
    rule_setof_container_values: "l \<in> ContainerValueList Imod \<Longrightarrow> setof l \<in> SetContainerValue Imod"

lemma set_container_values_member: "x \<in> SetContainerValue Imod \<Longrightarrow> contained_list x \<in> AtomValueList Imod \<or> contained_list x \<in> ContainerValueList Imod"
proof-
  fix x
  assume "x \<in> SetContainerValue Imod"
  then show "contained_list x \<in> AtomValueList Imod \<or> contained_list x \<in> ContainerValueList Imod"
    by (induct) (simp_all)
qed

lemma set_container_values_are_sets[simp]: "x \<in> SetContainerValue Imod \<Longrightarrow> \<exists>y. x = setof y"
  using SetContainerValue.cases by blast

lemma set_container_values_are_not_booleans[simp]: "bool x \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_are_not_integers[simp]: "int x \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_are_not_reals[simp]: "real x \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_are_not_strings[simp]: "string x \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_are_not_enumvalues[simp]: "enum x \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_are_not_userdatavalues[simp]: "data x \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_are_not_objects[simp]: "obj x \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_are_not_nil[simp]: "nil \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_are_not_bags[simp]: "bagof x \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_are_not_seqs[simp]: "seqof x \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_are_not_ords[simp]: "ordof x \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_not_unspecified[simp]: "unspecified \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_not_invalid[simp]: "invalid \<notin> SetContainerValue Imod"
  using set_container_values_are_sets by blast

lemma set_container_values_boolean_values_intersect[simp]: "SetContainerValue Imod \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma set_container_values_integer_values_intersect[simp]: "SetContainerValue Imod \<inter> IntegerValue = {}"
  using integer_values_are_integers by fastforce

lemma set_container_values_real_values_intersect[simp]: "SetContainerValue Imod \<inter> RealValue = {}"
  using real_values_are_reals by fastforce

lemma set_container_values_string_values_intersect[simp]: "SetContainerValue Imod \<inter> StringValue = {}"
  using string_values_are_strings by fastforce

lemma set_container_values_literal_values_intersect[simp]: "SetContainerValue Imod \<inter> LiteralValue = {}"
  using literal_value_members by fastforce

lemma set_container_values_enumvalues_values_intersect[simp]: "SetContainerValue Imod \<inter> EnumValueValue Tmod = {}"
  using enumvalues_values_are_enumvalues by fastforce

lemma set_container_values_userdata_values_intersect[simp]: "SetContainerValue Imod \<inter> UserDataValue = {}"
  using userdata_values_are_userdatavalues by fastforce

lemma set_container_values_proper_class_values_intersect[simp]: "SetContainerValue Imod \<inter> ProperClassValue Imod = {}"
  using proper_class_values_are_proper_objects by fastforce

lemma set_container_values_class_values_intersect[simp]: "SetContainerValue Imod \<inter> ClassValue Imod = {}"
  using class_value_members by fastforce

lemma set_container_values_atom_values_intersect[simp]: "SetContainerValue Imod \<inter> AtomValue Imod = {}"
  using set_container_values_are_sets by fastforce

lemma set_container_values_bag_container_values_intersect[simp]: "SetContainerValue Imod \<inter> BagContainerValue Imod = {}"
  using bag_container_values_are_bags by fastforce

lemma set_container_values_are_container_values[simp]: "SetContainerValue Imod \<subseteq> ContainerValue Imod"
proof
  fix x assume "x \<in> SetContainerValue Imod" then show "x \<in> ContainerValue Imod"
  proof (induct)
    case (rule_setof_atom_values l)
    then show ?case by (rule ContainerValue.rule_setof_atom_values)
  next
    case (rule_setof_container_values l)
    then show ?case by (rule ContainerValue.rule_setof_container_values)
  qed
qed

lemma set_container_values_are_values[simp]: "SetContainerValue Imod \<subseteq> Value Imod"
  by (simp add: Value_def sup.coboundedI2)

lemma set_container_values_container_values_intersect[simp]: "SetContainerValue Imod \<inter> ContainerValue Imod = SetContainerValue Imod"
  by (simp add: inf_absorb1)

lemma set_container_values_values_intersect[simp]: "SetContainerValue Imod \<inter> Value Imod = SetContainerValue Imod"
  by (simp add: inf_absorb1)

lemma list_of_atom_values_in_set_container_value: "set xs \<subseteq> AtomValue Imod \<Longrightarrow> setof xs \<in> SetContainerValue Imod"
proof (induct xs)
  case Nil
  then show ?case
    by (simp add: SetContainerValue.rule_setof_container_values ContainerValueList.rule_empty_list)
next
  case (Cons x xs)
  then show ?case
    using SetContainerValue.rule_setof_atom_values list.distinct(1) list_of_atom_values_in_atom_value_list rev_exhaust
    by metis
qed

lemma list_of_container_values_in_set_container_value: "set xs \<subseteq> ContainerValue Imod \<Longrightarrow> setof xs \<in> SetContainerValue Imod"
  by (simp add: SetContainerValue.rule_setof_container_values list_of_container_values_in_container_value_list)

subsubsection "Sequence containers"

inductive_set SeqContainerValue :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef set"
  for Imod :: "('o, 'nt) instance_model"
  where
    rule_seqof_atom_values: "l \<in> AtomValueList Imod \<Longrightarrow> seqof l \<in> SeqContainerValue Imod" |
    rule_seqof_container_values: "l \<in> ContainerValueList Imod \<Longrightarrow> seqof l \<in> SeqContainerValue Imod"

lemma seq_container_values_member: "x \<in> SeqContainerValue Imod \<Longrightarrow> contained_list x \<in> AtomValueList Imod \<or> contained_list x \<in> ContainerValueList Imod"
proof-
  fix x
  assume "x \<in> SeqContainerValue Imod"
  then show "contained_list x \<in> AtomValueList Imod \<or> contained_list x \<in> ContainerValueList Imod"
    by (induct) (simp_all)
qed

lemma seq_container_values_are_seqs[simp]: "x \<in> SeqContainerValue Imod \<Longrightarrow> \<exists>y. x = seqof y"
  using SeqContainerValue.cases by blast

lemma seq_container_values_are_not_booleans[simp]: "bool x \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_are_not_integers[simp]: "int x \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_are_not_reals[simp]: "real x \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_are_not_strings[simp]: "string x \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_are_not_enumvalues[simp]: "enum x \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_are_not_userdatavalues[simp]: "data x \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_are_not_objects[simp]: "obj x \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_are_not_nil[simp]: "nil \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_are_not_bags[simp]: "bagof x \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_are_not_sets[simp]: "setof x \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_are_not_ords[simp]: "ordof x \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_not_unspecified[simp]: "unspecified \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_not_invalid[simp]: "invalid \<notin> SeqContainerValue Imod"
  using seq_container_values_are_seqs by blast

lemma seq_container_values_boolean_values_intersect[simp]: "SeqContainerValue Imod \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma seq_container_values_integer_values_intersect[simp]: "SeqContainerValue Imod \<inter> IntegerValue = {}"
  using integer_values_are_integers by fastforce

lemma seq_container_values_real_values_intersect[simp]: "SeqContainerValue Imod \<inter> RealValue = {}"
  using real_values_are_reals by fastforce

lemma seq_container_values_string_values_intersect[simp]: "SeqContainerValue Imod \<inter> StringValue = {}"
  using string_values_are_strings by fastforce

lemma seq_container_values_literal_values_intersect[simp]: "SeqContainerValue Imod \<inter> LiteralValue = {}"
  using literal_value_members by fastforce

lemma seq_container_values_enumvalues_values_intersect[simp]: "SeqContainerValue Imod \<inter> EnumValueValue Tmod = {}"
  using enumvalues_values_are_enumvalues by fastforce

lemma seq_container_values_userdata_values_intersect[simp]: "SeqContainerValue Imod \<inter> UserDataValue = {}"
  using userdata_values_are_userdatavalues by fastforce

lemma seq_container_values_proper_class_values_intersect[simp]: "SeqContainerValue Imod \<inter> ProperClassValue Imod = {}"
  using proper_class_values_are_proper_objects by fastforce

lemma seq_container_values_class_values_intersect[simp]: "SeqContainerValue Imod \<inter> ClassValue Imod = {}"
  using class_value_members by fastforce

lemma seq_container_values_atom_values_intersect[simp]: "SeqContainerValue Imod \<inter> AtomValue Imod = {}"
  using seq_container_values_are_seqs by fastforce

lemma seq_container_values_bag_container_values_intersect[simp]: "SeqContainerValue Imod \<inter> BagContainerValue Imod = {}"
  using bag_container_values_are_bags by fastforce

lemma seq_container_values_set_container_values_intersect[simp]: "SeqContainerValue Imod \<inter> SetContainerValue Imod = {}"
  using set_container_values_are_sets by fastforce

lemma seq_container_values_are_container_values[simp]: "SeqContainerValue Imod \<subseteq> ContainerValue Imod"
proof
  fix x assume "x \<in> SeqContainerValue Imod" then show "x \<in> ContainerValue Imod"
  proof (induct)
    case (rule_seqof_atom_values l)
    then show ?case by (rule ContainerValue.rule_seqof_atom_values)
  next
    case (rule_seqof_container_values l)
    then show ?case by (rule ContainerValue.rule_seqof_container_values)
  qed
qed

lemma seq_container_values_are_values[simp]: "SeqContainerValue Imod \<subseteq> Value Imod"
  by (simp add: Value_def sup.coboundedI2)

lemma seq_container_values_container_values_intersect[simp]: "SeqContainerValue Imod \<inter> ContainerValue Imod = SeqContainerValue Imod"
  by (simp add: inf_absorb1)

lemma seq_container_values_values_intersect[simp]: "SeqContainerValue Imod \<inter> Value Imod = SeqContainerValue Imod"
  by (simp add: inf_absorb1)

lemma list_of_atom_values_in_seq_container_value: "set xs \<subseteq> AtomValue Imod \<Longrightarrow> seqof xs \<in> SeqContainerValue Imod"
proof (induct xs)
  case Nil
  then show ?case
    by (simp add: SeqContainerValue.rule_seqof_container_values ContainerValueList.rule_empty_list)
next
  case (Cons x xs)
  then show ?case
    using SeqContainerValue.rule_seqof_atom_values list.distinct(1) list_of_atom_values_in_atom_value_list rev_exhaust
    by metis
qed

lemma list_of_container_values_in_seq_container_value: "set xs \<subseteq> ContainerValue Imod \<Longrightarrow> seqof xs \<in> SeqContainerValue Imod"
  by (simp add: SeqContainerValue.rule_seqof_container_values list_of_container_values_in_container_value_list)

subsubsection "Ordered set containers"

inductive_set OrdContainerValue :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef set"
  for Imod :: "('o, 'nt) instance_model"
  where
    rule_ordof_atom_values: "l \<in> AtomValueList Imod \<Longrightarrow> ordof l \<in> OrdContainerValue Imod" |
    rule_ordof_container_values: "l \<in> ContainerValueList Imod \<Longrightarrow> ordof l \<in> OrdContainerValue Imod"

lemma ord_container_values_member: "x \<in> OrdContainerValue Imod \<Longrightarrow> contained_list x \<in> AtomValueList Imod \<or> contained_list x \<in> ContainerValueList Imod"
proof-
  fix x
  assume "x \<in> OrdContainerValue Imod"
  then show "contained_list x \<in> AtomValueList Imod \<or> contained_list x \<in> ContainerValueList Imod"
    by (induct) (simp_all)
qed

lemma ord_container_values_are_ords[simp]: "x \<in> OrdContainerValue Imod \<Longrightarrow> \<exists>y. x = ordof y"
  using OrdContainerValue.cases by blast

lemma ord_container_values_are_not_booleans[simp]: "bool x \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_are_not_integers[simp]: "int x \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_are_not_reals[simp]: "real x \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_are_not_strings[simp]: "string x \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_are_not_enumvalues[simp]: "enum x \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_are_not_userdatavalues[simp]: "data x \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_are_not_objects[simp]: "obj x \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_are_not_nil[simp]: "nil \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_are_not_bags[simp]: "bagof x \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_are_not_sets[simp]: "setof x \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_are_not_seqs[simp]: "seqof x \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_not_unspecified[simp]: "unspecified \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_not_invalid[simp]: "invalid \<notin> OrdContainerValue Imod"
  using ord_container_values_are_ords by blast

lemma ord_container_values_boolean_values_intersect[simp]: "OrdContainerValue Imod \<inter> BooleanValue = {}"
  using boolean_values_are_booleans by fastforce

lemma ord_container_values_integer_values_intersect[simp]: "OrdContainerValue Imod \<inter> IntegerValue = {}"
  using integer_values_are_integers by fastforce

lemma ord_container_values_real_values_intersect[simp]: "OrdContainerValue Imod \<inter> RealValue = {}"
  using real_values_are_reals by fastforce

lemma ord_container_values_string_values_intersect[simp]: "OrdContainerValue Imod \<inter> StringValue = {}"
  using string_values_are_strings by fastforce

lemma ord_container_values_literal_values_intersect[simp]: "OrdContainerValue Imod \<inter> LiteralValue = {}"
  using literal_value_members by fastforce

lemma ord_container_values_enumvalues_values_intersect[simp]: "OrdContainerValue Imod \<inter> EnumValueValue Tmod = {}"
  using enumvalues_values_are_enumvalues by fastforce

lemma ord_container_values_userdata_values_intersect[simp]: "OrdContainerValue Imod \<inter> UserDataValue = {}"
  using userdata_values_are_userdatavalues by fastforce

lemma ord_container_values_proper_class_values_intersect[simp]: "OrdContainerValue Imod \<inter> ProperClassValue Imod = {}"
  using proper_class_values_are_proper_objects by fastforce

lemma ord_container_values_class_values_intersect[simp]: "OrdContainerValue Imod \<inter> ClassValue Imod = {}"
  using class_value_members by fastforce

lemma ord_container_values_atom_values_intersect[simp]: "OrdContainerValue Imod \<inter> AtomValue Imod = {}"
  using ord_container_values_are_ords by fastforce

lemma ord_container_values_bag_container_values_intersect[simp]: "OrdContainerValue Imod \<inter> BagContainerValue Imod = {}"
  using bag_container_values_are_bags by fastforce

lemma ord_container_values_set_container_values_intersect[simp]: "OrdContainerValue Imod \<inter> SetContainerValue Imod = {}"
  using set_container_values_are_sets by fastforce

lemma ord_container_values_seq_container_values_intersect[simp]: "OrdContainerValue Imod \<inter> SeqContainerValue Imod = {}"
  using seq_container_values_are_seqs by fastforce

lemma ord_container_values_are_container_values[simp]: "OrdContainerValue Imod \<subseteq> ContainerValue Imod"
proof
  fix x assume "x \<in> OrdContainerValue Imod" then show "x \<in> ContainerValue Imod"
  proof (induct)
    case (rule_ordof_atom_values l)
    then show ?case by (rule ContainerValue.rule_ordof_atom_values)
  next
    case (rule_ordof_container_values l)
    then show ?case by (rule ContainerValue.rule_ordof_container_values)
  qed
qed

lemma ord_container_values_are_values[simp]: "OrdContainerValue Imod \<subseteq> Value Imod"
  by (simp add: Value_def sup.coboundedI2)

lemma ord_container_values_container_values_intersect[simp]: "OrdContainerValue Imod \<inter> ContainerValue Imod = OrdContainerValue Imod"
  by (simp add: inf_absorb1)

lemma ord_container_values_values_intersect[simp]: "OrdContainerValue Imod \<inter> Value Imod = OrdContainerValue Imod"
  by (simp add: inf_absorb1)

lemma list_of_atom_values_in_ord_container_value: "set xs \<subseteq> AtomValue Imod \<Longrightarrow> ordof xs \<in> OrdContainerValue Imod"
proof (induct xs)
  case Nil
  then show ?case
    by (simp add: OrdContainerValue.rule_ordof_container_values ContainerValueList.rule_empty_list)
next
  case (Cons x xs)
  then show ?case
    using OrdContainerValue.rule_ordof_atom_values list.distinct(1) list_of_atom_values_in_atom_value_list rev_exhaust
    by metis
qed

lemma list_of_container_values_in_ord_container_value: "set xs \<subseteq> ContainerValue Imod \<Longrightarrow> ordof xs \<in> OrdContainerValue Imod"
  by (simp add: OrdContainerValue.rule_ordof_container_values list_of_container_values_in_container_value_list)

lemma container_value_altdef: "ContainerValue Imod = BagContainerValue Imod \<union> SetContainerValue Imod \<union> SeqContainerValue Imod \<union> OrdContainerValue Imod"
proof
  show "ContainerValue Imod \<subseteq> BagContainerValue Imod \<union> SetContainerValue Imod \<union> SeqContainerValue Imod \<union> OrdContainerValue Imod"
  proof
    fix x
    assume "x \<in> ContainerValue Imod"
    then show "x \<in> BagContainerValue Imod \<union> SetContainerValue Imod \<union> SeqContainerValue Imod \<union> OrdContainerValue Imod"
    proof (induct)
      case (rule_bagof_atom_values l)
      then show ?case
        by (simp add: BagContainerValue.rule_bagof_atom_values)
    next
      case (rule_setof_atom_values l)
      then show ?case
        by (simp add: SetContainerValue.rule_setof_atom_values)
    next
      case (rule_seqof_atom_values l)
      then show ?case
        by (simp add: SeqContainerValue.rule_seqof_atom_values)
    next
      case (rule_ordof_atom_values l)
      then show ?case
        by (simp add: OrdContainerValue.rule_ordof_atom_values)
    next
      case (rule_bagof_container_values l)
      then show ?case
        by (simp add: BagContainerValue.rule_bagof_container_values)
    next
      case (rule_setof_container_values l)
      then show ?case
        by (simp add: SetContainerValue.rule_setof_container_values)
    next
      case (rule_seqof_container_values l)
      then show ?case
        by (simp add: SeqContainerValue.rule_seqof_container_values)
    next
      case (rule_ordof_container_values l)
      then show ?case
        by (simp add: OrdContainerValue.rule_ordof_container_values)
    qed
  qed
next
  show "BagContainerValue Imod \<union> SetContainerValue Imod \<union> SeqContainerValue Imod \<union> OrdContainerValue Imod \<subseteq> ContainerValue Imod"
    by simp
qed



section "Value equivalency"

inductive value_equiv :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef \<Rightarrow> ('o, 'nt) ValueDef \<Rightarrow> bool"
  for Imod :: "('o, 'nt) instance_model"
  where
    rule_atom_equiv: "\<lbrakk> v1 \<in> Value Imod; v2 \<in> Value Imod; v1 = v2 \<rbrakk> \<Longrightarrow> value_equiv Imod v1 v2" |
    rule_bagof_equiv: "\<lbrakk> length l1 = length l2; \<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> value_equiv Imod (l1 ! n) (l2 ! f n)) \<rbrakk> \<Longrightarrow> value_equiv Imod (bagof l1) (bagof l2)" |
    rule_setof_equiv: "\<lbrakk> length l1 = length l2; \<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> value_equiv Imod (l1 ! n) (l2 ! f n)) \<rbrakk> \<Longrightarrow> value_equiv Imod (setof l1) (setof l2)" |
    rule_seqof_equiv: "\<lbrakk> length l1 = length l2; \<forall>n. n \<in> {..<length l1} \<longrightarrow> value_equiv Imod (l1 ! n) (l2 ! n) \<rbrakk> \<Longrightarrow> value_equiv Imod (seqof l1) (seqof l2)" |
    rule_ordof_equiv: "\<lbrakk> length l1 = length l2; \<forall>n. n \<in> {..<length l1} \<longrightarrow> value_equiv Imod (l1 ! n) (l2 ! n) \<rbrakk> \<Longrightarrow> value_equiv Imod (ordof l1) (ordof l2)"

abbreviation value_equiv_notation :: "('o, 'nt) ValueDef \<Rightarrow> ('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef \<Rightarrow> bool" ("(_/ \<equiv>[_] _)" [52, 51, 52] 50) where
  "v1 \<equiv>[Imod] v2 \<equiv> value_equiv Imod v1 v2"

lemma container_bij_inverse_ex:
  assumes bij_f: "bij_betw f {..<n} {..<n}"
  shows "\<exists>g. bij_betw g {..<n} {..<n} \<and> (\<forall>x. x \<in> {..<n} \<longrightarrow> g (f x) = x \<and> f (g x) = x)"
  using bij_betw_inv_into bij_betw_inv_into_left bij_betw_inv_into_right bij_f
  by metis

lemma container_bij_equiv_translation:
  assumes length_eq: "length l1 = length l2"
  assumes bij_f: "bij_betw f {..<length l1} {..<length l2}"
  assumes inverse_g: "\<And>n. n \<in> {..<length l1} \<Longrightarrow> g (f n) = n"
  assumes property_holds_f: "\<And>n. n \<in> {..<length l1} \<Longrightarrow> P (l2 ! f n) (l1 ! n)"
  shows "\<And>n. n \<in> {..<length l1} \<Longrightarrow> P (l2 ! n) (l1 ! g n)"
proof-
  fix n
  assume n_def: "n \<in> {..<length l1}"
  then have inverse_g_reverse: "g (f n) = f (g n)"
    using bij_betw_def bij_f image_iff inverse_g length_eq
    by metis
  have "P (l2 ! f (g n)) (l1 ! g n)"
  proof-
    have "g n \<in> {..<length l1}"
      using bij_betw_def bij_f imageE inverse_g length_eq n_def
      by metis
    then show "P (l2 ! f (g n)) (l1 ! g n)"
      by (fact property_holds_f)
  qed
  then have "P (l2 ! g (f n)) (l1 ! g n)"
    by (simp add: inverse_g_reverse)
  then show "P (l2 ! n) (l1 ! g n)"
    using inverse_g n_def
    by simp
qed

lemma container_bij_equiv_translation_alt:
  assumes length_eq: "length l1 = length l2"
  assumes bij_f: "bij_betw f {..<length l1} {..<length l2}"
  assumes bij_h: "bij_betw h {..<length l1} {..<length l2}"
  assumes inverse_g: "\<And>n. n \<in> {..<length l1} \<Longrightarrow> g (f n) = n"
  assumes property_holds_f: "\<And>n. n \<in> {..<length l1} \<Longrightarrow> P (l2 ! f n) (l1 ! (h n))"
  shows "\<And>n. n \<in> {..<length l1} \<Longrightarrow> P (l2 ! n) (l1 ! h (g n))"
proof-
  fix n
  assume n_def: "n \<in> {..<length l1}"
  then have inverse_g_reverse: "g (f n) = f (g n)"
    using bij_betw_def bij_f image_iff inverse_g length_eq
    by metis
  have "P (l2 ! f (g n)) (l1 ! h (g n))"
  proof-
    have g_n: "g n \<in> {..<length l1}"
      using bij_betw_def bij_f imageE inverse_g length_eq n_def
      by metis
    then show "P (l2 ! f (g n)) (l1 ! h (g n))"
      by (fact property_holds_f)
  qed
  then have "P (l2 ! g (f n)) (l1 ! h (g n))"
    by (simp add: inverse_g_reverse)
  then show "P (l2 ! n) (l1 ! h (g n))"
    using inverse_g n_def
    by simp
qed

lemma container_bij_equiv_merge:
  assumes length_eq: "length l1 = length l2"
  assumes bij_g: "bij_betw g {..<length l1} {..<length l2}"
  assumes bij_h: "bij_betw h {..<length l1} {..<length l2}"
  shows "bij_betw (g \<circ> h) {..<length l1} {..<length l2}"
  using bij_betw_trans bij_g bij_h length_eq
  by fastforce

lemma value_equiv_reflexivity[simp]: "x \<in> Value Imod \<Longrightarrow> x \<equiv>[Imod] x"
  by (simp add: rule_atom_equiv)

lemma value_equiv_sym[simp]: "x \<equiv>[Imod] y \<longleftrightarrow> y \<equiv>[Imod] x"
proof
  assume "x \<equiv>[Imod] y"
  then show "y \<equiv>[Imod] x"
  proof (induct)
    case (rule_atom_equiv v1 v2)
    then show ?case
      by (simp add: value_equiv.rule_atom_equiv)
  next
    case (rule_bagof_equiv l1 l2)
    then show ?case
    proof (intro value_equiv.rule_bagof_equiv)
      assume "length l1 = length l2"
      then show "length l2 = length l1"
        by simp
    next
      assume length_eq: "length l1 = length l2"
      assume "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! f n \<equiv>[Imod] l1 ! n)"
      then have "\<exists>f g. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> (\<forall>x. x \<in> {..<length l1} \<longrightarrow> g (f x) = x \<and> f (g x) = x) \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! f n \<equiv>[Imod] l1 ! n)"
        using container_bij_inverse_ex length_eq
        by metis
      then have "\<exists>f g. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> (\<forall>x. x \<in> {..<length l1} \<longrightarrow> g (f x) = x \<and> f (g x) = x) \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! n \<equiv>[Imod] l1 ! g n)"
        using container_bij_equiv_translation length_eq
        by blast
      then show "\<exists>f. bij_betw f {..<length l2} {..<length l1} \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l2 ! n \<equiv>[Imod] l1 ! f n)"
        using length_eq
        by fastforce
    qed
  next
    case (rule_setof_equiv l1 l2)
    then show ?case
    proof (intro value_equiv.rule_setof_equiv)
      assume "length l1 = length l2"
      then show "length l2 = length l1"
        by simp
    next
      assume length_eq: "length l1 = length l2"
      assume "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! f n \<equiv>[Imod] l1 ! n)"
      then have "\<exists>f g. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> (\<forall>x. x \<in> {..<length l1} \<longrightarrow> g (f x) = x \<and> f (g x) = x) \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! f n \<equiv>[Imod] l1 ! n)"
        using container_bij_inverse_ex length_eq
        by metis
      then have "\<exists>f g. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> (\<forall>x. x \<in> {..<length l1} \<longrightarrow> g (f x) = x \<and> f (g x) = x) \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! n \<equiv>[Imod] l1 ! g n)"
        using container_bij_equiv_translation length_eq
        by blast
      then show "\<exists>f. bij_betw f {..<length l2} {..<length l1} \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l2 ! n \<equiv>[Imod] l1 ! f n)"
        using length_eq
        by fastforce
    qed
  next
    case (rule_seqof_equiv l1 l2)
    then show ?case
    proof (intro value_equiv.rule_seqof_equiv)
      assume "length l1 = length l2"
      then show "length l2 = length l1"
        by simp
    next
      assume length_eq: "length l1 = length l2"
      assume "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! n \<and> l2 ! n \<equiv>[Imod] l1 ! n"
      then show "\<forall>n. n \<in> {..<length l2} \<longrightarrow> l2 ! n \<equiv>[Imod] l1 ! n"
        by (simp add: length_eq)
    qed
  next
    case (rule_ordof_equiv l1 l2)
    then show ?case
    proof (intro value_equiv.rule_ordof_equiv)
      assume "length l1 = length l2"
      then show "length l2 = length l1"
        by simp
    next
      assume length_eq: "length l1 = length l2"
      assume "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! n \<and> l2 ! n \<equiv>[Imod] l1 ! n"
      then show "\<forall>n. n \<in> {..<length l2} \<longrightarrow> l2 ! n \<equiv>[Imod] l1 ! n"
        by (simp add: length_eq)
    qed
  qed
next
  assume "y \<equiv>[Imod] x"
  then show "x \<equiv>[Imod] y"
  proof (induct)
    case (rule_atom_equiv v1 v2)
    then show ?case
      by (simp add: value_equiv.rule_atom_equiv)
  next
    case (rule_bagof_equiv l1 l2)
    then show ?case
    proof (intro value_equiv.rule_bagof_equiv)
      assume "length l1 = length l2"
      then show "length l2 = length l1"
        by simp
    next
      assume length_eq: "length l1 = length l2"
      assume "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! f n \<equiv>[Imod] l1 ! n)"
      then have "\<exists>f g. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> (\<forall>x. x \<in> {..<length l1} \<longrightarrow> g (f x) = x \<and> f (g x) = x) \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! f n \<equiv>[Imod] l1 ! n)"
        using container_bij_inverse_ex length_eq
        by metis
      then have "\<exists>f g. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> (\<forall>x. x \<in> {..<length l1} \<longrightarrow> g (f x) = x \<and> f (g x) = x) \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! n \<equiv>[Imod] l1 ! g n)"
        using container_bij_equiv_translation length_eq
        by blast
      then show "\<exists>f. bij_betw f {..<length l2} {..<length l1} \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l2 ! n \<equiv>[Imod] l1 ! f n)"
        using length_eq
        by fastforce
    qed
  next
    case (rule_setof_equiv l1 l2)
    then show ?case
    proof (intro value_equiv.rule_setof_equiv)
      assume "length l1 = length l2"
      then show "length l2 = length l1"
        by simp
    next
      assume length_eq: "length l1 = length l2"
      assume "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! f n \<equiv>[Imod] l1 ! n)"
      then have "\<exists>f g. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> (\<forall>x. x \<in> {..<length l1} \<longrightarrow> g (f x) = x \<and> f (g x) = x) \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! f n \<equiv>[Imod] l1 ! n)"
        using container_bij_inverse_ex length_eq
        by metis
      then have "\<exists>f g. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> (\<forall>x. x \<in> {..<length l1} \<longrightarrow> g (f x) = x \<and> f (g x) = x) \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! f n \<and> l2 ! n \<equiv>[Imod] l1 ! g n)"
        using container_bij_equiv_translation length_eq
        by blast
      then show "\<exists>f. bij_betw f {..<length l2} {..<length l1} \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l2 ! n \<equiv>[Imod] l1 ! f n)"
        using length_eq
        by fastforce
    qed
  next
    case (rule_seqof_equiv l1 l2)
    then show ?case
    proof (intro value_equiv.rule_seqof_equiv)
      assume "length l1 = length l2"
      then show "length l2 = length l1"
        by simp
    next
      assume length_eq: "length l1 = length l2"
      assume "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! n \<and> l2 ! n \<equiv>[Imod] l1 ! n"
      then show "\<forall>n. n \<in> {..<length l2} \<longrightarrow> l2 ! n \<equiv>[Imod] l1 ! n"
        by (simp add: length_eq)
    qed
  next
    case (rule_ordof_equiv l1 l2)
    then show ?case
    proof (intro value_equiv.rule_ordof_equiv)
      assume "length l1 = length l2"
      then show "length l2 = length l1"
        by simp
    next
      assume length_eq: "length l1 = length l2"
      assume "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[Imod] l2 ! n \<and> l2 ! n \<equiv>[Imod] l1 ! n"
      then show "\<forall>n. n \<in> {..<length l2} \<longrightarrow> l2 ! n \<equiv>[Imod] l1 ! n"
        by (simp add: length_eq)
    qed
  qed
qed

lemma value_equiv_transitive[simp]: "x \<equiv>[Imod] y \<Longrightarrow> y \<equiv>[Imod] z \<Longrightarrow> x \<equiv>[Imod] z"
proof-
  fix y z
  assume x_y_equiv: "y \<equiv>[Imod] z"
  then show "\<And>x. x \<equiv>[Imod] y \<Longrightarrow> x \<equiv>[Imod] z"
  proof (induct)
    case (rule_atom_equiv v1 v2)
    show ?case
      using rule_atom_equiv.prems rule_atom_equiv.hyps
    proof (induct)
      case (rule_atom_equiv v3 v4)
      then show ?case
        by simp
    next
      case (rule_bagof_equiv l3 l4)
      then show ?case
        using value_equiv.rule_bagof_equiv
        by blast
    next
      case (rule_setof_equiv l3 l4)
      then show ?case
        using value_equiv.rule_setof_equiv
        by blast
    next
      case (rule_seqof_equiv l3 l4)
      then show ?case
        using value_equiv.rule_seqof_equiv
        by blast
    next
      case (rule_ordof_equiv l3 l4)
      then show ?case
        using value_equiv.rule_ordof_equiv
        by blast
    qed
  next
    case (rule_bagof_equiv l1 l2)
    show ?case
      using rule_bagof_equiv.prems
    proof (cases)
      case rule_atom_equiv
      then show ?thesis
        using rule_bagof_equiv.hyps(1) rule_bagof_equiv.hyps(2) value_equiv.rule_bagof_equiv
        by blast
    next
      case (rule_bagof_equiv l3)
      have "bagof l3 \<equiv>[Imod] bagof l2"
      proof (rule value_equiv.rule_bagof_equiv)
        show "length l3 = length l2"
          by (simp add: local.rule_bagof_equiv(2) rule_bagof_equiv.hyps(1))
      next
        have length_eq: "length l2 = length l3"
          by (simp add: local.rule_bagof_equiv(2) rule_bagof_equiv.hyps(1))
        have "\<exists>f. bij_betw f {..<length l3} {..<length l1} \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l1 ! f n \<equiv>[Imod] l3 ! n)"
          using local.rule_bagof_equiv(3) value_equiv_sym
          by blast
        then have "\<exists>f g. bij_betw f {..<length l3} {..<length l1} \<and> bij_betw g {..<length l3} {..<length l1} \<and> (\<forall>x. x \<in> {..<length l3} \<longrightarrow> g (f x) = x) \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l1 ! f n \<equiv>[Imod] l3 ! n)"
          using container_bij_inverse_ex local.rule_bagof_equiv(2)
          by metis
        then have "\<exists>f g. bij_betw f {..<length l3} {..<length l1} \<and> bij_betw g {..<length l3} {..<length l1} \<and> (\<forall>x. x \<in> {..<length l3} \<longrightarrow> g (f x) = x) \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l1 ! n \<equiv>[Imod] l3 ! g n)"
          using container_bij_equiv_translation local.rule_bagof_equiv(2)
          by blast
        then have "\<exists>f g. bij_betw f {..<length l3} {..<length l1} \<and> bij_betw g {..<length l3} {..<length l1} \<and> (\<forall>x. x \<in> {..<length l3} \<longrightarrow> g (f x) = x) \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l3 ! g n \<equiv>[Imod] l1 ! n)"
          using value_equiv_sym
          by blast
        then have "\<exists>f. bij_betw f {..<length l3} {..<length l1} \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l3 ! f n \<equiv>[Imod] l1 ! n)"
          by blast
        then have "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l3 ! f n \<equiv>[Imod] l1 ! n)"
          using local.rule_bagof_equiv(2) length_eq
          by simp
        then have "\<exists>f g. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l3 ! f n \<equiv>[Imod] l2 ! g n)"
          using rule_bagof_equiv.hyps(2)
          by metis
        then have "\<exists>f g h. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> bij_betw h {..<length l1} {..<length l2} \<and> (\<forall>x. x \<in> {..<length l1} \<longrightarrow> h (f x) = x) \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l3 ! f n \<equiv>[Imod] l2 ! g n)"
          using container_bij_inverse_ex rule_bagof_equiv.hyps(1)
          by metis
        then have "\<exists>f g h. bij_betw f {..<length l2} {..<length l3} \<and> bij_betw g {..<length l2} {..<length l3} \<and> bij_betw h {..<length l2} {..<length l3} \<and> (\<forall>x. x \<in> {..<length l2} \<longrightarrow> h (f x) = x) \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l3 ! f n \<equiv>[Imod] l2 ! g n)"
          using length_eq rule_bagof_equiv.hyps(1)
          by simp
        then have "\<exists>f g h. bij_betw f {..<length l2} {..<length l3} \<and> bij_betw g {..<length l2} {..<length l3} \<and> bij_betw h {..<length l2} {..<length l3} \<and> (\<forall>x. x \<in> {..<length l2} \<longrightarrow> h (f x) = x) \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l3 ! n \<equiv>[Imod] l2 ! g (h n))"
          using container_bij_equiv_translation_alt length_eq
          by blast
        then have "\<exists>f g. bij_betw f {..<length l2} {..<length l3} \<and> bij_betw g {..<length l2} {..<length l3} \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l3 ! n \<equiv>[Imod] l2 ! g (f n))"
          by blast
        then have "\<exists>f. bij_betw f {..<length l2} {..<length l3} \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l3 ! n \<equiv>[Imod] l2 ! f n)"
          using container_bij_equiv_merge length_eq
          by force
        then show "\<exists>f. bij_betw f {..<length l3} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l3 ! n \<equiv>[Imod] l2 ! f n)"
          using length_eq
          by simp
      qed
      then show ?thesis
        using local.rule_bagof_equiv(1)
        by blast
    qed
  next
    case (rule_setof_equiv l1 l2)
    show ?case
      using rule_setof_equiv.prems
    proof (cases)
      case rule_atom_equiv
      then show ?thesis
        using rule_setof_equiv.hyps(1) rule_setof_equiv.hyps(2) value_equiv.rule_setof_equiv
        by blast
    next
      case (rule_setof_equiv l3)
      have "setof l3 \<equiv>[Imod] setof l2"
      proof (rule value_equiv.rule_setof_equiv)
        show "length l3 = length l2"
          by (simp add: local.rule_setof_equiv(2) rule_setof_equiv.hyps(1))
      next
        have length_eq: "length l2 = length l3"
          by (simp add: local.rule_setof_equiv(2) rule_setof_equiv.hyps(1))
        have "\<exists>f. bij_betw f {..<length l3} {..<length l1} \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l1 ! f n \<equiv>[Imod] l3 ! n)"
          using local.rule_setof_equiv(3) value_equiv_sym
          by blast
        then have "\<exists>f g. bij_betw f {..<length l3} {..<length l1} \<and> bij_betw g {..<length l3} {..<length l1} \<and> (\<forall>x. x \<in> {..<length l3} \<longrightarrow> g (f x) = x) \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l1 ! f n \<equiv>[Imod] l3 ! n)"
          using container_bij_inverse_ex local.rule_setof_equiv(2)
          by metis
        then have "\<exists>f g. bij_betw f {..<length l3} {..<length l1} \<and> bij_betw g {..<length l3} {..<length l1} \<and> (\<forall>x. x \<in> {..<length l3} \<longrightarrow> g (f x) = x) \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l1 ! n \<equiv>[Imod] l3 ! g n)"
          using container_bij_equiv_translation local.rule_setof_equiv(2)
          by blast
        then have "\<exists>f g. bij_betw f {..<length l3} {..<length l1} \<and> bij_betw g {..<length l3} {..<length l1} \<and> (\<forall>x. x \<in> {..<length l3} \<longrightarrow> g (f x) = x) \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l3 ! g n \<equiv>[Imod] l1 ! n)"
          using value_equiv_sym
          by blast
        then have "\<exists>f. bij_betw f {..<length l3} {..<length l1} \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l3 ! f n \<equiv>[Imod] l1 ! n)"
          by blast
        then have "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l3 ! f n \<equiv>[Imod] l1 ! n)"
          using local.rule_setof_equiv(2) length_eq
          by simp
        then have "\<exists>f g. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l3 ! f n \<equiv>[Imod] l2 ! g n)"
          using rule_setof_equiv.hyps(2)
          by metis
        then have "\<exists>f g h. bij_betw f {..<length l1} {..<length l2} \<and> bij_betw g {..<length l1} {..<length l2} \<and> bij_betw h {..<length l1} {..<length l2} \<and> (\<forall>x. x \<in> {..<length l1} \<longrightarrow> h (f x) = x) \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l3 ! f n \<equiv>[Imod] l2 ! g n)"
          using container_bij_inverse_ex rule_setof_equiv.hyps(1)
          by metis
        then have "\<exists>f g h. bij_betw f {..<length l2} {..<length l3} \<and> bij_betw g {..<length l2} {..<length l3} \<and> bij_betw h {..<length l2} {..<length l3} \<and> (\<forall>x. x \<in> {..<length l2} \<longrightarrow> h (f x) = x) \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l3 ! f n \<equiv>[Imod] l2 ! g n)"
          using length_eq rule_setof_equiv.hyps(1)
          by simp
        then have "\<exists>f g h. bij_betw f {..<length l2} {..<length l3} \<and> bij_betw g {..<length l2} {..<length l3} \<and> bij_betw h {..<length l2} {..<length l3} \<and> (\<forall>x. x \<in> {..<length l2} \<longrightarrow> h (f x) = x) \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l3 ! n \<equiv>[Imod] l2 ! g (h n))"
          using container_bij_equiv_translation_alt length_eq
          by blast
        then have "\<exists>f g. bij_betw f {..<length l2} {..<length l3} \<and> bij_betw g {..<length l2} {..<length l3} \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l3 ! n \<equiv>[Imod] l2 ! g (f n))"
          by blast
        then have "\<exists>f. bij_betw f {..<length l2} {..<length l3} \<and> (\<forall>n. n \<in> {..<length l2} \<longrightarrow> l3 ! n \<equiv>[Imod] l2 ! f n)"
          using container_bij_equiv_merge length_eq
          by force
        then show "\<exists>f. bij_betw f {..<length l3} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l3} \<longrightarrow> l3 ! n \<equiv>[Imod] l2 ! f n)"
          using length_eq
          by simp
      qed
      then show ?thesis
        using local.rule_setof_equiv(1)
        by blast
    qed
  next
    case (rule_seqof_equiv l1 l2)
    show ?case
      using rule_seqof_equiv.prems
    proof (cases)
      case rule_atom_equiv
      then show ?thesis
        using rule_seqof_equiv.hyps(1) rule_seqof_equiv.hyps(2) value_equiv.rule_seqof_equiv
        by blast
    next
      case (rule_seqof_equiv l3)
      have "seqof l3 \<equiv>[Imod] seqof l2"
      proof (rule value_equiv.rule_seqof_equiv)
        show "length l3 = length l2"
          by (simp add: local.rule_seqof_equiv(2) rule_seqof_equiv.hyps(1))
      next
        have "\<forall>n. n \<in> {..<length l3} \<longrightarrow> l3 ! n \<equiv>[Imod] l1 ! n"
          using local.rule_seqof_equiv(3)
          by blast
        then show "\<forall>n. n \<in> {..<length l3} \<longrightarrow> l3 ! n \<equiv>[Imod] l2 ! n"
          using rule_seqof_equiv.hyps(2) local.rule_seqof_equiv(2)
          by metis
      qed
      then show ?thesis
        using local.rule_seqof_equiv(1)
        by blast
    qed
  next
    case (rule_ordof_equiv l1 l2)
    show ?case
      using rule_ordof_equiv.prems
    proof (cases)
      case rule_atom_equiv
      then show ?thesis
        using rule_ordof_equiv.hyps(1) rule_ordof_equiv.hyps(2) value_equiv.rule_ordof_equiv
        by blast
    next
      case (rule_ordof_equiv l3)
      have "ordof l3 \<equiv>[Imod] ordof l2"
      proof (rule value_equiv.rule_ordof_equiv)
        show "length l3 = length l2"
          by (simp add: local.rule_ordof_equiv(2) rule_ordof_equiv.hyps(1))
      next
        have "\<forall>n. n \<in> {..<length l3} \<longrightarrow> l3 ! n \<equiv>[Imod] l1 ! n"
          using local.rule_ordof_equiv(3)
          by blast
        then show "\<forall>n. n \<in> {..<length l3} \<longrightarrow> l3 ! n \<equiv>[Imod] l2 ! n"
          using rule_ordof_equiv.hyps(2) local.rule_ordof_equiv(2)
          by metis
      qed
      then show ?thesis
        using local.rule_ordof_equiv(1)
        by blast
    qed
  qed
qed

lemma value_equiv_existance[simp]: "x \<in> Value Imod \<Longrightarrow> \<exists>y. y \<in> Value Imod \<and> x \<equiv>[Imod] y"
  using rule_atom_equiv by auto

lemma value_equiv_atom_value_preserved: "\<And>x y. x \<in> AtomValue Imod \<Longrightarrow> x \<equiv>[ImodX] y \<Longrightarrow> y \<in> AtomValue Imod"
proof-
  fix x y
  assume x_in_value: "x \<in> AtomValue Imod"
  assume "x \<equiv>[ImodX] y"
  then show "y \<in> AtomValue Imod"
    using x_in_value
  proof (induct)
    case (rule_atom_equiv v1 v2)
    then show ?case
      by simp
  next
    case (rule_bagof_equiv l1 l2)
    then show ?case
      using no_bags_in_atom_values rule_bagof_equiv.prems by blast
  next
    case (rule_setof_equiv l1 l2)
    then show ?case
      using no_sets_in_atom_values rule_setof_equiv.prems by blast
  next
    case (rule_seqof_equiv l1 l2)
    then show ?case
      using no_seqs_in_atom_values rule_seqof_equiv.prems by blast
  next
    case (rule_ordof_equiv l1 l2)
    then show ?case
      using no_ords_in_atom_values rule_ordof_equiv.prems by blast
  qed
qed

lemma value_equiv_container_value_preserved: "\<And>x y. x \<in> ContainerValue Imod \<Longrightarrow> x \<equiv>[ImodX] y \<Longrightarrow> y \<in> ContainerValue Imod"
proof-
  fix x y
  assume x_in_value: "x \<in> ContainerValue Imod"
  assume "x \<equiv>[ImodX] y"
  then show "y \<in> ContainerValue Imod"
    using x_in_value
  proof (induct)
    case (rule_atom_equiv v1 v2)
    then show ?case
      by simp
  next
    case (rule_bagof_equiv l1 l2)
    then have "l1 \<in> ContainerValueList Imod \<or> l1 \<in> AtomValueList Imod"
      using contained_list.simps(1) container_value_members_alt
      by metis
    then show ?case
    proof (elim disjE)
      assume "l1 \<in> ContainerValueList Imod"
      then have "\<And>x. x \<in> set l1 \<Longrightarrow> x \<in> ContainerValue Imod"
        by simp
      then have "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[ImodX] l2 ! f n \<and> l2 ! f n \<in> ContainerValue Imod)"
        using rule_bagof_equiv.hyps(2)
        by simp
      then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l2 ! n \<in> ContainerValue Imod"
        using bij_betw_def imageE rule_bagof_equiv.hyps(1)
        by metis
      then have "\<And>x. x \<in> set l2 \<Longrightarrow> x \<in> ContainerValue Imod"
        using in_set_conv_nth lessThan_iff rule_bagof_equiv.hyps(1)
        by metis
      then have "l2 \<in> ContainerValueList Imod"
        using list_of_container_values_in_container_value_list
        by blast
      then show ?thesis
        by (fact ContainerValue.rule_bagof_container_values)
    next
      assume "l1 \<in> AtomValueList Imod"
      then show ?thesis
      proof (induct "l1 = []")
        case True
        then show ?case
          using rule_bagof_equiv.hyps(1) rule_bagof_equiv.prems
          by simp
      next
        case False
          then have "\<And>x. x \<in> set l1 \<Longrightarrow> x \<in> AtomValue Imod"
          by simp
        then have "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[ImodX] l2 ! f n \<and> l2 ! f n \<in> AtomValue Imod)"
          using lessThan_iff nth_mem rule_bagof_equiv.hyps(2) value_equiv_atom_value_preserved
          by metis
        then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l2 ! n \<in> AtomValue Imod"
          using bij_betw_def imageE rule_bagof_equiv.hyps(1)
          by metis
        then have "\<And>x. x \<in> set l2 \<Longrightarrow> x \<in> AtomValue Imod"
          using in_set_conv_nth lessThan_iff rule_bagof_equiv.hyps(1)
          by metis
        then have "l2 \<in> AtomValueList Imod"
          using False.hyps list_of_atom_values_in_atom_value_list_alt length_0_conv rule_bagof_equiv.hyps(1) subsetI
          by metis
        then show ?case
          by (fact ContainerValue.rule_bagof_atom_values)
      qed
    qed
  next
    case (rule_setof_equiv l1 l2)
    then have "l1 \<in> ContainerValueList Imod \<or> l1 \<in> AtomValueList Imod"
      using contained_list.simps(2) container_value_members_alt
      by metis
    then show ?case
    proof (elim disjE)
      assume "l1 \<in> ContainerValueList Imod"
      then have "\<And>x. x \<in> set l1 \<Longrightarrow> x \<in> ContainerValue Imod"
        by simp
      then have "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[ImodX] l2 ! f n \<and> l2 ! f n \<in> ContainerValue Imod)"
        using rule_setof_equiv.hyps(2)
        by simp
      then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l2 ! n \<in> ContainerValue Imod"
        using bij_betw_def imageE rule_setof_equiv.hyps(1)
        by metis
      then have "\<And>x. x \<in> set l2 \<Longrightarrow> x \<in> ContainerValue Imod"
        using in_set_conv_nth lessThan_iff rule_setof_equiv.hyps(1)
        by metis
      then have "l2 \<in> ContainerValueList Imod"
        using list_of_container_values_in_container_value_list
        by blast
      then show ?thesis
        by (fact ContainerValue.rule_setof_container_values)
    next
      assume "l1 \<in> AtomValueList Imod"
      then show ?thesis
      proof (induct "l1 = []")
        case True
        then show ?case
          using rule_setof_equiv.hyps(1) rule_setof_equiv.prems
          by simp
      next
        case False
          then have "\<And>x. x \<in> set l1 \<Longrightarrow> x \<in> AtomValue Imod"
          by simp
        then have "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[ImodX] l2 ! f n \<and> l2 ! f n \<in> AtomValue Imod)"
          using lessThan_iff nth_mem rule_setof_equiv.hyps(2) value_equiv_atom_value_preserved
          by metis
        then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l2 ! n \<in> AtomValue Imod"
          using bij_betw_def imageE rule_setof_equiv.hyps(1)
          by metis
        then have "\<And>x. x \<in> set l2 \<Longrightarrow> x \<in> AtomValue Imod"
          using in_set_conv_nth lessThan_iff rule_setof_equiv.hyps(1)
          by metis
        then have "l2 \<in> AtomValueList Imod"
          using False.hyps list_of_atom_values_in_atom_value_list_alt length_0_conv rule_setof_equiv.hyps(1) subsetI
          by metis
        then show ?case
          by (fact ContainerValue.rule_setof_atom_values)
      qed
    qed
  next
    case (rule_seqof_equiv l1 l2)
    then have "l1 \<in> ContainerValueList Imod \<or> l1 \<in> AtomValueList Imod"
      using contained_list.simps(3) container_value_members_alt
      by metis
    then show ?case
    proof (elim disjE)
      assume "l1 \<in> ContainerValueList Imod"
      then have "\<And>x. x \<in> set l1 \<Longrightarrow> x \<in> ContainerValue Imod"
        by simp
      then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[ImodX] l2 ! n \<and> l2 ! n \<in> ContainerValue Imod"
        using rule_seqof_equiv.hyps(2)
        by simp
      then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l2 ! n \<in> ContainerValue Imod"
        by simp
      then have "\<And>x. x \<in> set l2 \<Longrightarrow> x \<in> ContainerValue Imod"
        using in_set_conv_nth lessThan_iff rule_seqof_equiv.hyps(1)
        by metis
      then have "l2 \<in> ContainerValueList Imod"
        using list_of_container_values_in_container_value_list
        by blast
      then show ?thesis
        by (fact ContainerValue.rule_seqof_container_values)
    next
      assume "l1 \<in> AtomValueList Imod"
      then show ?thesis
      proof (induct "l1 = []")
        case True
        then show ?case
          using rule_seqof_equiv.hyps(1) rule_seqof_equiv.prems
          by simp
      next
        case False
          then have "\<And>x. x \<in> set l1 \<Longrightarrow> x \<in> AtomValue Imod"
          by simp
        then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[ImodX] l2 ! n \<and> l2 ! n \<in> AtomValue Imod"
          using lessThan_iff nth_mem rule_seqof_equiv.hyps(2) value_equiv_atom_value_preserved
          by metis
        then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l2 ! n \<in> AtomValue Imod"
          by simp
        then have "\<And>x. x \<in> set l2 \<Longrightarrow> x \<in> AtomValue Imod"
          using in_set_conv_nth lessThan_iff rule_seqof_equiv.hyps(1)
          by metis
        then have "l2 \<in> AtomValueList Imod"
          using False.hyps list_of_atom_values_in_atom_value_list_alt length_0_conv rule_seqof_equiv.hyps(1) subsetI
          by metis
        then show ?case
          by (fact ContainerValue.rule_seqof_atom_values)
      qed
    qed
  next
    case (rule_ordof_equiv l1 l2)
    then have "l1 \<in> ContainerValueList Imod \<or> l1 \<in> AtomValueList Imod"
      using contained_list.simps(4) container_value_members_alt
      by metis
    then show ?case
    proof (elim disjE)
      assume "l1 \<in> ContainerValueList Imod"
      then have "\<And>x. x \<in> set l1 \<Longrightarrow> x \<in> ContainerValue Imod"
        by simp
      then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[ImodX] l2 ! n \<and> l2 ! n \<in> ContainerValue Imod"
        using rule_ordof_equiv.hyps(2)
        by simp
      then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l2 ! n \<in> ContainerValue Imod"
        by simp
      then have "\<And>x. x \<in> set l2 \<Longrightarrow> x \<in> ContainerValue Imod"
        using in_set_conv_nth lessThan_iff rule_ordof_equiv.hyps(1)
        by metis
      then have "l2 \<in> ContainerValueList Imod"
        using list_of_container_values_in_container_value_list
        by blast
      then show ?thesis
        by (fact ContainerValue.rule_ordof_container_values)
    next
      assume "l1 \<in> AtomValueList Imod"
      then show ?thesis
      proof (induct "l1 = []")
        case True
        then show ?case
          using rule_ordof_equiv.hyps(1) rule_ordof_equiv.prems
          by simp
      next
        case False
          then have "\<And>x. x \<in> set l1 \<Longrightarrow> x \<in> AtomValue Imod"
          by simp
        then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l1 ! n \<equiv>[ImodX] l2 ! n \<and> l2 ! n \<in> AtomValue Imod"
          using lessThan_iff nth_mem rule_ordof_equiv.hyps(2) value_equiv_atom_value_preserved
          by metis
        then have "\<forall>n. n \<in> {..<length l1} \<longrightarrow> l2 ! n \<in> AtomValue Imod"
          by simp
        then have "\<And>x. x \<in> set l2 \<Longrightarrow> x \<in> AtomValue Imod"
          using in_set_conv_nth lessThan_iff rule_ordof_equiv.hyps(1)
          by metis
        then have "l2 \<in> AtomValueList Imod"
          using False.hyps list_of_atom_values_in_atom_value_list_alt length_0_conv rule_ordof_equiv.hyps(1) subsetI
          by metis
        then show ?case
          by (fact ContainerValue.rule_ordof_atom_values)
      qed
    qed
  qed
qed

lemma value_equiv_value_preserved: "\<And>x y. x \<in> Value Imod \<Longrightarrow> x \<equiv>[ImodX] y \<Longrightarrow> y \<in> Value Imod"
  unfolding Value_def
  using value_equiv_atom_value_preserved value_equiv_container_value_preserved
  by fastforce

lemma value_equiv_booleans[simp]: "x \<in> BooleanValue \<Longrightarrow> x \<equiv>[Imod] y \<Longrightarrow> y = x"
proof (induct rule: BooleanValue.induct)
  case rule_boolean_true
  then show ?case
    using value_equiv.cases by auto
next
  case rule_boolean_false
  then show ?case
    using value_equiv.cases by auto
qed

lemma value_equiv_integers[simp]: "x \<in> IntegerValue \<Longrightarrow> x \<equiv>[Imod] y \<Longrightarrow> y = x"
proof (induct rule: IntegerValue.induct)
  case (rule_integer i)
  then show ?case
    using value_equiv.cases by auto
qed

lemma value_equiv_reals[simp]: "x \<in> RealValue \<Longrightarrow> x \<equiv>[Imod] y \<Longrightarrow> y = x"
proof (induct rule: RealValue.induct)
  case (rule_real r)
  then show ?case
    using value_equiv.cases by auto
qed

lemma value_equiv_strings[simp]: "x \<in> StringValue \<Longrightarrow> x \<equiv>[Imod] y \<Longrightarrow> y = x"
proof (induct rule: StringValue.induct)
  case (rule_string s)
  then show ?case
    using value_equiv.cases by auto
qed

lemma value_equiv_literals[simp]: "x \<in> LiteralValue \<Longrightarrow> x \<equiv>[Imod] y \<Longrightarrow> y = x"
  unfolding LiteralValue_def
  by (elim UnE) simp_all

lemma value_equiv_proper_classes[simp]: "x \<in> ProperClassValue Imod \<Longrightarrow> x \<equiv>[Imod] y \<Longrightarrow> y = x"
proof (induct rule: ProperClassValue.induct)
  case (rule_proper_objects ob)
  then show ?case
    using value_equiv.cases by auto
qed

lemma value_equiv_classes[simp]: "x \<in> ClassValue Imod \<Longrightarrow> x \<equiv>[Imod] y \<Longrightarrow> y = x"
  unfolding ClassValue_def
  using value_equiv.cases
  by (elim UnE) auto

lemma value_equiv_enumvalues[simp]: "x \<in> EnumValueValue (Tm Imod) \<Longrightarrow> x \<equiv>[Imod] y \<Longrightarrow> y = x"
proof (induct rule: EnumValueValue.induct)
  case (rule_enumvalue ev)
  then show ?case
    using value_equiv.cases by auto
qed

lemma value_equiv_userdatavalues[simp]: "x \<in> UserDataValue \<Longrightarrow> x \<equiv>[Imod] y \<Longrightarrow> y = x"
proof (induct rule: UserDataValue.induct)
  case (rule_userdatavalue s)
  then show ?case
    using value_equiv.cases by auto
qed

lemma value_equiv_atoms[simp]: "x \<in> AtomValue Imod \<Longrightarrow> x \<equiv>[Imod] y \<Longrightarrow> y = x"
  unfolding AtomValue_def
  by (elim UnE) simp_all

lemma value_equiv_bagof_single_element[simp]: "v1 \<equiv>[Imod] v2 \<Longrightarrow> bagof [v1] \<equiv>[Imod] bagof [v2]"
proof (intro rule_bagof_equiv)
  fix x y
  show "v1 \<equiv>[Imod] v2 \<Longrightarrow> length [v1] = length [v2]"
    by simp
next
  assume "v1 \<equiv>[Imod] v2"
  then show "\<exists>f. bij_betw f {..<length [v1]} {..<length [v2]} \<and> (\<forall>n. n \<in> {..<length [v1]} \<longrightarrow> [v1] ! n \<equiv>[Imod] [v2] ! f n)"
    by fastforce
qed

lemma value_equiv_setof_single_element[simp]: "v1 \<equiv>[Imod] v2 \<Longrightarrow> setof [v1] \<equiv>[Imod] setof [v2]"
proof (intro rule_setof_equiv)
  fix x y
  show "v1 \<equiv>[Imod] v2 \<Longrightarrow> length [v1] = length [v2]"
    by simp
next
  assume "v1 \<equiv>[Imod] v2"
  then show "\<exists>f. bij_betw f {..<length [v1]} {..<length [v2]} \<and> (\<forall>n. n \<in> {..<length [v1]} \<longrightarrow> [v1] ! n \<equiv>[Imod] [v2] ! f n)"
    by fastforce
qed

lemma value_equiv_seqof_single_element[simp]: "v1 \<equiv>[Imod] v2 \<Longrightarrow> seqof [v1] \<equiv>[Imod] seqof [v2]"
proof (intro rule_seqof_equiv)
  fix x y
  show "v1 \<equiv>[Imod] v2 \<Longrightarrow> length [v1] = length [v2]"
    by simp
next
  assume "v1 \<equiv>[Imod] v2"
  then show "\<forall>n. n \<in> {..<length [v1]} \<longrightarrow> [v1] ! n \<equiv>[Imod] [v2] ! n"
    by simp
qed

lemma value_equiv_ordof_single_element[simp]: "v1 \<equiv>[Imod] v2 \<Longrightarrow> ordof [v1] \<equiv>[Imod] ordof [v2]"
proof (intro rule_ordof_equiv)
  fix x y
  show "v1 \<equiv>[Imod] v2 \<Longrightarrow> length [v1] = length [v2]"
    by simp
next
  assume "v1 \<equiv>[Imod] v2"
  then show "\<forall>n. n \<in> {..<length [v1]} \<longrightarrow> [v1] ! n \<equiv>[Imod] [v2] ! n"
    by simp
qed

lemma value_equiv_fst_unspecified[simp]: "\<not>unspecified \<equiv>[Imod] v"
proof-
  fix v
  have "\<And>u. u \<equiv>[Imod] v \<Longrightarrow> u \<noteq> unspecified"
  proof-
    fix u 
    assume "u \<equiv>[Imod] v"
    then show "u \<noteq> unspecified"
    proof (induct)
      case (rule_atom_equiv v1 v2)
      then show ?case
        by auto
    next
      case (rule_bagof_equiv l1 l2)
      then show ?case
        by blast
    next
      case (rule_setof_equiv l1 l2)
      then show ?case
        by blast
    next
      case (rule_seqof_equiv l1 l2)
      then show ?case
        by blast
    next
      case (rule_ordof_equiv l1 l2)
      then show ?case
        by blast
    qed
  qed
  then show "\<not>unspecified \<equiv>[Imod] v"
    by blast
qed

lemma value_equiv_snd_unspecified[simp]: "\<not>v \<equiv>[Imod] unspecified"
  using value_equiv_fst_unspecified value_equiv_sym
  by blast

lemma value_equiv_fst_invalid[simp]: "\<not>invalid \<equiv>[Imod] v"
proof-
  fix v
  have "\<And>u. u \<equiv>[Imod] v \<Longrightarrow> u \<noteq> invalid"
  proof-
    fix u 
    assume "u \<equiv>[Imod] v"
    then show "u \<noteq> invalid"
    proof (induct)
      case (rule_atom_equiv v1 v2)
      then show ?case
        by auto
    next
      case (rule_bagof_equiv l1 l2)
      then show ?case
        by blast
    next
      case (rule_setof_equiv l1 l2)
      then show ?case
        by blast
    next
      case (rule_seqof_equiv l1 l2)
      then show ?case
        by blast
    next
      case (rule_ordof_equiv l1 l2)
      then show ?case
        by blast
    qed
  qed
  then show "\<not>invalid \<equiv>[Imod] v"
    by blast
qed

lemma value_equiv_snd_invalid[simp]: "\<not>v \<equiv>[Imod] invalid"
  using value_equiv_fst_invalid value_equiv_sym
  by blast



section "Valid type values"

primrec distinct_values :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) ValueDef list \<Rightarrow> bool" where
"distinct_values Imod [] \<longleftrightarrow> True" |
"distinct_values Imod (x # xs) \<longleftrightarrow> (\<forall>y. y \<in> set xs \<longrightarrow> \<not>(x \<equiv>[Imod] y)) \<and> distinct_values Imod xs"

inductive_set Valid_rel :: "('o, 'nt) instance_model \<Rightarrow> (('nt) TypeDef \<times> ('o, 'nt) ValueDef) set"
  for Imod :: "('o, 'nt) instance_model"
  where
    valid_rule_booleans: "v \<in> BooleanValue \<Longrightarrow> (TypeDef.boolean, v) \<in> Valid_rel Imod" |
    valid_rule_integers: "v \<in> IntegerValue \<Longrightarrow> (TypeDef.integer, v) \<in> Valid_rel Imod" |
    valid_rule_reals: "v \<in> RealValue \<Longrightarrow> (TypeDef.real, v) \<in> Valid_rel Imod" |
    valid_rule_strings: "v \<in> StringValue \<Longrightarrow> (TypeDef.string, v) \<in> Valid_rel Imod" |
    valid_rule_proper_classes: "v \<in> Object Imod \<Longrightarrow> t \<in> ClassType (Tm Imod) \<Longrightarrow> \<exclamdown>(ObjectClass Imod v) \<sqsubseteq>[Tm Imod] t \<Longrightarrow> (t, obj v) \<in> Valid_rel Imod" |
    valid_rule_nullable_classes: "t \<in> NullableClassType (Tm Imod) \<Longrightarrow> (t, nil) \<in> Valid_rel Imod" |
    valid_rule_enumvalues: "(t, v) \<in> EnumValue (Tm Imod) \<Longrightarrow> TypeDef.enumtype t \<in> EnumType (Tm Imod) \<Longrightarrow> (TypeDef.enumtype t, enum (t, v)) \<in> Valid_rel Imod" |
    valid_rule_userdata_values: "v \<in> UserDataValue \<Longrightarrow> t \<in> UserDataTypeType (Tm Imod) \<Longrightarrow> (t, v) \<in> Valid_rel Imod" |
    valid_rule_bags: "t \<in> BagContainerType (Tm Imod) \<Longrightarrow> vs \<in> BagContainerValue Imod \<Longrightarrow> (\<And>x. x \<in> set (contained_list vs) \<Longrightarrow> (contained_type t, x) \<in> Valid_rel Imod) \<Longrightarrow> (t, vs) \<in> Valid_rel Imod" |
    valid_rule_sets: "t \<in> SetContainerType (Tm Imod) \<Longrightarrow> vs \<in> SetContainerValue Imod \<Longrightarrow> distinct_values Imod (contained_list vs) \<Longrightarrow> (\<And>x. x \<in> set (contained_list vs) \<Longrightarrow> (contained_type t, x) \<in> Valid_rel Imod) \<Longrightarrow> (t, vs) \<in> Valid_rel Imod" |
    valid_rule_seqs: "t \<in> SeqContainerType (Tm Imod) \<Longrightarrow> vs \<in> SeqContainerValue Imod \<Longrightarrow> (\<And>x. x \<in> set (contained_list vs) \<Longrightarrow> (contained_type t, x) \<in> Valid_rel Imod) \<Longrightarrow> (t, vs) \<in> Valid_rel Imod" |
    valid_rule_ords: "t \<in> OrdContainerType (Tm Imod) \<Longrightarrow> vs \<in> OrdContainerValue Imod \<Longrightarrow> distinct_values Imod (contained_list vs) \<Longrightarrow> (\<And>x. x \<in> set (contained_list vs) \<Longrightarrow> (contained_type t, x) \<in> Valid_rel Imod) \<Longrightarrow> (t, vs) \<in> Valid_rel Imod"

definition Valid :: "('o, 'nt) ValueDef \<Rightarrow> ('o, 'nt) instance_model \<Rightarrow> ('nt) TypeDef \<Rightarrow> bool" where
  "Valid v Imod T \<equiv> (T, v) \<in> Valid_rel Imod"

notation Valid ("(_/ :[_] _)" [52, 51, 52] 50)


subsection "Lemmas on the value validity"

lemma distinct_values_append: "distinct_values Imod xs \<Longrightarrow> \<forall>y. y \<in> set xs \<longrightarrow> \<not>(x \<equiv>[Imod] y) \<Longrightarrow> distinct_values Imod (xs @ [x])"
proof-
  fix xs x
  assume xs_distinct: "distinct_values Imod xs"
  assume "\<forall>y. y \<in> set xs \<longrightarrow> \<not>(x \<equiv>[Imod] y)"
  then show "distinct_values Imod (xs @ [x])"
    using xs_distinct
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a xs)
    then show ?case
      by simp
  qed
qed

lemma distinct_values_append_rev: "distinct_values Imod (xs @ ys) \<Longrightarrow> distinct_values Imod xs"
proof-
  fix xs x
  assume "distinct_values Imod (xs @ ys)"
  then show "distinct_values Imod xs"
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a xs)
    then show ?case
      by simp
  qed
qed

lemma distinct_values_append_rev_single: "distinct_values Imod (xs @ [x]) \<Longrightarrow> \<forall>y. y \<in> set xs \<longrightarrow> \<not>(x \<equiv>[Imod] y)"
proof-
  assume "distinct_values Imod (xs @ [x])"
  then show "\<forall>y. y \<in> set xs \<longrightarrow> \<not>(x \<equiv>[Imod] y)"
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a xs)
    then show ?case
      by simp
  qed
qed

lemma distinct_values_impl_distinct: "set xs \<subseteq> Value Imod \<Longrightarrow> distinct_values Imod xs \<Longrightarrow> distinct xs \<and> (\<forall>x1 x2. x1 \<in> set xs \<and> x2 \<in> set xs \<longrightarrow> x1 \<equiv>[Imod] x2 \<longrightarrow> x1 = x2)"
proof
  assume distinct_values_xs: "distinct_values Imod xs"
  then have unique_under_equiv: "\<And>x1 x2. x1 \<in> set xs \<Longrightarrow> x2 \<in> set xs \<Longrightarrow> x1 \<equiv>[Imod] x2 \<Longrightarrow> x1 = x2"
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    have x1_cases: "x1 = x \<or> x1 \<in> set xs"
      using Cons.prems(1)
      by fastforce
    have x2_cases: "x2 = x \<or> x2 \<in> set xs"
      using Cons.prems(2)
      by fastforce
    show ?case
      using x1_cases
    proof (elim disjE)
      assume x1_def: "x1 = x"
      then have "\<forall>y. y \<in> set xs \<longrightarrow> \<not>(x1 \<equiv>[Imod] y)"
        using Cons.prems(4) distinct_values.simps(2)
        by blast
      then show "x1 = x2"
        using Cons.prems(2) Cons.prems(3) x1_def
        by auto
    next
      assume x1_in_set_xs: "x1 \<in> set xs"
      show "x1 = x2"
        using x2_cases
      proof (elim disjE)
        assume x2_def: "x2 = x"
        then have "\<forall>y. y \<in> set xs \<longrightarrow> \<not>(x2 \<equiv>[Imod] y)"
          using Cons.prems(4) distinct_values.simps(2)
          by blast
        then show "x1 = x2"
          using Cons.prems(2) Cons.prems(3) x1_in_set_xs x2_def
          by auto
      next
        assume "x2 \<in> set xs"
        then show "x1 = x2"
          using Cons.hyps Cons.prems(3) Cons.prems(4) distinct_values.simps(2) x1_in_set_xs
          by blast
      qed
    qed
  qed
  then show "\<forall>x1 x2. x1 \<in> set xs \<and> x2 \<in> set xs \<longrightarrow> x1 \<equiv>[Imod] x2 \<longrightarrow> x1 = x2"
    by blast
  assume xs_in_value_imod: "set xs \<subseteq> Value Imod"
  then show "distinct xs"
    using distinct_values_xs
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    then have "\<forall>y. y \<in> set xs \<longrightarrow> \<not>(x \<equiv>[Imod] y)"
      by simp
    then have "\<forall>y. y \<in> set xs \<longrightarrow> x \<noteq> y"
      using Cons.prems(1)
      by fastforce
    then show ?case
      using Cons.hyps Cons.prems
      by fastforce
  qed
qed

lemma distinct_values_impl_distinct_rev: "distinct xs \<Longrightarrow> (\<forall>x1 x2. x1 \<in> set xs \<and> x2 \<in> set xs \<longrightarrow> x1 \<equiv>[Imod] x2 \<longrightarrow> x1 = x2) \<Longrightarrow> distinct_values Imod xs"
proof-
  assume  "\<forall>x1 x2. x1 \<in> set xs \<and> x2 \<in> set xs \<longrightarrow> x1 \<equiv>[Imod] x2 \<longrightarrow> x1 = x2"
  then have unique_under_equiv: "\<And>x1 x2. x1 \<in> set xs \<Longrightarrow> x2 \<in> set xs \<Longrightarrow> x1 \<equiv>[Imod] x2 \<Longrightarrow> x1 = x2"
    by blast
  assume "distinct xs"
  then show "distinct_values Imod xs"
    using unique_under_equiv
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    then have "\<And>x1 x2. x1 \<in> set xs \<Longrightarrow> x2 \<in> set xs \<Longrightarrow> x1 \<equiv>[Imod] x2 \<Longrightarrow> x1 = x2"
      by fastforce
    then have xs_distinct_values: "distinct_values Imod xs"
      using Cons.hyps Cons.prems(1)
      by simp
    have "\<forall>y. y \<in> set (x # xs) \<longrightarrow> x \<equiv>[Imod] y \<longrightarrow> x = y"
      by (simp add: Cons.prems)
    then have "\<forall>y. y \<in> set xs \<longrightarrow> \<not>(x \<equiv>[Imod] y)"
      using Cons.prems(1)
      by fastforce
    then show ?case
      using distinct_values.simps(2) xs_distinct_values
      by blast
  qed
qed

lemma distinct_values_altdef[simp]: "set xs \<subseteq> Value Imod \<Longrightarrow> distinct_values Imod xs \<longleftrightarrow> distinct xs \<and> (\<forall>x1 x2. x1 \<in> set xs \<and> x2 \<in> set xs \<longrightarrow> x1 \<equiv>[Imod] x2 \<longrightarrow> x1 = x2)"
  using distinct_values_impl_distinct distinct_values_impl_distinct_rev
  by blast

lemma distinct_values_preserved: "\<And>xs ys. set xs \<subseteq> Value Imod \<Longrightarrow> distinct_values Imod xs \<Longrightarrow> length xs = length ys \<Longrightarrow> bij_betw f {..<length xs} {..<length ys} \<and> (\<forall>n. n \<in> {..<length xs} \<longrightarrow> xs ! n \<equiv>[Imod] ys ! f n) \<Longrightarrow> distinct_values Imod ys"
proof-
  fix xs ys
  assume xs_in_value: "set xs \<subseteq> Value Imod"
  assume distinct_values_xs: "distinct_values Imod xs"
  have distinct_xs: "distinct xs"
    using xs_in_value distinct_values_xs distinct_values_altdef
    by blast
  have unique_xs: "\<And>x1 x2. x1 \<in> set xs \<Longrightarrow> x2 \<in> set xs \<Longrightarrow> x1 \<equiv>[Imod] x2 \<Longrightarrow> x1 = x2"
    using xs_in_value distinct_values_xs distinct_values_altdef
    by blast
  assume bijection_xs_ys: "bij_betw f {..<length xs} {..<length ys} \<and> (\<forall>n. n \<in> {..<length xs} \<longrightarrow> xs ! n \<equiv>[Imod] ys ! f n)"
  assume length_eq: "length xs = length ys"
  obtain g where g_def: "bij_betw g {..<length xs} {..<length ys} \<and> (\<forall>x. x \<in> {..<length xs} \<longrightarrow> g (f x) = x)"
    using bijection_xs_ys bij_betw_inv_into bij_betw_inv_into_left length_eq
    by metis
  have "\<And>n1 n2. n1 \<in> {..<length xs} \<Longrightarrow> n2 \<in> {..<length xs} \<Longrightarrow> xs ! n1 \<equiv>[Imod] xs ! n2 \<Longrightarrow> n1 = n2"
    using distinct_xs unique_xs lessThan_iff nth_eq_iff_index_eq nth_mem
    by metis
  then have "\<And>n1 n2. n1 \<in> {..<length ys} \<Longrightarrow> n2 \<in> {..<length ys} \<Longrightarrow> ys ! f n1 \<equiv>[Imod] ys ! f n2 \<Longrightarrow> n1 = n2"
    using length_eq bijection_xs_ys value_equiv_sym value_equiv_transitive
    by metis
  then have "\<And>n1 n2. n1 \<in> {..<length ys} \<Longrightarrow> n2 \<in> {..<length ys} \<Longrightarrow> ys ! g (f n1) \<equiv>[Imod] ys ! g (f n2) \<Longrightarrow> n1 = n2"
    using bij_betwE bijection_xs_ys container_bij_inverse_ex g_def length_eq
    by metis
  then have unique_list_ys: "\<And>n1 n2. n1 \<in> {..<length ys} \<Longrightarrow> n2 \<in> {..<length ys} \<Longrightarrow> ys ! n1 \<equiv>[Imod] ys ! n2 \<Longrightarrow> n1 = n2"
    using g_def length_eq
    by metis
  then have unique_ys: "\<And>x1 x2. x1 \<in> set ys \<Longrightarrow> x2 \<in> set ys \<Longrightarrow> x1 \<equiv>[Imod] x2 \<Longrightarrow> x1 = x2"
    using in_set_conv_nth lessThan_iff
    by metis
  have "\<And>n1 n2. n1 \<in> {..<length ys} \<Longrightarrow> n2 \<in> {..<length ys} \<Longrightarrow> n1 \<noteq> n2 \<Longrightarrow> ys ! f n1 \<noteq> ys ! f n2"
    using bijection_xs_ys distinct_xs length_eq lessThan_iff nth_eq_iff_index_eq nth_mem unique_xs value_equiv_sym value_equiv_transitive
    by metis
  then have "\<And>n1 n2. n1 \<in> {..<length ys} \<Longrightarrow> n2 \<in> {..<length ys} \<Longrightarrow> n1 \<noteq> n2 \<Longrightarrow> ys ! g (f n1) \<noteq> ys ! g (f n2)"
    using bij_betwE bijection_xs_ys container_bij_inverse_ex g_def length_eq
    by metis
  then have "\<And>n1 n2. n1 \<in> {..<length ys} \<Longrightarrow> n2 \<in> {..<length ys} \<Longrightarrow> n1 \<noteq> n2 \<Longrightarrow> ys ! n1 \<noteq> ys ! n2"
    by (simp add: g_def length_eq)
  then have "distinct ys"
    by (simp add: distinct_conv_nth)
  then show "distinct_values Imod ys"
    using distinct_values_impl_distinct_rev unique_ys
    by blast
qed

lemma distinct_values_preserved_alt: "\<And>xs ys. set xs \<subseteq> Value Imod \<Longrightarrow> distinct_values Imod xs \<Longrightarrow> length xs = length ys \<Longrightarrow> \<forall>n. n \<in> {..<length xs} \<longrightarrow> xs ! n \<equiv>[Imod] ys ! n \<Longrightarrow> distinct_values Imod ys"
proof-
  fix xs ys
  assume xs_in_value: "set xs \<subseteq> Value Imod"
  assume distinct_values_xs: "distinct_values Imod xs"
  assume equiv_list: "\<forall>n. n \<in> {..<length xs} \<longrightarrow> xs ! n \<equiv>[Imod] ys ! n"
  then have id_mapping_correct: "\<forall>n. n \<in> {..<length xs} \<longrightarrow> xs ! n \<equiv>[Imod] ys ! (id n)"
    by simp
  assume length_eq: "length xs = length ys"
  then have bij_id: "bij_betw id {..<length xs} {..<length ys}"
    by simp
  show "distinct_values Imod ys"
    using distinct_values_preserved distinct_values_xs id_mapping_correct length_eq local.bij_id xs_in_value
    by blast
qed

lemma valid_values_subtype: 
  assumes inh_wellformed_classes: "\<And>c. c \<in> Inh (Tm Imod) \<Longrightarrow> fst c \<in> Class (Tm Imod) \<and> snd c \<in> Class (Tm Imod)"
  shows "x :[Imod] y \<Longrightarrow> y \<sqsubseteq>[Tm Imod] z \<Longrightarrow> x :[Imod] z"
proof-
  fix x y z
  assume y_extends_z: "y \<sqsubseteq>[Tm Imod] z"
  assume "x :[Imod] y"
  then show "x :[Imod] z"
    using y_extends_z
    unfolding Valid_def
  proof (induct)
    case (valid_rule_booleans v)
    then have "z = boolean"
      using subtype_datatypes_no_supertypes
      unfolding DataType_def
      by blast
    then show ?case
      using valid_rule_booleans.hyps Valid_rel.valid_rule_booleans
      by simp
  next
    case (valid_rule_integers v)
    then have "z = integer"
      using subtype_datatypes_no_supertypes
      unfolding DataType_def
      by blast
    then show ?case
      using valid_rule_integers.hyps Valid_rel.valid_rule_integers
      by simp
  next
    case (valid_rule_reals v)
    then have "z = TypeDef.real"
      using subtype_datatypes_no_supertypes
      unfolding DataType_def
      by blast
    then show ?case
      using valid_rule_reals.hyps Valid_rel.valid_rule_reals
      by simp
  next
    case (valid_rule_strings v)
    then have "z = TypeDef.string"
      using subtype_datatypes_no_supertypes
      unfolding DataType_def
      by blast
    then show ?case
      using valid_rule_strings.hyps Valid_rel.valid_rule_strings
      by simp
  next
    case (valid_rule_proper_classes v t)
    then have "\<exclamdown>(ObjectClass Imod v) \<sqsubseteq>[Tm Imod] z"
      using inh_wellformed_classes subtype_rel_alt subtype_rel_alt_transitive
      unfolding subtype_def trans_def
      by blast
    then show ?case
      using FieldI2 Valid_rel.valid_rule_proper_classes inh_wellformed_classes non_container_type_not_member 
      using subtype_containertypes_no_subtypes subtype_def subtype_relation_datatypes_no_subtypes 
      using subtype_relation_enums_no_subtypes subtype_relation_field subtype_snd_no_class_equal type_not_member 
      using userdatatype_type_contains_no_nullable_classes userdatatype_type_contains_no_proper_classes 
      using valid_rule_proper_classes.prems valid_rule_proper_classes.hyps
      by metis
  next
    case (valid_rule_nullable_classes t)
    then have "z \<in> NullableClassType (Tm Imod)"
      by (simp add: inh_wellformed_classes subtype_def)
    then show ?case
      by (fact Valid_rel.valid_rule_nullable_classes)
  next
    case (valid_rule_enumvalues t v)
    then have "z = enumtype t"
      using subtype_enums_no_supertypes
      by blast
    then show ?case
      using valid_rule_enumvalues.hyps Valid_rel.valid_rule_enumvalues
      by simp
  next
    case (valid_rule_userdata_values v t)
    then have "z = t"
      using subtype_userdatatypes_no_supertypes
      by blast
    then show ?case
      using valid_rule_userdata_values.hyps Valid_rel.valid_rule_userdata_values
      by simp
  next
    case (valid_rule_bags t vs)
    then have "z = t"
      using bag_types_are_container_types subtype_containertypes_no_supertypes
      by blast
    then show ?case
      using valid_rule_bags.hyps Valid_rel.valid_rule_bags
      by blast
  next
    case (valid_rule_sets t vs)
    then have "z = t"
      using set_types_are_container_types subtype_containertypes_no_supertypes
      by blast
    then show ?case
      using valid_rule_sets.hyps Valid_rel.valid_rule_sets
      by blast
  next
    case (valid_rule_seqs t vs)
    then have "z = t"
      using seq_types_are_container_types subtype_containertypes_no_supertypes
      by blast
    then show ?case
      using valid_rule_seqs.hyps Valid_rel.valid_rule_seqs
      by blast
  next
    case (valid_rule_ords t vs)
    then have "z = t"
      using ord_types_are_container_types subtype_containertypes_no_supertypes
      by blast
    then show ?case
      using valid_rule_ords.hyps Valid_rel.valid_rule_ords
      by blast
  qed
qed

lemma valid_values_equiv:
  shows "x \<equiv>[Imod] y \<Longrightarrow> x :[Imod] z \<Longrightarrow> y :[Imod] z"
proof-
  fix x y z
  assume x_valid_z: "x :[Imod] z"
  then show "\<And>y. x \<equiv>[Imod] y \<Longrightarrow> y :[Imod] z"
    unfolding Valid_def
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using Valid_rel.valid_rule_booleans value_equiv_booleans
      by blast
  next
    case (valid_rule_integers v)
    then show ?case
      using Valid_rel.valid_rule_integers value_equiv_integers
      by blast
  next
    case (valid_rule_reals v)
    then show ?case
      using Valid_rel.valid_rule_reals value_equiv_reals
      by blast
  next
    case (valid_rule_strings v)
    then show ?case
      using Valid_rel.valid_rule_strings value_equiv_strings
      by blast
  next
    case (valid_rule_proper_classes v t)
    have "y = obj v"
      using valid_rule_proper_classes.prems
    proof (cases)
      case rule_atom_equiv
      then show ?thesis
        by blast
    qed
    then show ?case
      by (simp add: Valid_rel.valid_rule_proper_classes valid_rule_proper_classes.hyps)
  next
    case (valid_rule_nullable_classes t)
    have "y = nil"
      using valid_rule_nullable_classes.prems
    proof (cases)
      case rule_atom_equiv
      then show ?thesis
        by blast
    qed
    then show ?case
      by (simp add: Valid_rel.valid_rule_nullable_classes valid_rule_nullable_classes.hyps)
  next
    case (valid_rule_enumvalues t v)
    have "y = enum (t, v)"
      using valid_rule_enumvalues.prems
    proof (cases)
      case rule_atom_equiv
      then show ?thesis
        by blast
    qed
    then show ?case
      by (simp add: Valid_rel.valid_rule_enumvalues valid_rule_enumvalues.hyps)
  next
    case (valid_rule_userdata_values v t)
    then show ?case
      using Valid_rel.valid_rule_userdata_values value_equiv_userdatavalues
      by blast
  next
    case (valid_rule_bags t vs)
    then have "vs \<in> ContainerValue Imod"
      using bag_container_values_are_container_values
      by blast
    then have y_in_container_value: "y \<in> ContainerValue Imod"
      using valid_rule_bags.prems value_equiv_container_value_preserved
      by blast
    show ?case
      using valid_rule_bags.prems
    proof (cases)
      case rule_atom_equiv
      then show ?thesis
        using Valid_rel.valid_rule_bags valid_rule_bags.hyps
        by blast
    next
      case (rule_bagof_equiv l1 l2)
      then have "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> (contained_type t, l2 ! f n) \<in> Valid_rel Imod)"
        using contained_list.simps(1) lessThan_iff nth_mem valid_rule_bags.hyps(4)
        by metis
      then have all_valid_rel: "\<forall>n. n \<in> {..<length l1} \<longrightarrow> (contained_type t, l2 ! n) \<in> Valid_rel Imod"
        using bij_betwE bij_betw_the_inv_into f_the_inv_into_f_bij_betw local.rule_bagof_equiv(3)
        by metis
      show ?thesis
      proof (rule Valid_rel.valid_rule_bags)
        show "t \<in> BagContainerType (Tm Imod)"
          by (fact valid_rule_bags.hyps(1))
      next
        show "y \<in> BagContainerValue Imod"
          using BagContainerValue.rule_bagof_atom_values BagContainerValue.rule_bagof_container_values container_value_members_alt y_in_container_value rule_bagof_equiv(2)
          by fastforce
      next
        fix x
        assume "x \<in> set (contained_list y)"
        then show "(contained_type t, x) \<in> Valid_rel Imod"
          using all_valid_rel contained_list.simps(1) in_set_conv_nth lessThan_iff local.rule_bagof_equiv(2) local.rule_bagof_equiv(3)
          by metis
      qed
    next
      case (rule_setof_equiv l1 l2)
      then show ?thesis
        using bag_container_values_are_not_sets valid_rule_bags.hyps(2)
        by blast
    next
      case (rule_seqof_equiv l1 l2)
      then show ?thesis
        using bag_container_values_are_not_seqs valid_rule_bags.hyps(2)
        by blast
    next
      case (rule_ordof_equiv l1 l2)
      then show ?thesis
        using bag_container_values_are_not_ords valid_rule_bags.hyps(2)
        by blast
    qed
  next
    case (valid_rule_sets t vs)
    then have vs_in_container_value: "vs \<in> ContainerValue Imod"
      using set_container_values_are_container_values
      by blast
    then have y_in_container_value: "y \<in> ContainerValue Imod"
      using valid_rule_sets.prems value_equiv_container_value_preserved
      by blast
    show ?case
      using valid_rule_sets.prems
    proof (cases)
      case rule_atom_equiv
      then show ?thesis
        using Valid_rel.valid_rule_sets valid_rule_sets.hyps
        by blast
    next
      case (rule_bagof_equiv l1 l2)
      then show ?thesis
        using set_container_values_are_not_bags valid_rule_sets.hyps(2)
        by blast
    next
      case (rule_setof_equiv l1 l2)
      then have "\<exists>f. bij_betw f {..<length l1} {..<length l2} \<and> (\<forall>n. n \<in> {..<length l1} \<longrightarrow> (contained_type t, l2 ! f n) \<in> Valid_rel Imod)"
        using contained_list.simps(2) lessThan_iff nth_mem valid_rule_sets.hyps(5)
        by metis
      then have all_valid_rel: "\<forall>n. n \<in> {..<length l1} \<longrightarrow> (contained_type t, l2 ! n) \<in> Valid_rel Imod"
        using bij_betwE bij_betw_the_inv_into f_the_inv_into_f_bij_betw local.rule_setof_equiv(3)
        by metis
      show ?thesis
      proof (rule Valid_rel.valid_rule_sets)
        show "t \<in> SetContainerType (Tm Imod)"
          by (fact valid_rule_sets.hyps(1))
      next
        show "y \<in> SetContainerValue Imod"
          using SetContainerValue.rule_setof_atom_values SetContainerValue.rule_setof_container_values container_value_members_alt y_in_container_value rule_setof_equiv(2)
          by fastforce
      next
        have set_l1_subset_value: "set l1 \<subseteq> Value Imod"
          using Value_def vs_in_container_value container_value_members_alt local.rule_setof_equiv(1)
          by fastforce
        have "distinct_values Imod l1"
          using local.rule_setof_equiv(1) valid_rule_sets.hyps(3)
          by simp
        then have "distinct_values Imod l2"
          using set_l1_subset_value local.rule_setof_equiv(3) local.rule_setof_equiv(4) distinct_values_preserved
          by blast
        then show "distinct_values Imod (contained_list y)"
          by (simp add: local.rule_setof_equiv(2))
      next
        fix x
        assume "x \<in> set (contained_list y)"
        then show "(contained_type t, x) \<in> Valid_rel Imod"
          using all_valid_rel contained_list.simps(2) in_set_conv_nth lessThan_iff local.rule_setof_equiv(2) local.rule_setof_equiv(3)
          by metis
      qed
    next
      case (rule_seqof_equiv l1 l2)
      then show ?thesis
        using set_container_values_are_not_seqs valid_rule_sets.hyps(2)
        by blast
    next
      case (rule_ordof_equiv l1 l2)
      then show ?thesis
        using set_container_values_are_not_ords valid_rule_sets.hyps(2)
        by blast
    qed
  next
    case (valid_rule_seqs t vs)
    then have "vs \<in> ContainerValue Imod"
      using seq_container_values_are_container_values
      by blast
    then have y_in_container_value: "y \<in> ContainerValue Imod"
      using valid_rule_seqs.prems value_equiv_container_value_preserved
      by blast
    show ?case
      using valid_rule_seqs.prems
    proof (cases)
      case rule_atom_equiv
      then show ?thesis
        using Valid_rel.valid_rule_seqs valid_rule_seqs.hyps
        by blast
    next
      case (rule_bagof_equiv l1 l2)
      then show ?thesis
        using seq_container_values_are_not_bags valid_rule_seqs.hyps(2)
        by blast
    next
      case (rule_setof_equiv l1 l2)
      then show ?thesis
        using seq_container_values_are_not_sets valid_rule_seqs.hyps(2)
        by blast
    next
      case (rule_seqof_equiv l1 l2)
      then have all_valid_rel: "\<forall>n. n \<in> {..<length l1} \<longrightarrow> (contained_type t, l2 ! n) \<in> Valid_rel Imod"
        using contained_list.simps(3) lessThan_iff nth_mem valid_rule_seqs.hyps(4)
        by metis
      show ?thesis
      proof (rule Valid_rel.valid_rule_seqs)
        show "t \<in> SeqContainerType (Tm Imod)"
          by (fact valid_rule_seqs.hyps(1))
      next
        show "y \<in> SeqContainerValue Imod"
          using SeqContainerValue.rule_seqof_atom_values SeqContainerValue.rule_seqof_container_values container_value_members_alt y_in_container_value rule_seqof_equiv(2)
          by fastforce
      next
        fix x
        assume "x \<in> set (contained_list y)"
        then show "(contained_type t, x) \<in> Valid_rel Imod"
          using all_valid_rel contained_list.simps(3) in_set_conv_nth lessThan_iff local.rule_seqof_equiv(2) local.rule_seqof_equiv(3)
          by metis
      qed
    next
      case (rule_ordof_equiv l1 l2)
      then show ?thesis
        using seq_container_values_are_not_ords valid_rule_seqs.hyps(2)
        by blast
    qed
  next
    case (valid_rule_ords t vs)
    then have vs_in_container_value: "vs \<in> ContainerValue Imod"
      using ord_container_values_are_container_values
      by blast
    then have y_in_container_value: "y \<in> ContainerValue Imod"
      using valid_rule_ords.prems value_equiv_container_value_preserved
      by blast
    show ?case
      using valid_rule_ords.prems
    proof (cases)
      case rule_atom_equiv
      then show ?thesis
        using Valid_rel.valid_rule_ords valid_rule_ords.hyps
        by blast
    next
      case (rule_bagof_equiv l1 l2)
      then show ?thesis
        using ord_container_values_are_not_bags valid_rule_ords.hyps(2)
        by blast
    next
      case (rule_setof_equiv l1 l2)
      then show ?thesis
        using ord_container_values_are_not_sets valid_rule_ords.hyps(2)
        by blast
    next
      case (rule_seqof_equiv l1 l2)
      then show ?thesis
        using ord_container_values_are_not_seqs valid_rule_ords.hyps(2)
        by blast
    next
      case (rule_ordof_equiv l1 l2)
      then have all_valid_rel: "\<forall>n. n \<in> {..<length l1} \<longrightarrow> (contained_type t, l2 ! n) \<in> Valid_rel Imod"
        using contained_list.simps(4) lessThan_iff nth_mem valid_rule_ords.hyps(5)
        by metis
      show ?thesis
      proof (rule Valid_rel.valid_rule_ords)
        show "t \<in> OrdContainerType (Tm Imod)"
          by (fact valid_rule_ords.hyps(1))
      next
        show "y \<in> OrdContainerValue Imod"
          using OrdContainerValue.rule_ordof_atom_values OrdContainerValue.rule_ordof_container_values container_value_members_alt y_in_container_value rule_ordof_equiv(2)
          by fastforce
      next
        have set_l1_subset_value: "set l1 \<subseteq> Value Imod"
          using Value_def vs_in_container_value container_value_members_alt local.rule_ordof_equiv(1)
          by fastforce
        have "distinct_values Imod l1"
          using local.rule_ordof_equiv(1) valid_rule_ords.hyps(3)
          by simp
        then have "distinct_values Imod l2"
          using set_l1_subset_value local.rule_ordof_equiv(3) local.rule_ordof_equiv(4) distinct_values_preserved_alt
          by blast 
        then show "distinct_values Imod (contained_list y)"
          by (simp add: local.rule_ordof_equiv(2))
      next
        fix x
        assume "x \<in> set (contained_list y)"
        then show "(contained_type t, x) \<in> Valid_rel Imod"
          using all_valid_rel contained_list.simps(4) in_set_conv_nth lessThan_iff local.rule_ordof_equiv(2) local.rule_ordof_equiv(3)
          by metis
      qed
    qed
  qed
qed

lemma valid_values_boolean_unique[simp]: "x \<in> BooleanValue \<Longrightarrow> x :[Imod] y \<Longrightarrow> y = TypeDef.boolean"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> BooleanValue"
  assume "(y, x) \<in> Valid_rel Imod" then show "y = TypeDef.boolean"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      by simp
  next
    case (valid_rule_integers v)
    then show ?case 
      using integer_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_reals v)
    then show ?case
      using real_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_strings v)
    then show ?case
      using string_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values t v)
    then show ?case
      using userdata_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_bags t vs)
    then show ?case
      using bag_container_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      using set_container_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      using seq_container_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      using ord_container_values_boolean_values_intersect
      by blast
  qed
qed

lemma valid_values_boolean_unique_alt[simp]: "bool x :[Imod] y \<Longrightarrow> y = TypeDef.boolean"
  using BooleanValue.simps valid_values_boolean_unique by auto

lemma valid_values_boolean[simp]: "bool x :[Imod] TypeDef.boolean"
  by (simp add: BooleanValue.simps Valid_def Valid_rel.valid_rule_booleans)

lemma valid_type_boolean_values_unique[simp]: "x :[Imod] TypeDef.boolean \<Longrightarrow> x \<in> BooleanValue"
  unfolding Valid_def
proof-
  fix x
  assume "(TypeDef.boolean, x) \<in> Valid_rel Imod" then show "x \<in> BooleanValue"
  proof
    fix v
    assume x_is_v: "x = v"
    assume "v \<in> BooleanValue" then show ?thesis using x_is_v
      by simp
  next
    assume "TypeDef.boolean = TypeDef.integer"
    then show ?thesis
      by simp
  next
    assume "TypeDef.boolean = TypeDef.real"
    then show ?thesis
      by simp
  next
    assume "TypeDef.boolean = TypeDef.string"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume "TypeDef.boolean = t" then show ?thesis 
      using t_is_classtype by simp
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume "TypeDef.boolean = t" then show ?thesis 
      using t_is_nullable_classtype by simp
  next
    fix t :: "'nt Id"
    assume "TypeDef.boolean = enumtype t"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume "TypeDef.boolean = t" then show ?thesis 
      using t_is_userdatatype_type by simp
  next
    fix t
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume "TypeDef.boolean = t" then show ?thesis 
      using t_is_bag_container_type bag_types_typedef by blast
  next
    fix t
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume "TypeDef.boolean = t" then show ?thesis 
      using t_is_set_container_type set_types_typedef by blast
  next
    fix t
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume "TypeDef.boolean = t" then show ?thesis 
      using t_is_seq_container_type seq_types_typedef by blast
  next
    fix t
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume "TypeDef.boolean = t" then show ?thesis 
      using t_is_ord_container_type ord_types_typedef by blast
  qed
qed

lemma valid_type_boolean_values_unique_alt[simp]: "x :[Imod] TypeDef.boolean \<Longrightarrow> \<exists>y. x = bool y"
  by simp

lemma valid_values_integer_unique[simp]: "x \<in> IntegerValue \<Longrightarrow> x :[Imod] y \<Longrightarrow> y = TypeDef.integer"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> IntegerValue"
  assume "(y, x) \<in> Valid_rel Imod" then show "y = TypeDef.integer"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using integer_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_integers v)
    then show ?case 
      by simp
  next
    case (valid_rule_reals v)
    then show ?case
      using real_values_integer_values_intersect
      by blast
  next
    case (valid_rule_strings v)
    then show ?case
      using string_values_integer_values_intersect
      by blast
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values t v)
    then show ?case
      using userdata_values_integer_values_intersect
      by blast
  next
    case (valid_rule_bags t vs)
    then show ?case
      using bag_container_values_integer_values_intersect
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      using set_container_values_integer_values_intersect
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      using seq_container_values_integer_values_intersect
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      using ord_container_values_integer_values_intersect
      by blast
  qed
qed

lemma valid_values_integer_unique_alt[simp]: "int x :[Imod] y \<Longrightarrow> y = TypeDef.integer"
  using IntegerValue.rule_integer valid_values_integer_unique by blast

lemma valid_values_integer[simp]: "int x :[Imod] TypeDef.integer"
  by (simp add: IntegerValue.rule_integer Valid_def Valid_rel.intros)

lemma valid_type_integer_values_unique[simp]: "x :[Imod] TypeDef.integer \<Longrightarrow> x \<in> IntegerValue"
  unfolding Valid_def
proof-
  fix x
  assume "(TypeDef.integer, x) \<in> Valid_rel Imod" then show "x \<in> IntegerValue"
  proof
    assume "TypeDef.integer = TypeDef.boolean"
    then show ?thesis
      by simp
  next
    fix v
    assume x_is_v: "x = v"
    assume "v \<in> IntegerValue" then show ?thesis using x_is_v
      by simp
  next
    assume "TypeDef.integer = TypeDef.real"
    then show ?thesis
      by simp
  next
    assume "TypeDef.integer = TypeDef.string"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume "TypeDef.integer = t" then show ?thesis 
      using t_is_classtype by simp
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume "TypeDef.integer = t" then show ?thesis 
      using t_is_nullable_classtype by simp
  next
    fix t :: "'nt Id"
    assume "TypeDef.integer = enumtype t"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume "TypeDef.integer = t" then show ?thesis 
      using t_is_userdatatype_type by simp
  next
    fix t
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume "TypeDef.integer = t" then show ?thesis 
      using t_is_bag_container_type bag_types_typedef by blast
  next
    fix t
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume "TypeDef.integer = t" then show ?thesis 
      using t_is_set_container_type set_types_typedef by blast
  next
    fix t
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume "TypeDef.integer = t" then show ?thesis 
      using t_is_seq_container_type seq_types_typedef by blast
  next
    fix t
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume "TypeDef.integer = t" then show ?thesis 
      using t_is_ord_container_type ord_types_typedef by blast
  qed
qed

lemma valid_type_integer_values_unique_alt[simp]: "x :[Imod] TypeDef.integer \<Longrightarrow> \<exists>y. x = int y"
  by simp

lemma valid_values_real_unique[simp]: "x \<in> RealValue \<Longrightarrow> x :[Imod] y \<Longrightarrow> y = TypeDef.real"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> RealValue"
  assume "(y, x) \<in> Valid_rel Imod" then show "y = TypeDef.real"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using real_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_integers v)
    then show ?case 
      using real_values_integer_values_intersect
      by blast
  next
    case (valid_rule_reals v)
    then show ?case
      by simp
  next
    case (valid_rule_strings v)
    then show ?case
      using string_values_real_values_intersect
      by blast
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values t v)
    then show ?case
      using userdata_values_real_values_intersect
      by blast
  next
    case (valid_rule_bags t vs)
    then show ?case
      using bag_container_values_real_values_intersect
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      using set_container_values_real_values_intersect
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      using seq_container_values_real_values_intersect
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      using ord_container_values_real_values_intersect
      by blast
  qed
qed

lemma valid_values_real_unique_alt[simp]: "real x :[Imod] y \<Longrightarrow> y = TypeDef.real"
  using RealValue.rule_real valid_values_real_unique by blast

lemma valid_values_real[simp]: "real x :[Imod] TypeDef.real"
  by (simp add: RealValue.rule_real Valid_def Valid_rel.intros)

lemma valid_type_real_values_unique[simp]: "x :[Imod] TypeDef.real \<Longrightarrow> x \<in> RealValue"
  unfolding Valid_def
proof-
  fix x
  assume "(TypeDef.real, x) \<in> Valid_rel Imod" then show "x \<in> RealValue"
  proof
    assume "TypeDef.real = TypeDef.boolean"
    then show ?thesis
      by simp
  next
    assume "TypeDef.real = TypeDef.integer"
    then show ?thesis
      by simp
  next
    fix v
    assume x_is_v: "x = v"
    assume "v \<in> RealValue" then show ?thesis using x_is_v
      by simp
  next
    assume "TypeDef.real = TypeDef.string"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume "TypeDef.real = t" then show ?thesis 
      using t_is_classtype by simp
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume "TypeDef.real = t" then show ?thesis 
      using t_is_nullable_classtype by simp
  next
    fix t :: "'nt Id"
    assume "TypeDef.real = enumtype t"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume "TypeDef.real = t" then show ?thesis 
      using t_is_userdatatype_type by simp
  next
    fix t
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume "TypeDef.real = t" then show ?thesis 
      using t_is_bag_container_type bag_types_typedef by blast
  next
    fix t
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume "TypeDef.real = t" then show ?thesis 
      using t_is_set_container_type set_types_typedef by blast
  next
    fix t
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume "TypeDef.real = t" then show ?thesis 
      using t_is_seq_container_type seq_types_typedef by blast
  next
    fix t
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume "TypeDef.real = t" then show ?thesis 
      using t_is_ord_container_type ord_types_typedef by blast
  qed
qed

lemma valid_type_real_values_unique_alt[simp]: "x :[Imod] TypeDef.real \<Longrightarrow> \<exists>y. x = real y"
  by simp

lemma valid_values_string_unique[simp]: "x \<in> StringValue \<Longrightarrow> x :[Imod] y \<Longrightarrow> y = TypeDef.string"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> StringValue"
  assume "(y, x) \<in> Valid_rel Imod" then show "y = TypeDef.string"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using string_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_integers v)
    then show ?case 
      using string_values_integer_values_intersect
      by blast
  next
    case (valid_rule_reals v)
    then show ?case
      using string_values_real_values_intersect
      by blast
  next
    case (valid_rule_strings v)
    then show ?case
      by simp
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values t v)
    then show ?case
      using userdata_values_string_values_intersect
      by blast
  next
    case (valid_rule_bags t vs)
    then show ?case
      using bag_container_values_string_values_intersect
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      using set_container_values_string_values_intersect
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      using seq_container_values_string_values_intersect
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      using ord_container_values_string_values_intersect
      by blast
  qed
qed

lemma valid_values_string_unique_alt[simp]: "string x :[Imod] y \<Longrightarrow> y = TypeDef.string"
  using StringValue.rule_string valid_values_string_unique by blast

lemma valid_values_string[simp]: "string x :[Imod] TypeDef.string"
  by (simp add: StringValue.rule_string Valid_def Valid_rel.intros)

lemma valid_type_string_values_unique[simp]: "x :[Imod] TypeDef.string \<Longrightarrow> x \<in> StringValue"
  unfolding Valid_def
proof-
  fix x
  assume "(TypeDef.string, x) \<in> Valid_rel Imod" then show "x \<in> StringValue"
  proof
    assume "TypeDef.string = TypeDef.boolean"
    then show ?thesis
      by simp
  next
    assume "TypeDef.string = TypeDef.integer"
    then show ?thesis
      by simp
  next
    assume "TypeDef.string = TypeDef.real"
    then show ?thesis
      by simp
  next
    fix v
    assume x_is_v: "x = v"
    assume "v \<in> StringValue" then show ?thesis using x_is_v
      by simp
  next
    fix t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume "TypeDef.string = t" then show ?thesis 
      using t_is_classtype by simp
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume "TypeDef.string = t" then show ?thesis 
      using t_is_nullable_classtype by simp
  next
    fix t :: "'nt Id"
    assume "TypeDef.string = enumtype t"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume "TypeDef.string = t" then show ?thesis 
      using t_is_userdatatype_type by simp
  next
    fix t
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume "TypeDef.string = t" then show ?thesis 
      using t_is_bag_container_type bag_types_typedef by blast
  next
    fix t
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume "TypeDef.string = t" then show ?thesis 
      using t_is_set_container_type set_types_typedef by blast
  next
    fix t
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume "TypeDef.string = t" then show ?thesis 
      using t_is_seq_container_type seq_types_typedef by blast
  next
    fix t
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume "TypeDef.string = t" then show ?thesis 
      using t_is_ord_container_type ord_types_typedef by blast
  qed
qed

lemma valid_type_string_values_unique_alt[simp]: "x :[Imod] TypeDef.string \<Longrightarrow> \<exists>y. x = string y"
  by simp

lemma valid_values_proper_classes_unique[simp]: "x \<in> ProperClassValue Imod \<Longrightarrow> x :[Imod] y \<Longrightarrow> y \<in> ClassType (Tm Imod)"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> ProperClassValue Imod"
  assume "(y, x) \<in> Valid_rel Imod" then show "y \<in> ClassType (Tm Imod)"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using proper_class_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_integers v)
    then show ?case 
      using proper_class_values_integer_values_intersect
      by blast
  next
    case (valid_rule_reals v)
    then show ?case
      using proper_class_values_real_values_intersect
      by blast
  next
    case (valid_rule_strings v)
    then show ?case
      using proper_class_values_string_values_intersect
      by blast
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values t v)
    then show ?case
      using userdata_values_proper_class_values_intersect
      by blast
  next
    case (valid_rule_bags t vs)
    then show ?case
      using bag_container_values_proper_class_values_intersect
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      using set_container_values_proper_class_values_intersect
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      using seq_container_values_proper_class_values_intersect
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      using ord_container_values_proper_class_values_intersect
      by blast
  qed
qed

lemma valid_values_proper_classes_unique_alt[simp]: "x \<in> Object Imod \<Longrightarrow> obj x :[Imod] y \<Longrightarrow> y \<in> ClassType (Tm Imod)"
  using ProperClassValue.rule_proper_objects valid_values_proper_classes_unique
  by metis

lemma valid_type_proper_classes_values_unique[simp]: "\<And>y. x :[Imod] \<exclamdown>y \<Longrightarrow> x \<in> ProperClassValue Imod"
  unfolding Valid_def
proof-
  fix x y
  assume "(\<exclamdown>y, x) \<in> Valid_rel Imod" then show "x \<in> ProperClassValue Imod"
  proof
    assume "\<exclamdown>y = TypeDef.boolean"
    then show ?thesis
      by simp
  next
    assume "\<exclamdown>y = TypeDef.integer"
    then show ?thesis
      by simp
  next
    assume "\<exclamdown>y = TypeDef.real"
    then show ?thesis
      by simp
  next
    assume "\<exclamdown>y = TypeDef.string"
    then show ?thesis
      by simp
  next
    fix v t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume x_proper_object: "x = obj v"
    assume v_is_object: "v \<in> Object Imod"
    assume "\<exclamdown>y = t" then show ?thesis 
      using t_is_classtype x_proper_object v_is_object
      by (simp add: ProperClassValue.rule_proper_objects)
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume "\<exclamdown>y = t" then show ?thesis 
      using t_is_nullable_classtype by auto
  next
    fix t
    assume "\<exclamdown>y = enumtype t"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume "\<exclamdown>y = t" then show ?thesis 
      using t_is_userdatatype_type by auto
  next
    fix t
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume "\<exclamdown>y = t" then show ?thesis 
      using t_is_bag_container_type bag_types_typedef by blast
  next
    fix t
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume "\<exclamdown>y = t" then show ?thesis 
      using t_is_set_container_type set_types_typedef by blast
  next
    fix t
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume "\<exclamdown>y = t" then show ?thesis 
      using t_is_seq_container_type seq_types_typedef by blast
  next
    fix t
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume "\<exclamdown>y = t" then show ?thesis 
      using t_is_ord_container_type ord_types_typedef by blast
  qed
qed

lemma valid_type_proper_classes_values_unique_alt[simp]: "\<And>y. x :[Imod] \<exclamdown>y \<Longrightarrow> \<exists>z. x = obj z"
  using proper_class_values_are_proper_objects valid_type_proper_classes_values_unique by blast

lemma valid_values_nil_unique[simp]: "x = nil \<Longrightarrow> x :[Imod] y \<Longrightarrow> y \<in> NullableClassType (Tm Imod)"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x = nil"
  assume "(y, x) \<in> Valid_rel Imod" then show "y \<in> NullableClassType (Tm Imod)"
    using x_in_set
    by (induct) simp_all
qed

lemma valid_values_nil_unique_alt[simp]: "nil :[Imod] y \<Longrightarrow> y \<in> NullableClassType (Tm Imod)"
  by simp

lemma valid_type_nullable_classes_values_unique[simp]: "\<And>y. x :[Imod] \<questiondown>y \<Longrightarrow> x \<in> ClassValue Imod"
  unfolding Valid_def
proof-
  fix x y
  assume "(\<questiondown>y, x) \<in> Valid_rel Imod" then show "x \<in> ClassValue Imod"
  proof
    assume "\<questiondown>y = TypeDef.boolean"
    then show ?thesis
      by simp
  next
    assume "\<questiondown>y = TypeDef.integer"
    then show ?thesis
      by simp
  next
    assume "\<questiondown>y = TypeDef.real"
    then show ?thesis
      by simp
  next
    assume "\<questiondown>y = TypeDef.string"
    then show ?thesis
      by simp
  next
    fix v t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume x_proper_object: "x = obj v"
    assume v_is_object: "v \<in> Object Imod"
    assume "\<questiondown>y = t" then show ?thesis 
      unfolding ClassValue_def
      using t_is_classtype x_proper_object v_is_object
      by (simp add: ProperClassValue.rule_proper_objects)
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume x_is_nil: "x = nil"
    assume "\<questiondown>y = t" then show ?thesis 
      unfolding ClassValue_def
      using t_is_nullable_classtype x_is_nil
      by simp
  next
    fix t
    assume "\<questiondown>y = enumtype t"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume "\<questiondown>y = t" then show ?thesis 
      using t_is_userdatatype_type by auto
  next
    fix t
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume "\<questiondown>y = t" then show ?thesis 
      using t_is_bag_container_type bag_types_typedef by blast
  next
    fix t
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume "\<questiondown>y = t" then show ?thesis 
      using t_is_set_container_type set_types_typedef by blast
  next
    fix t
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume "\<questiondown>y = t" then show ?thesis 
      using t_is_seq_container_type seq_types_typedef by blast
  next
    fix t
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume "\<questiondown>y = t" then show ?thesis 
      using t_is_ord_container_type ord_types_typedef by blast
  qed
qed

lemma valid_type_nullable_classes_values_unique_alt[simp]: "\<And>y. x :[Imod] \<exclamdown>y \<Longrightarrow> \<exists>z. x = obj z \<or> x = nil"
  using proper_class_values_are_proper_objects valid_type_proper_classes_values_unique by blast

lemma valid_values_enumvalues_unique[simp]: "enum (x, y) \<in> EnumValueValue (Tm Imod) \<Longrightarrow> enum (x, y) :[Imod] z \<Longrightarrow> z = TypeDef.enumtype x"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "'nt Id"
  fix y :: "'nt"
  fix z :: "('nt) TypeDef"
  define w :: "('o, 'nt) ValueDef" where "w \<equiv> enum (x, y)"
  assume x_in_set: "enum (x, y) \<in> EnumValueValue (Tm Imod)"
  assume valid_rel: "(z, enum (x, y)) \<in> Valid_rel Imod" 
  have "w \<in> EnumValueValue (Tm Imod) \<Longrightarrow> (z, w) \<in> Valid_rel Imod \<Longrightarrow> z = TypeDef.enumtype x"
  proof-
    assume w_in_set: "w \<in> EnumValueValue (Tm Imod)"
    assume "(z, w) \<in> Valid_rel Imod" then show "z = TypeDef.enumtype x"
      using w_def w_in_set
      by (induct) auto
  qed
  then show "z = TypeDef.enumtype x"
    using w_def valid_rel x_in_set EnumValueValue.cases EnumValueValue.rule_enumvalue
    by blast
qed

lemma valid_type_enumvalues_values_unique[simp]: "\<And>y. x :[Imod] enumtype y \<Longrightarrow> x \<in> EnumValueValue (Tm Imod)"
  unfolding Valid_def
proof-
  fix x y
  assume "(enumtype y, x) \<in> Valid_rel Imod" then show "x \<in> EnumValueValue (Tm Imod)"
  proof
    assume "enumtype y = TypeDef.boolean"
    then show ?thesis
      by simp
  next
    assume "enumtype y = TypeDef.integer"
    then show ?thesis
      by simp
  next
    assume "enumtype y = TypeDef.real"
    then show ?thesis
      by simp
  next
    assume "enumtype y = TypeDef.string"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume "enumtype y = t" then show ?thesis 
      using t_is_classtype by auto
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume "enumtype y = t" then show ?thesis 
      using t_is_nullable_classtype by auto
  next
    fix t v
    assume x_is_enum: "x = enum (t, v)"
    assume t_v_from_enumvalue: "(t, v) \<in> EnumValue (Tm Imod)"
    assume "enumtype y = enumtype t"
    then show ?thesis
      using x_is_enum t_v_from_enumvalue
      by (simp add: EnumValueValue.rule_enumvalue)
  next
    fix t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume "enumtype y = t" then show ?thesis 
      using t_is_userdatatype_type by auto
  next
    fix t
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume "enumtype y = t" then show ?thesis 
      using t_is_bag_container_type bag_types_typedef by blast
  next
    fix t
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume "enumtype y = t" then show ?thesis 
      using t_is_set_container_type set_types_typedef by blast
  next
    fix t
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume "enumtype y = t" then show ?thesis 
      using t_is_seq_container_type seq_types_typedef by blast
  next
    fix t
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume "enumtype y = t" then show ?thesis 
      using t_is_ord_container_type ord_types_typedef by blast
  qed
qed

lemma valid_type_enumvalues_values_unique_alt[simp]: "\<And>y. x :[Imod] enumtype y \<Longrightarrow> \<exists>z. x = enum z"
  using enumvalues_values_are_enumvalues valid_type_enumvalues_values_unique by blast

lemma valid_values_userdata_unique[simp]: "x \<in> UserDataValue \<Longrightarrow> x :[Imod] y \<Longrightarrow> \<exists>z. y = userdatatype z"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> UserDataValue"
  assume "(y, x) \<in> Valid_rel Imod" then show "\<exists>z. y = userdatatype z"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using userdata_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_integers v)
    then show ?case 
      using userdata_values_integer_values_intersect
      by blast
  next
    case (valid_rule_reals v)
    then show ?case
      using userdata_values_real_values_intersect
      by blast
  next
    case (valid_rule_strings v)
    then show ?case
      using userdata_values_string_values_intersect
      by blast
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values t v)
    then show ?case
      using userdatatype_type_member by simp
  next
    case (valid_rule_bags t vs)
    then show ?case
      using bag_container_values_userdata_values_intersect
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      using set_container_values_userdata_values_intersect
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      using seq_container_values_userdata_values_intersect
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      using ord_container_values_userdata_values_intersect
      by blast
  qed
qed

lemma valid_values_userdata_unique_alt[simp]: "data x :[Imod] y \<Longrightarrow> \<exists>z. y = userdatatype z"
  using UserDataValue.rule_userdatavalue valid_values_userdata_unique by blast

lemma valid_values_userdata[simp]: "y \<in> UserDataType (Tm Imod) \<Longrightarrow> data x :[Imod] userdatatype y"
  by (simp add: UserDataTypeType.rule_userdatatypes UserDataValue.rule_userdatavalue Valid_def Valid_rel.valid_rule_userdata_values)

lemma valid_type_userdata_values_unique[simp]: "\<And>y. x :[Imod] userdatatype y \<Longrightarrow> x \<in> UserDataValue"
  unfolding Valid_def
proof-
  fix x y
  assume "(userdatatype y, x) \<in> Valid_rel Imod" then show "x \<in> UserDataValue"
  proof
    assume "userdatatype y = TypeDef.boolean"
    then show ?thesis
      by simp
  next
    assume "userdatatype y = TypeDef.integer"
    then show ?thesis
      by simp
  next
    assume "userdatatype y = TypeDef.real"
    then show ?thesis
      by simp
  next
    assume "userdatatype y = TypeDef.string"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume "userdatatype y = t" then show ?thesis 
      using t_is_classtype by auto
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume "userdatatype y = t" then show ?thesis 
      using t_is_nullable_classtype by auto
  next
    fix t
    assume "userdatatype y = enumtype t"
    then show ?thesis
      by simp
  next
    fix v t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume x_is_v: "x = v"
    assume v_is_userdatavalue: "v \<in> UserDataValue"
    assume "userdatatype y = t" then show ?thesis 
      using t_is_userdatatype_type x_is_v v_is_userdatavalue by auto
  next
    fix t
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume "userdatatype y = t" then show ?thesis 
      using t_is_bag_container_type bag_types_typedef by blast
  next
    fix t
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume "userdatatype y = t" then show ?thesis 
      using t_is_set_container_type set_types_typedef by blast
  next
    fix t
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume "userdatatype y = t" then show ?thesis 
      using t_is_seq_container_type seq_types_typedef by blast
  next
    fix t
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume "userdatatype y = t" then show ?thesis 
      using t_is_ord_container_type ord_types_typedef by blast
  qed
qed

lemma valid_type_userdata_values_unique_alt[simp]: "\<And>y. x :[Imod] userdatatype y \<Longrightarrow> \<exists>z. x = data z"
  by simp

lemma valid_values_atom_set[simp]: "x \<in> AtomValue Imod \<Longrightarrow> x :[Imod] y \<Longrightarrow> y \<in> NonContainerType (Tm Imod)"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> AtomValue Imod"
  assume "(y, x) \<in> Valid_rel Imod" then show "y \<in> NonContainerType (Tm Imod)"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      unfolding NonContainerType_def DataType_def
      by simp
  next
    case (valid_rule_integers v)
    then show ?case
      unfolding NonContainerType_def DataType_def
      by simp
  next
    case (valid_rule_reals v)
    then show ?case
      unfolding NonContainerType_def DataType_def
      by simp
  next
    case (valid_rule_strings v)
    then show ?case
      unfolding NonContainerType_def DataType_def
      by simp
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      unfolding NonContainerType_def
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      unfolding NonContainerType_def ClassType_def
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      unfolding NonContainerType_def
      by simp
  next
    case (valid_rule_userdata_values v t)
    then show ?case
      unfolding NonContainerType_def
      by simp
  next
    case (valid_rule_bags t vs)
    then show ?case
      using bag_container_values_atom_values_intersect
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      using set_container_values_atom_values_intersect
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      using seq_container_values_atom_values_intersect
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      using ord_container_values_atom_values_intersect
      by blast
  qed
qed

lemma valid_values_container_set[simp]: "x \<in> ContainerValue Imod \<Longrightarrow> x :[Imod] y \<Longrightarrow> y \<in> ContainerType (Tm Imod)"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> ContainerValue Imod"
  assume "(y, x) \<in> Valid_rel Imod" then show "y \<in> ContainerType (Tm Imod)"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using boolean_values_are_booleans container_values_are_not_booleans
      by blast
  next
    case (valid_rule_integers v)
    then show ?case
      using integer_values_are_integers container_values_are_not_integers
      by blast
  next
    case (valid_rule_reals v)
    then show ?case
      using real_values_are_reals container_values_are_not_reals
      by blast
  next
    case (valid_rule_strings v)
    then show ?case
      using string_values_are_strings container_values_are_not_strings
      by blast
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values v t)
    then show ?case
      using container_values_userdata_values_intersect
      by blast
  next
    case (valid_rule_bags t vs)
    then show ?case
      using bag_types_are_container_types
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      using set_types_are_container_types
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      using seq_types_are_container_types
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      using ord_types_are_container_types
      by blast
  qed
qed

lemma valid_values_container_recursive[simp]: "\<And>z. y \<in> ContainerType (Tm Imod) \<Longrightarrow> x :[Imod] y \<Longrightarrow> z \<in> set (contained_list x) \<Longrightarrow> z :[Imod] contained_type y"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x z :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume y_in_set: "y \<in> ContainerType (Tm Imod)"
  assume z_in_value: "z \<in> set (contained_list x)"
  assume "(y, x) \<in> Valid_rel Imod" then show "(contained_type y, z) \<in> Valid_rel Imod"
    using y_in_set z_in_value
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      by simp
  next
    case (valid_rule_integers v)
    then show ?case
      by simp
  next
    case (valid_rule_reals v)
    then show ?case
      by simp
  next
    case (valid_rule_strings v)
    then show ?case
      by simp
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      using container_type_class_type_intersect
      by blast
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      using container_type_nullable_class_type_intersect
      by blast
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values v t)
    then show ?case
      using container_type_userdatatype_type_intersect
      by blast
  next
    case (valid_rule_bags t vs)
    then show ?case
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      by blast
  qed
qed

lemma valid_values_bag_container_unique[simp]: "x \<in> BagContainerValue Imod \<Longrightarrow> x :[Imod] y \<Longrightarrow> \<exists>z. y = TypeDef.bagof z"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> BagContainerValue Imod"
  assume "(y, x) \<in> Valid_rel Imod" then show "\<exists>z. y = TypeDef.bagof z"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using bag_container_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_integers v)
    then show ?case 
      using bag_container_values_integer_values_intersect
      by blast
  next
    case (valid_rule_reals v)
    then show ?case
      using bag_container_values_real_values_intersect
      by blast
  next
    case (valid_rule_strings v)
    then show ?case
      using bag_container_values_string_values_intersect
      by blast
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values t v)
    then show ?case
      using bag_container_values_userdata_values_intersect
      by blast
  next
    case (valid_rule_bags t vs)
    then show ?case
      by simp
  next
    case (valid_rule_sets t vs)
    then show ?case
      using set_container_values_bag_container_values_intersect
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      using seq_container_values_bag_container_values_intersect
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      using ord_container_values_bag_container_values_intersect
      by blast
  qed
qed

lemma valid_values_bag_container_unique_alt[simp]: "x \<in> ContainerValueList Imod \<Longrightarrow> bagof x :[Imod] y \<Longrightarrow> \<exists>z. y = TypeDef.bagof z"
  using BagContainerValue.rule_bagof_container_values valid_values_bag_container_unique by blast

lemma valid_type_bag_container_values_unique[simp]: "\<And>y. x :[Imod] TypeDef.bagof y \<Longrightarrow> x \<in> BagContainerValue Imod"
  unfolding Valid_def
proof-
  fix x y
  assume "(TypeDef.bagof y, x) \<in> Valid_rel Imod" then show "x \<in> BagContainerValue Imod"
  proof
    assume "TypeDef.bagof y = TypeDef.boolean"
    then show ?thesis
      by simp
  next
    assume "TypeDef.bagof y = TypeDef.integer"
    then show ?thesis
      by simp
  next
    assume "TypeDef.bagof y = TypeDef.real"
    then show ?thesis
      by simp
  next
    assume "TypeDef.bagof y = TypeDef.string"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume "TypeDef.bagof y = t" then show ?thesis 
      using t_is_classtype by auto
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume "TypeDef.bagof y = t" then show ?thesis 
      using t_is_nullable_classtype by auto
  next
    fix t
    assume "TypeDef.bagof y = enumtype t"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume "TypeDef.bagof y = t" then show ?thesis 
      using t_is_userdatatype_type by auto
  next
    fix t vs
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume x_is_vs: "x = vs"
    assume vs_is_container_value: "vs \<in> BagContainerValue Imod"
    assume "TypeDef.bagof y = t" then show ?thesis 
      using t_is_bag_container_type x_is_vs vs_is_container_value by blast
  next
    fix t
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume "TypeDef.bagof y = t" then show ?thesis 
      using t_is_set_container_type set_types_typedef by blast
  next
    fix t
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume "TypeDef.bagof y = t" then show ?thesis 
      using t_is_seq_container_type seq_types_typedef by blast
  next
    fix t
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume "TypeDef.bagof y = t" then show ?thesis 
      using t_is_ord_container_type ord_types_typedef by blast
  qed
qed

lemma valid_type_bag_container_values_unique_alt[simp]: "\<And>y. x :[Imod] TypeDef.bagof y \<Longrightarrow> \<exists>z. x = bagof z"
  using bag_container_values_are_bags valid_type_bag_container_values_unique by blast

lemma valid_values_set_container_unique[simp]: "x \<in> SetContainerValue Imod \<Longrightarrow> x :[Imod] y \<Longrightarrow> \<exists>z. y = TypeDef.setof z"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> SetContainerValue Imod"
  assume "(y, x) \<in> Valid_rel Imod" then show "\<exists>z. y = TypeDef.setof z"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using set_container_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_integers v)
    then show ?case 
      using set_container_values_integer_values_intersect
      by blast
  next
    case (valid_rule_reals v)
    then show ?case
      using set_container_values_real_values_intersect
      by blast
  next
    case (valid_rule_strings v)
    then show ?case
      using set_container_values_string_values_intersect
      by blast
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values t v)
    then show ?case
      using set_container_values_userdata_values_intersect
      by blast
  next
    case (valid_rule_bags t vs)
    then show ?case
      using set_container_values_bag_container_values_intersect
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      by simp
  next
    case (valid_rule_seqs t vs)
    then show ?case
      using seq_container_values_set_container_values_intersect
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      using ord_container_values_set_container_values_intersect
      by blast
  qed
qed

lemma valid_values_set_container_unique_alt[simp]: "x \<in> ContainerValueList Imod \<Longrightarrow> setof x :[Imod] y \<Longrightarrow> \<exists>z. y = TypeDef.setof z"
  using SetContainerValue.rule_setof_container_values valid_values_set_container_unique by blast

lemma valid_type_set_container_values_unique[simp]: "\<And>y. x :[Imod] TypeDef.setof y \<Longrightarrow> x \<in> SetContainerValue Imod"
  unfolding Valid_def
proof-
  fix x y
  assume "(TypeDef.setof y, x) \<in> Valid_rel Imod" then show "x \<in> SetContainerValue Imod"
  proof
    assume "TypeDef.setof y = TypeDef.boolean"
    then show ?thesis
      by simp
  next
    assume "TypeDef.setof y = TypeDef.integer"
    then show ?thesis
      by simp
  next
    assume "TypeDef.setof y = TypeDef.real"
    then show ?thesis
      by simp
  next
    assume "TypeDef.setof y = TypeDef.string"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume "TypeDef.setof y = t" then show ?thesis 
      using t_is_classtype by auto
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume "TypeDef.setof y = t" then show ?thesis 
      using t_is_nullable_classtype by auto
  next
    fix t
    assume "TypeDef.setof y = enumtype t"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume "TypeDef.setof y = t" then show ?thesis 
      using t_is_userdatatype_type by auto
  next
    fix t
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume "TypeDef.setof y = t" then show ?thesis 
      using t_is_bag_container_type bag_types_typedef by blast
  next
    fix t vs
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume x_is_vs: "x = vs"
    assume vs_is_container_value: "vs \<in> SetContainerValue Imod"
    assume "TypeDef.setof y = t" then show ?thesis 
      using t_is_set_container_type x_is_vs vs_is_container_value by blast
  next
    fix t
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume "TypeDef.setof y = t" then show ?thesis 
      using t_is_seq_container_type seq_types_typedef by blast
  next
    fix t
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume "TypeDef.setof y = t" then show ?thesis 
      using t_is_ord_container_type ord_types_typedef by blast
  qed
qed

lemma valid_type_set_container_values_unique_alt[simp]: "\<And>y. x :[Imod] TypeDef.setof y \<Longrightarrow> \<exists>z. x = setof z"
  using set_container_values_are_sets valid_type_set_container_values_unique by blast

lemma valid_values_seq_container_unique[simp]: "x \<in> SeqContainerValue Imod \<Longrightarrow> x :[Imod] y \<Longrightarrow> \<exists>z. y = TypeDef.seqof z"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> SeqContainerValue Imod"
  assume "(y, x) \<in> Valid_rel Imod" then show "\<exists>z. y = TypeDef.seqof z"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using seq_container_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_integers v)
    then show ?case 
      using seq_container_values_integer_values_intersect
      by blast
  next
    case (valid_rule_reals v)
    then show ?case
      using seq_container_values_real_values_intersect
      by blast
  next
    case (valid_rule_strings v)
    then show ?case
      using seq_container_values_string_values_intersect
      by blast
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values t v)
    then show ?case
      using seq_container_values_userdata_values_intersect
      by blast
  next
    case (valid_rule_bags t vs)
    then show ?case
      using seq_container_values_bag_container_values_intersect
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      using seq_container_values_set_container_values_intersect
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      by simp
  next
    case (valid_rule_ords t vs)
    then show ?case
      using ord_container_values_seq_container_values_intersect
      by blast
  qed
qed

lemma valid_values_seq_container_unique_alt[simp]: "x \<in> ContainerValueList Imod \<Longrightarrow> seqof x :[Imod] y \<Longrightarrow> \<exists>z. y = TypeDef.seqof z"
  using SeqContainerValue.rule_seqof_container_values valid_values_seq_container_unique by blast

lemma valid_type_seq_container_values_unique[simp]: "\<And>y. x :[Imod] TypeDef.seqof y \<Longrightarrow> x \<in> SeqContainerValue Imod"
  unfolding Valid_def
proof-
  fix x y
  assume "(TypeDef.seqof y, x) \<in> Valid_rel Imod" then show "x \<in> SeqContainerValue Imod"
  proof
    assume "TypeDef.seqof y = TypeDef.boolean"
    then show ?thesis
      by simp
  next
    assume "TypeDef.seqof y = TypeDef.integer"
    then show ?thesis
      by simp
  next
    assume "TypeDef.seqof y = TypeDef.real"
    then show ?thesis
      by simp
  next
    assume "TypeDef.seqof y = TypeDef.string"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume "TypeDef.seqof y = t" then show ?thesis 
      using t_is_classtype by auto
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume "TypeDef.seqof y = t" then show ?thesis 
      using t_is_nullable_classtype by auto
  next
    fix t
    assume "TypeDef.seqof y = enumtype t"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume "TypeDef.seqof y = t" then show ?thesis 
      using t_is_userdatatype_type by auto
  next
    fix t
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume "TypeDef.seqof y = t" then show ?thesis 
      using t_is_bag_container_type bag_types_typedef by blast
  next
    fix t
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume "TypeDef.seqof y = t" then show ?thesis 
      using t_is_set_container_type set_types_typedef by blast
  next
    fix t vs
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume x_is_vs: "x = vs"
    assume vs_is_container_value: "vs \<in> SeqContainerValue Imod"
    assume "TypeDef.seqof y = t" then show ?thesis 
      using t_is_seq_container_type x_is_vs vs_is_container_value by blast
  next
    fix t
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume "TypeDef.seqof y = t" then show ?thesis 
      using t_is_ord_container_type ord_types_typedef by blast
  qed
qed

lemma valid_type_seq_container_values_unique_alt[simp]: "\<And>y. x :[Imod] TypeDef.seqof y \<Longrightarrow> \<exists>z. x = seqof z"
  using seq_container_values_are_seqs valid_type_seq_container_values_unique by blast

lemma valid_values_ord_container_unique[simp]: "x \<in> OrdContainerValue Imod \<Longrightarrow> x :[Imod] y \<Longrightarrow> \<exists>z. y = TypeDef.ordof z"
  unfolding Valid_def
proof-
  fix Imod :: "('o, 'nt) instance_model"
  fix x :: "('o, 'nt) ValueDef"
  fix y :: "('nt) TypeDef"
  assume x_in_set: "x \<in> OrdContainerValue Imod"
  assume "(y, x) \<in> Valid_rel Imod" then show "\<exists>z. y = TypeDef.ordof z"
    using x_in_set
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using ord_container_values_boolean_values_intersect
      by blast
  next
    case (valid_rule_integers v)
    then show ?case 
      using ord_container_values_integer_values_intersect
      by blast
  next
    case (valid_rule_reals v)
    then show ?case
      using ord_container_values_real_values_intersect
      by blast
  next
    case (valid_rule_strings v)
    then show ?case
      using ord_container_values_string_values_intersect
      by blast
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values t v)
    then show ?case
      using ord_container_values_userdata_values_intersect
      by blast
  next
    case (valid_rule_bags t vs)
    then show ?case
      using ord_container_values_bag_container_values_intersect
      by blast
  next
    case (valid_rule_sets t vs)
    then show ?case
      using ord_container_values_set_container_values_intersect
      by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case
      using ord_container_values_seq_container_values_intersect
      by blast
  next
    case (valid_rule_ords t vs)
    then show ?case
      by simp
  qed
qed

lemma valid_values_ord_container_unique_alt[simp]: "x \<in> ContainerValueList Imod \<Longrightarrow> ordof x :[Imod] y \<Longrightarrow> \<exists>z. y = TypeDef.ordof z"
  using OrdContainerValue.rule_ordof_container_values valid_values_ord_container_unique by blast

lemma valid_type_ord_container_values_unique[simp]: "\<And>y. x :[Imod] TypeDef.ordof y \<Longrightarrow> x \<in> OrdContainerValue Imod"
  unfolding Valid_def
proof-
  fix x y
  assume "(TypeDef.ordof y, x) \<in> Valid_rel Imod" then show "x \<in> OrdContainerValue Imod"
  proof
    assume "TypeDef.ordof y = TypeDef.boolean"
    then show ?thesis
      by simp
  next
    assume "TypeDef.ordof y = TypeDef.integer"
    then show ?thesis
      by simp
  next
    assume "TypeDef.ordof y = TypeDef.real"
    then show ?thesis
      by simp
  next
    assume "TypeDef.ordof y = TypeDef.string"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_classtype: "t \<in> ClassType (Tm Imod)"
    assume "TypeDef.ordof y = t" then show ?thesis 
      using t_is_classtype by auto
  next
    fix t
    assume t_is_nullable_classtype: "t \<in> NullableClassType (Tm Imod)"
    assume "TypeDef.ordof y = t" then show ?thesis 
      using t_is_nullable_classtype by auto
  next
    fix t
    assume "TypeDef.ordof y = enumtype t"
    then show ?thesis
      by simp
  next
    fix t
    assume t_is_userdatatype_type: "t \<in> UserDataTypeType (Tm Imod)"
    assume "TypeDef.ordof y = t" then show ?thesis 
      using t_is_userdatatype_type by auto
  next
    fix t
    assume t_is_bag_container_type: "t \<in> BagContainerType (Tm Imod)"
    assume "TypeDef.ordof y = t" then show ?thesis 
      using t_is_bag_container_type bag_types_typedef by blast
  next
    fix t
    assume t_is_set_container_type: "t \<in> SetContainerType (Tm Imod)"
    assume "TypeDef.ordof y = t" then show ?thesis 
      using t_is_set_container_type set_types_typedef by blast
  next
    fix t
    assume t_is_seq_container_type: "t \<in> SeqContainerType (Tm Imod)"
    assume "TypeDef.ordof y = t" then show ?thesis 
      using t_is_seq_container_type seq_types_typedef by blast
  next
    fix t vs
    assume t_is_ord_container_type: "t \<in> OrdContainerType (Tm Imod)"
    assume x_is_vs: "x = vs"
    assume vs_is_container_value: "vs \<in> OrdContainerValue Imod"
    assume "TypeDef.ordof y = t" then show ?thesis 
      using t_is_ord_container_type x_is_vs vs_is_container_value by blast
  qed
qed

lemma valid_type_ord_container_values_unique_alt[simp]: "\<And>y. x :[Imod] TypeDef.ordof y \<Longrightarrow> \<exists>z. x = ordof z"
  using ord_container_values_are_ords valid_type_ord_container_values_unique by blast

lemma unspecified_values_never_valid: "\<not>unspecified :[Imod] t"
proof-
  fix t
  have "\<And>v. v :[Imod] t \<Longrightarrow> v \<noteq> unspecified"
  proof-
    fix v
    assume "v :[Imod] t"
    then show "v \<noteq> unspecified"
      unfolding Valid_def
    proof (induct)
      case (valid_rule_booleans v)
      then show ?case
        by fastforce
    next
      case (valid_rule_integers v)
      then show ?case
        by fastforce
    next
      case (valid_rule_reals v)
      then show ?case
        by fastforce
    next
      case (valid_rule_strings v)
      then show ?case
        by fastforce
    next
      case (valid_rule_proper_classes v t)
      then show ?case
        by simp
    next
      case (valid_rule_nullable_classes t)
      then show ?case
        by simp
    next
      case (valid_rule_enumvalues t v)
      then show ?case
        by simp
    next
      case (valid_rule_userdata_values v t)
      then show ?case
        by fastforce
    next
      case (valid_rule_bags t vs)
      then show ?case
        by fastforce
    next
      case (valid_rule_sets t vs)
      then show ?case
        by fastforce
    next
      case (valid_rule_seqs t vs)
      then show ?case
        by fastforce
    next
      case (valid_rule_ords t vs)
      then show ?case
        by fastforce
    qed
  qed
  then show "\<not>unspecified :[Imod] t"
    by blast
qed

lemma invalid_values_never_valid: "\<not>invalid :[Imod] t"
proof-
  fix t
  have "\<And>v. v :[Imod] t \<Longrightarrow> v \<noteq> invalid"
  proof-
    fix v
    assume "v :[Imod] t"
    then show "v \<noteq> invalid"
      unfolding Valid_def
    proof (induct)
      case (valid_rule_booleans v)
      then show ?case
        by fastforce
    next
      case (valid_rule_integers v)
      then show ?case
        by fastforce
    next
      case (valid_rule_reals v)
      then show ?case
        by fastforce
    next
      case (valid_rule_strings v)
      then show ?case
        by fastforce
    next
      case (valid_rule_proper_classes v t)
      then show ?case
        by simp
    next
      case (valid_rule_nullable_classes t)
      then show ?case
        by simp
    next
      case (valid_rule_enumvalues t v)
      then show ?case
        by simp
    next
      case (valid_rule_userdata_values v t)
      then show ?case
        by fastforce
    next
      case (valid_rule_bags t vs)
      then show ?case
        by fastforce
    next
      case (valid_rule_sets t vs)
      then show ?case
        by fastforce
    next
      case (valid_rule_seqs t vs)
      then show ?case
        by fastforce
    next
      case (valid_rule_ords t vs)
      then show ?case
        by fastforce
    qed
  qed
  then show "\<not>invalid :[Imod] t"
    by blast
qed

lemma invalid_type_never_valid: "\<not>v :[Imod] TypeDef.invalid"
proof-
  fix v
  have "\<And>t. v :[Imod] t \<Longrightarrow> t \<noteq> TypeDef.invalid"
  proof-
    fix t
    assume "v :[Imod] t"
    then show "t \<noteq> TypeDef.invalid"
      unfolding Valid_def
    proof (induct)
      case (valid_rule_booleans v)
      then show ?case
        by simp
    next
      case (valid_rule_integers v)
      then show ?case
        by simp
    next
      case (valid_rule_reals v)
      then show ?case
        by simp
    next
      case (valid_rule_strings v)
      then show ?case
        by simp
    next
      case (valid_rule_proper_classes v t)
      then show ?case
        by fastforce
    next
      case (valid_rule_nullable_classes t)
      then show ?case
        by fastforce
    next
      case (valid_rule_enumvalues t v)
      then show ?case
        by simp
    next
      case (valid_rule_userdata_values v t)
      then show ?case
        by fastforce
    next
      case (valid_rule_bags t vs)
      then show ?case
        by fastforce
    next
      case (valid_rule_sets t vs)
      then show ?case
        by fastforce
    next
      case (valid_rule_seqs t vs)
      then show ?case
        by fastforce
    next
      case (valid_rule_ords t vs)
      then show ?case
        by fastforce
    qed
  qed
  then show "\<not>v :[Imod] TypeDef.invalid"
    by blast
qed

lemma valid_type_container_values_set_intersection: "xs \<in> ContainerValue Imod \<Longrightarrow> ys \<in> ContainerValue Imod \<Longrightarrow> 
  xs :[Imod] t1 \<Longrightarrow> ys :[Imod] t2 \<Longrightarrow> contained_list xs \<noteq> [] \<Longrightarrow> contained_list ys \<noteq> [] \<Longrightarrow> 
  set (contained_list xs) \<subseteq> AtomValue Imod \<Longrightarrow> set (contained_list ys) \<subseteq> ContainerValue Imod \<Longrightarrow> t1 \<noteq> t2"
proof-
  assume xs_container_value: "xs \<in> ContainerValue Imod"
  assume xs_valid: "xs :[Imod] t1"
  assume xs_not_empty: "contained_list xs \<noteq> []"
  assume xs_subset: "set (contained_list xs) \<subseteq> AtomValue Imod"
  have xs_of_type: "t1 \<in> ContainerType (Tm Imod)"
    using xs_container_value xs_valid
    by simp
  then have xs_contained_type: "\<And>z. z \<in> set (contained_list xs) \<Longrightarrow> z :[Imod] contained_type t1"
    using valid_values_container_recursive xs_valid
    by blast
  then have xs_contained_type: "contained_type t1 \<in> NonContainerType (Tm Imod)"
    using list.set_intros(1) neq_Nil_conv subsetD valid_values_atom_set xs_not_empty xs_subset
    by metis
  assume ys_container_value: "ys \<in> ContainerValue Imod"
  assume ys_valid: "ys :[Imod] t2"
  assume ys_not_empty: "contained_list ys \<noteq> []"
  assume ys_subset: "set (contained_list ys) \<subseteq> ContainerValue Imod"
  have ys_of_type: "t2 \<in> ContainerType (Tm Imod)"
    using ys_container_value ys_valid
    by simp
  then have ys_contained_type: "\<And>z. z \<in> set (contained_list ys) \<Longrightarrow> z :[Imod] contained_type t2"
    using valid_values_container_recursive ys_valid
    by blast
  then have ys_contained_type: "contained_type t2 \<in> ContainerType (Tm Imod)"
    using list.set_intros(1) neq_Nil_conv subsetD valid_values_container_set ys_not_empty ys_subset
    by metis
  show "t1 \<noteq> t2"
    using xs_contained_type ys_contained_type container_type_non_container_type_intersect
    by blast
qed

lemma valid_type_container_atom_values: "xs \<in> ContainerValue Imod \<Longrightarrow> ys \<in> ContainerValue Imod \<Longrightarrow> 
  xs :[Imod] t \<Longrightarrow> ys :[Imod] t \<Longrightarrow> contained_list xs \<noteq> [] \<Longrightarrow> contained_list ys \<noteq> [] \<Longrightarrow> 
  set (contained_list xs) \<subseteq> AtomValue Imod \<Longrightarrow> set (contained_list ys) \<subseteq> AtomValue Imod"
proof-
  assume xs_container_value: "xs \<in> ContainerValue Imod"
  assume xs_valid: "xs :[Imod] t"
  assume xs_not_empty: "contained_list xs \<noteq> []"
  assume xs_subset: "set (contained_list xs) \<subseteq> AtomValue Imod"
  assume ys_container_value: "ys \<in> ContainerValue Imod"
  assume ys_valid: "ys :[Imod] t"
  assume ys_not_empty: "contained_list ys \<noteq> []"
  then show "set (contained_list ys) \<subseteq> AtomValue Imod"
    using atom_value_list_members container_value_list_members_alt container_value_members_alt 
    using subset_code(1) valid_type_container_values_set_intersection xs_container_value xs_not_empty 
    using xs_subset xs_valid ys_container_value ys_not_empty ys_valid
    by metis
qed

lemma valid_type_container_container_values: "xs \<in> ContainerValue Imod \<Longrightarrow> ys \<in> ContainerValue Imod \<Longrightarrow> 
  xs :[Imod] t \<Longrightarrow> ys :[Imod] t \<Longrightarrow> contained_list xs \<noteq> [] \<Longrightarrow> contained_list ys \<noteq> [] \<Longrightarrow> 
  set (contained_list xs) \<subseteq> ContainerValue Imod \<Longrightarrow> set (contained_list ys) \<subseteq> ContainerValue Imod"
proof-
  assume xs_container_value: "xs \<in> ContainerValue Imod"
  assume xs_valid: "xs :[Imod] t"
  assume xs_not_empty: "contained_list xs \<noteq> []"
  assume xs_subset: "set (contained_list xs) \<subseteq> ContainerValue Imod"
  assume ys_container_value: "ys \<in> ContainerValue Imod"
  assume ys_valid: "ys :[Imod] t"
  assume ys_not_empty: "contained_list ys \<noteq> []"
  then show "set (contained_list ys) \<subseteq> ContainerValue Imod"
    using atom_value_list_members container_value_list_members_alt container_value_members_alt 
    using subset_code(1) valid_type_container_values_set_intersection xs_container_value xs_not_empty 
    using xs_subset xs_valid ys_container_value ys_not_empty ys_valid
    by metis
qed



section "Multiplicity validity"

definition validMul :: "('o, 'nt) instance_model \<Rightarrow> ('o \<times> ('nt Id \<times> 'nt)) \<times> ('o, 'nt) ValueDef \<Rightarrow> bool" where
  "validMul Imod fv \<equiv> snd fv :[Imod] type (Tm Imod) (snd (fst fv)) \<and> 
    (snd fv \<in> ContainerValue Imod \<longrightarrow> lower (Tm Imod) (snd (fst fv)) \<le> Nr (length (contained_list (snd fv))) \<and> 
      Nr (length (contained_list (snd fv))) \<le> upper (Tm Imod) (snd (fst fv)))"


subsection "Lemmas on the multiplicity validity"

lemma mulitiplicity_for_non_container[simp]: "v :[Imod] type (Tm Imod) f \<Longrightarrow> v \<notin> ContainerValue Imod \<Longrightarrow> validMul Imod ((ob, f), v)"
  unfolding validMul_def
proof
  show "v :[Imod] type (Tm Imod) f \<Longrightarrow> v \<notin> ContainerValue Imod \<Longrightarrow> snd ((ob, f), v) :[Imod] type (Tm Imod) (snd (fst ((ob, f), v)))"
    by simp
  show "v :[Imod] type (Tm Imod) f \<Longrightarrow> v \<notin> ContainerValue Imod \<Longrightarrow> snd ((ob, f), v) \<in> ContainerValue Imod \<longrightarrow> 
    lower (Tm Imod) (snd (fst ((ob, f), v))) \<le> \<^bold>(length (contained_list (snd ((ob, f), v)))) \<and> \<^bold>(length (contained_list (snd ((ob, f), v)))) \<le> upper (Tm Imod) (snd (fst ((ob, f), v)))"
    by simp
qed



section "Value edges"

definition objValueCheck :: "'o \<Rightarrow> ('o, 'nt) ValueDef \<Rightarrow> bool" where
  "objValueCheck ob v \<equiv> v = obj ob"

definition edgeCount :: "('o, 'nt) instance_model \<Rightarrow> 'o \<Rightarrow> ('nt Id \<times> 'nt) \<Rightarrow> 'o \<Rightarrow> nat" where
  "edgeCount Imod a r b \<equiv> if a \<notin> Object Imod \<or> r \<notin> Field (Tm Imod) \<or> \<not>\<exclamdown>(ObjectClass Imod a) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) r) then 0 else length (filter (objValueCheck b) (contained_list (FieldValue Imod (a, r))))"

definition edge :: "('o, 'nt) instance_model \<Rightarrow> 'o \<Rightarrow> ('nt Id \<times> 'nt) \<Rightarrow> 'o \<Rightarrow> bool" where
  "edge Imod a r b \<equiv> edgeCount Imod a r b \<ge> 1"



section "Property satisfaction"

inductive_set object_containments :: "('o, 'nt) instance_model \<Rightarrow> 'o \<Rightarrow> (('o \<times> ('nt Id \<times> 'nt)) \<times> 'o) set"
  for Imod :: "('o, 'nt) instance_model"
  and o2 :: "'o"
  where
    rule_object_containment: "\<And>o1 r. o1 \<in> Object Imod \<Longrightarrow> r \<in> CR (Tm Imod) \<Longrightarrow> r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod o1) \<Longrightarrow> obj o2 \<in> set (contained_values (FieldValue Imod (o1, r))) \<Longrightarrow> ((o1, r), o2) \<in> object_containments Imod o2"

inductive_set object_containments_relation :: "('o, 'nt) instance_model \<Rightarrow> 'o rel"
  for Imod :: "('o, 'nt) instance_model"
  where
    rule_object_containment: "\<And>o1 o2 r. o1 \<in> Object Imod \<Longrightarrow> r \<in> CR (Tm Imod) \<Longrightarrow> r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod o1) \<Longrightarrow> obj o2 \<in> set (contained_values (FieldValue Imod (o1, r))) \<Longrightarrow> (o1, o2) \<in> object_containments_relation Imod"

inductive property_satisfaction :: "('o, 'nt) instance_model \<Rightarrow> ('nt) PropertyDef \<Rightarrow> bool" ("_ \<Turnstile> _"  [50, 50] 50)
  for Imod :: "('o, 'nt) instance_model"
  where
    rule_property_abstract: "\<lbrakk> \<And>ob. ob \<in> Object Imod \<Longrightarrow> ObjectClass Imod ob \<noteq> c \<rbrakk> \<Longrightarrow> Imod \<Turnstile> abstract c" |
    rule_property_containment: "\<lbrakk> \<And>ob. ob \<in> Object Imod \<Longrightarrow> card (object_containments Imod ob) \<le> 1; irrefl ((object_containments_relation Imod)\<^sup>+) \<rbrakk> \<Longrightarrow> Imod \<Turnstile> containment r" |
    rule_property_defaultValue: "Imod \<Turnstile> defaultValue f v" | 
    rule_property_identity: "\<lbrakk> \<And>o1 o2 a. o1 \<in> Object Imod \<Longrightarrow> o2 \<in> Object Imod \<Longrightarrow> ObjectClass Imod o1 = c \<Longrightarrow> ObjectClass Imod o2 = c \<Longrightarrow> a \<in> A \<Longrightarrow> FieldValue Imod (o1, a) \<equiv>[Imod] FieldValue Imod (o2, a) \<Longrightarrow> o1 = o2 \<rbrakk> \<Longrightarrow> Imod \<Turnstile> identity c A" |
    rule_property_keyset: "\<lbrakk> \<And>o1 o2 p a. o1 \<in> Object Imod \<Longrightarrow> o2 \<in> Object Imod \<Longrightarrow> p \<in> Object Imod \<Longrightarrow> r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod p) \<Longrightarrow> edge Imod p r o1 \<Longrightarrow> edge Imod p r o2 \<Longrightarrow> a \<in> A \<Longrightarrow> FieldValue Imod (o1, a) \<equiv>[Imod] FieldValue Imod (o2, a) \<Longrightarrow> o1 = o2 \<rbrakk> \<Longrightarrow> Imod \<Turnstile> keyset r A" |
    rule_property_opposite: "\<lbrakk> \<And>o1 o2. o1 \<in> Object Imod \<Longrightarrow> o2 \<in> Object Imod \<Longrightarrow> edgeCount Imod o1 r1 o2 = edgeCount Imod o2 r2 o1 \<rbrakk> \<Longrightarrow> Imod \<Turnstile> opposite r1 r2" |
    rule_property_readonly: "Imod \<Turnstile> readonly f"

lemma property_satisfaction_abstract_rev: "Imod \<Turnstile> abstract c \<Longrightarrow> ob \<in> Object Imod \<Longrightarrow> ObjectClass Imod ob \<noteq> c"
proof-
  assume ob_in_imod: "ob \<in> Object Imod"
  assume "Imod \<Turnstile> abstract c"
  then show "ObjectClass Imod ob \<noteq> c"
  proof (cases)
    case rule_property_abstract
    then show ?thesis
      by (simp add: ob_in_imod)
  qed
qed

lemma property_satisfaction_containment_rev: "Imod \<Turnstile> containment r \<Longrightarrow> 
  (ob \<in> Object Imod \<longrightarrow> card (object_containments Imod ob) \<le> 1) \<and> irrefl ((object_containments_relation Imod)\<^sup>+)"
proof-
  assume "Imod \<Turnstile> containment r"
  then show "(ob \<in> Object Imod \<longrightarrow> card (object_containments Imod ob) \<le> 1) \<and> irrefl ((object_containments_relation Imod)\<^sup>+)"
  proof (cases)
    case rule_property_containment
    then show ?thesis
      by blast
  qed
qed

lemma property_satisfaction_identity_rev: "Imod \<Turnstile> identity c A \<Longrightarrow> 
  o1 \<in> Object Imod \<Longrightarrow> o2 \<in> Object Imod \<Longrightarrow> 
  ObjectClass Imod o1 = c \<Longrightarrow> ObjectClass Imod o2 = c \<Longrightarrow> a \<in> A \<Longrightarrow> 
  FieldValue Imod (o1, a) \<equiv>[Imod] FieldValue Imod (o2, a) \<Longrightarrow> o1 = o2"
proof-
  assume o1_in_imod: "o1 \<in> Object Imod"
  assume o2_in_imod: "o2 \<in> Object Imod"
  assume o1_class_c: "ObjectClass Imod o1 = c"
  assume o2_class_c: "ObjectClass Imod o2 = c"
  assume a_in_a: "a \<in> A"
  assume field_value_equiv: "FieldValue Imod (o1, a) \<equiv>[Imod] FieldValue Imod (o2, a)"
  assume "Imod \<Turnstile> identity c A"
  then show "o1 = o2"
  proof (cases)
    case rule_property_identity
    then show ?thesis
      using a_in_a field_value_equiv o1_class_c o1_in_imod o2_class_c o2_in_imod
      by blast
  qed
qed

lemma property_satisfaction_keyset_rev: "Imod \<Turnstile> keyset r A \<Longrightarrow> 
  o1 \<in> Object Imod \<Longrightarrow> o2 \<in> Object Imod \<Longrightarrow> p \<in> Object Imod \<Longrightarrow> 
  r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod p) \<Longrightarrow> edge Imod p r o1 \<Longrightarrow> edge Imod p r o2 \<Longrightarrow> 
  a \<in> A \<Longrightarrow> FieldValue Imod (o1, a) \<equiv>[Imod] FieldValue Imod (o2, a) \<Longrightarrow> o1 = o2"
proof-
  assume o1_in_imod: "o1 \<in> Object Imod"
  assume o2_in_imod: "o2 \<in> Object Imod"
  assume p_in_imod: "p \<in> Object Imod"
  assume r_field_in_p: "r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod p)"
  assume edge_o1: "edge Imod p r o1"
  assume edge_o2: "edge Imod p r o2"
  assume a_in_a: "a \<in> A"
  assume field_value_equiv: "FieldValue Imod (o1, a) \<equiv>[Imod] FieldValue Imod (o2, a)"
  assume "Imod \<Turnstile> keyset r A"
  then show "o1 = o2"
  proof (cases)
    case rule_property_keyset
    then show ?thesis
      using a_in_a edge_o1 edge_o2 field_value_equiv o1_in_imod o2_in_imod r_field_in_p p_in_imod
      by blast
  qed
qed

lemma property_satisfaction_opposite_rev: "Imod \<Turnstile> opposite r1 r2 \<Longrightarrow> 
  o1 \<in> Object Imod \<Longrightarrow> o2 \<in> Object Imod \<Longrightarrow> edgeCount Imod o1 r1 o2 = edgeCount Imod o2 r2 o1"
proof-
  assume o1_in_imod: "o1 \<in> Object Imod"
  assume o2_in_imod: "o2 \<in> Object Imod"
  assume "Imod \<Turnstile> opposite r1 r2"
  then show "edgeCount Imod o1 r1 o2 = edgeCount Imod o2 r2 o1"
  proof (cases)
    case rule_property_opposite
    then show ?thesis
      by (simp add: o1_in_imod o2_in_imod)
  qed
qed



section "Model validity"

locale instance_model = fixes Imod :: "('o, 'nt) instance_model"
  assumes structure_object_class_wellformed[simp]: "\<And>ob. ob \<in> Object Imod \<Longrightarrow> ObjectClass Imod ob \<in> Class (Tm Imod)"
  assumes structure_object_class_domain[simp]: "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectClass Imod ob = undefined"
  assumes structure_object_id_domain[simp]: "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectId Imod ob = undefined"
  assumes structure_field_values_domain: "\<And>ob f. ob \<notin> Object Imod \<or> f \<notin> Field (Tm Imod) \<Longrightarrow> FieldValue Imod (ob, f) = undefined"
  assumes structure_default_values_wellformed: "\<And>c. c \<in> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c \<in> Value Imod"
  assumes structure_default_values_domain[simp]: "\<And>c. c \<notin> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c = undefined"
  assumes property_object_id_uniqueness: "\<And>o1 o2. o1 \<in> Object Imod \<Longrightarrow> o2 \<in> Object Imod \<Longrightarrow> ObjectId Imod o1 = ObjectId Imod o2 \<Longrightarrow> o1 = o2"
  assumes property_field_values_outside_domain: "\<And>ob f. ob \<in> Object Imod \<Longrightarrow> f \<in> Field (Tm Imod) \<Longrightarrow> \<not>\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) f) \<Longrightarrow> FieldValue Imod (ob, f) = unspecified"
  assumes property_field_values_inside_domain: "\<And>ob f. ob \<in> Object Imod \<Longrightarrow> f \<in> Field (Tm Imod) \<Longrightarrow> \<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) f) \<Longrightarrow> FieldValue Imod (ob, f) \<in> Value Imod"
  assumes validity_values_typed: "\<And>ob f. ob \<in> Object Imod \<Longrightarrow> f \<in> Field (Tm Imod) \<Longrightarrow> \<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) f) \<Longrightarrow> FieldValue Imod (ob, f) :[Imod] type (Tm Imod) f"
  assumes validity_multiplicities_valid: "\<And>ob f. ob \<in> Object Imod \<Longrightarrow> f \<in> Field (Tm Imod) \<Longrightarrow> \<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) f) \<Longrightarrow> validMul Imod ((ob, f), FieldValue Imod (ob, f))"
  assumes validity_properties_satisfied: "\<And>p. p \<in> Prop (Tm Imod) \<Longrightarrow> Imod \<Turnstile> p"
  assumes validity_default_value_types: "\<And>c. c \<in> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c :[Imod] ConstType (Tm Imod) c"
  assumes validity_type_model_consistent: "type_model (Tm Imod)"

context instance_model
begin

lemma structure_field_values_domain_no_object[simp]: "\<And>ob f. ob \<notin> Object Imod \<Longrightarrow> FieldValue Imod (ob, f) = undefined"
  using structure_field_values_domain
  by blast

lemma structure_field_values_domain_no_field[simp]: "\<And>ob f. f \<notin> Field (Tm Imod) \<Longrightarrow> FieldValue Imod (ob, f) = undefined"
  using structure_field_values_domain
  by blast

lemma structure_field_values_domain_rev: "\<And>ob f. FieldValue Imod (ob, f) \<noteq> undefined \<Longrightarrow> ob \<in> Object Imod \<and> f \<in> Field (Tm Imod)"
  using structure_field_values_domain instance_model_axioms
  by metis

lemma structure_field_values_domain_rev_impl_object[simp]: "\<And>ob f. FieldValue Imod (ob, f) \<noteq> undefined \<Longrightarrow> ob \<in> Object Imod"
  using structure_field_values_domain
  by blast

lemma structure_field_values_domain_rev_impl_field[simp]: "\<And>ob f. FieldValue Imod (ob, f) \<noteq> undefined \<Longrightarrow> f \<in> Field (Tm Imod)"
  using structure_field_values_domain
  by blast

lemma property_field_values_wellformed: "FieldValue Imod (ob, f) = undefined \<or> FieldValue Imod (ob, f) = unspecified \<or> FieldValue Imod (ob, f) \<in> Value Imod"
proof-
  fix ob f
  show "FieldValue Imod (ob, f) = undefined \<or> FieldValue Imod (ob, f) = unspecified \<or> FieldValue Imod (ob, f) \<in> Value Imod"
  proof (induct "ob \<in> Object Imod")
    case True
    then show ?case
    proof (induct "f \<in> Field (Tm Imod)")
      case True
      then show ?case
      proof (induct "\<exclamdown>(ObjectClass Imod ob) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) f)")
        case True
        then show ?case
          using property_field_values_inside_domain
          by blast
      next
        case False
        then show ?case
          using property_field_values_outside_domain
          by blast
      qed
    next
      case False
      then show ?case
        using structure_field_values_domain
        by blast
    qed
  next
    case False
    then show ?case
      using structure_field_values_domain
      by blast
  qed
qed

lemma property_field_values_not_undef_impl_value: "FieldValue Imod (ob, f) \<noteq> undefined \<Longrightarrow> FieldValue Imod (ob, f) = unspecified \<or> FieldValue Imod (ob, f) \<in> Value Imod"
  using property_field_values_wellformed
  by blast

lemma property_field_values_not_value_impl_undef: "FieldValue Imod (ob, f) \<noteq> unspecified \<and> FieldValue Imod (ob, f) \<notin> Value Imod \<Longrightarrow> FieldValue Imod (ob, f) = undefined"
  using property_field_values_wellformed
  by blast

end

subsection "Lemmas on value edges using instance model validity"

lemma edge_count_non_container_leq_one[simp]: "instance_model Imod \<Longrightarrow> a \<in> Object Imod \<Longrightarrow> r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod a) \<Longrightarrow> type (Tm Imod) r \<notin> ContainerType (Tm Imod) \<Longrightarrow> edgeCount Imod a r b \<le> 1"
  unfolding edgeCount_def
proof-
  fix a b r
  assume valid_instance_model: "instance_model Imod"
  assume a_in_object: "a \<in> Object Imod"
  assume r_field_of_a: "r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod a)"
  assume r_not_container_type: "type (Tm Imod) r \<notin> ContainerType (Tm Imod)"
  have r_in_field: "r \<in> Field (Tm Imod)" 
    using r_field_of_a fields_of_class_are_fields
    by auto
  have a_extends_r_field_type: "\<exclamdown>(ObjectClass Imod a) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) r)"
    using fields_of_class_subtype_field_class r_field_of_a 
    by simp
  have field_r_set_for_a: "FieldValue Imod (a, r) \<in> Value Imod"
    by (simp add: r_in_field a_in_object instance_model.property_field_values_inside_domain r_field_of_a valid_instance_model)
  have "FieldValue Imod (a, r) :[Imod] type (Tm Imod) r"
    by (simp add: a_in_object instance_model.validity_values_typed r_field_of_a r_in_field valid_instance_model)
  then have field_not_in_container_value: "FieldValue Imod (a, r) \<notin> ContainerValue Imod"
    using r_not_container_type
    unfolding Valid_def
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      using container_values_are_not_booleans boolean_values_are_booleans by blast
  next
    case (valid_rule_integers v)
    then show ?case
      using container_values_are_not_integers integer_values_are_integers by blast
  next
    case (valid_rule_reals v)
    then show ?case
      using container_values_are_not_reals real_values_are_reals by blast
  next
    case (valid_rule_strings v)
    then show ?case
      using container_values_are_not_strings string_values_are_strings by blast
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      by simp
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      by simp
  next
    case (valid_rule_userdata_values v t)
    then show ?case
      using container_values_are_not_userdatavalues userdata_values_are_userdatavalues by blast
  next
    case (valid_rule_bags t vs)
    then show ?case using bag_container_values_are_container_values bag_types_are_container_types by blast
  next
    case (valid_rule_sets t vs)
    then show ?case using set_container_values_are_container_values set_types_are_container_types by blast
  next
    case (valid_rule_seqs t vs)
    then show ?case using seq_container_values_are_container_values seq_types_are_container_types by blast
  next
    case (valid_rule_ords t vs)
    then show ?case using ord_container_values_are_container_values ord_types_are_container_types by blast
  qed
  have not_container_value_atom_value: "\<And>x. x \<in> Value Imod \<Longrightarrow> x \<notin> ContainerValue Imod \<Longrightarrow> x \<in> AtomValue Imod"
    by (simp add: Value_def)
  have length_of_atom_type_is_one: "length (contained_list (FieldValue Imod (a, r))) = 1"
    using field_r_set_for_a field_not_in_container_value not_container_value_atom_value
    by fastforce
  have "length (filter (objValueCheck b) (contained_list (FieldValue Imod (a, r)))) \<le> 1"
    using length_of_atom_type_is_one length_filter_le
    by metis
  then show "(if a \<notin> Object Imod \<or> r \<notin> type_model.Field (Tm Imod) \<or> \<not> \<exclamdown>(ObjectClass Imod a) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) r) then 0 else length (filter (objValueCheck b) (contained_list (FieldValue Imod (a, r))))) \<le> 1"
    by fastforce
qed

lemma edge_count_non_container_incorrect_obj_eq_zero[simp]: "instance_model Imod \<Longrightarrow> a \<in> Object Imod \<Longrightarrow> r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod a) \<Longrightarrow> type (Tm Imod) r \<notin> ContainerType (Tm Imod) \<Longrightarrow> FieldValue Imod (a, r) \<noteq> obj b \<Longrightarrow> edgeCount Imod a r b = 0"
  unfolding edgeCount_def
proof-
  fix a b r x
  assume valid_instance_model: "instance_model Imod"
  assume a_in_object: "a \<in> Object Imod"
  assume r_field_of_a: "r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod a)"
  assume r_not_container_type: "type (Tm Imod) r \<notin> ContainerType (Tm Imod)"
  assume r_field_value_in_a: "FieldValue Imod (a, r) \<noteq> obj b"
  have r_in_field: "r \<in> Field (Tm Imod)" 
    using r_field_of_a fields_of_class_are_fields
    by auto
  then have field_in_value: "FieldValue Imod (a, r) \<in> Value Imod"
    by (simp add: a_in_object instance_model.property_field_values_inside_domain r_field_of_a valid_instance_model)
  have "FieldValue Imod (a, r) :[Imod] type (Tm Imod) r"
    by (simp add: a_in_object instance_model.validity_values_typed r_field_of_a r_in_field valid_instance_model)
  then have field_not_in_container_value: "FieldValue Imod (a, r) \<notin> ContainerValue Imod"
    using r_not_container_type
    unfolding Valid_def
  proof (induct "FieldValue Imod (a, r)")
    case valid_rule_booleans
    then show ?case
      using boolean_values_are_booleans by fastforce
  next
    case valid_rule_integers
    then show ?case
      using integer_values_are_integers by fastforce
  next
    case valid_rule_reals
    then show ?case
      using real_values_are_reals by fastforce
  next
    case valid_rule_strings
    then show ?case
      using string_values_are_strings by fastforce
  next
    case (valid_rule_proper_classes v t)
    then show ?case
      using container_values_are_not_objects by metis
  next
    case (valid_rule_nullable_classes t)
    then show ?case
      by simp
  next
    case (valid_rule_enumvalues t v)
    then show ?case
      using container_values_are_not_enumvalues by metis
  next
    case (valid_rule_userdata_values t)
    then show ?case
      using userdata_values_are_userdatavalues by fastforce
  next
    case (valid_rule_bags t)
    then show ?case
      using bag_types_are_container_types by blast
  next
    case (valid_rule_sets t)
    then show ?case
      using set_types_are_container_types by blast
  next
    case (valid_rule_seqs t)
    then show ?case
      using seq_types_are_container_types by blast
  next
    case (valid_rule_ords t)
    then show ?case
      using ord_types_are_container_types by blast
  qed
  then have "FieldValue Imod (a, r) \<in> AtomValue Imod"
    using field_in_value
    by (simp add: Value_def)
  then have "contained_list (FieldValue Imod (a, r)) = [FieldValue Imod (a, r)]"
    by simp
  then have "length (filter (objValueCheck b) (contained_list (FieldValue Imod (a, r)))) = 0"
    by (simp add: objValueCheck_def r_field_value_in_a)
  then show "(if a \<notin> Object Imod \<or> r \<notin> type_model.Field (Tm Imod) \<or> \<not> \<exclamdown>(ObjectClass Imod a) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) r) then 0 else length (filter (objValueCheck b) (contained_list (FieldValue Imod (a, r))))) = 0"
    by fastforce
qed

lemma edge_non_container_incorrect_obj[simp]: "instance_model Imod \<Longrightarrow> a \<in> Object Imod \<Longrightarrow> r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod a) \<Longrightarrow> type (Tm Imod) r \<notin> ContainerType (Tm Imod) \<Longrightarrow> FieldValue Imod (a, r) \<noteq> obj b \<Longrightarrow> \<not>(edge Imod a r b)"
  by (simp add: edge_def)

lemma edge_count_non_container_correct_obj_eq_one[simp]: "a \<in> Object Imod \<Longrightarrow> r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod a) \<Longrightarrow> FieldValue Imod (a, r) = obj b \<Longrightarrow> edgeCount Imod a r b = 1"
  unfolding edgeCount_def
proof-
  fix a b r
  assume a_in_object: "a \<in> Object Imod"
  assume "r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod a)"
  then have r_in_fields_a: "r \<in> Field (Tm Imod) \<and> \<exclamdown>(ObjectClass Imod a) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) r)"
    unfolding Type_Model.fields_def class_def
    by fastforce
  assume r_field_value_in_a: "FieldValue Imod (a, r) = obj b"
  have "contained_list (FieldValue Imod (a, r)) = [obj b]"
    by (simp add: r_field_value_in_a)
  then have filter_over_r_returns_obj_b: "filter (objValueCheck b) (contained_list (FieldValue Imod (a, r))) = [obj b]"
    by (simp add: objValueCheck_def)
  have "length (filter (objValueCheck b) (contained_list (FieldValue Imod (a, r)))) = 1"
    by (simp add: filter_over_r_returns_obj_b)
  then show "(if a \<notin> Object Imod \<or> r \<notin> Field (Tm Imod) \<or> \<not>\<exclamdown>(ObjectClass Imod a) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) r) then 0 else length (filter (objValueCheck b) (contained_list (FieldValue Imod (a, r))))) = 1"
    by (simp add: a_in_object r_in_fields_a)
qed

lemma edge_non_container_correct_obj[simp]: "a \<in> Object Imod \<Longrightarrow> r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod a) \<Longrightarrow> FieldValue Imod (a, r) = obj b \<Longrightarrow> edge Imod a r b"
  by (simp add: edge_def)

lemma edge_count_non_existant_object[simp]: "instance_model Imod \<Longrightarrow> a \<in> Object Imod \<Longrightarrow> r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod a) \<Longrightarrow> b \<notin> Object Imod \<Longrightarrow> edgeCount Imod a r b = 0"
  unfolding edgeCount_def
proof-
  fix a b r
  assume valid_instance_model: "instance_model Imod"
  assume a_in_object: "a \<in> Object Imod"
  assume "r \<in> Type_Model.fields (Tm Imod) (ObjectClass Imod a)"
  then have r_in_fields_a: "r \<in> Field (Tm Imod) \<and> \<exclamdown>(ObjectClass Imod a) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) r)"
    unfolding Type_Model.fields_def class_def
    by fastforce
  assume b_not_in_object: "b \<notin> Object Imod"
  have "\<And>x. x \<in> ProperClassValue Imod \<Longrightarrow> x \<noteq> obj b"
  proof-
    fix x
    assume "x \<in> ProperClassValue Imod"
    then show "x \<noteq> obj b"
    proof (induct)
      case (rule_proper_objects ob)
      then show ?case
        using b_not_in_object
        by blast
    qed
  qed
  then have b_not_in_value: "obj b \<notin> Value Imod"
    unfolding Value_def AtomValue_def ClassValue_def
    by fastforce
  then have object_value_check_invalid: "\<And>x. x \<in> Value Imod \<Longrightarrow> \<not>objValueCheck b x"
    unfolding objValueCheck_def
    by blast
  have "contained_list (FieldValue Imod (a, r)) \<in> ContainerValueList Imod \<or> contained_list (FieldValue Imod (a, r)) \<in> AtomValueList Imod"
    using AtomValueList.rule_fst_atom_element Un_iff Value_def a_in_object atom_values_contained_list_singleton container_value_members_alt instance_model.property_field_values_inside_domain r_in_fields_a valid_instance_model
    by metis
  then have "\<And>x. x \<in> set (contained_list (FieldValue Imod (a, r))) \<Longrightarrow> x \<in> Value Imod"
    using Un_iff Value_def atom_value_list_members container_value_list_members_alt
    by metis
  then have "length (filter (objValueCheck b) (contained_list (FieldValue Imod (a, r)))) = 0"
    by (simp add: object_value_check_invalid)
  then show "(if a \<notin> Object Imod \<or> r \<notin> type_model.Field (Tm Imod) \<or> \<not> \<exclamdown>(ObjectClass Imod a) \<sqsubseteq>[Tm Imod] \<exclamdown>(class (Tm Imod) r) then 0 else length (filter (objValueCheck b) (contained_list (FieldValue Imod (a, r))))) = 0"
    by simp
qed

lemma edge_count_impl_in_set[simp]: "edgeCount Imod a r b \<ge> 1 \<Longrightarrow> obj b \<in> set (contained_list (FieldValue Imod (a, r)))"
proof-
  assume edge_count_geq: "edgeCount Imod a r b \<ge> 1"
  then have "edgeCount Imod a r b = length (filter (objValueCheck b) (contained_list (FieldValue Imod (a, r))))"
    unfolding edgeCount_def
    by fastforce
  then have "length (filter (objValueCheck b) (contained_list (FieldValue Imod (a, r)))) \<ge> 1"
    using edge_count_geq
    by simp
  then show "obj b \<in> set (contained_list (FieldValue Imod (a, r)))"
    using One_nat_def filter_False le_zero_eq length_0_conv nat.simps(3) objValueCheck_def
    by metis
qed

lemma edge_impl_in_set[simp]: "edge Imod a r b \<Longrightarrow> obj b \<in> set (contained_list (FieldValue Imod (a, r)))"
  unfolding edge_def
  by (fact edge_count_impl_in_set)

lemma object_containments_relation_domain: "Domain (object_containments_relation Imod) \<subseteq> Object Imod"
proof
  fix x
  assume "x \<in> Domain (object_containments_relation Imod)"
  then show "x \<in> Object Imod"
  proof
    fix b
    assume "(x, b) \<in> object_containments_relation Imod"
    then show "x \<in> Object Imod"
      using object_containments_relation.induct
      by auto
  qed
qed

lemma object_containments_relation_range: "instance_model Imod \<Longrightarrow> Range (object_containments_relation Imod) \<subseteq> Object Imod"
proof
  fix x
  assume instance_model_valid: "instance_model Imod"
  assume "x \<in> Range (object_containments_relation Imod)"
  then show "x \<in> Object Imod"
  proof
    fix a
    assume "(a, x) \<in> object_containments_relation Imod"
    then show "x \<in> Object Imod"
    proof (induct)
      case (rule_object_containment o1 o2 r)
      then have "FieldValue Imod (o1, r) \<in> Value Imod"
        using fields_of_class_are_fields fields_of_class_subtype_field_class instance_model.property_field_values_inside_domain instance_model_valid
        by metis
      then have "set (contained_values (FieldValue Imod (o1, r))) \<subseteq> Value Imod"
        unfolding Value_def
        using container_value_contained_values atom_values_contained_values_singleton
        by fastforce
      then have "obj o2 \<in> Value Imod"
        using rule_object_containment.hyps(4)
        by blast
      then have "obj o2 \<in> ProperClassValue Imod"
        unfolding Value_def AtomValue_def ClassValue_def
        by simp
      then show ?case
        using ProperClassValue.cases
        by blast
    qed
  qed
qed

lemma object_containments_relation_field: "instance_model Imod \<Longrightarrow> Relation.Field (object_containments_relation Imod) \<subseteq> Object Imod"
proof
  fix x
  assume instance_model_valid: "instance_model Imod"
  assume "x \<in> Relation.Field (object_containments_relation Imod)"
  then show "x \<in> Object Imod"
    unfolding Relation.Field_def
    using Un_iff instance_model_valid object_containments_relation_domain object_containments_relation_range subset_eq
    by metis
qed



section "Validity of trivial instance models"

definition imod_empty :: "('nt, 'o) instance_model" where
  [simp]: "imod_empty = \<lparr>
    Tm = tmod_empty,
    Object = {},
    ObjectClass = (\<lambda>x. undefined),
    ObjectId = (\<lambda>x. undefined),
    FieldValue = (\<lambda>x. undefined),
    DefaultValue = (\<lambda>x. undefined)
  \<rparr>"

lemma imod_empty_correct[simp]: "instance_model imod_empty"
proof (intro instance_model.intro)
  show "type_model (Tm imod_empty)"
    unfolding imod_empty_def
    using tmod_empty_correct
    by simp
qed (simp_all)

lemma imod_empty_any_type_model_correct[simp]:
  assumes instance_model_type_model: "type_model (Tm Imod)"
  assumes instance_model_type_model_no_constants: "Constant (Tm Imod) = {}"
  assumes instance_model_objects: "Object Imod = {}"
  assumes instance_model_object_class: "ObjectClass Imod = (\<lambda>x. undefined)"
  assumes instance_model_object_id: "ObjectId Imod = (\<lambda>x. undefined)"
  assumes instance_model_field_value: "FieldValue Imod = (\<lambda>x. undefined)"
  assumes instance_model_default_value: "DefaultValue Imod = (\<lambda>x. undefined)"
  shows "instance_model Imod"
proof (intro instance_model.intro)
  fix p
  show "Imod \<Turnstile> p"
  proof (induct p)
    case (abstract c)
    then show ?case
    proof (intro property_satisfaction.rule_property_abstract)
      fix ob
      assume "ob \<in> Object Imod"
      then show "ObjectClass Imod ob \<noteq> c"
        by (simp add: instance_model_objects)
    qed
  next
    case (containment r)
    then show ?case
    proof (intro property_satisfaction.rule_property_containment)
      fix ob
      assume "ob \<in> Object Imod"
      then show "card (object_containments Imod ob) \<le> 1"
        by (simp add: instance_model_objects)
    next
      have "object_containments_relation Imod = {}"
        using Collect_empty_eq case_prodE empty_iff instance_model_objects mem_Collect_eq object_containments_relation.cases object_containments_relation_def
        by metis
      then show "irrefl ((object_containments_relation Imod)\<^sup>+)"
        by (simp add: irrefl_def)
    qed
  next
    case (defaultValue f v)
    then show ?case
      using property_satisfaction.rule_property_defaultValue
      by blast
  next
    case (identity c A)
    then show ?case
    proof (intro property_satisfaction.rule_property_identity)
      fix o1 o2 a
      assume "o1 \<in> Object Imod"
      then show "o1 = o2"
        by (simp add: instance_model_objects)
    qed
  next
    case (keyset r A)
    then show ?case
    proof (intro property_satisfaction.rule_property_keyset)
      fix o1 o2 p a
      assume "o1 \<in> Object Imod"
      then show "o1 = o2"
        by (simp add: instance_model_objects)
    qed
  next
    case (opposite r1 r2)
    then show ?case
    proof (intro property_satisfaction.rule_property_opposite)
      fix o1 o2 p a
      assume "o1 \<in> Object Imod"
      then show "edgeCount Imod o1 r1 o2 = edgeCount Imod o2 r2 o1"
        by (simp add: instance_model_objects)
    qed
  next
    case (readonly x)
    then show ?case
      using property_satisfaction.rule_property_readonly
      by blast
  qed
qed (simp_all add: assms)

end