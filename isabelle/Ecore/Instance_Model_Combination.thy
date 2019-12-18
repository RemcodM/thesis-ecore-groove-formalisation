theory Instance_Model_Combination
  imports 
    Main
    HOL.Transitive_Closure
    Multiplicity
    Type_Model_Combination
    Instance_Model
begin

section "Combining Instance Models"


subsection "Definitions for merging instance models"

definition imod_combine_object_class :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) instance_model \<Rightarrow> 'o \<Rightarrow> 'nt Id" where
  "imod_combine_object_class Imod1 Imod2 ob \<equiv>
    if ob \<in> Object Imod1 \<inter> Object Imod2 \<and> ObjectClass Imod1 ob = ObjectClass Imod2 ob then
      ObjectClass Imod1 ob
    else if ob \<in> Object Imod1 \<inter> Object Imod2 then
      undefined
    else if ob \<in> Object Imod1 then
      ObjectClass Imod1 ob
    else if ob \<in> Object Imod2 then
      ObjectClass Imod2 ob
    else
      undefined"

definition imod_combine_object_id :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) instance_model \<Rightarrow> 'o \<Rightarrow> 'nt" where
  "imod_combine_object_id Imod1 Imod2 ob \<equiv>
    if ob \<in> Object Imod1 \<inter> Object Imod2 \<and> ObjectId Imod1 ob = ObjectId Imod2 ob then
      ObjectId Imod1 ob
    else if ob \<in> Object Imod1 \<inter> Object Imod2 then
      undefined
    else if ob \<in> Object Imod1 then
      ObjectId Imod1 ob
    else if ob \<in> Object Imod2 then
      ObjectId Imod2 ob
    else
      undefined"

definition imod_combine_field_value :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) instance_model \<Rightarrow> ('o \<times> ('nt Id \<times> 'nt)) \<Rightarrow> ('o, 'nt) ValueDef" where
  "imod_combine_field_value Imod1 Imod2 f \<equiv>
    if fst f \<in> Object Imod1 \<inter> Object Imod2 \<and> snd f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) then
      if FieldValue Imod1 f = FieldValue Imod2 f then
        FieldValue Imod1 f
      else if FieldValue Imod1 f = unspecified then
        FieldValue Imod2 f
      else if FieldValue Imod2 f = unspecified then
        FieldValue Imod1 f
      else
        invalid
    else if fst f \<in> Object Imod1 \<and> snd f \<in> Field (Tm Imod1) then
      FieldValue Imod1 f
    else if fst f \<in> Object Imod2 \<and> snd f \<in> Field (Tm Imod2) then
      FieldValue Imod2 f
    else if fst f \<in> Object Imod1 \<union> Object Imod2 \<and> snd f \<in> Field (Tm Imod1) \<union> Field (Tm Imod2) then
      unspecified
    else
      undefined"

definition imod_combine_default_value :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) instance_model \<Rightarrow> 'nt Id \<Rightarrow> ('o, 'nt) ValueDef" where
  "imod_combine_default_value Imod1 Imod2 c \<equiv>
    if c \<in> Constant (Tm Imod1) \<inter> Constant (Tm Imod2) \<and> DefaultValue Imod1 c = DefaultValue Imod2 c then
      DefaultValue Imod1 c
    else if c \<in> Constant (Tm Imod1) \<inter> Constant (Tm Imod2) \<and> DefaultValue Imod1 c \<noteq> DefaultValue Imod2 c then
      invalid
    else if c \<in> Constant (Tm Imod1) \<and> c \<notin> Constant (Tm Imod2) then
      DefaultValue Imod1 c
    else if c \<in> Constant (Tm Imod2) \<and> c \<notin> Constant (Tm Imod1) then
      DefaultValue Imod2 c
    else
      undefined"

definition imod_combine :: "('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) instance_model \<Rightarrow> ('o, 'nt) instance_model" where
  "imod_combine Imod1 Imod2 \<equiv> \<lparr>
    Tm = tmod_combine (Tm Imod1) (Tm Imod2),
    Object = Object Imod1 \<union> Object Imod2,
    ObjectClass = imod_combine_object_class Imod1 Imod2,
    ObjectId = imod_combine_object_id Imod1 Imod2,
    FieldValue = imod_combine_field_value Imod1 Imod2,
    DefaultValue = imod_combine_default_value Imod1 Imod2
  \<rparr>"


subsection "Math laws for the combination of instance models"

subsubsection "Identity"

lemma imod_combine_object_class_identity[simp]:
  assumes structure_object_class_domain: "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectClass Imod ob = undefined"
  shows "imod_combine_object_class Imod imod_empty = ObjectClass Imod"
proof
  fix x
  show "imod_combine_object_class Imod imod_empty x = ObjectClass Imod x"
  proof-
    have x_cases: "x \<in> Object Imod \<or> x \<notin> Object Imod"
      by simp
    then show "imod_combine_object_class Imod imod_empty x = ObjectClass Imod x"
    proof (elim disjE)
      assume "x \<in> Object Imod"
      then show "imod_combine_object_class Imod imod_empty x = ObjectClass Imod x"
        unfolding imod_combine_object_class_def imod_empty_def
        by simp
    next
      assume "x \<notin> Object Imod"
      then show "imod_combine_object_class Imod imod_empty x = ObjectClass Imod x"
        unfolding imod_combine_object_class_def imod_empty_def
        using structure_object_class_domain
        by simp
    qed
  qed
qed

lemma imod_combine_object_id_identity[simp]:
  assumes structure_object_id_domain: "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectId Imod ob = undefined"
  shows "imod_combine_object_id Imod imod_empty = ObjectId Imod"
proof
  fix x
  show "imod_combine_object_id Imod imod_empty x = ObjectId Imod x"
  proof-
    have x_cases: "x \<in> Object Imod \<or> x \<notin> Object Imod"
      by simp
    then show "imod_combine_object_id Imod imod_empty x = ObjectId Imod x"
    proof (elim disjE)
      assume "x \<in> Object Imod"
      then show "imod_combine_object_id Imod imod_empty x = ObjectId Imod x"
        unfolding imod_combine_object_id_def imod_empty_def
        by simp
    next
      assume "x \<notin> Object Imod"
      then show "imod_combine_object_id Imod imod_empty x = ObjectId Imod x"
        unfolding imod_combine_object_id_def imod_empty_def
        using structure_object_id_domain
        by simp
    qed
  qed
qed

lemma imod_combine_field_value_identity[simp]:
  assumes structure_field_values_domain: "\<And>ob f. ob \<notin> Object Imod \<or> f \<notin> Field (Tm Imod) \<Longrightarrow> FieldValue Imod (ob, f) = undefined"
  shows "imod_combine_field_value Imod imod_empty = FieldValue Imod"
proof
  fix x
  show "imod_combine_field_value Imod imod_empty x = FieldValue Imod x"
  proof (induct "fst x \<in> Object Imod")
    case True
    then show ?case
    proof (induct "snd x \<in> Field (Tm Imod)")
      case True
      then show ?case
        unfolding imod_combine_field_value_def
        by simp
    next
      case False
      then have "FieldValue Imod x = undefined"
        using snd_conv structure_field_values_domain surj_pair
        by metis
      then show ?case
        unfolding imod_combine_field_value_def
        by simp
    qed
  next
    case False
    then have "FieldValue Imod x = undefined"
      using fst_conv structure_field_values_domain surj_pair
      by metis
    then show ?case
      unfolding imod_combine_field_value_def
      by simp
  qed
qed

lemma imod_combine_default_value_identity[simp]:
  assumes structure_default_values_domain: "\<And>c. c \<notin> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c = undefined"
  shows "imod_combine_default_value Imod imod_empty = DefaultValue Imod"
proof
  fix x
  show "imod_combine_default_value Imod imod_empty x = DefaultValue Imod x"
  proof-
    have x_cases: "x \<in> Constant (Tm Imod) \<or> x \<notin> Constant (Tm Imod)"
      by simp
    then show "imod_combine_default_value Imod imod_empty x = DefaultValue Imod x"
    proof (elim disjE)
      assume "x \<in> Constant (Tm Imod)"
      then show "imod_combine_default_value Imod imod_empty x = DefaultValue Imod x"
        unfolding imod_combine_default_value_def imod_empty_def
        by simp
    next
      assume "x \<notin> Constant (Tm Imod)"
      then show "imod_combine_default_value Imod imod_empty x = DefaultValue Imod x"
        unfolding imod_combine_default_value_def imod_empty_def
        using structure_default_values_domain
        by simp
    qed
  qed
qed

lemma imod_combine_identity:
  assumes structure_fieldsig_domain: "\<And>f. f \<notin> Field (Tm Imod) \<Longrightarrow> FieldSig (Tm Imod) f = undefined"
  assumes structure_consttype_domain: "\<And>c. c \<notin> Constant (Tm Imod) \<Longrightarrow> ConstType (Tm Imod) c = undefined"
  assumes structure_object_class_domain: "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectClass Imod ob = undefined"
  assumes structure_object_id_domain: "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectId Imod ob = undefined"
  assumes structure_field_values_domain: "\<And>ob f. ob \<notin> Object Imod \<or> f \<notin> Field (Tm Imod) \<Longrightarrow> FieldValue Imod (ob, f) = undefined"
  assumes structure_default_values_domain: "\<And>c. c \<notin> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c = undefined"
  shows "imod_combine Imod imod_empty = truncate Imod"
  unfolding truncate_def imod_combine_def
proof
  show "tmod_combine (Tm Imod) (Tm imod_empty) = Tm Imod \<and>
    Object Imod \<union> Object imod_empty = Object Imod \<and>
    imod_combine_object_class Imod imod_empty = ObjectClass Imod \<and> 
    imod_combine_object_id Imod imod_empty = ObjectId Imod \<and> 
    imod_combine_field_value Imod imod_empty = FieldValue Imod \<and> 
    imod_combine_default_value Imod imod_empty = DefaultValue Imod \<and> 
    () = ()"
  proof (intro conjI)
    have "tmod_combine (Tm Imod) (Tm imod_empty) = type_model.truncate (Tm Imod)"
      unfolding imod_empty_def
      using tmod_combine_identity instance_model.select_convs(1) structure_consttype_domain structure_fieldsig_domain tmod_combine_commute
      by metis
    then show "tmod_combine (Tm Imod) (Tm imod_empty) = Tm Imod"
      unfolding type_model.truncate_def
      by simp
  next
    show "imod_combine_object_class Imod imod_empty = ObjectClass Imod"
      using structure_object_class_domain imod_combine_object_class_identity
      by blast
  next
    show "imod_combine_object_id Imod imod_empty = ObjectId Imod"
      using structure_object_id_domain imod_combine_object_id_identity
      by blast
  next
    show "imod_combine_field_value Imod imod_empty = FieldValue Imod"
      using structure_field_values_domain imod_combine_field_value_identity
      by blast
  next
    show "imod_combine_default_value Imod imod_empty = DefaultValue Imod"
      using structure_default_values_domain imod_combine_default_value_identity
      by blast
  qed (simp_all)
qed

lemma imod_combine_identity_alt:
  assumes instance_model_valid: "instance_model Imod"
  shows "imod_combine Imod imod_empty = truncate Imod"
proof (intro imod_combine_identity)
  show "\<And>f. f \<notin> type_model.Field (Tm Imod) \<Longrightarrow> FieldSig (Tm Imod) f = undefined"
    using instance_model_valid instance_model.validity_type_model_consistent type_model.structure_fieldsig_domain
    by blast
next
  show "\<And>c. c \<notin> Constant (Tm Imod) \<Longrightarrow> ConstType (Tm Imod) c = undefined"
    using instance_model_valid instance_model.validity_type_model_consistent type_model.structure_consttype_domain
    by blast
next
  show "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectClass Imod ob = undefined"
    using instance_model_valid instance_model.structure_object_class_domain
    by metis
next
  show "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectId Imod ob = undefined"
    using instance_model_valid instance_model.structure_object_id_domain
    by metis
next
  show "\<And>ob f. ob \<notin> Object Imod \<or> f \<notin> type_model.Field (Tm Imod) \<Longrightarrow> FieldValue Imod (ob, f) = undefined"
    using instance_model_valid instance_model.structure_field_values_domain
    by metis
next
  show "\<And>c. c \<notin> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c = undefined"
    using instance_model_valid instance_model.structure_default_values_domain
    by blast
qed

subsubsection "Commutativity"

lemma imod_combine_object_class_commute[simp]:
  shows "imod_combine_object_class Imod1 Imod2 = imod_combine_object_class Imod2 Imod1"
proof
  fix x
  show "imod_combine_object_class Imod1 Imod2 x = imod_combine_object_class Imod2 Imod1 x"
    unfolding imod_combine_object_class_def
    by simp
qed

lemma imod_combine_object_id_commute[simp]:
  shows "imod_combine_object_id Imod1 Imod2 = imod_combine_object_id Imod2 Imod1"
proof
  fix x
  show "imod_combine_object_id Imod1 Imod2 x = imod_combine_object_id Imod2 Imod1 x"
    unfolding imod_combine_object_id_def
    by simp
qed

lemma imod_combine_field_value_commute[simp]: 
  shows "imod_combine_field_value Imod1 Imod2 = imod_combine_field_value Imod2 Imod1"
proof
  fix x :: "'a \<times> ('b Id \<times> 'b)"
  have imod1_object_cases: "fst x \<in> Object Imod1 \<or> fst x \<notin> Object Imod1"
    by simp
  have tmod1_field_cases: "snd x \<in> Field (Tm Imod1) \<or> snd x \<notin> Field (Tm Imod1)"
    by simp
  have imod2_object_cases: "fst x \<in> Object Imod2 \<or> fst x \<notin> Object Imod2"
    by simp
  have tmod2_field_cases: "snd x \<in> Field (Tm Imod2) \<or> snd x \<notin> Field (Tm Imod2)"
    by simp
  show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
    using imod1_object_cases tmod1_field_cases imod2_object_cases tmod2_field_cases
  proof (elim disjE)
    assume imod1_present: "fst x \<in> Object Imod1"
    assume tmod1_present: "snd x \<in> Field (Tm Imod1)"
    assume imod2_present: "fst x \<in> Object Imod2"
    assume tmod2_present: "snd x \<in> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_present tmod1_present imod2_present tmod2_present
      by fastforce
  next
    assume imod1_present: "fst x \<in> Object Imod1"
    assume tmod1_present: "snd x \<in> Field (Tm Imod1)"
    assume imod2_present: "fst x \<in> Object Imod2"
    assume tmod2_unpresent: "snd x \<notin> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_present tmod1_present imod2_present tmod2_unpresent
      by simp
  next
    assume imod1_present: "fst x \<in> Object Imod1"
    assume tmod1_present: "snd x \<in> Field (Tm Imod1)"
    assume imod2_unpresent: "fst x \<notin> Object Imod2"
    assume tmod2_present: "snd x \<in> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_present tmod1_present imod2_unpresent tmod2_present
      by simp
  next
    assume imod1_present: "fst x \<in> Object Imod1"
    assume tmod1_present: "snd x \<in> Field (Tm Imod1)"
    assume imod2_unpresent: "fst x \<notin> Object Imod2"
    assume tmod2_unpresent: "snd x \<notin> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_present tmod1_present imod2_unpresent tmod2_unpresent
      by simp
  next
    assume imod1_present: "fst x \<in> Object Imod1"
    assume tmod1_unpresent: "snd x \<notin> Field (Tm Imod1)"
    assume imod2_present: "fst x \<in> Object Imod2"
    assume tmod2_present: "snd x \<in> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_present tmod1_unpresent imod2_present tmod2_present
      by simp
  next
    assume imod1_present: "fst x \<in> Object Imod1"
    assume tmod1_unpresent: "snd x \<notin> Field (Tm Imod1)"
    assume imod2_present: "fst x \<in> Object Imod2"
    assume tmod2_unpresent: "snd x \<notin> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_present tmod1_unpresent imod2_present tmod2_unpresent
      by simp
  next
    assume imod1_present: "fst x \<in> Object Imod1"
    assume tmod1_unpresent: "snd x \<notin> Field (Tm Imod1)"
    assume imod2_unpresent: "fst x \<notin> Object Imod2"
    assume tmod2_present: "snd x \<in> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_present tmod1_unpresent imod2_unpresent tmod2_present
      by simp
  next
    assume imod1_present: "fst x \<in> Object Imod1"
    assume tmod1_unpresent: "snd x \<notin> Field (Tm Imod1)"
    assume imod2_unpresent: "fst x \<notin> Object Imod2"
    assume tmod2_unpresent: "snd x \<notin> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_present tmod1_unpresent imod2_unpresent tmod2_unpresent
      by simp
  next
    assume imod1_unpresent: "fst x \<notin> Object Imod1"
    assume tmod1_present: "snd x \<in> Field (Tm Imod1)"
    assume imod2_present: "fst x \<in> Object Imod2"
    assume tmod2_present: "snd x \<in> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_unpresent tmod1_present imod2_present tmod2_present
      by simp
  next
    assume imod1_unpresent: "fst x \<notin> Object Imod1"
    assume tmod1_present: "snd x \<in> Field (Tm Imod1)"
    assume imod2_present: "fst x \<in> Object Imod2"
    assume tmod2_unpresent: "snd x \<notin> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_unpresent tmod1_present imod2_present tmod2_unpresent
      by simp
  next
    assume imod1_unpresent: "fst x \<notin> Object Imod1"
    assume tmod1_present: "snd x \<in> Field (Tm Imod1)"
    assume imod2_unpresent: "fst x \<notin> Object Imod2"
    assume tmod2_present: "snd x \<in> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_unpresent tmod1_present imod2_unpresent tmod2_present
      by simp
  next
    assume imod1_unpresent: "fst x \<notin> Object Imod1"
    assume tmod1_present: "snd x \<in> Field (Tm Imod1)"
    assume imod2_unpresent: "fst x \<notin> Object Imod2"
    assume tmod2_unpresent: "snd x \<notin> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_unpresent tmod1_present imod2_unpresent tmod2_unpresent
      by simp
  next
    assume imod1_unpresent: "fst x \<notin> Object Imod1"
    assume tmod1_unpresent: "snd x \<notin> Field (Tm Imod1)"
    assume imod2_present: "fst x \<in> Object Imod2"
    assume tmod2_present: "snd x \<in> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_unpresent tmod1_unpresent imod2_present tmod2_present
      by simp
  next
    assume imod1_unpresent: "fst x \<notin> Object Imod1"
    assume tmod1_unpresent: "snd x \<notin> Field (Tm Imod1)"
    assume imod2_present: "fst x \<in> Object Imod2"
    assume tmod2_unpresent: "snd x \<notin> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_unpresent tmod1_unpresent imod2_present tmod2_unpresent
      by simp
  next
    assume imod1_unpresent: "fst x \<notin> Object Imod1"
    assume tmod1_unpresent: "snd x \<notin> Field (Tm Imod1)"
    assume imod2_unpresent: "fst x \<notin> Object Imod2"
    assume tmod2_present: "snd x \<in> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_unpresent tmod1_unpresent imod2_unpresent tmod2_present
      by simp
  next
    assume imod1_unpresent: "fst x \<notin> Object Imod1"
    assume tmod1_unpresent: "snd x \<notin> Field (Tm Imod1)"
    assume imod2_unpresent: "fst x \<notin> Object Imod2"
    assume tmod2_unpresent: "snd x \<notin> Field (Tm Imod2)"
    show "imod_combine_field_value Imod1 Imod2 x = imod_combine_field_value Imod2 Imod1 x"
      unfolding imod_combine_field_value_def
      using imod1_unpresent tmod1_unpresent imod2_unpresent tmod2_unpresent
      by simp
  qed
qed

lemma imod_combine_default_value_commute[simp]: 
  shows "imod_combine_default_value Imod1 Imod2 = imod_combine_default_value Imod2 Imod1"
proof
  fix c
  have "c \<in> Constant (Tm Imod1) \<inter> Constant (Tm Imod2) \<or> c \<in> Constant (Tm Imod1) - Constant (Tm Imod2) \<or>
    c \<in> Constant (Tm Imod2) - Constant (Tm Imod1) \<or> c \<notin> Constant (Tm Imod1) \<union> Constant (Tm Imod2)"
    by blast
  then show "imod_combine_default_value Imod1 Imod2 c = imod_combine_default_value Imod2 Imod1 c"
  proof (elim disjE)
    assume "c \<in> Constant (Tm Imod1) \<inter> Constant (Tm Imod2)"
    then show ?thesis
      unfolding imod_combine_default_value_def
      by simp
  next
    assume "c \<in> Constant (Tm Imod1) - Constant (Tm Imod2)"
    then show ?thesis
      unfolding imod_combine_default_value_def
      by simp
  next
    assume "c \<in> Constant (Tm Imod2) - Constant (Tm Imod1)"
    then show ?thesis
      unfolding imod_combine_default_value_def
      by simp
  next
    assume "c \<notin> Constant (Tm Imod1) \<union> Constant (Tm Imod2)"
    then show ?thesis
      unfolding imod_combine_default_value_def
      by simp
  qed
qed

lemma imod_combine_commute: "imod_combine Imod1 Imod2 = imod_combine Imod2 Imod1"
  unfolding imod_combine_def
proof
  show "tmod_combine (Tm Imod1) (Tm Imod2) = tmod_combine (Tm Imod2) (Tm Imod1) \<and>
    Object Imod1 \<union> Object Imod2 = Object Imod2 \<union> Object Imod1 \<and>
    imod_combine_object_class Imod1 Imod2 = imod_combine_object_class Imod2 Imod1 \<and>
    imod_combine_object_id Imod1 Imod2 = imod_combine_object_id Imod2 Imod1 \<and> 
    imod_combine_field_value Imod1 Imod2 = imod_combine_field_value Imod2 Imod1 \<and> 
    imod_combine_default_value Imod1 Imod2 = imod_combine_default_value Imod2 Imod1 \<and> 
    () = ()"
  proof (intro conjI)
    show "tmod_combine (Tm Imod1) (Tm Imod2) = tmod_combine (Tm Imod2) (Tm Imod1)"
      using tmod_combine_commute
      by blast
  qed (simp_all add: Un_commute)
qed

subsubsection "Idempotence"

lemma imod_combine_object_class_idemp[simp]:
  assumes structure_object_class_domain: "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectClass Imod ob = undefined"
  shows "imod_combine_object_class Imod Imod = ObjectClass Imod"
proof
  fix x
  show "imod_combine_object_class Imod Imod x = ObjectClass Imod x"
    unfolding imod_combine_object_class_def
    by (simp add: structure_object_class_domain)
qed

lemma imod_combine_object_id_idemp[simp]:
  assumes structure_object_id_domain: "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectId Imod ob = undefined"
  shows "imod_combine_object_id Imod Imod = ObjectId Imod"
proof
  fix x
  show "imod_combine_object_id Imod Imod x = ObjectId Imod x"
    unfolding imod_combine_object_id_def
    by (simp add: structure_object_id_domain)
qed

lemma imod_combine_field_value_idemp[simp]:
  assumes structure_field_values_domain: "\<And>ob f. ob \<notin> Object Imod \<or> f \<notin> Field (Tm Imod) \<Longrightarrow> FieldValue Imod (ob, f) = undefined"
  shows "imod_combine_field_value Imod Imod = FieldValue Imod"
proof
  fix x
  show "imod_combine_field_value Imod Imod x = FieldValue Imod x"
  proof (induct "fst x \<in> Object Imod")
    case True
    then show ?case
    proof (induct "snd x \<in> Field (Tm Imod)")
      case True
      then show ?case
        unfolding imod_combine_field_value_def
        by simp
    next
      case False
      then have "FieldValue Imod x = undefined"
        using snd_conv structure_field_values_domain surj_pair
        by metis
      then show ?case
        unfolding imod_combine_field_value_def
        by simp
    qed
  next
    case False
    then have "FieldValue Imod x = undefined"
      using fst_conv structure_field_values_domain surj_pair
      by metis
    then show ?case
      unfolding imod_combine_field_value_def
      by simp
  qed
qed

lemma imod_combine_default_value_idemp[simp]:
  assumes structure_default_values_wellformed: "\<And>c. c \<in> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c \<in> Value Imod"
  assumes structure_default_values_domain: "\<And>c. c \<notin> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c = undefined"
  shows "imod_combine_default_value Imod Imod = DefaultValue Imod"
proof
  fix c
  have "c \<in> Constant (Tm Imod) \<or> c \<notin> Constant (Tm Imod)"
    by simp
  then show "imod_combine_default_value Imod Imod c = DefaultValue Imod c"
  proof (elim disjE)
    assume c_in_tmod: "c \<in> Constant (Tm Imod)"
    then show ?thesis
      unfolding imod_combine_default_value_def
      by simp
  next
    assume "c \<notin> Constant (Tm Imod)"
    then show ?thesis
      unfolding imod_combine_default_value_def
      by (simp add: structure_default_values_domain)
  qed
qed

lemma imod_combine_idemp:
  assumes structure_fieldsig_domain: "\<And>f. f \<notin> Field (Tm Imod) \<Longrightarrow> FieldSig (Tm Imod) f = undefined"
  assumes structure_consttype_domain: "\<And>c. c \<notin> Constant (Tm Imod) \<Longrightarrow> ConstType (Tm Imod) c = undefined"
  assumes structure_object_class_domain: "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectClass Imod ob = undefined"
  assumes structure_object_id_domain: "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectId Imod ob = undefined"
  assumes structure_field_values_domain: "\<And>ob f. ob \<notin> Object Imod \<or> f \<notin> Field (Tm Imod) \<Longrightarrow> FieldValue Imod (ob, f) = undefined"
  assumes structure_default_values_wellformed: "\<And>c. c \<in> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c \<in> Value Imod"
  assumes structure_default_values_domain: "\<And>c. c \<notin> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c = undefined"
  shows "imod_combine Imod Imod = truncate Imod"
  unfolding imod_combine_def truncate_def
proof
  show "tmod_combine (Tm Imod) (Tm Imod) = Tm Imod \<and>
    Object Imod \<union> Object Imod = Object Imod \<and> 
    imod_combine_object_class Imod Imod = ObjectClass Imod \<and> 
    imod_combine_object_id Imod Imod = ObjectId Imod \<and> 
    imod_combine_field_value Imod Imod = FieldValue Imod \<and> 
    imod_combine_default_value Imod Imod = DefaultValue Imod \<and> 
    () = ()"
  proof (intro conjI)
    have "tmod_combine (Tm Imod) (Tm Imod) = type_model.truncate (Tm Imod)"
      using tmod_combine_idemp structure_fieldsig_domain structure_consttype_domain
      by blast
    then show "tmod_combine (Tm Imod) (Tm Imod) = Tm Imod"
      unfolding type_model.truncate_def
      by simp
  next
    show "imod_combine_field_value Imod Imod = FieldValue Imod"
      using imod_combine_field_value_idemp structure_field_values_domain
      by blast
  qed (simp_all add: assms)
qed

lemma imod_combine_idemp_alt:
  assumes "instance_model Imod"
  shows "imod_combine Imod Imod = truncate Imod"
proof (intro imod_combine_idemp)
  show "\<And>f. f \<notin> Field (Tm Imod) \<Longrightarrow> FieldSig (Tm Imod) f = undefined"
    by (simp add: assms instance_model.validity_type_model_consistent type_model.structure_fieldsig_domain)
next
  show "\<And>c. c \<notin> Constant (Tm Imod) \<Longrightarrow> ConstType (Tm Imod) c = undefined"
    by (simp add: assms instance_model.validity_type_model_consistent type_model.structure_consttype_domain)
next
  show "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectClass Imod ob = undefined"
    using assms instance_model.structure_object_class_domain
    by metis
next
  show "\<And>ob. ob \<notin> Object Imod \<Longrightarrow> ObjectId Imod ob = undefined"
    using assms instance_model.structure_object_id_domain
    by metis
next
  show "\<And>ob f. ob \<notin> Object Imod \<or> f \<notin> Field (Tm Imod) \<Longrightarrow> FieldValue Imod (ob, f) = undefined"
    using assms instance_model.structure_field_values_domain
    by metis
next
  show "\<And>c. c \<in> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c \<in> Value Imod"
    using assms instance_model.structure_default_values_wellformed
    by blast
next
  show "\<And>c. c \<notin> Constant (Tm Imod) \<Longrightarrow> DefaultValue Imod c = undefined"
    using assms instance_model.structure_default_values_domain
    by blast
qed

subsubsection "Associativity"

lemma imod_combine_object_class_assoc[simp]:
  shows "imod_combine_object_class (imod_combine Imod1 Imod2) Imod3 = imod_combine_object_class Imod1 (imod_combine Imod2 Imod3)"
proof
  fix x
  show "imod_combine_object_class (imod_combine Imod1 Imod2) Imod3 x = imod_combine_object_class Imod1 (imod_combine Imod2 Imod3) x"
    unfolding imod_combine_def imod_combine_object_class_def
    by simp
qed

lemma imod_combine_object_id_assoc[simp]:
  shows "imod_combine_object_id (imod_combine Imod1 Imod2) Imod3 = imod_combine_object_id Imod1 (imod_combine Imod2 Imod3)"
proof
  fix x
  show "imod_combine_object_id (imod_combine Imod1 Imod2) Imod3 x = imod_combine_object_id Imod1 (imod_combine Imod2 Imod3) x"
    unfolding imod_combine_def imod_combine_object_id_def
    by simp
qed

lemma imod_combine_field_value_assoc[simp]:
  shows "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) = imod_combine_field_value (imod_combine Imod1 Imod2) Imod3"
proof-
  have "\<And>ob f. imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f)"
  proof-
    fix ob f
    have ob_imod1_cases: "ob \<in> Object Imod1 \<or> ob \<notin> Object Imod1"
      by simp
    have ob_imod2_cases: "ob \<in> Object Imod2 \<or> ob \<notin> Object Imod2"
      by simp
    have ob_imod3_cases: "ob \<in> Object Imod3 \<or> ob \<notin> Object Imod3"
      by simp
    have f_imod1_cases: "f \<in> Field (Tm Imod1) \<or> f \<notin> Field (Tm Imod1)"
      by simp
    have f_imod2_cases: "f \<in> Field (Tm Imod2) \<or> f \<notin> Field (Tm Imod2)"
      by simp
    have f_imod3_cases: "f \<in> Field (Tm Imod3) \<or> f \<notin> Field (Tm Imod3)"
      by simp
    have value_imod1_cases: "FieldValue Imod1 (ob, f) = unspecified \<or> FieldValue Imod1 (ob, f) \<noteq> unspecified"
      by simp
    have value_imod2_cases: "FieldValue Imod2 (ob, f) = unspecified \<or> FieldValue Imod2 (ob, f) \<noteq> unspecified"
      by simp
    have value_imod3_cases: "FieldValue Imod3 (ob, f) = unspecified \<or> FieldValue Imod3 (ob, f) \<noteq> unspecified"
      by simp
    show "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f)"
      using ob_imod1_cases ob_imod2_cases ob_imod3_cases
    proof (elim disjE)
      assume ob_imod1_present: "ob \<in> Object Imod1"
      then have ob_imod12_present: "ob \<in> Object (imod_combine Imod1 Imod2)"
        by (simp add: imod_combine_def)
      assume ob_imod2_present: "ob \<in> Object Imod2"
      then have ob_imod23_present: "ob \<in> Object (imod_combine Imod2 Imod3)"
        by (simp add: imod_combine_def)
      assume ob_imod3_present: "ob \<in> Object Imod3"
      show ?thesis
        using f_imod1_cases f_imod2_cases f_imod3_cases
      proof (elim disjE)
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        show ?thesis
          using value_imod1_cases value_imod2_cases value_imod3_cases
        proof (elim disjE)
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod3_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod1_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod1_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod3_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod2 (ob, f) = FieldValue Imod3 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod2_present value_imod1_unspecified)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod12_present ob_imod12_present
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod2_present ob_imod2_present
              by simp
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified)
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod2_present value_imod1_unspecified)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod12_present f_imod3_present ob_imod12_present ob_imod3_present value_imod2_specified value_imod3_specified
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod2_present f_imod3_present ob_imod2_present ob_imod3_present value_imod2_specified value_imod3_specified
              by simp
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = invalid"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified)
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified value_imod3_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod3 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod12_present ob_imod12_present
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod1_present ob_imod1_present
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod12_present f_imod3_present ob_imod12_present ob_imod3_present value_imod1_specified value_imod3_specified
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod23_present ob_imod1_present ob_imod23_present value_imod1_specified value_imod3_specified
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          show ?thesis
          proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod2_present ob_imod2_present
              by simp
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod2_present value_imod3_unspecified)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod1_present ob_imod1_present
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod2_present ob_imod1_present ob_imod2_present value_imod1_specified value_imod2_specified
              by simp
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = invalid"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod2_present value_imod3_unspecified)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod23_present ob_imod1_present ob_imod23_present value_imod1_specified value_imod2_specified
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)")
            case True
            then show ?case
            proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod3 (ob, f)")
              case True
              have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
                unfolding imod_combine_field_value_def
                using True.prems f_imod1_present ob_imod1_present
                by simp
              then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
                by (simp add: imod_combine_def)
              then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
                unfolding imod_combine_field_value_def
                using True.hyps f_imod12_present ob_imod12_present
                by simp
              have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
                unfolding imod_combine_field_value_def
                using True.hyps True.prems f_imod2_present ob_imod2_present
                by simp
              then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
                by (simp add: imod_combine_def)
              then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
                unfolding imod_combine_field_value_def
                using True.prems f_imod1_present ob_imod1_present
                by simp
              then show ?thesis
                using imod12_imod3_def
                by simp
            next
              case False
              have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
                unfolding imod_combine_field_value_def
                using True.hyps f_imod1_present ob_imod1_present
                by simp
              then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
                by (simp add: imod_combine_def)
              then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
                unfolding imod_combine_field_value_def
                using False.hyps f_imod12_present f_imod3_present ob_imod12_present ob_imod3_present value_imod1_specified value_imod3_specified
                by simp
              have "imod_combine_field_value Imod2 Imod3 (ob, f) = invalid"
                unfolding imod_combine_field_value_def
                using False.hyps True.hyps f_imod2_present f_imod3_present ob_imod2_present ob_imod3_present value_imod2_specified value_imod3_specified
                by simp
              then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = invalid"
                by (simp add: imod_combine_def)
              then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
                unfolding imod_combine_field_value_def
                by (simp add: f_imod23_present ob_imod23_present)
              then show ?thesis
                using imod12_imod3_def
                by simp
            qed
          next
            case False
            then show ?case
            proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod3 (ob, f)")
              case True
              have "imod_combine_field_value Imod1 Imod2 (ob, f) = invalid"
                unfolding imod_combine_field_value_def
                using True.prems f_imod1_present f_imod2_present ob_imod1_present ob_imod2_present value_imod1_specified value_imod2_specified
                by simp
              then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = invalid"
                by (simp add: imod_combine_def)
              then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
                unfolding imod_combine_field_value_def
                by (simp add: f_imod12_present ob_imod12_present)
              have "imod_combine_field_value Imod2 Imod3 (ob, f) = invalid"
                unfolding imod_combine_field_value_def
                using True.hyps True.prems f_imod2_present f_imod3_present ob_imod2_present ob_imod3_present value_imod2_specified value_imod3_specified
                by simp
              then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = invalid"
                by (simp add: imod_combine_def)
              then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
                unfolding imod_combine_field_value_def
                by (simp add: f_imod23_present ob_imod23_present)
              then show ?thesis
                using imod12_imod3_def
                by simp
            next
              case False
              then show ?thesis
              proof (induct "FieldValue Imod2 (ob, f) = FieldValue Imod3 (ob, f)")
                case True
                have "imod_combine_field_value Imod1 Imod2 (ob, f) = invalid"
                  unfolding imod_combine_field_value_def
                  using False.prems f_imod1_present f_imod2_present ob_imod1_present ob_imod2_present value_imod1_specified value_imod2_specified
                  by simp
                then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = invalid"
                  by (simp add: imod_combine_def)
                then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
                  unfolding imod_combine_field_value_def
                  by (simp add: f_imod12_present ob_imod12_present)
                have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
                  unfolding imod_combine_field_value_def
                  using True.hyps f_imod2_present ob_imod2_present
                  by simp
                then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
                  by (simp add: imod_combine_def)
                then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
                  unfolding imod_combine_field_value_def
                  using False.prems f_imod1_present f_imod23_present ob_imod1_present ob_imod23_present value_imod1_specified value_imod2_specified
                  by simp
                then show ?thesis
                  using imod12_imod3_def
                  by simp
              next
                case False
                have "imod_combine_field_value Imod1 Imod2 (ob, f) = invalid"
                  unfolding imod_combine_field_value_def
                  using False.prems f_imod1_present f_imod2_present ob_imod1_present ob_imod2_present value_imod1_specified value_imod2_specified
                  by simp
                then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = invalid"
                  by (simp add: imod_combine_def)
                then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
                  unfolding imod_combine_field_value_def
                  by (simp add: f_imod12_present ob_imod12_present)
                have "imod_combine_field_value Imod2 Imod3 (ob, f) = invalid"
                  unfolding imod_combine_field_value_def
                  using False.hyps f_imod2_present f_imod3_present ob_imod2_present ob_imod3_present value_imod2_specified value_imod3_specified
                  by simp
                then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = invalid"
                  by (simp add: imod_combine_def)
                then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
                  unfolding imod_combine_field_value_def
                  using False.prems f_imod1_present f_imod23_present ob_imod1_present ob_imod23_present value_imod1_specified value_imod2_specified
                  by simp
                then show ?thesis
                  using imod12_imod3_def
                  by simp
              qed
            qed
          qed
        qed
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        show ?thesis
          using value_imod1_cases value_imod2_cases
        proof (elim disjE)
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod1_unspecified value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified value_imod2_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod1_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod2_present ob_imod2_present
              by simp
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_present)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod1_present ob_imod1_present
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod2_present ob_imod1_present ob_imod2_present value_imod1_specified value_imod2_specified
              by simp
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = invalid"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_present)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod23_present ob_imod1_present ob_imod23_present value_imod1_specified value_imod2_specified
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        qed
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        show ?thesis
          using value_imod1_cases value_imod3_cases
        proof (elim disjE)
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_unpresent f_imod3_present ob_imod3_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified value_imod3_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod1_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_unpresent f_imod3_present ob_imod3_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_unpresent f_imod3_present ob_imod3_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod3_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod3 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_present)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod12_present ob_imod12_present
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_unpresent f_imod3_present ob_imod3_present)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod1_present ob_imod1_present
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_present)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod12_present f_imod3_present ob_imod12_present ob_imod3_present value_imod1_specified value_imod3_specified
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_unpresent f_imod3_present ob_imod3_present)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod23_present ob_imod1_present ob_imod23_present value_imod1_specified value_imod3_specified
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        qed
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        show ?thesis
          using value_imod2_cases value_imod3_cases
        proof (elim disjE)
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod2_present ob_imod2_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified value_imod3_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod2_present ob_imod2_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod2_present ob_imod2_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod3_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod2 (ob, f) = FieldValue Imod3 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_unpresent f_imod2_present ob_imod2_present)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod12_present ob_imod12_present
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod2_present ob_imod2_present
              by simp
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_unpresent f_imod2_present ob_imod2_present)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod12_present f_imod3_present ob_imod12_present ob_imod3_present value_imod2_specified value_imod3_specified
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod2_present f_imod3_present ob_imod2_present ob_imod3_present value_imod2_specified value_imod3_specified
              by simp
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = invalid"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        qed
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
        have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present f_imod23_unpresent ob_imod1_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_present imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod2_present ob_imod2_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_present)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: f_imod1_unpresent imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_unpresent f_imod3_present ob_imod3_present)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_unpresent f_imod3_present ob_imod3_present)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: f_imod1_unpresent imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
        have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_unpresent f_imod3_unpresent)
        have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_unpresent)
        then show ?thesis
          using imod12_imod3_def
          by simp
      qed
    next
      assume ob_imod1_present: "ob \<in> Object Imod1"
      then have ob_imod12_present: "ob \<in> Object (imod_combine Imod1 Imod2)"
        by (simp add: imod_combine_def)
      assume ob_imod2_present: "ob \<in> Object Imod2"
      then have ob_imod23_present: "ob \<in> Object (imod_combine Imod2 Imod3)"
        by (simp add: imod_combine_def)
      assume ob_imod3_unpresent: "ob \<notin> Object Imod3"
      show ?thesis
        using f_imod1_cases f_imod2_cases f_imod3_cases
      proof (elim disjE)
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        show ?thesis
          using value_imod1_cases value_imod2_cases
        proof (elim disjE)
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod1_unspecified value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod1_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod2_present ob_imod2_present
              by simp
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod1_present ob_imod1_present
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod2_present ob_imod1_present ob_imod2_present value_imod1_specified value_imod2_specified
              by simp
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = invalid"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod23_present ob_imod1_present ob_imod23_present value_imod1_specified value_imod2_specified
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        qed
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        show ?thesis
          using value_imod1_cases value_imod2_cases
        proof (elim disjE)
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod1_unspecified value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod1_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod2_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod2_present ob_imod2_present
              by simp
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod1_present ob_imod1_present
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod2_present ob_imod1_present ob_imod2_present value_imod1_specified value_imod2_specified
              by simp
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = invalid"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod23_present ob_imod1_present ob_imod23_present value_imod1_specified value_imod2_specified
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        qed
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_unpresent f_imod3_present ob_imod2_present ob_imod3_unpresent)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = unspecified"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present ob_imod1_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod2_present ob_imod2_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
        have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present f_imod23_unpresent ob_imod1_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_present imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod2_present ob_imod2_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: f_imod1_unpresent imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_unpresent f_imod3_present ob_imod12_present ob_imod3_unpresent)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_unpresent f_imod3_present ob_imod2_present ob_imod3_unpresent)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = unspecified"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: f_imod1_unpresent imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
        have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_unpresent f_imod3_unpresent)
        have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_unpresent)
        then show ?thesis
          using imod12_imod3_def
          by simp
      qed
    next
      assume ob_imod1_present: "ob \<in> Object Imod1"
      then have ob_imod12_present: "ob \<in> Object (imod_combine Imod1 Imod2)"
        by (simp add: imod_combine_def)
      assume ob_imod2_unpresent: "ob \<notin> Object Imod2"
      assume ob_imod3_present: "ob \<in> Object Imod3"
      then have ob_imod23_present: "ob \<in> Object (imod_combine Imod2 Imod3)"
        by (simp add: imod_combine_def)
      show ?thesis
        using f_imod1_cases f_imod2_cases f_imod3_cases
      proof (elim disjE)
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        show ?thesis
          using value_imod1_cases value_imod3_cases
        proof (elim disjE)
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod1_unspecified value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified value_imod3_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod1_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod3_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod3 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod12_present ob_imod12_present
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod1_present ob_imod1_present
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod12_present f_imod3_present ob_imod12_present ob_imod3_present value_imod1_specified value_imod3_specified
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod23_present ob_imod1_present ob_imod23_present value_imod1_specified value_imod3_specified
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        qed
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_unpresent ob_imod3_present)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = unspecified"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present ob_imod1_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        show ?thesis
          using value_imod1_cases value_imod3_cases
        proof (elim disjE)
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod1_unspecified value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified value_imod3_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_unspecified: "FieldValue Imod1 (ob, f) = unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod1_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod23_present value_imod1_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present ob_imod1_present value_imod3_unspecified)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod1_specified: "FieldValue Imod1 (ob, f) \<noteq> unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod3 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod12_present ob_imod12_present
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod1_present ob_imod1_present
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod12_present f_imod3_present ob_imod12_present ob_imod3_present value_imod1_specified value_imod3_specified
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod1_present f_imod23_present ob_imod1_present ob_imod23_present value_imod1_specified value_imod3_specified
              by simp
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        qed
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod2_present ob_imod1_present ob_imod2_unpresent)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = unspecified"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod3_present ob_imod3_present)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
        have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present f_imod23_unpresent ob_imod1_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_present imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod2_present ob_imod1_present ob_imod2_unpresent)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = unspecified"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_unpresent ob_imod3_present)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = unspecified"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: f_imod1_unpresent imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_unpresent f_imod3_present ob_imod3_present)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_unpresent f_imod3_present ob_imod3_present)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_present ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: f_imod1_unpresent imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
        have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_unpresent f_imod3_unpresent)
        have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_unpresent)
        then show ?thesis
          using imod12_imod3_def
          by simp
      qed
    next
      assume ob_imod1_unpresent: "ob \<notin> Object Imod1"
      assume ob_imod2_present: "ob \<in> Object Imod2"
      then have ob_imod12_present: "ob \<in> Object (imod_combine Imod1 Imod2)"
        by (simp add: imod_combine_def)
      assume ob_imod3_present: "ob \<in> Object Imod3"
      then have ob_imod23_present: "ob \<in> Object (imod_combine Imod2 Imod3)"
        by (simp add: imod_combine_def)
      show ?thesis
        using f_imod1_cases f_imod2_cases f_imod3_cases
      proof (elim disjE)
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        show ?thesis
          using value_imod2_cases value_imod3_cases
        proof (elim disjE)
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified value_imod3_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod3_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod2 (ob, f) = FieldValue Imod3 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod12_present ob_imod12_present
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod2_present ob_imod2_present
              by simp
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod12_present f_imod3_present ob_imod12_present ob_imod3_present value_imod2_specified value_imod3_specified
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod2_present f_imod3_present ob_imod2_present ob_imod3_present value_imod2_specified value_imod3_specified
              by simp
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = invalid"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        qed
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_present)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_unpresent ob_imod2_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = unspecified"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod3_present ob_imod3_present)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_unpresent f_imod3_present ob_imod3_present)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        show ?thesis
          using value_imod2_cases value_imod3_cases
        proof (elim disjE)
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified value_imod3_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod2_unspecified: "FieldValue Imod2 (ob, f) = unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod3_present ob_imod3_present value_imod2_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          assume value_imod3_unspecified: "FieldValue Imod3 (ob, f) = unspecified"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present value_imod3_unspecified)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present ob_imod2_present value_imod3_unspecified)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume value_imod2_specified: "FieldValue Imod2 (ob, f) \<noteq> unspecified"
          assume value_imod3_specified: "FieldValue Imod3 (ob, f) \<noteq> unspecified"
          show ?thesis
          proof (induct "FieldValue Imod2 (ob, f) = FieldValue Imod3 (ob, f)")
            case True
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod12_present ob_imod12_present
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_imod2_present ob_imod2_present
              by simp
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
            then show ?thesis
              using imod12_imod3_def
              by simp
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
            then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
              by (simp add: imod_combine_def)
            then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod12_present f_imod3_present ob_imod12_present ob_imod3_present value_imod2_specified value_imod3_specified
              by simp
            have "imod_combine_field_value Imod2 Imod3 (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              using False.hyps f_imod2_present f_imod3_present ob_imod2_present ob_imod3_present value_imod2_specified value_imod3_specified
              by simp
            then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = invalid"
              by (simp add: imod_combine_def)
            then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = invalid"
              unfolding imod_combine_field_value_def
              by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
            then show ?thesis
              using imod12_imod3_def
              by simp
          qed
        qed
      next
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_unpresent ob_imod2_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = unspecified"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
        have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present f_imod23_unpresent ob_imod1_unpresent ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_present imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_present)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_present)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: f_imod1_unpresent imod_combine_def tmod_combine_def)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_unpresent f_imod3_present ob_imod3_present)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_unpresent f_imod3_present ob_imod3_present)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: f_imod1_unpresent imod_combine_def tmod_combine_def)
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
        have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_unpresent f_imod3_unpresent)
        have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_unpresent f_imod23_unpresent)
        then show ?thesis
          using imod12_imod3_def
          by simp
      qed
    next
      assume ob_imod1_present: "ob \<in> Object Imod1"
      then have ob_imod12_present: "ob \<in> Object (imod_combine Imod1 Imod2)"
        by (simp add: imod_combine_def)
      assume ob_imod2_unpresent: "ob \<notin> Object Imod2"
      assume ob_imod3_unpresent: "ob \<notin> Object Imod3"
      have ob_imod23_unpresent: "ob \<notin> Object (imod_combine Imod2 Imod3)"
        by (simp add: imod_combine_def ob_imod2_unpresent ob_imod3_unpresent)
      show ?thesis
        using f_imod1_cases
      proof (elim disjE)
        assume f_imod1_present: "f \<in> Field (Tm Imod1)"
        then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def tmod_combine_def)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present ob_imod1_present ob_imod2_unpresent)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod1 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
        have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod1_present ob_imod1_present ob_imod23_unpresent)
        then show ?thesis
          using imod12_imod3_def
          by simp
      next
        assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
        show ?thesis
          using f_imod2_cases f_imod3_cases
        proof (elim disjE)
          assume f_imod2_present: "f \<in> Field (Tm Imod2)"
          then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: imod_combine_def tmod_combine_def)
          assume f_imod3_present: "f \<in> Field (Tm Imod3)"
          then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: imod_combine_def tmod_combine_def)
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod2_present ob_imod1_present ob_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = unspecified"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod23_present ob_imod1_present ob_imod23_unpresent)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
          then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: f_imod1_unpresent imod_combine_def tmod_combine_def)
          assume f_imod3_present: "f \<in> Field (Tm Imod3)"
          then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: imod_combine_def tmod_combine_def)
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = undefined"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_unpresent f_imod3_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod23_present ob_imod1_present ob_imod23_unpresent)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume f_imod2_present: "f \<in> Field (Tm Imod2)"
          then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: imod_combine_def tmod_combine_def)
          have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: f_imod2_present imod_combine_def tmod_combine_def)
          assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod2_present ob_imod1_present ob_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = unspecified"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod23_present ob_imod1_present ob_imod23_unpresent)
          then show ?thesis
            using imod12_imod3_def
            by simp
        next
          assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
          then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: f_imod1_unpresent imod_combine_def tmod_combine_def)
          assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
          then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = undefined"
            by (simp add: imod_combine_def)
          then have imod12_imod3_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_unpresent f_imod3_unpresent)
          have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod23_unpresent)
          then show ?thesis
            using imod12_imod3_def
            by simp
        qed
      qed
    next
      assume ob_imod1_unpresent: "ob \<notin> Object Imod1"
      assume ob_imod2_present: "ob \<in> Object Imod2"
      assume ob_imod3_unpresent: "ob \<notin> Object Imod3"
      have ob_imod12_present: "ob \<in> Object (imod_combine Imod1 Imod2)"
        by (simp add: imod_combine_def ob_imod2_present)
      have ob_imod23_present: "ob \<in> Object (imod_combine Imod2 Imod3)"
        by (simp add: imod_combine_def ob_imod2_present)
      show ?thesis
        using f_imod2_cases
      proof (elim disjE)
        assume f_imod2_present: "f \<in> Field (Tm Imod2)"
        have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
          by (simp add: f_imod2_present imod_combine_def tmod_combine_def)
        have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: f_imod2_present imod_combine_def tmod_combine_def)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_present ob_imod1_unpresent ob_imod2_present)
        then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod1_imod23_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod2_present ob_imod2_present ob_imod3_unpresent)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: imod_combine_def)
        then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
        then show ?thesis
          using imod1_imod23_def
          by simp
      next
        assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
        show ?thesis
          using f_imod1_cases f_imod3_cases
        proof (elim disjE)
          assume f_imod1_present: "f \<in> Field (Tm Imod1)"
          then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: imod_combine_def tmod_combine_def)
          assume f_imod3_present: "f \<in> Field (Tm Imod3)"
          then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: imod_combine_def tmod_combine_def)
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_unpresent ob_imod2_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = unspecified"
            by (simp add: imod_combine_def)
          then have imod1_imod23_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_unpresent f_imod3_present ob_imod2_present ob_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
          then show ?thesis
            using imod1_imod23_def
            by simp
        next
          assume f_imod1_present: "f \<in> Field (Tm Imod1)"
          then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: imod_combine_def tmod_combine_def)
          assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
          then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present f_imod2_unpresent ob_imod1_unpresent ob_imod2_present)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = unspecified"
            by (simp add: imod_combine_def)
          then have imod1_imod23_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_unpresent f_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = undefined"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present f_imod23_unpresent ob_imod1_unpresent ob_imod23_present)
          then show ?thesis
            using imod1_imod23_def
            by simp
        next
          assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
          then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
          assume f_imod3_present: "f \<in> Field (Tm Imod3)"
          then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: imod_combine_def tmod_combine_def)
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = undefined"
            by (simp add: imod_combine_def)
          then have imod1_imod23_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_unpresent f_imod3_present ob_imod12_present ob_imod3_unpresent)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_unpresent f_imod3_present ob_imod2_present ob_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
          then show ?thesis
            using imod1_imod23_def
            by simp
        next
          assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
          then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
          assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
          then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: f_imod2_unpresent imod_combine_def tmod_combine_def)
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod2_unpresent)
          then have "FieldValue (imod_combine Imod1 Imod2) (ob, f) = undefined"
            by (simp add: imod_combine_def)
          then have imod1_imod23_def: "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_unpresent f_imod3_unpresent)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_unpresent f_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = undefined"
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod23_unpresent)
          then show ?thesis
            using imod1_imod23_def
            by simp
        qed
      qed
    next
      assume ob_imod1_unpresent: "ob \<notin> Object Imod1"
      assume ob_imod2_unpresent: "ob \<notin> Object Imod2"
      have ob_imod12_unpresent: "ob \<notin> Object (imod_combine Imod1 Imod2)"
        by (simp add: imod_combine_def ob_imod1_unpresent ob_imod2_unpresent)
      assume ob_imod3_present: "ob \<in> Object Imod3"
      then have ob_imod23_present: "ob \<in> Object (imod_combine Imod2 Imod3)"
        by (simp add: imod_combine_def)
      show ?thesis
        using f_imod3_cases
      proof (elim disjE)
        assume f_imod3_present: "f \<in> Field (Tm Imod3)"
        then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
          by (simp add: imod_combine_def tmod_combine_def)
        have "imod_combine_field_value Imod2 Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod3_present ob_imod2_unpresent ob_imod3_present)
        then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          by (simp add: imod_combine_def)
        then have imod1_imod23_def: "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
        have "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = FieldValue Imod3 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_imod3_present ob_imod12_unpresent ob_imod3_present)
        then show ?thesis
          using imod1_imod23_def
          by simp
      next
        assume f_imod3_unpresent: "f \<notin> Field (Tm Imod3)"
        show ?thesis
          using f_imod1_cases f_imod2_cases
        proof (elim disjE)
          assume f_imod1_present: "f \<in> Field (Tm Imod1)"
          then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: imod_combine_def tmod_combine_def)
          assume f_imod2_present: "f \<in> Field (Tm Imod2)"
          then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: imod_combine_def tmod_combine_def)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_unpresent ob_imod3_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            by (simp add: imod_combine_def)
          then have imod1_imod23_def: "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
          have "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_unpresent ob_imod3_present)
          then show ?thesis
            using imod1_imod23_def
            by simp
        next
          assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
          assume f_imod2_present: "f \<in> Field (Tm Imod2)"
          then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: imod_combine_def tmod_combine_def)
          then have f_imod23_present: "f \<in> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: f_imod2_present imod_combine_def tmod_combine_def)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_present f_imod3_unpresent ob_imod2_unpresent ob_imod3_present)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            by (simp add: imod_combine_def)
          then have imod1_imod23_def: "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod23_present ob_imod1_unpresent ob_imod23_present)
          have "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_unpresent ob_imod3_present)
          then show ?thesis
            using imod1_imod23_def
            by simp
        next
          assume f_imod1_present: "f \<in> Field (Tm Imod1)"
          then have f_imod12_present: "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: imod_combine_def tmod_combine_def)
          assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
          then have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: f_imod3_unpresent imod_combine_def tmod_combine_def)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_unpresent f_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = undefined"
            by (simp add: imod_combine_def)
          then have imod1_imod23_def: "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_present f_imod23_unpresent ob_imod1_unpresent ob_imod23_present)
          have "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = unspecified"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_present f_imod3_unpresent ob_imod12_unpresent ob_imod3_present)
          then show ?thesis
            using imod1_imod23_def
            by simp
        next
          assume f_imod1_unpresent: "f \<notin> Field (Tm Imod1)"
          assume f_imod2_unpresent: "f \<notin> Field (Tm Imod2)"
          then have f_imod12_unpresent: "f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
            by (simp add: f_imod1_unpresent imod_combine_def tmod_combine_def)
          have f_imod23_unpresent: "f \<notin> Field (Tm (imod_combine Imod2 Imod3))"
            by (simp add: f_imod2_unpresent f_imod3_unpresent imod_combine_def tmod_combine_def)
          have "imod_combine_field_value Imod2 Imod3 (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod2_unpresent f_imod3_unpresent)
          then have "FieldValue (imod_combine Imod2 Imod3) (ob, f) = undefined"
            by (simp add: imod_combine_def)
          then have imod1_imod23_def: "imod_combine_field_value Imod1 (imod_combine Imod2 Imod3) (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod1_unpresent f_imod23_unpresent)
          have "imod_combine_field_value (imod_combine Imod1 Imod2) Imod3 (ob, f) = undefined"
            unfolding imod_combine_field_value_def
            by (simp add: f_imod12_unpresent f_imod3_unpresent)
          then show ?thesis
            using imod1_imod23_def
            by simp
        qed
      qed
    next
      assume ob_imod1_unpresent: "ob \<notin> Object Imod1"
      assume ob_imod2_unpresent: "ob \<notin> Object Imod2"
      assume ob_imod3_unpresent: "ob \<notin> Object Imod3"
      have ob_imod12_unpresent: "ob \<notin> Object (imod_combine Imod1 Imod2)"
        by (simp add: imod_combine_def ob_imod1_unpresent ob_imod2_unpresent)
      have ob_imod23_unpresent: "ob \<notin> Object (imod_combine Imod2 Imod3)"
        by (simp add: imod_combine_def ob_imod2_unpresent ob_imod3_unpresent)
      show ?thesis
        unfolding imod_combine_field_value_def
        by (simp add: ob_imod12_unpresent ob_imod1_unpresent ob_imod23_unpresent ob_imod3_unpresent)
    qed
  qed
  then show ?thesis
    by fastforce
qed

lemma imod_combine_default_value_assoc[simp]:
  shows "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) = imod_combine_default_value (imod_combine Imod1 Imod2) Imod3"
proof
  fix c
  have tmod1_cases: "c \<in> Constant (Tm Imod1) \<or> c \<notin> Constant (Tm Imod1)"
    by simp
  have tmod2_cases: "c \<in> Constant (Tm Imod2) \<or> c \<notin> Constant (Tm Imod2)"
    by simp
  have tmod3_cases: "c \<in> Constant (Tm Imod3) \<or> c \<notin> Constant (Tm Imod3)"
    by simp
  show "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) c = imod_combine_default_value (imod_combine Imod1 Imod2) Imod3 c"
    using tmod1_cases tmod2_cases tmod3_cases
  proof (elim disjE)
    assume c_in_tmod1: "c \<in> Constant (Tm Imod1)"
    assume c_in_tmod2: "c \<in> Constant (Tm Imod2)"
    assume c_in_tmod3: "c \<in> Constant (Tm Imod3)"
    have c_in_tmod12: "c \<in> Constant (Tm (imod_combine Imod1 Imod2))"
      by (simp add: c_in_tmod2 imod_combine_def tmod_combine_def)
    have c_in_tmod23: "c \<in> Constant (Tm (imod_combine Imod2 Imod3))"
      by (simp add: c_in_tmod2 imod_combine_def tmod_combine_def)
    show ?thesis
    proof (induct "DefaultValue Imod1 c = DefaultValue Imod2 c")
      case True
      then have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod1 c"
        unfolding imod_combine_default_value_def
        using c_in_tmod1 c_in_tmod2
        by simp
      then have defaultvalue_tmod12: "DefaultValue (imod_combine Imod1 Imod2) c = DefaultValue Imod1 c"
        by (simp add: imod_combine_def)
      show ?case
        using True.hyps
      proof (induct "DefaultValue Imod2 c = DefaultValue Imod3 c")
        case True
        then have "imod_combine_default_value Imod2 Imod3 c = DefaultValue Imod2 c"
          unfolding imod_combine_default_value_def
          using c_in_tmod2 c_in_tmod3
          by simp
        then have "DefaultValue (imod_combine Imod2 Imod3) c = DefaultValue Imod2 c"
          by (simp add: imod_combine_def)
        then have defaultvalue_imod1_imod23: "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) c = DefaultValue Imod1 c"
          unfolding imod_combine_default_value_def
          using True.prems c_in_tmod23
          by simp
        have defaultvalue_imod12_imod3: "imod_combine_default_value (imod_combine Imod1 Imod2) Imod3 c = DefaultValue Imod1 c"
          unfolding imod_combine_default_value_def
          using True.hyps True.prems c_in_tmod12 defaultvalue_tmod12
          by simp
        show ?case
          using defaultvalue_imod1_imod23 defaultvalue_imod12_imod3
          by simp
      next
        case False
        then have "imod_combine_default_value Imod2 Imod3 c = invalid"
          unfolding imod_combine_default_value_def
          using c_in_tmod2 c_in_tmod3
          by simp
        then have "DefaultValue (imod_combine Imod2 Imod3) c = invalid"
          by (simp add: imod_combine_def)
        then have defaultvalue_imod1_imod23: "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) c = invalid"
          unfolding imod_combine_default_value_def
          by (simp add: c_in_tmod23)
        have defaultvalue_imod12_imod3: "imod_combine_default_value (imod_combine Imod1 Imod2) Imod3 c = invalid"
          unfolding imod_combine_default_value_def
          using False.hyps True.hyps c_in_tmod12 c_in_tmod3 defaultvalue_tmod12
          by simp
        show ?case
          using defaultvalue_imod1_imod23 defaultvalue_imod12_imod3
          by simp
      qed
    next
      case False
      then have "imod_combine_default_value Imod1 Imod2 c = invalid"
        unfolding imod_combine_default_value_def
        using c_in_tmod1 c_in_tmod2
        by simp
      then have defaultvalue_tmod12: "DefaultValue (imod_combine Imod1 Imod2) c = invalid"
        by (simp add: imod_combine_def)
      show ?case
        using False.hyps
      proof (induct "DefaultValue Imod2 c = DefaultValue Imod3 c")
        case True
        then have "imod_combine_default_value Imod2 Imod3 c = DefaultValue Imod2 c"
          unfolding imod_combine_default_value_def
          using c_in_tmod2 c_in_tmod3
          by simp
        then have "DefaultValue (imod_combine Imod2 Imod3) c = DefaultValue Imod2 c"
          by (simp add: imod_combine_def)
        then have defaultvalue_imod1_imod23: "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) c = invalid"
          unfolding imod_combine_default_value_def
          using True.prems c_in_tmod1 c_in_tmod23
          by simp
        have defaultvalue_imod12_imod3: "imod_combine_default_value (imod_combine Imod1 Imod2) Imod3 c = invalid"
          unfolding imod_combine_default_value_def
          by (simp add: c_in_tmod12 defaultvalue_tmod12)
        show ?case
          using defaultvalue_imod1_imod23 defaultvalue_imod12_imod3
          by simp
      next
        case False
        then have "imod_combine_default_value Imod2 Imod3 c = invalid"
          unfolding imod_combine_default_value_def
          using c_in_tmod2 c_in_tmod3
          by simp
        then have "DefaultValue (imod_combine Imod2 Imod3) c = invalid"
          by (simp add: imod_combine_def)
        then have defaultvalue_imod1_imod23: "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) c = invalid"
          unfolding imod_combine_default_value_def
          by (simp add: c_in_tmod23)
        have defaultvalue_imod12_imod3: "imod_combine_default_value (imod_combine Imod1 Imod2) Imod3 c = invalid"
          unfolding imod_combine_default_value_def
          by (simp add: c_in_tmod12 c_in_tmod3 defaultvalue_tmod12)
        show ?case
          using defaultvalue_imod1_imod23 defaultvalue_imod12_imod3
          by simp
      qed
    qed
  next
    assume c_in_tmod1: "c \<in> Constant (Tm Imod1)"
    assume c_in_tmod2: "c \<in> Constant (Tm Imod2)"
    assume c_not_in_tmod3: "c \<notin> Constant (Tm Imod3)"
    have c_in_tmod12: "c \<in> Constant (Tm (imod_combine Imod1 Imod2))"
      by (simp add: c_in_tmod2 imod_combine_def tmod_combine_def)
    have c_in_tmod23: "c \<in> Constant (Tm (imod_combine Imod2 Imod3))"
      by (simp add: c_in_tmod2 imod_combine_def tmod_combine_def)
    show ?thesis
    proof (induct "DefaultValue Imod1 c = DefaultValue Imod2 c")
      case True
      then have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod1 c"
        unfolding imod_combine_default_value_def
        using c_in_tmod1 c_in_tmod2
        by simp
      then have "DefaultValue (imod_combine Imod1 Imod2) c = DefaultValue Imod1 c"
        by (simp add: imod_combine_def)
      then have defaultvalue_imod12_imod3: "imod_combine_default_value (imod_combine Imod1 Imod2) Imod3 c = DefaultValue Imod1 c"
        unfolding imod_combine_default_value_def
        using c_in_tmod12 c_not_in_tmod3
        by simp
      have "imod_combine_default_value Imod2 Imod3 c = DefaultValue Imod2 c"
        unfolding imod_combine_default_value_def
        by (simp add: c_in_tmod2 c_not_in_tmod3)
      then have "DefaultValue (imod_combine Imod2 Imod3) c = DefaultValue Imod2 c"
        by (simp add: imod_combine_def)
      then have defaultvalue_imod1_imod23: "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) c = DefaultValue Imod1 c"
        unfolding imod_combine_default_value_def
        using True.hyps c_in_tmod23
        by simp
      show ?case
        using defaultvalue_imod1_imod23 defaultvalue_imod12_imod3
        by simp
    next
      case False
      then have "imod_combine_default_value Imod1 Imod2 c = invalid"
        unfolding imod_combine_default_value_def
        using c_in_tmod1 c_in_tmod2
        by simp
      then have "DefaultValue (imod_combine Imod1 Imod2) c = invalid"
        by (simp add: imod_combine_def)
      then have defaultvalue_imod12_imod3: "imod_combine_default_value (imod_combine Imod1 Imod2) Imod3 c = invalid"
        unfolding imod_combine_default_value_def
        using c_in_tmod12 c_not_in_tmod3
        by simp
      have "imod_combine_default_value Imod2 Imod3 c = DefaultValue Imod2 c"
        unfolding imod_combine_default_value_def
        by (simp add: c_in_tmod2 c_not_in_tmod3)
      then have "DefaultValue (imod_combine Imod2 Imod3) c = DefaultValue Imod2 c"
        by (simp add: imod_combine_def)
      then have defaultvalue_imod1_imod23: "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) c = invalid"
        unfolding imod_combine_default_value_def
        using False.hyps c_in_tmod1 c_in_tmod23
        by simp
      show ?case
        using defaultvalue_imod1_imod23 defaultvalue_imod12_imod3
        by simp
    qed
  next
    assume c_in_tmod1: "c \<in> Constant (Tm Imod1)"
    assume c_not_in_tmod2: "c \<notin> Constant (Tm Imod2)"
    assume c_in_tmod3: "c \<in> Constant (Tm Imod3)"
    have c_in_tmod12: "c \<in> Constant (Tm (imod_combine Imod1 Imod2))"
      by (simp add: c_in_tmod1 imod_combine_def tmod_combine_def)
    have c_in_tmod23: "c \<in> Constant (Tm (imod_combine Imod2 Imod3))"
      by (simp add: c_in_tmod3 imod_combine_def tmod_combine_def)
    have "imod_combine_default_value Imod2 Imod3 c = DefaultValue Imod3 c"
      unfolding imod_combine_default_value_def
      by (simp add: c_in_tmod3 c_not_in_tmod2)
    then have defaultvalue_tmod23: "DefaultValue (imod_combine Imod2 Imod3) c = DefaultValue Imod3 c"
      by (simp add: imod_combine_def)
    have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod1 c"
      unfolding imod_combine_default_value_def
      by (simp add: c_in_tmod1 c_not_in_tmod2)
    then have defaultvalue_tmod12: "DefaultValue (imod_combine Imod1 Imod2) c = DefaultValue Imod1 c"
      by (simp add: imod_combine_def)
    show ?thesis
    proof (induct "DefaultValue Imod1 c = DefaultValue Imod3 c")
      case True
      have defaultvalue_imod1_imod23: "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) c = DefaultValue Imod1 c"
        unfolding imod_combine_default_value_def
        using True.hyps c_in_tmod23 defaultvalue_tmod23
        by simp
      have defaultvalue_imod12_imod3: "imod_combine_default_value (imod_combine Imod1 Imod2) Imod3 c = DefaultValue Imod1 c"
        unfolding imod_combine_default_value_def
        using True.hyps c_in_tmod12 defaultvalue_tmod12
        by simp
      show ?case
        using defaultvalue_imod1_imod23 defaultvalue_imod12_imod3
        by simp
    next
      case False
      have defaultvalue_imod1_imod23: "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) c = invalid"
        unfolding imod_combine_default_value_def
        using False.hyps c_in_tmod1 c_in_tmod23 defaultvalue_tmod23
        by simp
      have defaultvalue_imod12_imod3: "imod_combine_default_value (imod_combine Imod1 Imod2) Imod3 c = invalid"
        unfolding imod_combine_default_value_def
        using False.hyps c_in_tmod12 c_in_tmod3 defaultvalue_tmod12
        by simp
      show ?case
        using defaultvalue_imod1_imod23 defaultvalue_imod12_imod3
        by simp
    qed
  next
    assume c_not_in_tmod1: "c \<notin> Constant (Tm Imod1)"
    assume c_in_tmod2: "c \<in> Constant (Tm Imod2)"
    assume c_in_tmod3: "c \<in> Constant (Tm Imod3)"
    have c_in_tmod12: "c \<in> Constant (Tm (imod_combine Imod1 Imod2))"
      by (simp add: c_in_tmod2 imod_combine_def tmod_combine_def)
    have c_in_tmod23: "c \<in> Constant (Tm (imod_combine Imod2 Imod3))"
      by (simp add: c_in_tmod2 imod_combine_def tmod_combine_def)
    show ?thesis
    proof (induct "DefaultValue Imod2 c = DefaultValue Imod3 c")
      case True
      then have "imod_combine_default_value Imod2 Imod3 c = DefaultValue Imod2 c"
        unfolding imod_combine_default_value_def
        using c_in_tmod2 c_in_tmod3
        by simp
      then have "DefaultValue (imod_combine Imod2 Imod3) c = DefaultValue Imod2 c"
        by (simp add: imod_combine_def)
      then have defaultvalue_imod1_imod23: "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) c = DefaultValue Imod2 c"
        unfolding imod_combine_default_value_def
        using c_not_in_tmod1 c_in_tmod23
        by simp
      have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod2 c"
        unfolding imod_combine_default_value_def
        by (simp add: c_not_in_tmod1 c_in_tmod2)
      then have "DefaultValue (imod_combine Imod1 Imod2) c = DefaultValue Imod2 c"
        by (simp add: imod_combine_def)
      then have defaultvalue_imod12_imod3: "imod_combine_default_value (imod_combine Imod1 Imod2) Imod3 c = DefaultValue Imod2 c"
        unfolding imod_combine_default_value_def
        using True.hyps c_in_tmod3
        by simp
      show ?case
        using defaultvalue_imod1_imod23 defaultvalue_imod12_imod3
        by simp
    next
      case False
      then have "imod_combine_default_value Imod2 Imod3 c = invalid"
        unfolding imod_combine_default_value_def
        using c_in_tmod2 c_in_tmod3
        by simp
      then have "DefaultValue (imod_combine Imod2 Imod3) c = invalid"
        by (simp add: imod_combine_def)
      then have defaultvalue_imod1_imod23: "imod_combine_default_value Imod1 (imod_combine Imod2 Imod3) c = invalid"
        unfolding imod_combine_default_value_def
        using c_not_in_tmod1 c_in_tmod23
        by simp
      have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod2 c"
        unfolding imod_combine_default_value_def
        by (simp add: c_not_in_tmod1 c_in_tmod2)
      then have "DefaultValue (imod_combine Imod1 Imod2) c = DefaultValue Imod2 c"
        by (simp add: imod_combine_def)
      then have defaultvalue_imod12_imod3: "imod_combine_default_value (imod_combine Imod1 Imod2) Imod3 c = invalid"
        unfolding imod_combine_default_value_def
        using False.hyps c_in_tmod12 c_in_tmod3
        by simp
      show ?case
        using defaultvalue_imod1_imod23 defaultvalue_imod12_imod3
        by simp
    qed
  next
    assume c_in_tmod1: "c \<in> Constant (Tm Imod1)"
    assume c_not_in_tmod2: "c \<notin> Constant (Tm Imod2)"
    assume c_not_in_tmod3: "c \<notin> Constant (Tm Imod3)"
    have c_in_tmod12: "c \<in> Constant (Tm (imod_combine Imod1 Imod2))"
      by (simp add: c_in_tmod1 imod_combine_def tmod_combine_def)
    have c_not_in_tmod23: "c \<notin> Constant (Tm (imod_combine Imod2 Imod3))"
      by (simp add: c_not_in_tmod2 c_not_in_tmod3 imod_combine_def tmod_combine_def)
    have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod1 c"
      unfolding imod_combine_default_value_def
      by (simp add: c_in_tmod1 c_not_in_tmod2)
    then have "DefaultValue (imod_combine Imod1 Imod2) c = DefaultValue Imod1 c"
      by (simp add: imod_combine_def)
    then show ?thesis
      unfolding imod_combine_default_value_def
      using c_in_tmod12 c_not_in_tmod3 c_in_tmod1 c_not_in_tmod23
      by simp
  next
    assume c_not_in_tmod1: "c \<notin> Constant (Tm Imod1)"
    assume c_in_tmod2: "c \<in> Constant (Tm Imod2)"
    assume c_not_in_tmod3: "c \<notin> Constant (Tm Imod3)"
    have c_in_tmod12: "c \<in> Constant (Tm (imod_combine Imod1 Imod2))"
      by (simp add: c_in_tmod2 imod_combine_def tmod_combine_def)
    have c_in_tmod23: "c \<in> Constant (Tm (imod_combine Imod2 Imod3))"
      by (simp add: c_in_tmod2 imod_combine_def tmod_combine_def)
    have "imod_combine_default_value Imod2 Imod3 c = DefaultValue Imod2 c"
      unfolding imod_combine_default_value_def
      by (simp add: c_not_in_tmod3 c_in_tmod2)
    then have defaultvalue_tmod23: "DefaultValue (imod_combine Imod2 Imod3) c = DefaultValue Imod2 c"
      by (simp add: imod_combine_def)
    have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod2 c"
      unfolding imod_combine_default_value_def
      by (simp add: c_not_in_tmod1 c_in_tmod2)
    then have defaultvalue_tmod12: "DefaultValue (imod_combine Imod1 Imod2) c = DefaultValue Imod2 c"
      by (simp add: imod_combine_def)
    show ?thesis
      unfolding imod_combine_default_value_def
      using c_in_tmod12 c_not_in_tmod3 c_not_in_tmod1 c_in_tmod23 defaultvalue_tmod12 defaultvalue_tmod23
      by simp
  next
    assume c_not_in_tmod1: "c \<notin> Constant (Tm Imod1)"
    assume c_not_in_tmod2: "c \<notin> Constant (Tm Imod2)"
    assume c_in_tmod3: "c \<in> Constant (Tm Imod3)"
    have c_not_in_tmod12: "c \<notin> Constant (Tm (imod_combine Imod1 Imod2))"
      by (simp add: c_not_in_tmod1 c_not_in_tmod2 imod_combine_def tmod_combine_def)
    have c_in_tmod23: "c \<in> Constant (Tm (imod_combine Imod2 Imod3))"
      by (simp add: c_in_tmod3 imod_combine_def tmod_combine_def)
    have "imod_combine_default_value Imod2 Imod3 c = DefaultValue Imod3 c"
      unfolding imod_combine_default_value_def
      by (simp add: c_in_tmod3 c_not_in_tmod2)
    then have "DefaultValue (imod_combine Imod2 Imod3) c = DefaultValue Imod3 c"
      by (simp add: imod_combine_def)
    then show ?thesis
      unfolding imod_combine_default_value_def
      using c_not_in_tmod12 c_in_tmod3 c_not_in_tmod1 c_in_tmod23
      by simp
  next
    assume c_not_in_tmod1: "c \<notin> Constant (Tm Imod1)"
    assume c_not_in_tmod2: "c \<notin> Constant (Tm Imod2)"
    assume c_not_in_tmod3: "c \<notin> Constant (Tm Imod3)"
    have c_not_in_tmod12: "c \<notin> Constant (Tm (imod_combine Imod1 Imod2))"
      by (simp add: c_not_in_tmod1 c_not_in_tmod2 imod_combine_def tmod_combine_def)
    have c_not_in_tmod23: "c \<notin> Constant (Tm (imod_combine Imod2 Imod3))"
      by (simp add: c_not_in_tmod2 c_not_in_tmod3 imod_combine_def tmod_combine_def)
    show ?thesis
      unfolding imod_combine_default_value_def
      using c_not_in_tmod1 c_not_in_tmod23 c_not_in_tmod12 c_not_in_tmod3
      by simp
  qed
qed

lemma imod_combine_assoc: "imod_combine (imod_combine Imod1 Imod2) Imod3 = imod_combine Imod1 (imod_combine Imod2 Imod3)"
proof-
  have "\<And>Imod12 Imod23. Imod12 = imod_combine Imod1 Imod2 \<Longrightarrow> Imod23 = imod_combine Imod2 Imod3 \<Longrightarrow> imod_combine Imod12 Imod3 = imod_combine Imod1 Imod23"
  proof-
    fix Imod12
    fix Imod23
    assume imod12_def: "Imod12 = imod_combine Imod1 Imod2"
    assume imod23_def: "Imod23 = imod_combine Imod2 Imod3"
    show "imod_combine Imod12 Imod3 = imod_combine Imod1 Imod23"
      unfolding imod_combine_def
    proof
      show "tmod_combine (Tm Imod12) (Tm Imod3) = tmod_combine (Tm Imod1) (Tm Imod23) \<and>
        Object Imod12 \<union> Object Imod3 = Object Imod1 \<union> Object Imod23 \<and>
        imod_combine_object_class Imod12 Imod3 = imod_combine_object_class Imod1 Imod23 \<and>
        imod_combine_object_id Imod12 Imod3 = imod_combine_object_id Imod1 Imod23 \<and> 
        imod_combine_field_value Imod12 Imod3 = imod_combine_field_value Imod1 Imod23 \<and> 
        imod_combine_default_value Imod12 Imod3 = imod_combine_default_value Imod1 Imod23 \<and> 
        () = ()"
        using imod12_def imod23_def
      proof (intro conjI)
        show "imod_combine_object_class Imod12 Imod3 = imod_combine_object_class Imod1 Imod23"
          using imod12_def imod23_def imod_combine_object_class_assoc
          by blast
      next
        show "imod_combine_object_id Imod12 Imod3 = imod_combine_object_id Imod1 Imod23"
          using imod12_def imod23_def imod_combine_object_id_assoc
          by blast
      next
        show "imod_combine_field_value Imod12 Imod3 = imod_combine_field_value Imod1 Imod23"
          using imod12_def imod23_def imod_combine_field_value_assoc
          by metis
      next
        show "imod_combine_default_value Imod12 Imod3 = imod_combine_default_value Imod1 Imod23"
          using imod12_def imod23_def imod_combine_default_value_assoc
          by metis
      qed (simp_all add: Un_assoc imod_combine_def tmod_combine_assoc)
    qed
  qed
  then show ?thesis
    by blast
qed


subsection "Merging value sets"

lemma imod_combine_proper_class_values: "ProperClassValue (imod_combine Imod1 Imod2) = ProperClassValue Imod1 \<union> ProperClassValue Imod2"
proof
  show "ProperClassValue (imod_combine Imod1 Imod2) \<subseteq> ProperClassValue Imod1 \<union> ProperClassValue Imod2"
  proof
    fix x
    assume "x \<in> ProperClassValue (imod_combine Imod1 Imod2)"
    then show "x \<in> ProperClassValue Imod1 \<union> ProperClassValue Imod2"
    proof (induct)
      case (rule_proper_objects ob)
      then have "ob \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then show ?case
        using ProperClassValue.rule_proper_objects
        by fastforce
    qed
  qed
next
  show "ProperClassValue Imod1 \<union> ProperClassValue Imod2 \<subseteq> ProperClassValue (imod_combine Imod1 Imod2)"
  proof
    fix x
    assume "x \<in> ProperClassValue Imod1 \<union> ProperClassValue Imod2"
    then show "x \<in> ProperClassValue (imod_combine Imod1 Imod2)"
    proof (elim UnE)
      assume "x \<in> ProperClassValue Imod1"
      then show "x \<in> ProperClassValue (imod_combine Imod1 Imod2)"
      proof (induct)
        case (rule_proper_objects ob)
        then show ?case
          by (simp add: ProperClassValue.rule_proper_objects imod_combine_def)
      qed
    next
      assume "x \<in> ProperClassValue Imod2"
      then show "x \<in> ProperClassValue (imod_combine Imod1 Imod2)"
      proof (induct)
        case (rule_proper_objects ob)
        then show ?case
          by (simp add: ProperClassValue.rule_proper_objects imod_combine_def)
      qed
    qed
  qed
qed

lemma imod_combine_class_values: "ClassValue (imod_combine Imod1 Imod2) = ClassValue Imod1 \<union> ClassValue Imod2"
  unfolding ClassValue_def
  by (simp add: imod_combine_proper_class_values)

lemma imod_combine_enum_values: "EnumValueValue (Tm (imod_combine Imod1 Imod2)) = EnumValueValue (Tm Imod1) \<union> EnumValueValue (Tm Imod2)"
proof
  show "EnumValueValue (Tm (imod_combine Imod1 Imod2)) \<subseteq> EnumValueValue (Tm Imod1) \<union> EnumValueValue (Tm Imod2)"
  proof
    fix x :: "('o, 'b) ValueDef"
    assume "x \<in> EnumValueValue (Tm (imod_combine Imod1 Imod2))"
    then have "x \<in> EnumValueValue (tmod_combine (Tm Imod1) (Tm Imod2))"
      by (simp add: imod_combine_def)
    then show "x \<in> EnumValueValue (Tm Imod1) \<union> EnumValueValue (Tm Imod2)"
    proof (induct)
      case (rule_enumvalue ev)
      then have "ev \<in> EnumValue (Tm Imod1) \<union> EnumValue (Tm Imod2)"
        by (simp add: tmod_combine_def)
      then show ?case
        using EnumValueValue.rule_enumvalue
        by blast
    qed
  qed
next
  show "EnumValueValue (Tm Imod1) \<union> EnumValueValue (Tm Imod2) \<subseteq> EnumValueValue (Tm (imod_combine Imod1 Imod2))"
  proof
    fix x :: "('o, 'b) ValueDef"
    assume "x \<in> EnumValueValue (Tm Imod1) \<union> EnumValueValue (Tm Imod2)"
    then have "x \<in> EnumValueValue (tmod_combine (Tm Imod1) (Tm Imod2))"
    proof (elim UnE)
      assume "x \<in> EnumValueValue (Tm Imod1)"
      then show "x \<in> EnumValueValue (tmod_combine (Tm Imod1) (Tm Imod2))"
      proof (induct)
        case (rule_enumvalue ev)
        then show ?case
          by (simp add: EnumValueValue.rule_enumvalue tmod_combine_def)
      qed
    next
      assume "x \<in> EnumValueValue (Tm Imod2)"
      then show "x \<in> EnumValueValue (tmod_combine (Tm Imod1) (Tm Imod2))"
      proof (induct)
        case (rule_enumvalue ev)
        then show ?case
          by (simp add: EnumValueValue.rule_enumvalue tmod_combine_def)
      qed
    qed
    then show "x \<in> EnumValueValue (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def)
  qed
qed

lemma imod_combine_atom_values: "AtomValue (imod_combine Imod1 Imod2) = AtomValue Imod1 \<union> AtomValue Imod2"
  unfolding AtomValue_def
  using imod_combine_class_values imod_combine_enum_values
  by blast

lemma imod_combine_atom_value_list: "AtomValueList Imod1 \<union> AtomValueList Imod2 \<subseteq> AtomValueList (imod_combine Imod1 Imod2)"
proof
  fix x
  assume "x \<in> AtomValueList Imod1 \<union> AtomValueList Imod2"
  then show "x \<in> AtomValueList (imod_combine Imod1 Imod2)"
  proof (elim UnE)
    assume "x \<in> AtomValueList Imod1"
    then show "x \<in> AtomValueList (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_fst_atom_element v)
      then show ?case
        by (simp add: AtomValueList.rule_fst_atom_element imod_combine_atom_values)
    next
      case (rule_rec_atom_element l v)
      then show ?case
        by (simp add: AtomValueList.rule_rec_atom_element imod_combine_atom_values)
    qed
  next
    assume "x \<in> AtomValueList Imod2"
    then show "x \<in> AtomValueList (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_fst_atom_element v)
      then show ?case
        by (simp add: AtomValueList.rule_fst_atom_element imod_combine_atom_values)
    next
      case (rule_rec_atom_element l v)
      then show ?case
        by (simp add: AtomValueList.rule_rec_atom_element imod_combine_atom_values)
    qed
  qed
qed

lemma imod_combine_container_value_list: "ContainerValueList Imod1 \<union> ContainerValueList Imod2 \<subseteq> ContainerValueList (imod_combine Imod1 Imod2)"
proof
  fix x
  assume "x \<in> ContainerValueList Imod1 \<union> ContainerValueList Imod2"
  then show "x \<in> ContainerValueList (imod_combine Imod1 Imod2)"
  proof (elim UnE)
    assume "x \<in> ContainerValueList Imod1"
    then show "x \<in> ContainerValueList (imod_combine Imod1 Imod2)"
    proof (induct)
      case rule_empty_list
      then show ?case 
        by (fact ContainerValueList.rule_empty_list)
    next
      case (rule_append_bag_element v l)
      then show ?case
        using ContainerValueList.rule_append_bag_element imod_combine_atom_value_list
        by blast
    next
      case (rule_append_set_element v l)
      then show ?case
        using ContainerValueList.rule_append_set_element imod_combine_atom_value_list
        by blast
    next
      case (rule_append_seq_element v l)
      then show ?case
        using ContainerValueList.rule_append_seq_element imod_combine_atom_value_list
        by blast
    next
      case (rule_append_ord_element v l)
      then show ?case
        using ContainerValueList.rule_append_ord_element imod_combine_atom_value_list
        by blast
    next
      case (rule_wrap_bag_element v1 v2)
      then show ?case
        using ContainerValueList.rule_wrap_bag_element
        by blast
    next
      case (rule_wrap_set_element v1 v2)
      then show ?case
        using ContainerValueList.rule_wrap_set_element
        by blast
    next
      case (rule_wrap_seq_element v1 v2)
      then show ?case
        using ContainerValueList.rule_wrap_seq_element
        by blast
    next
      case (rule_wrap_ord_element v1 v2)
      then show ?case
        using ContainerValueList.rule_wrap_ord_element
        by blast
    qed
  next
    assume "x \<in> ContainerValueList Imod2"
    then show "x \<in> ContainerValueList (imod_combine Imod1 Imod2)"
    proof (induct)
      case rule_empty_list
      then show ?case 
        by (fact ContainerValueList.rule_empty_list)
    next
      case (rule_append_bag_element v l)
      then show ?case
        using ContainerValueList.rule_append_bag_element imod_combine_atom_value_list
        by blast
    next
      case (rule_append_set_element v l)
      then show ?case
        using ContainerValueList.rule_append_set_element imod_combine_atom_value_list
        by blast
    next
      case (rule_append_seq_element v l)
      then show ?case
        using ContainerValueList.rule_append_seq_element imod_combine_atom_value_list
        by blast
    next
      case (rule_append_ord_element v l)
      then show ?case
        using ContainerValueList.rule_append_ord_element imod_combine_atom_value_list
        by blast
    next
      case (rule_wrap_bag_element v1 v2)
      then show ?case
        using ContainerValueList.rule_wrap_bag_element
        by blast
    next
      case (rule_wrap_set_element v1 v2)
      then show ?case
        using ContainerValueList.rule_wrap_set_element
        by blast
    next
      case (rule_wrap_seq_element v1 v2)
      then show ?case
        using ContainerValueList.rule_wrap_seq_element
        by blast
    next
      case (rule_wrap_ord_element v1 v2)
      then show ?case
        using ContainerValueList.rule_wrap_ord_element
        by blast
    qed
  qed
qed

lemma imod_combine_container_value: "ContainerValue Imod1 \<union> ContainerValue Imod2 \<subseteq> ContainerValue (imod_combine Imod1 Imod2)"
proof
  fix x
  assume "x \<in> ContainerValue Imod1 \<union> ContainerValue Imod2"
  then show "x \<in> ContainerValue (imod_combine Imod1 Imod2)"
  proof (elim UnE)
    assume "x \<in> ContainerValue Imod1"
    then show "x \<in> ContainerValue (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_bagof_atom_values l)
      then show ?case
        using ContainerValue.rule_bagof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_setof_atom_values l)
      then show ?case
        using ContainerValue.rule_setof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_seqof_atom_values l)
      then show ?case
        using ContainerValue.rule_seqof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_ordof_atom_values l)
      then show ?case
        using ContainerValue.rule_ordof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_bagof_container_values l)
      then show ?case
        using ContainerValue.rule_bagof_container_values imod_combine_container_value_list
        by blast
    next
      case (rule_setof_container_values l)
      then show ?case
        using ContainerValue.rule_setof_container_values imod_combine_container_value_list
        by blast
    next
      case (rule_seqof_container_values l)
      then show ?case
        using ContainerValue.rule_seqof_container_values imod_combine_container_value_list
        by blast
    next
      case (rule_ordof_container_values l)
      then show ?case
        using ContainerValue.rule_ordof_container_values imod_combine_container_value_list
        by blast
    qed
  next
    assume "x \<in> ContainerValue Imod2"
    then show "x \<in> ContainerValue (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_bagof_atom_values l)
      then show ?case
        using ContainerValue.rule_bagof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_setof_atom_values l)
      then show ?case
        using ContainerValue.rule_setof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_seqof_atom_values l)
      then show ?case
        using ContainerValue.rule_seqof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_ordof_atom_values l)
      then show ?case
        using ContainerValue.rule_ordof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_bagof_container_values l)
      then show ?case
        using ContainerValue.rule_bagof_container_values imod_combine_container_value_list
        by blast
    next
      case (rule_setof_container_values l)
      then show ?case
        using ContainerValue.rule_setof_container_values imod_combine_container_value_list
        by blast
    next
      case (rule_seqof_container_values l)
      then show ?case
        using ContainerValue.rule_seqof_container_values imod_combine_container_value_list
        by blast
    next
      case (rule_ordof_container_values l)
      then show ?case
        using ContainerValue.rule_ordof_container_values imod_combine_container_value_list
        by blast
    qed
  qed
qed

lemma imod_combine_value: "Value Imod1 \<union> Value Imod2 \<subseteq> Value (imod_combine Imod1 Imod2)"
  unfolding Value_def
  using imod_combine_atom_values imod_combine_container_value
  by blast

lemma imod_combine_bag_container_value: "BagContainerValue Imod1 \<union> BagContainerValue Imod2 \<subseteq> BagContainerValue (imod_combine Imod1 Imod2)"
proof
  fix x
  assume "x \<in> BagContainerValue Imod1 \<union> BagContainerValue Imod2"
  then show "x \<in> BagContainerValue (imod_combine Imod1 Imod2)"
  proof (elim UnE)
    assume "x \<in> BagContainerValue Imod1"
    then show "x \<in> BagContainerValue (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_bagof_atom_values l)
      then show ?case
        using BagContainerValue.rule_bagof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_bagof_container_values l)
      then show ?case
        using BagContainerValue.rule_bagof_container_values imod_combine_container_value_list
        by blast
    qed
  next
    assume "x \<in> BagContainerValue Imod2"
    then show "x \<in> BagContainerValue (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_bagof_atom_values l)
      then show ?case
        using BagContainerValue.rule_bagof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_bagof_container_values l)
      then show ?case
        using BagContainerValue.rule_bagof_container_values imod_combine_container_value_list
        by blast
    qed
  qed
qed

lemma imod_combine_set_container_value: "SetContainerValue Imod1 \<union> SetContainerValue Imod2 \<subseteq> SetContainerValue (imod_combine Imod1 Imod2)"
proof
  fix x
  assume "x \<in> SetContainerValue Imod1 \<union> SetContainerValue Imod2"
  then show "x \<in> SetContainerValue (imod_combine Imod1 Imod2)"
  proof (elim UnE)
    assume "x \<in> SetContainerValue Imod1"
    then show "x \<in> SetContainerValue (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_setof_atom_values l)
      then show ?case
        using SetContainerValue.rule_setof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_setof_container_values l)
      then show ?case
        using SetContainerValue.rule_setof_container_values imod_combine_container_value_list
        by blast
    qed
  next
    assume "x \<in> SetContainerValue Imod2"
    then show "x \<in> SetContainerValue (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_setof_atom_values l)
      then show ?case
        using SetContainerValue.rule_setof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_setof_container_values l)
      then show ?case
        using SetContainerValue.rule_setof_container_values imod_combine_container_value_list
        by blast
    qed
  qed
qed

lemma imod_combine_seq_container_value: "SeqContainerValue Imod1 \<union> SeqContainerValue Imod2 \<subseteq> SeqContainerValue (imod_combine Imod1 Imod2)"
proof
  fix x
  assume "x \<in> SeqContainerValue Imod1 \<union> SeqContainerValue Imod2"
  then show "x \<in> SeqContainerValue (imod_combine Imod1 Imod2)"
  proof (elim UnE)
    assume "x \<in> SeqContainerValue Imod1"
    then show "x \<in> SeqContainerValue (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_seqof_atom_values l)
      then show ?case
        using SeqContainerValue.rule_seqof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_seqof_container_values l)
      then show ?case
        using SeqContainerValue.rule_seqof_container_values imod_combine_container_value_list
        by blast
    qed
  next
    assume "x \<in> SeqContainerValue Imod2"
    then show "x \<in> SeqContainerValue (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_seqof_atom_values l)
      then show ?case
        using SeqContainerValue.rule_seqof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_seqof_container_values l)
      then show ?case
        using SeqContainerValue.rule_seqof_container_values imod_combine_container_value_list
        by blast
    qed
  qed
qed

lemma imod_combine_ord_container_value: "OrdContainerValue Imod1 \<union> OrdContainerValue Imod2 \<subseteq> OrdContainerValue (imod_combine Imod1 Imod2)"
proof
  fix x
  assume "x \<in> OrdContainerValue Imod1 \<union> OrdContainerValue Imod2"
  then show "x \<in> OrdContainerValue (imod_combine Imod1 Imod2)"
  proof (elim UnE)
    assume "x \<in> OrdContainerValue Imod1"
    then show "x \<in> OrdContainerValue (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_ordof_atom_values l)
      then show ?case
        using OrdContainerValue.rule_ordof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_ordof_container_values l)
      then show ?case
        using OrdContainerValue.rule_ordof_container_values imod_combine_container_value_list
        by blast
    qed
  next
    assume "x \<in> OrdContainerValue Imod2"
    then show "x \<in> OrdContainerValue (imod_combine Imod1 Imod2)"
    proof (induct)
      case (rule_ordof_atom_values l)
      then show ?case
        using OrdContainerValue.rule_ordof_atom_values imod_combine_atom_value_list
        by blast
    next
      case (rule_ordof_container_values l)
      then show ?case
        using OrdContainerValue.rule_ordof_container_values imod_combine_container_value_list
        by blast
    qed
  qed
qed


subsection "Value equivalence after combining instance models"

lemma imod_combine_value_equiv_imod1[simp]: "\<And>x y. x \<equiv>[Imod1] y \<Longrightarrow> x \<equiv>[imod_combine Imod1 Imod2] y"
proof-
  fix x y
  assume "x \<equiv>[Imod1] y"
  then show "x \<equiv>[imod_combine Imod1 Imod2] y"
  proof (induct)
    case (rule_atom_equiv v1 v2)
    then have "v1 \<in> Value (imod_combine Imod1 Imod2)"
      using imod_combine_value rule_atom_equiv.hyps(1)
      by blast
    then show ?case
      using rule_atom_equiv.hyps(3) value_equiv_reflexivity
      by blast
  next
    case (rule_bagof_equiv l1 l2)
    then show ?case
      using value_equiv.rule_bagof_equiv
      by blast
  next
    case (rule_setof_equiv l1 l2)
    then show ?case
      using value_equiv.rule_setof_equiv
      by blast
  next
    case (rule_seqof_equiv l1 l2)
    then show ?case
      using value_equiv.rule_seqof_equiv
      by blast
  next
    case (rule_ordof_equiv l1 l2)
    then show ?case
      using value_equiv.rule_ordof_equiv
      by blast
  qed
qed

lemma imod_combine_value_equiv_imod1_rev[simp]: "\<And>x y. x \<in> Value Imod1 \<Longrightarrow> y \<in> Value Imod1 \<Longrightarrow> x \<equiv>[imod_combine Imod1 Imod2] y \<Longrightarrow> x \<equiv>[Imod1] y"
proof-
  fix x y
  assume x_in_value_imod: "x \<in> Value Imod1"
  assume y_in_value_imod: "y \<in> Value Imod1"
  assume "x \<equiv>[imod_combine Imod1 Imod2] y"
  then show "x \<equiv>[Imod1] y"
    using x_in_value_imod y_in_value_imod
  proof (induct)
    case (rule_atom_equiv v1 v2)
    then show ?case
      by simp
  next
    case (rule_bagof_equiv l1 l2)
    have "l1 \<in> ContainerValueList Imod1 \<or> l1 \<in> AtomValueList Imod1"
      using rule_bagof_equiv.prems(1) Un_iff Value_def contained_list.simps(1) container_value_members_alt no_bags_in_atom_values
      by metis
    then have l1_value_imod1: "\<And>y. y \<in> set l1 \<Longrightarrow> y \<in> Value Imod1"
      using Value_def
      by fastforce
    have "l2 \<in> ContainerValueList Imod1 \<or> l2 \<in> AtomValueList Imod1"
      using rule_bagof_equiv.prems(2) Un_iff Value_def contained_list.simps(1) container_value_members_alt no_bags_in_atom_values
      by metis
    then have "\<And>y. y \<in> set l2 \<Longrightarrow> y \<in> Value Imod1"
      using Value_def
      by fastforce
    then have l2_value_imod1: "\<And>f n. bij_betw f {..<length l1} {..<length l2} \<Longrightarrow> n \<in> {..<length l1} \<Longrightarrow> l2 ! f n \<in> Value Imod1"
      using bij_betwE lessThan_iff nth_mem
      by metis
    show ?case
      using rule_bagof_equiv.hyps l1_value_imod1 l2_value_imod1 lessThan_iff nth_mem value_equiv.rule_bagof_equiv
      by metis
  next
    case (rule_setof_equiv l1 l2)
    have "l1 \<in> ContainerValueList Imod1 \<or> l1 \<in> AtomValueList Imod1"
      using rule_setof_equiv.prems(1) Un_iff Value_def contained_list.simps(2) container_value_members_alt no_sets_in_atom_values
      by metis
    then have l1_value_imod1: "\<And>y. y \<in> set l1 \<Longrightarrow> y \<in> Value Imod1"
      using Value_def
      by fastforce
    have "l2 \<in> ContainerValueList Imod1 \<or> l2 \<in> AtomValueList Imod1"
      using rule_setof_equiv.prems(2) Un_iff Value_def contained_list.simps(2) container_value_members_alt no_sets_in_atom_values
      by metis
    then have "\<And>y. y \<in> set l2 \<Longrightarrow> y \<in> Value Imod1"
      using Value_def
      by fastforce
    then have l2_value_imod1: "\<And>f n. bij_betw f {..<length l1} {..<length l2} \<Longrightarrow> n \<in> {..<length l1} \<Longrightarrow> l2 ! f n \<in> Value Imod1"
      using bij_betwE lessThan_iff nth_mem
      by metis
    show ?case
      using rule_setof_equiv.hyps l1_value_imod1 l2_value_imod1 lessThan_iff nth_mem value_equiv.rule_setof_equiv
      by metis
  next
    case (rule_seqof_equiv l1 l2)
    have "l1 \<in> ContainerValueList Imod1 \<or> l1 \<in> AtomValueList Imod1"
      using rule_seqof_equiv.prems(1) Un_iff Value_def contained_list.simps(3) container_value_members_alt no_seqs_in_atom_values
      by metis
    then have l1_value_imod1: "\<And>y. y \<in> set l1 \<Longrightarrow> y \<in> Value Imod1"
      using Value_def
      by fastforce
    have "l2 \<in> ContainerValueList Imod1 \<or> l2 \<in> AtomValueList Imod1"
      using rule_seqof_equiv.prems(2) Un_iff Value_def contained_list.simps(3) container_value_members_alt no_seqs_in_atom_values
      by metis
    then have l2_value_imod1: "\<And>y. y \<in> set l2 \<Longrightarrow> y \<in> Value Imod1"
      using Value_def
      by fastforce
    show ?case
      using rule_seqof_equiv.hyps l1_value_imod1 l2_value_imod1 lessThan_iff nth_mem value_equiv.rule_seqof_equiv
      by metis
  next
    case (rule_ordof_equiv l1 l2)
    have "l1 \<in> ContainerValueList Imod1 \<or> l1 \<in> AtomValueList Imod1"
      using rule_ordof_equiv.prems(1) Un_iff Value_def contained_list.simps(4) container_value_members_alt no_ords_in_atom_values
      by metis
    then have l1_value_imod1: "\<And>y. y \<in> set l1 \<Longrightarrow> y \<in> Value Imod1"
      using Value_def
      by fastforce
    have "l2 \<in> ContainerValueList Imod1 \<or> l2 \<in> AtomValueList Imod1"
      using rule_ordof_equiv.prems(2) Un_iff Value_def contained_list.simps(4) container_value_members_alt no_ords_in_atom_values
      by metis
    then have l2_value_imod1: "\<And>y. y \<in> set l2 \<Longrightarrow> y \<in> Value Imod1"
      using Value_def
      by fastforce
    show ?case
      using rule_ordof_equiv.hyps l1_value_imod1 l2_value_imod1 lessThan_iff nth_mem value_equiv.rule_ordof_equiv
      by metis
  qed
qed

lemma imod_combine_value_equiv_imod2[simp]: "\<And>x y. x \<equiv>[Imod2] y \<Longrightarrow> x \<equiv>[imod_combine Imod1 Imod2] y"
  using imod_combine_commute imod_combine_value_equiv_imod1
  by metis

lemma imod_combine_value_equiv_imod2_rev[simp]: "\<And>x y. x \<in> Value Imod2 \<Longrightarrow> y \<in> Value Imod2 \<Longrightarrow> x \<equiv>[imod_combine Imod1 Imod2] y \<Longrightarrow> x \<equiv>[Imod2] y"
  using imod_combine_commute imod_combine_value_equiv_imod1_rev
  by metis


subsection "Valid type values"

subsubsection "Valid type value relation"

lemma imod_combine_distinct_values_imod1: "\<And>x. x \<in> ContainerValueList Imod1 \<or> x \<in> AtomValueList Imod1 \<Longrightarrow> distinct_values Imod1 x \<Longrightarrow> distinct_values (imod_combine Imod1 Imod2) x"
proof-
  fix x
  assume distinct_values_imod: "distinct_values Imod1 x"
  assume x_in_container_values: "x \<in> ContainerValueList Imod1 \<or> x \<in> AtomValueList Imod1"
  then show "distinct_values (imod_combine Imod1 Imod2) x"
  proof (elim disjE)
    assume "x \<in> ContainerValueList Imod1"
    then show ?thesis
      using distinct_values_imod
    proof (induct x rule: list.induct)
      case Nil
      then show ?case
        by simp
    next
      case (Cons a x)
      then have list_subset_value_imod: "\<And>y. y \<in> set (a # x) \<Longrightarrow> y \<in> Value Imod1"
        using Un_iff Value_def container_value_list_members_alt
        by metis
      have "\<And>y. y \<in> set x \<Longrightarrow> \<not>(a \<equiv>[Imod1] y)"
        using Cons.prems(2) distinct_values.simps(2)
        by blast
      then have "\<And>y. y \<in> set x \<Longrightarrow> \<not>(a \<equiv>[imod_combine Imod1 Imod2] y)"
        using imod_combine_value_equiv_imod1_rev insert_iff list.simps(15) list_subset_value_imod
        by metis
      then show ?case
        using Cons.hyps Cons.prems(1) Cons.prems(2) ContainerValueList.simps
        by auto
    qed
  next
    assume "x \<in> AtomValueList Imod1"
    then show ?thesis
      using distinct_values_imod
    proof (induct x rule: list.induct)
      case Nil
      then show ?case
        by simp
    next
      case (Cons a x)
      then have list_subset_value_imod: "\<And>y. y \<in> set (a # x) \<Longrightarrow> y \<in> Value Imod1"
        using Un_iff Value_def atom_value_list_members
        by metis
      have "\<And>y. y \<in> set x \<Longrightarrow> \<not>(a \<equiv>[Imod1] y)"
        using Cons.prems(2) distinct_values.simps(2)
        by blast
      then have "\<And>y. y \<in> set x \<Longrightarrow> \<not>(a \<equiv>[imod_combine Imod1 Imod2] y)"
        using imod_combine_value_equiv_imod1_rev insert_iff list.simps(15) list_subset_value_imod
        by metis
      then show ?case
        using AtomValueList.simps Cons.hyps Cons.prems(1) Cons.prems(2) distinct_values.simps(1) distinct_values.simps(2) list.inject
        by metis
    qed
  qed
qed

lemma imod_combine_distinct_values_imod1_rev: "\<And>x. distinct_values (imod_combine Imod1 Imod2) x \<Longrightarrow> distinct_values Imod1 x"
proof-
  fix x
  assume "distinct_values (imod_combine Imod1 Imod2) x"
  then show "distinct_values Imod1 x"
  proof (induct x)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a x)
    then show ?case
      using distinct_values.simps(2) imod_combine_value_equiv_imod1
      by blast
  qed
qed

lemma imod_combine_distinct_values_imod2: "\<And>x. x \<in> ContainerValueList Imod2 \<or> x \<in> AtomValueList Imod2 \<Longrightarrow> distinct_values Imod2 x \<Longrightarrow> distinct_values (imod_combine Imod1 Imod2) x"
  using imod_combine_commute imod_combine_distinct_values_imod1
  by metis

lemma imod_combine_distinct_values_imod2_rev: "\<And>x. distinct_values (imod_combine Imod1 Imod2) x \<Longrightarrow> distinct_values Imod2 x"
  using imod_combine_commute imod_combine_distinct_values_imod1_rev
  by metis

lemma imod_combine_valid_rel_imod1:
  assumes instance_types_eq: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  shows "\<And>t v. (t, v) \<in> Valid_rel Imod1 \<Longrightarrow> (t, v) \<in> Valid_rel (imod_combine Imod1 Imod2)"
proof-
  fix t v
  assume "(t, v) \<in> Valid_rel Imod1"
  then show "(t, v) \<in> Valid_rel (imod_combine Imod1 Imod2)"
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      by (fact Valid_rel.valid_rule_booleans)
  next
  case (valid_rule_integers v)
  then show ?case
    by (fact Valid_rel.valid_rule_integers)
  next
    case (valid_rule_reals v)
    then show ?case
      by (fact Valid_rel.valid_rule_reals)
  next
    case (valid_rule_strings v)
    then show ?case
      by (fact Valid_rel.valid_rule_strings)
  next
    case (valid_rule_proper_classes v t)
    have "v \<in> Object Imod1 \<union> Object Imod2"
      by (simp add: valid_rule_proper_classes.hyps(1))
    then have v_in_combination: "v \<in> Object (imod_combine Imod1 Imod2)"
      by (simp add: imod_combine_def)
    have "t \<in> ClassType (Tm Imod1) \<union> ClassType (Tm Imod2)"
      by (simp add: valid_rule_proper_classes.hyps(2))
    then have "t \<in> ClassType (tmod_combine (Tm Imod1) (Tm Imod2))"
      by simp
    then have t_in_combination: "t \<in> ClassType (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def)
    have "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) v) \<sqsubseteq>[Tm Imod1] t"
      using Int_iff imod_combine_def imod_combine_object_class_def instance_model.simps(3) instance_types_eq valid_rule_proper_classes.hyps(1) valid_rule_proper_classes.hyps(3)
      by metis
    then have "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) v) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] t"
      by (fact tmod_combine_subtype_subset_tmod1)
    then show ?case
      using Valid_rel.valid_rule_proper_classes imod_combine_def instance_model.simps(1) t_in_combination v_in_combination
      by metis
  next
    case (valid_rule_nullable_classes t)
    then have "t \<in> NullableClassType (Tm Imod1) \<union> NullableClassType (Tm Imod2)"
      by simp
    then have "t \<in> NullableClassType (tmod_combine (Tm Imod1) (Tm Imod2))"
      by simp
    then have "t \<in> NullableClassType (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def)
    then show ?case
      by (fact Valid_rel.valid_rule_nullable_classes)
  next
    case (valid_rule_enumvalues t v)
    have "(t, v) \<in> EnumValue (Tm Imod1) \<union> EnumValue (Tm Imod2)"
      by (simp add: valid_rule_enumvalues.hyps(1))
    then have "(t, v) \<in> EnumValue (tmod_combine (Tm Imod1) (Tm Imod2))"
      by (simp add: tmod_combine_def)
    then have tv_in_combination: "(t, v) \<in> EnumValue (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def)
    have "enumtype t \<in> EnumType (Tm Imod1) \<union> EnumType (Tm Imod2)"
      by (simp add: valid_rule_enumvalues.hyps(2))
    then have "enumtype t \<in> EnumType (tmod_combine (Tm Imod1) (Tm Imod2))"
      by simp
    then have t_in_combination: "enumtype t \<in> EnumType (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def)
    show ?case
      using tv_in_combination t_in_combination
      by (fact Valid_rel.valid_rule_enumvalues)
  next
    case (valid_rule_userdata_values v t)
    then have "t \<in> UserDataTypeType (Tm Imod1) \<union> UserDataTypeType (Tm Imod2)"
      by simp
    then have "t \<in> UserDataTypeType (tmod_combine (Tm Imod1) (Tm Imod2))"
      by simp
    then have t_in_combination: "t \<in> UserDataTypeType (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def)
    show ?case
      using valid_rule_userdata_values.hyps(1) t_in_combination
      by (fact Valid_rel.valid_rule_userdata_values)
  next
    case (valid_rule_bags t vs)
    have "t \<in> BagContainerType (Tm Imod1) \<union> BagContainerType (Tm Imod2)"
      by (simp add: valid_rule_bags.hyps(1))
    then have "t \<in> BagContainerType (tmod_combine (Tm Imod1) (Tm Imod2))"
      by simp
    then have t_in_combination: "t \<in> BagContainerType (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def)
    have "vs \<in> BagContainerValue Imod1 \<union> BagContainerValue Imod2"
      by (simp add: valid_rule_bags.hyps(2))
    then have vs_in_combination: "vs \<in> BagContainerValue (imod_combine Imod1 Imod2)"
      using imod_combine_bag_container_value
      by blast
    show ?case
      using t_in_combination vs_in_combination valid_rule_bags.hyps(4)
      by (fact Valid_rel.valid_rule_bags)
  next
    case (valid_rule_sets t vs)
    have "t \<in> SetContainerType (Tm Imod1) \<union> SetContainerType (Tm Imod2)"
      by (simp add: valid_rule_sets.hyps(1))
    then have "t \<in> SetContainerType (tmod_combine (Tm Imod1) (Tm Imod2))"
      by simp
    then have t_in_combination: "t \<in> SetContainerType (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def)
    have "vs \<in> SetContainerValue Imod1 \<union> SetContainerValue Imod2"
      by (simp add: valid_rule_sets.hyps(2))
    then have vs_in_combination: "vs \<in> SetContainerValue (imod_combine Imod1 Imod2)"
      using imod_combine_set_container_value
      by blast
    have "contained_list vs \<in> ContainerValueList Imod1 \<or> contained_list vs \<in> AtomValueList Imod1"
      using set_container_values_member valid_rule_sets.hyps(2)
      by blast
    then have combination_distinct: "distinct_values (imod_combine Imod1 Imod2) (contained_list vs)"
      using imod_combine_distinct_values_imod1 valid_rule_sets.hyps(3)
      by blast
    show ?case
      using t_in_combination vs_in_combination combination_distinct valid_rule_sets.hyps(5)
      by (fact Valid_rel.valid_rule_sets)
  next
    case (valid_rule_seqs t vs)
    have "t \<in> SeqContainerType (Tm Imod1) \<union> SeqContainerType (Tm Imod2)"
      by (simp add: valid_rule_seqs.hyps(1))
    then have "t \<in> SeqContainerType (tmod_combine (Tm Imod1) (Tm Imod2))"
      by simp
    then have t_in_combination: "t \<in> SeqContainerType (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def)
    have "vs \<in> SeqContainerValue Imod1 \<union> SeqContainerValue Imod2"
      by (simp add: valid_rule_seqs.hyps(2))
    then have vs_in_combination: "vs \<in> SeqContainerValue (imod_combine Imod1 Imod2)"
      using imod_combine_seq_container_value
      by blast
    show ?case
      using t_in_combination vs_in_combination valid_rule_seqs.hyps(4)
      by (fact Valid_rel.valid_rule_seqs)
  next
    case (valid_rule_ords t vs)
    have "t \<in> OrdContainerType (Tm Imod1) \<union> OrdContainerType (Tm Imod2)"
      by (simp add: valid_rule_ords.hyps(1))
    then have "t \<in> OrdContainerType (tmod_combine (Tm Imod1) (Tm Imod2))"
      by simp
    then have t_in_combination: "t \<in> OrdContainerType (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def)
    have "vs \<in> OrdContainerValue Imod1 \<union> OrdContainerValue Imod2"
      by (simp add: valid_rule_ords.hyps(2))
    then have vs_in_combination: "vs \<in> OrdContainerValue (imod_combine Imod1 Imod2)"
      using imod_combine_ord_container_value
      by blast
    have "contained_list vs \<in> ContainerValueList Imod1 \<or> contained_list vs \<in> AtomValueList Imod1"
      using ord_container_values_member valid_rule_ords.hyps(2)
      by blast
    then have combination_distinct: "distinct_values (imod_combine Imod1 Imod2) (contained_list vs)"
      using imod_combine_distinct_values_imod1 valid_rule_ords.hyps(3)
      by blast
    show ?case
      using t_in_combination vs_in_combination combination_distinct valid_rule_ords.hyps(5)
      by (fact Valid_rel.valid_rule_ords)
  qed
qed

lemma imod_combine_valid_rel_imod1_rev:
  assumes instance_types_eq: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes inheritance_rev: "\<And>v t. v \<in> Object Imod1 \<Longrightarrow> t \<in> ClassType (Tm Imod1) \<Longrightarrow> \<exclamdown>(ObjectClass Imod1 v) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] t \<Longrightarrow> \<exclamdown>(ObjectClass Imod1 v) \<sqsubseteq>[Tm Imod1] t"
  shows "\<And>v t. t \<in> Type (Tm Imod1) \<Longrightarrow> v \<in> Value Imod1 \<Longrightarrow> (t, v) \<in> Valid_rel (imod_combine Imod1 Imod2) \<Longrightarrow> (t, v) \<in> Valid_rel Imod1"
proof-
  fix t v
  assume t_in_type_tmod: "t \<in> Type (Tm Imod1)"
  assume v_in_value_imod: "v \<in> Value Imod1"
  assume "(t, v) \<in> Valid_rel (imod_combine Imod1 Imod2)"
  then show "(t, v) \<in> Valid_rel Imod1"
    using t_in_type_tmod v_in_value_imod
  proof (induct)
    case (valid_rule_booleans v)
    then show ?case
      by (simp add: Valid_rel.valid_rule_booleans)
  next
    case (valid_rule_integers v)
    then show ?case
      by (simp add: Valid_rel.valid_rule_integers)
  next
    case (valid_rule_reals v)
    then show ?case
      by (simp add: Valid_rel.valid_rule_reals)
  next
    case (valid_rule_strings v)
    then show ?case
      by (simp add: Valid_rel.valid_rule_strings)
  next
    case (valid_rule_proper_classes v t)
    have "obj v \<in> ProperClassValue Imod1"
      using valid_rule_proper_classes.prems(2)
      by (simp add: AtomValue_def ClassValue_def Value_def)
    then have v_in_object_imod: "v \<in> Object Imod1"
      using ProperClassValue.cases valid_rule_proper_classes.hyps(1)
      by blast
    have t_in_classtype_tmod: "t \<in> ClassType (Tm Imod1)"
      using valid_rule_proper_classes.prems(1) valid_rule_proper_classes.hyps(2) valid_rule_proper_classes.hyps(3)
      using class_type_member container_type_contains_no_nullable_classes container_type_contains_no_proper_classes 
      using datatype_contains_no_proper_classes enum_type_contains_no_nullable_classes enum_type_contains_no_proper_classes 
      using non_container_type_not_member subtype_datatypes_no_subtypes type_not_member 
      using userdatatype_type_contains_no_nullable_classes userdatatype_type_contains_no_proper_classes
      by metis
    have "ObjectClass (imod_combine Imod1 Imod2) v = ObjectClass Imod1 v"
      by (simp add: imod_combine_def imod_combine_object_class_def instance_types_eq v_in_object_imod)
    then have "\<exclamdown>(ObjectClass Imod1 v) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] t"
      using imod_combine_def instance_model.simps(1) valid_rule_proper_classes.hyps(3)
      by metis
    then have "\<exclamdown>(ObjectClass Imod1 v) \<sqsubseteq>[Tm Imod1] t"
      using v_in_object_imod t_in_classtype_tmod inheritance_rev
      by simp
    then show ?case
      by (simp add: Valid_rel.valid_rule_proper_classes t_in_classtype_tmod v_in_object_imod)
  next
    case (valid_rule_nullable_classes t)
    then have "t \<in> NullableClassType (Tm Imod1)"
      using class_type_not_member container_type_contains_no_nullable_classes disjoint_iff_not_equal 
      using enum_type_contains_no_nullable_classes non_container_type_not_member nullable_class_type_contains_no_proper_classes 
      using nullable_class_type_datatype_intersect nullable_class_type_member proper_class_type_member 
      using type_not_member userdatatype_type_contains_no_nullable_classes
      by metis
    then show ?case
      by (fact Valid_rel.valid_rule_nullable_classes)
  next
    case (valid_rule_enumvalues t v)
    have "enum (t, v) \<in> EnumValueValue (Tm Imod1)"
      using valid_rule_enumvalues.prems(2)
      by (simp add: AtomValue_def EnumValueValue.simps Value_def)
    then have tv_in_enumvalue_tmod: "(t, v) \<in> EnumValue (Tm Imod1)"
      by (simp add: EnumValueValue.simps)
    have t_in_enumtype_tmod: "enumtype t \<in> EnumType (Tm Imod1)"
      using class_type_contains_no_enumtypes container_type_contains_no_enumtypes datatype_contains_no_enumtypes 
      using non_container_type_not_member type_not_member userdatatype_type_contains_no_enumtypes valid_rule_enumvalues.prems(1)
      by blast
    show ?case
      using tv_in_enumvalue_tmod t_in_enumtype_tmod
      by (fact Valid_rel.valid_rule_enumvalues)
  next
    case (valid_rule_userdata_values v t)
    then have "\<exists>u. t = userdatatype u"
      using userdatatype_type_member
      by blast
    then have t_in_userdatatypetype: "t \<in> UserDataTypeType (Tm Imod1)"
      using valid_rule_userdata_values.prems(1)
      unfolding Type_def NonContainerType_def
      by fastforce
    show ?case
      using valid_rule_userdata_values.hyps(1) t_in_userdatatypetype
      by (fact Valid_rel.valid_rule_userdata_values)
  next
    case (valid_rule_bags t vs)
    have vs_in_imod: "vs \<in> BagContainerValue Imod1"
      using BagContainerValue.simps UnE Value_def contained_list.simps(1) container_value_members_alt 
      using no_bags_in_atom_values valid_rule_bags.hyps(2) valid_rule_bags.prems(2)
      by metis
    then have vs_members_in_imod: "\<And>y. y \<in> set (contained_list vs) \<Longrightarrow> y \<in> Value Imod1"
      using Value_def atom_value_list_members bag_container_values_member
      by fastforce
    have "\<exists>s. t = TypeDef.bagof s"
      using bag_types_typedef valid_rule_bags.hyps(1)
      by blast
    then have t_in_tmod: "t \<in> BagContainerType (Tm Imod1)"
      using BagContainerType.rule_bagof_all_type Un_iff attribute_bags_have_attribute_types 
      using relation_bags_have_relation_types_alt relations_and_attributes_are_types_alt valid_rule_bags.prems(1)
      by metis
    then have contained_type_t_in_tmod: "contained_type t \<in> Type (Tm Imod1)"
      using BagContainerType.simps contained_type.simps(1)
      by metis
    show ?case
      using Valid_rel.valid_rule_bags contained_type_t_in_tmod t_in_tmod valid_rule_bags.hyps(4) vs_in_imod vs_members_in_imod
      by blast
  next
    case (valid_rule_sets t vs)
    have vs_in_imod: "vs \<in> SetContainerValue Imod1"
      using SetContainerValue.simps UnE Value_def contained_list.simps(2) container_value_members_alt 
      using no_sets_in_atom_values valid_rule_sets.hyps(2) valid_rule_sets.prems(2)
      by metis
    then have vs_members_in_imod: "\<And>y. y \<in> set (contained_list vs) \<Longrightarrow> y \<in> Value Imod1"
      using Value_def atom_value_list_members set_container_values_member
      by fastforce
    have "\<exists>s. t = TypeDef.setof s"
      using set_types_typedef valid_rule_sets.hyps(1)
      by blast
    then have t_in_tmod: "t \<in> SetContainerType (Tm Imod1)"
      using SetContainerType.rule_setof_all_type Un_iff attribute_sets_have_attribute_types 
      using relation_sets_have_relation_types_alt relations_and_attributes_are_types_alt valid_rule_sets.prems(1)
      by metis
    then have contained_type_t_in_tmod: "contained_type t \<in> Type (Tm Imod1)"
      using SetContainerType.simps contained_type.simps(2)
      by metis
    have "distinct_values Imod1 (contained_list vs)"
      using valid_rule_sets.hyps(3)
      by (fact imod_combine_distinct_values_imod1_rev)
    then show ?case
      using Valid_rel.valid_rule_sets contained_type_t_in_tmod t_in_tmod valid_rule_sets.hyps(5) vs_in_imod vs_members_in_imod
      by blast
  next
    case (valid_rule_seqs t vs)
    have vs_in_imod: "vs \<in> SeqContainerValue Imod1"
      using SeqContainerValue.simps UnE Value_def contained_list.simps(3) container_value_members_alt 
      using no_seqs_in_atom_values valid_rule_seqs.hyps(2) valid_rule_seqs.prems(2)
      by metis
    then have vs_members_in_imod: "\<And>y. y \<in> set (contained_list vs) \<Longrightarrow> y \<in> Value Imod1"
      using Value_def atom_value_list_members seq_container_values_member
      by fastforce
    have "\<exists>s. t = TypeDef.seqof s"
      using seq_types_typedef valid_rule_seqs.hyps(1)
      by blast
    then have t_in_tmod: "t \<in> SeqContainerType (Tm Imod1)"
      using SeqContainerType.rule_seqof_all_type Un_iff attribute_seqs_have_attribute_types 
      using relation_seqs_have_relation_types_alt relations_and_attributes_are_types_alt valid_rule_seqs.prems(1)
      by metis
    then have contained_type_t_in_tmod: "contained_type t \<in> Type (Tm Imod1)"
      using SeqContainerType.simps contained_type.simps(3)
      by metis
    show ?case
      using Valid_rel.valid_rule_seqs contained_type_t_in_tmod t_in_tmod valid_rule_seqs.hyps(4) vs_in_imod vs_members_in_imod
      by blast
  next
    case (valid_rule_ords t vs)
    have vs_in_imod: "vs \<in> OrdContainerValue Imod1"
      using OrdContainerValue.simps UnE Value_def contained_list.simps(4) container_value_members_alt 
      using no_ords_in_atom_values valid_rule_ords.hyps(2) valid_rule_ords.prems(2)
      by metis
    then have vs_members_in_imod: "\<And>y. y \<in> set (contained_list vs) \<Longrightarrow> y \<in> Value Imod1"
      using Value_def atom_value_list_members ord_container_values_member
      by fastforce
    have "\<exists>s. t = TypeDef.ordof s"
      using ord_types_typedef valid_rule_ords.hyps(1)
      by blast
    then have t_in_tmod: "t \<in> OrdContainerType (Tm Imod1)"
      using OrdContainerType.rule_ordof_all_type Un_iff attribute_ords_have_attribute_types 
      using relation_ords_have_relation_types_alt relations_and_attributes_are_types_alt valid_rule_ords.prems(1)
      by metis
    then have contained_type_t_in_tmod: "contained_type t \<in> Type (Tm Imod1)"
      using OrdContainerType.simps contained_type.simps(4)
      by metis
    have "distinct_values Imod1 (contained_list vs)"
      using valid_rule_ords.hyps(3)
      by (fact imod_combine_distinct_values_imod1_rev)
    then show ?case
      using Valid_rel.valid_rule_ords contained_type_t_in_tmod t_in_tmod valid_rule_ords.hyps(5) vs_in_imod vs_members_in_imod
      by blast
  qed
qed

lemma imod_combine_valid_rel_imod2:
  assumes instance_types_eq: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  shows "\<And>t v. (t, v) \<in> Valid_rel Imod2 \<Longrightarrow> (t, v) \<in> Valid_rel (imod_combine Imod1 Imod2)"
  using imod_combine_commute imod_combine_valid_rel_imod1 instance_types_eq
  by metis

lemma imod_combine_valid_rel_imod2_rev:
  assumes instance_types_eq: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes inheritance_rev: "\<And>v t. v \<in> Object Imod2 \<Longrightarrow> t \<in> ClassType (Tm Imod2) \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 v) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] t \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 v) \<sqsubseteq>[Tm Imod2] t"
  shows "\<And>v t. t \<in> Type (Tm Imod2) \<Longrightarrow> v \<in> Value Imod2 \<Longrightarrow> (t, v) \<in> Valid_rel (imod_combine Imod1 Imod2) \<Longrightarrow> (t, v) \<in> Valid_rel Imod2"
  using imod_combine_commute imod_combine_valid_rel_imod1_rev inheritance_rev instance_types_eq tmod_combine_commute
  by metis


subsubsection "Valid type value function"

lemma imod_combine_valid_imod1:
  assumes instance_types_eq: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes inh_wellformed_classes_tmod1: "\<And>c. c \<in> Inh (Tm Imod1) \<Longrightarrow> fst c \<in> Class (Tm Imod1) \<and> snd c \<in> Class (Tm Imod1)"
  assumes inh_wellformed_classes_tmod2: "\<And>c. c \<in> Inh (Tm Imod2) \<Longrightarrow> fst c \<in> Class (Tm Imod2) \<and> snd c \<in> Class (Tm Imod2)"
  shows "v :[Imod1] t \<Longrightarrow> v :[imod_combine Imod1 Imod2] t"
  unfolding Valid_def
  using assms imod_combine_valid_rel_imod1
  by blast

lemma imod_combine_valid_imod1_rev:
  assumes instance_types_eq: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes inheritance_rev: "\<And>v t. v \<in> Object Imod1 \<Longrightarrow> t \<in> ClassType (Tm Imod1) \<Longrightarrow> \<exclamdown>(ObjectClass Imod1 v) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] t \<Longrightarrow> \<exclamdown>(ObjectClass Imod1 v) \<sqsubseteq>[Tm Imod1] t"
  shows "t \<in> Type (Tm Imod1) \<Longrightarrow> v \<in> Value Imod1 \<Longrightarrow> v :[imod_combine Imod1 Imod2] t \<Longrightarrow> v :[Imod1] t"
  unfolding Valid_def
  using assms imod_combine_valid_rel_imod1_rev
  by blast

lemma imod_combine_valid_imod2:
  assumes instance_types_eq: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes inh_wellformed_classes_tmod1: "\<And>c. c \<in> Inh (Tm Imod1) \<Longrightarrow> fst c \<in> Class (Tm Imod1) \<and> snd c \<in> Class (Tm Imod1)"
  assumes inh_wellformed_classes_tmod2: "\<And>c. c \<in> Inh (Tm Imod2) \<Longrightarrow> fst c \<in> Class (Tm Imod2) \<and> snd c \<in> Class (Tm Imod2)"
  shows "v :[Imod2] t \<Longrightarrow> v :[imod_combine Imod1 Imod2] t"
  unfolding Valid_def
  using assms imod_combine_valid_rel_imod2
  by blast

lemma imod_combine_valid_imod2_rev:
  assumes instance_types_eq: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes inheritance_rev: "\<And>v t. v \<in> Object Imod2 \<Longrightarrow> t \<in> ClassType (Tm Imod2) \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 v) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] t \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 v) \<sqsubseteq>[Tm Imod2] t"
  shows "t \<in> Type (Tm Imod2) \<Longrightarrow> v \<in> Value Imod2 \<Longrightarrow> v :[imod_combine Imod1 Imod2] t \<Longrightarrow> v :[Imod2] t"
  unfolding Valid_def
  using assms imod_combine_valid_rel_imod2_rev
  by blast


subsection "Proofs related to value edges"

lemma imod_combine_valid_mul_imod1:
  assumes instance_types_eq: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
  assumes fieldvalue_wellformed: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> ob \<notin> Object Imod2 \<or> \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow>
    FieldValue Imod1 (ob, f) \<in> ContainerValue Imod1 \<Longrightarrow>
    Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and>
    \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
  shows "ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> 
    ob \<notin> Object Imod2 \<or> f \<notin> Field (Tm Imod2) \<or> \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> FieldValue Imod1 (ob, f) \<in> Value Imod1 \<Longrightarrow>
    validMul Imod1 ((ob, f), FieldValue Imod1 (ob, f)) \<Longrightarrow> validMul (imod_combine Imod1 Imod2) ((ob, f), FieldValue Imod1 (ob, f))"
  unfolding validMul_def
proof
  assume f_in_field: "f \<in> Field (Tm Imod1)"
  then have fieldsig_def: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = fst (FieldSig (Tm Imod1) f)"
    unfolding tmod_combine_fieldsig_def
    using fieldsig_wellformed
    by simp
  assume "snd ((ob, f), FieldValue Imod1 (ob, f)) :[Imod1] type (Tm Imod1) (snd (fst ((ob, f), FieldValue Imod1 (ob, f)))) \<and> 
    (snd ((ob, f), FieldValue Imod1 (ob, f)) \<in> ContainerValue Imod1 \<longrightarrow>
    lower (Tm Imod1) (snd (fst ((ob, f), FieldValue Imod1 (ob, f)))) \<le> \<^bold>(length (contained_list (snd ((ob, f), FieldValue Imod1 (ob, f))))) \<and>
    \<^bold>(length (contained_list (snd ((ob, f), FieldValue Imod1 (ob, f))))) \<le> upper (Tm Imod1) (snd (fst ((ob, f), FieldValue Imod1 (ob, f)))))"
  then have "FieldValue Imod1 (ob, f) :[Imod1] fst (FieldSig (Tm Imod1) f)"
    unfolding type_def
    by simp
  then have valid_in_combination: "FieldValue Imod1 (ob, f) :[imod_combine Imod1 Imod2] fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f)"
    by (simp add: Valid_def fieldsig_def imod_combine_valid_rel_imod1 instance_types_eq)
  then have "FieldValue Imod1 (ob, f) :[imod_combine Imod1 Imod2] fst (FieldSig (Tm (imod_combine Imod1 Imod2)) f)"
    by (simp add: imod_combine_def tmod_combine_def)
  then show "snd ((ob, f), FieldValue Imod1 (ob, f)) :[imod_combine Imod1 Imod2] type (Tm (imod_combine Imod1 Imod2)) (snd (fst ((ob, f), FieldValue Imod1 (ob, f))))"
    unfolding type_def
    by simp
next
  assume ob_in_object: "ob \<in> Object Imod1"
  assume f_in_field: "f \<in> Field (Tm Imod1)"
  assume subtype: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assume no_value_imod: "ob \<notin> Object Imod2 \<or> f \<notin> Field (Tm Imod2) \<or> \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assume value_in_imod: "FieldValue Imod1 (ob, f) \<in> Value Imod1"
  have container_value: "FieldValue Imod1 (ob, f) \<in> ContainerValue (imod_combine Imod1 Imod2) \<Longrightarrow> FieldValue Imod1 (ob, f) \<in> ContainerValue Imod1"
  proof-
    assume "FieldValue Imod1 (ob, f) \<in> ContainerValue (imod_combine Imod1 Imod2)"
    then have "FieldValue Imod1 (ob, f) \<notin> AtomValue Imod1"
      using container_values_atom_values_intersect
      by blast
    then show "FieldValue Imod1 (ob, f) \<in> ContainerValue Imod1"
      using value_in_imod
      unfolding Value_def
      by simp
  qed
  assume "snd ((ob, f), FieldValue Imod1 (ob, f)) :[Imod1] type (Tm Imod1) (snd (fst ((ob, f), FieldValue Imod1 (ob, f)))) \<and> (snd ((ob, f), FieldValue Imod1 (ob, f)) \<in> ContainerValue Imod1 \<longrightarrow>
   lower (Tm Imod1) (snd (fst ((ob, f), FieldValue Imod1 (ob, f)))) \<le> \<^bold>(length (contained_list (snd ((ob, f), FieldValue Imod1 (ob, f))))) \<and>
   \<^bold>(length (contained_list (snd ((ob, f), FieldValue Imod1 (ob, f))))) \<le> upper (Tm Imod1) (snd (fst ((ob, f), FieldValue Imod1 (ob, f)))))"
  then have "FieldValue Imod1 (ob, f) \<in> ContainerValue Imod1 \<longrightarrow> lower (Tm Imod1) f \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> upper (Tm Imod1) f"
    by simp
  then have "FieldValue Imod1 (ob, f) \<in> ContainerValue Imod1 \<longrightarrow> 
    Multiplicity.lower (snd (FieldSig (Tm Imod1) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and> 
    \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f))"
    unfolding lower_def upper_def
    by simp
  then have "FieldValue Imod1 (ob, f) \<in> ContainerValue (imod_combine Imod1 Imod2) \<longrightarrow> 
    Multiplicity.lower (snd (FieldSig (Tm Imod1) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and> 
    \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f))"
    using container_value
    by simp
  then have "FieldValue Imod1 (ob, f) \<in> ContainerValue (imod_combine Imod1 Imod2) \<longrightarrow>
    Multiplicity.lower (snd (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and> 
    \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> Multiplicity.upper (snd (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f))"
  proof (induct "f \<in> Field (Tm Imod2)")
    case True
    then show ?case
      unfolding tmod_combine_fieldsig_def
      using f_in_field container_value fieldsig_wellformed fieldvalue_wellformed no_value_imod ob_in_object subtype
      by auto
  next
    case False
    then show ?case
      unfolding tmod_combine_fieldsig_def
      using f_in_field
      by simp
  qed
  then have "FieldValue Imod1 (ob, f) \<in> ContainerValue (imod_combine Imod1 Imod2) \<longrightarrow>
    lower (Tm (imod_combine Imod1 Imod2)) f \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> upper (Tm (imod_combine Imod1 Imod2)) f"
    unfolding lower_def upper_def
    by (simp add: tmod_combine_def imod_combine_def)
  then show "snd ((ob, f), (FieldValue Imod1 (ob, f))) \<in> ContainerValue (imod_combine Imod1 Imod2) \<longrightarrow>
    lower (Tm (imod_combine Imod1 Imod2)) (snd (fst ((ob, f), (FieldValue Imod1 (ob, f))))) \<le> \<^bold>(length (contained_list (snd ((ob, f), (FieldValue Imod1 (ob, f)))))) \<and>
    \<^bold>(length (contained_list (snd ((ob, f), (FieldValue Imod1 (ob, f)))))) \<le> upper (Tm (imod_combine Imod1 Imod2)) (snd (fst ((ob, f), (FieldValue Imod1 (ob, f)))))"
    by simp
qed

lemma imod_combine_valid_mul_imod2:
  assumes instance_types_eq: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
  assumes fieldvalue_wellformed: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> ob \<notin> Object Imod1 \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow>
    FieldValue Imod2 (ob, f) \<in> ContainerValue Imod2 \<Longrightarrow>
    Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<and>
    \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
  shows "ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> 
    ob \<notin> Object Imod1 \<or> f \<notin> Field (Tm Imod1) \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> FieldValue Imod2 (ob, f) \<in> Value Imod2 \<Longrightarrow> 
    validMul Imod2 ((ob, f), FieldValue Imod2 (ob, f)) \<Longrightarrow> validMul (imod_combine Imod1 Imod2) ((ob, f), FieldValue Imod2 (ob, f))"
proof-
  assume ob_in_imod2: "ob \<in> Object Imod2"
  assume f_in_imod2: "f \<in> Field (Tm Imod2)"
  assume subtype_imod2: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assume no_value_imod1: "ob \<notin> Object Imod1 \<or> f \<notin> Field (Tm Imod1) \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assume value_imod2: "FieldValue Imod2 (ob, f) \<in> Value Imod2"
  assume valid_mul_imod2: "validMul Imod2 ((ob, f), FieldValue Imod2 (ob, f))"
  have "validMul (imod_combine Imod2 Imod1) ((ob, f), FieldValue Imod2 (ob, f))"
  proof (intro imod_combine_valid_mul_imod1)
    show "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
      \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> ob \<notin> Object Imod1 \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow>
      FieldValue Imod2 (ob, f) \<in> ContainerValue Imod2 \<Longrightarrow>
      Multiplicity.lower (snd (FieldSig (Tm Imod2) f) \<sqinter> snd (FieldSig (Tm Imod1) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<and>
      \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod2) f) \<sqinter> snd (FieldSig (Tm Imod1) f))"
      using fieldvalue_wellformed
      by simp
  next
    show "ob \<notin> Object Imod1 \<or> f \<notin> type_model.Field (Tm Imod1) \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
      by (fact no_value_imod1)
  qed (simp_all add: ob_in_imod2 f_in_imod2 subtype_imod2 value_imod2 valid_mul_imod2 assms)
  then show "validMul (imod_combine Imod1 Imod2) ((ob, f), FieldValue Imod2 (ob, f))"
    by (simp add: imod_combine_commute)
qed


subsection "Proofs related to property satisfaction"

lemma imod_combine_object_containments_subset_imod1:
  assumes object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes fieldsig_wellformed_type_tmod1: "\<And>f. f \<in> Field (Tm Imod1) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) \<in> Type (Tm Imod1)"
  assumes fieldsig_wellformed_type_tmod2: "\<And>f. f \<in> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod2) f) \<in> Type (Tm Imod2)"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
  assumes field_values_wellformed: "\<And>ob f. ob \<in> Object Imod1 \<inter> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> 
    FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)"
  assumes field_values_outside_domain: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> 
    \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> FieldValue Imod2 (ob, f) = unspecified"
  shows "object_containments Imod1 ob \<subseteq> object_containments (imod_combine Imod1 Imod2) ob"
proof
  fix x
  assume "x \<in> object_containments Imod1 ob"
  then show "x \<in> object_containments (imod_combine Imod1 Imod2) ob"
  proof (induct x)
    case (Pair abc d)
    then show ?case
    proof (induct abc)
      case (fields a b c)
      then show ?case
      proof (induct)
        case (rule_object_containment o1 r)
        then have r_in_imod1: "r \<in> Field (Tm Imod1)"
          by simp
        have o1_in_combination: "o1 \<in> Object (imod_combine Imod1 Imod2)"
          by (simp add: imod_combine_def rule_object_containment.hyps(1))
        have "r \<in> CR (tmod_combine (Tm Imod1) (Tm Imod2))"
          using assms tmod_combine_containment_relation_subset_tmod1 rule_object_containment.hyps(2)
          by blast
        then have r_in_combination: "r \<in> CR (Tm (imod_combine Imod1 Imod2))"
          by (simp add: imod_combine_def)
        then have r_in_combination_field: "r \<in> Field (Tm (imod_combine Imod1 Imod2))"
          using containment_relations_are_fields
          by blast
        have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: rule_object_containment.hyps(1) object_class_wellformed)
        then have object_class_o1_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        have subtype_imod1: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r)"
          using rule_object_containment.hyps(3)
          unfolding Type_Model.fields_def class_def
          by fastforce
        then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r)"
          using class_def imod_combine_def instance_model.select_convs(1) tmod_combine_commute tmod_combine_subtype_subset_tmod2
          by metis
        then have "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r)"
          by (simp add: object_class_o1_def)
        then have r_in_combination_fields: "r \<in> Type_Model.fields (Tm (imod_combine Imod1 Imod2)) (ObjectClass (imod_combine Imod1 Imod2) o1)"
          unfolding Type_Model.fields_def class_def
          using r_in_combination_field
          by fastforce
        have "imod_combine_field_value Imod1 Imod2 (o1, r) = FieldValue Imod1 (o1, r)"
          unfolding imod_combine_field_value_def
        proof (induct "o1 \<in> Object Imod2 \<and> r \<in> Field (Tm Imod2)")
          case True
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r)")
            case True
            then show ?case
              using field_values_wellformed r_in_imod1 rule_object_containment.hyps(1) subtype_imod1
              by simp
          next
            case False
            then show ?case
              using field_values_outside_domain r_in_imod1 rule_object_containment.hyps(1)
              by simp
          qed
        next
          case False
          then show ?case
            by (simp add: False.hyps r_in_imod1 rule_object_containment.hyps(1))
        qed
        then have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod1 (o1, r)"
          by (simp add: imod_combine_def)
        then have "obj ob \<in> set (contained_values (FieldValue (imod_combine Imod1 Imod2) (o1, r)))"
          by (simp add: rule_object_containment.hyps(4))
        then show ?case
          by (simp add: object_containments.rule_object_containment o1_in_combination r_in_combination r_in_combination_fields)
      qed
    qed
  qed
qed

lemma imod_combine_object_containments_subset_imod2:
  assumes object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes fieldsig_wellformed_type_tmod1: "\<And>f. f \<in> Field (Tm Imod1) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) \<in> Type (Tm Imod1)"
  assumes fieldsig_wellformed_type_tmod2: "\<And>f. f \<in> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod2) f) \<in> Type (Tm Imod2)"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
  assumes field_values_wellformed: "\<And>ob f. ob \<in> Object Imod1 \<inter> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> 
    FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)"
  assumes field_values_outside_domain: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
    \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> FieldValue Imod1 (ob, f) = unspecified"
  shows "object_containments Imod2 ob \<subseteq> object_containments (imod_combine Imod1 Imod2) ob"
proof-
  have "object_containments Imod2 ob \<subseteq> object_containments (imod_combine Imod2 Imod1) ob"
    by (intro imod_combine_object_containments_subset_imod1) (simp_all add: assms)
  then show "object_containments Imod2 ob \<subseteq> object_containments (imod_combine Imod1 Imod2) ob"
    by (simp add: imod_combine_commute)
qed

lemma imod_combine_object_containments_relation_subset_imod1:
  assumes object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes fieldsig_wellformed_type_tmod1: "\<And>f. f \<in> Field (Tm Imod1) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) \<in> Type (Tm Imod1)"
  assumes fieldsig_wellformed_type_tmod2: "\<And>f. f \<in> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod2) f) \<in> Type (Tm Imod2)"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
  assumes field_values_wellformed: "\<And>ob f. ob \<in> Object Imod1 \<inter> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> 
    FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)"
  assumes field_values_outside_domain: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> 
    \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> FieldValue Imod2 (ob, f) = unspecified"
  shows "object_containments_relation Imod1 \<subseteq> object_containments_relation (imod_combine Imod1 Imod2)"
proof
  fix x
  assume "x \<in> object_containments_relation Imod1"
  then show "x \<in> object_containments_relation (imod_combine Imod1 Imod2)"
  proof (induct x)
    case (Pair a b)
    then show ?case
    proof (induct)
      case (rule_object_containment o1 o2 r)
      then have r_in_imod1: "r \<in> Field (Tm Imod1)"
        by simp
      have o1_in_combination: "o1 \<in> Object (imod_combine Imod1 Imod2)"
        by (simp add: imod_combine_def rule_object_containment.hyps(1))
      have "r \<in> CR (tmod_combine (Tm Imod1) (Tm Imod2))"
        using assms tmod_combine_containment_relation_subset_tmod1 rule_object_containment.hyps(2)
        by blast
      then have r_in_combination: "r \<in> CR (Tm (imod_combine Imod1 Imod2))"
        by (simp add: imod_combine_def)
      then have r_in_combination_field: "r \<in> Field (Tm (imod_combine Imod1 Imod2))"
        using containment_relations_are_fields
        by blast
      have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
        unfolding imod_combine_object_class_def
        by (simp add: rule_object_containment.hyps(1) object_class_wellformed)
      then have object_class_o1_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
        by (simp add: imod_combine_def)
      have subtype_imod1: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r)"
        using rule_object_containment.hyps(3)
        unfolding Type_Model.fields_def class_def
        by fastforce
      then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r)"
        using class_def imod_combine_def instance_model.select_convs(1) tmod_combine_commute tmod_combine_subtype_subset_tmod2
        by metis
      then have "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r)"
        by (simp add: object_class_o1_def)
      then have r_in_combination_fields: "r \<in> Type_Model.fields (Tm (imod_combine Imod1 Imod2)) (ObjectClass (imod_combine Imod1 Imod2) o1)"
        unfolding Type_Model.fields_def class_def
        using r_in_combination_field
        by fastforce
      have "imod_combine_field_value Imod1 Imod2 (o1, r) = FieldValue Imod1 (o1, r)"
        unfolding imod_combine_field_value_def
      proof (induct "o1 \<in> Object Imod2 \<and> r \<in> Field (Tm Imod2)")
        case True
        then show ?case
        proof (induct "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r)")
          case True
          then show ?case
            using field_values_wellformed r_in_imod1 rule_object_containment.hyps(1) subtype_imod1
            by simp
        next
          case False
          then show ?case
            using field_values_outside_domain r_in_imod1 rule_object_containment.hyps(1)
            by simp
        qed
      next
        case False
        then show ?case
          by (simp add: False.hyps r_in_imod1 rule_object_containment.hyps(1))
      qed
      then have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod1 (o1, r)"
        by (simp add: imod_combine_def)
      then have "obj o2 \<in> set (contained_values (FieldValue (imod_combine Imod1 Imod2) (o1, r)))"
        by (simp add: rule_object_containment.hyps(4))
      then show ?case
        using o1_in_combination r_in_combination r_in_combination_fields
        by (simp add: object_containments_relation.rule_object_containment)
    qed
  qed
qed

lemma imod_combine_object_containments_relation_subset_imod2:
  assumes object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes fieldsig_wellformed_type_tmod1: "\<And>f. f \<in> Field (Tm Imod1) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) \<in> Type (Tm Imod1)"
  assumes fieldsig_wellformed_type_tmod2: "\<And>f. f \<in> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod2) f) \<in> Type (Tm Imod2)"
  assumes fieldsig_wellformed: "\<And>f. f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
  assumes field_values_wellformed: "\<And>ob f. ob \<in> Object Imod1 \<inter> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> 
    FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)"
  assumes field_values_outside_domain: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
    \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> FieldValue Imod1 (ob, f) = unspecified"
  shows "object_containments_relation Imod2 \<subseteq> object_containments_relation (imod_combine Imod1 Imod2)"
proof-
  have "object_containments_relation Imod2 \<subseteq> object_containments_relation (imod_combine Imod2 Imod1)"
    by (intro imod_combine_object_containments_relation_subset_imod1) (simp_all add: assms)
  then show "object_containments_relation Imod2 \<subseteq> object_containments_relation (imod_combine Imod1 Imod2)"
    by (simp add: imod_combine_commute)
qed

lemma imod_combine_containment_satisfaction_imod1:
  assumes imod1_correct: "instance_model Imod1"
  assumes imod2_correct: "instance_model Imod2"
  assumes combine_fields_distinct: "Field (Tm Imod1) \<inter> Field (Tm Imod2) = {}"
  assumes structure_object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes property_field_values_not_field: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes property_field_values_subtype: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow>
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes validity_type_model_consistent: "type_model (tmod_combine (Tm Imod1) (Tm Imod2))"
  shows "\<And>ob. \<forall>r. containment r \<notin> Prop (Tm Imod2) \<Longrightarrow> ob \<in> Object Imod1 \<union> Object Imod2 \<Longrightarrow> 
    card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
proof-
  fix ob
  assume imod2_no_containment: "\<forall>r. containment r \<notin> Prop (Tm Imod2)"
  have object_containments_altdef: "object_containments (imod_combine Imod1 Imod2) ob = object_containments Imod1 ob"
  proof
    show "object_containments (imod_combine Imod1 Imod2) ob \<subseteq> object_containments Imod1 ob"
    proof
      fix x
      assume "x \<in> object_containments (imod_combine Imod1 Imod2) ob"
      then show "x \<in> object_containments Imod1 ob"
      proof (induct x)
        case (Pair a d)
        then show ?case
        proof (induct a)
          case (fields a b c)
          then show ?case
          proof (induct)
            case (rule_object_containment o1 r)
            then have o1_in_imods: "o1 \<in> Object Imod1 \<union> Object Imod2"
              unfolding imod_combine_def
              by simp
            have "r \<in> CR (tmod_combine (Tm Imod1) (Tm Imod2))"
              using rule_object_containment.hyps(2)
              unfolding imod_combine_def
              by simp
            then have "r \<in> CR (Tm Imod1) \<union> CR (Tm Imod2)"
              using tmod_combine_containment_relation imod1_correct imod2_correct instance_model.validity_type_model_consistent
              using type_model.structure_fieldsig_wellformed_type type_model.structure_properties_wellfomed combine_fields_distinct empty_iff
              by metis
            then have "r \<in> CR (Tm Imod1)"
              by (simp add: CR.simps imod2_no_containment)
            then show ?case
              using o1_in_imods
            proof (elim UnE)
              assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
              then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
                by (simp add: CR.simps Type_Model.Rel_def)
              then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
                using combine_fields_distinct
                by blast
              then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
                using containment_relations_are_fields
                by blast
              have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
                by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
              then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
                by (fact ProperClassType.rule_proper_classes)
              then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
                unfolding Type_def NonContainerType_def ClassType_def
                by simp
              assume o1_in_imod1: "o1 \<in> Object Imod1"
              then have o1_class_in_tmod1: "ObjectClass Imod1 o1 \<in> Class (Tm Imod1)"
                using imod1_correct instance_model.structure_object_class_wellformed
                by metis
              then have "\<exclamdown>(ObjectClass Imod1 o1) \<in> ProperClassType (Tm Imod1)"
                by (fact ProperClassType.rule_proper_classes)
              then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod1 o1) \<in> Type (Tm Imod1)"
                unfolding Type_def NonContainerType_def ClassType_def
                by simp
              have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r)"
                using fields_of_class_subtype_field_class o1_in_imod1 property_field_values_subtype r_in_field_tmod1 rule_object_containment.hyps(3)
                by blast
              then have r_in_fields_tmod1: "r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 o1)"
                unfolding Type_Model.fields_def class_def
                using r_in_field_tmod1
                by fastforce
              have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod1 (o1, r)"
                unfolding imod_combine_def imod_combine_field_value_def
                by (simp add: combine_fields_distinct o1_in_imod1 r_in_field_tmod1)
              then have "obj ob \<in> set (contained_values (FieldValue Imod1 (o1, r)))"
                using rule_object_containment.hyps(4)
                by simp
              then show ?thesis
                by (simp add: o1_in_imod1 object_containments.rule_object_containment r_in_fields_tmod1 r_in_tmod1)
            next
              assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
              then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
                by (simp add: CR.simps Type_Model.Rel_def)
              then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
                using combine_fields_distinct
                by blast
              then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
                using containment_relations_are_fields
                by blast
              have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
                by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
              then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
                by (fact ProperClassType.rule_proper_classes)
              then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
                unfolding Type_def NonContainerType_def ClassType_def
                by simp
              assume o1_in_imod2: "o1 \<in> Object Imod2"
              then have o1_class_in_tmod2: "ObjectClass Imod2 o1 \<in> Class (Tm Imod2)"
                using imod2_correct instance_model.structure_object_class_wellformed
                by metis
              then have "\<exclamdown>(ObjectClass Imod2 o1) \<in> ProperClassType (Tm Imod2)"
                by (fact ProperClassType.rule_proper_classes)
              then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod2 o1) \<in> Type (Tm Imod2)"
                unfolding Type_def NonContainerType_def ClassType_def
                by simp
              have o1_has_field: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r)"
                using fields_of_class_subtype_field_class o1_in_imod2 property_field_values_not_field r_in_field_tmod1 rule_object_containment.hyps(3)
                by blast
              then have r_in_fields_tmod1: "r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 o1)"
                unfolding Type_Model.fields_def class_def
                using r_in_field_tmod1
                by fastforce
              have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod1 (o1, r)"
                unfolding imod_combine_def imod_combine_field_value_def
                by (simp add: combine_fields_distinct o1_has_field r_in_field_tmod1)
              then have "obj ob \<in> set (contained_values (FieldValue Imod1 (o1, r)))"
                using rule_object_containment.hyps(4)
                by simp
              then show ?thesis
                by (simp add: o1_has_field object_containments.rule_object_containment r_in_fields_tmod1 r_in_tmod1)
            qed
          qed
        qed
      qed
    qed
  next
    show "object_containments Imod1 ob \<subseteq> object_containments (imod_combine Imod1 Imod2) ob"
      by (intro imod_combine_object_containments_subset_imod1) 
        (simp_all add: assms instance_model.validity_type_model_consistent type_model.structure_fieldsig_wellformed_type instance_model.property_field_values_outside_domain)
  qed
  have object_containments_altdef_empty: "ob \<in> Object Imod2 - Object Imod1 \<Longrightarrow> object_containments (imod_combine Imod1 Imod2) ob = {}"
  proof
    assume object_in_imod2: "ob \<in> Object Imod2 - Object Imod1"
    then have "obj ob \<notin> ProperClassValue Imod1"
      by (simp add: ProperClassValue.simps)
    then have ob_not_in_value_imod1: "obj ob \<notin> Value Imod1"
      unfolding Value_def AtomValue_def ClassValue_def
      by simp
    show "object_containments (imod_combine Imod1 Imod2) ob \<subseteq> {}"
    proof
      fix x
      assume "x \<in> object_containments (imod_combine Imod1 Imod2) ob"
      then show "x \<in> {}"
      proof (induct x)
        case (Pair a d)
        then show ?case
        proof (induct a)
          case (fields a b c)
          then show ?case
          proof (induct)
            case (rule_object_containment o1 r)
            then have o1_in_imods: "o1 \<in> Object Imod1 \<union> Object Imod2"
              unfolding imod_combine_def
              by simp
            have "r \<in> CR (tmod_combine (Tm Imod1) (Tm Imod2))"
              using rule_object_containment.hyps(2)
              unfolding imod_combine_def
              by simp
            then have "r \<in> CR (Tm Imod1) \<union> CR (Tm Imod2)"
              using tmod_combine_containment_relation imod1_correct imod2_correct instance_model.validity_type_model_consistent
              using type_model.structure_fieldsig_wellformed_type type_model.structure_properties_wellfomed combine_fields_distinct empty_iff
              by metis
            then have "r \<in> CR (Tm Imod1)"
              by (simp add: CR.simps imod2_no_containment)
            then show ?case
              using o1_in_imods
            proof (elim UnE)
              assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
              then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
                by (simp add: CR.simps Type_Model.Rel_def)
              then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
                using combine_fields_distinct
                by blast
              then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
                using containment_relations_are_fields
                by blast
              have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
                by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
              then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
                by (fact ProperClassType.rule_proper_classes)
              then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
                unfolding Type_def NonContainerType_def ClassType_def
                by simp
              assume o1_in_imod1: "o1 \<in> Object Imod1"
              then have o1_class_in_tmod1: "ObjectClass Imod1 o1 \<in> Class (Tm Imod1)"
                using imod1_correct instance_model.structure_object_class_wellformed
                by metis
              then have "\<exclamdown>(ObjectClass Imod1 o1) \<in> ProperClassType (Tm Imod1)"
                by (fact ProperClassType.rule_proper_classes)
              then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod1 o1) \<in> Type (Tm Imod1)"
                unfolding Type_def NonContainerType_def ClassType_def
                by simp
              have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r)"
                using fields_of_class_subtype_field_class o1_in_imod1 property_field_values_subtype r_in_field_tmod1 rule_object_containment.hyps(3)
                by blast
              then have r_in_fields_tmod1: "r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 o1)"
                unfolding Type_Model.fields_def class_def
                using r_in_field_tmod1
                by fastforce
              have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod1 (o1, r)"
                unfolding imod_combine_def imod_combine_field_value_def
                by (simp add: combine_fields_distinct o1_in_imod1 r_in_field_tmod1)
              then have ob_in_value: "obj ob \<in> set (contained_values (FieldValue Imod1 (o1, r)))"
                using rule_object_containment.hyps(4)
                by simp
              have "FieldValue Imod1 (o1, r) \<in> Value Imod1"
                by (simp add: imod1_correct instance_model.property_field_values_inside_domain o1_in_imod1 r_in_field_tmod1 r_in_fields_tmod1)
              then have "set (contained_values (FieldValue Imod1 (o1, r))) \<subseteq> Value Imod1"
                unfolding Value_def
                using container_value_contained_values atom_values_contained_values_singleton
                by fastforce
              then have "obj ob \<notin> set (contained_values (FieldValue Imod1 (o1, r)))"
                using ob_not_in_value_imod1
                by blast
              then show ?thesis
                using ob_in_value
                by blast
            next
              assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
              then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
                by (simp add: CR.simps Type_Model.Rel_def)
              then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
                using combine_fields_distinct
                by blast
              then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
                using containment_relations_are_fields
                by blast
              have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
                by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
              then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
                by (fact ProperClassType.rule_proper_classes)
              then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
                unfolding Type_def NonContainerType_def ClassType_def
                by simp
              assume o1_in_imod2: "o1 \<in> Object Imod2"
              then have o1_class_in_tmod2: "ObjectClass Imod2 o1 \<in> Class (Tm Imod2)"
                using imod2_correct instance_model.structure_object_class_wellformed
                by metis
              then have "\<exclamdown>(ObjectClass Imod2 o1) \<in> ProperClassType (Tm Imod2)"
                by (fact ProperClassType.rule_proper_classes)
              then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod2 o1) \<in> Type (Tm Imod2)"
                unfolding Type_def NonContainerType_def ClassType_def
                by simp
              have o1_has_field: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r)"
                using fields_of_class_subtype_field_class o1_in_imod2 property_field_values_not_field r_in_field_tmod1 rule_object_containment.hyps(3)
                by blast
              then have r_in_fields_tmod1: "r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 o1)"
                unfolding Type_Model.fields_def class_def
                using r_in_field_tmod1
                by fastforce
              have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod1 (o1, r)"
                unfolding imod_combine_def imod_combine_field_value_def
                by (simp add: combine_fields_distinct o1_has_field r_in_field_tmod1)
              then have ob_in_value: "obj ob \<in> set (contained_values (FieldValue Imod1 (o1, r)))"
                using rule_object_containment.hyps(4)
                by simp
              have "FieldValue Imod1 (o1, r) \<in> Value Imod1"
                by (simp add: imod1_correct instance_model.property_field_values_inside_domain o1_has_field r_in_field_tmod1)
              then have "set (contained_values (FieldValue Imod1 (o1, r))) \<subseteq> Value Imod1"
                unfolding Value_def
                using container_value_contained_values atom_values_contained_values_singleton
                by fastforce
              then have "obj ob \<notin> set (contained_values (FieldValue Imod1 (o1, r)))"
                using ob_not_in_value_imod1
                by blast
              then show ?thesis
                using ob_in_value
                by blast
            qed
          qed
        qed
      qed
    qed
  next
    show "{} \<subseteq> object_containments (imod_combine Imod1 Imod2) ob"
      by simp
  qed
  have object_containments_altdef_no_containment: "\<forall>r. containment r \<notin> Prop (Tm Imod1) \<Longrightarrow> object_containments (imod_combine Imod1 Imod2) ob = {}"
  proof
    assume imod1_no_containment: "\<forall>r. containment r \<notin> Prop (Tm Imod1)"
    show "object_containments (imod_combine Imod1 Imod2) ob \<subseteq> {}"
    proof
      fix x
      assume "x \<in> object_containments (imod_combine Imod1 Imod2) ob"
      then show "x \<in> {}"
      proof (induct x)
        case (Pair a d)
        then show ?case
        proof (induct a)
          case (fields a b c)
          then show ?case
          proof (induct)
            case (rule_object_containment o1 r)
            then have "r \<in> CR (tmod_combine (Tm Imod1) (Tm Imod2))"
              unfolding imod_combine_def
              by simp
            then have "r \<in> CR (Tm Imod1) \<union> CR (Tm Imod2)"
              using tmod_combine_containment_relation imod1_correct imod2_correct instance_model.validity_type_model_consistent
              using type_model.structure_fieldsig_wellformed_type type_model.structure_properties_wellfomed combine_fields_distinct empty_iff
              by metis
            then show ?case
              using imod1_no_containment imod2_no_containment
              by (simp add: CR.simps)
          qed
        qed
      qed
    qed
  next
    show "{} \<subseteq> object_containments (imod_combine Imod1 Imod2) ob"
      by simp
  qed
  assume "ob \<in> Object Imod1 \<union> Object Imod2"
  then have "ob \<in> Object Imod1 \<or> ob \<in> Object Imod2 - Object Imod1"
    by blast
  then show "card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
  proof (elim disjE)
    assume ob_in_imod1: "ob \<in> Object Imod1"
    then show ?thesis
    proof (induct "\<exists>r. containment r \<in> Prop (Tm Imod1)")
      case True
      then have imod1_satisfied: "ob \<in> Object Imod1 \<Longrightarrow> card (object_containments Imod1 ob) \<le> 1"
        using imod1_correct instance_model.validity_properties_satisfied property_satisfaction_containment_rev
        by metis
      then show ?case
        by (simp add: ob_in_imod1 object_containments_altdef)
    next
      case False
      then show ?case
        using object_containments_altdef_no_containment
        by simp
    qed
  next
    assume ob_in_imod2: "ob \<in> Object Imod2 - Object Imod1"
    then show ?thesis
      by (simp add: object_containments_altdef_empty)
  qed
qed

lemma imod_combine_containment_satisfaction_imod2:
  assumes imod1_correct: "instance_model Imod1"
  assumes imod2_correct: "instance_model Imod2"
  assumes combine_fields_distinct: "Field (Tm Imod1) \<inter> Field (Tm Imod2) = {}"
  assumes structure_object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes property_field_values_not_field: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes property_field_values_subtype: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow>
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes validity_type_model_consistent: "type_model (tmod_combine (Tm Imod1) (Tm Imod2))"
  shows "\<And>ob. \<forall>r. containment r \<notin> Prop (Tm Imod1) \<Longrightarrow> 
    ob \<in> Object Imod1 \<union> Object Imod2 \<Longrightarrow> card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
proof-
  fix ob
  assume imod1_no_containment: "\<forall>r. containment r \<notin> Prop (Tm Imod1)"
  assume ob_in_imods: "ob \<in> Object Imod1 \<union> Object Imod2"
  have "card (object_containments (imod_combine Imod2 Imod1) ob) \<le> 1"
  proof (intro imod_combine_containment_satisfaction_imod1)
    show "ob \<in> Object Imod2 \<union> Object Imod1"
      using ob_in_imods
      by blast
  qed (simp_all add: imod1_no_containment assms Int_commute tmod_combine_commute imod_combine_commute)
  then show "card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
    by (simp add: imod_combine_commute)
qed

lemma imod_combine_containment_relation_satisfaction_imod1:
  assumes imod1_correct: "instance_model Imod1"
  assumes imod2_correct: "instance_model Imod2"
  assumes combine_fields_distinct: "Field (Tm Imod1) \<inter> Field (Tm Imod2) = {}"
  assumes structure_object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes property_field_values_not_field: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes property_field_values_subtype: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow>
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes validity_type_model_consistent: "type_model (tmod_combine (Tm Imod1) (Tm Imod2))"
  shows "\<forall>r. containment r \<notin> Prop (Tm Imod2) \<Longrightarrow> irrefl ((object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+)"
proof-
  assume imod2_no_containment: "\<forall>r. containment r \<notin> Prop (Tm Imod2)"
  have containment_relation_altdef: "object_containments_relation (imod_combine Imod1 Imod2) = object_containments_relation Imod1"
  proof
    show "object_containments_relation (imod_combine Imod1 Imod2) \<subseteq> object_containments_relation Imod1"
    proof
      fix x
      assume "x \<in> object_containments_relation (imod_combine Imod1 Imod2)"
      then show "x \<in> object_containments_relation Imod1"
      proof (induct x)
        case (Pair a d)
        then show ?case
        proof (induct)
          case (rule_object_containment o1 o2 r)
          then have o1_in_imods: "o1 \<in> Object Imod1 \<union> Object Imod2"
            unfolding imod_combine_def
            by simp
          have "r \<in> CR (tmod_combine (Tm Imod1) (Tm Imod2))"
            using rule_object_containment.hyps(2)
            unfolding imod_combine_def
            by simp
          then have "r \<in> CR (Tm Imod1) \<union> CR (Tm Imod2)"
            using tmod_combine_containment_relation imod1_correct imod2_correct instance_model.validity_type_model_consistent
            using type_model.structure_fieldsig_wellformed_type type_model.structure_properties_wellfomed combine_fields_distinct empty_iff
            by metis
          then have "r \<in> CR (Tm Imod1)"
            by (simp add: CR.simps imod2_no_containment)
          then show ?case
            using o1_in_imods
          proof (elim UnE)
            assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
            then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
              by (simp add: CR.simps Type_Model.Rel_def)
            then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
              using combine_fields_distinct
              by blast
            then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
              using containment_relations_are_fields
              by blast
            have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
              by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
            then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
              by (fact ProperClassType.rule_proper_classes)
            then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            assume o1_in_imod1: "o1 \<in> Object Imod1"
            then have o1_class_in_tmod1: "ObjectClass Imod1 o1 \<in> Class (Tm Imod1)"
              using imod1_correct instance_model.structure_object_class_wellformed
              by metis
            then have "\<exclamdown>(ObjectClass Imod1 o1) \<in> ProperClassType (Tm Imod1)"
              by (fact ProperClassType.rule_proper_classes)
            then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod1 o1) \<in> Type (Tm Imod1)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r)"
              using fields_of_class_subtype_field_class o1_in_imod1 property_field_values_subtype r_in_field_tmod1 rule_object_containment.hyps(3)
              by blast
            then have r_in_fields_tmod1: "r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 o1)"
              unfolding Type_Model.fields_def class_def
              using r_in_field_tmod1
              by fastforce
            have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod1 (o1, r)"
              unfolding imod_combine_def imod_combine_field_value_def
              by (simp add: combine_fields_distinct o1_in_imod1 r_in_field_tmod1)
            then have "obj o2 \<in> set (contained_values (FieldValue Imod1 (o1, r)))"
              using rule_object_containment.hyps(4)
              by simp
            then show ?thesis
              using o1_in_imod1 object_containments_relation.rule_object_containment r_in_fields_tmod1 r_in_tmod1
              by metis
          next
            assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
            then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
              by (simp add: CR.simps Type_Model.Rel_def)
            then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
              using combine_fields_distinct
              by blast
            then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
              using containment_relations_are_fields
              by blast
            have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
              by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
            then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
              by (fact ProperClassType.rule_proper_classes)
            then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            assume o1_in_imod2: "o1 \<in> Object Imod2"
            then have o1_class_in_tmod2: "ObjectClass Imod2 o1 \<in> Class (Tm Imod2)"
              using imod2_correct instance_model.structure_object_class_wellformed
              by metis
            then have "\<exclamdown>(ObjectClass Imod2 o1) \<in> ProperClassType (Tm Imod2)"
              by (fact ProperClassType.rule_proper_classes)
            then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod2 o1) \<in> Type (Tm Imod2)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            have o1_has_field: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r)"
              using fields_of_class_subtype_field_class o1_in_imod2 property_field_values_not_field r_in_field_tmod1 rule_object_containment.hyps(3)
              by blast
            then have r_in_fields_tmod1: "r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 o1)"
              unfolding Type_Model.fields_def class_def
              using r_in_field_tmod1
              by fastforce
            have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod1 (o1, r)"
              unfolding imod_combine_def imod_combine_field_value_def
              by (simp add: combine_fields_distinct o1_has_field r_in_field_tmod1)
            then have "obj o2 \<in> set (contained_values (FieldValue Imod1 (o1, r)))"
              using rule_object_containment.hyps(4)
              by simp
            then show ?thesis
              using o1_has_field object_containments_relation.rule_object_containment r_in_fields_tmod1 r_in_tmod1
              by metis
          qed
        qed
      qed
    qed
  next
    show "object_containments_relation Imod1 \<subseteq> object_containments_relation (imod_combine Imod1 Imod2)"
      by (intro imod_combine_object_containments_relation_subset_imod1) 
        (simp_all add: assms instance_model.validity_type_model_consistent type_model.structure_fieldsig_wellformed_type instance_model.property_field_values_outside_domain)
  qed
  have containments_relation_altdef_no_containment: "\<forall>r. containment r \<notin> Prop (Tm Imod1) \<Longrightarrow> object_containments_relation (imod_combine Imod1 Imod2) = {}"
  proof
    assume imod1_no_containment: "\<forall>r. containment r \<notin> Prop (Tm Imod1)"
    show "object_containments_relation (imod_combine Imod1 Imod2) \<subseteq> {}"
    proof
      fix x
      assume "x \<in> object_containments_relation (imod_combine Imod1 Imod2)"
      then show "x \<in> {}"
      proof (induct x)
        case (Pair a d)
        then show ?case
        proof (induct)
          case (rule_object_containment o1 o2 r)
          then have "r \<in> CR (tmod_combine (Tm Imod1) (Tm Imod2))"
            unfolding imod_combine_def
            by simp
          then have "r \<in> CR (Tm Imod1) \<union> CR (Tm Imod2)"
            using tmod_combine_containment_relation imod1_correct imod2_correct instance_model.validity_type_model_consistent
            using type_model.structure_fieldsig_wellformed_type type_model.structure_properties_wellfomed combine_fields_distinct empty_iff
            by metis
          then show ?case
            using imod1_no_containment imod2_no_containment
            by (simp add: CR.simps)
        qed
      qed
    qed
  next
    show "{} \<subseteq> object_containments_relation (imod_combine Imod1 Imod2)"
      by simp
  qed
  show "irrefl ((object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+)"
  proof (induct "\<exists>r. containment r \<in> Prop (Tm Imod1)")
    case True
    then have imod1_satisfied: "irrefl ((object_containments_relation Imod1)\<^sup>+)"
      using imod1_correct instance_model.validity_properties_satisfied property_satisfaction_containment_rev
      by metis
    then show ?case
      by (simp add: containment_relation_altdef)
  next
    case False
    then show ?case
      using containments_relation_altdef_no_containment irrefl_def
      by fastforce
  qed
qed

lemma imod_combine_containment_relation_satisfaction_imod2:
  assumes imod1_correct: "instance_model Imod1"
  assumes imod2_correct: "instance_model Imod2"
  assumes combine_fields_distinct: "Field (Tm Imod1) \<inter> Field (Tm Imod2) = {}"
  assumes structure_object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes property_field_values_not_field: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes property_field_values_subtype: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow>
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes validity_type_model_consistent: "type_model (tmod_combine (Tm Imod1) (Tm Imod2))"
  shows "\<forall>r. containment r \<notin> Prop (Tm Imod1) \<Longrightarrow> irrefl ((object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+)"
proof-
  fix ob
  assume imod1_no_containment: "\<forall>r. containment r \<notin> Prop (Tm Imod1)"
  have "irrefl ((object_containments_relation (imod_combine Imod2 Imod1))\<^sup>+)"
    by (intro imod_combine_containment_relation_satisfaction_imod1) 
      (simp_all add: imod1_no_containment assms Int_commute tmod_combine_commute imod_combine_commute)
  then show "irrefl ((object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+)"
    by (simp add: imod_combine_commute)
qed


subsection "Correctness of merging instance models"

lemma imod_combine_correct:
  assumes imod1_correct: "instance_model Imod1"
  assumes imod2_correct: "instance_model Imod2"
  assumes structure_object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes structure_object_id_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectId Imod1 ob = ObjectId Imod2 ob"
  assumes structure_default_values_wellformed: "\<And>c. c \<in> Constant (Tm Imod1) \<Longrightarrow> c \<in> Constant (Tm Imod2) \<Longrightarrow> DefaultValue Imod1 c = DefaultValue Imod2 c"
  assumes property_object_id_uniqueness: "\<And>o1 o2. o1 \<in> Object Imod1 - Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 - Object Imod1 \<Longrightarrow> 
    ObjectId Imod1 o1 = ObjectId Imod2 o2 \<Longrightarrow> o1 = o2"
  assumes property_field_values_wellformed: "\<And>ob f. ob \<in> Object Imod1 \<inter> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> 
    FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)"
  assumes property_field_values_not_field_imod1: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod2) - Field (Tm Imod1) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes property_field_values_not_field_imod2: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) - Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes property_field_values_not_subtype_imod1: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow>
    \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod2 \<and> f \<in> Field (Tm Imod2) \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes property_field_values_not_subtype_imod2: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow>
    \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod1 \<and> f \<in> Field (Tm Imod1) \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes validity_multiplicities_valid_imod1: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> FieldValue Imod1 (ob, f) \<in> ContainerValue Imod1 \<Longrightarrow>
    Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and>
    \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
  assumes validity_multiplicities_valid_imod2: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> FieldValue Imod2 (ob, f) \<in> ContainerValue Imod2 \<Longrightarrow>
    Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<and>
    \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
  assumes validity_containment_properties_satisfied: "\<And>r ob. containment r \<in> Prop (Tm Imod1) \<union> Prop (Tm Imod2) \<Longrightarrow> 
    ob \<in> Object Imod1 \<union> Object Imod2 \<Longrightarrow> card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
  assumes validity_containments_relation: "irrefl ((object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+)"
  assumes validity_identity_properties_satisfied: "\<And>c A o1 o2 a. identity c A \<in> Prop (Tm Imod1) \<Longrightarrow> identity c A \<in> Prop (Tm Imod2) \<Longrightarrow> 
    o1 \<in> Object Imod1 - Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 - Object Imod1 \<Longrightarrow> a \<in> A \<Longrightarrow> ObjectClass Imod1 o1 = c \<Longrightarrow> ObjectClass Imod2 o2 = c \<Longrightarrow> 
    FieldValue Imod1 (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue Imod2 (o2, a) \<Longrightarrow> o1 = o2"
  assumes validity_opposite_properties_satisfied: "\<And>r1 r2 o1 o2. opposite r1 r2 \<in> Prop (Tm Imod1) \<Longrightarrow> opposite r1 r2 \<in> Prop (Tm Imod2) \<Longrightarrow> 
    o1 \<in> Object Imod1 \<Longrightarrow> o1 \<notin> Object Imod2 \<or> \<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1) \<Longrightarrow> 
    o2 \<in> Object Imod2 \<Longrightarrow> o2 \<notin> Object Imod1 \<or> \<not>\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2) \<Longrightarrow> edgeCount Imod1 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
  assumes validity_type_model_consistent: "type_model (tmod_combine (Tm Imod1) (Tm Imod2))"
  shows "instance_model (imod_combine Imod1 Imod2)"
proof (intro instance_model.intro)
  fix ob
  assume "ob \<in> Object (imod_combine Imod1 Imod2)"
  then have "ob \<in> Object Imod1 \<union> Object Imod2"
    by (simp add: imod_combine_def)
  then have "ob \<in> Object Imod1 \<inter> Object Imod2 \<or> ob \<in> Object Imod1 - Object Imod2 \<or> ob \<in> Object Imod2 - Object Imod1"
    by blast
  then have "ObjectClass (imod_combine Imod1 Imod2) ob \<in> Class (Tm Imod1) \<union> Class (Tm Imod2)"
  proof (elim disjE)
    assume ob_in_imods: "ob \<in> Object Imod1 \<inter> Object Imod2"
    then have "ObjectClass (imod_combine Imod1 Imod2) ob = ObjectClass Imod1 ob"
      by (simp add: imod_combine_def imod_combine_object_class_def structure_object_class_wellformed)
    then have "ObjectClass (imod_combine Imod1 Imod2) ob \<in> Class (Tm Imod1)"
      using ob_in_imods imod1_correct instance_model.structure_object_class_wellformed
      by fastforce
    then show ?thesis
      by simp
  next
    assume ob_in_imod1: "ob \<in> Object Imod1 - Object Imod2"
    then have "ObjectClass (imod_combine Imod1 Imod2) ob = ObjectClass Imod1 ob"
      by (simp add: imod_combine_def imod_combine_object_class_def structure_object_class_wellformed)
    then have "ObjectClass (imod_combine Imod1 Imod2) ob \<in> Class (Tm Imod1)"
      using ob_in_imod1 imod1_correct instance_model.structure_object_class_wellformed
      by fastforce
    then show ?thesis
      by simp
  next
    assume ob_in_imod2: "ob \<in> Object Imod2 - Object Imod1"
    then have "ObjectClass (imod_combine Imod1 Imod2) ob = ObjectClass Imod2 ob"
      by (simp add: imod_combine_def imod_combine_object_class_def structure_object_class_wellformed)
    then have "ObjectClass (imod_combine Imod1 Imod2) ob \<in> Class (Tm Imod2)"
      using ob_in_imod2 imod2_correct instance_model.structure_object_class_wellformed
      by fastforce
    then show ?thesis
      by simp
  qed
  then show "ObjectClass (imod_combine Imod1 Imod2) ob \<in> Class (Tm (imod_combine Imod1 Imod2))"
    by (simp add: imod_combine_def tmod_combine_def)
next
  fix ob
  assume "ob \<notin> Object (imod_combine Imod1 Imod2)"
  then have "ob \<notin> Object Imod1 \<union> Object Imod2"
    by (simp add: imod_combine_def)
  then show "ObjectClass (imod_combine Imod1 Imod2) ob = undefined"
    by (simp add: imod1_correct imod_combine_def imod_combine_object_class_def instance_model.structure_object_class_domain)
next
  fix ob
  assume "ob \<notin> Object (imod_combine Imod1 Imod2)"
  then have "ob \<notin> Object Imod1 \<union> Object Imod2"
    by (simp add: imod_combine_def)
  then show "ObjectId (imod_combine Imod1 Imod2) ob = undefined"
    by (simp add: imod1_correct imod_combine_def imod_combine_object_id_def instance_model.structure_object_id_domain)
next
  fix ob f
  assume "ob \<notin> Object (imod_combine Imod1 Imod2) \<or> f \<notin> Field (Tm (imod_combine Imod1 Imod2))"
  then have "ob \<notin> Object Imod1 \<union> Object Imod2 \<or> f \<notin> Field (Tm Imod1) \<union> Field (Tm Imod2)"
    by (simp add: imod_combine_def tmod_combine_def)
  then have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
  proof (elim disjE)
    assume "ob \<notin> Object Imod1 \<union> Object Imod2"
    then show ?thesis
      unfolding imod_combine_field_value_def
      by simp
  next
    assume "f \<notin> Field (Tm Imod1) \<union> Field (Tm Imod2)"
    then show ?thesis
      unfolding imod_combine_field_value_def
      by simp
  qed
  then show "FieldValue (imod_combine Imod1 Imod2) (ob, f) = undefined"
    by (simp add: imod_combine_def)
next
  fix c
  assume "c \<in> Constant (Tm (imod_combine Imod1 Imod2))"
  then have "c \<in> Constant (Tm Imod1) \<union> Constant (Tm Imod2)"
    by (simp add: imod_combine_def tmod_combine_def)
  then have "c \<in> Constant (Tm Imod1) \<inter> Constant (Tm Imod2) \<or> c \<in> Constant (Tm Imod1) - Constant (Tm Imod2) \<or> c \<in> Constant (Tm Imod2) - Constant (Tm Imod1)"
    by blast
  then show "DefaultValue (imod_combine Imod1 Imod2) c \<in> Value (imod_combine Imod1 Imod2)"
  proof (elim disjE)
    assume c_in_contant_tmods: "c \<in> Constant (Tm Imod1) \<inter> Constant (Tm Imod2)"
    then have "DefaultValue (imod_combine Imod1 Imod2) c = DefaultValue Imod1 c"
      by (simp add: imod_combine_def imod_combine_default_value_def structure_default_values_wellformed)
    then have "DefaultValue (imod_combine Imod1 Imod2) c \<in> Value Imod1"
      using c_in_contant_tmods imod1_correct instance_model.structure_default_values_wellformed
      by fastforce
    then show "DefaultValue (imod_combine Imod1 Imod2) c \<in> Value (imod_combine Imod1 Imod2)"
      using imod_combine_value
      by blast
  next
    assume c_in_contant_tmod1: "c \<in> Constant (Tm Imod1) - Constant (Tm Imod2)"
    then have "DefaultValue (imod_combine Imod1 Imod2) c = DefaultValue Imod1 c"
      by (simp add: imod_combine_def imod_combine_default_value_def)
    then have "DefaultValue (imod_combine Imod1 Imod2) c \<in> Value Imod1"
      using c_in_contant_tmod1 imod1_correct instance_model.structure_default_values_wellformed
      by fastforce
    then show "DefaultValue (imod_combine Imod1 Imod2) c \<in> Value (imod_combine Imod1 Imod2)"
      using imod_combine_value
      by blast
  next
    assume c_in_contant_tmod2: "c \<in> Constant (Tm Imod2) - Constant (Tm Imod1)"
    then have "DefaultValue (imod_combine Imod1 Imod2) c = DefaultValue Imod2 c"
      by (simp add: imod_combine_def imod_combine_default_value_def)
    then have "DefaultValue (imod_combine Imod1 Imod2) c \<in> Value Imod2"
      using c_in_contant_tmod2 imod2_correct instance_model.structure_default_values_wellformed
      by fastforce
    then show "DefaultValue (imod_combine Imod1 Imod2) c \<in> Value (imod_combine Imod1 Imod2)"
      using imod_combine_value
      by blast
  qed
next
  fix c
  assume "c \<notin> Constant (Tm (imod_combine Imod1 Imod2))"
  then have "c \<notin> Constant (Tm Imod1) \<union> Constant (Tm Imod2)"
    by (simp add: imod_combine_def tmod_combine_def)
  then show "DefaultValue (imod_combine Imod1 Imod2) c = undefined"
    by (simp add: imod_combine_def imod_combine_default_value_def)
next
  fix o1 o2
  assume "o1 \<in> Object (imod_combine Imod1 Imod2)"
  then have "o1 \<in> Object Imod1 \<union> Object Imod2"
    by (simp add: imod_combine_def)
  then have o1_def: "o1 \<in> Object Imod1 \<inter> Object Imod2 \<or> o1 \<in> Object Imod1 - Object Imod2 \<or> o1 \<in> Object Imod2 - Object Imod1"
    by blast
  assume "o2 \<in> Object (imod_combine Imod1 Imod2)"
  then have "o2 \<in> Object Imod1 \<union> Object Imod2"
    by (simp add: imod_combine_def)
  then have o2_def: "o2 \<in> Object Imod1 \<inter> Object Imod2 \<or> o2 \<in> Object Imod1 - Object Imod2 \<or> o2 \<in> Object Imod2 - Object Imod1"
    by blast
  assume objectid_eq: "ObjectId (imod_combine Imod1 Imod2) o1 = ObjectId (imod_combine Imod1 Imod2) o2"
  then show "o1 = o2"
    using o1_def o2_def
  proof (elim disjE)
    assume o1_case: "o1 \<in> Object Imod1 \<inter> Object Imod2"
    then have o1_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o1 = ObjectId Imod1 o1"
      using IntD1 IntD2 imod_combine_def imod_combine_object_id_def instance_model.select_convs(4) structure_object_id_wellformed
      by metis
    assume o2_case: "o2 \<in> Object Imod1 \<inter> Object Imod2"
    then have o2_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o2 = ObjectId Imod1 o2"
      using IntD1 IntD2 imod_combine_def imod_combine_object_id_def instance_model.select_convs(4) structure_object_id_wellformed
      by metis
    show "o1 = o2"
      using o1_case o1_objectid_def o2_case o2_objectid_def objectid_eq imod1_correct instance_model.property_object_id_uniqueness
      by fastforce
  next
    assume o1_case: "o1 \<in> Object Imod1 \<inter> Object Imod2"
    then have o1_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o1 = ObjectId Imod1 o1"
      using IntD1 IntD2 imod_combine_def imod_combine_object_id_def instance_model.select_convs(4) structure_object_id_wellformed
      by metis
    assume o2_case: "o2 \<in> Object Imod1 - Object Imod2"
    then have o2_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o2 = ObjectId Imod1 o2"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    show "o1 = o2"
      using o1_case o1_objectid_def o2_case o2_objectid_def objectid_eq imod1_correct instance_model.property_object_id_uniqueness
      by fastforce
  next
    assume o1_case: "o1 \<in> Object Imod1 \<inter> Object Imod2"
    then have o1_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o1 = ObjectId Imod1 o1"
      using IntD1 IntD2 imod_combine_def imod_combine_object_id_def instance_model.select_convs(4) structure_object_id_wellformed
      by metis
    assume o2_case: "o2 \<in> Object Imod2 - Object Imod1"
    then have o2_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o2 = ObjectId Imod2 o2"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    show "o1 = o2"
      using o1_case o1_objectid_def o2_case o2_objectid_def objectid_eq imod2_correct instance_model.property_object_id_uniqueness structure_object_id_wellformed
      by fastforce
  next
    assume o1_case: "o1 \<in> Object Imod1 - Object Imod2"
    then have o1_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o1 = ObjectId Imod1 o1"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    assume o2_case: "o2 \<in> Object Imod1 \<inter> Object Imod2"
    then have o2_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o2 = ObjectId Imod1 o2"
      using IntD1 IntD2 imod_combine_def imod_combine_object_id_def instance_model.select_convs(4) structure_object_id_wellformed
      by metis
    show "o1 = o2"
      using o1_case o1_objectid_def o2_case o2_objectid_def objectid_eq imod1_correct instance_model.property_object_id_uniqueness
      by fastforce
  next
    assume o1_case: "o1 \<in> Object Imod2 - Object Imod1"
    then have o1_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o1 = ObjectId Imod2 o1"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    assume o2_case: "o2 \<in> Object Imod1 \<inter> Object Imod2"
    then have o2_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o2 = ObjectId Imod1 o2"
      using IntD1 IntD2 imod_combine_def imod_combine_object_id_def instance_model.select_convs(4) structure_object_id_wellformed
      by metis
    show "o1 = o2"
      using o1_case o1_objectid_def o2_case o2_objectid_def objectid_eq imod2_correct instance_model.property_object_id_uniqueness structure_object_id_wellformed
      by fastforce
  next
    assume o1_case: "o1 \<in> Object Imod1 - Object Imod2"
    then have o1_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o1 = ObjectId Imod1 o1"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    assume o2_case: "o2 \<in> Object Imod1 - Object Imod2"
    then have o2_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o2 = ObjectId Imod1 o2"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    show "o1 = o2"
      using o1_case o1_objectid_def o2_case o2_objectid_def objectid_eq imod1_correct instance_model.property_object_id_uniqueness
      by fastforce
  next
    assume o1_case: "o1 \<in> Object Imod1 - Object Imod2"
    then have o1_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o1 = ObjectId Imod1 o1"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    assume o2_case: "o2 \<in> Object Imod2 - Object Imod1"
    then have o2_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o2 = ObjectId Imod2 o2"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    show "o1 = o2"
      using o1_case o1_objectid_def o2_case o2_objectid_def objectid_eq property_object_id_uniqueness
      by fastforce
  next
    assume o1_case: "o1 \<in> Object Imod2 - Object Imod1"
    then have o1_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o1 = ObjectId Imod2 o1"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    assume o2_case: "o2 \<in> Object Imod1 - Object Imod2"
    then have o2_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o2 = ObjectId Imod1 o2"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    show "o1 = o2"
      using o1_case o1_objectid_def o2_case o2_objectid_def objectid_eq property_object_id_uniqueness
      by fastforce
  next
    assume o1_case: "o1 \<in> Object Imod2 - Object Imod1"
    then have o1_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o1 = ObjectId Imod2 o1"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    assume o2_case: "o2 \<in> Object Imod2 - Object Imod1"
    then have o2_objectid_def: "ObjectId (imod_combine Imod1 Imod2) o2 = ObjectId Imod2 o2"
      by (simp add: imod_combine_def imod_combine_object_id_def)
    show "o1 = o2"
      using o1_case o1_objectid_def o2_case o2_objectid_def objectid_eq imod2_correct instance_model.property_object_id_uniqueness
      by fastforce
  qed
next
  fix ob f
  assume "ob \<in> Object (imod_combine Imod1 Imod2)"
  then have ob_in_imod12: "ob \<in> Object Imod1 \<union> Object Imod2"
    by (simp add: imod_combine_def)
  then have ob_in_imod12_cases: "ob \<in> Object Imod1 \<inter> Object Imod2 \<or> ob \<in> Object Imod1 - Object Imod2 \<or> ob \<in> Object Imod2 - Object Imod1"
    by blast
  assume "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
  then have f_in_imod12: "f \<in> Field (Tm Imod1) \<union> Field (Tm Imod2)"
    by (simp add: imod_combine_def tmod_combine_def)
  then have f_in_imod12_cases: "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<or> f \<in> Field (Tm Imod1) - Field (Tm Imod2) \<or> f \<in> Field (Tm Imod2) - Field (Tm Imod1)"
    by blast
  assume "\<not>\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  then have no_subtype: "\<not>\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(class (tmod_combine (Tm Imod1) (Tm Imod2)) f)"
    by (simp add: imod_combine_def)
  have "imod_combine_field_value Imod1 Imod2 (ob, f) = unspecified"
    using ob_in_imod12_cases
  proof (elim disjE)
    assume ob_in_both: "ob \<in> Object Imod1 \<inter> Object Imod2"
    then have object_class_eq: "ObjectClass Imod1 ob = ObjectClass Imod2 ob"
      using structure_object_class_wellformed
      by blast
    then have object_class_def: "imod_combine_object_class Imod1 Imod2 ob = ObjectClass Imod1 ob"
      unfolding imod_combine_object_class_def
      using ob_in_both
      by simp
    then have no_subtype_imod1: "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
      using class_def no_subtype tmod_combine_subtype_subset_tmod1
      by metis
    have no_subtype_imod2: "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
      using class_def no_subtype object_class_def object_class_eq tmod_combine_subtype_subset_tmod2
      by metis
    show ?thesis
      using f_in_imod12_cases
    proof (elim disjE)
      assume f_in_both: "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2)"
      have fieldvalue_imod1_def: "FieldValue Imod1 (ob, f) = unspecified"
        using IntD1 f_in_both imod1_correct instance_model.property_field_values_outside_domain no_subtype_imod1 ob_in_both
        by metis
      have fieldvalue_imod2_def: "FieldValue Imod2 (ob, f) = unspecified"
        using IntD2 f_in_both imod2_correct instance_model.property_field_values_outside_domain no_subtype_imod2 ob_in_both
        by metis
      show ?thesis
        unfolding imod_combine_field_value_def
        using f_in_both fieldvalue_imod1_def fieldvalue_imod2_def ob_in_both
        by simp
    next
      assume f_in_imod1: "f \<in> Field (Tm Imod1) - Field (Tm Imod2)"
      then have "FieldValue Imod1 (ob, f) = unspecified"
        using DiffD1 IntD1 imod1_correct instance_model.property_field_values_outside_domain no_subtype_imod1 ob_in_both
        by metis
      then show ?thesis
        unfolding imod_combine_field_value_def
        using f_in_imod1 ob_in_imod12
        by auto
    next
      assume f_in_imod2: "f \<in> Field (Tm Imod2) - Field (Tm Imod1)"
      then have "FieldValue Imod2 (ob, f) = unspecified"
        using DiffD1 IntD2 imod2_correct instance_model.property_field_values_outside_domain no_subtype_imod2 ob_in_both
        by metis
      then show ?thesis
        unfolding imod_combine_field_value_def
        using f_in_imod2 ob_in_imod12
        by auto
    qed
  next
    assume ob_in_imod1: "ob \<in> Object Imod1 - Object Imod2"
    then have object_class_def: "imod_combine_object_class Imod1 Imod2 ob = ObjectClass Imod1 ob"
      unfolding imod_combine_object_class_def
      by simp
    then have no_subtype_imod1: "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
      using class_def no_subtype tmod_combine_subtype_subset_tmod1
      by metis
    show ?thesis
    proof (induct "f \<in> Field (Tm Imod1)")
      case True
      then have "FieldValue Imod1 (ob, f) = unspecified"
        using DiffD1 imod1_correct instance_model.property_field_values_outside_domain no_subtype_imod1 ob_in_imod1
        by metis
      then show ?case
        unfolding imod_combine_field_value_def
        using f_in_imod12 ob_in_imod1
        by auto
    next
      case False
      then show ?case
        unfolding imod_combine_field_value_def
        using f_in_imod12 ob_in_imod1
        by simp
    qed
  next
    assume ob_in_imod2: "ob \<in> Object Imod2 - Object Imod1"
    then have object_class_def: "imod_combine_object_class Imod1 Imod2 ob = ObjectClass Imod2 ob"
      unfolding imod_combine_object_class_def
      by simp
    then have no_subtype_imod2: "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
      using class_def no_subtype tmod_combine_subtype_subset_tmod2
      by metis
    show ?thesis
    proof (induct "f \<in> Field (Tm Imod2)")
      case True
      then have "FieldValue Imod2 (ob, f) = unspecified"
        using DiffD1 imod2_correct instance_model.property_field_values_outside_domain no_subtype_imod2 ob_in_imod2
        by metis
      then show ?case
        unfolding imod_combine_field_value_def
        using f_in_imod12 ob_in_imod2
        by auto
    next
      case False
      then show ?case
        unfolding imod_combine_field_value_def
        using f_in_imod12 ob_in_imod2
        by simp
    qed
  qed
  then show "FieldValue (imod_combine Imod1 Imod2) (ob, f) = unspecified"
    by (simp add: imod_combine_def)
next
  fix ob f
  assume "ob \<in> Object (imod_combine Imod1 Imod2)"
  then have ob_in_imod12: "ob \<in> Object Imod1 \<union> Object Imod2"
    by (simp add: imod_combine_def)
  then have ob_in_imod12_cases: "ob \<in> Object Imod1 \<inter> Object Imod2 \<or> ob \<in> Object Imod1 - Object Imod2 \<or> ob \<in> Object Imod2 - Object Imod1"
    by blast
  assume "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
  then have f_in_fields: "f \<in> Field (Tm Imod1) \<union> Field (Tm Imod2)"
    by (simp add: imod_combine_def tmod_combine_def)
  then have f_in_fields_cases: "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<or> f \<in> Field (Tm Imod1) - Field (Tm Imod2) \<or> f \<in> Field (Tm Imod2) - Field (Tm Imod1)"
    by blast
  assume subtype_combine: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  have imod1_subtype_cases: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
    by simp
  have imod2_subtype_cases: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<or> \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
    by simp
  have "imod_combine_field_value Imod1 Imod2 (ob, f) \<in> Value (imod_combine Imod1 Imod2)"
    using ob_in_imod12_cases
  proof (elim disjE)
    assume ob_in_both: "ob \<in> Object Imod1 \<inter> Object Imod2"
    show ?thesis
      using f_in_fields_cases
    proof (elim disjE)
      assume f_in_both: "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2)"
      show ?thesis
        using imod1_subtype_cases imod2_subtype_cases
      proof (elim disjE)
        assume subtype_imod2: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        assume subtype_imod1: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have "FieldValue Imod1 (ob, f) \<in> Value Imod1"
          using IntD1 f_in_both imod1_correct instance_model.property_field_values_inside_domain ob_in_both
          by metis
        then have "FieldValue Imod1 (ob, f) \<in> Value (imod_combine Imod1 Imod2)"
          using imod_combine_value
          by blast
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_both ob_in_both property_field_values_wellformed subtype_imod1 subtype_imod2
          by simp
      next
        assume subtype_imod1: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have "FieldValue Imod1 (ob, f) \<in> Value Imod1"
          using IntD1 f_in_both imod1_correct instance_model.property_field_values_inside_domain ob_in_both
          by metis
        then have fieldvalue_imod1_def: "FieldValue Imod1 (ob, f) \<in> Value (imod_combine Imod1 Imod2)"
          using imod_combine_value
          by blast
        assume no_subtype_imod2: "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have "FieldValue Imod2 (ob, f) = unspecified"
          using IntD2 f_in_both imod2_correct instance_model.property_field_values_outside_domain ob_in_both
          by metis
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_both fieldvalue_imod1_def ob_in_both
          by auto
      next
        assume no_subtype_imod1: "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have fieldvalue_imod1_def: "FieldValue Imod1 (ob, f) = unspecified"
          using IntD1 f_in_both imod1_correct instance_model.property_field_values_outside_domain ob_in_both
          by metis
        assume subtype_imod2: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have "FieldValue Imod2 (ob, f) \<in> Value Imod2"
          using IntD2 f_in_both imod2_correct instance_model.property_field_values_inside_domain ob_in_both
          by metis
        then have "FieldValue Imod2 (ob, f) \<in> Value (imod_combine Imod1 Imod2)"
          using imod_combine_value
          by blast
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_both fieldvalue_imod1_def ob_in_both
          by auto
      next
        assume no_subtype_imod1: "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        assume no_subtype_imod2: "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        show ?thesis
          using f_in_both no_subtype_imod1 no_subtype_imod2 ob_in_both property_field_values_not_subtype_imod1 subtype_combine
          by simp
      qed
    next
      assume f_in_imod1: "f \<in> Field (Tm Imod1) - Field (Tm Imod2)"
      show ?thesis
        using imod1_subtype_cases
      proof (elim disjE)
        assume "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have "FieldValue Imod1 (ob, f) \<in> Value Imod1"
          using DiffD1 IntD1 f_in_imod1 imod1_correct instance_model.property_field_values_inside_domain ob_in_both
          by metis
        then have "FieldValue Imod1 (ob, f) \<in> Value (imod_combine Imod1 Imod2)"
          using imod_combine_value
          by blast
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_imod1 ob_in_both
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then show ?thesis
          using f_in_imod1 ob_in_both property_field_values_not_field_imod2 subtype_combine
          by simp
      qed
    next
      assume f_in_imod2: "f \<in> Field (Tm Imod2) - Field (Tm Imod1)"
      show ?thesis
        using imod2_subtype_cases
      proof (elim disjE)
        assume "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have "FieldValue Imod2 (ob, f) \<in> Value Imod2"
          using DiffD1 IntD2 f_in_imod2 imod2_correct instance_model.property_field_values_inside_domain ob_in_both
          by metis
        then have "FieldValue Imod2 (ob, f) \<in> Value (imod_combine Imod1 Imod2)"
          using imod_combine_value
          by blast
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_imod2 ob_in_both
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then show ?thesis
          using f_in_imod2 ob_in_both property_field_values_not_field_imod1 subtype_combine
          by simp
      qed
    qed
  next
    assume ob_in_imod1: "ob \<in> Object Imod1 - Object Imod2"
    show ?thesis
    proof (induct "f \<in> Field (Tm Imod1)")
      case True
      then show ?case
        using imod1_subtype_cases
      proof (elim disjE)
        assume "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have "FieldValue Imod1 (ob, f) \<in> Value Imod1"
          using DiffD1 True.hyps imod1_correct instance_model.property_field_values_inside_domain ob_in_imod1
          by metis
        then have "FieldValue Imod1 (ob, f) \<in> Value (imod_combine Imod1 Imod2)"
          using imod_combine_value
          by blast
        then show ?thesis
          unfolding imod_combine_field_value_def
          using True.hyps ob_in_imod1
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then show ?thesis
          using Diff_iff True.hyps ob_in_imod1 property_field_values_not_subtype_imod1 subtype_combine
          by metis
      qed
    next
      case False
      then show ?case
        using DiffD1 DiffD2 Int_iff f_in_fields_cases ob_in_imod1 property_field_values_not_field_imod1 subtype_combine
        by metis
    qed
  next
    assume ob_in_imod2: "ob \<in> Object Imod2 - Object Imod1"
    show ?thesis
    proof (induct "f \<in> Field (Tm Imod2)")
      case True
      then show ?case
        using imod2_subtype_cases
      proof (elim disjE)
        assume "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have "FieldValue Imod2 (ob, f) \<in> Value Imod2"
          using DiffD1 True.hyps imod2_correct instance_model.property_field_values_inside_domain ob_in_imod2
          by metis
        then have "FieldValue Imod2 (ob, f) \<in> Value (imod_combine Imod1 Imod2)"
          using imod_combine_value
          by blast
        then show ?thesis
          unfolding imod_combine_field_value_def
          using True.hyps ob_in_imod2
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then show ?thesis
          using Diff_iff True.hyps ob_in_imod2 property_field_values_not_subtype_imod2 subtype_combine
          by metis
      qed
    next
      case False
      then show ?case
        using DiffD1 DiffD2 Int_iff f_in_fields_cases ob_in_imod2 property_field_values_not_field_imod2 subtype_combine
        by metis
    qed
  qed
  then show "FieldValue (imod_combine Imod1 Imod2) (ob, f) \<in> Value (imod_combine Imod1 Imod2)"
    by (simp add: imod_combine_def)
next
  have structure_fieldsig_wellformed_type: "\<And>f. f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
  proof-
    fix f
    assume f_in_both: "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2)"
    then have "f \<in> Field (tmod_combine (Tm Imod1) (Tm Imod2))"
      unfolding tmod_combine_def
      by simp
    then have "fst (FieldSig (tmod_combine (Tm Imod1) (Tm Imod2)) f) \<in> Type (tmod_combine (Tm Imod1) (Tm Imod2))"
      using validity_type_model_consistent type_model.structure_fieldsig_wellformed_type
      by blast
    then have fst_in_type: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) \<in> Type (tmod_combine (Tm Imod1) (Tm Imod2))"
      by (simp add: tmod_combine_def)
    then show "fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
    proof (induct "fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)")
      case True
      then show ?case
        by simp
    next
      case False
      then have "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = TypeDef.invalid"
        unfolding tmod_combine_fieldsig_def
        using f_in_both 
        by simp
      then have "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) \<notin> Type (tmod_combine (Tm Imod1) (Tm Imod2))"
        by simp
      then show ?case
        using fst_in_type
        by simp
    qed
  qed
  fix ob f
  assume "ob \<in> Object (imod_combine Imod1 Imod2)"
  then have ob_in_imod12: "ob \<in> Object Imod1 \<union> Object Imod2"
    by (simp add: imod_combine_def)
  then have ob_in_imod12_cases: "ob \<in> Object Imod1 \<inter> Object Imod2 \<or> ob \<in> Object Imod1 - Object Imod2 \<or> ob \<in> Object Imod2 - Object Imod1"
    by blast
  assume "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
  then have f_in_fields: "f \<in> Field (Tm Imod1) \<union> Field (Tm Imod2)"
    by (simp add: imod_combine_def tmod_combine_def)
  then have f_in_fields_cases: "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<or> f \<in> Field (Tm Imod1) - Field (Tm Imod2) \<or> f \<in> Field (Tm Imod2) - Field (Tm Imod1)"
    by blast
  assume subtype_combine: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  have imod1_subtype_cases: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
    by simp
  have imod2_subtype_cases: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<or> \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
    by simp
  have "imod_combine_field_value Imod1 Imod2 (ob, f) :[imod_combine Imod1 Imod2] fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f)"
    using ob_in_imod12_cases
  proof (elim disjE)
    assume ob_in_both: "ob \<in> Object Imod1 \<inter> Object Imod2"
    show ?thesis
      using f_in_fields_cases
    proof (elim disjE)
      assume f_in_both: "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2)"
      then have fieldsig_eq: "fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
        using structure_fieldsig_wellformed_type
        by blast
      then have fieldsig_def: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = fst (FieldSig (Tm Imod1) f)"
        unfolding tmod_combine_fieldsig_def
        using f_in_both
        by simp
      show ?thesis
        using imod1_subtype_cases imod2_subtype_cases
      proof (elim disjE)
        assume subtype_imod2: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        assume subtype_imod1: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have "FieldValue Imod1 (ob, f) :[Imod1] fst (FieldSig (Tm Imod1) f)"
          using IntD1 f_in_both imod1_correct instance_model.validity_values_typed ob_in_both type_def
          by metis
        then have "FieldValue Imod1 (ob, f) :[imod_combine Imod1 Imod2] fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f)"
          by (simp add: Valid_def fieldsig_def imod_combine_valid_rel_imod1 structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_both ob_in_both property_field_values_wellformed subtype_imod1 subtype_imod2
          by simp
      next
        assume subtype_imod1: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have "FieldValue Imod1 (ob, f) :[Imod1] fst (FieldSig (Tm Imod1) f)"
          using IntD1 f_in_both imod1_correct instance_model.validity_values_typed ob_in_both type_def
          by metis
        then have fieldvalue_imod1_def: "FieldValue Imod1 (ob, f) :[imod_combine Imod1 Imod2] fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f)"
          by (simp add: Valid_def fieldsig_def imod_combine_valid_rel_imod1 structure_object_class_wellformed)
        assume no_subtype_imod2: "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have "FieldValue Imod2 (ob, f) = unspecified"
          using IntD2 f_in_both imod2_correct instance_model.property_field_values_outside_domain ob_in_both
          by metis
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_both fieldvalue_imod1_def ob_in_both
          by auto
      next
        assume no_subtype_imod1: "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have fieldvalue_imod1_def: "FieldValue Imod1 (ob, f) = unspecified"
          using IntD1 f_in_both imod1_correct instance_model.property_field_values_outside_domain ob_in_both
          by metis
        assume subtype_imod2: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have "FieldValue Imod2 (ob, f) :[Imod2] fst (FieldSig (Tm Imod2) f)"
          using IntD2 f_in_both imod2_correct instance_model.validity_values_typed ob_in_both type_def
          by metis
        then have "FieldValue Imod2 (ob, f) :[imod_combine Imod1 Imod2] fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f)"
          by (simp add: Valid_def fieldsig_def fieldsig_eq imod_combine_valid_rel_imod2 structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_both fieldvalue_imod1_def ob_in_both
          by auto
      next
        assume no_subtype_imod1: "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        assume no_subtype_imod2: "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        show ?thesis
          using f_in_both no_subtype_imod1 no_subtype_imod2 ob_in_both property_field_values_not_subtype_imod1 subtype_combine
          by simp
      qed
    next
      assume f_in_imod1: "f \<in> Field (Tm Imod1) - Field (Tm Imod2)"
      then have fieldsig_def: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = fst (FieldSig (Tm Imod1) f)"
        unfolding tmod_combine_fieldsig_def
        by simp
      show ?thesis
        using imod1_subtype_cases
      proof (elim disjE)
        assume "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have "FieldValue Imod1 (ob, f) :[Imod1] fst (FieldSig (Tm Imod1) f)"
          using DiffD1 IntD1 f_in_imod1 imod1_correct instance_model.validity_values_typed ob_in_both type_def
          by metis
        then have "FieldValue Imod1 (ob, f) :[imod_combine Imod1 Imod2] fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f)"
          by (simp add: Valid_def fieldsig_def imod_combine_valid_rel_imod1 structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_imod1 ob_in_both
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then show ?thesis
          using f_in_imod1 ob_in_both property_field_values_not_field_imod2 subtype_combine
          by simp
      qed
    next
      assume f_in_imod2: "f \<in> Field (Tm Imod2) - Field (Tm Imod1)"
      then have fieldsig_def: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = fst (FieldSig (Tm Imod2) f)"
        unfolding tmod_combine_fieldsig_def
        by simp
      show ?thesis
        using imod2_subtype_cases
      proof (elim disjE)
        assume "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have "FieldValue Imod2 (ob, f) :[Imod2] fst (FieldSig (Tm Imod2) f)"
          using DiffD1 IntD2 f_in_imod2 imod2_correct instance_model.validity_values_typed ob_in_both type_def
          by metis
        then have "FieldValue Imod2 (ob, f) :[imod_combine Imod1 Imod2] fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f)"
          by (simp add: Valid_def fieldsig_def imod_combine_valid_rel_imod2 structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_imod2 ob_in_both
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then show ?thesis
          using f_in_imod2 ob_in_both property_field_values_not_field_imod1 subtype_combine
          by simp
      qed
    qed
  next
    assume ob_in_imod1: "ob \<in> Object Imod1 - Object Imod2"
    show ?thesis
    proof (induct "f \<in> Field (Tm Imod1)")
      case True
      then have fieldsig_def: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = fst (FieldSig (Tm Imod1) f)"
        unfolding tmod_combine_fieldsig_def
        using structure_fieldsig_wellformed_type
        by simp
      then show ?case
        using imod1_subtype_cases
      proof (elim disjE)
        assume "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have "FieldValue Imod1 (ob, f) :[Imod1] fst (FieldSig (Tm Imod1) f)"
          using DiffD1 True.hyps imod1_correct instance_model.validity_values_typed ob_in_imod1 type_def
          by metis
        then have "FieldValue Imod1 (ob, f) :[imod_combine Imod1 Imod2] fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f)"
          by (simp add: Valid_def fieldsig_def imod_combine_valid_rel_imod1 structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using True.hyps ob_in_imod1
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then show ?thesis
          using Diff_iff True.hyps ob_in_imod1 property_field_values_not_subtype_imod1 subtype_combine
          by metis
      qed
    next
      case False
      then show ?case
        using DiffD1 DiffD2 Int_iff f_in_fields_cases ob_in_imod1 property_field_values_not_field_imod1 subtype_combine
        by metis
    qed
  next
    assume ob_in_imod2: "ob \<in> Object Imod2 - Object Imod1"
    show ?thesis
    proof (induct "f \<in> Field (Tm Imod2)")
      case True
      then have fieldsig_def: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = fst (FieldSig (Tm Imod2) f)"
        unfolding tmod_combine_fieldsig_def
        using structure_fieldsig_wellformed_type
        by simp
      then show ?case
        using imod2_subtype_cases
      proof (elim disjE)
        assume "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have "FieldValue Imod2 (ob, f) :[Imod2] fst (FieldSig (Tm Imod2) f)"
          using DiffD1 True.hyps imod2_correct instance_model.validity_values_typed ob_in_imod2 type_def
          by metis
        then have "FieldValue Imod2 (ob, f) :[imod_combine Imod1 Imod2] fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f)"
          by (simp add: Valid_def fieldsig_def imod_combine_valid_rel_imod2 structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using True.hyps ob_in_imod2
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then show ?thesis
          using Diff_iff True.hyps ob_in_imod2 property_field_values_not_subtype_imod2 subtype_combine
          by metis
      qed
    next
      case False
      then show ?case
        using DiffD1 DiffD2 Int_iff f_in_fields_cases ob_in_imod2 property_field_values_not_field_imod2 subtype_combine
        by metis
    qed
  qed
  then show "FieldValue (imod_combine Imod1 Imod2) (ob, f) :[imod_combine Imod1 Imod2] type (Tm (imod_combine Imod1 Imod2)) f"
    by (simp add: imod_combine_def tmod_combine_def type_def)
next
  have structure_fieldsig_wellformed_type: "\<And>f. f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<Longrightarrow> fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
  proof-
    fix f
    assume f_in_both: "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2)"
    then have "f \<in> Field (tmod_combine (Tm Imod1) (Tm Imod2))"
      unfolding tmod_combine_def
      by simp
    then have "fst (FieldSig (tmod_combine (Tm Imod1) (Tm Imod2)) f) \<in> Type (tmod_combine (Tm Imod1) (Tm Imod2))"
      using validity_type_model_consistent type_model.structure_fieldsig_wellformed_type
      by blast
    then have fst_in_type: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) \<in> Type (tmod_combine (Tm Imod1) (Tm Imod2))"
      by (simp add: tmod_combine_def)
    then show "fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
    proof (induct "fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)")
      case True
      then show ?case
        by simp
    next
      case False
      then have "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = TypeDef.invalid"
        unfolding tmod_combine_fieldsig_def
        using f_in_both 
        by simp
      then have "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) \<notin> Type (tmod_combine (Tm Imod1) (Tm Imod2))"
        by simp
      then show ?case
        using fst_in_type
        by simp
    qed
  qed
  fix ob f
  assume "ob \<in> Object (imod_combine Imod1 Imod2)"
  then have ob_in_imod12: "ob \<in> Object Imod1 \<union> Object Imod2"
    by (simp add: imod_combine_def)
  then have ob_in_imod12_cases: "ob \<in> Object Imod1 \<inter> Object Imod2 \<or> ob \<in> Object Imod1 - Object Imod2 \<or> ob \<in> Object Imod2 - Object Imod1"
    by blast
  assume "f \<in> Field (Tm (imod_combine Imod1 Imod2))"
  then have f_in_fields: "f \<in> Field (Tm Imod1) \<union> Field (Tm Imod2)"
    by (simp add: imod_combine_def tmod_combine_def)
  then have f_in_fields_cases: "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2) \<or> f \<in> Field (Tm Imod1) - Field (Tm Imod2) \<or> f \<in> Field (Tm Imod2) - Field (Tm Imod1)"
    by blast
  assume subtype_combine: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  have imod1_subtype_cases: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
    by simp
  have imod2_subtype_cases: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<or> \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
    by simp
  have "validMul (imod_combine Imod1 Imod2) ((ob, f), imod_combine_field_value Imod1 Imod2 (ob, f))"
    using ob_in_imod12_cases
  proof (elim disjE)
    assume ob_in_both: "ob \<in> Object Imod1 \<inter> Object Imod2"
    show ?thesis
      using f_in_fields_cases
    proof (elim disjE)
      assume f_in_both: "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2)"
      then have fieldsig_eq: "fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
        using structure_fieldsig_wellformed_type
        by blast
      then have fieldsig_def: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = fst (FieldSig (Tm Imod1) f)"
        unfolding tmod_combine_fieldsig_def
        using f_in_both
        by simp
      have fieldsig_mult_def: "snd (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)"
        using f_in_both fieldsig_eq snd_conv tmod_combine_fieldsig_def
        by metis
      show ?thesis
        using imod1_subtype_cases imod2_subtype_cases
      proof (elim disjE)
        assume subtype_imod2: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        assume subtype_imod1: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have "FieldValue Imod1 (ob, f) :[Imod1] fst (FieldSig (Tm Imod1) f)"
          using IntD1 f_in_both imod1_correct instance_model.validity_values_typed ob_in_both type_def
          by metis
        then have fieldvalue_imod1_valid: "FieldValue Imod1 (ob, f) :[imod_combine Imod1 Imod2] fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f)"
          by (simp add: Valid_def fieldsig_def imod_combine_valid_rel_imod1 structure_object_class_wellformed)
        have fieldvalue_imod1_def: "FieldValue Imod1 (ob, f) \<in> Value Imod1"
          using IntD1 f_in_both imod1_correct instance_model.property_field_values_inside_domain ob_in_both subtype_imod1
          by metis
        show ?thesis
          unfolding validMul_def
        proof
          have "FieldValue Imod1 (ob, f) :[imod_combine Imod1 Imod2] fst (FieldSig (tmod_combine (Tm Imod1) (Tm Imod2)) f)"
            by (simp add: fieldvalue_imod1_valid tmod_combine_def)
          then have "FieldValue Imod1 (ob, f) :[imod_combine Imod1 Imod2] type (Tm (imod_combine Imod1 Imod2)) f"
            unfolding type_def
            by (simp add: imod_combine_def)
          then have "imod_combine_field_value Imod1 Imod2 (ob, f) :[imod_combine Imod1 Imod2] type (Tm (imod_combine Imod1 Imod2)) f"
            unfolding imod_combine_field_value_def
            using f_in_both ob_in_both property_field_values_wellformed subtype_imod1 subtype_imod2
            by simp
          then show "snd ((ob, f), imod_combine_field_value Imod1 Imod2 (ob, f)) :[imod_combine Imod1 Imod2] type (Tm (imod_combine Imod1 Imod2)) (snd (fst ((ob, f), imod_combine_field_value Imod1 Imod2 (ob, f))))"
            by simp
        next
          have "FieldValue Imod1 (ob, f) \<in> ContainerValue Imod1 \<Longrightarrow>
            Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and>
            \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
            using f_in_both ob_in_both subtype_imod1 validity_multiplicities_valid_imod1
            by simp
          then have "FieldValue Imod1 (ob, f) \<in> ContainerValue (imod_combine Imod1 Imod2) \<Longrightarrow>
            Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and>
            \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
            using Int_iff Un_iff Value_def container_values_atom_values_intersect fieldvalue_imod1_def
            by metis
          then have "FieldValue Imod1 (ob, f) \<in> ContainerValue (imod_combine Imod1 Imod2) \<Longrightarrow>
            lower (Tm (imod_combine Imod1 Imod2)) f \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and>
            \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> upper (Tm (imod_combine Imod1 Imod2)) f"
            unfolding lower_def upper_def
            by (simp add: fieldsig_mult_def imod_combine_def tmod_combine_def)
          then have "imod_combine_field_value Imod1 Imod2 (ob, f) \<in> ContainerValue (imod_combine Imod1 Imod2) \<Longrightarrow>
            lower (Tm (imod_combine Imod1 Imod2)) f \<le> \<^bold>(length (contained_list (imod_combine_field_value Imod1 Imod2 (ob, f)))) \<and>
            \<^bold>(length (contained_list (imod_combine_field_value Imod1 Imod2 (ob, f)))) \<le> upper (Tm (imod_combine Imod1 Imod2)) f"
            unfolding imod_combine_field_value_def
            using f_in_both ob_in_both property_field_values_wellformed subtype_imod1 subtype_imod2
            by simp
          then show "snd ((ob, f), imod_combine_field_value Imod1 Imod2 (ob, f)) \<in> ContainerValue (imod_combine Imod1 Imod2) \<longrightarrow>
            lower (Tm (imod_combine Imod1 Imod2)) (snd (fst ((ob, f), imod_combine_field_value Imod1 Imod2 (ob, f)))) \<le> \<^bold>(length (contained_list (snd ((ob, f), imod_combine_field_value Imod1 Imod2 (ob, f))))) \<and>
            \<^bold>(length (contained_list (snd ((ob, f), imod_combine_field_value Imod1 Imod2 (ob, f))))) \<le> upper (Tm (imod_combine Imod1 Imod2)) (snd (fst ((ob, f), imod_combine_field_value Imod1 Imod2 (ob, f))))"
            by simp
        qed
      next
        assume subtype_imod1: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have fieldvalue_imod1_def: "FieldValue Imod1 (ob, f) \<in> Value Imod1"
          using IntD1 f_in_both imod1_correct instance_model.property_field_values_inside_domain ob_in_both
          by metis
        have valid_mul_imod1_def: "validMul Imod1 ((ob, f), FieldValue Imod1 (ob, f))"
          using IntD1 f_in_both imod1_correct instance_model.validity_multiplicities_valid ob_in_both subtype_imod1
          by metis
        assume no_subtype_imod2: "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have fieldvalue_imod2_def: "FieldValue Imod2 (ob, f) = unspecified"
          using IntD2 f_in_both imod2_correct instance_model.property_field_values_outside_domain ob_in_both
          by metis
        have "validMul (imod_combine Imod1 Imod2) ((ob, f), FieldValue Imod1 (ob, f))"
        proof (intro imod_combine_valid_mul_imod1)
          show "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow>
            ob \<notin> Object Imod2 \<or> \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> FieldValue Imod1 (ob, f) \<in> ContainerValue Imod1 \<Longrightarrow>
            Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and> 
            \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
            using validity_multiplicities_valid_imod1
            by blast
        next
          show "ob \<in> Object Imod1"
            using ob_in_both
            by blast
        next
          show "f \<in> Field (Tm Imod1)"
            using f_in_both
            by blast
        qed (simp_all add: subtype_imod1 no_subtype_imod2 fieldvalue_imod1_def valid_mul_imod1_def structure_fieldsig_wellformed_type structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_both fieldvalue_imod2_def ob_in_both
          by auto
      next
        assume no_subtype_imod1: "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have fieldvalue_imod1_def: "FieldValue Imod1 (ob, f) = unspecified"
          using IntD1 f_in_both imod1_correct instance_model.property_field_values_outside_domain ob_in_both
          by metis
        assume subtype_imod2: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have fieldvalue_imod2_def: "FieldValue Imod2 (ob, f) \<in> Value Imod2"
          using IntD2 f_in_both imod2_correct instance_model.property_field_values_inside_domain ob_in_both
          by metis
        have valid_mul_imod2_def: "validMul Imod2 ((ob, f), FieldValue Imod2 (ob, f))"
          using IntD2 f_in_both imod2_correct instance_model.validity_multiplicities_valid ob_in_both subtype_imod2
          by metis
        have "validMul (imod_combine Imod1 Imod2) ((ob, f), FieldValue Imod2 (ob, f))"
        proof (intro imod_combine_valid_mul_imod2)
          show "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow>
            ob \<notin> Object Imod1 \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> FieldValue Imod2 (ob, f) \<in> ContainerValue Imod2 \<Longrightarrow>
            Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<and> 
            \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
            using validity_multiplicities_valid_imod2
            by blast
        next
          show "ob \<in> Object Imod2"
            using ob_in_both
            by blast
        next
          show "f \<in> Field (Tm Imod2)"
            using f_in_both
            by blast
        qed (simp_all add: no_subtype_imod1 subtype_imod2 fieldvalue_imod2_def valid_mul_imod2_def structure_fieldsig_wellformed_type structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_both fieldvalue_imod1_def ob_in_both
          by auto
      next
        assume no_subtype_imod1: "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        assume no_subtype_imod2: "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        show ?thesis
          using f_in_both no_subtype_imod1 no_subtype_imod2 ob_in_both property_field_values_not_subtype_imod1 subtype_combine
          by simp
      qed
    next
      assume f_in_imod1: "f \<in> Field (Tm Imod1) - Field (Tm Imod2)"
      then have fieldsig_def: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = fst (FieldSig (Tm Imod1) f)"
        unfolding tmod_combine_fieldsig_def
        by simp
      show ?thesis
        using imod1_subtype_cases
      proof (elim disjE)
        assume subtype_imod1: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have fieldvalue_imod1_def: "FieldValue Imod1 (ob, f) \<in> Value Imod1"
          using DiffD1 IntD1 f_in_imod1 imod1_correct instance_model.property_field_values_inside_domain ob_in_both
          by metis
        have valid_mul_imod1_def: "validMul Imod1 ((ob, f), FieldValue Imod1 (ob, f))"
          using DiffD1 IntD1 f_in_imod1 imod1_correct instance_model.validity_multiplicities_valid ob_in_both subtype_imod1
          by metis
        have "validMul (imod_combine Imod1 Imod2) ((ob, f), FieldValue Imod1 (ob, f))"
        proof (intro imod_combine_valid_mul_imod1)
          show "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow>
            ob \<notin> Object Imod2 \<or> \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> FieldValue Imod1 (ob, f) \<in> ContainerValue Imod1 \<Longrightarrow>
            Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and> 
            \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
            using validity_multiplicities_valid_imod1
            by blast
        next
          show "ob \<in> Object Imod1"
            using ob_in_both
            by blast
        next
          show "f \<in> Field (Tm Imod1)"
            using f_in_imod1
            by blast
        next
          show "ob \<notin> Object Imod2 \<or> f \<notin> Field (Tm Imod2) \<or> \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
            using f_in_imod1
            by blast
        qed (simp_all add: subtype_imod1 fieldvalue_imod1_def valid_mul_imod1_def structure_fieldsig_wellformed_type structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_imod1 ob_in_both
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then show ?thesis
          using f_in_imod1 ob_in_both property_field_values_not_field_imod2 subtype_combine
          by simp
      qed
    next
      assume f_in_imod2: "f \<in> Field (Tm Imod2) - Field (Tm Imod1)"
      then have fieldsig_def: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = fst (FieldSig (Tm Imod2) f)"
        unfolding tmod_combine_fieldsig_def
        by simp
      show ?thesis
        using imod2_subtype_cases
      proof (elim disjE)
        assume subtype_imod2: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have fieldvalue_imod2_def: "FieldValue Imod2 (ob, f) \<in> Value Imod2"
          using DiffD1 IntD2 f_in_imod2 imod2_correct instance_model.property_field_values_inside_domain ob_in_both
          by metis
        have valid_mul_imod2_def: "validMul Imod2 ((ob, f), FieldValue Imod2 (ob, f))"
          using DiffD1 IntD2 f_in_imod2 imod2_correct instance_model.validity_multiplicities_valid ob_in_both subtype_imod2
          by metis
        have "validMul (imod_combine Imod1 Imod2) ((ob, f), FieldValue Imod2 (ob, f))"
        proof (intro imod_combine_valid_mul_imod2)
          show "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow>
            ob \<notin> Object Imod1 \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> FieldValue Imod2 (ob, f) \<in> ContainerValue Imod2 \<Longrightarrow>
            Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<and> 
            \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
            using validity_multiplicities_valid_imod2
            by blast
        next
          show "ob \<in> Object Imod2"
            using ob_in_both
            by blast
        next
          show "f \<in> Field (Tm Imod2)"
            using f_in_imod2
            by blast
        next
          show "ob \<notin> Object Imod1 \<or> f \<notin> Field (Tm Imod1) \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
            using f_in_imod2
            by blast
        qed (simp_all add: subtype_imod2 fieldvalue_imod2_def valid_mul_imod2_def structure_fieldsig_wellformed_type structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using f_in_imod2 ob_in_both
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then show ?thesis
          using f_in_imod2 ob_in_both property_field_values_not_field_imod1 subtype_combine
          by simp
      qed
    qed
  next
    assume ob_in_imod1: "ob \<in> Object Imod1 - Object Imod2"
    show ?thesis
    proof (induct "f \<in> Field (Tm Imod1)")
      case True
      then have fieldsig_def: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = fst (FieldSig (Tm Imod1) f)"
        unfolding tmod_combine_fieldsig_def
        using structure_fieldsig_wellformed_type
        by simp
      then show ?case
        using imod1_subtype_cases
      proof (elim disjE)
        assume subtype_imod1: "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then have fieldvalue_imod1_def: "FieldValue Imod1 (ob, f) \<in> Value Imod1"
          using DiffD1 True.hyps imod1_correct instance_model.property_field_values_inside_domain ob_in_imod1
          by metis
        have valid_mul_imod1_def: "validMul Imod1 ((ob, f), FieldValue Imod1 (ob, f))"
          using DiffD1 True.hyps imod1_correct instance_model.validity_multiplicities_valid ob_in_imod1 subtype_imod1
          by metis
        have "validMul (imod_combine Imod1 Imod2) ((ob, f), FieldValue Imod1 (ob, f))"
        proof (intro imod_combine_valid_mul_imod1)
          show "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow>
            ob \<notin> Object Imod2 \<or> \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow> FieldValue Imod1 (ob, f) \<in> ContainerValue Imod1 \<Longrightarrow>
            Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and> 
            \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
            using validity_multiplicities_valid_imod1
            by blast
        next
          show "ob \<in> Object Imod1"
            using ob_in_imod1
            by blast
        next
          show "f \<in> Field (Tm Imod1)"
            using True.hyps
            by blast
        next
          show "ob \<notin> Object Imod2 \<or> f \<notin> Field (Tm Imod2) \<or> \<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
            using ob_in_imod1
            by blast
        qed (simp_all add: subtype_imod1 fieldvalue_imod1_def valid_mul_imod1_def structure_fieldsig_wellformed_type structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using True.hyps ob_in_imod1
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
        then show ?thesis
          using Diff_iff True.hyps ob_in_imod1 property_field_values_not_subtype_imod1 subtype_combine
          by metis
      qed
    next
      case False
      then show ?case
        using DiffD1 DiffD2 Int_iff f_in_fields_cases ob_in_imod1 property_field_values_not_field_imod1 subtype_combine
        by metis
    qed
  next
    assume ob_in_imod2: "ob \<in> Object Imod2 - Object Imod1"
    show ?thesis
    proof (induct "f \<in> Field (Tm Imod2)")
      case True
      then have fieldsig_def: "fst (tmod_combine_fieldsig (Tm Imod1) (Tm Imod2) f) = fst (FieldSig (Tm Imod2) f)"
        unfolding tmod_combine_fieldsig_def
        using structure_fieldsig_wellformed_type
        by simp
      then show ?case
        using imod2_subtype_cases
      proof (elim disjE)
        assume subtype_imod2: "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then have fieldvalue_imod2_def: "FieldValue Imod2 (ob, f) \<in> Value Imod2"
          using DiffD1 True.hyps imod2_correct instance_model.property_field_values_inside_domain ob_in_imod2
          by metis
        have valid_mul_imod2_def: "validMul Imod2 ((ob, f), FieldValue Imod2 (ob, f))"
          using DiffD1 True.hyps imod2_correct instance_model.validity_multiplicities_valid ob_in_imod2 subtype_imod2
          by metis
        have "validMul (imod_combine Imod1 Imod2) ((ob, f), FieldValue Imod2 (ob, f))"
        proof (intro imod_combine_valid_mul_imod2)
          show "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f) \<Longrightarrow>
            ob \<notin> Object Imod1 \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f) \<Longrightarrow> FieldValue Imod2 (ob, f) \<in> ContainerValue Imod2 \<Longrightarrow>
            Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<and> 
            \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
            using validity_multiplicities_valid_imod2
            by blast
        next
          show "ob \<in> Object Imod2"
            using ob_in_imod2
            by blast
        next
          show "f \<in> Field (Tm Imod2)"
            using True.hyps
            by blast
        next
          show "ob \<notin> Object Imod1 \<or> f \<notin> Field (Tm Imod1) \<or> \<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
            using ob_in_imod2
            by blast
        qed (simp_all add: subtype_imod2 fieldvalue_imod2_def valid_mul_imod2_def structure_fieldsig_wellformed_type structure_object_class_wellformed)
        then show ?thesis
          unfolding imod_combine_field_value_def
          using True.hyps ob_in_imod2
          by simp
      next
        assume "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        then show ?thesis
          using Diff_iff True.hyps ob_in_imod2 property_field_values_not_subtype_imod2 subtype_combine
          by metis
      qed
    next
      case False
      then show ?case
        using DiffD1 DiffD2 Int_iff f_in_fields_cases ob_in_imod2 property_field_values_not_field_imod2 subtype_combine
        by metis
    qed
  qed
  then show "validMul (imod_combine Imod1 Imod2) ((ob, f), FieldValue (imod_combine Imod1 Imod2) (ob, f))"
    by (simp add: imod_combine_def)
next
  fix p
  assume "p \<in> Prop (Tm (imod_combine Imod1 Imod2))"
  then have "p \<in> tmod_combine_prop (Tm Imod1) (Tm Imod2)"
    by (simp add: imod_combine_def tmod_combine_def)
  then show "imod_combine Imod1 Imod2 \<Turnstile> p"
  proof (induct)
    case (abstract_property_tmod1 c)
    then have "Imod1 \<Turnstile> abstract c"
      using imod1_correct instance_model.validity_properties_satisfied
      by blast
    then have imod1_no_instance: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ObjectClass Imod1 ob \<noteq> c"
      using property_satisfaction_abstract_rev
      by fastforce
    have imod2_no_instance: "\<And>ob. ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod2 ob \<noteq> c"
      using abstract_property_tmod1.hyps(2) imod2_correct instance_model.structure_object_class_wellformed
      by fastforce
    show ?case
    proof (intro property_satisfaction.rule_property_abstract)
      fix ob
      assume "ob \<in> Object (imod_combine Imod1 Imod2)"
      then have "ob \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have "imod_combine_object_class Imod1 Imod2 ob \<noteq> c"
        using imod1_no_instance imod2_no_instance Int_iff Un_iff imod_combine_object_class_def structure_object_class_wellformed
        by metis
      then show "ObjectClass (imod_combine Imod1 Imod2) ob \<noteq> c"
        by (simp add: imod_combine_def)
    qed
  next
    case (abstract_property_tmod2 c)
    then have "Imod2 \<Turnstile> abstract c"
      using imod2_correct instance_model.validity_properties_satisfied
      by blast
    then have imod2_no_instance: "\<And>ob. ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod2 ob \<noteq> c"
      using property_satisfaction_abstract_rev
      by fastforce
    have imod1_no_instance: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ObjectClass Imod1 ob \<noteq> c"
      using abstract_property_tmod2.hyps(2) imod1_correct instance_model.structure_object_class_wellformed
      by fastforce
    show ?case
    proof (intro property_satisfaction.rule_property_abstract)
      fix ob
      assume "ob \<in> Object (imod_combine Imod1 Imod2)"
      then have "ob \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have "imod_combine_object_class Imod1 Imod2 ob \<noteq> c"
        using imod1_no_instance imod2_no_instance Int_iff Un_iff imod_combine_object_class_def structure_object_class_wellformed
        by metis
      then show "ObjectClass (imod_combine Imod1 Imod2) ob \<noteq> c"
        by (simp add: imod_combine_def)
    qed
  next
    case (abstract_property_both c)
    then have "Imod1 \<Turnstile> abstract c"
      using imod1_correct instance_model.validity_properties_satisfied
      by blast
    then have imod1_no_instance: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ObjectClass Imod1 ob \<noteq> c"
      using property_satisfaction_abstract_rev
      by fastforce
    have "Imod2 \<Turnstile> abstract c"
      using abstract_property_both.hyps(2) imod2_correct instance_model.validity_properties_satisfied
      by blast
    then have imod2_no_instance: "\<And>ob. ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod2 ob \<noteq> c"
      using property_satisfaction_abstract_rev
      by fastforce
    show ?case
    proof (intro property_satisfaction.rule_property_abstract)
      fix ob
      assume "ob \<in> Object (imod_combine Imod1 Imod2)"
      then have "ob \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have "imod_combine_object_class Imod1 Imod2 ob \<noteq> c"
        using imod1_no_instance imod2_no_instance Int_iff Un_iff imod_combine_object_class_def structure_object_class_wellformed
        by metis
      then show "ObjectClass (imod_combine Imod1 Imod2) ob \<noteq> c"
        by (simp add: imod_combine_def)
    qed
  next
    case (containment_property_tmod1 r)
    then have "Imod1 \<Turnstile> containment r"
      using imod1_correct instance_model.validity_properties_satisfied
      by blast
    then have imod1_containment: "\<And>ob. (ob \<in> Object Imod1 \<longrightarrow> card (object_containments Imod1 ob) \<le> 1) \<and> 
      irrefl ((object_containments_relation Imod1)\<^sup>+)"
      using property_satisfaction_containment_rev
      by simp
    have "containment r \<in> Property (Tm Imod1)"
      using imod1_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed containment_property_tmod1.hyps
      by blast
    then have containment_props: "r \<in> Rel (Tm Imod1)"
      using properties_rev_impl_containment
      by blast
    show ?case
    proof (intro property_satisfaction.rule_property_containment)
      fix ob
      assume "ob \<in> Object (imod_combine Imod1 Imod2)"
      then have "ob \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then show "card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
        using UnCI containment_property_tmod1.hyps validity_containment_properties_satisfied
        by metis
    next
      show "irrefl ((object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+)"
        by (fact validity_containments_relation)
    qed
  next
    case (containment_property_tmod2 r)
    then have "Imod2 \<Turnstile> containment r"
      using imod2_correct instance_model.validity_properties_satisfied
      by blast
    then have imod2_containment: "\<And>ob. (ob \<in> Object Imod2 \<longrightarrow> card (object_containments Imod2 ob) \<le> 1) \<and> 
      irrefl ((object_containments_relation Imod2)\<^sup>+)"
      using property_satisfaction_containment_rev
      by simp
    have "containment r \<in> Property (Tm Imod2)"
      using imod2_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed containment_property_tmod2.hyps
      by blast
    then have containment_props: "r \<in> Rel (Tm Imod2)"
      using properties_rev_impl_containment
      by blast
    show ?case
    proof (intro property_satisfaction.rule_property_containment)
      fix ob
      assume "ob \<in> Object (imod_combine Imod1 Imod2)"
      then have "ob \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then show "card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
        using UnCI containment_property_tmod2.hyps validity_containment_properties_satisfied
        by metis
    next
      show "irrefl ((object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+)"
        by (fact validity_containments_relation)
    qed
  next
    case (default_value_property_tmod1 f v)
    then show ?case
      using property_satisfaction.rule_property_defaultValue
      by blast
  next
    case (default_value_property_tmod2 f v)
    then show ?case
      using property_satisfaction.rule_property_defaultValue
      by blast
  next
    case (default_value_property_both f v)
    then show ?case
      using property_satisfaction.rule_property_defaultValue
      by blast
  next
    case (identity_property_tmod1 c A)
    then have "Imod1 \<Turnstile> identity c A"
      using imod1_correct instance_model.validity_properties_satisfied
      by blast
    then have imod1_identity: "\<And>o1 o2 a. o1 \<in> Object Imod1 \<Longrightarrow> o2 \<in> Object Imod1 \<Longrightarrow> 
      ObjectClass Imod1 o1 = c \<Longrightarrow> ObjectClass Imod1 o2 = c \<Longrightarrow> a \<in> A \<Longrightarrow> 
      FieldValue Imod1 (o1, a) \<equiv>[Imod1] FieldValue Imod1 (o2, a) \<Longrightarrow> o1 = o2"
      using property_satisfaction_identity_rev
      by metis
    have "identity c A \<in> Property (Tm Imod1)"
      using imod1_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed identity_property_tmod1.hyps(1)
      by blast
    then have identity_props: "c \<in> Class (Tm Imod1) \<and> A \<subseteq> Type_Model.fields (Tm Imod1) c"
      using properties_rev_impl_identity
      by blast
    have imod2_no_instance: "\<And>ob. ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod2 ob \<noteq> c"
      using identity_property_tmod1.hyps(2) imod2_correct instance_model.structure_object_class_wellformed
      by fastforce
    show ?case
    proof (intro property_satisfaction.rule_property_identity)
      fix o1 o2 a
      assume "o1 \<in> Object (imod_combine Imod1 Imod2)"
      then have o1_in_object: "o1 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      assume "o2 \<in> Object (imod_combine Imod1 Imod2)"
      then have o2_in_object: "o2 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      assume object_class_o1: "ObjectClass (imod_combine Imod1 Imod2) o1 = c"
      assume object_class_o2: "ObjectClass (imod_combine Imod1 Imod2) o2 = c"
      assume a_in_a: "a \<in> A"
      then have a_in_field: "a \<in> Field (Tm Imod1) \<and> \<exclamdown>c \<sqsubseteq>[Tm Imod1] \<exclamdown>(fst a)"
        using identity_props
        unfolding Type_Model.fields_def
        by fastforce
      assume value_equiv: "FieldValue (imod_combine Imod1 Imod2) (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue (imod_combine Imod1 Imod2) (o2, a)"
      show "o1 = o2"
        using o1_in_object o2_in_object
      proof (elim UnE)
        assume o1_in_imod1: "o1 \<in> Object Imod1"
        then have o1_object_class_imod1: "ObjectClass Imod1 o1 = c"
          using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o1 structure_object_class_wellformed
          by metis
        then have o1_not_in_imod2: "o1 \<notin> Object Imod2"
          using imod2_no_instance o1_in_imod1 structure_object_class_wellformed
          by fastforce
        then have "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod1 (o1, a)"
          unfolding imod_combine_field_value_def class_def
          using o1_in_imod1 o1_object_class_imod1 a_in_field
          by simp
        then have o1_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o1, a) = FieldValue Imod1 (o1, a)"
          by (simp add: imod_combine_def)
        have o1_value: "FieldValue Imod1 (o1, a) \<in> Value Imod1"
          by (simp add: a_in_field class_def imod1_correct instance_model.property_field_values_inside_domain o1_in_imod1 o1_object_class_imod1)
        assume o2_in_imod1: "o2 \<in> Object Imod1"
        then have o2_object_class_imod1: "ObjectClass Imod1 o2 = c"
          using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o2 structure_object_class_wellformed
          by metis
        then have o2_not_in_imod2: "o2 \<notin> Object Imod2"
          using imod2_no_instance o2_in_imod1 structure_object_class_wellformed
          by fastforce
        then have "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod1 (o2, a)"
          unfolding imod_combine_field_value_def class_def
          using o2_in_imod1 o2_object_class_imod1 a_in_field
          by simp
        then have o2_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o2, a) = FieldValue Imod1 (o2, a)"
          by (simp add: imod_combine_def)
        have o2_value: "FieldValue Imod1 (o2, a) \<in> Value Imod1"
          by (simp add: a_in_field class_def imod1_correct instance_model.property_field_values_inside_domain o2_in_imod1 o2_object_class_imod1)
        have "FieldValue Imod1 (o1, a) \<equiv>[Imod1] FieldValue Imod1 (o2, a)"
          using imod_combine_value_equiv_imod1_rev o1_fieldvalue o1_value o2_fieldvalue o2_value value_equiv
          by metis
        then show "o1 = o2"
          using a_in_a imod1_identity o1_in_imod1 o1_object_class_imod1 o2_in_imod1 o2_object_class_imod1
          by blast
      next
        assume o1_in_imod1: "o1 \<in> Object Imod1"
        assume o2_in_imod2: "o2 \<in> Object Imod2"
        then have "ObjectClass (imod_combine Imod1 Imod2) o2 \<noteq> c"
          by (simp add: imod2_no_instance imod_combine_def imod_combine_object_class_def structure_object_class_wellformed)
        then show "o1 = o2"
          using object_class_o2
          by simp
      next
        assume o2_in_imod1: "o2 \<in> Object Imod1"
        assume o1_in_imod1: "o1 \<in> Object Imod2"
        then have "ObjectClass (imod_combine Imod1 Imod2) o1 \<noteq> c"
          by (simp add: imod2_no_instance imod_combine_def imod_combine_object_class_def structure_object_class_wellformed)
        then show "o1 = o2"
          using object_class_o1
          by simp
      next
        assume o1_in_imod1: "o1 \<in> Object Imod2"
        assume o2_in_imod2: "o2 \<in> Object Imod2"
        then have "ObjectClass (imod_combine Imod1 Imod2) o2 \<noteq> c"
          by (simp add: imod2_no_instance imod_combine_def imod_combine_object_class_def structure_object_class_wellformed)
        then show "o1 = o2"
          using object_class_o2
          by simp
      qed
    qed
  next
    case (identity_property_tmod2 c A)
    then have "Imod2 \<Turnstile> identity c A"
      using imod2_correct instance_model.validity_properties_satisfied
      by blast
    then have imod2_identity: "\<And>o1 o2 a. o1 \<in> Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 \<Longrightarrow> 
      ObjectClass Imod2 o1 = c \<Longrightarrow> ObjectClass Imod2 o2 = c \<Longrightarrow> a \<in> A \<Longrightarrow> 
      FieldValue Imod2 (o1, a) \<equiv>[Imod2] FieldValue Imod2 (o2, a) \<Longrightarrow> o1 = o2"
      using property_satisfaction_identity_rev
      by metis
    have "identity c A \<in> Property (Tm Imod2)"
      using imod2_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed identity_property_tmod2.hyps(1)
      by blast
    then have identity_props: "c \<in> Class (Tm Imod2) \<and> A \<subseteq> Type_Model.fields (Tm Imod2) c"
      using properties_rev_impl_identity
      by blast
    have imod1_no_instance: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ObjectClass Imod1 ob \<noteq> c"
      using identity_property_tmod2.hyps(2) imod1_correct instance_model.structure_object_class_wellformed
      by fastforce
    show ?case
    proof (intro property_satisfaction.rule_property_identity)
      fix o1 o2 a
      assume "o1 \<in> Object (imod_combine Imod1 Imod2)"
      then have o1_in_object: "o1 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      assume "o2 \<in> Object (imod_combine Imod1 Imod2)"
      then have o2_in_object: "o2 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      assume object_class_o1: "ObjectClass (imod_combine Imod1 Imod2) o1 = c"
      assume object_class_o2: "ObjectClass (imod_combine Imod1 Imod2) o2 = c"
      assume a_in_a: "a \<in> A"
      then have a_in_field: "a \<in> Field (Tm Imod2) \<and> \<exclamdown>c \<sqsubseteq>[Tm Imod2] \<exclamdown>(fst a)"
        using identity_props
        unfolding Type_Model.fields_def
        by fastforce
      assume value_equiv: "FieldValue (imod_combine Imod1 Imod2) (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue (imod_combine Imod1 Imod2) (o2, a)"
      show "o1 = o2"
        using o1_in_object o2_in_object
      proof (elim UnE)
        assume o1_in_imod1: "o1 \<in> Object Imod1"
        assume o2_in_imod1: "o2 \<in> Object Imod1"
        then have "ObjectClass (imod_combine Imod1 Imod2) o2 \<noteq> c"
          using Int_iff imod1_no_instance imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) structure_object_class_wellformed
          by metis
        then show "o1 = o2"
          using object_class_o2
          by simp
      next
        assume o2_in_imod2: "o2 \<in> Object Imod2"
        assume o1_in_imod1: "o1 \<in> Object Imod1"
        then have "ObjectClass (imod_combine Imod1 Imod2) o1 \<noteq> c"
          using Int_iff imod1_no_instance imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) structure_object_class_wellformed
          by metis
        then show "o1 = o2"
          using object_class_o1
          by simp
      next
        assume o1_in_imod2: "o1 \<in> Object Imod2"
        assume o2_in_imod1: "o2 \<in> Object Imod1"
        then have "ObjectClass (imod_combine Imod1 Imod2) o2 \<noteq> c"
          using Int_iff imod1_no_instance imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) structure_object_class_wellformed
          by metis
        then show "o1 = o2"
          using object_class_o2
          by simp
      next
        assume o1_in_imod2: "o1 \<in> Object Imod2"
        then have o1_object_class_imod2: "ObjectClass Imod2 o1 = c"
          using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o1 structure_object_class_wellformed
          by metis
        then have o1_not_in_imod2: "o1 \<notin> Object Imod1"
          using imod1_no_instance o1_in_imod2 structure_object_class_wellformed
          by fastforce
        then have "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod2 (o1, a)"
          unfolding imod_combine_field_value_def class_def
          using o1_in_imod2 o1_object_class_imod2 a_in_field
          by simp
        then have o1_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o1, a) = FieldValue Imod2 (o1, a)"
          by (simp add: imod_combine_def)
        have o1_value: "FieldValue Imod2 (o1, a) \<in> Value Imod2"
          by (simp add: a_in_field class_def imod2_correct instance_model.property_field_values_inside_domain o1_in_imod2 o1_object_class_imod2)
        assume o2_in_imod2: "o2 \<in> Object Imod2"
        then have o2_object_class_imod2: "ObjectClass Imod2 o2 = c"
          using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o2 structure_object_class_wellformed
          by metis
        then have o2_not_in_imod2: "o2 \<notin> Object Imod1"
          using imod1_no_instance o2_in_imod2 structure_object_class_wellformed
          by fastforce
        then have "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod2 (o2, a)"
          unfolding imod_combine_field_value_def class_def
          using o2_in_imod2 o2_object_class_imod2 a_in_field
          by simp
        then have o2_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o2, a) = FieldValue Imod2 (o2, a)"
          by (simp add: imod_combine_def)
        have o2_value: "FieldValue Imod2 (o2, a) \<in> Value Imod2"
          by (simp add: a_in_field class_def imod2_correct instance_model.property_field_values_inside_domain o2_in_imod2 o2_object_class_imod2)
        have "FieldValue Imod2 (o1, a) \<equiv>[Imod2] FieldValue Imod2 (o2, a)"
          using imod_combine_value_equiv_imod2_rev o1_fieldvalue o1_value o2_fieldvalue o2_value value_equiv
          by metis
        then show "o1 = o2"
          using a_in_a imod2_identity o1_in_imod2 o1_object_class_imod2 o2_in_imod2 o2_object_class_imod2
          by blast
      qed
    qed
  next
    case (identity_property_both c A)
    have "Imod1 \<Turnstile> identity c A"
      using identity_property_both.hyps(1) imod1_correct instance_model.validity_properties_satisfied
      by blast
    then have imod1_identity: "\<And>o1 o2 a. o1 \<in> Object Imod1 \<Longrightarrow> o2 \<in> Object Imod1 \<Longrightarrow> 
      ObjectClass Imod1 o1 = c \<Longrightarrow> ObjectClass Imod1 o2 = c \<Longrightarrow> a \<in> A \<Longrightarrow> 
      FieldValue Imod1 (o1, a) \<equiv>[Imod1] FieldValue Imod1 (o2, a) \<Longrightarrow> o1 = o2"
      using property_satisfaction_identity_rev
      by metis
    have "identity c A \<in> Property (Tm Imod1)"
      using imod1_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed identity_property_both.hyps(1)
      by blast
    then have identity_props1: "c \<in> Class (Tm Imod1) \<and> A \<subseteq> Type_Model.fields (Tm Imod1) c"
      using properties_rev_impl_identity
      by blast
    have "Imod2 \<Turnstile> identity c A"
      using identity_property_both.hyps(2) imod2_correct instance_model.validity_properties_satisfied
      by blast
    then have imod2_identity: "\<And>o1 o2 a. o1 \<in> Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 \<Longrightarrow> 
      ObjectClass Imod2 o1 = c \<Longrightarrow> ObjectClass Imod2 o2 = c \<Longrightarrow> a \<in> A \<Longrightarrow> 
      FieldValue Imod2 (o1, a) \<equiv>[Imod2] FieldValue Imod2 (o2, a) \<Longrightarrow> o1 = o2"
      using property_satisfaction_identity_rev
      by metis
    have "identity c A \<in> Property (Tm Imod2)"
      using imod2_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed identity_property_both.hyps(2)
      by blast
    then have identity_props2: "c \<in> Class (Tm Imod2) \<and> A \<subseteq> Type_Model.fields (Tm Imod2) c"
      using properties_rev_impl_identity
      by blast
    show ?case
    proof (intro property_satisfaction.rule_property_identity)
      fix o1 o2 a
      assume "o1 \<in> Object (imod_combine Imod1 Imod2)"
      then have o1_in_object: "o1 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have "o1 \<in> Object Imod1 \<inter> Object Imod2 \<or> o1 \<in> Object Imod1 - Object Imod2 \<or> o1 \<in> Object Imod2 - Object Imod1"
        by blast
      assume "o2 \<in> Object (imod_combine Imod1 Imod2)"
      then have o2_in_object: "o2 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have "o2 \<in> Object Imod1 \<inter> Object Imod2 \<or> o2 \<in> Object Imod1 - Object Imod2 \<or> o2 \<in> Object Imod2 - Object Imod1"
        by blast
      assume object_class_o1: "ObjectClass (imod_combine Imod1 Imod2) o1 = c"
      assume object_class_o2: "ObjectClass (imod_combine Imod1 Imod2) o2 = c"
      assume a_in_a: "a \<in> A"
      have a_in_field_tmod1: "a \<in> Field (Tm Imod1) \<and> \<exclamdown>c \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)"
        using identity_props1 a_in_a
        unfolding Type_Model.fields_def class_def
        by fastforce
      have a_in_field_tmod2: "a \<in> Field (Tm Imod2) \<and> \<exclamdown>c \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)"
        using identity_props2 a_in_a
        unfolding Type_Model.fields_def class_def
        by fastforce
      assume value_equiv: "FieldValue (imod_combine Imod1 Imod2) (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue (imod_combine Imod1 Imod2) (o2, a)"
      show "o1 = o2"
        using o1_in_object o2_in_object
      proof (elim UnE)
        assume o1_in_imod1: "o1 \<in> Object Imod1"
        then have o1_object_class_imod1: "ObjectClass Imod1 o1 = c"
          using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o1 structure_object_class_wellformed
          by metis
        then have "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod1 (o1, a)"
          unfolding imod_combine_field_value_def
        proof (induct "o1 \<in> Object Imod2")
          case True
          then show ?case
            using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2 o1_in_imod1
            by simp
        next
          case False
          then show ?case
            using a_in_field_tmod1 o1_in_imod1
            by simp
        qed
        then have o1_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o1, a) = FieldValue Imod1 (o1, a)"
          by (simp add: imod_combine_def)
        have o1_value: "FieldValue Imod1 (o1, a) \<in> Value Imod1"
          using a_in_field_tmod1 imod1_correct o1_in_imod1 o1_object_class_imod1
          by (simp add: class_def instance_model.property_field_values_inside_domain)
        assume o2_in_imod1: "o2 \<in> Object Imod1"
        then have o2_object_class_imod1: "ObjectClass Imod1 o2 = c"
          using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o2 structure_object_class_wellformed
          by metis
        then have "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod1 (o2, a)"
          unfolding imod_combine_field_value_def
        proof (induct "o2 \<in> Object Imod2")
          case True
          then show ?case
            using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2 o2_in_imod1
            by simp
        next
          case False
          then show ?case
            using a_in_field_tmod1 o2_in_imod1
            by simp
        qed
        then have o2_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o2, a) = FieldValue Imod1 (o2, a)"
          by (simp add: imod_combine_def)
        have o2_value: "FieldValue Imod1 (o2, a) \<in> Value Imod1"
          using a_in_field_tmod1 imod1_correct o2_in_imod1 o2_object_class_imod1
          by (simp add: class_def instance_model.property_field_values_inside_domain)
        have "FieldValue Imod1 (o1, a) \<equiv>[Imod1] FieldValue Imod1 (o2, a)"
          using imod_combine_value_equiv_imod1_rev o1_fieldvalue o1_value o2_fieldvalue o2_value value_equiv
          by metis
        then show ?thesis
          using a_in_a imod1_identity o1_in_imod1 o1_object_class_imod1 o2_in_imod1 o2_object_class_imod1
          by blast
      next
        assume o1_in_imod1: "o1 \<in> Object Imod1"
        assume o2_in_imod2: "o2 \<in> Object Imod2"
        show ?thesis
          using o1_in_imod1 o2_in_imod2
        proof (induct "o1 \<in> Object Imod2")
          case True
          then have o1_object_class_imod2: "ObjectClass Imod2 o1 = c"
            using imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o1 structure_object_class_wellformed
            by metis
          then have "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod2 (o1, a)"
            unfolding imod_combine_field_value_def class_def
            using True.hyps
          proof (induct "o1 \<in> Object Imod1")
            case True
            then show ?case
              using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2
              by simp
          next
            case False
            then show ?case
              using a_in_field_tmod2
              by simp
          qed
          then have o1_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o1, a) = FieldValue Imod2 (o1, a)"
            by (simp add: imod_combine_def)
          have o1_value: "FieldValue Imod2 (o1, a) \<in> Value Imod2"
            using a_in_field_tmod2 imod2_correct True.hyps o1_object_class_imod2
            by (simp add: class_def instance_model.property_field_values_inside_domain)
          assume o2_in_imod2: "o2 \<in> Object Imod2"
          then have o2_object_class_imod2: "ObjectClass Imod2 o2 = c"
            using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o2 structure_object_class_wellformed
            by metis
          then have "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod2 (o2, a)"
            unfolding imod_combine_field_value_def class_def
          proof (induct "o2 \<in> Object Imod1")
            case True
            then show ?case
              using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2 o2_in_imod2
              by simp
          next
            case False
            then show ?case
              using a_in_field_tmod2 o2_in_imod2
              by simp
          qed
          then have o2_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o2, a) = FieldValue Imod2 (o2, a)"
            by (simp add: imod_combine_def)
          have o2_value: "FieldValue Imod2 (o2, a) \<in> Value Imod2"
            using a_in_field_tmod2 imod2_correct o2_in_imod2 o2_object_class_imod2
            by (simp add: class_def instance_model.property_field_values_inside_domain)
          have "FieldValue Imod2 (o1, a) \<equiv>[Imod2] FieldValue Imod2 (o2, a)"
            using imod_combine_value_equiv_imod2_rev o1_fieldvalue o1_value o2_fieldvalue o2_value value_equiv
            by metis
          then show ?case
            using a_in_a imod2_identity True.hyps o1_object_class_imod2 o2_in_imod2 o2_object_class_imod2
            by blast
        next
          case False
          then show ?case
          proof (induct "o2 \<in> Object Imod1")
            case True
            assume o1_in_imod1: "o1 \<in> Object Imod1"
            then have o1_object_class_imod1: "ObjectClass Imod1 o1 = c"
              using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o1 structure_object_class_wellformed
              by metis
            then have "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod1 (o1, a)"
              unfolding imod_combine_field_value_def
            proof (induct "o1 \<in> Object Imod2")
              case True
              then show ?case
                using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2 o1_in_imod1
                by simp
            next
              case False
              then show ?case
                using a_in_field_tmod1 o1_in_imod1
                by simp
            qed
            then have o1_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o1, a) = FieldValue Imod1 (o1, a)"
              by (simp add: imod_combine_def)
            have o1_value: "FieldValue Imod1 (o1, a) \<in> Value Imod1"
              using a_in_field_tmod1 imod1_correct o1_in_imod1 o1_object_class_imod1
              by (simp add: class_def instance_model.property_field_values_inside_domain)
            have o2_object_class_imod1: "ObjectClass Imod1 o2 = c"
              using Diff_Diff_Int Diff_iff True.hyps imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o2 structure_object_class_wellformed
              by metis
            then have "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod1 (o2, a)"
              unfolding imod_combine_field_value_def
              using True.hyps
            proof (induct "o2 \<in> Object Imod2")
              case True
              then show ?case
                using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2
                by simp
            next
              case False
              then show ?case
                using a_in_field_tmod1
                by simp
            qed
            then have o2_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o2, a) = FieldValue Imod1 (o2, a)"
              by (simp add: imod_combine_def)
            have o2_value: "FieldValue Imod1 (o2, a) \<in> Value Imod1"
              using True.hyps a_in_field_tmod1 imod1_correct o2_object_class_imod1
              by (simp add: class_def instance_model.property_field_values_inside_domain)
            have "FieldValue Imod1 (o1, a) \<equiv>[Imod1] FieldValue Imod1 (o2, a)"
              using imod_combine_value_equiv_imod1_rev o1_fieldvalue o1_value o2_fieldvalue o2_value value_equiv
              by metis
            then show ?case
              using True.hyps a_in_a imod1_identity o1_in_imod1 o1_object_class_imod1 o2_object_class_imod1
              by blast
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod1 (o1, a)"
              unfolding imod_combine_field_value_def
              using False.prems a_in_field_tmod1
              by simp
            then have o1_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o1, a) = FieldValue Imod1 (o1, a)"
              by (simp add: imod_combine_def)
            have o1_object_class: "ObjectClass Imod1 o1 = c"
              using False.prems Int_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) o1_in_imod1 object_class_o1
              by metis
            have "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod2 (o2, a)"
              unfolding imod_combine_field_value_def
              using False.hyps False.prems a_in_field_tmod2
              by simp
            then have o2_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o2, a) = FieldValue Imod2 (o2, a)"
              by (simp add: imod_combine_def)
            have o2_object_class: "ObjectClass Imod2 o2 = c"
              using False.hyps Int_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) o2_in_imod2 object_class_o2
              by metis
            show ?case
              using Diff_iff False.hyps False.prems validity_identity_properties_satisfied identity_property_both.hyps 
              using o1_object_class o2_object_class o1_fieldvalue o2_fieldvalue a_in_a value_equiv
              by metis
          qed
        qed
      next
        assume o1_in_imod2: "o1 \<in> Object Imod2"
        assume o2_in_imod1: "o2 \<in> Object Imod1"
        show ?thesis
          using o1_in_imod2 o2_in_imod1
        proof (induct "o1 \<in> Object Imod1")
          case True
          then have o1_object_class_imod1: "ObjectClass Imod1 o1 = c"
            using imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o1 structure_object_class_wellformed
            by metis
          then have "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod1 (o1, a)"
            unfolding imod_combine_field_value_def
            using True.hyps
          proof (induct "o1 \<in> Object Imod2")
            case True
            then show ?case
              using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2
              by simp
          next
            case False
            then show ?case
              using a_in_field_tmod1
              by simp
          qed
          then have o1_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o1, a) = FieldValue Imod1 (o1, a)"
            by (simp add: imod_combine_def)
          have o1_value: "FieldValue Imod1 (o1, a) \<in> Value Imod1"
            using True.hyps a_in_field_tmod1 imod1_correct o1_object_class_imod1
            by (simp add: class_def instance_model.property_field_values_inside_domain)
          assume o2_in_imod1: "o2 \<in> Object Imod1"
          then have o2_object_class_imod1: "ObjectClass Imod1 o2 = c"
            using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o2 structure_object_class_wellformed
            by metis
          then have "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod1 (o2, a)"
            unfolding imod_combine_field_value_def
          proof (induct "o2 \<in> Object Imod2")
            case True
            then show ?case
              using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2 o2_in_imod1
              by simp
          next
            case False
            then show ?case
              using a_in_field_tmod1 o2_in_imod1
              by simp
          qed
          then have o2_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o2, a) = FieldValue Imod1 (o2, a)"
            by (simp add: imod_combine_def)
          have o2_value: "FieldValue Imod1 (o2, a) \<in> Value Imod1"
            using a_in_field_tmod1 imod1_correct o2_in_imod1 o2_object_class_imod1
            by (simp add: class_def instance_model.property_field_values_inside_domain)
          have "FieldValue Imod1 (o1, a) \<equiv>[Imod1] FieldValue Imod1 (o2, a)"
            using imod_combine_value_equiv_imod1_rev o1_fieldvalue o1_value o2_fieldvalue o2_value value_equiv
            by metis
          then show ?thesis
            using True.hyps a_in_a imod1_identity o1_object_class_imod1 o2_in_imod1 o2_object_class_imod1
            by blast
        next
          case False
          then show ?case
          proof (induct "o2 \<in> Object Imod2")
            case True
            assume o1_in_imod2: "o1 \<in> Object Imod2"
            then have o1_object_class_imod2: "ObjectClass Imod2 o1 = c"
              using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o1 structure_object_class_wellformed
              by metis
            then have "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod2 (o1, a)"
              unfolding imod_combine_field_value_def class_def
            proof (induct "o1 \<in> Object Imod1")
              case True
              then show ?case
                using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2 o1_in_imod2
                by simp
            next
              case False
              then show ?case
                using a_in_field_tmod2 o1_in_imod2
                by simp
            qed
            then have o1_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o1, a) = FieldValue Imod2 (o1, a)"
              by (simp add: imod_combine_def)
            have o1_value: "FieldValue Imod2 (o1, a) \<in> Value Imod2"
              using a_in_field_tmod2 imod2_correct o1_in_imod2 o1_object_class_imod2
              by (simp add: class_def instance_model.property_field_values_inside_domain)
            then have o2_object_class_imod2: "ObjectClass Imod2 o2 = c"
              using Diff_Diff_Int Diff_iff True.hyps imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o2 structure_object_class_wellformed
              by metis
            then have "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod2 (o2, a)"
              unfolding imod_combine_field_value_def class_def
              using True.hyps
            proof (induct "o2 \<in> Object Imod1")
              case True
              then show ?case
                using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2
                by simp
            next
              case False
              then show ?case
                using a_in_field_tmod2
                by simp
            qed
            then have o2_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o2, a) = FieldValue Imod2 (o2, a)"
              by (simp add: imod_combine_def)
            have o2_value: "FieldValue Imod2 (o2, a) \<in> Value Imod2"
              using True.hyps a_in_field_tmod2 imod2_correct o2_object_class_imod2
              by (simp add: class_def instance_model.property_field_values_inside_domain)
            have "FieldValue Imod2 (o1, a) \<equiv>[Imod2] FieldValue Imod2 (o2, a)"
              using imod_combine_value_equiv_imod2_rev o1_fieldvalue o1_value o2_fieldvalue o2_value value_equiv
              by metis
            then show ?thesis
              using True.hyps a_in_a imod2_identity o1_in_imod2 o1_object_class_imod2 o2_object_class_imod2
              by blast
          next
            case False
            have "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod2 (o1, a)"
              unfolding imod_combine_field_value_def
              using False.prems a_in_field_tmod2
              by simp
            then have o1_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o1, a) = FieldValue Imod2 (o1, a)"
              by (simp add: imod_combine_def)
            have o1_object_class: "ObjectClass Imod2 o1 = c"
              using False.prems Int_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) o1_in_imod2 object_class_o1
              by metis
            have "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod1 (o2, a)"
              unfolding imod_combine_field_value_def
              using False.hyps False.prems a_in_field_tmod1
              by simp
            then have o2_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o2, a) = FieldValue Imod1 (o2, a)"
              by (simp add: imod_combine_def)
            have o2_object_class: "ObjectClass Imod1 o2 = c"
              using False.hyps Int_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) o2_in_imod1 object_class_o2
              by metis
            show ?case
              using Diff_iff False.hyps False.prems validity_identity_properties_satisfied identity_property_both.hyps 
              using o1_object_class o2_object_class o1_fieldvalue o2_fieldvalue a_in_a value_equiv value_equiv_sym
              by metis
          qed
        qed
      next
        assume o1_in_imod2: "o1 \<in> Object Imod2"
        then have o1_object_class_imod2: "ObjectClass Imod2 o1 = c"
          using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o1 structure_object_class_wellformed
          by metis
        then have "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod2 (o1, a)"
          unfolding imod_combine_field_value_def class_def
        proof (induct "o1 \<in> Object Imod1")
          case True
          then show ?case
            using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2 o1_in_imod2
            by simp
        next
          case False
          then show ?case
            using a_in_field_tmod2 o1_in_imod2
            by simp
        qed
        then have o1_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o1, a) = FieldValue Imod2 (o1, a)"
          by (simp add: imod_combine_def)
        have o1_value: "FieldValue Imod2 (o1, a) \<in> Value Imod2"
          using a_in_field_tmod2 imod2_correct o1_in_imod2 o1_object_class_imod2
          by (simp add: class_def instance_model.property_field_values_inside_domain)
        assume o2_in_imod2: "o2 \<in> Object Imod2"
        then have o2_object_class_imod2: "ObjectClass Imod2 o2 = c"
          using Diff_Diff_Int Diff_iff imod_combine_def imod_combine_object_class_def instance_model.select_convs(3) object_class_o2 structure_object_class_wellformed
          by metis
        then have "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod2 (o2, a)"
          unfolding imod_combine_field_value_def class_def
        proof (induct "o2 \<in> Object Imod1")
          case True
          then show ?case
            using structure_object_class_wellformed property_field_values_wellformed a_in_field_tmod1 a_in_field_tmod2 o2_in_imod2
            by simp
        next
          case False
          then show ?case
            using a_in_field_tmod2 o2_in_imod2
            by simp
        qed
        then have o2_fieldvalue: "FieldValue (imod_combine Imod1 Imod2) (o2, a) = FieldValue Imod2 (o2, a)"
          by (simp add: imod_combine_def)
        have o2_value: "FieldValue Imod2 (o2, a) \<in> Value Imod2"
          using a_in_field_tmod2 imod2_correct o2_in_imod2 o2_object_class_imod2
          by (simp add: class_def instance_model.property_field_values_inside_domain)
        have "FieldValue Imod2 (o1, a) \<equiv>[Imod2] FieldValue Imod2 (o2, a)"
          using imod_combine_value_equiv_imod2_rev o1_fieldvalue o1_value o2_fieldvalue o2_value value_equiv
          by metis
        then show ?thesis
          using a_in_a imod2_identity o1_in_imod2 o1_object_class_imod2 o2_in_imod2 o2_object_class_imod2
          by blast
      qed
    qed
  next
    case (keyset_property_tmod1 r A)
    then have "Imod1 \<Turnstile> keyset r A"
      using imod1_correct instance_model.validity_properties_satisfied
      by blast
    then have imod1_keyset: "\<And>o1 o2 p a. o1 \<in> Object Imod1 \<Longrightarrow> o2 \<in> Object Imod1 \<Longrightarrow> p \<in> Object Imod1 \<Longrightarrow> 
      r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 p) \<Longrightarrow> edge Imod1 p r o1 \<Longrightarrow> edge Imod1 p r o2 \<Longrightarrow> 
      a \<in> A \<Longrightarrow> FieldValue Imod1 (o1, a) \<equiv>[Imod1] FieldValue Imod1 (o2, a) \<Longrightarrow> o1 = o2"
      using property_satisfaction_keyset_rev
      by metis
    have "keyset r A \<in> Property (Tm Imod1)"
      by (simp add: imod1_correct instance_model.validity_type_model_consistent keyset_property_tmod1.hyps(1) type_model.structure_properties_wellfomed)
    then have keyset_props: "r \<in> Rel (Tm Imod1) \<and> A \<subseteq> Attr (Tm Imod1) \<and> 
      (\<forall>f. f \<in> A \<longrightarrow> (uncontainer (type (Tm Imod1) r) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f))) \<and>
      type (Tm Imod1) r \<in> UniqueContainerOfClassType (Tm Imod1)"
      using properties_rev_impl_keyset
      by blast
    then have r_type: "fst (FieldSig (Tm Imod1) r) \<in> UniqueContainerOfClassType (Tm Imod1)"
      unfolding type_def
      by simp
    then have contained_type_r: "contained_type (fst (FieldSig (Tm Imod1) r)) \<in> ClassType (Tm Imod1)"
    proof (cases)
      case (rule_setof_class_type t)
      then show ?thesis
        by simp
    next
      case (rule_ordof_class_type t)
      then show ?thesis
        by simp
    qed
    have contained_type_is_uncontainer_r: "contained_type (fst (FieldSig (Tm Imod1) r)) = uncontainer (fst (FieldSig (Tm Imod1) r))"
      using r_type
    proof (cases)
      case (rule_setof_class_type t)
      then have "uncontainer t = t"
        unfolding ClassType_def
        using local.rule_setof_class_type(2) non_container_type_subset_class_type non_container_type_uncontainer_identity
        by blast
      then show ?thesis
        by (simp add: local.rule_setof_class_type(1))
    next
      case (rule_ordof_class_type t)
      then have "uncontainer t = t"
        unfolding ClassType_def
        using local.rule_ordof_class_type(2) non_container_type_subset_class_type non_container_type_uncontainer_identity
        by blast
      then show ?thesis
        by (simp add: local.rule_ordof_class_type(1))
    qed
    have r1_in_field: "r \<in> Field (Tm Imod1)"
      using keyset_props
      unfolding Rel_def
      by blast
    then have r_in_combination: "r \<in> Field (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def tmod_combine_def)
    show ?case
    proof (intro property_satisfaction.rule_property_keyset)
      fix o1 o2 p a
      assume o1_present: "o1 \<in> Object (imod_combine Imod1 Imod2)"
      then have o1_in_object: "o1 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      assume o2_present: "o2 \<in> Object (imod_combine Imod1 Imod2)"
      then have o2_in_object: "o2 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      assume p_present: "p \<in> Object (imod_combine Imod1 Imod2)"
      then have p_in_object: "p \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have p_in_object_cases: "p \<in> Object Imod1 \<or> p \<in> Object Imod2 - Object Imod1"
        by blast
      assume r_field_of_p: "r \<in> Type_Model.fields (Tm (imod_combine Imod1 Imod2)) (ObjectClass (imod_combine Imod1 Imod2) p)"
      then have subtype_r: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) p) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm Imod1) r)"
        unfolding Type_Model.fields_def class_def
        by fastforce
      assume o1_in_r: "edge (imod_combine Imod1 Imod2) p r o1"
      assume o2_in_r: "edge (imod_combine Imod1 Imod2) p r o2"
      assume a_in_attributes: "a \<in> A"
      then have a_type: "uncontainer (type (Tm Imod1) r) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)"
        using keyset_props
        by blast
      have a_field_imod1: "a \<in> Field (Tm Imod1)"
        using a_in_attributes keyset_props
        unfolding Attr_def
        by blast
      assume value_equiv: "FieldValue (imod_combine Imod1 Imod2) (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue (imod_combine Imod1 Imod2) (o2, a)"
      show "o1 = o2"
        using p_in_object_cases
      proof (elim disjE)
        assume p_in_imod1: "p \<in> Object Imod1"
        have "imod_combine_field_value Imod1 Imod2 (p, r) = FieldValue Imod1 (p, r)"
          unfolding imod_combine_field_value_def
          by (simp add: keyset_property_tmod1.hyps(2) p_in_imod1 r1_in_field)
        then have "FieldValue (imod_combine Imod1 Imod2) (p, r) = FieldValue Imod1 (p, r)"
          by (simp add: imod_combine_def)
        then show ?thesis
        proof (induct "\<exclamdown>(ObjectClass Imod1 p) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r)")
          case True
          then have r_field_of_p_imod1: "r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 p)"
            unfolding Type_Model.fields_def class_def
            using r1_in_field
            by fastforce
          have o1_in_r_imod1: "edge Imod1 p r o1"
            using True.hyps True.prems o1_in_r p_present r_in_combination subtype_r p_in_imod1 r1_in_field r_field_of_p
            unfolding edge_def edgeCount_def
            by simp
          then have o1_in_imod1: "o1 \<in> Object Imod1"
            using edge_def imod1_correct le_numeral_extra(2) edge_count_non_existant_object p_in_imod1 r_field_of_p_imod1
            by metis
          have "FieldValue Imod1 (p, r) :[Imod1] type (Tm Imod1) r"
            using True.hyps p_in_imod1 r1_in_field imod1_correct instance_model.validity_values_typed
            by metis
          then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] contained_type (fst (FieldSig (Tm Imod1) r))"
            unfolding Valid_def type_def
          proof (cases)
            case valid_rule_booleans
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_integers
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_reals
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_strings
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case (valid_rule_proper_classes v)
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_class_type_intersect
              by blast
          next
            case valid_rule_nullable_classes
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_nullable_class_type_intersect
              by blast
          next
            case (valid_rule_enumvalues t v)
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_enum_type_intersect
              by fastforce
          next
            case valid_rule_userdata_values
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_userdatatype_type_intersect
              by blast
          next
            case valid_rule_bags
            then show ?thesis
              using r_type unique_container_of_class_types_are_unique_containers bag_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_sets
            then have "(contained_type (fst (FieldSig (Tm Imod1) r)), obj o1) \<in> Valid_rel Imod1"
              using o1_in_r_imod1
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r)
          next
            case valid_rule_seqs
            then show ?thesis
              using r_type unique_container_of_class_types_are_unique_containers seq_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_ords
            then have "(contained_type (fst (FieldSig (Tm Imod1) r)), obj o1) \<in> Valid_rel Imod1"
              using o1_in_r_imod1
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r)
          qed
          then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] uncontainer (type (Tm Imod1) r)"
            unfolding type_def
            by (simp add: contained_type_is_uncontainer_r)
          then have o1_subtype_a: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)"
            using a_type imod1_correct instance_model.validity_type_model_consistent subtype_relation_transitive_alt
            unfolding subtype_def trans_def
            by blast
          then have "FieldValue Imod1 (o1, a) \<noteq> unspecified"
            using o1_in_imod1 a_field_imod1 imod1_correct instance_model.property_field_values_inside_domain
            by fastforce
          then have fieldvalue_o1: "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod1 (o1, a)"
            unfolding imod_combine_field_value_def
            using o1_in_imod1 a_field_imod1
          proof (induct "o1 \<in> Object Imod2 \<and> a \<in> Field (Tm Imod2)")
            case True
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)")
              case True
              then show ?case
                using o1_subtype_a property_field_values_wellformed
                by simp
            next
              case False
              then have "FieldValue Imod2 (o1, a) = unspecified"
                using imod2_correct instance_model.property_field_values_outside_domain
                by metis
              then show ?case
                using False.hyps False.prems
                by simp
            qed
          next
            case False
            then show ?case
              by auto
          qed
          have o2_in_r_imod1: "edge Imod1 p r o2"
            using True.hyps True.prems o2_in_r p_present r_in_combination subtype_r p_in_imod1 r1_in_field r_field_of_p
            unfolding edge_def edgeCount_def
            by simp
          then have o2_in_imod1: "o2 \<in> Object Imod1"
            using edge_def imod1_correct le_numeral_extra(2) edge_count_non_existant_object p_in_imod1 r_field_of_p_imod1
            by metis
          have "FieldValue Imod1 (p, r) :[Imod1] type (Tm Imod1) r"
            using True.hyps p_in_imod1 r1_in_field imod1_correct instance_model.validity_values_typed
            by metis
          then have "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] contained_type (fst (FieldSig (Tm Imod1) r))"
            unfolding Valid_def type_def
          proof (cases)
            case valid_rule_booleans
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_integers
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_reals
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_strings
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case (valid_rule_proper_classes v)
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_class_type_intersect
              by blast
          next
            case valid_rule_nullable_classes
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_nullable_class_type_intersect
              by blast
          next
            case (valid_rule_enumvalues t v)
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_enum_type_intersect
              by fastforce
          next
            case valid_rule_userdata_values
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_userdatatype_type_intersect
              by blast
          next
            case valid_rule_bags
            then show ?thesis
              using r_type unique_container_of_class_types_are_unique_containers bag_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_sets
            then have "(contained_type (fst (FieldSig (Tm Imod1) r)), obj o2) \<in> Valid_rel Imod1"
              using o2_in_r_imod1
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r)
          next
            case valid_rule_seqs
            then show ?thesis
              using r_type unique_container_of_class_types_are_unique_containers seq_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_ords
            then have "(contained_type (fst (FieldSig (Tm Imod1) r)), obj o2) \<in> Valid_rel Imod1"
              using o2_in_r_imod1
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r)
          qed
          then have "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] uncontainer (type (Tm Imod1) r)"
            unfolding type_def
            by (simp add: contained_type_is_uncontainer_r)
          then have o2_subtype_a: "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)"
            using a_type imod1_correct instance_model.validity_type_model_consistent subtype_relation_transitive_alt
            unfolding subtype_def trans_def
            by blast
          then have "FieldValue Imod1 (o2, a) \<noteq> unspecified"
            using o2_in_imod1 a_field_imod1 imod1_correct instance_model.property_field_values_inside_domain
            by fastforce
          then have fieldvalue_o2: "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod1 (o2, a)"
            unfolding imod_combine_field_value_def
            using o2_in_imod1 a_field_imod1
          proof (induct "o2 \<in> Object Imod2 \<and> a \<in> Field (Tm Imod2)")
            case True
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)")
              case True
              then show ?case
                using o2_subtype_a property_field_values_wellformed
                by simp
            next
              case False
              then have "FieldValue Imod2 (o2, a) = unspecified"
                using imod2_correct instance_model.property_field_values_outside_domain
                by metis
              then show ?case
                using False.hyps False.prems
                by simp
            qed
          next
            case False
            then show ?case
              by auto
          qed
          have "FieldValue Imod1 (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue Imod1 (o2, a)"
            using value_equiv fieldvalue_o1 fieldvalue_o2
            by (simp add: imod_combine_def)
          then have "FieldValue Imod1 (o1, a) \<equiv>[Imod1] FieldValue Imod1 (o2, a)"
            using a_field_imod1 imod1_correct imod_combine_value_equiv_imod1_rev instance_model.property_field_values_inside_domain o1_in_imod1 o1_subtype_a o2_in_imod1 o2_subtype_a
            by metis
          then show ?case
            using a_in_attributes imod1_keyset o1_in_imod1 o1_in_r_imod1 o2_in_imod1 o2_in_r_imod1 p_in_imod1 r_field_of_p_imod1
            by blast
        next
          case False
          then show ?case
            using fields_of_class_subtype_field_class keyset_property_tmod1.hyps(2) p_in_imod1 property_field_values_not_subtype_imod1 r1_in_field r_field_of_p
            by blast
        qed
      next
        assume p_in_imod2: "p \<in> Object Imod2 - Object Imod1"
        then have "p \<in> Object Imod1"
          using Diff_iff class_def keyset_property_tmod1.hyps(2) property_field_values_not_field_imod2 r1_in_field subtype_r
          by metis
        then show ?thesis
          using p_in_imod2
          by blast
      qed
    qed
  next
    case (keyset_property_tmod2 r A)
    then have "Imod2 \<Turnstile> keyset r A"
      using imod2_correct instance_model.validity_properties_satisfied
      by blast
    then have imod2_keyset: "\<And>o1 o2 p a. o1 \<in> Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 \<Longrightarrow> p \<in> Object Imod2 \<Longrightarrow> 
      r \<in> Type_Model.fields (Tm Imod2) (ObjectClass Imod2 p) \<Longrightarrow> edge Imod2 p r o1 \<Longrightarrow> edge Imod2 p r o2 \<Longrightarrow> 
      a \<in> A \<Longrightarrow> FieldValue Imod2 (o1, a) \<equiv>[Imod2] FieldValue Imod2 (o2, a) \<Longrightarrow> o1 = o2"
      using property_satisfaction_keyset_rev
      by metis
    have "keyset r A \<in> Property (Tm Imod2)"
      by (simp add: imod2_correct instance_model.validity_type_model_consistent keyset_property_tmod2.hyps(1) type_model.structure_properties_wellfomed)
    then have keyset_props: "r \<in> Rel (Tm Imod2) \<and> A \<subseteq> Attr (Tm Imod2) \<and> 
      (\<forall>f. f \<in> A \<longrightarrow> (uncontainer (type (Tm Imod2) r) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f))) \<and>
      type (Tm Imod2) r \<in> UniqueContainerOfClassType (Tm Imod2)"
      using properties_rev_impl_keyset
      by blast
    then have r_type: "fst (FieldSig (Tm Imod2) r) \<in> UniqueContainerOfClassType (Tm Imod2)"
      unfolding type_def
      by simp
    then have contained_type_r: "contained_type (fst (FieldSig (Tm Imod2) r)) \<in> ClassType (Tm Imod2)"
    proof (cases)
      case (rule_setof_class_type t)
      then show ?thesis
        by simp
    next
      case (rule_ordof_class_type t)
      then show ?thesis
        by simp
    qed
    have contained_type_is_uncontainer_r: "contained_type (fst (FieldSig (Tm Imod2) r)) = uncontainer (fst (FieldSig (Tm Imod2) r))"
      using r_type
    proof (cases)
      case (rule_setof_class_type t)
      then have "uncontainer t = t"
        unfolding ClassType_def
        using local.rule_setof_class_type(2) non_container_type_subset_class_type non_container_type_uncontainer_identity
        by blast
      then show ?thesis
        by (simp add: local.rule_setof_class_type(1))
    next
      case (rule_ordof_class_type t)
      then have "uncontainer t = t"
        unfolding ClassType_def
        using local.rule_ordof_class_type(2) non_container_type_subset_class_type non_container_type_uncontainer_identity
        by blast
      then show ?thesis
        by (simp add: local.rule_ordof_class_type(1))
    qed
    have r1_in_field: "r \<in> Field (Tm Imod2)"
      using keyset_props
      unfolding Rel_def
      by blast
    then have r_in_combination: "r \<in> Field (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def tmod_combine_def)
    show ?case
    proof (intro property_satisfaction.rule_property_keyset)
      fix o1 o2 p a
      assume o1_present: "o1 \<in> Object (imod_combine Imod1 Imod2)"
      then have o1_in_object: "o1 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      assume o2_present: "o2 \<in> Object (imod_combine Imod1 Imod2)"
      then have o2_in_object: "o2 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      assume p_present: "p \<in> Object (imod_combine Imod1 Imod2)"
      then have p_in_object: "p \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have p_in_object_cases: "p \<in> Object Imod2 \<or> p \<in> Object Imod1 - Object Imod2"
        by blast
      assume r_field_of_p: "r \<in> Type_Model.fields (Tm (imod_combine Imod1 Imod2)) (ObjectClass (imod_combine Imod1 Imod2) p)"
      then have subtype_r: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) p) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm Imod1) r)"
        unfolding Type_Model.fields_def class_def
        by fastforce
      assume o1_in_r: "edge (imod_combine Imod1 Imod2) p r o1"
      assume o2_in_r: "edge (imod_combine Imod1 Imod2) p r o2"
      assume a_in_attributes: "a \<in> A"
      then have a_type: "uncontainer (type (Tm Imod2) r) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)"
        using keyset_props
        by blast
      have a_field_imod2: "a \<in> Field (Tm Imod2)"
        using a_in_attributes keyset_props
        unfolding Attr_def
        by blast
      assume value_equiv: "FieldValue (imod_combine Imod1 Imod2) (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue (imod_combine Imod1 Imod2) (o2, a)"
      show "o1 = o2"
        using p_in_object_cases
      proof (elim disjE)
        assume p_in_imod2: "p \<in> Object Imod2"
        have "imod_combine_field_value Imod1 Imod2 (p, r) = FieldValue Imod2 (p, r)"
          unfolding imod_combine_field_value_def
          by (simp add: keyset_property_tmod2.hyps(2) p_in_imod2 r1_in_field)
        then have "FieldValue (imod_combine Imod1 Imod2) (p, r) = FieldValue Imod2 (p, r)"
          by (simp add: imod_combine_def)
        then show ?thesis
        proof (induct "\<exclamdown>(ObjectClass Imod2 p) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r)")
          case True
          then have r_field_of_p_imod2: "r \<in> Type_Model.fields (Tm Imod2) (ObjectClass Imod2 p)"
            unfolding Type_Model.fields_def class_def
            using r1_in_field
            by fastforce
          have o1_in_r_imod2: "edge Imod2 p r o1"
            using True.hyps True.prems o1_in_r p_present r_in_combination subtype_r p_in_imod2 r1_in_field r_field_of_p
            unfolding edge_def edgeCount_def
            by simp
          then have o1_in_imod2: "o1 \<in> Object Imod2"
            using edge_def imod2_correct le_numeral_extra(2) edge_count_non_existant_object p_in_imod2 r_field_of_p_imod2
            by metis
          have "FieldValue Imod2 (p, r) :[Imod2] type (Tm Imod2) r"
            using True.hyps p_in_imod2 r1_in_field imod2_correct instance_model.validity_values_typed
            by metis
          then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] contained_type (fst (FieldSig (Tm Imod2) r))"
            unfolding Valid_def type_def
          proof (cases)
            case valid_rule_booleans
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_integers
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_reals
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_strings
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case (valid_rule_proper_classes v)
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_class_type_intersect
              by blast
          next
            case valid_rule_nullable_classes
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_nullable_class_type_intersect
              by blast
          next
            case (valid_rule_enumvalues t v)
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_enum_type_intersect
              by fastforce
          next
            case valid_rule_userdata_values
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_userdatatype_type_intersect
              by blast
          next
            case valid_rule_bags
            then show ?thesis
              using r_type unique_container_of_class_types_are_unique_containers bag_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_sets
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o1) \<in> Valid_rel Imod2"
              using o1_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r)
          next
            case valid_rule_seqs
            then show ?thesis
              using r_type unique_container_of_class_types_are_unique_containers seq_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_ords
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o1) \<in> Valid_rel Imod2"
              using o1_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r)
          qed
          then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] uncontainer (type (Tm Imod2) r)"
            unfolding type_def
            by (simp add: contained_type_is_uncontainer_r)
          then have o1_subtype_a: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)"
            using a_type imod2_correct instance_model.validity_type_model_consistent subtype_relation_transitive_alt
            unfolding subtype_def trans_def
            by blast
          then have "FieldValue Imod2 (o1, a) \<noteq> unspecified"
            using o1_in_imod2 a_field_imod2 imod2_correct instance_model.property_field_values_inside_domain
            by fastforce
          then have fieldvalue_o1: "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod2 (o1, a)"
            unfolding imod_combine_field_value_def
            using o1_in_imod2 a_field_imod2
          proof (induct "o1 \<in> Object Imod1 \<and> a \<in> Field (Tm Imod1)")
            case True
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)")
              case True
              then show ?case
                using o1_subtype_a property_field_values_wellformed
                by simp
            next
              case False
              then have "FieldValue Imod1 (o1, a) = unspecified"
                using imod1_correct instance_model.property_field_values_outside_domain
                by metis
              then show ?case
                using False.hyps False.prems
                by simp
            qed
          next
            case False
            then show ?case
              by auto
          qed
          have o2_in_r_imod2: "edge Imod2 p r o2"
            using True.hyps True.prems o2_in_r p_present r_in_combination subtype_r p_in_imod2 r1_in_field r_field_of_p
            unfolding edge_def edgeCount_def
            by simp
          then have o2_in_imod2: "o2 \<in> Object Imod2"
            using edge_def imod2_correct le_numeral_extra(2) edge_count_non_existant_object p_in_imod2 r_field_of_p_imod2
            by metis
          have "FieldValue Imod2 (p, r) :[Imod2] type (Tm Imod2) r"
            using True.hyps p_in_imod2 r1_in_field imod2_correct instance_model.validity_values_typed
            by metis
          then have "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] contained_type (fst (FieldSig (Tm Imod2) r))"
            unfolding Valid_def type_def
          proof (cases)
            case valid_rule_booleans
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_integers
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_reals
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_strings
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types
              by fastforce
          next
            case (valid_rule_proper_classes v)
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_class_type_intersect
              by blast
          next
            case valid_rule_nullable_classes
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_nullable_class_type_intersect
              by blast
          next
            case (valid_rule_enumvalues t v)
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_enum_type_intersect
              by fastforce
          next
            case valid_rule_userdata_values
            then show ?thesis
              using r_type unique_container_of_class_types_are_container_types container_type_userdatatype_type_intersect
              by blast
          next
            case valid_rule_bags
            then show ?thesis
              using r_type unique_container_of_class_types_are_unique_containers bag_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_sets
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o2) \<in> Valid_rel Imod2"
              using o2_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r)
          next
            case valid_rule_seqs
            then show ?thesis
              using r_type unique_container_of_class_types_are_unique_containers seq_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_ords
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o2) \<in> Valid_rel Imod2"
              using o2_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r)
          qed
          then have "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] uncontainer (type (Tm Imod2) r)"
            unfolding type_def
            by (simp add: contained_type_is_uncontainer_r)
          then have o2_subtype_a: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)"
            using a_type imod2_correct instance_model.validity_type_model_consistent subtype_relation_transitive_alt
            unfolding subtype_def trans_def
            by blast
          then have "FieldValue Imod2 (o2, a) \<noteq> unspecified"
            using o2_in_imod2 a_field_imod2 imod2_correct instance_model.property_field_values_inside_domain
            by fastforce
          then have fieldvalue_o2: "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod2 (o2, a)"
            unfolding imod_combine_field_value_def
            using o2_in_imod2 a_field_imod2
          proof (induct "o2 \<in> Object Imod1 \<and> a \<in> Field (Tm Imod1)")
            case True
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)")
              case True
              then show ?case
                using o2_subtype_a property_field_values_wellformed
                by simp
            next
              case False
              then have "FieldValue Imod1 (o2, a) = unspecified"
                using imod1_correct instance_model.property_field_values_outside_domain
                by metis
              then show ?case
                using False.hyps False.prems
                by simp
            qed
          next
            case False
            then show ?case
              by auto
          qed
          have "FieldValue Imod2 (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue Imod2 (o2, a)"
            using value_equiv fieldvalue_o1 fieldvalue_o2
            by (simp add: imod_combine_def)
          then have "FieldValue Imod2 (o1, a) \<equiv>[Imod2] FieldValue Imod2 (o2, a)"
            using a_field_imod2 imod2_correct imod_combine_value_equiv_imod2_rev instance_model.property_field_values_inside_domain o1_in_imod2 o1_subtype_a o2_in_imod2 o2_subtype_a
            by metis
          then show ?case
            using a_in_attributes imod2_keyset o1_in_imod2 o1_in_r_imod2 o2_in_imod2 o2_in_r_imod2 p_in_imod2 r_field_of_p_imod2
            by blast
        next
          case False
          then show ?case
            using fields_of_class_subtype_field_class keyset_property_tmod2.hyps(2) p_in_imod2 property_field_values_not_subtype_imod2 r1_in_field r_field_of_p
            by blast
        qed
      next
        assume p_in_imod2: "p \<in> Object Imod1 - Object Imod2"
        then have "p \<in> Object Imod2"
          using Diff_iff class_def keyset_property_tmod2.hyps(2) property_field_values_not_field_imod1 r1_in_field subtype_r
          by metis
        then show ?thesis
          using p_in_imod2
          by blast
      qed
    qed
  next
    case (keyset_property_both r A)
    have "Imod1 \<Turnstile> keyset r A"
      using local.keyset_property_both(1) imod1_correct instance_model.validity_properties_satisfied
      by blast
    then have imod1_keyset: "\<And>o1 o2 p a. o1 \<in> Object Imod1 \<Longrightarrow> o2 \<in> Object Imod1 \<Longrightarrow> p \<in> Object Imod1 \<Longrightarrow> 
      r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 p) \<Longrightarrow> edge Imod1 p r o1 \<Longrightarrow> edge Imod1 p r o2 \<Longrightarrow> 
      a \<in> A \<Longrightarrow> FieldValue Imod1 (o1, a) \<equiv>[Imod1] FieldValue Imod1 (o2, a) \<Longrightarrow> o1 = o2"
      using property_satisfaction_keyset_rev
      by metis
    have "Imod2 \<Turnstile> keyset r A"
      using local.keyset_property_both(2) imod2_correct instance_model.validity_properties_satisfied
      by blast
    then have imod2_keyset: "\<And>o1 o2 p a. o1 \<in> Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 \<Longrightarrow> p \<in> Object Imod2 \<Longrightarrow> 
      r \<in> Type_Model.fields (Tm Imod2) (ObjectClass Imod2 p) \<Longrightarrow> edge Imod2 p r o1 \<Longrightarrow> edge Imod2 p r o2 \<Longrightarrow> 
      a \<in> A \<Longrightarrow> FieldValue Imod2 (o1, a) \<equiv>[Imod2] FieldValue Imod2 (o2, a) \<Longrightarrow> o1 = o2"
      using property_satisfaction_keyset_rev
      by metis
    have "keyset r A \<in> Property (Tm Imod1)"
      by (simp add: imod1_correct instance_model.validity_type_model_consistent keyset_property_both.hyps(1) type_model.structure_properties_wellfomed)
    then have keyset_props_imod1: "r \<in> Rel (Tm Imod1) \<and> A \<subseteq> Attr (Tm Imod1) \<and> 
      (\<forall>f. f \<in> A \<longrightarrow> (uncontainer (type (Tm Imod1) r) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f))) \<and>
      type (Tm Imod1) r \<in> UniqueContainerOfClassType (Tm Imod1)"
      using properties_rev_impl_keyset
      by blast
    then have r_type_imod1: "fst (FieldSig (Tm Imod1) r) \<in> UniqueContainerOfClassType (Tm Imod1)"
      unfolding type_def
      by simp
    then have contained_type_r_imod1: "contained_type (fst (FieldSig (Tm Imod1) r)) \<in> ClassType (Tm Imod1)"
    proof (cases)
      case (rule_setof_class_type t)
      then show ?thesis
        by simp
    next
      case (rule_ordof_class_type t)
      then show ?thesis
        by simp
    qed
    have contained_type_is_uncontainer_r_imod1: "contained_type (fst (FieldSig (Tm Imod1) r)) = uncontainer (fst (FieldSig (Tm Imod1) r))"
      using r_type_imod1
    proof (cases)
      case (rule_setof_class_type t)
      then have "uncontainer t = t"
        unfolding ClassType_def
        using local.rule_setof_class_type(2) non_container_type_subset_class_type non_container_type_uncontainer_identity
        by blast
      then show ?thesis
        by (simp add: local.rule_setof_class_type(1))
    next
      case (rule_ordof_class_type t)
      then have "uncontainer t = t"
        unfolding ClassType_def
        using local.rule_ordof_class_type(2) non_container_type_subset_class_type non_container_type_uncontainer_identity
        by blast
      then show ?thesis
        by (simp add: local.rule_ordof_class_type(1))
    qed
    have r1_in_field_imod1: "r \<in> Field (Tm Imod1)"
      using keyset_props_imod1
      unfolding Rel_def
      by blast
    have "keyset r A \<in> Property (Tm Imod2)"
      by (simp add: imod2_correct instance_model.validity_type_model_consistent keyset_property_both.hyps(2) type_model.structure_properties_wellfomed)
    then have keyset_props_imod2: "r \<in> Rel (Tm Imod2) \<and> A \<subseteq> Attr (Tm Imod2) \<and> 
      (\<forall>f. f \<in> A \<longrightarrow> (uncontainer (type (Tm Imod2) r) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f))) \<and>
      type (Tm Imod2) r \<in> UniqueContainerOfClassType (Tm Imod2)"
      using properties_rev_impl_keyset
      by blast
    then have r_type_imod2: "fst (FieldSig (Tm Imod2) r) \<in> UniqueContainerOfClassType (Tm Imod2)"
      unfolding type_def
      by simp
    then have contained_type_r_imod2: "contained_type (fst (FieldSig (Tm Imod2) r)) \<in> ClassType (Tm Imod2)"
    proof (cases)
      case (rule_setof_class_type t)
      then show ?thesis
        by simp
    next
      case (rule_ordof_class_type t)
      then show ?thesis
        by simp
    qed
    have contained_type_is_uncontainer_r_imod2: "contained_type (fst (FieldSig (Tm Imod2) r)) = uncontainer (fst (FieldSig (Tm Imod2) r))"
      using r_type_imod2
    proof (cases)
      case (rule_setof_class_type t)
      then have "uncontainer t = t"
        unfolding ClassType_def
        using local.rule_setof_class_type(2) non_container_type_subset_class_type non_container_type_uncontainer_identity
        by blast
      then show ?thesis
        by (simp add: local.rule_setof_class_type(1))
    next
      case (rule_ordof_class_type t)
      then have "uncontainer t = t"
        unfolding ClassType_def
        using local.rule_ordof_class_type(2) non_container_type_subset_class_type non_container_type_uncontainer_identity
        by blast
      then show ?thesis
        by (simp add: local.rule_ordof_class_type(1))
    qed
    have r1_in_field_imod2: "r \<in> Field (Tm Imod2)"
      using keyset_props_imod2
      unfolding Rel_def
      by blast
    then have r_in_combination: "r \<in> Field (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def tmod_combine_def)
    show ?case
    proof (intro property_satisfaction.rule_property_keyset)
      fix o1 o2 p a
      assume o1_present: "o1 \<in> Object (imod_combine Imod1 Imod2)"
      then have o1_in_object: "o1 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      assume o2_present: "o2 \<in> Object (imod_combine Imod1 Imod2)"
      then have o2_in_object: "o2 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      assume p_present: "p \<in> Object (imod_combine Imod1 Imod2)"
      then have p_in_object: "p \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have p_in_object_cases: "p \<in> Object Imod1 \<or> p \<in> Object Imod2 - Object Imod1"
        by blast
      assume r_field_of_p: "r \<in> Type_Model.fields (Tm (imod_combine Imod1 Imod2)) (ObjectClass (imod_combine Imod1 Imod2) p)"
      then have subtype_r: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) p) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm Imod1) r)"
        unfolding Type_Model.fields_def class_def
        by fastforce
      assume o1_in_r: "edge (imod_combine Imod1 Imod2) p r o1"
      assume o2_in_r: "edge (imod_combine Imod1 Imod2) p r o2"
      assume a_in_attributes: "a \<in> A"
      have a_type_imod1: "uncontainer (type (Tm Imod1) r) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)"
        using a_in_attributes keyset_props_imod1
        by blast
      have a_field_imod1: "a \<in> Field (Tm Imod1)"
        using a_in_attributes keyset_props_imod1
        unfolding Attr_def
        by blast
      have a_type_imod2: "uncontainer (type (Tm Imod2) r) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)"
        using a_in_attributes keyset_props_imod2
        by blast
      have a_field_imod2: "a \<in> Field (Tm Imod2)"
        using a_in_attributes keyset_props_imod2
        unfolding Attr_def
        by blast
      assume value_equiv: "FieldValue (imod_combine Imod1 Imod2) (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue (imod_combine Imod1 Imod2) (o2, a)"
      show "o1 = o2"
        using p_in_object_cases
      proof (elim disjE)
        assume p_in_imod1: "p \<in> Object Imod1"
        then show ?thesis
        proof (induct "\<exclamdown>(ObjectClass Imod1 p) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r)")
          case True
          then have "imod_combine_field_value Imod1 Imod2 (p, r) = FieldValue Imod1 (p, r)"
            unfolding imod_combine_field_value_def
          proof (induct "p \<in> Object Imod2")
            case True
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass Imod2 p) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r)")
              case True
              then show ?case
                using property_field_values_wellformed r1_in_field_imod1 r1_in_field_imod2
                by simp
            next
              case False
              then have "FieldValue Imod2 (p, r) = unspecified"
                using r1_in_field_imod2 imod2_correct instance_model.property_field_values_outside_domain
                by metis
              then show ?case
                using False.hyps False.prems r1_in_field_imod1 r1_in_field_imod2
                by simp
            qed
          next
            case False
            then show ?case
              using r1_in_field_imod1
              by auto
          qed
          then have fieldvalue_p: "FieldValue (imod_combine Imod1 Imod2) (p, r) = FieldValue Imod1 (p, r)"
            by (simp add: imod_combine_def)
          then have r_field_of_p_imod1: "r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 p)"
            using r1_in_field_imod1 True.hyps
            unfolding Type_Model.fields_def class_def
            by fastforce
          have o1_in_r_imod1: "edge Imod1 p r o1"
            using True.hyps fieldvalue_p o1_in_r p_present r_in_combination subtype_r p_in_imod1 r1_in_field_imod1 r_field_of_p
            unfolding edge_def edgeCount_def
            by simp
          then have o1_in_imod1: "o1 \<in> Object Imod1"
            using edge_def imod1_correct le_numeral_extra(2) edge_count_non_existant_object p_in_imod1 r_field_of_p_imod1
            by metis
          have "FieldValue Imod1 (p, r) :[Imod1] type (Tm Imod1) r"
            using True.hyps p_in_imod1 r1_in_field_imod1 imod1_correct instance_model.validity_values_typed
            by metis
          then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] contained_type (fst (FieldSig (Tm Imod1) r))"
            unfolding Valid_def type_def
          proof (cases)
            case valid_rule_booleans
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_integers
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_reals
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_strings
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case (valid_rule_proper_classes v)
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types container_type_class_type_intersect
              by blast
          next
            case valid_rule_nullable_classes
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types container_type_nullable_class_type_intersect
              by blast
          next
            case (valid_rule_enumvalues t v)
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types container_type_enum_type_intersect
              by fastforce
          next
            case valid_rule_userdata_values
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types container_type_userdatatype_type_intersect
              by blast
          next
            case valid_rule_bags
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_unique_containers bag_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_sets
            then have "(contained_type (fst (FieldSig (Tm Imod1) r)), obj o1) \<in> Valid_rel Imod1"
              using o1_in_r_imod1
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod1)
          next
            case valid_rule_seqs
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_unique_containers seq_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_ords
            then have "(contained_type (fst (FieldSig (Tm Imod1) r)), obj o1) \<in> Valid_rel Imod1"
              using o1_in_r_imod1
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod1)
          qed
          then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] uncontainer (type (Tm Imod1) r)"
            unfolding type_def
            by (simp add: contained_type_is_uncontainer_r_imod1)
          then have o1_subtype_a: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)"
            using a_type_imod1 imod1_correct instance_model.validity_type_model_consistent subtype_relation_transitive_alt
            unfolding subtype_def trans_def
            by blast
          then have "FieldValue Imod1 (o1, a) \<noteq> unspecified"
            using o1_in_imod1 a_field_imod1 imod1_correct instance_model.property_field_values_inside_domain
            by fastforce
          then have fieldvalue_o1: "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod1 (o1, a)"
            unfolding imod_combine_field_value_def
            using o1_in_imod1 a_field_imod1
          proof (induct "o1 \<in> Object Imod2 \<and> a \<in> Field (Tm Imod2)")
            case True
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)")
              case True
              then show ?case
                using o1_subtype_a property_field_values_wellformed
                by simp
            next
              case False
              then have "FieldValue Imod2 (o1, a) = unspecified"
                using imod2_correct instance_model.property_field_values_outside_domain
                by metis
              then show ?case
                using False.hyps False.prems
                by simp
            qed
          next
            case False
            then show ?case
              by auto
          qed
          have o2_in_r_imod1: "edge Imod1 p r o2"
            using True.hyps fieldvalue_p o2_in_r p_present r_in_combination subtype_r p_in_imod1 r1_in_field_imod1 r_field_of_p
            unfolding edge_def edgeCount_def
            by simp
          then have o2_in_imod1: "o2 \<in> Object Imod1"
            using edge_def imod1_correct le_numeral_extra(2) edge_count_non_existant_object p_in_imod1 r_field_of_p_imod1
            by metis
          have "FieldValue Imod1 (p, r) :[Imod1] type (Tm Imod1) r"
            using True.hyps p_in_imod1 r1_in_field_imod1 imod1_correct instance_model.validity_values_typed
            by metis
          then have "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] contained_type (fst (FieldSig (Tm Imod1) r))"
            unfolding Valid_def type_def
          proof (cases)
            case valid_rule_booleans
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_integers
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_reals
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_strings
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case (valid_rule_proper_classes v)
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types container_type_class_type_intersect
              by blast
          next
            case valid_rule_nullable_classes
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types container_type_nullable_class_type_intersect
              by blast
          next
            case (valid_rule_enumvalues t v)
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types container_type_enum_type_intersect
              by fastforce
          next
            case valid_rule_userdata_values
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_container_types container_type_userdatatype_type_intersect
              by blast
          next
            case valid_rule_bags
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_unique_containers bag_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_sets
            then have "(contained_type (fst (FieldSig (Tm Imod1) r)), obj o2) \<in> Valid_rel Imod1"
              using o2_in_r_imod1
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod1)
          next
            case valid_rule_seqs
            then show ?thesis
              using r_type_imod1 unique_container_of_class_types_are_unique_containers seq_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_ords
            then have "(contained_type (fst (FieldSig (Tm Imod1) r)), obj o2) \<in> Valid_rel Imod1"
              using o2_in_r_imod1
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod1)
          qed
          then have "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] uncontainer (type (Tm Imod1) r)"
            unfolding type_def
            by (simp add: contained_type_is_uncontainer_r_imod1)
          then have o2_subtype_a: "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)"
            using a_type_imod1 imod1_correct instance_model.validity_type_model_consistent subtype_relation_transitive_alt
            unfolding subtype_def trans_def
            by blast
          then have "FieldValue Imod1 (o2, a) \<noteq> unspecified"
            using o2_in_imod1 a_field_imod1 imod1_correct instance_model.property_field_values_inside_domain
            by fastforce
          then have fieldvalue_o2: "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod1 (o2, a)"
            unfolding imod_combine_field_value_def
            using o2_in_imod1 a_field_imod1
          proof (induct "o2 \<in> Object Imod2 \<and> a \<in> Field (Tm Imod2)")
            case True
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)")
              case True
              then show ?case
                using o2_subtype_a property_field_values_wellformed
                by simp
            next
              case False
              then have "FieldValue Imod2 (o2, a) = unspecified"
                using imod2_correct instance_model.property_field_values_outside_domain
                by metis
              then show ?case
                using False.hyps False.prems
                by simp
            qed
          next
            case False
            then show ?case
              by auto
          qed
          have "FieldValue Imod1 (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue Imod1 (o2, a)"
            using value_equiv fieldvalue_o1 fieldvalue_o2
            by (simp add: imod_combine_def)
          then have "FieldValue Imod1 (o1, a) \<equiv>[Imod1] FieldValue Imod1 (o2, a)"
            using a_field_imod1 imod1_correct imod_combine_value_equiv_imod1_rev instance_model.property_field_values_inside_domain o1_in_imod1 o1_subtype_a o2_in_imod1 o2_subtype_a
            by metis
          then show ?case
            using a_in_attributes imod1_keyset o1_in_imod1 o1_in_r_imod1 o2_in_imod1 o2_in_r_imod1 p_in_imod1 r_field_of_p_imod1
            by blast
        next
          case False
          then have fieldvalue_p_imod1: "FieldValue Imod1 (p, r) = unspecified"
            using imod1_correct instance_model.property_field_values_outside_domain r1_in_field_imod1
            by metis
          have p_in_imod2: "p \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 p) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r)"
            using False.hyps False.prems fields_of_class_subtype_field_class property_field_values_not_subtype_imod1 r1_in_field_imod1 r_field_of_p
            by blast
          then have "imod_combine_field_value Imod1 Imod2 (p, r) = FieldValue Imod2 (p, r)"
            unfolding imod_combine_field_value_def
            by (simp add: fieldvalue_p_imod1 r1_in_field_imod2)
          then have fieldvalue_p: "FieldValue (imod_combine Imod1 Imod2) (p, r) = FieldValue Imod2 (p, r)"
            by (simp add: imod_combine_def)
          then have r_field_of_p_imod2: "r \<in> Type_Model.fields (Tm Imod2) (ObjectClass Imod2 p)"
            using r1_in_field_imod2 p_in_imod2
            unfolding Type_Model.fields_def class_def
            by fastforce
          have o1_in_r_imod2: "edge Imod2 p r o1"
            using False.hyps fieldvalue_p o1_in_r p_present r_in_combination subtype_r p_in_imod2 r1_in_field_imod2 r_field_of_p
            unfolding edge_def edgeCount_def
            by simp
          then have o1_in_imod2: "o1 \<in> Object Imod2"
            using edge_def imod2_correct le_numeral_extra(2) edge_count_non_existant_object p_in_imod2 r_field_of_p_imod2
            by metis
          have "FieldValue Imod2 (p, r) :[Imod2] type (Tm Imod2) r"
            using False.hyps p_in_imod2 r1_in_field_imod2 imod2_correct instance_model.validity_values_typed
            by metis
          then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] contained_type (fst (FieldSig (Tm Imod2) r))"
            unfolding Valid_def type_def
          proof (cases)
            case valid_rule_booleans
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_integers
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_reals
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_strings
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case (valid_rule_proper_classes v)
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_class_type_intersect
              by blast
          next
            case valid_rule_nullable_classes
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_nullable_class_type_intersect
              by blast
          next
            case (valid_rule_enumvalues t v)
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_enum_type_intersect
              by fastforce
          next
            case valid_rule_userdata_values
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_userdatatype_type_intersect
              by blast
          next
            case valid_rule_bags
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_unique_containers bag_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_sets
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o1) \<in> Valid_rel Imod2"
              using o1_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod2)
          next
            case valid_rule_seqs
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_unique_containers seq_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_ords
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o1) \<in> Valid_rel Imod2"
              using o1_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod2)
          qed
          then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] uncontainer (type (Tm Imod2) r)"
            unfolding type_def
            by (simp add: contained_type_is_uncontainer_r_imod2)
          then have o1_subtype_a: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)"
            using a_type_imod2 imod2_correct instance_model.validity_type_model_consistent subtype_relation_transitive_alt
            unfolding subtype_def trans_def
            by blast
          then have "FieldValue Imod2 (o1, a) \<noteq> unspecified"
            using o1_in_imod2 a_field_imod2 imod2_correct instance_model.property_field_values_inside_domain
            by fastforce
          then have fieldvalue_o1: "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod2 (o1, a)"
            unfolding imod_combine_field_value_def
            using o1_in_imod2 a_field_imod2
          proof (induct "o1 \<in> Object Imod1 \<and> a \<in> Field (Tm Imod1)")
            case True
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)")
              case True
              then show ?case
                using o1_subtype_a property_field_values_wellformed
                by simp
            next
              case False
              then have "FieldValue Imod1 (o1, a) = unspecified"
                using imod1_correct instance_model.property_field_values_outside_domain
                by metis
              then show ?case
                using False.hyps False.prems
                by simp
            qed
          next
            case False
            then show ?case
              by auto
          qed
          have o2_in_r_imod2: "edge Imod2 p r o2"
            using False.hyps fieldvalue_p o2_in_r p_present r_in_combination subtype_r p_in_imod2 r1_in_field_imod2 r_field_of_p
            unfolding edge_def edgeCount_def
            by simp
          then have o2_in_imod2: "o2 \<in> Object Imod2"
            using edge_def imod2_correct le_numeral_extra(2) edge_count_non_existant_object p_in_imod2 r_field_of_p_imod2
            by metis
          have "FieldValue Imod2 (p, r) :[Imod2] type (Tm Imod2) r"
            using False.hyps p_in_imod2 r1_in_field_imod2 imod2_correct instance_model.validity_values_typed
            by metis
          then have "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] contained_type (fst (FieldSig (Tm Imod2) r))"
            unfolding Valid_def type_def
          proof (cases)
            case valid_rule_booleans
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_integers
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_reals
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_strings
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case (valid_rule_proper_classes v)
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_class_type_intersect
              by blast
          next
            case valid_rule_nullable_classes
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_nullable_class_type_intersect
              by blast
          next
            case (valid_rule_enumvalues t v)
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_enum_type_intersect
              by fastforce
          next
            case valid_rule_userdata_values
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_userdatatype_type_intersect
              by blast
          next
            case valid_rule_bags
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_unique_containers bag_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_sets
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o2) \<in> Valid_rel Imod2"
              using o2_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod2)
          next
            case valid_rule_seqs
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_unique_containers seq_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_ords
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o2) \<in> Valid_rel Imod2"
              using o2_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod2)
          qed
          then have "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] uncontainer (type (Tm Imod2) r)"
            unfolding type_def
            by (simp add: contained_type_is_uncontainer_r_imod2)
          then have o2_subtype_a: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)"
            using a_type_imod2 imod2_correct instance_model.validity_type_model_consistent subtype_relation_transitive_alt
            unfolding subtype_def trans_def
            by blast
          then have "FieldValue Imod2 (o2, a) \<noteq> unspecified"
            using o2_in_imod2 a_field_imod2 imod2_correct instance_model.property_field_values_inside_domain
            by fastforce
          then have fieldvalue_o2: "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod2 (o2, a)"
            unfolding imod_combine_field_value_def
            using o2_in_imod2 a_field_imod2
          proof (induct "o2 \<in> Object Imod1 \<and> a \<in> Field (Tm Imod1)")
            case True
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)")
              case True
              then show ?case
                using o2_subtype_a property_field_values_wellformed
                by simp
            next
              case False
              then have "FieldValue Imod1 (o2, a) = unspecified"
                using imod1_correct instance_model.property_field_values_outside_domain
                by metis
              then show ?case
                using False.hyps False.prems
                by simp
            qed
          next
            case False
            then show ?case
              by auto
          qed
          have "FieldValue Imod2 (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue Imod2 (o2, a)"
            using value_equiv fieldvalue_o1 fieldvalue_o2
            by (simp add: imod_combine_def)
          then have "FieldValue Imod2 (o1, a) \<equiv>[Imod2] FieldValue Imod2 (o2, a)"
            using a_field_imod2 imod2_correct imod_combine_value_equiv_imod2_rev instance_model.property_field_values_inside_domain o1_in_imod2 o1_subtype_a o2_in_imod2 o2_subtype_a
            by metis
          then show ?case
            using a_in_attributes imod2_keyset o1_in_imod2 o1_in_r_imod2 o2_in_imod2 o2_in_r_imod2 p_in_imod2 r_field_of_p_imod2
            by blast
        qed
      next
        assume p_in_imod2: "p \<in> Object Imod2 - Object Imod1"
        then have "imod_combine_field_value Imod1 Imod2 (p, r) = FieldValue Imod2 (p, r)"
          unfolding imod_combine_field_value_def
          by (simp add: r1_in_field_imod2)
        then have "FieldValue (imod_combine Imod1 Imod2) (p, r) = FieldValue Imod2 (p, r)"
          by (simp add: imod_combine_def)
        then show ?thesis
        proof (induct "\<exclamdown>(ObjectClass Imod2 p) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r)")
          case True
          then have r_field_of_p_imod2: "r \<in> Type_Model.fields (Tm Imod2) (ObjectClass Imod2 p)"
            unfolding Type_Model.fields_def class_def
            using r1_in_field_imod2
            by fastforce
          have o1_in_r_imod2: "edge Imod2 p r o1"
            using True.hyps True.prems o1_in_r p_present r_in_combination subtype_r p_in_imod2 r1_in_field_imod2 r_field_of_p
            unfolding edge_def edgeCount_def
            by simp
          then have o1_in_imod2: "o1 \<in> Object Imod2"
            using DiffD1 edge_def imod2_correct le_numeral_extra(2) edge_count_non_existant_object p_in_imod2 r_field_of_p_imod2
            by metis
          have "FieldValue Imod2 (p, r) :[Imod2] type (Tm Imod2) r"
            using DiffD1 True.hyps p_in_imod2 r1_in_field_imod2 imod2_correct instance_model.validity_values_typed
            by metis
          then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] contained_type (fst (FieldSig (Tm Imod2) r))"
            unfolding Valid_def type_def
          proof (cases)
            case valid_rule_booleans
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_integers
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_reals
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_strings
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case (valid_rule_proper_classes v)
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_class_type_intersect
              by blast
          next
            case valid_rule_nullable_classes
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_nullable_class_type_intersect
              by blast
          next
            case (valid_rule_enumvalues t v)
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_enum_type_intersect
              by fastforce
          next
            case valid_rule_userdata_values
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_userdatatype_type_intersect
              by blast
          next
            case valid_rule_bags
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_unique_containers bag_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_sets
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o1) \<in> Valid_rel Imod2"
              using o1_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod2)
          next
            case valid_rule_seqs
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_unique_containers seq_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_ords
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o1) \<in> Valid_rel Imod2"
              using o1_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod2)
          qed
          then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] uncontainer (type (Tm Imod2) r)"
            unfolding type_def
            by (simp add: contained_type_is_uncontainer_r_imod2)
          then have o1_subtype_a: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)"
            using a_type_imod2 imod2_correct instance_model.validity_type_model_consistent subtype_relation_transitive_alt
            unfolding subtype_def trans_def
            by blast
          then have "FieldValue Imod2 (o1, a) \<noteq> unspecified"
            using o1_in_imod2 a_field_imod2 imod2_correct instance_model.property_field_values_inside_domain
            by fastforce
          then have fieldvalue_o1: "imod_combine_field_value Imod1 Imod2 (o1, a) = FieldValue Imod2 (o1, a)"
            unfolding imod_combine_field_value_def
            using o1_in_imod2 a_field_imod2
          proof (induct "o1 \<in> Object Imod1 \<and> a \<in> Field (Tm Imod1)")
            case True
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)")
              case True
              then show ?case
                using o1_subtype_a property_field_values_wellformed
                by simp
            next
              case False
              then have "FieldValue Imod1 (o1, a) = unspecified"
                using imod1_correct instance_model.property_field_values_outside_domain
                by metis
              then show ?case
                using False.hyps False.prems
                by simp
            qed
          next
            case False
            then show ?case
              by auto
          qed
          have o2_in_r_imod2: "edge Imod2 p r o2"
            using True.hyps True.prems o2_in_r p_present r_in_combination subtype_r p_in_imod2 r1_in_field_imod2 r_field_of_p
            unfolding edge_def edgeCount_def
            by simp
          then have o2_in_imod2: "o2 \<in> Object Imod2"
            using DiffD1 edge_def imod2_correct le_numeral_extra(2) edge_count_non_existant_object p_in_imod2 r_field_of_p_imod2
            by metis
          have "FieldValue Imod2 (p, r) :[Imod2] type (Tm Imod2) r"
            using DiffD1 True.hyps p_in_imod2 r1_in_field_imod2 imod2_correct instance_model.validity_values_typed
            by metis
          then have "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] contained_type (fst (FieldSig (Tm Imod2) r))"
            unfolding Valid_def type_def
          proof (cases)
            case valid_rule_booleans
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_integers
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_reals
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case valid_rule_strings
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types
              by fastforce
          next
            case (valid_rule_proper_classes v)
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_class_type_intersect
              by blast
          next
            case valid_rule_nullable_classes
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_nullable_class_type_intersect
              by blast
          next
            case (valid_rule_enumvalues t v)
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_enum_type_intersect
              by fastforce
          next
            case valid_rule_userdata_values
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_container_types container_type_userdatatype_type_intersect
              by blast
          next
            case valid_rule_bags
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_unique_containers bag_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_sets
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o2) \<in> Valid_rel Imod2"
              using o2_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod2)
          next
            case valid_rule_seqs
            then show ?thesis
              using r_type_imod2 unique_container_of_class_types_are_unique_containers seq_types_are_non_unique_containers unique_and_non_unique_containers_distinct
              by blast
          next
            case valid_rule_ords
            then have "(contained_type (fst (FieldSig (Tm Imod2) r)), obj o2) \<in> Valid_rel Imod2"
              using o2_in_r_imod2
              by simp
            then show ?thesis
              by (cases) (simp_all add: contained_type_r_imod2)
          qed
          then have "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] uncontainer (type (Tm Imod2) r)"
            unfolding type_def
            by (simp add: contained_type_is_uncontainer_r_imod2)
          then have o2_subtype_a: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) a)"
            using a_type_imod2 imod2_correct instance_model.validity_type_model_consistent subtype_relation_transitive_alt
            unfolding subtype_def trans_def
            by blast
          then have "FieldValue Imod2 (o2, a) \<noteq> unspecified"
            using o2_in_imod2 a_field_imod2 imod2_correct instance_model.property_field_values_inside_domain
            by fastforce
          then have fieldvalue_o2: "imod_combine_field_value Imod1 Imod2 (o2, a) = FieldValue Imod2 (o2, a)"
            unfolding imod_combine_field_value_def
            using o2_in_imod2 a_field_imod2
          proof (induct "o2 \<in> Object Imod1 \<and> a \<in> Field (Tm Imod1)")
            case True
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) a)")
              case True
              then show ?case
                using o2_subtype_a property_field_values_wellformed
                by simp
            next
              case False
              then have "FieldValue Imod1 (o2, a) = unspecified"
                using imod1_correct instance_model.property_field_values_outside_domain
                by metis
              then show ?case
                using False.hyps False.prems
                by simp
            qed
          next
            case False
            then show ?case
              by auto
          qed
          have "FieldValue Imod2 (o1, a) \<equiv>[imod_combine Imod1 Imod2] FieldValue Imod2 (o2, a)"
            using value_equiv fieldvalue_o1 fieldvalue_o2
            by (simp add: imod_combine_def)
          then have "FieldValue Imod2 (o1, a) \<equiv>[Imod2] FieldValue Imod2 (o2, a)"
            using a_field_imod2 imod2_correct imod_combine_value_equiv_imod2_rev instance_model.property_field_values_inside_domain o1_in_imod2 o1_subtype_a o2_in_imod2 o2_subtype_a
            by metis
          then show ?case
            using a_in_attributes imod2_keyset o1_in_imod2 o1_in_r_imod2 o2_in_imod2 o2_in_r_imod2 p_in_imod2 r_field_of_p_imod2
            by blast
        next
          case False
          then show ?case
            using DiffD1 DiffD2 fields_of_class_subtype_field_class p_in_imod2 property_field_values_not_subtype_imod2 r1_in_field_imod2 r_field_of_p
            by metis
        qed
      qed
    qed
  next
    case (opposite_property_tmod1 r1 r2)
    then have "Imod1 \<Turnstile> opposite r1 r2"
      using imod1_correct instance_model.validity_properties_satisfied
      by blast
    then have imod1_opposite: "\<And>o1 o2. o1 \<in> Object Imod1 \<Longrightarrow> o2 \<in> Object Imod1 \<Longrightarrow> edgeCount Imod1 o1 r1 o2 = edgeCount Imod1 o2 r2 o1"
      using property_satisfaction_opposite_rev
      by metis
    have "opposite r1 r2 \<in> Property (Tm Imod1)"
      using imod1_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed opposite_property_tmod1.hyps(1)
      by blast
    then have opposite_props: "r1 \<in> Rel (Tm Imod1) \<and> r2 \<in> Rel (Tm Imod1) \<and> r1 \<noteq> r2 \<and> 
      \<exclamdown>(class (Tm Imod1) r1) = uncontainer (type (Tm Imod1) r2) \<and> \<exclamdown>(class (Tm Imod1) r2) = uncontainer (type (Tm Imod1) r1) \<and> 
      type (Tm Imod1) r1 \<notin> NonUniqueContainerType (Tm Imod1) \<and> type (Tm Imod1) r2 \<notin> NonUniqueContainerType (Tm Imod1)"
      using properties_rev_impl_opposite
      by blast
    have r1_in_field: "r1 \<in> Field (Tm Imod1)"
      using opposite_props
      unfolding Rel_def
      by blast
    then have r1_in_combination: "r1 \<in> Field (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def tmod_combine_def)
    have r2_in_field: "r2 \<in> Field (Tm Imod1)"
      using opposite_props
      unfolding Rel_def
      by blast
    then have r2_in_combination: "r2 \<in> Field (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def tmod_combine_def)
    show ?case
    proof (intro property_satisfaction.rule_property_opposite)
      fix o1 o2
      assume o1_present: "o1 \<in> Object (imod_combine Imod1 Imod2)"
      then have o1_in_object: "o1 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have o1_in_object_cases: "o1 \<in> Object Imod1 \<or> o1 \<in> Object Imod2 - Object Imod1"
        by blast
      assume o2_present: "o2 \<in> Object (imod_combine Imod1 Imod2)"
      then have o2_in_object: "o2 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have o2_in_object_cases: "o2 \<in> Object Imod1 \<or> o2 \<in> Object Imod2 - Object Imod1"
        by blast
      show "edgeCount (imod_combine Imod1 Imod2) o1 r1 o2 = edgeCount (imod_combine Imod1 Imod2) o2 r2 o1"
        using o1_in_object_cases o2_in_object_cases
      proof (elim disjE)
        assume o1_in_imod1: "o1 \<in> Object Imod1"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        assume o2_in_imod1: "o2 \<in> Object Imod1"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod1 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod1 o2"
          by (simp add: imod_combine_def)
        have r1_subtype_cases: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1) \<or> \<not>\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          by simp
        have r2_subtype_cases: "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2) \<or> \<not>\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
          by simp
        show ?thesis
          using r1_subtype_cases r2_subtype_cases
        proof (elim disjE)
          assume subtype_r1: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          then have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
            using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def tmod_combine_subtype_subset_tmod1
            by metis
          have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod1 (o1, r1)"
            unfolding imod_combine_field_value_def
            by (simp add: o1_in_imod1 opposite_property_tmod1.hyps(2) r1_in_field)
          then have edge_count_r1_def: "edgeCount Imod1 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
            unfolding edgeCount_def
            using o1_in_imod1 r1_in_field subtype_r1
            by simp
          assume subtype_r2: "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
          then have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
            using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def tmod_combine_subtype_subset_tmod1
            by metis
          have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod1 (o2, r2)"
            unfolding imod_combine_field_value_def
            by (simp add: o2_in_imod1 opposite_property_tmod1.hyps(3) r2_in_field)
          then have edge_count_r2_def: "edgeCount Imod1 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
            unfolding edgeCount_def
            using o2_in_imod1 r2_in_field subtype_r2
            by simp
          have "edgeCount Imod1 o1 r1 o2 = edgeCount Imod1 o2 r2 o1"
            using imod1_opposite o1_in_imod1 o2_in_imod1
            by blast
          then show ?thesis
            using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5) o1_present o2_present r1_in_combination r2_in_combination subtype_combine_r1 subtype_combine_r2
            by metis
        next
          assume subtype_r1: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          then have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
            using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def tmod_combine_subtype_subset_tmod1
            by metis
          have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod1 (o1, r1)"
            unfolding imod_combine_field_value_def
            by (simp add: o1_in_imod1 opposite_property_tmod1.hyps(2) r1_in_field)
          then have edge_count_r1_def: "edgeCount Imod1 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
            unfolding edgeCount_def
            using o1_in_imod1 r1_in_field subtype_r1
            by simp
          assume not_subtype_r2: "\<not>\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
          have edge_count_r2_def: "edgeCount Imod1 o2 r2 o1 = 0"
            unfolding edgeCount_def
            using not_subtype_r2
            by simp
          have "edgeCount Imod1 o1 r1 o2 = edgeCount Imod1 o2 r2 o1"
            using imod1_opposite o1_in_imod1 o2_in_imod1
            by blast
          then show ?thesis
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
            case True
            then show ?case
              using not_subtype_r2 o2_in_imod1 opposite_property_tmod1.hyps(3) property_field_values_not_subtype_imod1 r2_in_field
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5)
              by metis
          qed
        next
          assume not_subtype_r1: "\<not>\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          have edge_count_r2_def: "edgeCount Imod1 o1 r1 o2 = 0"
            unfolding edgeCount_def
            using not_subtype_r1
            by simp
          assume subtype_r2: "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
          then have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
            using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def tmod_combine_subtype_subset_tmod1
            by metis
          have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod1 (o2, r2)"
            unfolding imod_combine_field_value_def
            by (simp add: o2_in_imod1 opposite_property_tmod1.hyps(3) r2_in_field)
          then have edge_count_r1_def: "edgeCount Imod1 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
            unfolding edgeCount_def
            using o2_in_imod1 r2_in_field subtype_r2
            by simp
          have "edgeCount Imod1 o1 r1 o2 = edgeCount Imod1 o2 r2 o1"
            using imod1_opposite o1_in_imod1 o2_in_imod1
            by blast
          then show ?thesis
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using not_subtype_r1 o1_in_imod1 opposite_property_tmod1.hyps(2) property_field_values_not_subtype_imod1 r1_in_field
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5)
              by metis
          qed
        next
          assume not_subtype_r1: "\<not>\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          assume not_subtype_r2: "\<not>\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
          have "edgeCount Imod1 o1 r1 o2 = edgeCount Imod1 o2 r2 o1"
            using imod1_opposite o1_in_imod1 o2_in_imod1
            by blast
          then show ?thesis
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using not_subtype_r1 o1_in_imod1 opposite_property_tmod1.hyps(2) property_field_values_not_subtype_imod1 r1_in_field
              by blast
          next
            case False
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
              case True
              then show ?case
                using not_subtype_r2 o2_in_imod1 opposite_property_tmod1.hyps(3) property_field_values_not_subtype_imod1 r2_in_field
                by blast
            next
              case False
              then show ?case
                unfolding edgeCount_def
                by simp
            qed
          qed
        qed
      next
        assume o1_in_imod1: "o1 \<in> Object Imod1"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        assume o2_in_imod2: "o2 \<in> Object Imod2 - Object Imod1"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod2 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod2 o2"
          by (simp add: imod_combine_def)
        have r1_subtype_cases: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1) \<or> \<not>\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          by simp
        have r2_subtype_cases: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2) \<or> \<not>\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
          by simp
        show ?thesis
          using r2_subtype_cases
        proof (elim disjE)
          assume subtype_r2: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
          then have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
            using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def tmod_combine_subtype_subset_tmod2
            by metis
          then have "o2 \<in> Object Imod1"
            using Diff_iff UnE o2_in_object opposite_property_tmod1.hyps(3) property_field_values_not_field_imod2 r2_in_field
            by metis
          then show ?thesis
            using o2_in_imod2
            by blast
        next
          assume no_subtype_r2: "\<not>\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
          show ?thesis
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
            case True
            then show ?case
              using o2_in_imod2 opposite_property_tmod1.hyps(3) property_field_values_not_field_imod2 r2_in_field
              by blast
          next
            case False
            then have edge_count_r2_def: "edgeCount (imod_combine Imod1 Imod2) o2 r2 o1 = 0"
              unfolding edgeCount_def
              by simp
            show ?case
              using r1_subtype_cases
            proof (elim disjE)
              assume subtype_r1: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
              then have r1_in_fields: "r1 \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 o1)"
                unfolding Type_Model.fields_def class_def
                using r1_in_field
                by fastforce
              have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod1 (o1, r1)"
                unfolding imod_combine_field_value_def
                by (simp add: o1_in_imod1 opposite_property_tmod1.hyps(2) r1_in_field)
              then have edge_count_r1_def: "edgeCount Imod1 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
                unfolding edgeCount_def
                using o1_in_imod1 r1_in_field subtype_r1
                by simp
              then show ?thesis
                using DiffD2 edgeCount_def edge_count_non_existant_object edge_count_r2_def imod1_correct imod_combine_def instance_model.select_convs(5) o2_in_imod2 r1_in_fields
                by metis
            next
              assume no_subtype_r1: "\<not>\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
              show ?thesis
              proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
                case True
                then show ?case
                  using no_subtype_r1 o1_in_imod1 opposite_property_tmod1.hyps(2) property_field_values_not_subtype_imod1 r1_in_field
                  by blast
              next
                case False
                then have "edgeCount (imod_combine Imod1 Imod2) o1 r1 o2 = 0"
                  unfolding edgeCount_def
                  by simp
                then show ?case
                  by (simp add: edge_count_r2_def)
              qed
            qed
          qed
        qed
      next
        assume o1_in_imod2: "o1 \<in> Object Imod2 - Object Imod1"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod2 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod2 o1"
          by (simp add: imod_combine_def)
        assume o2_in_imod1: "o2 \<in> Object Imod1"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod1 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod1 o2"
          by (simp add: imod_combine_def)
        have r1_subtype_cases: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1) \<or> \<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          by simp
        have r2_subtype_cases: "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2) \<or> \<not>\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
          by simp
        show ?thesis
          using r1_subtype_cases
        proof (elim disjE)
          assume subtype_r1: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          then have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
            using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def tmod_combine_subtype_subset_tmod2
            by metis
          then have "o1 \<in> Object Imod1"
            using Diff_iff o1_in_imod2 opposite_property_tmod1.hyps(2) property_field_values_not_field_imod2 r1_in_field
            by metis
          then show ?thesis
            using o1_in_imod2
            by blast
        next
          assume no_subtype_r1: "\<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          show ?thesis
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using o1_in_imod2 opposite_property_tmod1.hyps(2) property_field_values_not_field_imod2 r1_in_field
              by blast
          next
            case False
            then have edge_count_r1_def: "edgeCount (imod_combine Imod1 Imod2) o1 r1 o2 = 0"
              unfolding edgeCount_def
              by simp
            show ?case
              using r2_subtype_cases
            proof (elim disjE)
              assume subtype_r2: "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
              then have r1_in_fields: "r2 \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 o2)"
                unfolding Type_Model.fields_def class_def
                using r2_in_field
                by fastforce
              have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod1 (o2, r2)"
                unfolding imod_combine_field_value_def
                by (simp add: o2_in_imod1 opposite_property_tmod1.hyps(3) r2_in_field)
              then have edge_count_r1_def: "edgeCount Imod1 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
                unfolding edgeCount_def
                using o2_in_imod1 r2_in_field subtype_r2
                by simp
              then show ?thesis
                using Diff_iff False.hyps edgeCount_def edge_count_non_existant_object imod1_correct imod_combine_def instance_model.select_convs(5) o1_in_imod2 r1_in_fields
                by metis
            next
              assume no_subtype_r2: "\<not>\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
              show ?thesis
              proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
                case True
                then show ?case
                  using no_subtype_r2 o2_in_imod1 opposite_property_tmod1.hyps(3) property_field_values_not_subtype_imod1 r2_in_field
                  by blast
              next
                case False
                then have "edgeCount (imod_combine Imod1 Imod2) o2 r2 o1 = 0"
                  unfolding edgeCount_def
                  by simp
                then show ?case
                  by (simp add: edge_count_r1_def)
              qed
            qed
          qed
        qed
      next
        assume o1_in_imod2: "o1 \<in> Object Imod2 - Object Imod1"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod2 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod2 o1"
          by (simp add: imod_combine_def)
        assume o2_in_imod2: "o2 \<in> Object Imod2 - Object Imod1"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod2 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod2 o2"
          by (simp add: imod_combine_def)
        have r1_subtype_cases: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1) \<or> \<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          by simp
        have r2_subtype_cases: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2) \<or> \<not>\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
          by simp
        show ?thesis
          using r1_subtype_cases
        proof (elim disjE)
          assume subtype_r1: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          then have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
            using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def tmod_combine_subtype_subset_tmod2
            by metis
          then have "o1 \<in> Object Imod1"
            using Diff_iff o1_in_imod2 opposite_property_tmod1.hyps(2) property_field_values_not_field_imod2 r1_in_field
            by metis
          then show ?thesis
            using o1_in_imod2
            by blast
        next
          assume not_subtype_r1: "\<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          show ?thesis
            using r2_subtype_cases
          proof (elim disjE)
            assume subtype_r2: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
            then have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
              using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def tmod_combine_subtype_subset_tmod2
              by metis
            then have "o2 \<in> Object Imod1"
              using Diff_iff UnE o2_in_object opposite_property_tmod1.hyps(3) property_field_values_not_field_imod2 r2_in_field
              by metis
            then show ?thesis
              using o2_in_imod2
              by blast
          next
            assume not_subtype_r2: "\<not>\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
            show ?thesis
            proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
              case True
              then show ?case
                using Diff_iff o1_in_imod2 opposite_property_tmod1.hyps(2) property_field_values_not_field_imod2 r1_in_field
                by metis
            next
              case False
              then show ?case
              proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
                case True
                then show ?case
                  using Diff_iff o2_in_imod2 opposite_property_tmod1.hyps(3) property_field_values_not_field_imod2 r2_in_field
                  by metis
              next
                case False
                then show ?case
                  unfolding edgeCount_def
                  by simp
              qed
            qed
          qed
        qed
      qed
    qed
  next
    case (opposite_property_tmod2 r1 r2)
    then have "Imod2 \<Turnstile> opposite r1 r2"
      using imod2_correct instance_model.validity_properties_satisfied
      by blast
    then have imod2_opposite: "\<And>o1 o2. o1 \<in> Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 \<Longrightarrow> edgeCount Imod2 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
      using property_satisfaction_opposite_rev
      by metis
    have "opposite r1 r2 \<in> Property (Tm Imod2)"
      using imod2_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed opposite_property_tmod2.hyps(1)
      by blast
    then have opposite_props: "r1 \<in> Rel (Tm Imod2) \<and> r2 \<in> Rel (Tm Imod2) \<and> r1 \<noteq> r2 \<and> 
      \<exclamdown>(class (Tm Imod2) r1) = uncontainer (type (Tm Imod2) r2) \<and> \<exclamdown>(class (Tm Imod2) r2) = uncontainer (type (Tm Imod2) r1) \<and> 
      type (Tm Imod2) r1 \<notin> NonUniqueContainerType (Tm Imod2) \<and> type (Tm Imod2) r2 \<notin> NonUniqueContainerType (Tm Imod2)"
      using properties_rev_impl_opposite
      by blast
    have r1_in_field: "r1 \<in> Field (Tm Imod2)"
      using opposite_props
      unfolding Rel_def
      by blast
    then have r1_in_combination: "r1 \<in> Field (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def tmod_combine_def)
    have r2_in_field: "r2 \<in> Field (Tm Imod2)"
      using opposite_props
      unfolding Rel_def
      by blast
    then have r2_in_combination: "r2 \<in> Field (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def tmod_combine_def)
    show ?case
    proof (intro property_satisfaction.rule_property_opposite)
      fix o1 o2
      assume o1_present: "o1 \<in> Object (imod_combine Imod1 Imod2)"
      then have o1_in_object: "o1 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have o1_in_object_cases: "o1 \<in> Object Imod2 \<or> o1 \<in> Object Imod1 - Object Imod2"
        by blast
      assume o2_present: "o2 \<in> Object (imod_combine Imod1 Imod2)"
      then have o2_in_object: "o2 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      then have o2_in_object_cases: "o2 \<in> Object Imod2 \<or> o2 \<in> Object Imod1 - Object Imod2"
        by blast
      show "edgeCount (imod_combine Imod1 Imod2) o1 r1 o2 = edgeCount (imod_combine Imod1 Imod2) o2 r2 o1"
        using o1_in_object_cases o2_in_object_cases
      proof (elim disjE)
        assume o1_in_imod2: "o1 \<in> Object Imod2"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod2 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod2 o1"
          by (simp add: imod_combine_def)
        assume o2_in_imod2: "o2 \<in> Object Imod2"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod2 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod2 o2"
          by (simp add: imod_combine_def)
        have r1_subtype_cases: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1) \<or> \<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          by simp
        have r2_subtype_cases: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2) \<or> \<not>\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
          by simp
        show ?thesis
          using r1_subtype_cases r2_subtype_cases
        proof (elim disjE)
          assume subtype_r1: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          then have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
            using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def tmod_combine_subtype_subset_tmod2
            by metis
          have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod2 (o1, r1)"
            unfolding imod_combine_field_value_def
            by (simp add: o1_in_imod2 opposite_property_tmod2.hyps(2) r1_in_field)
          then have edge_count_r1_def: "edgeCount Imod2 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
            unfolding edgeCount_def
            using o1_in_imod2 r1_in_field subtype_r1
            by simp
          assume subtype_r2: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
          then have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
            using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def tmod_combine_subtype_subset_tmod2
            by metis
          have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod2 (o2, r2)"
            unfolding imod_combine_field_value_def
            by (simp add: o2_in_imod2 opposite_property_tmod2.hyps(3) r2_in_field)
          then have edge_count_r2_def: "edgeCount Imod2 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
            unfolding edgeCount_def
            using o2_in_imod2 r2_in_field subtype_r2
            by simp
          have "edgeCount Imod2 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
            using imod2_opposite o1_in_imod2 o2_in_imod2
            by blast
          then show ?thesis
            using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5) o1_present o2_present r1_in_combination r2_in_combination subtype_combine_r1 subtype_combine_r2
            by metis
        next
          assume subtype_r1: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          then have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
            using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def tmod_combine_subtype_subset_tmod2
            by metis
          have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod2 (o1, r1)"
            unfolding imod_combine_field_value_def
            by (simp add: o1_in_imod2 opposite_property_tmod2.hyps(2) r1_in_field)
          then have edge_count_r1_def: "edgeCount Imod2 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
            unfolding edgeCount_def
            using o1_in_imod2 r1_in_field subtype_r1
            by simp
          assume not_subtype_r2: "\<not>\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
          have edge_count_r2_def: "edgeCount Imod2 o2 r2 o1 = 0"
            unfolding edgeCount_def
            using not_subtype_r2
            by simp
          have "edgeCount Imod2 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
            using imod2_opposite o1_in_imod2 o2_in_imod2
            by blast
          then show ?thesis
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
            case True
            then show ?case
              using not_subtype_r2 o2_in_imod2 opposite_property_tmod2.hyps(3) property_field_values_not_subtype_imod2 r2_in_field
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5)
              by metis
          qed
        next
          assume not_subtype_r1: "\<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          have edge_count_r1_def: "edgeCount Imod2 o1 r1 o2 = 0"
            unfolding edgeCount_def
            using not_subtype_r1
            by simp
          assume subtype_r2: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
          then have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
            using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def tmod_combine_subtype_subset_tmod2
            by metis
          have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod2 (o2, r2)"
            unfolding imod_combine_field_value_def
            by (simp add: o2_in_imod2 opposite_property_tmod2.hyps(3) r2_in_field)
          then have edge_count_r2_def: "edgeCount Imod2 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
            unfolding edgeCount_def
            using o2_in_imod2 r2_in_field subtype_r2
            by simp
          have "edgeCount Imod2 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
            using imod2_opposite o1_in_imod2 o2_in_imod2
            by blast
          then show ?thesis
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using not_subtype_r1 o1_in_imod2 opposite_property_tmod2.hyps(2) property_field_values_not_subtype_imod2 r1_in_field
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5)
              by metis
          qed
        next
          assume not_subtype_r1: "\<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          assume not_subtype_r2: "\<not>\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
          have "edgeCount Imod2 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
            using imod2_opposite o1_in_imod2 o2_in_imod2
            by blast
          then show ?thesis
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using not_subtype_r1 o1_in_imod2 opposite_property_tmod2.hyps(2) property_field_values_not_subtype_imod2 r1_in_field
              by blast
          next
            case False
            then show ?case
            proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
              case True
              then show ?case
                using not_subtype_r2 o2_in_imod2 opposite_property_tmod2.hyps(3) property_field_values_not_subtype_imod2 r2_in_field
                by blast
            next
              case False
              then show ?case
                unfolding edgeCount_def
                by simp
            qed
          qed
        qed
      next
        assume o1_in_imod2: "o1 \<in> Object Imod2"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod2 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod2 o1"
          by (simp add: imod_combine_def)
        assume o2_in_imod1: "o2 \<in> Object Imod1 - Object Imod2"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod1 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod1 o2"
          by (simp add: imod_combine_def)
        have r1_subtype_cases: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1) \<or> \<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
          by simp
        have r2_subtype_cases: "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2) \<or> \<not>\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
          by simp
        show ?thesis
          using r2_subtype_cases
        proof (elim disjE)
          assume subtype_r2: "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
          then have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
            using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def tmod_combine_subtype_subset_tmod1
            by metis
          then have "o2 \<in> Object Imod2"
            using Diff_iff UnE o2_in_object opposite_property_tmod2.hyps(3) property_field_values_not_field_imod1 r2_in_field
            by metis
          then show ?thesis
            using o2_in_imod1
            by blast
        next
          assume no_subtype_r2: "\<not>\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
          show ?thesis
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
            case True
            then show ?case
              using o2_in_imod1 opposite_property_tmod2.hyps(3) property_field_values_not_field_imod1 r2_in_field
              by blast
          next
            case False
            then have edge_count_r2_def: "edgeCount (imod_combine Imod1 Imod2) o2 r2 o1 = 0"
              unfolding edgeCount_def
              by simp
            show ?case
              using r1_subtype_cases
            proof (elim disjE)
              assume subtype_r1: "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
              then have r1_in_fields: "r1 \<in> Type_Model.fields (Tm Imod2) (ObjectClass Imod2 o1)"
                unfolding Type_Model.fields_def class_def
                using r1_in_field
                by fastforce
              have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod2 (o1, r1)"
                unfolding imod_combine_field_value_def
                by (simp add: o1_in_imod2 opposite_property_tmod2.hyps(2) r1_in_field)
              then have edge_count_r1_def: "edgeCount Imod2 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
                unfolding edgeCount_def
                using o1_in_imod2 r1_in_field subtype_r1
                by simp
              then show ?thesis
                using DiffD2 edgeCount_def edge_count_non_existant_object edge_count_r2_def imod2_correct imod_combine_def instance_model.select_convs(5) o2_in_imod1 r1_in_fields
                by metis
            next
              assume no_subtype_r1: "\<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
              show ?thesis
              proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
                case True
                then show ?case
                  using no_subtype_r1 o1_in_imod2 opposite_property_tmod2.hyps(2) property_field_values_not_subtype_imod2 r1_in_field
                  by blast
              next
                case False
                then have "edgeCount (imod_combine Imod1 Imod2) o1 r1 o2 = 0"
                  unfolding edgeCount_def
                  by simp
                then show ?case
                  by (simp add: edge_count_r2_def)
              qed
            qed
          qed
        qed
      next
        assume o1_in_imod1: "o1 \<in> Object Imod1 - Object Imod2"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        assume o2_in_imod2: "o2 \<in> Object Imod2"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod2 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod2 o2"
          by (simp add: imod_combine_def)
        have r1_subtype_cases: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1) \<or> \<not>\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          by simp
        have r2_subtype_cases: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2) \<or> \<not>\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
          by simp
        show ?thesis
          using r1_subtype_cases
        proof (elim disjE)
          assume subtype_r1: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          then have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
            using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def tmod_combine_subtype_subset_tmod1
            by metis
          then have "o1 \<in> Object Imod2"
            using Diff_iff o1_in_imod1 opposite_property_tmod2.hyps(2) property_field_values_not_field_imod1 r1_in_field
            by metis
          then show ?thesis
            using o1_in_imod1
            by blast
        next
          assume no_subtype_r1: "\<not>\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          show ?thesis
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using o1_in_imod1 opposite_property_tmod2.hyps(2) property_field_values_not_field_imod1 r1_in_field
              by blast
          next
            case False
            then have edge_count_r1_def: "edgeCount (imod_combine Imod1 Imod2) o1 r1 o2 = 0"
              unfolding edgeCount_def
              by simp
            show ?case
              using r2_subtype_cases
            proof (elim disjE)
              assume subtype_r2: "\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
              then have r1_in_fields: "r2 \<in> Type_Model.fields (Tm Imod2) (ObjectClass Imod2 o2)"
                unfolding Type_Model.fields_def class_def
                using r2_in_field
                by fastforce
              have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod2 (o2, r2)"
                unfolding imod_combine_field_value_def
                by (simp add: o2_in_imod2 opposite_property_tmod2.hyps(3) r2_in_field)
              then have edge_count_r1_def: "edgeCount Imod2 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
                unfolding edgeCount_def
                using o2_in_imod2 r2_in_field subtype_r2
                by simp
              then show ?thesis
                using Diff_iff False.hyps edgeCount_def edge_count_non_existant_object imod2_correct imod_combine_def instance_model.select_convs(5) o1_in_imod1 r1_in_fields
                by metis
            next
              assume no_subtype_r2: "\<not>\<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
              show ?thesis
              proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
                case True
                then show ?case
                  using no_subtype_r2 o2_in_imod2 opposite_property_tmod2.hyps(3) property_field_values_not_subtype_imod2 r2_in_field
                  by blast
              next
                case False
                then have "edgeCount (imod_combine Imod1 Imod2) o2 r2 o1 = 0"
                  unfolding edgeCount_def
                  by simp
                then show ?case
                  by (simp add: edge_count_r1_def)
              qed
            qed
          qed
        qed
      next
        assume o1_in_imod1: "o1 \<in> Object Imod1 - Object Imod2"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        assume o2_in_imod1: "o2 \<in> Object Imod1 - Object Imod2"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod1 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod1 o2"
          by (simp add: imod_combine_def)
        have r1_subtype_cases: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1) \<or> \<not>\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          by simp
        have r2_subtype_cases: "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2) \<or> \<not>\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
          by simp
        show ?thesis
          using r1_subtype_cases
        proof (elim disjE)
          assume subtype_r1: "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          then have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
            using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def tmod_combine_subtype_subset_tmod1
            by metis
          then have "o1 \<in> Object Imod2"
            using Diff_iff o1_in_imod1 opposite_property_tmod2.hyps(2) property_field_values_not_field_imod1 r1_in_field
            by metis
          then show ?thesis
            using o1_in_imod1
            by blast
        next
          assume not_subtype_r1: "\<not>\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
          show ?thesis
            using r2_subtype_cases
          proof (elim disjE)
            assume subtype_r2: "\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
            then have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
              using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def tmod_combine_subtype_subset_tmod1
              by metis
            then have "o2 \<in> Object Imod2"
              using Diff_iff UnE o2_in_object opposite_property_tmod2.hyps(3) property_field_values_not_field_imod1 r2_in_field
              by metis
            then show ?thesis
              using o2_in_imod1
              by blast
          next
            assume not_subtype_r2: "\<not>\<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
            show ?thesis
            proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
              case True
              then show ?case
                using Diff_iff o1_in_imod1 opposite_property_tmod2.hyps(2) property_field_values_not_field_imod1 r1_in_field
                by metis
            next
              case False
              then show ?case
              proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
                case True
                then show ?case
                  using Diff_iff o2_in_imod1 opposite_property_tmod2.hyps(3) property_field_values_not_field_imod1 r2_in_field
                  by metis
              next
                case False
                then show ?case
                  unfolding edgeCount_def
                  by simp
              qed
            qed
          qed
        qed
      qed
    qed
  next
    case (opposite_property_both r1 r2)
    have "Imod1 \<Turnstile> opposite r1 r2"
      using imod1_correct instance_model.validity_properties_satisfied opposite_property_both.hyps(1)
      by blast
    then have imod1_opposite: "\<And>o1 o2. o1 \<in> Object Imod1 \<Longrightarrow> o2 \<in> Object Imod1 \<Longrightarrow> edgeCount Imod1 o1 r1 o2 = edgeCount Imod1 o2 r2 o1"
      using property_satisfaction_opposite_rev
      by metis
    have "opposite r1 r2 \<in> Property (Tm Imod1)"
      using imod1_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed opposite_property_both.hyps(1)
      by blast
    then have imod1_opposite_props: "r1 \<in> Rel (Tm Imod1) \<and> r2 \<in> Rel (Tm Imod1) \<and> r1 \<noteq> r2 \<and> 
      \<exclamdown>(class (Tm Imod1) r1) = uncontainer (type (Tm Imod1) r2) \<and> \<exclamdown>(class (Tm Imod1) r2) = uncontainer (type (Tm Imod1) r1) \<and> 
      type (Tm Imod1) r1 \<notin> NonUniqueContainerType (Tm Imod1) \<and> type (Tm Imod1) r2 \<notin> NonUniqueContainerType (Tm Imod1)"
      using properties_rev_impl_opposite
      by blast
    have "Imod2 \<Turnstile> opposite r1 r2"
      using imod2_correct instance_model.validity_properties_satisfied opposite_property_both.hyps(2)
      by blast
    then have imod2_opposite: "\<And>o1 o2. o1 \<in> Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 \<Longrightarrow> edgeCount Imod2 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
      using property_satisfaction_opposite_rev
      by metis
    have "opposite r1 r2 \<in> Property (Tm Imod2)"
      using imod2_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed opposite_property_both.hyps(2)
      by blast
    then have imod2_opposite_props: "r1 \<in> Rel (Tm Imod2) \<and> r2 \<in> Rel (Tm Imod2) \<and> r1 \<noteq> r2 \<and> 
      \<exclamdown>(class (Tm Imod2) r1) = uncontainer (type (Tm Imod2) r2) \<and> \<exclamdown>(class (Tm Imod2) r2) = uncontainer (type (Tm Imod2) r1) \<and> 
      type (Tm Imod2) r1 \<notin> NonUniqueContainerType (Tm Imod2) \<and> type (Tm Imod2) r2 \<notin> NonUniqueContainerType (Tm Imod2)"
      using properties_rev_impl_opposite
      by blast
    have r1_in_field_imod1: "r1 \<in> Field (Tm Imod1)"
      using imod1_opposite_props
      unfolding Rel_def
      by blast
    then have r1_in_combination: "r1 \<in> Field (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def tmod_combine_def)
    have r1_in_field_imod2: "r1 \<in> Field (Tm Imod2)"
      using imod2_opposite_props
      unfolding Rel_def
      by blast
    have r2_in_field_imod1: "r2 \<in> Field (Tm Imod1)"
      using imod1_opposite_props
      unfolding Rel_def
      by blast
    then have r2_in_combination: "r2 \<in> Field (Tm (imod_combine Imod1 Imod2))"
      by (simp add: imod_combine_def tmod_combine_def)
    have r2_in_field_imod2: "r2 \<in> Field (Tm Imod2)"
      using imod2_opposite_props
      unfolding Rel_def
      by blast
    show ?case
    proof (intro property_satisfaction.rule_property_opposite)
      fix o1 o2
      assume o1_present: "o1 \<in> Object (imod_combine Imod1 Imod2)"
      then have o1_in_object: "o1 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      assume o2_present: "o2 \<in> Object (imod_combine Imod1 Imod2)"
      then have o2_in_object: "o2 \<in> Object Imod1 \<union> Object Imod2"
        by (simp add: imod_combine_def)
      have r1_subtype_cases_imod1: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1) \<or> \<not>(o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1))"
        by simp
      have r2_subtype_cases_imod1: "o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2) \<or> \<not>(o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2))"
        by simp
      have r1_subtype_cases_imod2: "o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1) \<or> \<not>(o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1))"
        by simp
      have r2_subtype_cases_imod2: "o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2) \<or> \<not>(o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2))"
        by simp
      show "edgeCount (imod_combine Imod1 Imod2) o1 r1 o2 = edgeCount (imod_combine Imod1 Imod2) o2 r2 o1"
        using r1_subtype_cases_imod1 r2_subtype_cases_imod1 r1_subtype_cases_imod2 r2_subtype_cases_imod2
      proof (elim disjE)
        assume r1_present_imod1: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        assume r2_present_imod1: "o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod1 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod1 o2"
          by (simp add: imod_combine_def)
        assume r1_present_imod2: "o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
        assume r2_present_imod2: "o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod1 (o1, r1)"
          unfolding imod_combine_field_value_def
          by (simp add: property_field_values_wellformed r1_in_field_imod1 r1_present_imod1 r1_present_imod2)
        then have edge_count_r1_def: "edgeCount Imod1 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          using r1_present_imod1 r1_in_field_imod1
          by simp
        have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod1 (o2, r2)"
          unfolding imod_combine_field_value_def
          by (simp add: property_field_values_wellformed r2_in_field_imod1 r2_present_imod1 r2_present_imod2)
        then have edge_count_r2_def: "edgeCount Imod1 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          using r2_present_imod1 r2_in_field_imod1
          by simp
        have "edgeCount Imod1 o1 r1 o2 = edgeCount Imod1 o2 r2 o1"
          using imod1_opposite r1_present_imod1 r2_present_imod1
          by simp
        then show ?thesis
          using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5) o1_present o2_present r1_in_combination r2_in_combination subtype_combine_r1 subtype_combine_r2
          by metis
      next
        assume r1_present_imod1: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        assume r2_present_imod1: "o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod1 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod1 o2"
          by (simp add: imod_combine_def)
        assume r1_present_imod2: "o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
        assume r2_not_present_imod2: "\<not>(o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2))"
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod1 (o1, r1)"
          unfolding imod_combine_field_value_def
          by (simp add: property_field_values_wellformed r1_in_field_imod1 r1_present_imod1 r1_present_imod2)
        then have edge_count_r1_def: "edgeCount Imod1 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          using r1_present_imod1 r1_in_field_imod1
          by simp
        have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod1 (o2, r2)"
          unfolding imod_combine_field_value_def
        proof (induct "o2 \<in> Object Imod2")
          case True
          then have "FieldValue Imod2 (o2, r2) = unspecified"
            using imod2_correct instance_model.property_field_values_outside_domain r2_in_field_imod2 r2_not_present_imod2
            by metis
          then show ?case
            by (simp add: r2_in_field_imod1 r2_present_imod1)
        next
          case False
          then show ?case
            using r2_in_field_imod1 r2_present_imod1
            by simp
        qed
        then have edge_count_r2_def: "edgeCount Imod1 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          using r2_present_imod1 r2_in_field_imod1
          by simp
        have "edgeCount Imod1 o1 r1 o2 = edgeCount Imod1 o2 r2 o1"
          using imod1_opposite r1_present_imod1 r2_present_imod1
          by simp
        then show ?thesis
          using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5) o1_present o2_present r1_in_combination r2_in_combination subtype_combine_r1 subtype_combine_r2
          by metis
      next
        assume r1_present_imod1: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        assume r2_present_imod1: "o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod1 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod1 o2"
          by (simp add: imod_combine_def)
        assume r1_not_present_imod2: "\<not>(o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1))"
        assume r2_present_imod2: "o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod1 (o1, r1)"
          unfolding imod_combine_field_value_def
        proof (induct "o1 \<in> Object Imod2")
          case True
          then have "FieldValue Imod2 (o1, r1) = unspecified"
            using imod2_correct instance_model.property_field_values_outside_domain r1_in_field_imod2 r1_not_present_imod2
            by metis
          then show ?case
            by (simp add: r1_in_field_imod1 r1_present_imod1)
        next
          case False
          then show ?case
            using r1_in_field_imod1 r1_present_imod1
            by simp
        qed
        then have edge_count_r1_def: "edgeCount Imod1 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          using r1_present_imod1 r1_in_field_imod1
          by simp
        have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod1 (o2, r2)"
          unfolding imod_combine_field_value_def
          by (simp add: property_field_values_wellformed r2_in_field_imod1 r2_present_imod1 r2_present_imod2)
        then have edge_count_r2_def: "edgeCount Imod1 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          using r2_present_imod1 r2_in_field_imod1
          by simp
        have "edgeCount Imod1 o1 r1 o2 = edgeCount Imod1 o2 r2 o1"
          using imod1_opposite r1_present_imod1 r2_present_imod1
          by simp
        then show ?thesis
          using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5) o1_present o2_present r1_in_combination r2_in_combination subtype_combine_r1 subtype_combine_r2
          by metis
      next
        assume r1_present_imod1: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        assume r2_present_imod1: "o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod1 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod1 o2"
          by (simp add: imod_combine_def)
        assume r1_not_present_imod2: "\<not>(o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1))"
        assume r2_not_present_imod2: "\<not>(o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2))"
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod1 (o1, r1)"
          unfolding imod_combine_field_value_def
        proof (induct "o1 \<in> Object Imod2")
          case True
          then have "FieldValue Imod2 (o1, r1) = unspecified"
            using imod2_correct instance_model.property_field_values_outside_domain r1_in_field_imod2 r1_not_present_imod2
            by metis
          then show ?case
            by (simp add: r1_in_field_imod1 r1_present_imod1)
        next
          case False
          then show ?case
            using r1_in_field_imod1 r1_present_imod1
            by simp
        qed
        then have edge_count_r1_def: "edgeCount Imod1 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          using r1_present_imod1 r1_in_field_imod1
          by simp
        have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod1 (o2, r2)"
          unfolding imod_combine_field_value_def
        proof (induct "o2 \<in> Object Imod2")
          case True
          then have "FieldValue Imod2 (o2, r2) = unspecified"
            using imod2_correct instance_model.property_field_values_outside_domain r2_in_field_imod2 r2_not_present_imod2
            by metis
          then show ?case
            by (simp add: r2_in_field_imod1 r2_present_imod1)
        next
          case False
          then show ?case
            using r2_in_field_imod1 r2_present_imod1
            by simp
        qed
        then have edge_count_r2_def: "edgeCount Imod1 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          using r2_present_imod1 r2_in_field_imod1
          by simp
        have "edgeCount Imod1 o1 r1 o2 = edgeCount Imod1 o2 r2 o1"
          using imod1_opposite r1_present_imod1 r2_present_imod1
          by simp
        then show ?thesis
          using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5) o1_present o2_present r1_in_combination r2_in_combination subtype_combine_r1 subtype_combine_r2
          by metis
      next
        assume r1_present_imod1: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
        assume r2_not_present_imod1: "\<not>(o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2))"
        assume r1_present_imod2: "o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod2 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod2 o1"
          by (simp add: imod_combine_def)
        assume r2_present_imod2: "o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod2 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod2 o2"
          by (simp add: imod_combine_def)
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod2 tmod_combine_subtype_subset_tmod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod2 (o1, r1)"
          unfolding imod_combine_field_value_def
          by (simp add: property_field_values_wellformed r1_in_field_imod2 r1_present_imod1 r1_present_imod2)
        then have edge_count_r1_def: "edgeCount Imod2 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          by (simp add: r1_in_field_imod2 r1_present_imod2)
        have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod2 tmod_combine_subtype_subset_tmod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod2 (o2, r2)"
          unfolding imod_combine_field_value_def
        proof (induct "o2 \<in> Object Imod1")
          case True
          then have "FieldValue Imod1 (o2, r2) = unspecified"
            using imod1_correct instance_model.property_field_values_outside_domain r2_in_field_imod1 r2_not_present_imod1
            by metis
          then show ?case
            by (simp add: r2_in_field_imod2 r2_present_imod2)
        next
          case False
          then show ?case
            using r2_in_field_imod2 r2_present_imod2
            by simp
        qed
        then have edge_count_r2_def: "edgeCount Imod2 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          by (simp add: r2_in_field_imod2 r2_present_imod2)
        have "edgeCount Imod2 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
          using imod2_opposite r1_present_imod2 r2_present_imod2
          by simp
        then show ?thesis
          using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5) o1_present o2_present r1_in_combination r2_in_combination subtype_combine_r1 subtype_combine_r2
          by metis
      next
        assume r1_present_imod1: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        assume r2_not_present_imod1: "\<not>(o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2))"
        assume r1_present_imod2: "o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
        assume r2_not_present_imod2: "\<not>(o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2))"
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod1 (o1, r1)"
          unfolding imod_combine_field_value_def
          by (simp add: property_field_values_wellformed r1_in_field_imod1 r1_present_imod1 r1_present_imod2)
        then have edge_count_r1_imod1_def: "edgeCount Imod1 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          using r1_present_imod1 r1_in_field_imod1
          by simp
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod2 (o1, r1)"
          unfolding imod_combine_field_value_def
          by (simp add: property_field_values_wellformed r1_in_field_imod2 r1_present_imod1 r1_present_imod2)
        then have edge_count_r1_imod2_def: "edgeCount Imod2 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          using r1_present_imod2 r1_in_field_imod2
          by simp
        show ?thesis
        proof (induct "o2 \<in> Object Imod1")
          case True
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
            case True
            then show ?case
              using property_field_values_not_subtype_imod1 r2_in_field_imod1 r2_not_present_imod1 r2_not_present_imod2
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r1_imod1_def imod1_opposite imod_combine_def instance_model.select_convs(5) r2_not_present_imod1
              by metis
          qed
        next
          case False
          then have "o2 \<in> Object Imod2"
            using o2_in_object
            by blast
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
            case True
            then show ?case
              using False.hyps property_field_values_not_subtype_imod2 r2_in_field_imod2 r2_not_present_imod2
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r1_imod2_def imod2_opposite imod_combine_def instance_model.select_convs(5) r2_not_present_imod2
              by metis
          qed
        qed
      next
        assume r1_present_imod1: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        assume r2_not_present_imod1: "\<not>(o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2))"
        assume r1_not_present_imod2: "\<not>(o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1))"
        assume r2_present_imod2: "o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod2 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod2 o2"
          by (simp add: imod_combine_def)
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod1 (o1, r1)"
          unfolding imod_combine_field_value_def
        proof (induct "o1 \<in> Object Imod2")
          case True
          then have "FieldValue Imod2 (o1, r1) = unspecified"
            using imod2_correct instance_model.property_field_values_outside_domain r1_in_field_imod2 r1_not_present_imod2
            by metis
          then show ?case
            by (simp add: r1_in_field_imod1 r1_present_imod1)
        next
          case False
          then show ?case
            using r1_in_field_imod1 r1_present_imod1
            by simp
        qed
        then have edge_count_r1_def: "edgeCount Imod1 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          using r1_present_imod1 r1_in_field_imod1
          by simp
        have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod2 tmod_combine_subtype_subset_tmod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod2 (o2, r2)"
          unfolding imod_combine_field_value_def
        proof (induct "o2 \<in> Object Imod1")
          case True
          then have "FieldValue Imod1 (o2, r2) = unspecified"
            using imod1_correct instance_model.property_field_values_outside_domain r2_in_field_imod1 r2_not_present_imod1
            by metis
          then show ?case
            by (simp add: r2_in_field_imod2 r2_present_imod2)
        next
          case False
          then show ?case
            using r2_in_field_imod2 r2_present_imod2
            by simp
        qed
        then have edge_count_r2_def: "edgeCount Imod2 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          using r2_present_imod2 r2_in_field_imod2
          by simp
        have "edgeCount Imod1 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
          using validity_opposite_properties_satisfied opposite_property_both.hyps(1) opposite_property_both.hyps(2) r1_not_present_imod2 r1_present_imod1 r2_not_present_imod1 r2_present_imod2
          by blast
        then show ?thesis
          using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5) o1_present o2_present r1_in_combination r2_in_combination subtype_combine_r1 subtype_combine_r2
          by metis
      next
        assume r1_present_imod1: "o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod1 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod1 o1"
          by (simp add: imod_combine_def)
        assume r2_not_present_imod1: "\<not>(o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2))"
        assume r1_not_present_imod2: "\<not>(o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1))"
        assume r2_not_present_imod2: "\<not>(o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2))"
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod1 (o1, r1)"
          unfolding imod_combine_field_value_def
        proof (induct "o1 \<in> Object Imod2")
          case True
          then have "FieldValue Imod2 (o1, r1) = unspecified"
            using imod2_correct instance_model.property_field_values_outside_domain r1_in_field_imod2 r1_not_present_imod2
            by metis
          then show ?case
            by (simp add: r1_in_field_imod1 r1_present_imod1)
        next
          case False
          then show ?case
            using r1_in_field_imod1 r1_present_imod1
            by simp
        qed
        then have edge_count_r1_def: "edgeCount Imod1 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          using r1_present_imod1 r1_in_field_imod1
          by simp
        have edge_count_r2_imod1_def: "edgeCount Imod1 o2 r2 o1 = 0"
          unfolding edgeCount_def
          using r2_not_present_imod1
          by simp
        have edge_count_r2_imod2_def: "edgeCount Imod2 o2 r2 o1 = 0"
          unfolding edgeCount_def
          using r2_not_present_imod2
          by simp
        show ?thesis
        proof (induct "o2 \<in> Object Imod1")
          case True
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
            case True
            then show ?case
              using property_field_values_not_subtype_imod1 r2_in_field_imod1 r2_not_present_imod1 r2_not_present_imod2
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r1_def edge_count_r2_imod1_def imod1_opposite imod_combine_def instance_model.select_convs(5)
              by metis
          qed
        next
          case False
          then have "o2 \<in> Object Imod2"
            using o2_in_object
            by blast
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
            case True
            then show ?case
              using False.hyps property_field_values_not_subtype_imod2 r2_in_field_imod2 r2_not_present_imod2
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r1_def edge_count_r2_imod2_def imod_combine_def instance_model.select_convs(5) opposite_property_both.hyps(1) 
              using opposite_property_both.hyps(2) r1_not_present_imod2 r2_not_present_imod1 validity_opposite_properties_satisfied
              by metis
          qed
        qed
      next
        assume r1_not_present_imod1: "\<not>(o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1))"
        assume r2_present_imod1: "o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
        assume r1_present_imod2: "o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod2 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod2 o1"
          by (simp add: imod_combine_def)
        assume r2_present_imod2: "o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod2 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod2 o2"
          by (simp add: imod_combine_def)
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod2 tmod_combine_subtype_subset_tmod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod2 (o1, r1)"
          unfolding imod_combine_field_value_def
        proof (induct "o1 \<in> Object Imod1")
          case True
          then have "FieldValue Imod1 (o1, r1) = unspecified"
            using imod1_correct instance_model.property_field_values_outside_domain r1_in_field_imod1 r1_not_present_imod1
            by metis
          then show ?case
            by (simp add: r1_in_field_imod2 r1_present_imod2)
        next
          case False
          then show ?case
            using r1_in_field_imod2 r1_present_imod2
            by simp
        qed
        then have edge_count_r1_def: "edgeCount Imod2 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          by (simp add: r1_in_field_imod2 r1_present_imod2)
        have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod2 tmod_combine_subtype_subset_tmod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod2 (o2, r2)"
          unfolding imod_combine_field_value_def
          by (simp add: property_field_values_wellformed r2_in_field_imod2 r2_present_imod1 r2_present_imod2)
        then have edge_count_r2_def: "edgeCount Imod2 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          by (simp add: r2_in_field_imod2 r2_present_imod2)
        have "edgeCount Imod2 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
          using imod2_opposite r1_present_imod2 r2_present_imod2
          by simp
        then show ?thesis
          using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5) o1_present o2_present r1_in_combination r2_in_combination subtype_combine_r1 subtype_combine_r2
          by metis
      next
        assume r1_not_present_imod1: "\<not>(o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1))"
        assume r2_present_imod1: "o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod1 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod1 o2"
          by (simp add: imod_combine_def)
        assume r1_present_imod2: "o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod2 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod2 o1"
          by (simp add: imod_combine_def)
        assume r2_not_present_imod2: "\<not>(o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2))"
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod2 tmod_combine_subtype_subset_tmod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod2 (o1, r1)"
          unfolding imod_combine_field_value_def
        proof (induct "o1 \<in> Object Imod1")
          case True
          then have "FieldValue Imod1 (o1, r1) = unspecified"
            using imod1_correct instance_model.property_field_values_outside_domain r1_in_field_imod1 r1_not_present_imod1
            by metis
          then show ?case
            by (simp add: r1_in_field_imod2 r1_present_imod2)
        next
          case False
          then show ?case
            using r1_in_field_imod2 r1_present_imod2
            by simp
        qed
        then have edge_count_r1_def: "edgeCount Imod2 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          by (simp add: r1_in_field_imod2 r1_present_imod2)
        have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod1 (o2, r2)"
          unfolding imod_combine_field_value_def
        proof (induct "o2 \<in> Object Imod2")
          case True
          then have "FieldValue Imod2 (o2, r2) = unspecified"
            using imod2_correct instance_model.property_field_values_outside_domain r2_in_field_imod2 r2_not_present_imod2
            by metis
          then show ?case
            by (simp add: r2_in_field_imod1 r2_present_imod1)
        next
          case False
          then show ?case
            using r2_in_field_imod1 r2_present_imod1
            by simp
        qed
        then have edge_count_r2_def: "edgeCount Imod1 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          by (simp add: r2_in_field_imod1 r2_present_imod1)
        have "edgeCount Imod2 o1 r1 o2 = edgeCount Imod1 o2 r2 o1"
          using validity_opposite_properties_satisfied opposite_property_both.hyps(1) opposite_property_both.hyps(2) r1_not_present_imod1 r1_present_imod2 r2_not_present_imod2 r2_present_imod1
          using imod1_correct imod2_correct instance_model.validity_type_model_consistent type_model.consistency_opposite_sym
          by metis
        then show ?thesis
          using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5) o1_present o2_present r1_in_combination r2_in_combination subtype_combine_r1 subtype_combine_r2
          by metis
      next
        assume r1_not_present_imod1: "\<not>(o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1))"
        assume r2_present_imod1: "o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod1 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod1 o2"
          by (simp add: imod_combine_def)
        assume r1_not_present_imod2: "\<not>(o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1))"
        assume r2_present_imod2: "o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod1 (o2, r2)"
          unfolding imod_combine_field_value_def
          by (simp add: property_field_values_wellformed r2_in_field_imod1 r2_present_imod1 r2_present_imod2)
        then have edge_count_r2_imod1_def: "edgeCount Imod1 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          using r2_present_imod1 r2_in_field_imod1
          by simp
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod2 (o2, r2)"
          unfolding imod_combine_field_value_def
          by (simp add: property_field_values_wellformed r2_in_field_imod2 r2_present_imod1 r2_present_imod2)
        then have edge_count_r2_imod2_def: "edgeCount Imod2 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          using r2_present_imod2 r2_in_field_imod2
          by simp
        show ?thesis
        proof (induct "o1 \<in> Object Imod1")
          case True
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using property_field_values_not_subtype_imod1 r1_in_field_imod1 r1_not_present_imod1 r1_not_present_imod2
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r2_imod1_def imod1_opposite imod_combine_def instance_model.select_convs(5) r1_not_present_imod1
              by metis
          qed
        next
          case False
          then have "o1 \<in> Object Imod2"
            using o1_in_object
            by blast
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using False.hyps property_field_values_not_subtype_imod2 r1_in_field_imod2 r1_not_present_imod2
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r2_imod2_def imod2_opposite imod_combine_def instance_model.select_convs(5) r1_not_present_imod2
              by metis
          qed
        qed
      next
        assume r1_not_present_imod1: "\<not>(o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1))"
        assume r2_present_imod1: "o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod1 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod1 o2"
          by (simp add: imod_combine_def)
        assume r1_not_present_imod2: "\<not>(o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1))"
        assume r2_not_present_imod2: "\<not>(o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2))"
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod1 tmod_combine_subtype_subset_tmod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod1 (o2, r2)"
          unfolding imod_combine_field_value_def
        proof (induct "o2 \<in> Object Imod2")
          case True
          then have "FieldValue Imod2 (o2, r2) = unspecified"
            using imod2_correct instance_model.property_field_values_outside_domain r2_in_field_imod2 r2_not_present_imod2
            by metis
          then show ?case
            by (simp add: r2_in_field_imod1 r2_present_imod1)
        next
          case False
          then show ?case
            using r2_in_field_imod1 r2_present_imod1
            by simp
        qed
        then have edge_count_r2_imod1_def: "edgeCount Imod1 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          using r2_present_imod1 r2_in_field_imod1
          by simp
        have edge_count_r1_imod2_def: "edgeCount Imod2 o1 r1 o2 = 0"
          unfolding edgeCount_def
          using r1_not_present_imod2
          by simp
        show ?thesis
        proof (induct "o1 \<in> Object Imod1")
          case True
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using property_field_values_not_subtype_imod1 r1_in_field_imod1 r1_not_present_imod1 r1_not_present_imod2
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r2_imod1_def imod1_opposite imod_combine_def instance_model.select_convs(5) r1_not_present_imod1
              by metis
          qed
        next
          case False
          then have o1_in_imod2: "o1 \<in> Object Imod2"
            using o1_in_object
            by blast
          then have "\<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
            using r1_not_present_imod2
            by blast
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using False.hyps property_field_values_not_subtype_imod2 r1_in_field_imod2 o1_in_imod2
              by blast
          next
            case False
            then have edge_count_r1_def: "edgeCount (imod_combine Imod1 Imod2) o1 r1 o2 = 0"
              unfolding edgeCount_def
              by simp
            then have "edgeCount (imod_combine Imod1 Imod2) o2 r2 o1 = edgeCount Imod1 o2 r2 o1"
              using edgeCount_def edge_count_r2_imod1_def imod_combine_def instance_model.select_convs(5) o2_present r2_in_combination subtype_combine_r1
              by metis
            then show ?case
              using edge_count_r1_def edge_count_r1_imod2_def imod1_correct imod2_correct instance_model.validity_type_model_consistent o1_in_imod2 opposite_property_both.hyps(1)
              using opposite_property_both.hyps(2) r1_not_present_imod1 r2_not_present_imod2 r2_present_imod1 type_model.consistency_opposite_sym validity_opposite_properties_satisfied
              by metis
          qed
        qed
      next
        assume r1_not_present_imod1: "\<not>(o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1))"
        assume r2_not_present_imod1: "\<not>(o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2))"
        assume r1_present_imod2: "o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod2 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod2 o1"
          by (simp add: imod_combine_def)
        assume r2_present_imod2: "o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod2 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod2 o2"
          by (simp add: imod_combine_def)
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod2 tmod_combine_subtype_subset_tmod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod2 (o1, r1)"
          unfolding imod_combine_field_value_def
        proof (induct "o1 \<in> Object Imod1")
          case True
          then have "FieldValue Imod1 (o1, r1) = unspecified"
            using imod1_correct instance_model.property_field_values_outside_domain r1_in_field_imod1 r1_not_present_imod1
            by metis
          then show ?case
            by (simp add: r1_in_field_imod2 r1_present_imod2)
        next
          case False
          then show ?case
            using r1_in_field_imod2 r1_present_imod2
            by simp
        qed
        then have edge_count_r1_def: "edgeCount Imod2 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          by (simp add: r1_in_field_imod2 r1_present_imod2)
        have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod2 tmod_combine_subtype_subset_tmod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod2 (o2, r2)"
          unfolding imod_combine_field_value_def
        proof (induct "o2 \<in> Object Imod1")
          case True
          then have "FieldValue Imod1 (o2, r2) = unspecified"
            using imod1_correct instance_model.property_field_values_outside_domain r2_in_field_imod1 r2_not_present_imod1
            by metis
          then show ?case
            by (simp add: r2_in_field_imod2 r2_present_imod2)
        next
          case False
          then show ?case
            using r2_in_field_imod2 r2_present_imod2
            by simp
        qed
        then have edge_count_r2_def: "edgeCount Imod2 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          by (simp add: r2_in_field_imod2 r2_present_imod2)
        have "edgeCount Imod2 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
          using imod2_opposite r1_present_imod2 r2_present_imod2
          by simp
        then show ?thesis
          using edgeCount_def edge_count_r1_def edge_count_r2_def imod_combine_def instance_model.select_convs(5) o1_present o2_present r1_in_combination r2_in_combination subtype_combine_r1 subtype_combine_r2
          by metis
      next
        assume r1_not_present_imod1: "\<not>(o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1))"
        assume r2_not_present_imod1: "\<not>(o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2))"
        assume r1_present_imod2: "o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
        then have "imod_combine_object_class Imod1 Imod2 o1 = ObjectClass Imod2 o1"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o1_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o1 = ObjectClass Imod2 o1"
          by (simp add: imod_combine_def)
        assume r2_not_present_imod2: "\<not>(o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2))"
        have subtype_combine_r1: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)"
          using class_def imod_combine_def instance_model.select_convs(1) o1_object_class_def r1_present_imod2 tmod_combine_subtype_subset_tmod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o1, r1) = FieldValue Imod2 (o1, r1)"
          unfolding imod_combine_field_value_def
        proof (induct "o1 \<in> Object Imod1")
          case True
          then have "FieldValue Imod1 (o1, r1) = unspecified"
            using imod1_correct instance_model.property_field_values_outside_domain r1_in_field_imod1 r1_not_present_imod1
            by metis
          then show ?case
            by (simp add: r1_in_field_imod2 r1_present_imod2)
        next
          case False
          then show ?case
            using r1_in_field_imod2 r1_present_imod2
            by simp
        qed
        then have edge_count_r1_def: "edgeCount Imod2 o1 r1 o2 = length (filter (objValueCheck o2) (contained_list (imod_combine_field_value Imod1 Imod2 (o1, r1))))"
          unfolding edgeCount_def
          using r1_present_imod2 r1_in_field_imod2
          by simp
        have edge_count_r2_imod1_def: "edgeCount Imod1 o2 r2 o1 = 0"
          unfolding edgeCount_def
          using r2_not_present_imod1
          by simp
        have edge_count_r2_imod2_def: "edgeCount Imod2 o2 r2 o1 = 0"
          unfolding edgeCount_def
          using r2_not_present_imod2
          by simp
        show ?thesis
        proof (induct "o2 \<in> Object Imod1")
          case True
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
            case True
            then show ?case
              using property_field_values_not_subtype_imod1 r2_in_field_imod1 r2_not_present_imod1 r2_not_present_imod2
              by blast
          next
            case False
            then have edge_count_r2_def: "edgeCount (imod_combine Imod1 Imod2) o2 r2 o1 = 0"
              unfolding edgeCount_def
              by simp
            then have "edgeCount (imod_combine Imod1 Imod2) o1 r1 o2 = edgeCount Imod2 o1 r1 o2"
              using edgeCount_def edge_count_r1_def imod_combine_def instance_model.select_convs(5) o1_present r1_in_combination subtype_combine_r1
              by metis
            then show ?case
              using True.hyps edge_count_r2_def edge_count_r2_imod1_def imod1_correct imod2_correct instance_model.validity_type_model_consistent opposite_property_both.hyps(1) 
              using opposite_property_both.hyps(2) r1_not_present_imod1 r1_present_imod2 r2_not_present_imod2 type_model.consistency_opposite_sym validity_opposite_properties_satisfied
              by metis
          qed
        next
          case False
          then have "o2 \<in> Object Imod2"
            using o2_in_object
            by blast
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
            case True
            then show ?case
              using False.hyps property_field_values_not_subtype_imod2 r2_in_field_imod2 r2_not_present_imod2
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r1_def edge_count_r2_imod2_def imod2_opposite imod_combine_def instance_model.select_convs(5)
              by metis
          qed
        qed
      next
        assume r1_not_present_imod1: "\<not>(o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1))"
        assume r2_not_present_imod1: "\<not>(o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2))"
        assume r1_not_present_imod2: "\<not>(o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1))"
        assume r2_present_imod2: "o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2)"
        then have "imod_combine_object_class Imod1 Imod2 o2 = ObjectClass Imod2 o2"
          unfolding imod_combine_object_class_def
          by (simp add: structure_object_class_wellformed)
        then have o2_object_class_def: "ObjectClass (imod_combine Imod1 Imod2) o2 = ObjectClass Imod2 o2"
          by (simp add: imod_combine_def)
        have subtype_combine_r2: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)"
          using class_def imod_combine_def instance_model.select_convs(1) o2_object_class_def r2_present_imod2 tmod_combine_subtype_subset_tmod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (o2, r2) = FieldValue Imod2 (o2, r2)"
          unfolding imod_combine_field_value_def
        proof (induct "o2 \<in> Object Imod1")
          case True
          then have "FieldValue Imod1 (o2, r2) = unspecified"
            using imod1_correct instance_model.property_field_values_outside_domain r2_in_field_imod1 r2_not_present_imod1
            by metis
          then show ?case
            by (simp add: r2_in_field_imod2 r2_present_imod2)
        next
          case False
          then show ?case
            using r2_in_field_imod2 r2_present_imod2
            by simp
        qed
        then have edge_count_r2_imod1_def: "edgeCount Imod2 o2 r2 o1 = length (filter (objValueCheck o1) (contained_list (imod_combine_field_value Imod1 Imod2 (o2, r2))))"
          unfolding edgeCount_def
          using r2_present_imod2 r2_in_field_imod2
          by simp
        have edge_count_r1_imod2_def: "edgeCount Imod2 o1 r1 o2 = 0"
          unfolding edgeCount_def
          using r1_not_present_imod2
          by simp
        show ?thesis
        proof (induct "o1 \<in> Object Imod1")
          case True
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using property_field_values_not_subtype_imod1 r1_in_field_imod1 r1_not_present_imod1 r1_not_present_imod2
              by blast
          next
            case False
            then have edge_count_r1_def: "edgeCount (imod_combine Imod1 Imod2) o1 r1 o2 = 0"
              unfolding edgeCount_def
              by simp
            then have "edgeCount (imod_combine Imod1 Imod2) o2 r2 o1 = edgeCount Imod2 o2 r2 o1"
              using edgeCount_def edge_count_r2_imod1_def imod_combine_def instance_model.select_convs(5) o2_present r2_in_combination subtype_combine_r2
              by metis
            then show ?case
              using True.hyps edgeCount_def edge_count_r1_def edge_count_r1_imod2_def imod2_opposite opposite_property_both.hyps(1) opposite_property_both.hyps(2) r1_not_present_imod1 r2_not_present_imod1 validity_opposite_properties_satisfied
              by metis
          qed
        next
          case False
          then have o1_in_imod2: "o1 \<in> Object Imod2"
            using o1_in_object
            by blast
          then have "\<not>\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1)"
            using r1_not_present_imod2
            by blast
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
            case True
            then show ?case
              using False.hyps property_field_values_not_subtype_imod2 r1_in_field_imod2 o1_in_imod2
              by blast
          next
            case False
            then show ?case
              using edgeCount_def edge_count_r2_imod1_def imod2_opposite imod_combine_def instance_model.select_convs(5) o1_in_imod2
              by metis
          qed
        qed
      next
        assume r1_not_present_imod1: "\<not>(o1 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r1))"
        assume r2_not_present_imod1: "\<not>(o2 \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 o2) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) r2))"
        assume r1_not_present_imod2: "\<not>(o1 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r1))"
        assume r2_not_present_imod2: "\<not>(o2 \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 o2) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) r2))"
        show ?thesis
        proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o1) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r1)")
          case True
          then show ?case
            using Un_iff o1_in_object property_field_values_not_subtype_imod1 property_field_values_not_subtype_imod2 r1_in_field_imod1 r1_in_field_imod2 r1_not_present_imod1 r1_not_present_imod2
            by metis
        next
          case False
          then show ?case
          proof (induct "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) o2) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) r2)")
            case True
            then show ?case
              using Un_iff o2_in_object property_field_values_not_subtype_imod1 property_field_values_not_subtype_imod2 r2_in_field_imod1 r2_in_field_imod2 r2_not_present_imod1 r2_not_present_imod2
              by metis
          next
            case False
            then show ?case
              unfolding edgeCount_def
              by simp
          qed
        qed
      qed
    qed
  next
    case (readonly_property_tmod1 f)
    then show ?case
      using property_satisfaction.rule_property_readonly
      by blast
  next
    case (readonly_property_tmod2 f)
    then show ?case
      using property_satisfaction.rule_property_readonly
      by blast
  next
    case (readonly_property_both f)
    then show ?case
      using property_satisfaction.rule_property_readonly
      by blast
  qed
next
  have structure_consttype_wellformed_type: "\<And>c. c \<in> Constant (Tm Imod1) \<inter> Constant (Tm Imod2) \<Longrightarrow> ConstType (Tm Imod1) c = ConstType (Tm Imod2) c"
  proof-
    fix c
    assume f_in_both: "c \<in> Constant (Tm Imod1) \<inter> Constant (Tm Imod2)"
    then have "c \<in> Constant (tmod_combine (Tm Imod1) (Tm Imod2))"
      unfolding tmod_combine_def
      by simp
    then have "ConstType (tmod_combine (Tm Imod1) (Tm Imod2)) c \<in> Type (tmod_combine (Tm Imod1) (Tm Imod2))"
      using validity_type_model_consistent type_model.structure_consttype_wellformed
      by blast
    then have fst_in_type: "tmod_combine_const_type (Tm Imod1) (Tm Imod2) c \<in> Type (tmod_combine (Tm Imod1) (Tm Imod2))"
      by (simp add: tmod_combine_def)
    then show "ConstType (Tm Imod1) c = ConstType (Tm Imod2) c"
    proof (induct "ConstType (Tm Imod1) c = ConstType (Tm Imod2) c")
      case True
      then show ?case
        by simp
    next
      case False
      then have "tmod_combine_const_type (Tm Imod1) (Tm Imod2) c = TypeDef.invalid"
        unfolding tmod_combine_const_type_def
        using f_in_both 
        by simp
      then have "tmod_combine_const_type (Tm Imod1) (Tm Imod2) c \<notin> Type (tmod_combine (Tm Imod1) (Tm Imod2))"
        by simp
      then show ?case
        using fst_in_type
        by simp
    qed
  qed
  fix c
  assume "c \<in> Constant (Tm (imod_combine Imod1 Imod2))"
  then have "c \<in> Constant (Tm Imod1) \<union> Constant (Tm Imod2)"
    by (simp add: imod_combine_def tmod_combine_def)
  then have "c \<in> Constant (Tm Imod1) \<inter> Constant (Tm Imod2) \<or> c \<in> Constant (Tm Imod1) - Constant (Tm Imod2) \<or> c \<in> Constant (Tm Imod2) - Constant (Tm Imod1)"
    by blast
  then have "imod_combine_default_value Imod1 Imod2 c :[imod_combine Imod1 Imod2] tmod_combine_const_type (Tm Imod1) (Tm Imod2) c"
  proof (elim disjE)
    assume c_in_both: "c \<in> Constant (Tm Imod1) \<inter> Constant (Tm Imod2)"
    then have combine_value_def: "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod1 c"
      unfolding imod_combine_default_value_def
      by (simp add: structure_default_values_wellformed)
    then have value_typed_imod1: "imod_combine_default_value Imod1 Imod2 c :[Imod1] ConstType (Tm Imod1) c"
      using IntD1 c_in_both imod1_correct instance_model.validity_default_value_types
      by metis
    then have value_typed_combination: "imod_combine_default_value Imod1 Imod2 c :[imod_combine Imod1 Imod2] ConstType (Tm Imod1) c"
      by (simp add: Valid_def imod_combine_valid_rel_imod1 structure_object_class_wellformed)
    then show ?thesis
      unfolding tmod_combine_const_type_def
      using c_in_both structure_consttype_wellformed_type
      by simp
  next
    assume c_in_tmod1: "c \<in> Constant (Tm Imod1) - Constant (Tm Imod2)"
    then have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod1 c"
      by (simp add: imod_combine_default_value_def)
    then have "imod_combine_default_value Imod1 Imod2 c :[Imod1] ConstType (Tm Imod1) c"
      using c_in_tmod1 imod1_correct instance_model.validity_default_value_types
      by fastforce
    then have combine_def: "imod_combine_default_value Imod1 Imod2 c :[imod_combine Imod1 Imod2] ConstType (Tm Imod1) c"
      by (simp add: Valid_def imod_combine_valid_rel_imod1 structure_object_class_wellformed)
    have "tmod_combine_const_type (Tm Imod1) (Tm Imod2) c = ConstType (Tm Imod1) c"
      unfolding tmod_combine_const_type_def
      using c_in_tmod1
      by simp
    then show ?thesis
      using combine_def
      by metis
  next
    assume c_in_tmod2: "c \<in> Constant (Tm Imod2) - Constant (Tm Imod1)"
    then have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod2 c"
      by (simp add: imod_combine_default_value_def)
    then have "imod_combine_default_value Imod1 Imod2 c :[Imod2] ConstType (Tm Imod2) c"
      using c_in_tmod2 imod2_correct instance_model.validity_default_value_types
      by fastforce
    then have combine_def: "imod_combine_default_value Imod1 Imod2 c :[imod_combine Imod1 Imod2] ConstType (Tm Imod2) c"
      by (simp add: Valid_def imod_combine_valid_rel_imod2 structure_object_class_wellformed)
    have "tmod_combine_const_type (Tm Imod1) (Tm Imod2) c = ConstType (Tm Imod2) c"
      unfolding tmod_combine_const_type_def
      using c_in_tmod2
      by simp
    then show ?thesis
      using combine_def
      by metis
  qed
  then have "imod_combine_default_value Imod1 Imod2 c :[imod_combine Imod1 Imod2] ConstType (tmod_combine (Tm Imod1) (Tm Imod2)) c"
    using tmod_combine_def type_model.select_convs(10)
    by metis
  then show "DefaultValue (imod_combine Imod1 Imod2) c :[imod_combine Imod1 Imod2] ConstType (Tm (imod_combine Imod1 Imod2)) c"
    by (simp add: imod_combine_def)
next
  have "type_model (tmod_combine (Tm Imod1) (Tm Imod2))"
    by (fact validity_type_model_consistent)
  then show "type_model (Tm (imod_combine Imod1 Imod2))"
    by (simp add: imod_combine_def)
qed

lemma imod_combine_merge_correct[intro]:
  assumes imod1_correct: "instance_model Imod1"
  assumes imod2_correct: "instance_model Imod2"
  assumes combine_fields_distinct: "Field (Tm Imod1) \<inter> Field (Tm Imod2) = {}"
  assumes combine_constants_distinct: "Constant (Tm Imod1) \<inter> Constant (Tm Imod2) = {}"
  assumes structure_object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes structure_object_id_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectId Imod1 ob = ObjectId Imod2 ob"
  assumes property_object_id_uniqueness: "\<And>o1 o2. o1 \<in> Object Imod1 - Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 - Object Imod1 \<Longrightarrow> 
    ObjectId Imod1 o1 = ObjectId Imod2 o2 \<Longrightarrow> o1 = o2"
  assumes property_field_values_not_field_imod1: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes property_field_values_not_field_imod2: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes property_field_values_subtype_imod1: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow>
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes property_field_values_subtype_imod2: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow>
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes validity_containment_properties_satisfied: "\<And>r ob. containment r \<in> Prop (Tm Imod1) \<union> Prop (Tm Imod2) \<Longrightarrow> 
    ob \<in> Object Imod1 \<union> Object Imod2 \<Longrightarrow> card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
  assumes validity_containments_relation: "irrefl ((object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+)"
  assumes validity_type_model_consistent: "type_model (tmod_combine (Tm Imod1) (Tm Imod2))"
  shows "instance_model (imod_combine Imod1 Imod2)"
proof (intro imod_combine_correct)
  fix c
  assume c_in_imod1: "c \<in> Constant (Tm Imod1)"
  assume c_in_imod2: "c \<in> Constant (Tm Imod2)"
  then show "DefaultValue Imod1 c = DefaultValue Imod2 c"
    using c_in_imod1 c_in_imod2 combine_constants_distinct
    by blast
next
  fix ob f
  assume "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2)"
  then show "FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)"
    using combine_fields_distinct
    by blast
next
  fix ob f
  assume ob_in_imod1: "ob \<in> Object Imod1"
  assume f_in_tmod2: "f \<in> Field (Tm Imod2) - Field (Tm Imod1)"
  assume subtype: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  show "ob \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
    using ob_in_imod1 f_in_tmod2 subtype property_field_values_not_field_imod1
    by blast
next
  fix ob f
  assume ob_in_imod2: "ob \<in> Object Imod2"
  assume f_in_tmod1: "f \<in> Field (Tm Imod1) - Field (Tm Imod2)"
  assume subtype: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  show "ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
    using ob_in_imod2 f_in_tmod1 subtype property_field_values_not_field_imod2
    by blast
next
  fix ob f
  assume ob_in_imod1: "ob \<in> Object Imod1"
  assume f_in_tmod1: "f \<in> Field (Tm Imod1)"
  assume not_subtype_imod1: "\<not>\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assume subtype: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  show "ob \<in> Object Imod2 \<and> f \<in> type_model.Field (Tm Imod2) \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
    using f_in_tmod1 not_subtype_imod1 ob_in_imod1 subtype property_field_values_subtype_imod1
    by blast
next
  fix ob f
  assume ob_in_imod2: "ob \<in> Object Imod2"
  assume f_in_tmod2: "f \<in> Field (Tm Imod2)"
  assume not_subtype_imod2: "\<not>\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assume subtype: "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  show "ob \<in> Object Imod1 \<and> f \<in> type_model.Field (Tm Imod1) \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
    using f_in_tmod2 not_subtype_imod2 ob_in_imod2 subtype property_field_values_subtype_imod2
    by blast
next
  fix ob f
  assume f_in_imod1: "f \<in> Field (Tm Imod1)"
  assume f_in_imod2: "f \<in> Field (Tm Imod2)"
  show "Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<and>
    \<^bold>(length (contained_list (FieldValue Imod1 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
    using f_in_imod1 f_in_imod2 combine_fields_distinct
    by blast
next
  fix ob f
  assume f_in_imod1: "f \<in> Field (Tm Imod1)"
  assume f_in_imod2: "f \<in> Field (Tm Imod2)"
  show "Multiplicity.lower (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f)) \<le> \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<and>
    \<^bold>(length (contained_list (FieldValue Imod2 (ob, f)))) \<le> Multiplicity.upper (snd (FieldSig (Tm Imod1) f) \<sqinter> snd (FieldSig (Tm Imod2) f))"
    using f_in_imod1 f_in_imod2 combine_fields_distinct
    by blast
next
  fix c A o1 o2 a
  assume "identity c A \<in> Prop (Tm Imod1)"
  then have "identity c A \<in> Property (Tm Imod1)"
    by (simp add: imod1_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed)
  then have "A \<subseteq> Type_Model.fields (Tm Imod1) c"
    by (simp add: properties_rev_impl_identity)
  then have subset_field_imod1: "A \<subseteq> Field (Tm Imod1)"
    unfolding Type_Model.fields_def
    by blast
  assume "identity c A \<in> Prop (Tm Imod2)"
  then have "identity c A \<in> Property (Tm Imod2)"
    by (simp add: imod2_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed)
  then have "A \<subseteq> Type_Model.fields (Tm Imod2) c"
    by (simp add: properties_rev_impl_identity)
  then have subset_field_imod2: "A \<subseteq> Field (Tm Imod2)"
    unfolding Type_Model.fields_def
    by blast
  have A_empty: "A = {}"
    using subset_field_imod1 subset_field_imod2 combine_fields_distinct
    by blast
  assume "o1 \<in> Object Imod1 - Object Imod2"
  assume "o2 \<in> Object Imod2 - Object Imod1"
  assume "a \<in> A"
  then show "o1 = o2"
    using A_empty
    by blast
next
  fix r1 r2 o1 o2
  assume "opposite r1 r2 \<in> Prop (Tm Imod1)"
  then have "opposite r1 r2 \<in> Property (Tm Imod1)"
    by (simp add: imod1_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed)
  then have r1_in_imod1: "r1 \<in> Rel (Tm Imod1)"
    using properties_rev_impl_opposite
    by blast
  assume "opposite r1 r2 \<in> Prop (Tm Imod2)"
  then have "opposite r1 r2 \<in> Property (Tm Imod2)"
    by (simp add: imod2_correct instance_model.validity_type_model_consistent type_model.structure_properties_wellfomed)
  then have r1_in_imod2: "r1 \<in> Rel (Tm Imod2)"
    using properties_rev_impl_opposite
    by blast
  show "edgeCount Imod1 o1 r1 o2 = edgeCount Imod2 o2 r2 o1"
    using Diff_iff Diff_triv Type_Model.Rel_def combine_fields_distinct r1_in_imod1 r1_in_imod2
    by metis
next
  show "\<And>r ob. containment r \<in> Prop (Tm Imod1) \<union> Prop (Tm Imod2) \<Longrightarrow> 
    ob \<in> Object Imod1 \<union> Object Imod2 \<Longrightarrow> card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
    by (fact validity_containment_properties_satisfied)
qed (simp_all add: assms)

lemma imod_combine_merge_no_containment_imod1_correct[intro]:
  assumes imod1_correct: "instance_model Imod1"
  assumes imod2_correct: "instance_model Imod2"
  assumes combine_fields_distinct: "Field (Tm Imod1) \<inter> Field (Tm Imod2) = {}"
  assumes combine_constants_distinct: "Constant (Tm Imod1) \<inter> Constant (Tm Imod2) = {}"
  assumes combine_no_containment: "\<And>r. containment r \<notin> Prop (Tm Imod1)"
  assumes structure_object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes structure_object_id_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectId Imod1 ob = ObjectId Imod2 ob"
  assumes property_object_id_uniqueness: "\<And>o1 o2. o1 \<in> Object Imod1 - Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 - Object Imod1 \<Longrightarrow> 
    ObjectId Imod1 o1 = ObjectId Imod2 o2 \<Longrightarrow> o1 = o2"
  assumes property_field_values_not_field_imod1: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes property_field_values_not_field_imod2: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes property_field_values_subtype_imod1: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow>
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes property_field_values_subtype_imod2: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow>
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes validity_type_model_consistent: "type_model (tmod_combine (Tm Imod1) (Tm Imod2))"
  shows "instance_model (imod_combine Imod1 Imod2)"
proof (intro imod_combine_merge_correct)
  show "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
    by (fact local.property_field_values_not_field_imod2)
next
  fix ob
  assume ob_in_imods: "ob \<in> Object Imod1 \<union> Object Imod2"
  then show "card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
    by (intro imod_combine_containment_satisfaction_imod2) (simp_all add: assms)
next
  show "irrefl ((object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+)"
    by (intro imod_combine_containment_relation_satisfaction_imod2) (simp_all add: assms)
qed (simp_all add: assms)

lemma imod_combine_merge_no_containment_imod2_correct[intro]:
  assumes imod1_correct: "instance_model Imod1"
  assumes imod2_correct: "instance_model Imod2"
  assumes combine_fields_distinct: "Field (Tm Imod1) \<inter> Field (Tm Imod2) = {}"
  assumes combine_constants_distinct: "Constant (Tm Imod1) \<inter> Constant (Tm Imod2) = {}"
  assumes combine_no_containment: "\<And>r. containment r \<notin> Prop (Tm Imod2)"
  assumes structure_object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes structure_object_id_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectId Imod1 ob = ObjectId Imod2 ob"
  assumes property_object_id_uniqueness: "\<And>o1 o2. o1 \<in> Object Imod1 - Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 - Object Imod1 \<Longrightarrow> 
    ObjectId Imod1 o1 = ObjectId Imod2 o2 \<Longrightarrow> o1 = o2"
  assumes property_field_values_not_field_imod1: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes property_field_values_not_field_imod2: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes property_field_values_subtype_imod1: "\<And>ob f. ob \<in> Object Imod1 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow>
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
  assumes property_field_values_subtype_imod2: "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod2) \<Longrightarrow>
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
  assumes validity_type_model_consistent: "type_model (tmod_combine (Tm Imod1) (Tm Imod2))"
  shows "instance_model (imod_combine Imod1 Imod2)"
proof (intro imod_combine_merge_correct)
  show "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
    by (fact local.property_field_values_not_field_imod2)
next
  fix ob
  assume ob_in_imods: "ob \<in> Object Imod1 \<union> Object Imod2"
  then show "card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
  proof (intro imod_combine_containment_satisfaction_imod1)
    show "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
      by (fact local.property_field_values_not_field_imod2)
  qed (simp_all add: assms)
next
  show "irrefl ((object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+)"
  proof (intro imod_combine_containment_relation_satisfaction_imod1)
    show "\<And>ob f. ob \<in> Object Imod2 \<Longrightarrow> f \<in> Field (Tm Imod1) \<Longrightarrow> 
    \<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f) \<Longrightarrow> 
    ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
      by (fact local.property_field_values_not_field_imod2)
  qed (simp_all add: assms)
qed (simp_all add: assms)

lemma imod_combine_distinct_correct[intro]:
  assumes imod1_correct: "instance_model Imod1"
  assumes imod2_correct: "instance_model Imod2"
  assumes combine_classes_distinct: "Class (Tm Imod1) \<inter> Class (Tm Imod2) = {}"
  assumes combine_enums_distinct: "Enum (Tm Imod1) \<inter> Enum (Tm Imod2) = {}"
  assumes combine_userdatatypes_distinct: "UserDataType (Tm Imod1) \<inter> UserDataType (Tm Imod2) = {}"
  assumes combine_constants_distinct: "Constant (Tm Imod1) \<inter> Constant (Tm Imod2) = {}"
  assumes structure_object_class_wellformed: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> ob \<in> Object Imod2 \<Longrightarrow> ObjectClass Imod1 ob = ObjectClass Imod2 ob"
  assumes property_object_id_uniqueness: "\<And>o1 o2. o1 \<in> Object Imod1 - Object Imod2 \<Longrightarrow> o2 \<in> Object Imod2 - Object Imod1 \<Longrightarrow> 
    ObjectId Imod1 o1 \<noteq> ObjectId Imod2 o2"
  assumes validity_type_model_consistent: "type_model (tmod_combine (Tm Imod1) (Tm Imod2))"
  shows "instance_model (imod_combine Imod1 Imod2)"
proof (intro imod_combine_merge_correct)
  fix ob
  assume ob_in_imod1: "ob \<in> Object Imod1"
  then have "ObjectClass Imod1 ob \<in> Class (Tm Imod1)"
    using imod1_correct instance_model.structure_object_class_wellformed
    by metis
  then have "ObjectClass Imod1 ob \<notin> Class (Tm Imod2)"
    using combine_classes_distinct
    by blast
  then have ob_not_in_imod2: "ob \<notin> Object Imod2"
    using imod2_correct instance_model.structure_object_class_wellformed ob_in_imod1 structure_object_class_wellformed 
    by fastforce
  assume "ob \<in> Object Imod2"
  then show "ObjectId Imod1 ob = ObjectId Imod2 ob"
    using ob_not_in_imod2 
    by blast
next
  fix o1 o2
  assume o1_in_imod1: "o1 \<in> Object Imod1 - Object Imod2"
  assume o2_in_imod2: "o2 \<in> Object Imod2 - Object Imod1"
  have object_id_neq: "ObjectId Imod1 o1 \<noteq> ObjectId Imod2 o2"
    using o1_in_imod1 o2_in_imod2 property_object_id_uniqueness
    by simp
  assume "ObjectId Imod1 o1 = ObjectId Imod2 o2"
  then show "o1 = o2"
    using object_id_neq 
    by blast
next
  fix ob f
  assume ob_in_imod1: "ob \<in> Object Imod1"
  then have ob_class_in_tmod1: "ObjectClass Imod1 ob \<in> Class (Tm Imod1)"
    using imod1_correct instance_model.structure_object_class_wellformed
    by metis
  then have ob_class_not_in_tmod1: "ObjectClass Imod1 ob \<notin> Class (Tm Imod2)"
    using combine_classes_distinct
    by blast
  then have ob_not_in_imod2: "ob \<notin> Object Imod2"
    using imod2_correct instance_model.structure_object_class_wellformed ob_in_imod1 structure_object_class_wellformed
    by fastforce
  assume f_in_tmod2: "f \<in> Field (Tm Imod2)"
  then have class_f_in_tmod2: "fst f \<in> Class (Tm Imod2)"
    by (simp add: imod2_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
  then have class_f_not_in_tmod1: "fst f \<notin> Class (Tm Imod1)"
    using combine_classes_distinct
    by blast
  have not_extend: "\<not>\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  proof
    assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
    then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
      unfolding imod_combine_def class_def
      by simp
    then have "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
      using Int_iff imod_combine_object_class_def ob_in_imod1 structure_object_class_wellformed
      by metis
    then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
      unfolding subtype_def
      by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
    then show "False"
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
      then have "\<exclamdown>(ObjectClass Imod1 ob) = \<exclamdown>(fst f)"
        unfolding subtype_tuple_def
        by fastforce
      then show ?thesis
        using class_f_not_in_tmod1 ob_class_in_tmod1
        by simp
    next
      assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    next
      assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
      then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
        unfolding subtype_conv_def
        by fastforce
      then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
        unfolding tmod_combine_def
        by simp
      then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
        by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
      then show ?thesis
      proof (elim UnE)
        assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
        then show ?thesis
          using class_f_not_in_tmod1 imod1_correct instance_model.validity_type_model_consistent snd_conv trancl.simps type_model.structure_inh_wellformed_classes
          by metis
      next
        assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
        then show ?thesis
          using converse_tranclE imod2_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
          by metis
      qed
    next
      assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    next
      assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    qed
  qed
  assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  then show "ob \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
    using not_extend
    by blast
next
  fix ob f
  assume ob_in_imod2: "ob \<in> Object Imod2"
  then have ob_class_in_tmod2: "ObjectClass Imod2 ob \<in> Class (Tm Imod2)"
    using imod2_correct instance_model.structure_object_class_wellformed
    by metis
  then have ob_class_not_in_tmod1: "ObjectClass Imod2 ob \<notin> Class (Tm Imod1)"
    using combine_classes_distinct
    by blast
  then have ob_not_in_imod1: "ob \<notin> Object Imod1"
    using imod1_correct instance_model.structure_object_class_wellformed ob_in_imod2 structure_object_class_wellformed
    by fastforce
  assume f_in_tmod1: "f \<in> Field (Tm Imod1)"
  then have class_f_in_tmod2: "fst f \<in> Class (Tm Imod1)"
    by (simp add: imod1_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
  then have class_f_not_in_tmod2: "fst f \<notin> Class (Tm Imod2)"
    using combine_classes_distinct
    by blast
  have not_extend: "\<not>\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  proof
    assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
    then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
      unfolding imod_combine_def class_def
      by simp
    then have "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
      using Int_iff imod_combine_object_class_def ob_in_imod2 structure_object_class_wellformed
      by metis
    then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
      unfolding subtype_def
      by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
    then show "False"
      unfolding subtype_rel_altdef_def
    proof (elim UnE)
      assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
      then have "\<exclamdown>(ObjectClass Imod2 ob) = \<exclamdown>(fst f)"
        unfolding subtype_tuple_def
        by fastforce
      then show ?thesis
        using class_f_not_in_tmod2 ob_class_in_tmod2
        by simp
    next
      assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    next
      assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
      then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
        unfolding subtype_conv_def
        by fastforce
      then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
        unfolding tmod_combine_def
        by simp
      then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
        by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
      then show ?thesis
      proof (elim UnE)
        assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
        then show ?thesis
          using converse_tranclE imod1_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
          by metis
      next
        assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
        then show ?thesis
          using class_f_not_in_tmod2 imod2_correct instance_model.validity_type_model_consistent snd_conv trancl.simps type_model.structure_inh_wellformed_classes
          by metis
      qed
    next
      assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    next
      assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
      then show ?thesis
        unfolding subtype_conv_def
        by blast
    qed
  qed
  assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  then show "ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
    using not_extend
    by blast
next
  fix ob f
  assume ob_in_imod1: "ob \<in> Object Imod1"
  then have ob_class_in_tmod1: "ObjectClass Imod1 ob \<in> Class (Tm Imod1)"
    using imod1_correct instance_model.structure_object_class_wellformed
    by metis
  then have ob_class_not_in_tmod1: "ObjectClass Imod1 ob \<notin> Class (Tm Imod2)"
    using combine_classes_distinct
    by blast
  then have ob_not_in_imod2: "ob \<notin> Object Imod2" 
    using imod2_correct instance_model.structure_object_class_wellformed ob_in_imod1 structure_object_class_wellformed
    by fastforce
  assume f_in_tmod1: "f \<in> Field (Tm Imod1)"
  then have class_f_in_tmod1: "fst f \<in> Class (Tm Imod1)"
    by (simp add: imod1_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
  then have class_f_not_in_tmod2: "fst f \<notin> Class (Tm Imod2)"
    using combine_classes_distinct
    by blast
  assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
    unfolding imod_combine_def class_def
    by simp
  then have "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
    using Int_iff imod_combine_object_class_def ob_in_imod1 structure_object_class_wellformed
    by metis
  then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
    unfolding subtype_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
  then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod1)"
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
    then have "\<exclamdown>(ObjectClass Imod1 ob) = \<exclamdown>(fst f)"
      unfolding subtype_tuple_def
      by fastforce
    then show ?thesis
      using FieldI1 class_f_in_tmod1 imod1_correct instance_model.validity_type_model_consistent subtype_rel.nullable_proper_classes 
      using subtype_rel.reflexivity subtype_rel_alt subtype_rel_alt_field type_model.structure_inh_wellformed_classes
      by metis
  next
    assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
    then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
      unfolding subtype_conv_def
      by fastforce
    then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
      unfolding tmod_combine_def
      by simp
    then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
      by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
    then show ?thesis
    proof (elim UnE)
      assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
      then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod1))\<^sup>+"
        unfolding subtype_conv_def
        by force
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    next
      assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
      then show ?thesis
        using converse_tranclE imod2_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
        by metis
    qed
  next
    assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then show "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
    unfolding subtype_def
    by (simp add: class_def imod1_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
next
  fix ob f
  assume ob_in_imod2: "ob \<in> Object Imod2"
  then have ob_class_in_tmod2: "ObjectClass Imod2 ob \<in> Class (Tm Imod2)"
    using imod2_correct instance_model.structure_object_class_wellformed
    by metis
  then have ob_class_not_in_tmod2: "ObjectClass Imod2 ob \<notin> Class (Tm Imod1)"
    using combine_classes_distinct
    by blast
  then have ob_not_in_imod1: "ob \<notin> Object Imod1" 
    using imod1_correct instance_model.structure_object_class_wellformed ob_in_imod2 structure_object_class_wellformed
    by fastforce
  assume f_in_tmod2: "f \<in> Field (Tm Imod2)"
  then have class_f_in_tmod2: "fst f \<in> Class (Tm Imod2)"
    by (simp add: imod2_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
  then have class_f_not_in_tmod1: "fst f \<notin> Class (Tm Imod1)"
    using combine_classes_distinct
    by blast
  assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
  then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
    unfolding imod_combine_def class_def
    by simp
  then have "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
    using Int_iff imod_combine_object_class_def ob_in_imod2 structure_object_class_wellformed
    by metis
  then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
    unfolding subtype_def
    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
  then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
    unfolding subtype_rel_altdef_def
    by simp
  then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod2)"
  proof (elim UnE)
    assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
    then have "\<exclamdown>(ObjectClass Imod2 ob) = \<exclamdown>(fst f)"
      unfolding subtype_tuple_def
      by fastforce
    then show ?thesis
      using FieldI1 class_f_in_tmod2 imod2_correct instance_model.validity_type_model_consistent subtype_rel.nullable_proper_classes 
      using subtype_rel.reflexivity subtype_rel_alt subtype_rel_alt_field type_model.structure_inh_wellformed_classes
      by metis
  next
    assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
    then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
      unfolding subtype_conv_def
      by fastforce
    then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
      unfolding tmod_combine_def
      by simp
    then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
      by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
    then show ?thesis
    proof (elim UnE)
      assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
      then show ?thesis
        using converse_tranclE imod1_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod2 type_model.structure_inh_wellformed_alt
        by metis
    next
      assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
      then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod2))\<^sup>+"
        unfolding subtype_conv_def
        by force
      then show ?thesis
        unfolding subtype_rel_altdef_def
        by simp
    qed
  next
    assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  next
    assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
    then show ?thesis
      unfolding subtype_conv_def
      by blast
  qed
  then show "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
    unfolding subtype_def
    by (simp add: class_def imod2_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
next
  show fields_distinct: "Field (Tm Imod1) \<inter> Field (Tm Imod2) = {}"
    using imod1_correct imod2_correct instance_model.validity_type_model_consistent 
    using type_model.structure_field_wellformed_class combine_classes_distinct disjoint_iff_not_equal
    by metis
  have containments_altdef_imod1: "\<And>ob. ob \<in> Object Imod1 \<Longrightarrow> object_containments (imod_combine Imod1 Imod2) ob = object_containments Imod1 ob"
  proof-
    fix ob
    assume object_in_imod1: "ob \<in> Object Imod1"
    then have "ObjectClass Imod1 ob \<in> Class (Tm Imod1)"
      using imod1_correct instance_model.structure_object_class_wellformed
      by fastforce
    then have "ObjectClass Imod1 ob \<notin> Class (Tm Imod2)"
      using combine_classes_distinct 
      by blast
    then have "ob \<notin> Object Imod2"
      using imod2_correct instance_model.structure_object_class_wellformed object_in_imod1 structure_object_class_wellformed 
      by fastforce
    then have "obj ob \<notin> ProperClassValue Imod2"
      using ProperClassValue.cases 
      by blast
    then have ob_not_value_imod2: "obj ob \<notin> Value Imod2"
      unfolding Value_def AtomValue_def ClassValue_def
      by simp
    show "object_containments (imod_combine Imod1 Imod2) ob = object_containments Imod1 ob"
    proof
      show "object_containments (imod_combine Imod1 Imod2) ob \<subseteq> object_containments Imod1 ob"
      proof
        fix x
        assume "x \<in> object_containments (imod_combine Imod1 Imod2) ob"
        then show "x \<in> object_containments Imod1 ob"
        proof (induct x)
          case (Pair a d)
          then show ?case
          proof (induct a)
            case (fields a b c)
            then show ?case
            proof (induct)
              case (rule_object_containment o1 r)
              then have o1_in_imods: "o1 \<in> Object Imod1 \<union> Object Imod2"
                unfolding imod_combine_def
                by simp
              have "r \<in> CR (tmod_combine (Tm Imod1) (Tm Imod2))"
                using rule_object_containment.hyps(2)
                unfolding imod_combine_def
                by simp
              then have "r \<in> CR (Tm Imod1) \<union> CR (Tm Imod2)"
                using tmod_combine_containment_relation imod1_correct imod2_correct instance_model.validity_type_model_consistent
                using type_model.structure_fieldsig_wellformed_type type_model.structure_properties_wellfomed fields_distinct empty_iff
                by metis
              then show ?case
                using o1_in_imods
              proof (elim UnE)
                assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
                then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
                  by (simp add: CR.simps Type_Model.Rel_def)
                then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
                  using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
                  using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
                  by metis
                then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
                  using containment_relations_are_fields
                  by blast
                have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
                  by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
                then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
                  by (fact ProperClassType.rule_proper_classes)
                then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                assume o1_in_imod1: "o1 \<in> Object Imod1"
                then have o1_class_in_tmod1: "ObjectClass Imod1 o1 \<in> Class (Tm Imod1)"
                  using imod1_correct instance_model.structure_object_class_wellformed
                  by metis
                then have o1_class_not_in_tmod2: "ObjectClass Imod1 o1 \<notin> Class (Tm Imod2)"
                  using combine_classes_distinct
                  by blast
                then have ob_not_in_imod2: "o1 \<notin> Object Imod2"
                  using imod2_correct instance_model.structure_object_class_wellformed o1_in_imod1 structure_object_class_wellformed 
                  by fastforce
                have "\<exclamdown>(ObjectClass Imod1 o1) \<in> ProperClassType (Tm Imod1)"
                  using o1_class_in_tmod1
                  by (fact ProperClassType.rule_proper_classes)
                then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod1 o1) \<in> Type (Tm Imod1)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
                  using rule_object_containment.hyps(3)
                  unfolding imod_combine_def
                  by (simp add: imod_combine_object_class_def o1_in_imod1 ob_not_in_imod2)
                then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
                  unfolding Type_Model.fields_def
                  by fastforce
                then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
                  unfolding subtype_def
                  by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
                then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
                  subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
                  subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
                  subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
                  subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  unfolding subtype_rel_altdef_def
                  by simp
                then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod1)"
                proof (elim UnE)
                  assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
                  then have "\<exclamdown>(ObjectClass Imod1 o1) = \<exclamdown>(fst r)"
                    unfolding subtype_tuple_def
                    by fastforce
                  then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (Tm Imod1)"
                    unfolding subtype_tuple_def
                    using r_in_type_tmod1
                    by blast
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    unfolding subtype_conv_def
                    by fastforce
                  then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                    unfolding tmod_combine_def
                    by simp
                  then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                    by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
                  then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+"
                    using UnE o1_class_not_in_tmod2 converse_tranclE eq_fst_iff imod2_correct instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_classes
                    by metis
                  then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod1))\<^sup>+"
                    unfolding subtype_conv_def
                    by force
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                qed
                then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(fst r)"
                  unfolding subtype_def
                  by (simp add: imod1_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
                then have r_in_fields_tmod1: "r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 o1)"
                  unfolding Type_Model.fields_def
                  using r_in_field_tmod1
                  by fastforce
                have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod1 (o1, r)"
                  unfolding imod_combine_def imod_combine_field_value_def
                  by (simp add: o1_in_imod1 ob_not_in_imod2 r_in_field_tmod1)
                then have "obj ob \<in> set (contained_values (FieldValue Imod1 (o1, r)))"
                  using rule_object_containment.hyps(4)
                  by simp
                then show ?thesis
                  by (simp add: o1_in_imod1 object_containments.rule_object_containment r_in_fields_tmod1 r_in_tmod1)
              next
                assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
                then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
                  by (simp add: CR.simps Type_Model.Rel_def)
                then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
                  using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
                  using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
                  by metis
                then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
                  using containment_relations_are_fields
                  by blast
                have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
                  by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
                then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
                  by (fact ProperClassType.rule_proper_classes)
                then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                assume o1_in_imod2: "o1 \<in> Object Imod2"
                then have o1_class_in_tmod2: "ObjectClass Imod2 o1 \<in> Class (Tm Imod2)"
                  using imod2_correct instance_model.structure_object_class_wellformed
                  by metis
                then have o1_class_not_in_tmod1: "ObjectClass Imod2 o1 \<notin> Class (Tm Imod1)"
                  using combine_classes_distinct
                  by blast
                then have ob_not_in_imod1: "o1 \<notin> Object Imod1"
                  using imod1_correct instance_model.structure_object_class_wellformed o1_in_imod2 structure_object_class_wellformed 
                  by fastforce
                have "\<exclamdown>(ObjectClass Imod2 o1) \<in> ProperClassType (Tm Imod2)"
                  using o1_class_in_tmod2
                  by (fact ProperClassType.rule_proper_classes)
                then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod2 o1) \<in> Type (Tm Imod2)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                have r_not_field: "r \<notin> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
                proof
                  assume "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
                  then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
                    unfolding Type_Model.fields_def
                    by fastforce
                  then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
                    unfolding subtype_def
                    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
                  then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
                    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
                    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
                    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
                    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    unfolding subtype_rel_altdef_def
                    by simp
                  then show "False"
                  proof (elim UnE)
                    assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
                    then have "\<exclamdown>(ObjectClass Imod2 o1) = \<exclamdown>(fst r)"
                      unfolding subtype_tuple_def
                      by fastforce
                    then show ?thesis
                      using o1_class_not_in_tmod1 r_class_in_tmod1
                      by simp
                  next
                    assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                      unfolding subtype_conv_def
                      by fastforce
                    then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                      unfolding tmod_combine_def
                      by simp
                    then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                      by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
                    then show ?thesis
                    proof (elim UnE)
                      assume "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+"
                      then show ?thesis
                        using converse_tranclE imod1_correct instance_model.validity_type_model_consistent 
                        using o1_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
                        by metis
                    next
                      assume "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod2))\<^sup>+"
                      then show ?thesis
                        using combine_classes_distinct disjoint_iff_not_equal imod2_correct r_class_in_tmod1 trancl.simps 
                        using instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_alt
                        by metis
                    qed
                  next
                    assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  qed
                qed
                have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
                  using rule_object_containment.hyps(3)
                  unfolding imod_combine_def
                  by (simp add: imod_combine_object_class_def o1_in_imod2 ob_not_in_imod1)
                then show ?thesis
                  using r_not_field
                  by blast
              next
                assume r_in_tmod2: "r \<in> CR (Tm Imod2)"
                then have r_in_field_tmod2: "r \<in> Field (Tm Imod2)"
                  by (simp add: CR.simps Type_Model.Rel_def)
                then have r_not_in_field_tmod1: "r \<notin> Field (Tm Imod1)"
                  using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
                  using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
                  by metis
                then have r_not_in_tmod1: "r \<notin> CR (Tm Imod1)"
                  using containment_relations_are_fields
                  by blast
                have r_class_in_tmod2: "fst r \<in> Class (Tm Imod2)"
                  by (simp add: imod2_correct instance_model.validity_type_model_consistent r_in_field_tmod2 type_model.structure_field_wellformed_class)
                then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod2)"
                  by (fact ProperClassType.rule_proper_classes)
                then have r_in_type_tmod2: "\<exclamdown>(fst r) \<in> Type (Tm Imod2)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                assume o1_in_imod1: "o1 \<in> Object Imod1"
                then have o1_class_in_tmod1: "ObjectClass Imod1 o1 \<in> Class (Tm Imod1)"
                  using imod1_correct instance_model.structure_object_class_wellformed
                  by metis
                then have o1_class_not_in_tmod2: "ObjectClass Imod1 o1 \<notin> Class (Tm Imod2)"
                  using combine_classes_distinct
                  by blast
                then have ob_not_in_imod2: "o1 \<notin> Object Imod2"
                  using imod2_correct instance_model.structure_object_class_wellformed o1_in_imod1 structure_object_class_wellformed 
                  by fastforce
                have "\<exclamdown>(ObjectClass Imod1 o1) \<in> ProperClassType (Tm Imod1)"
                  using o1_class_in_tmod1
                  by (fact ProperClassType.rule_proper_classes)
                then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod1 o1) \<in> Type (Tm Imod1)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                have r_not_field: "r \<notin> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
                proof
                  assume "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
                  then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
                    unfolding Type_Model.fields_def
                    by fastforce
                  then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
                    unfolding subtype_def
                    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
                  then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
                    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
                    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
                    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
                    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    unfolding subtype_rel_altdef_def
                    by simp
                  then show "False"
                  proof (elim UnE)
                    assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
                    then have "\<exclamdown>(ObjectClass Imod1 o1) = \<exclamdown>(fst r)"
                      unfolding subtype_tuple_def
                      by fastforce
                    then show ?thesis
                      using o1_class_not_in_tmod2 r_class_in_tmod2
                      by simp
                  next
                    assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                      unfolding subtype_conv_def
                      by fastforce
                    then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                      unfolding tmod_combine_def
                      by simp
                    then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                      by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
                    then show ?thesis
                    proof (elim UnE)
                      assume "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+"
                      then show ?thesis
                        using combine_classes_distinct disjoint_iff_not_equal imod1_correct r_class_in_tmod2 trancl.simps 
                        using instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_alt
                        by metis
                    next
                      assume "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod2))\<^sup>+"
                      then show ?thesis
                        using converse_tranclE imod2_correct instance_model.validity_type_model_consistent 
                        using o1_class_not_in_tmod2 type_model.structure_inh_wellformed_alt
                        by metis
                    qed
                  next
                    assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  qed
                qed
                have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
                  using rule_object_containment.hyps(3)
                  unfolding imod_combine_def
                  by (simp add: imod_combine_object_class_def o1_in_imod1 ob_not_in_imod2)
                then show ?thesis
                  using r_not_field
                  by blast
              next
                assume r_in_tmod2: "r \<in> CR (Tm Imod2)"
                then have r_in_field_tmod2: "r \<in> Field (Tm Imod2)"
                  by (simp add: CR.simps Type_Model.Rel_def)
                then have r_not_in_field_tmod1: "r \<notin> Field (Tm Imod1)"
                  using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
                  using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
                  by metis
                then have r_not_in_tmod1: "r \<notin> CR (Tm Imod1)"
                  using containment_relations_are_fields
                  by blast
                have r_class_in_tmod2: "fst r \<in> Class (Tm Imod2)"
                  by (simp add: imod2_correct instance_model.validity_type_model_consistent r_in_field_tmod2 type_model.structure_field_wellformed_class)
                then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod2)"
                  by (fact ProperClassType.rule_proper_classes)
                then have r_in_type_tmod2: "\<exclamdown>(fst r) \<in> Type (Tm Imod2)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                assume o1_in_imod2: "o1 \<in> Object Imod2"
                then have o1_class_in_tmod2: "ObjectClass Imod2 o1 \<in> Class (Tm Imod2)"
                  using imod2_correct instance_model.structure_object_class_wellformed
                  by metis
                then have o1_class_not_in_tmod1: "ObjectClass Imod2 o1 \<notin> Class (Tm Imod1)"
                  using combine_classes_distinct
                  by blast
                then have ob_not_in_imod1: "o1 \<notin> Object Imod1"
                  using imod1_correct instance_model.structure_object_class_wellformed o1_in_imod2 structure_object_class_wellformed 
                  by fastforce
                have "\<exclamdown>(ObjectClass Imod2 o1) \<in> ProperClassType (Tm Imod2)"
                  using o1_class_in_tmod2
                  by (fact ProperClassType.rule_proper_classes)
                then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod2 o1) \<in> Type (Tm Imod2)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
                  using rule_object_containment.hyps(3)
                  unfolding imod_combine_def
                  by (simp add: imod_combine_object_class_def o1_in_imod2 ob_not_in_imod1)
                then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
                  unfolding Type_Model.fields_def
                  by fastforce
                then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
                  unfolding subtype_def
                  by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
                then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
                  subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
                  subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
                  subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
                  subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  unfolding subtype_rel_altdef_def
                  by simp
                then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod2)"
                proof (elim UnE)
                  assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
                  then have "\<exclamdown>(ObjectClass Imod2 o1) = \<exclamdown>(fst r)"
                    unfolding subtype_tuple_def
                    by fastforce
                  then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (Tm Imod2)"
                    unfolding subtype_tuple_def
                    using r_in_type_tmod2
                    by blast
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    unfolding subtype_conv_def
                    by fastforce
                  then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                    unfolding tmod_combine_def
                    by simp
                  then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                    by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
                  then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod2))\<^sup>+"
                    using UnE o1_class_not_in_tmod1 converse_tranclE eq_fst_iff imod1_correct instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_classes
                    by metis
                  then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod2))\<^sup>+"
                    unfolding subtype_conv_def
                    by force
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                qed
                then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(fst r)"
                  unfolding subtype_def
                  by (simp add: imod2_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
                then have r_in_fields_tmod2: "r \<in> Type_Model.fields (Tm Imod2) (ObjectClass Imod2 o1)"
                  unfolding Type_Model.fields_def
                  using r_in_field_tmod2
                  by fastforce
                have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod2 (o1, r)"
                  unfolding imod_combine_def imod_combine_field_value_def
                  by (simp add: o1_in_imod2 ob_not_in_imod1 r_in_field_tmod2)
                then have object_value_o1: "obj ob \<in> set (contained_values (FieldValue Imod2 (o1, r)))"
                  using rule_object_containment.hyps(4)
                  by simp
                have "FieldValue Imod2 (o1, r) \<in> Value Imod2"
                  by (simp add: imod2_correct instance_model.property_field_values_inside_domain o1_in_imod2 r_in_field_tmod2 r_in_fields_tmod2)
                then have "set (contained_values (FieldValue Imod2 (o1, r))) \<subseteq> Value Imod2"
                  unfolding Value_def
                  using container_value_contained_values atom_values_contained_values_singleton
                  by fastforce
                then have "obj ob \<in> Value Imod2"
                  using object_value_o1
                  by blast
                then show ?thesis
                  using ob_not_value_imod2 
                  by blast
              qed
            qed
          qed
        qed
      qed
    next
      show "object_containments Imod1 ob \<subseteq> object_containments (imod_combine Imod1 Imod2) ob"
      proof (intro imod_combine_object_containments_subset_imod1)
        fix f
        assume "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2)"
        then show "fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
          by (simp add: fields_distinct)
      next
        fix ob f
        assume "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2)"
        then show "FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: fields_distinct)
      qed (simp_all add: assms instance_model.validity_type_model_consistent type_model.structure_fieldsig_wellformed_type instance_model.property_field_values_outside_domain)
    qed
  qed
  have containments_altdef_imod2: "\<And>ob. ob \<in> Object Imod2 \<Longrightarrow> object_containments (imod_combine Imod1 Imod2) ob = object_containments Imod2 ob"
  proof-
    fix ob
    assume object_in_imod2: "ob \<in> Object Imod2"
    then have "ObjectClass Imod2 ob \<in> Class (Tm Imod2)"
      using imod2_correct instance_model.structure_object_class_wellformed
      by fastforce
    then have "ObjectClass Imod2 ob \<notin> Class (Tm Imod1)"
      using combine_classes_distinct 
      by blast
    then have "ob \<notin> Object Imod1"
      using imod1_correct instance_model.structure_object_class_wellformed object_in_imod2 structure_object_class_wellformed 
      by fastforce
    then have "obj ob \<notin> ProperClassValue Imod1"
      using ProperClassValue.cases 
      by blast
    then have ob_not_value_imod1: "obj ob \<notin> Value Imod1"
      unfolding Value_def AtomValue_def ClassValue_def
      by simp
    show "object_containments (imod_combine Imod1 Imod2) ob = object_containments Imod2 ob"
    proof
      show "object_containments (imod_combine Imod1 Imod2) ob \<subseteq> object_containments Imod2 ob"
      proof
        fix x
        assume "x \<in> object_containments (imod_combine Imod1 Imod2) ob"
        then show "x \<in> object_containments Imod2 ob"
        proof (induct x)
          case (Pair a d)
          then show ?case
          proof (induct a)
            case (fields a b c)
            then show ?case
            proof (induct)
              case (rule_object_containment o1 r)
              then have o1_in_imods: "o1 \<in> Object Imod1 \<union> Object Imod2"
                unfolding imod_combine_def
                by simp
              have "r \<in> CR (tmod_combine (Tm Imod1) (Tm Imod2))"
                using rule_object_containment.hyps(2)
                unfolding imod_combine_def
                by simp
              then have "r \<in> CR (Tm Imod1) \<union> CR (Tm Imod2)"
                using tmod_combine_containment_relation imod1_correct imod2_correct instance_model.validity_type_model_consistent
                using type_model.structure_fieldsig_wellformed_type type_model.structure_properties_wellfomed fields_distinct empty_iff
                by metis
              then show ?case
                using o1_in_imods
              proof (elim UnE)
                assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
                then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
                  by (simp add: CR.simps Type_Model.Rel_def)
                then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
                  using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
                  using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
                  by metis
                then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
                  using containment_relations_are_fields
                  by blast
                have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
                  by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
                then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
                  by (fact ProperClassType.rule_proper_classes)
                then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                assume o1_in_imod1: "o1 \<in> Object Imod1"
                then have o1_class_in_tmod1: "ObjectClass Imod1 o1 \<in> Class (Tm Imod1)"
                  using imod1_correct instance_model.structure_object_class_wellformed
                  by metis
                then have o1_class_not_in_tmod2: "ObjectClass Imod1 o1 \<notin> Class (Tm Imod2)"
                  using combine_classes_distinct
                  by blast
                then have ob_not_in_imod2: "o1 \<notin> Object Imod2"
                  using imod2_correct instance_model.structure_object_class_wellformed o1_in_imod1 structure_object_class_wellformed 
                  by fastforce
                have "\<exclamdown>(ObjectClass Imod1 o1) \<in> ProperClassType (Tm Imod1)"
                  using o1_class_in_tmod1
                  by (fact ProperClassType.rule_proper_classes)
                then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod1 o1) \<in> Type (Tm Imod1)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
                  using rule_object_containment.hyps(3)
                  unfolding imod_combine_def
                  by (simp add: imod_combine_object_class_def o1_in_imod1 ob_not_in_imod2)
                then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
                  unfolding Type_Model.fields_def
                  by fastforce
                then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
                  unfolding subtype_def
                  by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
                then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
                  subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
                  subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
                  subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
                  subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  unfolding subtype_rel_altdef_def
                  by simp
                then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod1)"
                proof (elim UnE)
                  assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
                  then have "\<exclamdown>(ObjectClass Imod1 o1) = \<exclamdown>(fst r)"
                    unfolding subtype_tuple_def
                    by fastforce
                  then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (Tm Imod1)"
                    unfolding subtype_tuple_def
                    using r_in_type_tmod1
                    by blast
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    unfolding subtype_conv_def
                    by fastforce
                  then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                    unfolding tmod_combine_def
                    by simp
                  then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                    by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
                  then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+"
                    using UnE o1_class_not_in_tmod2 converse_tranclE eq_fst_iff imod2_correct instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_classes
                    by metis
                  then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod1))\<^sup>+"
                    unfolding subtype_conv_def
                    by force
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                qed
                then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(fst r)"
                  unfolding subtype_def
                  by (simp add: imod1_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
                then have r_in_fields_tmod1: "r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 o1)"
                  unfolding Type_Model.fields_def
                  using r_in_field_tmod1
                  by fastforce
                have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod1 (o1, r)"
                  unfolding imod_combine_def imod_combine_field_value_def
                  by (simp add: o1_in_imod1 ob_not_in_imod2 r_in_field_tmod1)
                then have object_value_o1: "obj ob \<in> set (contained_values (FieldValue Imod1 (o1, r)))"
                  using rule_object_containment.hyps(4)
                  by simp
                have "FieldValue Imod1 (o1, r) \<in> Value Imod1"
                  by (simp add: imod1_correct instance_model.property_field_values_inside_domain o1_in_imod1 r_in_field_tmod1 r_in_fields_tmod1)
                then have "set (contained_values (FieldValue Imod1 (o1, r))) \<subseteq> Value Imod1"
                  unfolding Value_def
                  using container_value_contained_values atom_values_contained_values_singleton
                  by fastforce
                then have "obj ob \<in> Value Imod1"
                  using object_value_o1
                  by blast
                then show ?thesis
                  using ob_not_value_imod1
                  by blast
              next
                assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
                then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
                  by (simp add: CR.simps Type_Model.Rel_def)
                then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
                  using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
                  using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
                  by metis
                then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
                  using containment_relations_are_fields
                  by blast
                have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
                  by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
                then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
                  by (fact ProperClassType.rule_proper_classes)
                then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                assume o1_in_imod2: "o1 \<in> Object Imod2"
                then have o1_class_in_tmod2: "ObjectClass Imod2 o1 \<in> Class (Tm Imod2)"
                  using imod2_correct instance_model.structure_object_class_wellformed
                  by metis
                then have o1_class_not_in_tmod1: "ObjectClass Imod2 o1 \<notin> Class (Tm Imod1)"
                  using combine_classes_distinct
                  by blast
                then have ob_not_in_imod1: "o1 \<notin> Object Imod1"
                  using imod1_correct instance_model.structure_object_class_wellformed o1_in_imod2 structure_object_class_wellformed 
                  by fastforce
                have "\<exclamdown>(ObjectClass Imod2 o1) \<in> ProperClassType (Tm Imod2)"
                  using o1_class_in_tmod2
                  by (fact ProperClassType.rule_proper_classes)
                then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod2 o1) \<in> Type (Tm Imod2)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                have r_not_field: "r \<notin> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
                proof
                  assume "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
                  then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
                    unfolding Type_Model.fields_def
                    by fastforce
                  then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
                    unfolding subtype_def
                    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
                  then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
                    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
                    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
                    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
                    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    unfolding subtype_rel_altdef_def
                    by simp
                  then show "False"
                  proof (elim UnE)
                    assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
                    then have "\<exclamdown>(ObjectClass Imod2 o1) = \<exclamdown>(fst r)"
                      unfolding subtype_tuple_def
                      by fastforce
                    then show ?thesis
                      using o1_class_not_in_tmod1 r_class_in_tmod1
                      by simp
                  next
                    assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                      unfolding subtype_conv_def
                      by fastforce
                    then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                      unfolding tmod_combine_def
                      by simp
                    then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                      by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
                    then show ?thesis
                    proof (elim UnE)
                      assume "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+"
                      then show ?thesis
                        using converse_tranclE imod1_correct instance_model.validity_type_model_consistent 
                        using o1_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
                        by metis
                    next
                      assume "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod2))\<^sup>+"
                      then show ?thesis
                        using combine_classes_distinct disjoint_iff_not_equal imod2_correct r_class_in_tmod1 trancl.simps 
                        using instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_alt
                        by metis
                    qed
                  next
                    assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  qed
                qed
                have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
                  using rule_object_containment.hyps(3)
                  unfolding imod_combine_def
                  by (simp add: imod_combine_object_class_def o1_in_imod2 ob_not_in_imod1)
                then show ?thesis
                  using r_not_field
                  by blast
              next
                assume r_in_tmod2: "r \<in> CR (Tm Imod2)"
                then have r_in_field_tmod2: "r \<in> Field (Tm Imod2)"
                  by (simp add: CR.simps Type_Model.Rel_def)
                then have r_not_in_field_tmod1: "r \<notin> Field (Tm Imod1)"
                  using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
                  using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
                  by metis
                then have r_not_in_tmod1: "r \<notin> CR (Tm Imod1)"
                  using containment_relations_are_fields
                  by blast
                have r_class_in_tmod2: "fst r \<in> Class (Tm Imod2)"
                  by (simp add: imod2_correct instance_model.validity_type_model_consistent r_in_field_tmod2 type_model.structure_field_wellformed_class)
                then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod2)"
                  by (fact ProperClassType.rule_proper_classes)
                then have r_in_type_tmod2: "\<exclamdown>(fst r) \<in> Type (Tm Imod2)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                assume o1_in_imod1: "o1 \<in> Object Imod1"
                then have o1_class_in_tmod1: "ObjectClass Imod1 o1 \<in> Class (Tm Imod1)"
                  using imod1_correct instance_model.structure_object_class_wellformed
                  by metis
                then have o1_class_not_in_tmod2: "ObjectClass Imod1 o1 \<notin> Class (Tm Imod2)"
                  using combine_classes_distinct
                  by blast
                then have ob_not_in_imod2: "o1 \<notin> Object Imod2"
                  using imod2_correct instance_model.structure_object_class_wellformed o1_in_imod1 structure_object_class_wellformed 
                  by fastforce
                have "\<exclamdown>(ObjectClass Imod1 o1) \<in> ProperClassType (Tm Imod1)"
                  using o1_class_in_tmod1
                  by (fact ProperClassType.rule_proper_classes)
                then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod1 o1) \<in> Type (Tm Imod1)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                have r_not_field: "r \<notin> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
                proof
                  assume "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
                  then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
                    unfolding Type_Model.fields_def
                    by fastforce
                  then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
                    unfolding subtype_def
                    by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
                  then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
                    subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
                    subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
                    subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
                    subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    unfolding subtype_rel_altdef_def
                    by simp
                  then show "False"
                  proof (elim UnE)
                    assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
                    then have "\<exclamdown>(ObjectClass Imod1 o1) = \<exclamdown>(fst r)"
                      unfolding subtype_tuple_def
                      by fastforce
                    then show ?thesis
                      using o1_class_not_in_tmod2 r_class_in_tmod2
                      by simp
                  next
                    assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                      unfolding subtype_conv_def
                      by fastforce
                    then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                      unfolding tmod_combine_def
                      by simp
                    then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                      by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
                    then show ?thesis
                    proof (elim UnE)
                      assume "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+"
                      then show ?thesis
                        using combine_classes_distinct disjoint_iff_not_equal imod1_correct r_class_in_tmod2 trancl.simps 
                        using instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_alt
                        by metis
                    next
                      assume "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod2))\<^sup>+"
                      then show ?thesis
                        using converse_tranclE imod2_correct instance_model.validity_type_model_consistent 
                        using o1_class_not_in_tmod2 type_model.structure_inh_wellformed_alt
                        by metis
                    qed
                  next
                    assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  next
                    assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    then show ?thesis
                      unfolding subtype_conv_def
                      by blast
                  qed
                qed
                have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
                  using rule_object_containment.hyps(3)
                  unfolding imod_combine_def
                  by (simp add: imod_combine_object_class_def o1_in_imod1 ob_not_in_imod2)
                then show ?thesis
                  using r_not_field
                  by blast
              next
                assume r_in_tmod2: "r \<in> CR (Tm Imod2)"
                then have r_in_field_tmod2: "r \<in> Field (Tm Imod2)"
                  by (simp add: CR.simps Type_Model.Rel_def)
                then have r_not_in_field_tmod1: "r \<notin> Field (Tm Imod1)"
                  using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
                  using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
                  by metis
                then have r_not_in_tmod1: "r \<notin> CR (Tm Imod1)"
                  using containment_relations_are_fields
                  by blast
                have r_class_in_tmod2: "fst r \<in> Class (Tm Imod2)"
                  by (simp add: imod2_correct instance_model.validity_type_model_consistent r_in_field_tmod2 type_model.structure_field_wellformed_class)
                then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod2)"
                  by (fact ProperClassType.rule_proper_classes)
                then have r_in_type_tmod2: "\<exclamdown>(fst r) \<in> Type (Tm Imod2)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                assume o1_in_imod2: "o1 \<in> Object Imod2"
                then have o1_class_in_tmod2: "ObjectClass Imod2 o1 \<in> Class (Tm Imod2)"
                  using imod2_correct instance_model.structure_object_class_wellformed
                  by metis
                then have o1_class_not_in_tmod1: "ObjectClass Imod2 o1 \<notin> Class (Tm Imod1)"
                  using combine_classes_distinct
                  by blast
                then have ob_not_in_imod1: "o1 \<notin> Object Imod1"
                  using imod1_correct instance_model.structure_object_class_wellformed o1_in_imod2 structure_object_class_wellformed 
                  by fastforce
                have "\<exclamdown>(ObjectClass Imod2 o1) \<in> ProperClassType (Tm Imod2)"
                  using o1_class_in_tmod2
                  by (fact ProperClassType.rule_proper_classes)
                then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod2 o1) \<in> Type (Tm Imod2)"
                  unfolding Type_def NonContainerType_def ClassType_def
                  by simp
                have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
                  using rule_object_containment.hyps(3)
                  unfolding imod_combine_def
                  by (simp add: imod_combine_object_class_def o1_in_imod2 ob_not_in_imod1)
                then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
                  unfolding Type_Model.fields_def
                  by fastforce
                then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
                  unfolding subtype_def
                  by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
                then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
                  subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
                  subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
                  subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
                  subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  unfolding subtype_rel_altdef_def
                  by simp
                then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod2)"
                proof (elim UnE)
                  assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
                  then have "\<exclamdown>(ObjectClass Imod2 o1) = \<exclamdown>(fst r)"
                    unfolding subtype_tuple_def
                    by fastforce
                  then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (Tm Imod2)"
                    unfolding subtype_tuple_def
                    using r_in_type_tmod2
                    by blast
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                    unfolding subtype_conv_def
                    by fastforce
                  then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                    unfolding tmod_combine_def
                    by simp
                  then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                    by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
                  then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod2))\<^sup>+"
                    using UnE o1_class_not_in_tmod1 converse_tranclE eq_fst_iff imod1_correct instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_classes
                    by metis
                  then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod2))\<^sup>+"
                    unfolding subtype_conv_def
                    by force
                  then show ?thesis
                    unfolding subtype_rel_altdef_def
                    by simp
                next
                  assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                next
                  assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  then show ?thesis
                    unfolding subtype_conv_def
                    by blast
                qed
                then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(fst r)"
                  unfolding subtype_def
                  by (simp add: imod2_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
                then have r_in_fields_tmod2: "r \<in> Type_Model.fields (Tm Imod2) (ObjectClass Imod2 o1)"
                  unfolding Type_Model.fields_def
                  using r_in_field_tmod2
                  by fastforce
                have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod2 (o1, r)"
                  unfolding imod_combine_def imod_combine_field_value_def
                  by (simp add: o1_in_imod2 ob_not_in_imod1 r_in_field_tmod2)
                then have "obj ob \<in> set (contained_values (FieldValue Imod2 (o1, r)))"
                  using rule_object_containment.hyps(4)
                  by simp
                then show ?thesis
                  by (simp add: o1_in_imod2 object_containments.rule_object_containment r_in_fields_tmod2 r_in_tmod2)
              qed
            qed
          qed
        qed
      qed
    next
      show "object_containments Imod2 ob \<subseteq> object_containments (imod_combine Imod1 Imod2) ob"
      proof (intro imod_combine_object_containments_subset_imod2)
        fix f
        assume "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2)"
        then show "fst (FieldSig (Tm Imod1) f) = fst (FieldSig (Tm Imod2) f)"
          by (simp add: fields_distinct)
      next
        fix ob f
        assume "f \<in> Field (Tm Imod1) \<inter> Field (Tm Imod2)"
        then show "FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)"
          by (simp add: fields_distinct)
      qed (simp_all add: assms instance_model.validity_type_model_consistent type_model.structure_fieldsig_wellformed_type instance_model.property_field_values_outside_domain)
    qed
  qed
  fix r ob
  assume containment_in_tmods: "containment r \<in> Prop (Tm Imod1) \<union> Prop (Tm Imod2)"
  assume ob_in_imods: "ob \<in> Object Imod1 \<union> Object Imod2"
  show "card (object_containments (imod_combine Imod1 Imod2) ob) \<le> 1"
    using ob_in_imods
  proof (induct "\<exists>r. containment r \<in> Prop (Tm Imod1)")
    case True
    then show ?case
    proof (induct "\<exists>r. containment r \<in> Prop (Tm Imod2)")
      case True
      then show ?case
      proof (elim UnE)
        assume ob_in_imod1: "ob \<in> Object Imod1"
        then have "card (object_containments Imod1 ob) \<le> 1"
          using imod1_correct instance_model.validity_properties_satisfied property_satisfaction_containment_rev True.prems(1)
          by metis
        then show ?thesis
          by (simp add: containments_altdef_imod1 ob_in_imod1)
      next
        assume ob_in_imod2: "ob \<in> Object Imod2"
        then have "card (object_containments Imod2 ob) \<le> 1"
          using imod2_correct instance_model.validity_properties_satisfied property_satisfaction_containment_rev True.hyps
          by metis
        then show ?thesis
          by (simp add: containments_altdef_imod2 ob_in_imod2)
      qed
    next
      case False
      then show ?case
      proof (intro imod_combine_containment_satisfaction_imod1)
        fix ob f
        assume ob_in_imod2: "ob \<in> Object Imod2"
        then have ob_class_in_tmod2: "ObjectClass Imod2 ob \<in> Class (Tm Imod2)"
          using imod2_correct instance_model.structure_object_class_wellformed
          by metis
        then have ob_class_not_in_tmod1: "ObjectClass Imod2 ob \<notin> Class (Tm Imod1)"
          using combine_classes_distinct
          by blast
        then have ob_not_in_imod1: "ob \<notin> Object Imod1"
          using imod1_correct instance_model.structure_object_class_wellformed ob_in_imod2 structure_object_class_wellformed
          by fastforce
        assume f_in_tmod1: "f \<in> Field (Tm Imod1)"
        then have class_f_in_tmod2: "fst f \<in> Class (Tm Imod1)"
          by (simp add: imod1_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
        then have class_f_not_in_tmod2: "fst f \<notin> Class (Tm Imod2)"
          using combine_classes_distinct
          by blast
        have not_extend: "\<not>\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
        proof
          assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
          then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
            unfolding imod_combine_def class_def
            by simp
          then have "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
            using Int_iff imod_combine_object_class_def ob_in_imod2 structure_object_class_wellformed
            by metis
          then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
            unfolding subtype_def
            by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
          then show "False"
            unfolding subtype_rel_altdef_def
          proof (elim UnE)
            assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
            then have "\<exclamdown>(ObjectClass Imod2 ob) = \<exclamdown>(fst f)"
              unfolding subtype_tuple_def
              by fastforce
            then show ?thesis
              using class_f_not_in_tmod2 ob_class_in_tmod2
              by simp
          next
            assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
            then show ?thesis
              unfolding subtype_conv_def
              by blast
          next
            assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
            then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
              unfolding subtype_conv_def
              by fastforce
            then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
              unfolding tmod_combine_def
              by simp
            then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
              by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
            then show ?thesis
            proof (elim UnE)
              assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
              then show ?thesis
                using converse_tranclE imod1_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
                by metis
            next
              assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
              then show ?thesis
                using class_f_not_in_tmod2 imod2_correct instance_model.validity_type_model_consistent snd_conv trancl.simps type_model.structure_inh_wellformed_classes
                by metis
            qed
          next
            assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
            then show ?thesis
              unfolding subtype_conv_def
              by blast
          next
            assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
            then show ?thesis
              unfolding subtype_conv_def
              by blast
          qed
        qed
        assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
        then show "ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
          using not_extend
          by blast
      next
        fix ob f
        assume ob_in_imod1: "ob \<in> Object Imod1"
        then have ob_class_in_tmod1: "ObjectClass Imod1 ob \<in> Class (Tm Imod1)"
          using imod1_correct instance_model.structure_object_class_wellformed
          by metis
        then have ob_class_not_in_tmod1: "ObjectClass Imod1 ob \<notin> Class (Tm Imod2)"
          using combine_classes_distinct
          by blast
        then have ob_not_in_imod2: "ob \<notin> Object Imod2" 
          using imod2_correct instance_model.structure_object_class_wellformed ob_in_imod1 structure_object_class_wellformed
          by fastforce
        assume f_in_tmod1: "f \<in> Field (Tm Imod1)"
        then have class_f_in_tmod1: "fst f \<in> Class (Tm Imod1)"
          by (simp add: imod1_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
        then have class_f_not_in_tmod2: "fst f \<notin> Class (Tm Imod2)"
          using combine_classes_distinct
          by blast
        assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
        then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
          unfolding imod_combine_def class_def
          by simp
        then have "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
          using Int_iff imod_combine_object_class_def ob_in_imod1 structure_object_class_wellformed
          by metis
        then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
          unfolding subtype_def
          by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
        then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
          subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
          subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
          subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
          subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          unfolding subtype_rel_altdef_def
          by simp
        then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod1)"
        proof (elim UnE)
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
          then have "\<exclamdown>(ObjectClass Imod1 ob) = \<exclamdown>(fst f)"
            unfolding subtype_tuple_def
            by fastforce
          then show ?thesis
            using FieldI1 class_f_in_tmod1 imod1_correct instance_model.validity_type_model_consistent subtype_rel.nullable_proper_classes 
            using subtype_rel.reflexivity subtype_rel_alt subtype_rel_alt_field type_model.structure_inh_wellformed_classes
            by metis
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
            unfolding subtype_conv_def
            by fastforce
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
            unfolding tmod_combine_def
            by simp
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
            by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
          then show ?thesis
          proof (elim UnE)
            assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
            then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod1))\<^sup>+"
              unfolding subtype_conv_def
              by force
            then show ?thesis
              unfolding subtype_rel_altdef_def
              by simp
          next
            assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
            then show ?thesis
              using converse_tranclE imod2_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
              by metis
          qed
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        qed
        then show "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
          unfolding subtype_def
          by (simp add: class_def imod1_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
      qed (simp_all add: assms fields_distinct)
    qed
  next
    case False
    then show ?case
    proof (intro imod_combine_containment_satisfaction_imod2)
      fix ob f
      assume ob_in_imod1: "ob \<in> Object Imod1"
      then have ob_class_in_tmod1: "ObjectClass Imod1 ob \<in> Class (Tm Imod1)"
        using imod1_correct instance_model.structure_object_class_wellformed
        by metis
      then have ob_class_not_in_tmod1: "ObjectClass Imod1 ob \<notin> Class (Tm Imod2)"
        using combine_classes_distinct
        by blast
      then have ob_not_in_imod2: "ob \<notin> Object Imod2"
        using imod2_correct instance_model.structure_object_class_wellformed ob_in_imod1 structure_object_class_wellformed
        by fastforce
      assume f_in_tmod2: "f \<in> Field (Tm Imod2)"
      then have class_f_in_tmod2: "fst f \<in> Class (Tm Imod2)"
        by (simp add: imod2_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
      then have class_f_not_in_tmod1: "fst f \<notin> Class (Tm Imod1)"
        using combine_classes_distinct
        by blast
      have not_extend: "\<not>\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
      proof
        assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
        then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
          unfolding imod_combine_def class_def
          by simp
        then have "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
          using Int_iff imod_combine_object_class_def ob_in_imod1 structure_object_class_wellformed
          by metis
        then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
          unfolding subtype_def
          by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
        then show "False"
          unfolding subtype_rel_altdef_def
        proof (elim UnE)
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
          then have "\<exclamdown>(ObjectClass Imod1 ob) = \<exclamdown>(fst f)"
            unfolding subtype_tuple_def
            by fastforce
          then show ?thesis
            using class_f_not_in_tmod1 ob_class_in_tmod1
            by simp
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
            unfolding subtype_conv_def
            by fastforce
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
            unfolding tmod_combine_def
            by simp
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
            by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
          then show ?thesis
          proof (elim UnE)
            assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
            then show ?thesis
              using class_f_not_in_tmod1 imod1_correct instance_model.validity_type_model_consistent snd_conv trancl.simps type_model.structure_inh_wellformed_classes
              by metis
          next
            assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
            then show ?thesis
              using converse_tranclE imod2_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
              by metis
          qed
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        qed
      qed
      assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
      then show "ob \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        using not_extend
        by blast
    next
      fix ob f
      assume ob_in_imod2: "ob \<in> Object Imod2"
      then have ob_class_in_tmod2: "ObjectClass Imod2 ob \<in> Class (Tm Imod2)"
        using imod2_correct instance_model.structure_object_class_wellformed
        by metis
      then have ob_class_not_in_tmod2: "ObjectClass Imod2 ob \<notin> Class (Tm Imod1)"
        using combine_classes_distinct
        by blast
      then have ob_not_in_imod1: "ob \<notin> Object Imod1" 
        using imod1_correct instance_model.structure_object_class_wellformed ob_in_imod2 structure_object_class_wellformed
        by fastforce
      assume f_in_tmod2: "f \<in> Field (Tm Imod2)"
      then have class_f_in_tmod2: "fst f \<in> Class (Tm Imod2)"
        by (simp add: imod2_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
      then have class_f_not_in_tmod1: "fst f \<notin> Class (Tm Imod1)"
        using combine_classes_distinct
        by blast
      assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
      then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
        unfolding imod_combine_def class_def
        by simp
      then have "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
        using Int_iff imod_combine_object_class_def ob_in_imod2 structure_object_class_wellformed
        by metis
      then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
        unfolding subtype_def
        by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
      then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
        subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
        subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
        subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
        subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
        unfolding subtype_rel_altdef_def
        by simp
      then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod2)"
      proof (elim UnE)
        assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
        then have "\<exclamdown>(ObjectClass Imod2 ob) = \<exclamdown>(fst f)"
          unfolding subtype_tuple_def
          by fastforce
        then show ?thesis
          using FieldI1 class_f_in_tmod2 imod2_correct instance_model.validity_type_model_consistent subtype_rel.nullable_proper_classes 
          using subtype_rel.reflexivity subtype_rel_alt subtype_rel_alt_field type_model.structure_inh_wellformed_classes
          by metis
      next
        assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
        then show ?thesis
          unfolding subtype_conv_def
          by blast
      next
        assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
        then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          unfolding subtype_conv_def
          by fastforce
        then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
          unfolding tmod_combine_def
          by simp
        then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
          by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
        then show ?thesis
        proof (elim UnE)
          assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
          then show ?thesis
            using converse_tranclE imod1_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod2 type_model.structure_inh_wellformed_alt
            by metis
        next
          assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
          then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod2))\<^sup>+"
            unfolding subtype_conv_def
            by force
          then show ?thesis
            unfolding subtype_rel_altdef_def
            by simp
        qed
      next
        assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
        then show ?thesis
          unfolding subtype_conv_def
          by blast
      next
        assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
        then show ?thesis
          unfolding subtype_conv_def
          by blast
      qed
      then show "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        unfolding subtype_def
        by (simp add: class_def imod2_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
    qed (simp_all add: assms fields_distinct)
  qed
next
  have fields_distinct: "Field (Tm Imod1) \<inter> Field (Tm Imod2) = {}"
    using imod1_correct imod2_correct instance_model.validity_type_model_consistent 
    using type_model.structure_field_wellformed_class combine_classes_distinct disjoint_iff_not_equal
    by metis
  have containment_relation_altdef: "(object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+ = (object_containments_relation Imod1)\<^sup>+ \<union> (object_containments_relation Imod2)\<^sup>+"
  proof
    have subset_containments: "object_containments_relation (imod_combine Imod1 Imod2) \<subseteq> object_containments_relation Imod1 \<union> object_containments_relation Imod2"
    proof
      fix x
      assume "x \<in> object_containments_relation (imod_combine Imod1 Imod2)"
      then show "x \<in> object_containments_relation Imod1 \<union> object_containments_relation Imod2"
      proof (induct x)
        case (Pair a b)
        then show ?case
        proof (induct)
          case (rule_object_containment o1 o2 r)
          then have o1_in_imods: "o1 \<in> Object Imod1 \<union> Object Imod2"
            unfolding imod_combine_def
            by simp
          have "r \<in> CR (tmod_combine (Tm Imod1) (Tm Imod2))"
            using rule_object_containment.hyps(2)
            unfolding imod_combine_def
            by simp
          then have "r \<in> CR (Tm Imod1) \<union> CR (Tm Imod2)"
            using tmod_combine_containment_relation imod1_correct imod2_correct instance_model.validity_type_model_consistent
            using type_model.structure_fieldsig_wellformed_type type_model.structure_properties_wellfomed fields_distinct empty_iff
            by metis
          then show ?case
            using o1_in_imods
          proof (elim UnE)
            assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
            then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
              by (simp add: CR.simps Type_Model.Rel_def)
            then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
              using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
              using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
              by metis
            then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
              using containment_relations_are_fields
              by blast
            have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
              by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
            then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
              by (fact ProperClassType.rule_proper_classes)
            then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            assume o1_in_imod1: "o1 \<in> Object Imod1"
            then have o1_class_in_tmod1: "ObjectClass Imod1 o1 \<in> Class (Tm Imod1)"
              using imod1_correct instance_model.structure_object_class_wellformed
              by metis
            then have o1_class_not_in_tmod2: "ObjectClass Imod1 o1 \<notin> Class (Tm Imod2)"
              using combine_classes_distinct
              by blast
            then have ob_not_in_imod2: "o1 \<notin> Object Imod2"
              using imod2_correct instance_model.structure_object_class_wellformed o1_in_imod1 structure_object_class_wellformed 
              by fastforce
            have "\<exclamdown>(ObjectClass Imod1 o1) \<in> ProperClassType (Tm Imod1)"
              using o1_class_in_tmod1
              by (fact ProperClassType.rule_proper_classes)
            then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod1 o1) \<in> Type (Tm Imod1)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
              using rule_object_containment.hyps(3)
              unfolding imod_combine_def
              by (simp add: imod_combine_object_class_def o1_in_imod1 ob_not_in_imod2)
            then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
              unfolding Type_Model.fields_def
              by fastforce
            then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
              unfolding subtype_def
              by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
            then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
              subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
              subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
              subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
              subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
              unfolding subtype_rel_altdef_def
              by simp
            then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod1)"
            proof (elim UnE)
              assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
              then have "\<exclamdown>(ObjectClass Imod1 o1) = \<exclamdown>(fst r)"
                unfolding subtype_tuple_def
                by fastforce
              then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (Tm Imod1)"
                unfolding subtype_tuple_def
                using r_in_type_tmod1
                by blast
              then show ?thesis
                unfolding subtype_rel_altdef_def
                by simp
            next
              assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
              then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                unfolding subtype_conv_def
                by fastforce
              then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                unfolding tmod_combine_def
                by simp
              then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
              then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+"
                using UnE o1_class_not_in_tmod2 converse_tranclE eq_fst_iff imod2_correct instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_classes
                by metis
              then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod1))\<^sup>+"
                unfolding subtype_conv_def
                by force
              then show ?thesis
                unfolding subtype_rel_altdef_def
                by simp
            next
              assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            qed
            then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[Tm Imod1] \<exclamdown>(fst r)"
              unfolding subtype_def
              by (simp add: imod1_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
            then have r_in_fields_tmod1: "r \<in> Type_Model.fields (Tm Imod1) (ObjectClass Imod1 o1)"
              unfolding Type_Model.fields_def
              using r_in_field_tmod1
              by fastforce
            have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod1 (o1, r)"
              unfolding imod_combine_def imod_combine_field_value_def
              by (simp add: o1_in_imod1 ob_not_in_imod2 r_in_field_tmod1)
            then have "obj o2 \<in> set (contained_values (FieldValue Imod1 (o1, r)))"
              using rule_object_containment.hyps(4)
              by simp
            then show ?thesis
              using UnI1 o1_in_imod1 object_containments_relation.rule_object_containment r_in_fields_tmod1 r_in_tmod1
              by metis
          next
            assume r_in_tmod1: "r \<in> CR (Tm Imod1)"
            then have r_in_field_tmod1: "r \<in> Field (Tm Imod1)"
              by (simp add: CR.simps Type_Model.Rel_def)
            then have r_not_in_field_tmod2: "r \<notin> Field (Tm Imod2)"
              using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
              using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
              by metis
            then have r_not_in_tmod2: "r \<notin> CR (Tm Imod2)"
              using containment_relations_are_fields
              by blast
            have r_class_in_tmod1: "fst r \<in> Class (Tm Imod1)"
              by (simp add: imod1_correct instance_model.validity_type_model_consistent r_in_field_tmod1 type_model.structure_field_wellformed_class)
            then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod1)"
              by (fact ProperClassType.rule_proper_classes)
            then have r_in_type_tmod1: "\<exclamdown>(fst r) \<in> Type (Tm Imod1)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            assume o1_in_imod2: "o1 \<in> Object Imod2"
            then have o1_class_in_tmod2: "ObjectClass Imod2 o1 \<in> Class (Tm Imod2)"
              using imod2_correct instance_model.structure_object_class_wellformed
              by metis
            then have o1_class_not_in_tmod1: "ObjectClass Imod2 o1 \<notin> Class (Tm Imod1)"
              using combine_classes_distinct
              by blast
            then have ob_not_in_imod1: "o1 \<notin> Object Imod1"
              using imod1_correct instance_model.structure_object_class_wellformed o1_in_imod2 structure_object_class_wellformed 
              by fastforce
            have "\<exclamdown>(ObjectClass Imod2 o1) \<in> ProperClassType (Tm Imod2)"
              using o1_class_in_tmod2
              by (fact ProperClassType.rule_proper_classes)
            then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod2 o1) \<in> Type (Tm Imod2)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            have r_not_field: "r \<notin> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
            proof
              assume "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
              then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
                unfolding Type_Model.fields_def
                by fastforce
              then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
                unfolding subtype_def
                by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
              then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
                subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
                subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
                subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
                subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                unfolding subtype_rel_altdef_def
                by simp
              then show "False"
              proof (elim UnE)
                assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
                then have "\<exclamdown>(ObjectClass Imod2 o1) = \<exclamdown>(fst r)"
                  unfolding subtype_tuple_def
                  by fastforce
                then show ?thesis
                  using o1_class_not_in_tmod1 r_class_in_tmod1
                  by simp
              next
                assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                then show ?thesis
                  unfolding subtype_conv_def
                  by blast
              next
                assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  unfolding subtype_conv_def
                  by fastforce
                then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                  unfolding tmod_combine_def
                  by simp
                then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                  by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
                then show ?thesis
                proof (elim UnE)
                  assume "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+"
                  then show ?thesis
                    using converse_tranclE imod1_correct instance_model.validity_type_model_consistent 
                    using o1_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
                    by metis
                next
                  assume "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod2))\<^sup>+"
                  then show ?thesis
                    using combine_classes_distinct disjoint_iff_not_equal imod2_correct r_class_in_tmod1 trancl.simps 
                    using instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_alt
                    by metis
                qed
              next
                assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
                then show ?thesis
                  unfolding subtype_conv_def
                  by blast
              next
                assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                then show ?thesis
                  unfolding subtype_conv_def
                  by blast
              qed
            qed
            have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
              using rule_object_containment.hyps(3)
              unfolding imod_combine_def
              by (simp add: imod_combine_object_class_def o1_in_imod2 ob_not_in_imod1)
            then show ?thesis
              using r_not_field
              by blast
          next
            assume r_in_tmod2: "r \<in> CR (Tm Imod2)"
            then have r_in_field_tmod2: "r \<in> Field (Tm Imod2)"
              by (simp add: CR.simps Type_Model.Rel_def)
            then have r_not_in_field_tmod1: "r \<notin> Field (Tm Imod1)"
              using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
              using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
              by metis
            then have r_not_in_tmod1: "r \<notin> CR (Tm Imod1)"
              using containment_relations_are_fields
              by blast
            have r_class_in_tmod2: "fst r \<in> Class (Tm Imod2)"
              by (simp add: imod2_correct instance_model.validity_type_model_consistent r_in_field_tmod2 type_model.structure_field_wellformed_class)
            then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod2)"
              by (fact ProperClassType.rule_proper_classes)
            then have r_in_type_tmod2: "\<exclamdown>(fst r) \<in> Type (Tm Imod2)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            assume o1_in_imod1: "o1 \<in> Object Imod1"
            then have o1_class_in_tmod1: "ObjectClass Imod1 o1 \<in> Class (Tm Imod1)"
              using imod1_correct instance_model.structure_object_class_wellformed
              by metis
            then have o1_class_not_in_tmod2: "ObjectClass Imod1 o1 \<notin> Class (Tm Imod2)"
              using combine_classes_distinct
              by blast
            then have ob_not_in_imod2: "o1 \<notin> Object Imod2"
              using imod2_correct instance_model.structure_object_class_wellformed o1_in_imod1 structure_object_class_wellformed 
              by fastforce
            have "\<exclamdown>(ObjectClass Imod1 o1) \<in> ProperClassType (Tm Imod1)"
              using o1_class_in_tmod1
              by (fact ProperClassType.rule_proper_classes)
            then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod1 o1) \<in> Type (Tm Imod1)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            have r_not_field: "r \<notin> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
            proof
              assume "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
              then have "\<exclamdown>(ObjectClass Imod1 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
                unfolding Type_Model.fields_def
                by fastforce
              then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
                unfolding subtype_def
                by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
              then have "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
                subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
                subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
                subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
                subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                unfolding subtype_rel_altdef_def
                by simp
              then show "False"
              proof (elim UnE)
                assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
                then have "\<exclamdown>(ObjectClass Imod1 o1) = \<exclamdown>(fst r)"
                  unfolding subtype_tuple_def
                  by fastforce
                then show ?thesis
                  using o1_class_not_in_tmod2 r_class_in_tmod2
                  by simp
              next
                assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                then show ?thesis
                  unfolding subtype_conv_def
                  by blast
              next
                assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                  unfolding subtype_conv_def
                  by fastforce
                then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                  unfolding tmod_combine_def
                  by simp
                then have "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                  by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
                then show ?thesis
                proof (elim UnE)
                  assume "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+"
                  then show ?thesis
                    using combine_classes_distinct disjoint_iff_not_equal imod1_correct r_class_in_tmod2 trancl.simps 
                    using instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_alt
                    by metis
                next
                  assume "(ObjectClass Imod1 o1, fst r) \<in> (Inh (Tm Imod2))\<^sup>+"
                  then show ?thesis
                    using converse_tranclE imod2_correct instance_model.validity_type_model_consistent 
                    using o1_class_not_in_tmod2 type_model.structure_inh_wellformed_alt
                    by metis
                qed
              next
                assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
                then show ?thesis
                  unfolding subtype_conv_def
                  by blast
              next
                assume "(\<exclamdown>(ObjectClass Imod1 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                then show ?thesis
                  unfolding subtype_conv_def
                  by blast
              qed
            qed
            have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod1 o1)"
              using rule_object_containment.hyps(3)
              unfolding imod_combine_def
              by (simp add: imod_combine_object_class_def o1_in_imod1 ob_not_in_imod2)
            then show ?thesis
              using r_not_field
              by blast
          next
            assume r_in_tmod2: "r \<in> CR (Tm Imod2)"
            then have r_in_field_tmod2: "r \<in> Field (Tm Imod2)"
              by (simp add: CR.simps Type_Model.Rel_def)
            then have r_not_in_field_tmod1: "r \<notin> Field (Tm Imod1)"
              using combine_classes_distinct disjoint_iff_not_equal imod1_correct imod2_correct 
              using instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class
              by metis
            then have r_not_in_tmod1: "r \<notin> CR (Tm Imod1)"
              using containment_relations_are_fields
              by blast
            have r_class_in_tmod2: "fst r \<in> Class (Tm Imod2)"
              by (simp add: imod2_correct instance_model.validity_type_model_consistent r_in_field_tmod2 type_model.structure_field_wellformed_class)
            then have "\<exclamdown>(fst r) \<in> ProperClassType (Tm Imod2)"
              by (fact ProperClassType.rule_proper_classes)
            then have r_in_type_tmod2: "\<exclamdown>(fst r) \<in> Type (Tm Imod2)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            assume o1_in_imod2: "o1 \<in> Object Imod2"
            then have o1_class_in_tmod2: "ObjectClass Imod2 o1 \<in> Class (Tm Imod2)"
              using imod2_correct instance_model.structure_object_class_wellformed
              by metis
            then have o1_class_not_in_tmod1: "ObjectClass Imod2 o1 \<notin> Class (Tm Imod1)"
              using combine_classes_distinct
              by blast
            then have ob_not_in_imod1: "o1 \<notin> Object Imod1"
              using imod1_correct instance_model.structure_object_class_wellformed o1_in_imod2 structure_object_class_wellformed 
              by fastforce
            have "\<exclamdown>(ObjectClass Imod2 o1) \<in> ProperClassType (Tm Imod2)"
              using o1_class_in_tmod2
              by (fact ProperClassType.rule_proper_classes)
            then have o1_class_in_type_tmod1: "\<exclamdown>(ObjectClass Imod2 o1) \<in> Type (Tm Imod2)"
              unfolding Type_def NonContainerType_def ClassType_def
              by simp
            have "r \<in> Type_Model.fields (tmod_combine (Tm Imod1) (Tm Imod2)) (ObjectClass Imod2 o1)"
              using rule_object_containment.hyps(3)
              unfolding imod_combine_def
              by (simp add: imod_combine_object_class_def o1_in_imod2 ob_not_in_imod1)
            then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst r)"
              unfolding Type_Model.fields_def
              by fastforce
            then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
              unfolding subtype_def
              by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
            then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
              subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
              subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
              subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
              subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
              unfolding subtype_rel_altdef_def
              by simp
            then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_rel_altdef (Tm Imod2)"
            proof (elim UnE)
              assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
              then have "\<exclamdown>(ObjectClass Imod2 o1) = \<exclamdown>(fst r)"
                unfolding subtype_tuple_def
                by fastforce
              then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_tuple ` Type (Tm Imod2)"
                unfolding subtype_tuple_def
                using r_in_type_tmod2
                by blast
              then show ?thesis
                unfolding subtype_rel_altdef_def
                by simp
            next
              assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
              then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
                unfolding subtype_conv_def
                by fastforce
              then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
                unfolding tmod_combine_def
                by simp
              then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
                by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
              then have "(ObjectClass Imod2 o1, fst r) \<in> (Inh (Tm Imod2))\<^sup>+"
                using UnE o1_class_not_in_tmod1 converse_tranclE eq_fst_iff imod1_correct instance_model.validity_type_model_consistent type_model.structure_inh_wellformed_classes
                by metis
              then have "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper proper ` (Inh (Tm Imod2))\<^sup>+"
                unfolding subtype_conv_def
                by force
              then show ?thesis
                unfolding subtype_rel_altdef_def
                by simp
            next
              assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            next
              assume "(\<exclamdown>(ObjectClass Imod2 o1), \<exclamdown>(fst r)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
              then show ?thesis
                unfolding subtype_conv_def
                by blast
            qed
            then have "\<exclamdown>(ObjectClass Imod2 o1) \<sqsubseteq>[Tm Imod2] \<exclamdown>(fst r)"
              unfolding subtype_def
              by (simp add: imod2_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
            then have r_in_fields_tmod2: "r \<in> Type_Model.fields (Tm Imod2) (ObjectClass Imod2 o1)"
              unfolding Type_Model.fields_def
              using r_in_field_tmod2
              by fastforce
            have "FieldValue (imod_combine Imod1 Imod2) (o1, r) = FieldValue Imod2 (o1, r)"
              unfolding imod_combine_def imod_combine_field_value_def
              by (simp add: o1_in_imod2 ob_not_in_imod1 r_in_field_tmod2)
            then have object_value_o1: "obj o2 \<in> set (contained_values (FieldValue Imod2 (o1, r)))"
              using rule_object_containment.hyps(4)
              by simp
            then show ?thesis
              using UnI2 o1_in_imod2 object_containments_relation.rule_object_containment r_in_fields_tmod2 r_in_tmod2
              by metis
          qed
        qed
      qed
    qed
    show "(object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+ \<subseteq> (object_containments_relation Imod1)\<^sup>+ \<union> (object_containments_relation Imod2)\<^sup>+"
    proof
      fix x
      assume "x \<in> (object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+"
      then show "x \<in> (object_containments_relation Imod1)\<^sup>+ \<union> (object_containments_relation Imod2)\<^sup>+"
      proof (induct x)
        case (Pair a b)
        then show ?case
        proof (induct)
          case (base y)
          then show ?case
            using subset_containments
            by fastforce
        next
          case (step y z)
          then have "(y, z) \<in> object_containments_relation Imod1 \<union> object_containments_relation Imod2"
            using subset_containments
            by blast
          then show ?case
          proof (elim UnE)
            assume yz_in_imod1: "(y, z) \<in> object_containments_relation Imod1"
            then have y_in_imod1: "y \<in> Object Imod1"
              using object_containments_relation.induct
              by auto
            then have "ObjectClass Imod1 y \<in> Class (Tm Imod1)"
              using imod1_correct instance_model.structure_object_class_wellformed
              by metis
            then have "ObjectClass Imod1 y \<notin> Class (Tm Imod2)"
              using combine_classes_distinct
              by blast
            then have "y \<notin> Object Imod2"
              using imod2_correct instance_model.structure_object_class_wellformed structure_object_class_wellformed y_in_imod1
              by fastforce
            then have "y \<notin> Relation.Field (object_containments_relation Imod2)"
              using imod2_correct object_containments_relation_field
              by blast
            then have "(a, y) \<notin> (object_containments_relation Imod2)\<^sup>+"
              using FieldI2 tranclE
              by metis
            then have "(a, y) \<in> (object_containments_relation Imod1)\<^sup>+"
              using step.hyps(3)
              by blast
            then show ?thesis
              using Un_iff trancl.trancl_into_trancl yz_in_imod1
              by metis
          next
            assume yz_in_imod2: "(y, z) \<in> object_containments_relation Imod2"
            then have y_in_imod2: "y \<in> Object Imod2"
              using object_containments_relation.induct
              by auto
            then have "ObjectClass Imod2 y \<in> Class (Tm Imod2)"
              using imod2_correct instance_model.structure_object_class_wellformed
              by metis
            then have "ObjectClass Imod2 y \<notin> Class (Tm Imod1)"
              using combine_classes_distinct
              by blast
            then have "y \<notin> Object Imod1"
              using imod1_correct instance_model.structure_object_class_wellformed structure_object_class_wellformed y_in_imod2
              by fastforce
            then have "y \<notin> Relation.Field (object_containments_relation Imod1)"
              using imod1_correct object_containments_relation_field
              by blast
            then have "(a, y) \<notin> (object_containments_relation Imod1)\<^sup>+"
              using FieldI2 tranclE
              by metis
            then have "(a, y) \<in> (object_containments_relation Imod2)\<^sup>+"
              using step.hyps(3)
              by blast
            then show ?thesis
              using Un_iff trancl.trancl_into_trancl yz_in_imod2
              by metis
          qed
        qed
      qed
    qed
  next
    have "object_containments_relation Imod1 \<subseteq> object_containments_relation (imod_combine Imod1 Imod2)"
      by (intro imod_combine_object_containments_relation_subset_imod1)
        (simp_all add: assms instance_model.validity_type_model_consistent type_model.structure_fieldsig_wellformed_type instance_model.property_field_values_outside_domain fields_distinct)
    then have subset_imod1: "(object_containments_relation Imod1)\<^sup>+ \<subseteq> (object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+"
      by (simp add: subsetI trancl_mono)
    have "object_containments_relation Imod2 \<subseteq> object_containments_relation (imod_combine Imod1 Imod2)"
      by (intro imod_combine_object_containments_relation_subset_imod2)
        (simp_all add: assms instance_model.validity_type_model_consistent type_model.structure_fieldsig_wellformed_type instance_model.property_field_values_outside_domain fields_distinct)
    then have subset_imod2: "(object_containments_relation Imod2)\<^sup>+ \<subseteq> (object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+"
      by (simp add: subsetI trancl_mono)
    show "(object_containments_relation Imod1)\<^sup>+ \<union> (object_containments_relation Imod2)\<^sup>+ \<subseteq> (object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+"
      by (simp add: subset_imod1 subset_imod2)
  qed
  show "irrefl ((object_containments_relation (imod_combine Imod1 Imod2))\<^sup>+)"
  proof (induct "\<exists>r. containment r \<in> Prop (Tm Imod1)")
    case True
    then show ?case
    proof (induct "\<exists>r. containment r \<in> Prop (Tm Imod2)")
      case True
      have irrefl_imod1: "irrefl ((object_containments_relation Imod1)\<^sup>+)"
        using True.prems imod1_correct instance_model.validity_properties_satisfied property_satisfaction_containment_rev
        by metis
      have irrefl_imod2: "irrefl ((object_containments_relation Imod2)\<^sup>+)"
        using True.hyps imod2_correct instance_model.validity_properties_satisfied property_satisfaction_containment_rev
        by metis
      have "irrefl ((object_containments_relation Imod1)\<^sup>+ \<union> (object_containments_relation Imod2)\<^sup>+)"
        using irrefl_def irrefl_imod1 irrefl_imod2
        by blast
      then show ?case
        by (simp add: containment_relation_altdef)
    next
      case False
      then show ?case
      proof (intro imod_combine_containment_relation_satisfaction_imod1)
        fix ob f
        assume ob_in_imod2: "ob \<in> Object Imod2"
        then have ob_class_in_tmod2: "ObjectClass Imod2 ob \<in> Class (Tm Imod2)"
          using imod2_correct instance_model.structure_object_class_wellformed
          by metis
        then have ob_class_not_in_tmod1: "ObjectClass Imod2 ob \<notin> Class (Tm Imod1)"
          using combine_classes_distinct
          by blast
        then have ob_not_in_imod1: "ob \<notin> Object Imod1"
          using imod1_correct instance_model.structure_object_class_wellformed ob_in_imod2 structure_object_class_wellformed
          by fastforce
        assume f_in_tmod1: "f \<in> Field (Tm Imod1)"
        then have class_f_in_tmod2: "fst f \<in> Class (Tm Imod1)"
          by (simp add: imod1_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
        then have class_f_not_in_tmod2: "fst f \<notin> Class (Tm Imod2)"
          using combine_classes_distinct
          by blast
        have not_extend: "\<not>\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
        proof
          assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
          then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
            unfolding imod_combine_def class_def
            by simp
          then have "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
            using Int_iff imod_combine_object_class_def ob_in_imod2 structure_object_class_wellformed
            by metis
          then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
            unfolding subtype_def
            by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
          then show "False"
            unfolding subtype_rel_altdef_def
          proof (elim UnE)
            assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
            then have "\<exclamdown>(ObjectClass Imod2 ob) = \<exclamdown>(fst f)"
              unfolding subtype_tuple_def
              by fastforce
            then show ?thesis
              using class_f_not_in_tmod2 ob_class_in_tmod2
              by simp
          next
            assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
            then show ?thesis
              unfolding subtype_conv_def
              by blast
          next
            assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
            then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
              unfolding subtype_conv_def
              by fastforce
            then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
              unfolding tmod_combine_def
              by simp
            then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
              by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
            then show ?thesis
            proof (elim UnE)
              assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
              then show ?thesis
                using converse_tranclE imod1_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
                by metis
            next
              assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
              then show ?thesis
                using class_f_not_in_tmod2 imod2_correct instance_model.validity_type_model_consistent snd_conv trancl.simps type_model.structure_inh_wellformed_classes
                by metis
            qed
          next
            assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
            then show ?thesis
              unfolding subtype_conv_def
              by blast
          next
            assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
            then show ?thesis
              unfolding subtype_conv_def
              by blast
          qed
        qed
        assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
        then show "ob \<in> Object Imod1 \<and> \<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
          using not_extend
          by blast
      next
        fix ob f
        assume ob_in_imod1: "ob \<in> Object Imod1"
        then have ob_class_in_tmod1: "ObjectClass Imod1 ob \<in> Class (Tm Imod1)"
          using imod1_correct instance_model.structure_object_class_wellformed
          by metis
        then have ob_class_not_in_tmod1: "ObjectClass Imod1 ob \<notin> Class (Tm Imod2)"
          using combine_classes_distinct
          by blast
        then have ob_not_in_imod2: "ob \<notin> Object Imod2" 
          using imod2_correct instance_model.structure_object_class_wellformed ob_in_imod1 structure_object_class_wellformed
          by fastforce
        assume f_in_tmod1: "f \<in> Field (Tm Imod1)"
        then have class_f_in_tmod1: "fst f \<in> Class (Tm Imod1)"
          by (simp add: imod1_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
        then have class_f_not_in_tmod2: "fst f \<notin> Class (Tm Imod2)"
          using combine_classes_distinct
          by blast
        assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
        then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
          unfolding imod_combine_def class_def
          by simp
        then have "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
          using Int_iff imod_combine_object_class_def ob_in_imod1 structure_object_class_wellformed
          by metis
        then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
          unfolding subtype_def
          by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
        then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
          subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
          subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
          subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
          subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          unfolding subtype_rel_altdef_def
          by simp
        then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod1)"
        proof (elim UnE)
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
          then have "\<exclamdown>(ObjectClass Imod1 ob) = \<exclamdown>(fst f)"
            unfolding subtype_tuple_def
            by fastforce
          then show ?thesis
            using FieldI1 class_f_in_tmod1 imod1_correct instance_model.validity_type_model_consistent subtype_rel.nullable_proper_classes 
            using subtype_rel.reflexivity subtype_rel_alt subtype_rel_alt_field type_model.structure_inh_wellformed_classes
            by metis
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
            unfolding subtype_conv_def
            by fastforce
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
            unfolding tmod_combine_def
            by simp
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
            by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
          then show ?thesis
          proof (elim UnE)
            assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
            then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod1))\<^sup>+"
              unfolding subtype_conv_def
              by force
            then show ?thesis
              unfolding subtype_rel_altdef_def
              by simp
          next
            assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
            then show ?thesis
              using converse_tranclE imod2_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
              by metis
          qed
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        qed
        then show "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[Tm Imod1] \<exclamdown>(class (Tm Imod1) f)"
          unfolding subtype_def
          by (simp add: class_def imod1_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
      qed (simp_all add: assms fields_distinct)
    qed
  next
    case False
    then show ?case
    proof (intro imod_combine_containment_relation_satisfaction_imod2)
      fix ob f
      assume ob_in_imod1: "ob \<in> Object Imod1"
      then have ob_class_in_tmod1: "ObjectClass Imod1 ob \<in> Class (Tm Imod1)"
        using imod1_correct instance_model.structure_object_class_wellformed
        by metis
      then have ob_class_not_in_tmod1: "ObjectClass Imod1 ob \<notin> Class (Tm Imod2)"
        using combine_classes_distinct
        by blast
      then have ob_not_in_imod2: "ob \<notin> Object Imod2"
        using imod2_correct instance_model.structure_object_class_wellformed ob_in_imod1 structure_object_class_wellformed
        by fastforce
      assume f_in_tmod2: "f \<in> Field (Tm Imod2)"
      then have class_f_in_tmod2: "fst f \<in> Class (Tm Imod2)"
        by (simp add: imod2_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
      then have class_f_not_in_tmod1: "fst f \<notin> Class (Tm Imod1)"
        using combine_classes_distinct
        by blast
      have not_extend: "\<not>\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
      proof
        assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
        then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
          unfolding imod_combine_def class_def
          by simp
        then have "\<exclamdown>(ObjectClass Imod1 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
          using Int_iff imod_combine_object_class_def ob_in_imod1 structure_object_class_wellformed
          by metis
        then have "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
          unfolding subtype_def
          by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
        then show "False"
          unfolding subtype_rel_altdef_def
        proof (elim UnE)
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
          then have "\<exclamdown>(ObjectClass Imod1 ob) = \<exclamdown>(fst f)"
            unfolding subtype_tuple_def
            by fastforce
          then show ?thesis
            using class_f_not_in_tmod1 ob_class_in_tmod1
            by simp
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
            unfolding subtype_conv_def
            by fastforce
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
            unfolding tmod_combine_def
            by simp
          then have "((ObjectClass Imod1 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
            by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
          then show ?thesis
          proof (elim UnE)
            assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
            then show ?thesis
              using class_f_not_in_tmod1 imod1_correct instance_model.validity_type_model_consistent snd_conv trancl.simps type_model.structure_inh_wellformed_classes
              by metis
          next
            assume "(ObjectClass Imod1 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
            then show ?thesis
              using converse_tranclE imod2_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod1 type_model.structure_inh_wellformed_alt
              by metis
          qed
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        next
          assume "(\<exclamdown>(ObjectClass Imod1 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          then show ?thesis
            unfolding subtype_conv_def
            by blast
        qed
      qed
      assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
      then show "ob \<in> Object Imod2 \<and> \<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        using not_extend
        by blast
    next
      fix ob f
      assume ob_in_imod2: "ob \<in> Object Imod2"
      then have ob_class_in_tmod2: "ObjectClass Imod2 ob \<in> Class (Tm Imod2)"
        using imod2_correct instance_model.structure_object_class_wellformed
        by metis
      then have ob_class_not_in_tmod2: "ObjectClass Imod2 ob \<notin> Class (Tm Imod1)"
        using combine_classes_distinct
        by blast
      then have ob_not_in_imod1: "ob \<notin> Object Imod1" 
        using imod1_correct instance_model.structure_object_class_wellformed ob_in_imod2 structure_object_class_wellformed
        by fastforce
      assume f_in_tmod2: "f \<in> Field (Tm Imod2)"
      then have class_f_in_tmod2: "fst f \<in> Class (Tm Imod2)"
        by (simp add: imod2_correct instance_model.validity_type_model_consistent type_model.structure_field_wellformed_class)
      then have class_f_not_in_tmod1: "fst f \<notin> Class (Tm Imod1)"
        using combine_classes_distinct
        by blast
      assume "\<exclamdown>(ObjectClass (imod_combine Imod1 Imod2) ob) \<sqsubseteq>[Tm (imod_combine Imod1 Imod2)] \<exclamdown>(class (Tm (imod_combine Imod1 Imod2)) f)"
      then have "\<exclamdown>(imod_combine_object_class Imod1 Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
        unfolding imod_combine_def class_def
        by simp
      then have "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[tmod_combine (Tm Imod1) (Tm Imod2)] \<exclamdown>(fst f)"
        using Int_iff imod_combine_object_class_def ob_in_imod2 structure_object_class_wellformed
        by metis
      then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (tmod_combine (Tm Imod1) (Tm Imod2))"
        unfolding subtype_def
        by (simp add: subtype_rel_alt type_model.structure_inh_wellformed_classes validity_type_model_consistent)
      then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2)) \<union> 
        subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union> 
        subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+ \<union>
        subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2)) \<union>
        subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
        unfolding subtype_rel_altdef_def
        by simp
      then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_rel_altdef (Tm Imod2)"
      proof (elim UnE)
        assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_tuple ` Type (tmod_combine (Tm Imod1) (Tm Imod2))"
        then have "\<exclamdown>(ObjectClass Imod2 ob) = \<exclamdown>(fst f)"
          unfolding subtype_tuple_def
          by fastforce
        then show ?thesis
          using FieldI1 class_f_in_tmod2 imod2_correct instance_model.validity_type_model_consistent subtype_rel.nullable_proper_classes 
          using subtype_rel.reflexivity subtype_rel_alt subtype_rel_alt_field type_model.structure_inh_wellformed_classes
          by metis
      next
        assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv nullable nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
        then show ?thesis
          unfolding subtype_conv_def
          by blast
      next
        assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
        then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
          unfolding subtype_conv_def
          by fastforce
        then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1) \<union> Inh (Tm Imod2))\<^sup>+"
          unfolding tmod_combine_def
          by simp
        then have "((ObjectClass Imod2 ob), (fst f)) \<in> (Inh (Tm Imod1))\<^sup>+ \<union> (Inh (Tm Imod2))\<^sup>+"
          by (simp add: combine_classes_distinct imod1_correct imod2_correct instance_model.validity_type_model_consistent)
        then show ?thesis
        proof (elim UnE)
          assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod1))\<^sup>+"
          then show ?thesis
            using converse_tranclE imod1_correct instance_model.validity_type_model_consistent ob_class_not_in_tmod2 type_model.structure_inh_wellformed_alt
            by metis
        next
          assume "(ObjectClass Imod2 ob, fst f) \<in> (Inh (Tm Imod2))\<^sup>+"
          then have "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper proper ` (Inh (Tm Imod2))\<^sup>+"
            unfolding subtype_conv_def
            by force
          then show ?thesis
            unfolding subtype_rel_altdef_def
            by simp
        qed
      next
        assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` subtype_tuple ` Class (tmod_combine (Tm Imod1) (Tm Imod2))"
        then show ?thesis
          unfolding subtype_conv_def
          by blast
      next
        assume "(\<exclamdown>(ObjectClass Imod2 ob), \<exclamdown>(fst f)) \<in> subtype_conv proper nullable ` (Inh (tmod_combine (Tm Imod1) (Tm Imod2)))\<^sup>+"
        then show ?thesis
          unfolding subtype_conv_def
          by blast
      qed
      then show "\<exclamdown>(ObjectClass Imod2 ob) \<sqsubseteq>[Tm Imod2] \<exclamdown>(class (Tm Imod2) f)"
        unfolding subtype_def
        by (simp add: class_def imod2_correct instance_model.validity_type_model_consistent subtype_rel_alt type_model.structure_inh_wellformed_classes)
    qed (simp_all add: assms fields_distinct)
  qed
qed (simp_all add: assms)

end