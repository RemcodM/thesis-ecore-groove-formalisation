theory Multiplicity
  imports Main
begin

section "Linear order of \<M>, which is the set of natural numbers \<union> {\<star>}"

datatype \<M> = Star | Nr nat

notation
  Star ("(\<^emph>)" 1000) and
  Nr ("(\<^bold>_)" [1000] 1000)

instantiation \<M> :: linorder
begin

fun less_eq_\<M> :: "\<M> \<Rightarrow> \<M> \<Rightarrow> bool" where
"less_eq_\<M> _ \<^emph> = True" |
"less_eq_\<M> (\<^bold>a) (\<^bold>b) = (a \<le> b)" | 
"less_eq_\<M> _ _ = False"

fun less_\<M> :: "\<M> \<Rightarrow> \<M> \<Rightarrow> bool" where
"less_\<M> (\<^bold>_) \<^emph> = True" |
"less_\<M> (\<^bold>a) (\<^bold>b) = (a < b)" |
"less_\<M> _ _ = False"

instance proof
  fix x y z :: \<M>
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  proof (induction x arbitrary: y)
    case Star
    then show ?case by simp_all
  next
    case (Nr x)
    then show ?case by (cases y) auto
  qed

  show "x \<le> x" by (induction x) simp_all
  then show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  proof (induction x arbitrary: y)
    case Star
    then show ?case by (cases y) simp_all
  next
    case (Nr x)
    then show ?case by (cases y) simp_all
  qed

  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  proof (induction x arbitrary: y z)
    case Star
    then show ?case by (cases y) simp_all
  next
    case (Nr x)
    then show ?case
    proof (induction y arbitrary: z)
      case Star
      then show ?case by (cases z) simp_all
    next
      case (Nr x)
      then show ?case by (cases z) simp_all
    qed
  qed

  show "x \<le> y \<or> y \<le> x"
  proof (induction x arbitrary: y)
    case Star
    then show ?case by simp
  next
    case (Nr x)
    then show ?case by (cases y) auto
  qed
qed

end



section "Definition of multiplicity"

type_synonym multiplicity = "\<M> \<times> \<M>"

definition lower :: "multiplicity \<Rightarrow> \<M>" where
  "lower m \<equiv> fst m"

declare lower_def[simp add]

definition upper :: "multiplicity \<Rightarrow> \<M>" where
  "upper m \<equiv> snd m"

declare upper_def[simp add]

locale multiplicity = fixes mult :: "multiplicity"
  assumes lower_bound_valid[simp]: "lower mult \<noteq> \<^emph>"
  assumes upper_bound_valid: "upper mult \<noteq> \<^bold>0"
  assumes properly_bounded[simp]: "lower mult \<le> upper mult"

context multiplicity
begin

lemma upper_bound_valid_alt[simp]: "upper mult \<ge> \<^bold>1"
  using less_\<M>.elims not_less upper_bound_valid by fastforce

end

abbreviation multiplicity_notation :: "\<M> \<Rightarrow> \<M> \<Rightarrow> multiplicity" ("(_/.._)" [52, 52] 51) where
  "l..u \<equiv> (l,u)"

definition within_multiplicity :: "nat \<Rightarrow> multiplicity \<Rightarrow> bool" (infixl "in" 50) where
  "n in m \<equiv> lower m \<le> \<^bold>n \<and> \<^bold>n \<le> upper m"

theorem mult_zero_unbounded_valid[simp]: "n in \<^bold>0..\<^emph>"
  unfolding within_multiplicity_def
  by simp

theorem mult_single_value_bound[simp]: "n in \<^bold>m..\<^bold>m \<Longrightarrow> n = m"
  unfolding within_multiplicity_def
  by auto



section "Intersection of multiplicities"

definition mult_intersect :: "multiplicity \<Rightarrow> multiplicity \<Rightarrow> multiplicity" where
  "mult_intersect m1 m2 \<equiv> (max (lower m1) (lower m2))..(min (upper m1) (upper m2))"

abbreviation mult_intersect_notation :: "multiplicity \<Rightarrow> multiplicity \<Rightarrow> multiplicity" ("(_ \<sqinter> _)" [52, 52] 51) where
  "m1 \<sqinter> m2 \<equiv> mult_intersect m1 m2"

lemma mult_intersect_identity[simp]: "m \<sqinter> (\<^bold>0..\<^emph>) = m"
proof
  show "fst (m \<sqinter> (\<^bold>0..\<^emph>)) = fst m"
    unfolding mult_intersect_def
    using less_eq_\<M>.elims(3) max.absorb1
    by fastforce
next
  show "snd (m \<sqinter> (\<^bold>0..\<^emph>)) = snd m"
    unfolding mult_intersect_def
    by (simp add: min_absorb1)
qed

lemma mult_intersect_commute[simp]: "m1 \<sqinter> m2 = m2 \<sqinter> m1"
  by (simp add: max.commute min.commute mult_intersect_def)

lemma mult_intersect_assoc[simp]: "(m1 \<sqinter> m2) \<sqinter> m3 = m1 \<sqinter> (m2 \<sqinter> m3)"
  unfolding mult_intersect_def
  by (simp add: max.assoc min.assoc)

lemma mult_intersect_idemp[simp]: "m \<sqinter> m = m"
  unfolding mult_intersect_def
  by simp

lemma mult_intersect_invalid[simp]: "m \<sqinter> (\<^emph>..\<^bold>0) = (\<^emph>..\<^bold>0)"
proof
  show "fst (m \<sqinter> (\<^emph>..\<^bold>0)) = fst (\<^emph>..\<^bold>0)"
    unfolding mult_intersect_def
    by (simp add: max.absorb2)
next
  show "snd (m \<sqinter> (\<^emph>..\<^bold>0)) = snd (\<^emph>..\<^bold>0)"
    unfolding mult_intersect_def
    using less_eq_\<M>.elims(3) min.absorb2
    by fastforce
qed

theorem mult_intersect_correct[simp]: "multiplicity m1 \<Longrightarrow> multiplicity m2 \<Longrightarrow> max (lower m1) (lower m2) \<le> min (upper m1) (upper m2) \<Longrightarrow> multiplicity (m1 \<sqinter> m2)"
proof
  fix m1 m2
  assume m1_is_multiplicity: "multiplicity m1"
  assume m2_is_multiplicity: "multiplicity m2"
  have lower_bound_m1_valid: "lower m1 \<noteq> \<^emph>"
    using m1_is_multiplicity multiplicity.lower_bound_valid by auto
  have lower_bound_m2_valid: "lower m2 \<noteq> \<^emph>"
    using m2_is_multiplicity multiplicity.lower_bound_valid by auto
  have intersect_lower_def: "lower (m1 \<sqinter> m2) = max (lower m1) (lower m2)"
    by (simp add: mult_intersect_def)
  then show "lower (m1 \<sqinter> m2) \<noteq> \<^emph>"
    using lower_bound_m1_valid lower_bound_m2_valid max_def
    by metis
  have upper_bound_m1_valid: "upper m1 \<noteq> \<^bold>0"
    using m1_is_multiplicity multiplicity.upper_bound_valid by auto
  have upper_bound_m2_valid: "upper m2 \<noteq> \<^bold>0"
    using m2_is_multiplicity multiplicity.upper_bound_valid by auto
  have intersect_upper_def: "upper (m1 \<sqinter> m2) = min (upper m1) (upper m2)"
    by (simp add: mult_intersect_def)
  then show "upper (m1 \<sqinter> m2) \<noteq> \<^bold>0"
    using min_def upper_bound_m1_valid upper_bound_m2_valid
    by metis
  assume "max (lower m1) (lower m2) \<le> min (upper m1) (upper m2)"
  then show "lower (m1 \<sqinter> m2) \<le> upper (m1 \<sqinter> m2)"
    using intersect_lower_def intersect_upper_def by auto
qed

lemma mult_intersect_eq[simp]: "m = m \<sqinter> m"
  by (simp add: mult_intersect_def)

end