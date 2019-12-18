theory Multiplicity_Pair
  imports 
    Main
    Ecore.Multiplicity
begin

section "Definition of a multiplicity pair"

type_synonym multiplicity_pair = "multiplicity \<times> multiplicity"

definition m_in :: "multiplicity_pair \<Rightarrow> multiplicity" where
  "m_in p = fst p"

declare m_in_def[simp add]

definition m_out :: "multiplicity_pair \<Rightarrow> multiplicity" where
  "m_out p = snd p"

declare m_out_def[simp add]

lemma multiplicity_pair_in_out: "\<And>mp. mp = (mp_in, mp_out) \<Longrightarrow> m_in mp = mp_in \<and> m_out mp = mp_out"
  by auto

locale multiplicity_pair = fixes mult_pair :: "multiplicity_pair"
  assumes in_mult_is_mult: "multiplicity (m_in mult_pair)"
  assumes out_mult_is_mult: "multiplicity (m_out mult_pair)"

context multiplicity_pair
begin

lemma in_mult_lower_bound_valid[simp]: "lower (m_in mult_pair) \<noteq> \<^emph>"
  using in_mult_is_mult multiplicity_def by simp

lemma in_mult_upper_bound_valid[simp]: "upper (m_in mult_pair) \<noteq> \<^bold>0"
  using in_mult_is_mult multiplicity_def by simp

lemma in_mult_properly_bounded[simp]: "lower (m_in mult_pair) \<le> upper (m_in mult_pair)"
  using in_mult_is_mult multiplicity_def by simp

lemma out_mult_lower_bound_valid[simp]: "lower (m_out mult_pair) \<noteq> \<^emph>"
  using out_mult_is_mult multiplicity_def by simp

lemma out_mult_upper_bound_valid[simp]: "upper (m_out mult_pair) \<noteq> \<^bold>0"
  using out_mult_is_mult multiplicity_def by simp

lemma out_mult_properly_bounded[simp]: "lower (m_out mult_pair) \<le> upper (m_out mult_pair)"
  using out_mult_is_mult multiplicity_def by simp

end



section "Definition of intersection of a multiplicity pair"

definition mult_pair_intersect :: "multiplicity_pair \<Rightarrow> multiplicity_pair \<Rightarrow> multiplicity_pair" where
  "mult_pair_intersect mp1 mp2 \<equiv> (m_in mp1 \<sqinter> m_in mp2, m_out mp1 \<sqinter> m_out mp2)"

lemma mult_pair_intersect_identity[simp]: "mult_pair_intersect mp (\<^bold>0..\<^emph>, \<^bold>0..\<^emph>) = mp"
  unfolding mult_pair_intersect_def
  by simp

lemma mult_pair_intersect_commute[simp]: "mult_pair_intersect mp1 mp2 = mult_pair_intersect mp2 mp1"
  unfolding mult_pair_intersect_def
  by simp

lemma mult_pair_intersect_assoc[simp]: "mult_pair_intersect (mult_pair_intersect mp1 mp2) mp3 = mult_pair_intersect mp1 (mult_pair_intersect mp2 mp3)"
  unfolding mult_pair_intersect_def
  using mult_intersect_assoc 
  by simp

lemma mult_pair_intersect_idemp[simp]: "mult_pair_intersect mp mp = mp"
  unfolding mult_pair_intersect_def
  by simp

lemma mult_pair_intersect_correct[simp]: "\<And>mp1 mp2. multiplicity (m_in mp1 \<sqinter> m_in mp2) \<Longrightarrow> multiplicity (m_out mp1 \<sqinter> m_out mp2) \<Longrightarrow> multiplicity_pair (mult_pair_intersect mp1 mp2)"
  by (simp add: mult_pair_intersect_def multiplicity_pair_def)

lemma mult_pair_intersect_correct_alt: "\<And>mp1 mp2. multiplicity_pair mp1 \<Longrightarrow> multiplicity_pair mp2 \<Longrightarrow> max (lower (m_in mp1)) (lower (m_in mp2)) \<le> min (upper (m_in mp1)) (upper (m_in mp2)) \<Longrightarrow> max (lower (m_out mp1)) (lower (m_out mp2)) \<le> min (upper (m_out mp1)) (upper (m_out mp2)) \<Longrightarrow> multiplicity_pair (mult_pair_intersect mp1 mp2)"
  using mult_intersect_correct mult_pair_intersect_correct multiplicity_pair.in_mult_is_mult multiplicity_pair.out_mult_is_mult by auto

lemma mult_pair_intersect_eq[simp]: "\<And>mp. mp = mult_pair_intersect mp mp"
  using mult_pair_intersect_def by auto

lemma mult_pair_intersect_in_eq[simp]: "\<And>mp1 mp2. m_in mp1 = m_in mp2 \<Longrightarrow> m_in (mult_pair_intersect mp1 mp2) = m_in mp1"
  by (simp add: mult_intersect_def mult_pair_intersect_def)

lemma mult_pair_intersect_in_eq_alt[simp]: "\<And>mp1 mp2. m_in mp1 = m_in mp2 \<Longrightarrow> m_in (mult_pair_intersect mp1 mp2) = m_in mp2"
  by (simp add: mult_intersect_def mult_pair_intersect_def)

lemma mult_pair_intersect_out_eq[simp]: "\<And>mp1 mp2. m_out mp1 = m_out mp2 \<Longrightarrow> m_out (mult_pair_intersect mp1 mp2) = m_out mp1"
  by (simp add: mult_intersect_def mult_pair_intersect_def)

lemma mult_pair_intersect_out_eq_alt[simp]: "\<And>mp1 mp2. m_out mp1 = m_out mp2 \<Longrightarrow> m_out (mult_pair_intersect mp1 mp2) = m_out mp2"
  by (simp add: mult_intersect_def mult_pair_intersect_def)

end
