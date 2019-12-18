theory Instance_Graph_Retype
  imports 
    Instance_Graph_Combination
begin

section "Validity of instance graphs when changing type graph"

definition instance_graph_retype :: "('lt) type_graph \<Rightarrow> ('nt, 'lt, 'id) instance_graph \<Rightarrow> ('nt, 'lt, 'id) instance_graph" where
  "instance_graph_retype newTG IG \<equiv> \<lparr>
    TG = newTG,
    Id = Id IG,
    N = N IG,
    E = E IG,
    ident = ident IG
  \<rparr>"

lemma instance_graph_retype_identity[simp]: "instance_graph_retype (TG IG) IG = IG"
  unfolding instance_graph_retype_def
  by simp

lemma instance_graph_retype_identity_correct[simp]: "instance_graph IG \<Longrightarrow> instance_graph (instance_graph_retype (TG IG) IG)"
  by simp

lemma instance_graph_retype_combine_empty_correct[simp]:
  assumes type_graph_valid: "type_graph newTG"
  shows "instance_graph (instance_graph_retype newTG ig_empty)"
  unfolding instance_graph_retype_def
  using ig_empty_any_type_graph_correct assms
  by simp

lemma instance_graph_retype_combine_correct[intro]:
  assumes instance_graph_valid: "instance_graph IG"
  assumes type_graph_second_valid: "type_graph TG2"
  assumes type_graph_combination_valid: "type_graph (tg_combine (TG IG) TG2)"
  assumes validity_outgoing_mult: "\<And>et n. et \<in> ET (TG IG) \<union> ET TG2 \<Longrightarrow> n \<in> N IG \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et)"
  assumes validity_ingoing_mult: "\<And>et n. et \<in> ET (TG IG) \<union> ET TG2 \<Longrightarrow> n \<in> N IG \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et)"
  assumes validity_contained_node: "\<And>n. n \<in> N IG \<Longrightarrow> card { e \<in> E IG. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG) \<union> contains TG2 } \<le> 1"
  assumes validity_containment: "irrefl ((edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) \<union> contains TG2})\<^sup>+)"
  shows "instance_graph (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
proof (intro instance_graph.intro)
  fix n
  assume "n \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  then have "n \<in> N IG"
    unfolding instance_graph_retype_def
    by simp
  then show "n \<in> Node"
    using instance_graph_valid instance_graph.structure_nodes_wellformed
    by blast
next
  fix s l t
  assume "(s, l, t) \<in> E (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  then have "(s, l, t) \<in> E IG"
    unfolding instance_graph_retype_def
    by simp
  then show "s \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG) \<and> 
    l \<in> ET (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG)) \<and>
    t \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  proof (intro conjI)
    assume "(s, l, t) \<in> E IG"
    then have "s \<in> N IG"
      using instance_graph_valid instance_graph.structure_edges_wellformed_src_node
      by blast
    then show "s \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
      unfolding instance_graph_retype_def
      by simp
  next
    assume "(s, l, t) \<in> E IG"
    then have "l \<in> ET (TG IG)"
      using instance_graph_valid instance_graph.structure_edges_wellformed_edge_type
      by blast
    then show "l \<in> ET (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))"
      unfolding instance_graph_retype_def tg_combine_def
      by simp
  next
    assume "(s, l, t) \<in> E IG"
    then have "t \<in> N IG"
      using instance_graph_valid instance_graph.structure_edges_wellformed_tgt_node
      by blast
    then show "t \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
      unfolding instance_graph_retype_def
      by simp
  qed
next
  fix i
  assume "i \<in> Id (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  then have "i \<in> Id IG"
    unfolding instance_graph_retype_def
    by simp
  then have "ident IG i \<in> N IG \<and> type\<^sub>n (ident IG i) \<in> Lab\<^sub>t"
    using instance_graph_valid instance_graph.structure_ident_wellformed
    by metis
  then show "ident (instance_graph_retype (tg_combine (TG IG) TG2) IG) i \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG) \<and> type\<^sub>n (ident (instance_graph_retype (tg_combine (TG IG) TG2) IG) i) \<in> Lab\<^sub>t"
    unfolding instance_graph_retype_def
    by simp
next
  fix i
  assume "i \<notin> Id (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  then have "i \<notin> Id IG"
    unfolding instance_graph_retype_def
    by simp
  then have "ident IG i = undefined"
    using instance_graph_valid instance_graph.structure_ident_domain
    by metis
  then show "ident (instance_graph_retype (tg_combine (TG IG) TG2) IG) i = undefined"
    unfolding instance_graph_retype_def
    by simp
next
  have "type_graph (tg_combine (TG IG) TG2)"
    by (fact assms)
  then show "type_graph (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))"
    unfolding instance_graph_retype_def
    by simp
next
  fix n
  assume "n \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  then have "n \<in> N IG"
    unfolding instance_graph_retype_def
    by simp
  then have "type\<^sub>n n \<in> NT (TG IG)"
    using instance_graph_valid instance_graph.validity_node_typed
    by blast
  then show "type\<^sub>n n \<in> NT (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))"
    unfolding instance_graph_retype_def tg_combine_def
    by simp
next
  fix e
  assume "e \<in> E (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  then have "e \<in> E IG"
    unfolding instance_graph_retype_def
    by simp
  then have "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG IG)"
    using instance_graph_valid instance_graph.validity_edge_src_typed
    by blast
  then show "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))"
    unfolding instance_graph_retype_def tg_combine_def
    by auto
next
  fix e
  assume "e \<in> E (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  then have "e \<in> E IG"
    unfolding instance_graph_retype_def
    by simp
  then have "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG IG)"
    using instance_graph_valid instance_graph.validity_edge_tgt_typed
    by blast
  then show "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))"
    unfolding instance_graph_retype_def tg_combine_def
    by auto
next
  fix n
  assume "n \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  then have n_in_ig: "n \<in> N IG"
    unfolding instance_graph_retype_def
    by simp
  then have "type\<^sub>n n \<notin> abs (TG IG)"
    using instance_graph_valid instance_graph.validity_abs_no_instances
    by blast
  then have "type\<^sub>n n \<notin> (abs (TG IG) - NT TG2) \<union> (abs TG2 - NT (TG IG)) \<union> (abs (TG IG) \<inter> abs TG2)"
    using n_in_ig instance_graph.validity_node_typed instance_graph_valid 
    by fastforce
  then show "type\<^sub>n n \<notin> abs (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))"
    unfolding instance_graph_retype_def tg_combine_def
    by simp
next
  fix et n
  assume "et \<in> ET (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))"
  then have et_in_ef: "et \<in> ET (TG IG) \<union> ET TG2"
    unfolding instance_graph_retype_def tg_combine_def
    by simp
  assume "n \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  then have n_in_in: "n \<in> N IG"
    unfolding instance_graph_retype_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> inh (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))"
  then have type_extend: "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+"
    unfolding instance_graph_retype_def tg_combine_def
    by simp
  have "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in
       m_out (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et)"
    using et_in_ef n_in_in type_extend
    by (fact assms)
  then show "card {e \<in> E (instance_graph_retype (tg_combine (TG IG) TG2) IG). src e = n \<and> type\<^sub>e e = et} in
       m_out (mult (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG)) et)"
    unfolding instance_graph_retype_def tg_combine_def
    by simp
next
  fix et n
  assume "et \<in> ET (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))"
  then have et_in_ef: "et \<in> ET (TG IG) \<union> ET TG2"
    unfolding instance_graph_retype_def tg_combine_def
    by simp
  assume "n \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  then have n_in_in: "n \<in> N IG"
    unfolding instance_graph_retype_def
    by simp
  assume "(type\<^sub>n n, tgt et) \<in> inh (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))"
  then have type_extend: "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+"
    unfolding instance_graph_retype_def tg_combine_def
    by simp
  have "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in
       m_in (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et)"
    using et_in_ef n_in_in type_extend
    by (fact assms)
  then show "card {e \<in> E (instance_graph_retype (tg_combine (TG IG) TG2) IG). tgt e = n \<and> type\<^sub>e e = et} in
       m_in (mult (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG)) et)"
    unfolding instance_graph_retype_def tg_combine_def
    by simp
next
  fix n
  assume "n \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
  then have "n \<in> N IG"
    unfolding instance_graph_retype_def
    by simp
  then have "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG) \<union> contains TG2} \<le> 1"
    by (fact assms)
  then show "card {e \<in> E (instance_graph_retype (tg_combine (TG IG) TG2) IG). tgt e = n \<and> type\<^sub>e e \<in> contains (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))} \<le> 1"
    unfolding instance_graph_retype_def tg_combine_def
    by simp
next
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj (instance_graph_retype (tg_combine (TG IG) TG2) IG)) p"
  proof (intro validity_containmentI)
    show "\<And>e. e \<in> E (instance_graph_retype (tg_combine (TG IG) TG2) IG) \<Longrightarrow> type\<^sub>e e \<in> contains (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG)) \<Longrightarrow> 
      src e \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG) \<and> tgt e \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
    proof (intro conjI)
      fix e
      assume "e \<in> E (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
      then have "e \<in> E IG"
        unfolding instance_graph_retype_def
        by simp
      then have "src e \<in> N IG"
        using instance_graph_valid instance_graph.structure_edges_wellformed_src_node_alt
        by blast
      then show "src e \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
        unfolding instance_graph_retype_def
        by simp
    next
      fix e
      assume "e \<in> E (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
      then have "e \<in> E IG"
        unfolding instance_graph_retype_def
        by simp
      then have "tgt e \<in> N IG"
        using instance_graph_valid instance_graph.structure_edges_wellformed_tgt_node_alt
        by blast
      then show "tgt e \<in> N (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
        unfolding instance_graph_retype_def
        by simp
    qed
  next
    have "irrefl ((edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) \<union> contains TG2})\<^sup>+)"
      by (fact validity_containment)
    then show "irrefl ((edge_to_tuple ` {e \<in> E (instance_graph_retype (tg_combine (TG IG) TG2) IG). type\<^sub>e e \<in> contains (TG (instance_graph_retype (tg_combine (TG IG) TG2) IG))})\<^sup>+)"
      unfolding instance_graph_retype_def tg_combine_def
      by simp
  qed
qed

lemma instance_graph_retype_combine_merge_correct[intro]:
  assumes instance_graph_valid: "instance_graph IG"
  assumes type_graph_second_valid: "type_graph TG2"
  assumes type_graph_combination_valid: "type_graph (tg_combine (TG IG) TG2)"
  assumes combine_edges_distinct: "ET (TG IG) \<inter> ET TG2 = {}"
  assumes validity_outgoing_mult_first: "\<And>et n. et \<in> ET (TG IG) \<Longrightarrow> n \<in> N IG \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG) et)"
  assumes validity_outgoing_mult_second: "\<And>et n. et \<in> ET TG2 \<Longrightarrow> n \<in> N IG \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+ \<Longrightarrow> 0 in m_out (mult TG2 et)"
  assumes validity_ingoing_mult_first: "\<And>et n. et \<in> ET (TG IG) \<Longrightarrow> n \<in> N IG \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG) et)"
  assumes validity_ingoing_mult_second: "\<And>et n. et \<in> ET TG2 \<Longrightarrow> n \<in> N IG \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+ \<Longrightarrow> 0 in m_in (mult TG2 et)"
  shows "instance_graph (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
proof (intro instance_graph_retype_combine_correct)
  fix et n
  assume et_in_tg_e: "et \<in> ET (TG IG) \<union> ET TG2"
  assume n_in_in_ig: "n \<in> N IG"
  assume edge_of_type: "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+"
  show "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et)"
    using et_in_tg_e n_in_in_ig edge_of_type
  proof (elim UnE)
    assume et_in_e: "et \<in> ET (TG IG)"
    then have mult_et: "m_out (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et) = m_out (mult (TG IG) et)"
      unfolding tg_combine_mult_def
      by (simp add: combine_edges_distinct)
    have "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG) et)"
      using et_in_e n_in_in_ig edge_of_type
      by (fact validity_outgoing_mult_first)
    then show "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et)"
      using mult_et
      by simp
  next
    assume et_in_e: "et \<in> ET TG2"
    then have "\<And>e. e \<in> E IG \<Longrightarrow> src e = n \<and> type\<^sub>e e = et \<Longrightarrow> False"
      using combine_edges_distinct disjoint_iff_not_equal instance_graph.structure_edges_wellformed_edge_type_alt instance_graph_valid
      by metis
    then have "{e \<in> E IG. src e = n \<and> type\<^sub>e e = et} = {}"
      by blast
    then have card_zero: "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} = 0"
      using card_empty
      by metis
    have mult_et: "m_out (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et) = m_out (mult TG2 et)"
      unfolding tg_combine_mult_def
      using et_in_e combine_edges_distinct 
      by auto
    have "0 in m_out (mult TG2 et)"
      using et_in_e n_in_in_ig edge_of_type
      by (fact validity_outgoing_mult_second)
    then show "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et)"
      using card_zero mult_et
      by simp
  qed
next
  fix et n
  assume et_in_tg_e: "et \<in> ET (TG IG) \<union> ET TG2"
  assume n_in_in_ig: "n \<in> N IG"
  assume edge_of_type: "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+"
  show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et)"
    using et_in_tg_e n_in_in_ig edge_of_type
  proof (elim UnE)
    assume et_in_e: "et \<in> ET (TG IG)"
    then have mult_et: "m_in (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et) = m_in (mult (TG IG) et)"
      unfolding tg_combine_mult_def
      by (simp add: combine_edges_distinct)
    have "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG) et)"
      using et_in_e n_in_in_ig edge_of_type
      by (fact validity_ingoing_mult_first)
    then show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et)"
      using mult_et
      by simp
  next
    assume et_in_e: "et \<in> ET TG2"
    then have "\<And>e. e \<in> E IG \<Longrightarrow> tgt e = n \<and> type\<^sub>e e = et \<Longrightarrow> False"
      using combine_edges_distinct disjoint_iff_not_equal instance_graph.structure_edges_wellformed_edge_type_alt instance_graph_valid
      by metis
    then have "{e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} = {}"
      by blast
    then have card_zero: "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} = 0"
      using card_empty
      by metis
    have mult_et: "m_in (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et) = m_in (mult TG2 et)"
      unfolding tg_combine_mult_def
      using et_in_e combine_edges_distinct 
      by auto
    have "0 in m_in (mult TG2 et)"
      using et_in_e n_in_in_ig edge_of_type
      by (fact validity_ingoing_mult_second)
    then show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (tg_combine_mult (ET (TG IG)) (mult (TG IG)) (ET TG2) (mult TG2) et)"
      using card_zero mult_et
      by simp
  qed
next
  fix n
  assume n_in_in_ig: "n \<in> N IG"
  have "\<And>e. e \<in> E IG \<Longrightarrow> type\<^sub>e e \<notin> contains TG2"
  proof-
    fix e
    assume "e \<in> E IG"
    then have "type\<^sub>e e \<in> ET (TG IG)"
      using instance_graph_valid instance_graph.structure_edges_wellformed_edge_type_alt
      by blast
    then have "type\<^sub>e e \<notin> ET TG2"
      using combine_edges_distinct 
      by blast
    then show "type\<^sub>e e \<notin> contains TG2"
      using type_graph.structure_contains_wellformed type_graph_second_valid 
      by blast
  qed
  then have "{e \<in> E IG. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG) \<union> contains TG2} = {e \<in> E IG. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG)}"
    by blast
  then show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG) \<union> contains TG2} \<le> 1"
    using n_in_in_ig instance_graph_valid instance_graph.validity_contained_node
    by simp
next
  fix p
  have irrefl_contains: "irrefl ((edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)})\<^sup>+)"
    using instance_graph_valid instance_graph.validity_containment_alt'
    by blast
  have "\<And>e. e \<in> E IG \<Longrightarrow> type\<^sub>e e \<notin> contains TG2"
  proof-
    fix e
    assume "e \<in> E IG"
    then have "type\<^sub>e e \<in> ET (TG IG)"
      using instance_graph_valid instance_graph.structure_edges_wellformed_edge_type_alt
      by blast
    then have "type\<^sub>e e \<notin> ET TG2"
      using combine_edges_distinct 
      by blast
    then show "type\<^sub>e e \<notin> contains TG2"
      using type_graph.structure_contains_wellformed type_graph_second_valid 
      by blast
  qed
  then have "{e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) \<union> contains TG2} = {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG)}"
    by blast
  then show "irrefl ((edge_to_tuple ` {e \<in> E IG. type\<^sub>e e \<in> contains (TG IG) \<union> contains TG2})\<^sup>+)"
    using irrefl_contains
    by simp
qed (simp_all only: assms)

lemma instance_graph_retype_combine_distinct_correct[simp]:
  assumes instance_graph_valid: "instance_graph IG"
  assumes type_graph_second_valid: "type_graph TG2"
  assumes combine_edges_distinct: "ET (TG IG) \<inter> ET TG2 = {}"
  assumes combine_nodes_distinct: "NT (TG IG) \<inter> NT TG2 = {}"
  shows "instance_graph (instance_graph_retype (tg_combine (TG IG) TG2) IG)"
proof (intro instance_graph_retype_combine_merge_correct)
  show "type_graph (tg_combine (TG IG) TG2)"
    by (intro tg_combine_distinct_correct) (simp_all only: assms instance_graph.validity_type_graph)
next
  fix et n
  assume et_in_tg_ig: "et \<in> ET (TG IG)"
  then have "src et \<in> NT (TG IG)"
    using instance_graph.validity_type_graph instance_graph_valid type_graph.structure_edges_wellformed_alt 
    by blast
  then have src_et_not_tg2: "src et \<notin> NT TG2"
    using combine_nodes_distinct 
    by blast
  assume n_in_in_ig: "n \<in> N IG"
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG) \<union> inh TG2"
    using combine_nodes_distinct instance_graph.validity_type_graph instance_graph_valid tg_combine_distinct_inh type_graph_second_valid 
    by blast
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG)"
    using UnE type_graph.structure_inheritance_wellformed_second_node type_graph_second_valid src_et_not_tg2
    by metis
  then show "card {e \<in> E IG. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG) et)"
    using et_in_tg_ig n_in_in_ig instance_graph_valid instance_graph.validity_outgoing_mult
    by simp
next
  fix et n
  assume "et \<in> ET TG2"
  then have "src et \<in> NT TG2"
    using type_graph_second_valid type_graph.structure_edges_wellformed_alt 
    by blast
  then have src_et_not_tg_ig: "src et \<notin> NT (TG IG)"
    using combine_nodes_distinct 
    by blast
  assume "n \<in> N IG"
  then have "type\<^sub>n n \<in> NT (TG IG)"
    using instance_graph_valid instance_graph.validity_node_typed
    by blast
  then have type_n_not_tg2: "type\<^sub>n n \<notin> NT TG2"
    using combine_nodes_distinct 
    by blast
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG) \<union> inh TG2"
    using combine_nodes_distinct instance_graph.validity_type_graph instance_graph_valid tg_combine_distinct_inh type_graph_second_valid 
    by blast
  then have "False"
    using Un_iff instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node 
    using type_graph.structure_inheritance_wellformed_second_node type_graph_second_valid type_n_not_tg2
    using instance_graph_valid src_et_not_tg_ig
    by metis
  then show "0 in m_out (mult TG2 et)"
    by simp
next
  fix et n
  assume et_in_tg_ig: "et \<in> ET (TG IG)"
  then have "tgt et \<in> NT (TG IG)"
    using instance_graph.validity_type_graph instance_graph_valid type_graph.structure_edges_wellformed_alt 
    by blast
  then have tgt_et_not_tg2: "tgt et \<notin> NT TG2"
    using combine_nodes_distinct 
    by blast
  assume n_in_in_ig: "n \<in> N IG"
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+"
  then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG) \<union> inh TG2"
    using combine_nodes_distinct instance_graph.validity_type_graph instance_graph_valid tg_combine_distinct_inh type_graph_second_valid 
    by blast
  then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG)"
    using UnE type_graph.structure_inheritance_wellformed_second_node type_graph_second_valid tgt_et_not_tg2
    by metis
  then show "card {e \<in> E IG. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG) et)"
    using et_in_tg_ig n_in_in_ig instance_graph_valid instance_graph.validity_ingoing_mult
    by simp
next
  fix et n
  assume "et \<in> ET TG2"
  then have "tgt et \<in> NT TG2"
    using type_graph_second_valid type_graph.structure_edges_wellformed_alt 
    by blast
  then have tgt_et_not_tg_ig: "tgt et \<notin> NT (TG IG)"
    using combine_nodes_distinct 
    by blast
  assume "n \<in> N IG"
  then have "type\<^sub>n n \<in> NT (TG IG)"
    using instance_graph_valid instance_graph.validity_node_typed
    by blast
  then have type_n_not_tg2: "type\<^sub>n n \<notin> NT TG2"
    using combine_nodes_distinct 
    by blast
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG) \<union> inh TG2)\<^sup>+"
  then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG) \<union> inh TG2"
    using combine_nodes_distinct instance_graph.validity_type_graph instance_graph_valid tg_combine_distinct_inh type_graph_second_valid 
    by blast
  then have "False"
    using Un_iff instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node 
    using type_graph.structure_inheritance_wellformed_second_node type_graph_second_valid type_n_not_tg2
    using instance_graph_valid tgt_et_not_tg_ig
    by metis
  then show "0 in m_in (mult TG2 et)"
    by simp
qed (simp_all only: assms)
  
end
