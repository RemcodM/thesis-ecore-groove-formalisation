theory Type_Graph_Combination
  imports 
    Type_Graph
begin

section "Combining type graphs"

definition tg_combine_mult :: "('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) set \<Rightarrow> (('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) \<Rightarrow> multiplicity_pair) \<Rightarrow> 
                   ('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) set \<Rightarrow> (('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) \<Rightarrow> multiplicity_pair) \<Rightarrow> 
                   ('lt LabDef \<times> 'lt LabDef \<times> 'lt LabDef) \<Rightarrow> multiplicity_pair" where
  "tg_combine_mult E1 mult1 E2 mult2 e = (if e \<in> E1 \<inter> E2 then mult_pair_intersect (mult1 e) (mult2 e) else if e \<in> E1 then mult1 e else if e \<in> E2 then mult2 e else undefined)"

definition tg_combine :: "('lt) type_graph \<Rightarrow> ('lt) type_graph \<Rightarrow> ('lt) type_graph" where
  "tg_combine TG1 TG2 \<equiv> \<lparr>
    NT = NT TG1 \<union> NT TG2,
    ET = ET TG1 \<union> ET TG2,
    inh = (inh TG1 \<union> inh TG2)\<^sup>+,
    abs = (abs TG1 - NT TG2) \<union> (abs TG2 - NT TG1) \<union> (abs TG1 \<inter> abs TG2),
    mult = tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2),
    contains = contains TG1 \<union> contains TG2
  \<rparr>"

lemma tg_combine_identity:
  assumes structure_mult_domain: "\<And>e. e \<notin> ET TG \<Longrightarrow> mult TG e = undefined"
  assumes validity_inh_trans: "trans (inh TG)"
  shows "tg_combine tg_empty TG = truncate TG"
  unfolding truncate_def tg_combine_def tg_combine_mult_def tg_empty_def
  using validity_inh_trans structure_mult_domain
  by fastforce

lemma tg_combine_identity_alt:
  assumes type_graph_correct: "type_graph TG"
  shows "tg_combine tg_empty TG = truncate TG"
  using tg_combine_identity type_graph.structure_mult_domain type_graph.validity_inh_trans type_graph_correct
  by blast

lemma tg_combine_commute[simp]: "tg_combine TG1 TG2 = tg_combine TG2 TG1"
  unfolding tg_combine_def tg_combine_mult_def
  by (auto simp add: Un_commute)

lemma tg_combine_assoc[simp]: "tg_combine (tg_combine TG1 TG2) TG3 = tg_combine TG1 (tg_combine TG2 TG3)"
  unfolding tg_combine_def
proof (auto)
  fix a b
  assume "(a, b) \<in> ((inh TG1 \<union> inh TG2)\<^sup>+ \<union> inh TG3)\<^sup>+"
  then show "(a, b) \<in> (inh TG1 \<union> (inh TG2 \<union> inh TG3)\<^sup>+)\<^sup>+"
  proof (induct)
    case (base w)
    then have "(a, w) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (a, w) \<in> inh TG3"
      by simp
    then show ?case
    proof (elim disjE)
      assume "(a, w) \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
      then show "(a, w) \<in> (inh TG1 \<union> (inh TG2 \<union> inh TG3)\<^sup>+)\<^sup>+"
      proof (induct)
        case (base y)
        then show ?case
          by blast
      next
        case (step y z)
        then show ?case
          using Un_iff r_into_trancl' trancl.trancl_into_trancl
          by metis
      qed
    next
      assume "(a, w) \<in> inh TG3"
      then show "(a, w) \<in> (inh TG1 \<union> (inh TG2 \<union> inh TG3)\<^sup>+)\<^sup>+"
        by blast
    qed
  next
    case (step w x)
    then have "(w, x) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (w, x) \<in> inh TG3"
      by blast
    then show ?case
    proof (elim disjE)
      assume "(w, x) \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
      then show "(a, x) \<in> (inh TG1 \<union> (inh TG2 \<union> inh TG3)\<^sup>+)\<^sup>+"
      proof (induct)
        case (base y)
        then show ?case
          using Un_iff step.hyps(3) trancl.trancl_into_trancl trancl_unfold
          by metis
      next
        case (step y z)
        then show ?case
          using Un_iff r_into_trancl' trancl.trancl_into_trancl
          by metis
      qed
    next
      assume "(w, x) \<in> inh TG3"
      then show "(a, x) \<in> (inh TG1 \<union> (inh TG2 \<union> inh TG3)\<^sup>+)\<^sup>+"
        using Un_iff step.hyps(3) trancl.trancl_into_trancl trancl_unfold
        by metis
    qed
  qed
next
  fix a b
  assume "(a, b) \<in> (inh TG1 \<union> (inh TG2 \<union> inh TG3)\<^sup>+)\<^sup>+"
  then show "(a, b) \<in> ((inh TG1 \<union> inh TG2)\<^sup>+ \<union> inh TG3)\<^sup>+"
  proof (induct)
    case (base w)
    then have "(a, w) \<in> inh TG1 \<or> (a, w) \<in> (inh TG2 \<union> inh TG3)\<^sup>+"
      by simp
    then show ?case
    proof (elim disjE)
      assume "(a, w) \<in> inh TG1"
      then show "(a, w) \<in> ((inh TG1 \<union> inh TG2)\<^sup>+ \<union> inh TG3)\<^sup>+"
        by blast
    next
      assume "(a, w) \<in> (inh TG2 \<union> inh TG3)\<^sup>+"
      then show "(a, w) \<in> ((inh TG1 \<union> inh TG2)\<^sup>+ \<union> inh TG3)\<^sup>+"
      proof (induct)
        case (base y)
        then show ?case
          by blast
      next
        case (step y z)
        then show ?case
          using Un_iff r_into_trancl' trancl.trancl_into_trancl
          by metis
      qed
    qed
  next
    case (step w x)
    then have "(w, x) \<in> inh TG1 \<or> (w, x) \<in> (inh TG2 \<union> inh TG3)\<^sup>+"
      by simp
    then show ?case
    proof (elim disjE)
      assume "(w, x) \<in> inh TG1"
      then show "(a, x) \<in> ((inh TG1 \<union> inh TG2)\<^sup>+ \<union> inh TG3)\<^sup>+"
        using Un_iff step.hyps(3) trancl.trancl_into_trancl trancl_unfold
        by metis
    next
      assume "(w, x) \<in> (inh TG2 \<union> inh TG3)\<^sup>+"
      then show "(a, x) \<in> ((inh TG1 \<union> inh TG2)\<^sup>+ \<union> inh TG3)\<^sup>+"
      proof (induct)
        case (base y)
        then show ?case 
          using Un_iff r_into_trancl' step.hyps(3) trancl.trancl_into_trancl
          by metis
      next
        case (step y z)
        then show ?case
          using Un_iff r_into_trancl' trancl.trancl_into_trancl
          by metis
      qed
    qed
  qed
next
  show "tg_combine_mult (ET TG1 \<union> ET TG2) (tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2)) (ET TG3) (mult TG3) =
      tg_combine_mult (ET TG1) (mult TG1) (ET TG2 \<union> ET TG3) (tg_combine_mult (ET TG2) (mult TG2) (ET TG3) (mult TG3))"
  proof
    fix x
    show "tg_combine_mult (ET TG1 \<union> ET TG2) (tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2)) (ET TG3) (mult TG3) x =
        tg_combine_mult (ET TG1) (mult TG1) (ET TG2 \<union> ET TG3) (tg_combine_mult (ET TG2) (mult TG2) (ET TG3) (mult TG3)) x"
      unfolding tg_combine_mult_def
      using mult_pair_intersect_assoc
      by auto
  qed
qed

lemma tg_combine_idemp:
  assumes structure_mult_domain: "\<And>e. e \<notin> ET TG \<Longrightarrow> mult TG e = undefined"
  assumes validity_inh_trans: "trans (inh TG)"
  shows "tg_combine TG TG = truncate TG"
  unfolding truncate_def tg_combine_def tg_combine_mult_def
  using validity_inh_trans structure_mult_domain
  by fastforce

lemma tg_combine_idemp_alt[simp]:
  assumes type_graph_correct: "type_graph TG"
  shows "tg_combine TG TG = truncate TG"
proof (intro tg_combine_idemp)
  show "\<And>e. e \<notin> ET TG \<Longrightarrow> mult TG e = undefined"
    using type_graph_correct type_graph.structure_mult_domain
    by blast
next
  show "trans (inh TG)"
    using type_graph_correct type_graph.validity_inh_trans
    by blast
qed

lemma tg_combine_idemp'[simp]:
  assumes structure_mult_domain: "\<And>e. e \<notin> ET TG2 \<Longrightarrow> mult TG2 e = undefined"
  assumes validity_inh_trans: "trans (inh TG2)"
  shows "tg_combine (tg_combine TG1 TG2) TG2 = tg_combine TG1 TG2"
proof-
  have assoc_rule: "tg_combine (tg_combine TG1 TG2) TG2 = tg_combine TG1 (tg_combine TG2 TG2)"
    by (fact tg_combine_assoc)
  have "tg_combine TG2 TG2 = truncate TG2"
    using tg_combine_idemp validity_inh_trans structure_mult_domain
    by blast
  then have "tg_combine TG2 TG2 = TG2"
    unfolding truncate_def
    by simp
  then show "tg_combine (tg_combine TG1 TG2) TG2 = tg_combine TG1 TG2"
    using assoc_rule
    by simp
qed

lemma tg_combine_idemp'_alt[simp]:
  assumes type_graph_correct: "type_graph TG2"
  shows "tg_combine (tg_combine TG1 TG2) TG2 = tg_combine TG1 TG2"
proof (intro tg_combine_idemp')
  show "\<And>e. e \<notin> ET TG2 \<Longrightarrow> mult TG2 e = undefined"
    using type_graph_correct type_graph.structure_mult_domain
    by blast
next
  show "trans (inh TG2)"
    using type_graph_correct type_graph.validity_inh_trans
    by blast
qed


subsection "Correctness of combining type graphs"

lemma tg_combine_correct[intro]:
  assumes first_type_graph_correct: "type_graph TG1"
  assumes second_type_graph_correct: "type_graph TG2"
  assumes edges_inheritance_correct_src_tg1: "\<And>l s1 t1 s2 t2. (s1, l, t1) \<in> ET TG1 \<Longrightarrow> (s2, l, t2) \<in> ET TG1 \<Longrightarrow> 
    (s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1 \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1 \<Longrightarrow> 
    (t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> s1 = s2 \<and> t1 = t2"
  assumes edges_inheritance_correct_tgt_tg1: "\<And>l s1 t1 s2 t2. (s1, l, t1) \<in> ET TG1 \<Longrightarrow> (s2, l, t2) \<in> ET TG1 \<Longrightarrow> 
    (s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> 
    (t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1 \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1 \<Longrightarrow> s1 = s2 \<and> t1 = t2"
  assumes edges_inheritance_correct_src_tg2: "\<And>l s1 t1 s2 t2. (s1, l, t1) \<in> ET TG2 \<Longrightarrow> (s2, l, t2) \<in> ET TG2 \<Longrightarrow> 
    (s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2 \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2 \<Longrightarrow> 
    (t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> s1 = s2 \<and> t1 = t2"
  assumes edges_inheritance_correct_tgt_tg2: "\<And>l s1 t1 s2 t2. (s1, l, t1) \<in> ET TG2 \<Longrightarrow> (s2, l, t2) \<in> ET TG2 \<Longrightarrow> 
    (s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> 
    (t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2 \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2 \<Longrightarrow> s1 = s2 \<and> t1 = t2"
  assumes edges_inheritance_correct_tg1_tg2: "\<And>l s1 t1 s2 t2. (s1, l, t1) \<in> ET TG1 \<Longrightarrow> (s2, l, t2) \<in> ET TG2 \<Longrightarrow> 
    (s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> 
    (t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> s1 = s2 \<and> t1 = t2"
  assumes multiplicity_intersection_correct: "\<And>e. e \<in> ET TG1 \<inter> ET TG2 \<Longrightarrow> multiplicity_pair (mult_pair_intersect (mult TG1 e) (mult TG2 e))"
  assumes inheritance_antisymmetry: "antisym ((inh TG1 \<union> inh TG2)\<^sup>+)"
  (* assumes first_type_graph_contains_mult: "\<And>e. e \<in> contains TG1 \<Longrightarrow> e \<notin> contains TG2 \<Longrightarrow> e \<in> ET TG2 \<Longrightarrow> lower (m_in (mult TG2 e)) = \<^bold>0"
  assumes second_type_graph_contains_mult: "\<And>e. e \<in> contains TG2 \<Longrightarrow> e \<notin> contains TG1 \<Longrightarrow> e \<in> ET TG1 \<Longrightarrow> lower (m_in (mult TG1 e)) = \<^bold>0" *)
  shows "type_graph (tg_combine TG1 TG2)"
proof (intro Type_Graph.type_graph.intro)
  fix n
  assume "n \<in> NT (tg_combine TG1 TG2)"
  then have "n \<in> NT TG1 \<union> NT TG2"
    by (simp add: tg_combine_def)
  then show "n \<in> Lab\<^sub>t \<union> Lab\<^sub>p"
    using first_type_graph_correct second_type_graph_correct type_graph.structure_nodes_wellformed by auto
next
  fix s l t
  assume "(s, l, t) \<in> ET (tg_combine TG1 TG2)"
  then have edges_tg_combined: "(s, l, t) \<in> ET TG1 \<union> ET TG2"
    by (simp add: tg_combine_def)
  then have "s \<in> NT TG1 \<union> NT TG2 \<and> l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> NT TG1 \<union> NT TG2"
    using first_type_graph_correct second_type_graph_correct type_graph.structure_edges_wellformed by auto
  then show "s \<in> NT (tg_combine TG1 TG2) \<and> l \<in> Lab\<^sub>e \<union> Lab\<^sub>f \<and> t \<in> NT (tg_combine TG1 TG2)"
    by (simp add: tg_combine_def)
next
  have "Field ((inh TG1 \<union> inh TG2)\<^sup>+) = NT TG1 \<union> NT TG2"
    by (simp add: Domain_Un_eq Field_def Range_Un_eq first_type_graph_correct second_type_graph_correct type_graph.validity_inh_domain type_graph.validity_inh_range)
  then show "Field (inh (tg_combine TG1 TG2)) = NT (tg_combine TG1 TG2)"
    by (simp add: tg_combine_def)
next
  fix n
  assume "n \<in> type_graph.abs (tg_combine TG1 TG2)"
  then have "n \<in> abs TG1 \<union> abs TG2"
    using Diff_iff Int_iff UnE UnI1 UnI2 tg_combine_def type_graph.simps(4)
    by metis
  then have "n \<in> NT TG1 \<union> NT TG2"
    using first_type_graph_correct second_type_graph_correct type_graph.structure_abstract_wellformed by auto
  then show "n \<in> NT (tg_combine TG1 TG2)"
    by (simp add: tg_combine_def)
next
  fix e
  assume "e \<in> ET (tg_combine TG1 TG2)"
  then have "e \<in> ET TG1 \<union> ET TG2"
    by (simp add: tg_combine_def)
  then have "multiplicity_pair (tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2) e)"
    using Un_iff first_type_graph_correct multiplicity_intersection_correct second_type_graph_correct tg_combine_mult_def type_graph.structure_mult_wellformed
    by metis
  then show "multiplicity_pair (mult (tg_combine TG1 TG2) e)"
    by (simp add: tg_combine_def)
next
  fix e
  assume "e \<notin> ET (tg_combine TG1 TG2)"
  then show "mult (tg_combine TG1 TG2) e = undefined"
    by (simp add: tg_combine_def tg_combine_mult_def)
next
  fix e
  assume "e \<in> contains (tg_combine TG1 TG2)"
  then have "e \<in> contains TG1 \<union> contains TG2"
    by (simp add: tg_combine_def)
  then have "e \<in> ET TG1 \<union> ET TG2"
    using Un_iff first_type_graph_correct second_type_graph_correct type_graph.structure_contains_wellformed
    by metis
  then show "e \<in> ET (tg_combine TG1 TG2)"
    by (simp add: tg_combine_def)
next
  fix l s1 t1 s2 t2
  assume "(s1, l, t1) \<in> ET (tg_combine TG1 TG2)"
  then have edge1: "(s1, l, t1) \<in> ET TG1 \<union> ET TG2"
    by (simp add: tg_combine_def)
  assume "(s2, l, t2) \<in> ET (tg_combine TG1 TG2)"
  then have edge2: "(s2, l, t2) \<in> ET TG1 \<union> ET TG2"
    by (simp add: tg_combine_def)
  assume "(s1, s2) \<in> inh (tg_combine TG1 TG2) \<or> (s2, s1) \<in> inh (tg_combine TG1 TG2)"
  then have src_inh: "(s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
    by (simp add: tg_combine_def)
  assume "(t1, t2) \<in> inh (tg_combine TG1 TG2) \<or> (t2, t1) \<in> inh (tg_combine TG1 TG2)"
  then have tgt_inh: "(t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
    by (simp add: tg_combine_def)
  show "s1 = s2 \<and> t1 = t2"
    using edge1 edge2
  proof (elim UnE)
    assume first_edge_in_tg: "(s1, l, t1) \<in> ET TG1"
    assume second_edge_in_tg: "(s2, l, t2) \<in> ET TG1"
    show ?thesis
      using src_inh tgt_inh
    proof (induct "(s1, s2) \<in> inh TG1 \<or> (s2, s1) \<in> inh TG1")
      case True
      then show ?case
      proof (induct "(t1, t2) \<in> inh TG1 \<or> (t2, t1) \<in> inh TG1")
        case True
        then show ?case
          using first_edge_in_tg second_edge_in_tg first_type_graph_correct type_graph.validity_edges_inh
          by blast
      next
        case False
        then show ?case
          using edges_inheritance_correct_tgt_tg1 first_edge_in_tg second_edge_in_tg
          by blast
      qed
    next
      case False
      then show ?case
        using edges_inheritance_correct_src_tg1 first_edge_in_tg second_edge_in_tg
        by blast
    qed
  next
    assume first_edge_in_tg: "(s1, l, t1) \<in> ET TG1"
    assume second_edge_in_tg: "(s2, l, t2) \<in> ET TG2"
    show ?thesis
      using edges_inheritance_correct_tg1_tg2 first_edge_in_tg second_edge_in_tg src_inh tgt_inh
      by blast
  next
    assume first_edge_in_tg: "(s1, l, t1) \<in> ET TG2"
    assume second_edge_in_tg: "(s2, l, t2) \<in> ET TG1"
    show ?thesis
      using edges_inheritance_correct_tg1_tg2 first_edge_in_tg second_edge_in_tg src_inh tgt_inh
      by blast
  next
    assume first_edge_in_tg: "(s1, l, t1) \<in> ET TG2"
    assume second_edge_in_tg: "(s2, l, t2) \<in> ET TG2"
    show ?thesis
      using src_inh tgt_inh
    proof (induct "(s1, s2) \<in> inh TG2 \<or> (s2, s1) \<in> inh TG2")
      case True
      then show ?case
      proof (induct "(t1, t2) \<in> inh TG2 \<or> (t2, t1) \<in> inh TG2")
        case True
        then show ?case
          using first_edge_in_tg second_edge_in_tg second_type_graph_correct type_graph.validity_edges_inh
          by blast
      next
        case False
        then show ?case
          using edges_inheritance_correct_tgt_tg2 first_edge_in_tg second_edge_in_tg
          by blast
      qed
    next
      case False
      then show ?case
        using edges_inheritance_correct_src_tg2 first_edge_in_tg second_edge_in_tg
        by blast
    qed
  qed
next
  fix s l t
  assume "(s, l, t) \<in> ET (tg_combine TG1 TG2)"
  then have edge_in_edges: "(s, l, t) \<in> ET TG1 \<union> ET TG2"
    by (simp add: tg_combine_def)
  assume "l \<in> Lab\<^sub>f"
  then show "s = t"
    using edge_in_edges first_type_graph_correct second_type_graph_correct type_graph.validity_flags by auto
next
  have "Partial_order ((inh TG1 \<union> inh TG2)\<^sup>+)"
    unfolding partial_order_on_def preorder_on_def
  proof (intro conjI)
    have trancl_subset: "(inh TG1 \<union> inh TG2) \<subseteq> (inh TG1 \<union> inh TG2)\<^sup>+"
      by auto
    have "Refl (inh TG1 \<union> inh TG2)"
      by (simp add: first_type_graph_correct second_type_graph_correct type_graph.validity_inh_refl refl_on_Un)
    then show "Refl ((inh TG1 \<union> inh TG2)\<^sup>+)"
      unfolding refl_on_def
    proof (intro conjI)
      assume refl_assump: "inh TG1 \<union> inh TG2 \<subseteq> Field (inh TG1 \<union> inh TG2) \<times> Field (inh TG1 \<union> inh TG2) \<and> (\<forall>x\<in>Field (inh TG1 \<union> inh TG2). (x, x) \<in> inh TG1 \<union> inh TG2)"
      have "inh TG1 \<union> inh TG2 \<subseteq> Field (inh TG1 \<union> inh TG2) \<times> Field (inh TG1 \<union> inh TG2)"
        using refl_assump
        by blast
      then show "(inh TG1 \<union> inh TG2)\<^sup>+ \<subseteq> Field ((inh TG1 \<union> inh TG2)\<^sup>+) \<times> Field ((inh TG1 \<union> inh TG2)\<^sup>+)"
        by (simp add: FieldI1 FieldI2 subrelI)
      have "(\<forall>x\<in>Field (inh TG1 \<union> inh TG2). (x, x) \<in> inh TG1 \<union> inh TG2)"
        using refl_assump
        by blast
      then show "\<forall>x\<in>Field ((inh TG1 \<union> inh TG2)\<^sup>+). (x, x) \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
        using Field_square mono_Field set_mp set_mp trancl_subset trancl_subset_Field2
        by metis
    qed
    show "trans ((inh TG1 \<union> inh TG2)\<^sup>+)"
      by auto
    show "antisym ((inh TG1 \<union> inh TG2)\<^sup>+)"
      using assms by simp
  qed
  then show "Partial_order (inh (tg_combine TG1 TG2))"
    by (simp add: tg_combine_def)
next
  fix e
  assume "e \<in> contains (tg_combine TG1 TG2)"
  then have "e \<in> contains TG1 \<union> contains TG2"
    by (simp add: tg_combine_def)
  then have "e \<in> contains TG1 \<inter> contains TG2 \<or> e \<in> contains TG1 - contains TG2 \<or> e \<in> contains TG2 - contains TG1"
    by blast
  then have "upper (m_in (tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2) e)) = \<^bold>1"
  proof (elim disjE)
    assume e_in_intersection: "e \<in> contains TG1 \<inter> contains TG2"
    have e_in_tg1: "e \<in> contains TG1"
      using e_in_intersection
      by auto
    have e_in_tg2: "e \<in> contains TG2"
      using e_in_intersection
      by auto
    have "upper (m_in (mult_pair_intersect (mult TG1 e) (mult TG2 e))) = \<^bold>1"
      using e_in_tg1 e_in_tg2 first_type_graph_correct second_type_graph_correct type_graph.validity_mult_containment
      using fstI m_in_def min_def mult_intersect_def mult_pair_intersect_def sndI upper_def
      by metis
    then show "upper (m_in (tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2) e)) = \<^bold>1"
      unfolding tg_combine_mult_def
      by (simp add: e_in_tg1 e_in_tg2 first_type_graph_correct second_type_graph_correct type_graph.structure_contains_wellformed)
  next
    assume e_in_contains: "e \<in> contains TG1 - contains TG2"
    have e_not_in_tg2: "e \<notin> contains TG2"
      using e_in_contains by simp
    have e_in_tg1: "e \<in> contains TG1"
      using e_in_contains by simp
    have contains_mult_e: "upper (m_in (mult TG1 e)) = \<^bold>1"
      using e_in_tg1 first_type_graph_correct type_graph.validity_mult_containment by blast
    have "e \<in> ET TG2 \<Longrightarrow> upper (m_in (mult TG2 e)) \<ge> \<^bold>1"
      using second_type_graph_correct type_graph.structure_mult_wellformed multiplicity_pair.in_mult_is_mult multiplicity.upper_bound_valid_alt 
      by blast
    then have upper_intersect_one: "e \<in> ET TG2 \<Longrightarrow> upper (m_in (mult_pair_intersect (mult TG1 e) (mult TG2 e))) = \<^bold>1"
      unfolding mult_pair_intersect_def mult_intersect_def
      using contains_mult_e min.absorb1 by auto
    then show "upper (m_in (tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2) e)) = \<^bold>1"
      unfolding tg_combine_mult_def
      using e_in_tg1 first_type_graph_correct contains_mult_e type_graph.structure_contains_wellformed by fastforce
  next
    assume e_in_contains: "e \<in> contains TG2 - contains TG1"
    have e_not_in_tg1: "e \<notin> contains TG1"
      using e_in_contains by simp
    have e_in_tg2: "e \<in> contains TG2"
      using e_in_contains by simp
    have contains_mult_e: "upper (m_in (mult TG2 e)) = \<^bold>1"
      using e_in_tg2 second_type_graph_correct type_graph.validity_mult_containment by blast
    have "e \<in> ET TG1 \<Longrightarrow> upper (m_in (mult TG1 e)) \<ge> \<^bold>1"
      using first_type_graph_correct type_graph.structure_mult_wellformed multiplicity_pair.in_mult_is_mult multiplicity.upper_bound_valid_alt 
      by blast
    then have upper_intersect_one: "e \<in> ET TG1 \<Longrightarrow> upper (m_in (mult_pair_intersect (mult TG1 e) (mult TG2 e))) = \<^bold>1"
      unfolding mult_pair_intersect_def mult_intersect_def
      using contains_mult_e min.absorb2 by auto
    then show "upper (m_in (tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2) e)) = \<^bold>1"
      unfolding tg_combine_mult_def
      using e_in_tg2 second_type_graph_correct contains_mult_e type_graph.structure_contains_wellformed by fastforce
  qed
  then show "upper (m_in (mult (tg_combine TG1 TG2) e)) = \<^bold>1"
    by (simp add: tg_combine_def)
qed

lemma tg_combine_merge_correct[intro]:
  assumes first_type_graph_correct: "type_graph TG1"
  assumes second_type_graph_correct: "type_graph TG2"
  assumes combine_edges_distinct: "ET TG1 \<inter> ET TG2 = {}"
  assumes edges_inheritance_correct_src_tg1: "\<And>l s1 t1 s2 t2. (s1, l, t1) \<in> ET TG1 \<Longrightarrow> (s2, l, t2) \<in> ET TG1 \<Longrightarrow> 
    (s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1 \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1 \<Longrightarrow> 
    (t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> s1 = s2 \<and> t1 = t2"
  assumes edges_inheritance_correct_tgt_tg1: "\<And>l s1 t1 s2 t2. (s1, l, t1) \<in> ET TG1 \<Longrightarrow> (s2, l, t2) \<in> ET TG1 \<Longrightarrow> 
    (s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> 
    (t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1 \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1 \<Longrightarrow> s1 = s2 \<and> t1 = t2"
  assumes edges_inheritance_correct_src_tg2: "\<And>l s1 t1 s2 t2. (s1, l, t1) \<in> ET TG2 \<Longrightarrow> (s2, l, t2) \<in> ET TG2 \<Longrightarrow> 
    (s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2 \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2 \<Longrightarrow> 
    (t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> s1 = s2 \<and> t1 = t2"
  assumes edges_inheritance_correct_tgt_tg2: "\<And>l s1 t1 s2 t2. (s1, l, t1) \<in> ET TG2 \<Longrightarrow> (s2, l, t2) \<in> ET TG2 \<Longrightarrow> 
    (s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> 
    (t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2 \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2 \<Longrightarrow> s1 = s2 \<and> t1 = t2"
  assumes edges_inheritance_correct_tg1_tg2: "\<And>l s1 t1 s2 t2. (s1, l, t1) \<in> ET TG1 \<Longrightarrow> (s2, l, t2) \<in> ET TG2 \<Longrightarrow> 
    (s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> 
    (t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<Longrightarrow> s1 = s2 \<and> t1 = t2"
  assumes inheritance_antisymmetry: "antisym ((inh TG1 \<union> inh TG2)\<^sup>+)"
  shows "type_graph (tg_combine TG1 TG2)"
proof (intro tg_combine_correct)
  fix e
  assume "e \<in> ET TG1 \<inter> ET TG2"
  then show "multiplicity_pair (mult_pair_intersect (mult TG1 e) (mult TG2 e))"
    using combine_edges_distinct 
    by blast
qed (simp_all only: assms)

lemma tg_combine_distinct_inh[simp]:
  assumes first_type_graph_correct: "type_graph TG1"
  assumes second_type_graph_correct: "type_graph TG2"
  assumes combine_nodes_distinct: "NT TG1 \<inter> NT TG2 = {}"
  shows "(inh TG1 \<union> inh TG2)\<^sup>+ = inh TG1 \<union> inh TG2"
proof
  show "(inh TG1 \<union> inh TG2)\<^sup>+ \<subseteq> inh TG1 \<union> inh TG2"
  proof
    fix x
    assume "x \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
    then show "x \<in> inh TG1 \<union> inh TG2"
    proof (induct x)
      case (Pair a b)
      then show ?case
      proof (induct)
        case (base y)
        then show ?case
          by simp
      next
        case (step y z)
        then show ?case
        proof (induct "(a, y) \<in> inh TG1")
          case True
          then have "(y, z) \<notin> inh TG2"
            using combine_nodes_distinct disjoint_iff_not_equal first_type_graph_correct 
            using second_type_graph_correct type_graph.structure_inheritance_wellformed_first_node 
            using type_graph.structure_inheritance_wellformed_second_node
            by metis
          then have "(y, z) \<in> inh TG1"
            using step.hyps(2) by blast
          then have "(a, z) \<in> inh TG1"
            using True.hyps first_type_graph_correct transE type_graph.validity_inh_trans
            by metis
          then show ?case
            by simp
        next
          case False
          then have ay_in_tg2: "(a, y) \<in> inh TG2"
            by simp
          then have "(y, z) \<notin> inh TG1"
            using combine_nodes_distinct disjoint_iff_not_equal first_type_graph_correct 
            using second_type_graph_correct type_graph.structure_inheritance_wellformed_first_node 
            using type_graph.structure_inheritance_wellformed_second_node
            by metis
          then have "(y, z) \<in> inh TG2"
            using step.hyps(2) by blast
          then have "(a, z) \<in> inh TG2"
            using ay_in_tg2 second_type_graph_correct transE type_graph.validity_inh_trans
            by metis
          then show ?case
            by simp
        qed
      qed
    qed
  qed
next
  show "inh TG1 \<union> inh TG2 \<subseteq> (inh TG1 \<union> inh TG2)\<^sup>+"
    by auto
qed

lemma tg_combine_distinct_correct[simp]:
  assumes first_type_graph_correct: "type_graph TG1"
  assumes second_type_graph_correct: "type_graph TG2"
  assumes combine_nodes_distinct: "NT TG1 \<inter> NT TG2 = {}"
  shows "type_graph (tg_combine TG1 TG2)"
proof (intro tg_combine_merge_correct)
  show "ET TG1 \<inter> ET TG2 = {}"
    using combine_nodes_distinct disjoint_iff_not_equal first_type_graph_correct second_type_graph_correct type_graph.structure_edges_wellformed_src_node_alt
    by metis
next
  fix l s1 t1 s2 t2
  assume first_edge_in_tg: "(s1, l, t1) \<in> ET TG1"
  assume second_edge_in_tg: "(s2, l, t2) \<in> ET TG1"
  assume "(s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1 \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1"
  then have src_inh: "(s1, s2) \<in> inh TG2 \<or> (s2, s1) \<in> inh TG2"
    using combine_nodes_distinct first_type_graph_correct second_type_graph_correct
    by auto
  assume "(t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
  then have tgt_inh: "(t1, t2) \<in> inh TG1 \<union> inh TG2 \<or> (t2, t1) \<in> inh TG1 \<union> inh TG2"
    by (simp add: combine_nodes_distinct first_type_graph_correct second_type_graph_correct)
  then show "s1 = s2 \<and> t1 = t2"
    using FieldI1 FieldI2 combine_nodes_distinct disjoint_iff_not_equal first_edge_in_tg first_type_graph_correct second_type_graph_correct src_inh type_graph.structure_edges_wellformed type_graph.structure_inheritance_wellformed
    by metis
next
  fix l s1 t1 s2 t2
  assume first_edge_in_tg: "(s1, l, t1) \<in> ET TG1"
  assume second_edge_in_tg: "(s2, l, t2) \<in> ET TG1"
  assume "(s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
  then have src_inh: "(s1, s2) \<in> inh TG1 \<union> inh TG2 \<or> (s2, s1) \<in> inh TG1 \<union> inh TG2"
    by (simp add: combine_nodes_distinct first_type_graph_correct second_type_graph_correct)
  assume "(t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1 \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG1"
  then have tgt_inh: "(t1, t2) \<in> inh TG2 \<or> (t2, t1) \<in> inh TG2"
    using combine_nodes_distinct first_type_graph_correct second_type_graph_correct
    by auto
  then show "s1 = s2 \<and> t1 = t2"
    using FieldI1 FieldI2 combine_nodes_distinct disjoint_iff_not_equal first_edge_in_tg first_type_graph_correct second_type_graph_correct src_inh type_graph.structure_edges_wellformed type_graph.structure_inheritance_wellformed
    by metis
next
  fix l s1 t1 s2 t2
  assume first_edge_in_tg: "(s1, l, t1) \<in> ET TG2"
  assume second_edge_in_tg: "(s2, l, t2) \<in> ET TG2"
  assume "(s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2 \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2"
  then have src_inh: "(s1, s2) \<in> inh TG1 \<or> (s2, s1) \<in> inh TG1"
    using combine_nodes_distinct first_type_graph_correct second_type_graph_correct
    by auto
  assume "(t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
  then have tgt_inh: "(t1, t2) \<in> inh TG1 \<union> inh TG2 \<or> (t2, t1) \<in> inh TG1 \<union> inh TG2"
    by (simp add: combine_nodes_distinct first_type_graph_correct second_type_graph_correct)
  then show "s1 = s2 \<and> t1 = t2"
    using FieldI1 FieldI2 combine_nodes_distinct disjoint_iff_not_equal first_edge_in_tg first_type_graph_correct second_type_graph_correct src_inh type_graph.structure_edges_wellformed type_graph.structure_inheritance_wellformed
    by metis
next
  fix l s1 t1 s2 t2
  assume first_edge_in_tg: "(s1, l, t1) \<in> ET TG2"
  assume second_edge_in_tg: "(s2, l, t2) \<in> ET TG2"
  assume "(s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
  then have src_inh: "(s1, s2) \<in> inh TG1 \<union> inh TG2 \<or> (s2, s1) \<in> inh TG1 \<union> inh TG2"
    by (simp add: combine_nodes_distinct first_type_graph_correct second_type_graph_correct)
  assume "(t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2 \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ - inh TG2"
  then have tgt_inh: "(t1, t2) \<in> inh TG1 \<or> (t2, t1) \<in> inh TG1"
    using combine_nodes_distinct first_type_graph_correct second_type_graph_correct
    by auto
  then show "s1 = s2 \<and> t1 = t2"
    using FieldI1 FieldI2 combine_nodes_distinct disjoint_iff_not_equal first_edge_in_tg first_type_graph_correct second_type_graph_correct src_inh type_graph.structure_edges_wellformed type_graph.structure_inheritance_wellformed
    by metis
next
  fix l s1 t1 s2 t2
  assume first_edge_in_tg: "(s1, l, t1) \<in> ET TG1"
  assume second_edge_in_tg: "(s2, l, t2) \<in> ET TG2"
  assume "(s1, s2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (s2, s1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
  then have src_inh: "(s1, s2) \<in> inh TG1 \<union> inh TG2 \<or> (s2, s1) \<in> inh TG1 \<union> inh TG2"
    by (simp add: combine_nodes_distinct first_type_graph_correct second_type_graph_correct)
  assume "(t1, t2) \<in> (inh TG1 \<union> inh TG2)\<^sup>+ \<or> (t2, t1) \<in> (inh TG1 \<union> inh TG2)\<^sup>+"
  then have tgt_inh: "(t1, t2) \<in> inh TG1 \<union> inh TG2 \<or> (t2, t1) \<in> inh TG1 \<union> inh TG2"
    by (simp add: combine_nodes_distinct first_type_graph_correct second_type_graph_correct)
  then show "s1 = s2 \<and> t1 = t2"
  proof-
    have "\<And>l. l \<notin> NT TG2 \<or> l \<notin> NT TG1"
      using combine_nodes_distinct by blast
    then show ?thesis
      using Un_iff first_edge_in_tg first_type_graph_correct second_edge_in_tg second_type_graph_correct tgt_inh type_graph.structure_edges_wellformed type_graph.structure_inheritance_wellformed_first_node type_graph.structure_inheritance_wellformed_second_node
      by metis
  qed
next
  have "antisym (inh TG1 \<union> inh TG2)"
  proof
    fix x y
    assume xy_in_merged_inh: "(x, y) \<in> inh TG1 \<union> inh TG2"
    assume yx_in_merged_inh: "(y, x) \<in> inh TG1 \<union> inh TG2"
    show "x = y"
      using xy_in_merged_inh yx_in_merged_inh
    proof (elim UnE)
      assume xy: "(x, y) \<in> inh TG1"
      assume yx: "(y, x) \<in> inh TG1"
      then show "x = y"
        using xy yx antisymD first_type_graph_correct type_graph.validity_inh_antisym
        by metis
    next
      assume xy: "(x, y) \<in> inh TG1"
      assume yx: "(y, x) \<in> inh TG2"
      then show "x = y"
        using combine_nodes_distinct disjoint_iff_not_equal first_type_graph_correct 
        using second_type_graph_correct type_graph.structure_inheritance_wellformed_first_node 
        using type_graph.structure_inheritance_wellformed_second_node xy
        by metis
    next
      assume xy: "(x, y) \<in> inh TG2"
      assume yx: "(y, x) \<in> inh TG2"
      then show "x = y"
        using xy yx antisymD second_type_graph_correct type_graph.validity_inh_antisym
        by metis
    next
      assume xy: "(x, y) \<in> inh TG2"
      assume yx: "(y, x) \<in> inh TG1"
      then show "x = y"
        using combine_nodes_distinct disjoint_iff_not_equal first_type_graph_correct 
        using second_type_graph_correct type_graph.structure_inheritance_wellformed_first_node 
        using type_graph.structure_inheritance_wellformed_second_node xy
        by metis
    qed
  qed
  then show "antisym ((inh TG1 \<union> inh TG2)\<^sup>+)"
    by (simp add: combine_nodes_distinct first_type_graph_correct second_type_graph_correct)
qed (simp_all only: assms)

lemma tg_combine_empty_correct1[simp]:
  assumes second_type_graph_correct: "type_graph TG2"
  shows "type_graph (tg_combine tg_empty TG2)"
proof (intro tg_combine_distinct_correct)
  show "type_graph tg_empty"
    by (fact Type_Graph.tg_empty_correct)
qed (simp_all add: assms)

lemma tg_combine_empty_correct2[simp]:
  assumes first_type_graph_correct: "type_graph TG1"
  shows "type_graph (tg_combine TG1 tg_empty)"
  using first_type_graph_correct tg_combine_empty_correct1
  by simp

end
