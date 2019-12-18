theory Instance_Graph_Combination
  imports 
    Type_Graph_Combination
    Instance_Graph
begin

section "Combining instance graphs"

definition ig_combine_ident :: "'id set \<Rightarrow> ('id \<Rightarrow> ('nt, 'lt) NodeDef) \<Rightarrow> 'id set \<Rightarrow> ('id \<Rightarrow> ('nt, 'lt) NodeDef) \<Rightarrow> 'id \<Rightarrow> ('nt, 'lt) NodeDef" where
  "ig_combine_ident Id1 ident1 Id2 ident2 i = (
    if i \<in> Id1 \<and> i \<in> Id2 \<and> ident1 i = ident2 i then
      ident1 i
    else if i \<in> Id1 \<and> i \<in> Id2 \<and> ident1 i \<noteq> ident2 i then
      invalid
    else if i \<in> Id1 \<and> i \<notin> Id2 then 
      ident1 i
    else if i \<notin> Id1 \<and> i \<in> Id2 then 
      ident2 i
    else
      undefined
  )"

definition ig_combine :: "('nt, 'lt, 'id) instance_graph \<Rightarrow> ('nt, 'lt, 'id) instance_graph \<Rightarrow> ('nt, 'lt, 'id) instance_graph" where
  "ig_combine IG1 IG2 \<equiv> \<lparr>
    TG = tg_combine (TG IG1) (TG IG2),
    Id = Id IG1 \<union> Id IG2,
    N = N IG1 \<union> N IG2,
    E = E IG1 \<union> E IG2,
    ident = ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2)
  \<rparr>"

lemma ig_combine_identity:
  assumes structure_mult_domain: "\<And>e. e \<notin> ET (TG IG) \<Longrightarrow> mult (TG IG) e = undefined"
  assumes validity_inh_trans: "trans (inh (TG IG))"
  assumes structure_ident_domain: "\<And>i. i \<notin> Id IG \<Longrightarrow> ident IG i = undefined"
  shows "ig_combine IG ig_empty = truncate IG"
  unfolding truncate_def ig_combine_def
proof
  show "tg_combine (TG IG) (TG ig_empty) = TG IG \<and> 
      Id IG \<union> Id ig_empty = Id IG \<and>
      N IG \<union> N ig_empty = N IG \<and> 
      E IG \<union> E ig_empty = E IG \<and> 
      ig_combine_ident (Id IG) (ident IG) (Id ig_empty) (ident ig_empty) = ident IG \<and> 
      () = ()"
  proof (intro conjI)
    have "tg_combine tg_empty (TG IG) = type_graph.truncate (TG IG)"
      by (intro tg_combine_identity) (simp_all add: assms)
    then show "tg_combine (TG IG) (TG ig_empty) = TG IG"
      unfolding type_graph.truncate_def ig_empty_def
      using tg_combine_commute
      by simp
  next
    show "ig_combine_ident (Id IG) (ident IG) (Id ig_empty) (ident ig_empty) = ident IG"
    proof
      fix i
      show "ig_combine_ident (Id IG) (ident IG) (Id ig_empty) (ident ig_empty) i = ident IG i"
        unfolding ig_combine_ident_def ig_empty_def
        by (simp add: structure_ident_domain)
    qed
  qed (simp_all)
qed

lemma ig_combine_identity_alt[simp]:
  assumes instance_graph_valid: "instance_graph IG"
  shows "ig_combine IG ig_empty = truncate IG"
proof (intro ig_combine_identity)
  show "\<And>e. e \<notin> ET (TG IG) \<Longrightarrow> mult (TG IG) e = undefined"
    using instance_graph_valid instance_graph.validity_type_graph type_graph.structure_mult_domain
    by blast
next
  show "trans (inh (TG IG))"
    using instance_graph_valid instance_graph.validity_type_graph type_graph.validity_inh_trans
    by blast
next
  show "\<And>i. i \<notin> Id IG \<Longrightarrow> ident IG i = undefined"
    using instance_graph_valid instance_graph.structure_ident_domain
    by metis
qed

lemma ig_combine_ident_commute: "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) = ig_combine_ident (Id IG2) (ident IG2) (Id IG1) (ident IG1)"
  unfolding ig_combine_ident_def
  by fastforce

lemma ig_combine_commute[simp]: "ig_combine IG1 IG2 = ig_combine IG2 IG1"
  unfolding ig_combine_def
proof
  show "tg_combine (TG IG1) (TG IG2) = tg_combine (TG IG2) (TG IG1) \<and>
    Id IG1 \<union> Id IG2 = Id IG2 \<union> Id IG1 \<and>
    N IG1 \<union> N IG2 = N IG2 \<union> N IG1 \<and>
    E IG1 \<union> E IG2 = E IG2 \<union> E IG1 \<and>
    ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) = ig_combine_ident (Id IG2) (ident IG2) (Id IG1) (ident IG1) \<and>
    () = ()"
  proof (intro conjI)
    show "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) = ig_combine_ident (Id IG2) (ident IG2) (Id IG1) (ident IG1)"
      by (fact ig_combine_ident_commute)
  qed (simp_all add: Un_commute)
qed

lemma ig_combine_idemp:
  assumes structure_mult_domain: "\<And>e. e \<notin> ET (TG IG) \<Longrightarrow> mult (TG IG) e = undefined"
  assumes validity_inh_trans: "trans (inh (TG IG))"
  assumes structure_ident_domain: "\<And>i. i \<notin> Id IG \<Longrightarrow> ident IG i = undefined"
  shows "ig_combine IG IG = truncate IG"
  unfolding truncate_def ig_combine_def
proof
  show "tg_combine (TG IG) (TG IG) = TG IG \<and>
      Id IG \<union> Id IG = Id IG \<and>
      N IG \<union> N IG = N IG \<and>
      E IG \<union> E IG = E IG \<and>
      ig_combine_ident (Id IG) (ident IG) (Id IG) (ident IG) = ident IG \<and>
      () = ()"
  proof (intro conjI)
    have "tg_combine (TG IG) (TG IG) = type_graph.truncate (TG IG)"
      using tg_combine_idemp structure_mult_domain validity_inh_trans
      by blast
    then show "tg_combine (TG IG) (TG IG) = TG IG"
      unfolding type_graph.truncate_def
      by simp
  next
    show "ig_combine_ident (Id IG) (ident IG) (Id IG) (ident IG) = ident IG"
    proof
      fix i
      show "ig_combine_ident (Id IG) (ident IG) (Id IG) (ident IG) i = ident IG i"
        unfolding ig_combine_ident_def
        by (simp add: structure_ident_domain)
    qed
  qed (simp_all)
qed

lemma ig_combine_idemp_alt[simp]:
  assumes instance_graph_valid: "instance_graph IG"
  shows "ig_combine IG IG = truncate IG"
proof (intro ig_combine_idemp)
  show "\<And>e. e \<notin> ET (TG IG) \<Longrightarrow> mult (TG IG) e = undefined"
    using instance_graph_valid instance_graph.validity_type_graph type_graph.structure_mult_domain
    by blast
next
  show "trans (inh (TG IG))"
    using instance_graph_valid instance_graph.validity_type_graph type_graph.validity_inh_trans
    by blast
next
  show "\<And>i. i \<notin> Id IG \<Longrightarrow> ident IG i = undefined"
    using instance_graph_valid instance_graph.structure_ident_domain
    by metis
qed

lemma ig_combine_ident_assoc:
  shows "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) = 
    ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3))"
proof
  fix i
  have id_ig1_cases: "i \<in> Id IG1 \<or> i \<notin> Id IG1"
    by simp
  have id_ig2_cases: "i \<in> Id IG2 \<or> i \<notin> Id IG2"
    by simp
  have id_ig3_cases: "i \<in> Id IG3 \<or> i \<notin> Id IG3"
    by simp
  have ident_ig1_ig2_eq_cases: "ident IG1 i = ident IG2 i \<or> ident IG1 i \<noteq> ident IG2 i"
    by simp
  have ident_ig1_ig3_eq_cases: "ident IG1 i = ident IG3 i \<or> ident IG1 i \<noteq> ident IG3 i"
    by simp
  have ident_ig2_ig3_eq_cases: "ident IG2 i = ident IG3 i \<or> ident IG2 i \<noteq> ident IG3 i"
    by simp
  show "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = 
    ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i"
    using id_ig1_cases id_ig2_cases id_ig3_cases
  proof (elim disjE)
    assume ig1_in_set: "i \<in> Id IG1"
    assume ig2_in_set: "i \<in> Id IG2"
    then have ig12_in_set: "i \<in> Id (ig_combine IG1 IG2)"
      unfolding ig_combine_def
      by simp
    assume ig3_in_set: "i \<in> Id IG3"
    then have ig23_in_set: "i \<in> Id (ig_combine IG2 IG3)"
      unfolding ig_combine_def
      by simp
    show ?thesis
      using ident_ig1_ig2_eq_cases ident_ig2_ig3_eq_cases ident_ig1_ig3_eq_cases
    proof (elim disjE)
      assume ig1_ig2_eq: "ident IG1 i = ident IG2 i"
      then have ig12_def: "ident (ig_combine IG1 IG2) i = ident IG1 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig1_in_set ig2_in_set
        by simp
      assume ig2_ig3_eq: "ident IG2 i = ident IG3 i"
      then have ig23_def: "ident (ig_combine IG2 IG3) i = ident IG2 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig2_in_set ig3_in_set
        by simp
      assume ig1_ig3_eq: "ident IG1 i = ident IG3 i"
      then have "ident (ig_combine IG1 IG2) i = ident IG3 i"
        using ig12_def
        by simp
      then have ig12_ig3_def: "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = ident IG1 i"
        unfolding ig_combine_ident_def
        using ig12_in_set ig3_in_set ig1_ig3_eq
        by simp
      have "ident IG1 i = ident (ig_combine IG2 IG3) i"
        using ig1_ig2_eq ig23_def
        by simp
      then have "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = ident IG1 i"
        unfolding ig_combine_ident_def
        using ig1_in_set ig23_in_set
        by simp
      then show ?thesis
        using ig12_ig3_def
        by simp
    next
      assume ig1_ig2_eq: "ident IG1 i = ident IG2 i"
      then have ig12_def: "ident (ig_combine IG1 IG2) i = ident IG1 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig1_in_set ig2_in_set
        by simp
      assume ig2_ig3_not_eq: "ident IG2 i \<noteq> ident IG3 i"
      then have ig23_def: "ident (ig_combine IG2 IG3) i = invalid"
        unfolding ig_combine_def ig_combine_ident_def
        using ig2_in_set ig3_in_set
        by simp
      assume ig1_ig3_not_eq: "ident IG1 i \<noteq> ident IG3 i"
      then have "ident (ig_combine IG1 IG2) i \<noteq> ident IG3 i"
        using ig12_def
        by simp
      then have ig12_ig3_def: "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = invalid"
        unfolding ig_combine_ident_def
        using ig12_in_set ig3_in_set
        by simp
      have "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = invalid"
        unfolding ig_combine_ident_def
        using ig1_in_set ig23_in_set ig23_def
        by simp
      then show ?thesis
        using ig12_ig3_def
        by simp
    next
      assume ig1_ig2_not_eq: "ident IG1 i \<noteq> ident IG2 i"
      then have ig12_def: "ident (ig_combine IG1 IG2) i = invalid"
        unfolding ig_combine_def ig_combine_ident_def
        using ig1_in_set ig2_in_set
        by simp
      assume ig2_ig3_eq: "ident IG2 i = ident IG3 i"
      then have ig23_def: "ident (ig_combine IG2 IG3) i = ident IG2 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig2_in_set ig3_in_set
        by simp
      assume ig1_ig3_not_eq: "ident IG1 i \<noteq> ident IG3 i"
      have "ident IG1 i \<noteq> ident (ig_combine IG2 IG3) i"
        using ig23_def ig1_ig2_not_eq
        by simp
      then have ig1_ig23_def: "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = invalid"
        unfolding ig_combine_ident_def
        using ig1_in_set ig23_in_set
        by simp
      have "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = invalid"
        unfolding ig_combine_ident_def
        using ig12_in_set ig3_in_set ig12_def
        by simp
      then show ?thesis
        using ig1_ig23_def
        by simp
    next
      assume ig1_ig2_not_eq: "ident IG1 i \<noteq> ident IG2 i"
      then have ig12_def: "ident (ig_combine IG1 IG2) i = invalid"
        unfolding ig_combine_def ig_combine_ident_def
        using ig1_in_set ig2_in_set
        by simp
      assume ig2_ig3_not_eq: "ident IG2 i \<noteq> ident IG3 i"
      then have ig23_def: "ident (ig_combine IG2 IG3) i = invalid"
        unfolding ig_combine_def ig_combine_ident_def
        using ig2_in_set ig3_in_set
        by simp
      assume ig1_ig3_eq: "ident IG1 i = ident IG3 i"
      have ig1_ig23_def: "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = invalid"
        unfolding ig_combine_ident_def
        using ig1_in_set ig23_in_set ig23_def
        by simp
      have "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = invalid"
        unfolding ig_combine_ident_def
        using ig12_in_set ig3_in_set ig12_def
        by simp
      then show ?thesis
        using ig1_ig23_def
        by simp
    next
      assume ig1_ig2_not_eq: "ident IG1 i \<noteq> ident IG2 i"
      then have ig12_def: "ident (ig_combine IG1 IG2) i = invalid"
        unfolding ig_combine_def ig_combine_ident_def
        using ig1_in_set ig2_in_set
        by simp
      assume ig2_ig3_not_eq: "ident IG2 i \<noteq> ident IG3 i"
      then have ig23_def: "ident (ig_combine IG2 IG3) i = invalid"
        unfolding ig_combine_def ig_combine_ident_def
        using ig2_in_set ig3_in_set
        by simp
      assume ig1_ig3_not_eq: "ident IG1 i \<noteq> ident IG3 i"
      have ig1_ig23_def: "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = invalid"
        unfolding ig_combine_ident_def
        using ig1_in_set ig23_in_set ig23_def
        by simp
      have "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = invalid"
        unfolding ig_combine_ident_def
        using ig12_in_set ig3_in_set ig12_def
        by simp
      then show ?thesis
        using ig1_ig23_def
        by simp
    qed (simp_all)
  next
    assume ig1_in_set: "i \<in> Id IG1"
    then have ig12_in_set: "i \<in> Id (ig_combine IG1 IG2)"
      unfolding ig_combine_def
      by simp
    assume ig2_in_set: "i \<in> Id IG2"
    then have ig23_in_set: "i \<in> Id (ig_combine IG2 IG3)"
      unfolding ig_combine_def
      by simp
    assume ig3_not_in_set: "i \<notin> Id IG3"
    show ?thesis
      using ident_ig1_ig2_eq_cases
    proof (elim disjE)
      assume ig1_ig2_eq: "ident IG1 i = ident IG2 i"
      then have ig12_def: "ident (ig_combine IG1 IG2) i = ident IG1 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig1_in_set ig2_in_set
        by simp
      then have ig12_ig3_def: "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = ident IG1 i"
        unfolding ig_combine_ident_def
        using ig12_in_set ig3_not_in_set
        by simp
      have ig23_def: "ident (ig_combine IG2 IG3) i = ident IG2 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig2_in_set ig3_not_in_set
        by simp
      then have "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = ident IG1 i"
        unfolding ig_combine_ident_def
        using ig1_in_set ig23_in_set ig1_ig2_eq
        by simp
      then show ?thesis
        using ig12_ig3_def
        by simp
    next
      assume ig1_ig2_not_eq: "ident IG1 i \<noteq> ident IG2 i"
      then have ig12_def: "ident (ig_combine IG1 IG2) i = invalid"
        unfolding ig_combine_def ig_combine_ident_def
        using ig1_in_set ig2_in_set
        by simp
      then have ig12_ig3_def: "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = invalid"
        unfolding ig_combine_ident_def
        using ig12_in_set ig3_not_in_set
        by simp
      have ig23_def: "ident (ig_combine IG2 IG3) i = ident IG2 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig2_in_set ig3_not_in_set
        by simp
      then have "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = invalid"
        unfolding ig_combine_ident_def
        using ig1_in_set ig23_in_set ig1_ig2_not_eq
        by simp
      then show ?thesis
        using ig12_ig3_def
        by simp
    qed
  next
    assume ig1_in_set: "i \<in> Id IG1"
    then have ig12_in_set: "i \<in> Id (ig_combine IG1 IG2)"
      unfolding ig_combine_def
      by simp
    assume ig2_not_in_set: "i \<notin> Id IG2"
    assume ig3_in_set: "i \<in> Id IG3"
    then have ig23_in_set: "i \<in> Id (ig_combine IG2 IG3)"
      unfolding ig_combine_def
      by simp
    show ?thesis
      using ident_ig1_ig3_eq_cases
    proof (elim disjE)
      assume ig1_ig3_eq: "ident IG1 i = ident IG3 i"
      then have ig12_def: "ident (ig_combine IG1 IG2) i = ident IG1 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig1_in_set ig2_not_in_set
        by simp
      then have ig12_ig3_def: "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = ident IG1 i"
        unfolding ig_combine_ident_def
        using ig12_in_set ig3_in_set ig1_ig3_eq
        by simp
      have ig23_def: "ident (ig_combine IG2 IG3) i = ident IG3 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig2_not_in_set ig3_in_set
        by simp
      then have "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = ident IG1 i"
        unfolding ig_combine_ident_def
        using ig1_in_set ig23_in_set ig1_ig3_eq
        by simp
      then show ?thesis
        using ig12_ig3_def
        by simp
    next
      assume ig1_ig3_not_eq: "ident IG1 i \<noteq> ident IG3 i"
      then have ig12_def: "ident (ig_combine IG1 IG2) i = ident IG1 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig1_in_set ig2_not_in_set
        by simp
      then have ig12_ig3_def: "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = invalid"
        unfolding ig_combine_ident_def
        using ig12_in_set ig3_in_set ig1_ig3_not_eq
        by simp
      have ig23_def: "ident (ig_combine IG2 IG3) i = ident IG3 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig2_not_in_set ig3_in_set
        by simp
      then have "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = invalid"
        unfolding ig_combine_ident_def
        using ig1_in_set ig23_in_set ig1_ig3_not_eq
        by simp
      then show ?thesis
        using ig12_ig3_def
        by simp
    qed
  next
    assume ig1_in_set: "i \<in> Id IG1"
    then have ig12_in_set: "i \<in> Id (ig_combine IG1 IG2)"
      unfolding ig_combine_def
      by simp
    assume ig2_not_in_set: "i \<notin> Id IG2"
    assume ig3_not_in_set: "i \<notin> Id IG3"
    have ig23_not_in_set: "i \<notin> Id (ig_combine IG2 IG3)"
      unfolding ig_combine_def
      using ig2_not_in_set ig3_not_in_set
      by simp
    then have ig1_ig23_def: "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = ident IG1 i"
      unfolding ig_combine_ident_def
      using ig1_in_set ig23_not_in_set
      by simp
    have ig12_def: "ident (ig_combine IG1 IG2) i = ident IG1 i"
      unfolding ig_combine_def ig_combine_ident_def
      using ig1_in_set ig2_not_in_set
      by simp
    then have "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = ident IG1 i"
      unfolding ig_combine_ident_def
      using ig12_in_set ig3_not_in_set
      by simp
    then show ?thesis
      using ig1_ig23_def
      by simp
  next
    assume ig1_not_in_set: "i \<notin> Id IG1"
    assume ig2_in_set: "i \<in> Id IG2"
    then have ig12_in_set: "i \<in> Id (ig_combine IG1 IG2)"
      unfolding ig_combine_def
      by simp
    assume ig3_in_set: "i \<in> Id IG3"
    then have ig23_in_set: "i \<in> Id (ig_combine IG2 IG3)"
      unfolding ig_combine_def
      by simp
    show ?thesis
      using ident_ig2_ig3_eq_cases
    proof (elim disjE)
      assume ig2_ig3_eq: "ident IG2 i = ident IG3 i"
      have ig12_def: "ident (ig_combine IG1 IG2) i = ident IG2 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig1_not_in_set ig2_in_set
        by simp
      then have ig12_ig3_def: "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = ident IG2 i"
        unfolding ig_combine_ident_def
        using ig12_in_set ig3_in_set ig2_ig3_eq
        by simp
      have ig23_def: "ident (ig_combine IG2 IG3) i = ident IG2 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig2_in_set ig3_in_set ig2_ig3_eq
        by simp
      then have "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = ident IG2 i"
        unfolding ig_combine_ident_def
        using ig1_not_in_set ig23_in_set
        by simp
      then show ?thesis
        using ig12_ig3_def
        by simp
    next
      assume ig2_ig3_not_eq: "ident IG2 i \<noteq> ident IG3 i"
      have ig12_def: "ident (ig_combine IG1 IG2) i = ident IG2 i"
        unfolding ig_combine_def ig_combine_ident_def
        using ig1_not_in_set ig2_in_set
        by simp
      then have ig12_ig3_def: "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = invalid"
        unfolding ig_combine_ident_def
        using ig12_in_set ig3_in_set ig2_ig3_not_eq
        by simp
      have ig23_def: "ident (ig_combine IG2 IG3) i = invalid"
        unfolding ig_combine_def ig_combine_ident_def
        using ig2_in_set ig3_in_set ig2_ig3_not_eq
        by simp
      then have "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = invalid"
        unfolding ig_combine_ident_def
        using ig1_not_in_set ig23_in_set
        by simp
      then show ?thesis
        using ig12_ig3_def
        by simp
    qed
  next
    assume ig1_not_in_set: "i \<notin> Id IG1"
    assume ig2_in_set: "i \<in> Id IG2"
    then have ig12_in_set: "i \<in> Id (ig_combine IG1 IG2)"
      unfolding ig_combine_def
      by simp
    have ig23_in_set: "i \<in> Id (ig_combine IG2 IG3)"
      unfolding ig_combine_def
      using ig2_in_set
      by simp
    assume ig3_not_in_set: "i \<notin> Id IG3"
    have ig12_def: "ident (ig_combine IG1 IG2) i = ident IG2 i"
      unfolding ig_combine_def ig_combine_ident_def
      using ig1_not_in_set ig2_in_set
      by simp
    then have ig12_ig3_def: "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = ident IG2 i"
      unfolding ig_combine_ident_def
      using ig12_in_set ig3_not_in_set
      by simp
    have ig23_def: "ident (ig_combine IG2 IG3) i = ident IG2 i"
      unfolding ig_combine_def ig_combine_ident_def
      using ig2_in_set ig3_not_in_set
      by simp
    then have "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = ident IG2 i"
      unfolding ig_combine_ident_def
      using ig1_not_in_set ig23_in_set
      by simp
    then show ?thesis
      using ig12_ig3_def
      by simp
  next
    assume ig1_not_in_set: "i \<notin> Id IG1"
    assume ig2_not_in_set: "i \<notin> Id IG2"
    assume ig3_in_set: "i \<in> Id IG3"
    then have ig23_in_set: "i \<in> Id (ig_combine IG2 IG3)"
      unfolding ig_combine_def
      by simp
    have ig12_not_in_set: "i \<notin> Id (ig_combine IG1 IG2)"
      unfolding ig_combine_def
      using ig1_not_in_set ig2_not_in_set
      by simp
    then have ig12_ig3_def: "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = ident IG3 i"
      unfolding ig_combine_ident_def
      using ig12_not_in_set ig3_in_set
      by simp
    have ig12_def: "ident (ig_combine IG2 IG3) i = ident IG3 i"
      unfolding ig_combine_def ig_combine_ident_def
      using ig2_not_in_set ig3_in_set
      by simp
    then have "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = ident IG3 i"
      unfolding ig_combine_ident_def
      using ig1_not_in_set ig23_in_set
      by simp
    then show ?thesis
      using ig12_ig3_def
      by simp
  next
    assume ig1_not_in_set: "i \<notin> Id IG1"
    assume ig2_not_in_set: "i \<notin> Id IG2"
    assume ig3_not_in_set: "i \<notin> Id IG3"
    have ig12_not_in_set: "i \<notin> Id (ig_combine IG1 IG2)"
      unfolding ig_combine_def
      using ig1_not_in_set ig2_not_in_set
      by simp
    then have ig12_ig3_def: "ig_combine_ident (Id (ig_combine IG1 IG2)) (ident (ig_combine IG1 IG2)) (Id IG3) (ident IG3) i = undefined"
      unfolding ig_combine_ident_def
      using ig3_not_in_set
      by simp
    have ig23_not_in_set: "i \<notin> Id (ig_combine IG2 IG3)"
      unfolding ig_combine_def
      using ig2_not_in_set ig3_not_in_set
      by simp
    then have "ig_combine_ident (Id IG1) (ident IG1) (Id (ig_combine IG2 IG3)) (ident (ig_combine IG2 IG3)) i = undefined"
      unfolding ig_combine_ident_def
      using ig1_not_in_set
      by simp
    then show ?thesis
      using ig12_ig3_def
      by simp
  qed
qed

lemma ig_combine_assoc: "ig_combine (ig_combine IG1 IG2) IG3 = ig_combine IG1 (ig_combine IG2 IG3)"
proof-
  have "\<And>IG12 IG23. IG12 = ig_combine IG1 IG2 \<Longrightarrow> IG23 = ig_combine IG2 IG3 \<Longrightarrow> ig_combine IG12 IG3 = ig_combine IG1 IG23"
  proof-
    fix IG12
    fix IG23
    assume ig12_def: "IG12 = ig_combine IG1 IG2"
    assume ig23_def: "IG23 = ig_combine IG2 IG3"
    show "ig_combine IG12 IG3 = ig_combine IG1 IG23"
      unfolding ig_combine_def
    proof
      show "tg_combine (TG IG12) (TG IG3) = tg_combine (TG IG1) (TG IG23) \<and>
        Id IG12 \<union> Id IG3 = Id IG1 \<union> Id IG23 \<and>
        N IG12 \<union> N IG3 = N IG1 \<union> N IG23 \<and>
        E IG12 \<union> E IG3 = E IG1 \<union> E IG23 \<and>
        ig_combine_ident (Id IG12) (ident IG12) (Id IG3) (ident IG3) = ig_combine_ident (Id IG1) (ident IG1) (Id IG23) (ident IG23) \<and>
        () = ()"
      proof (intro conjI)
        show "tg_combine (TG IG12) (TG IG3) = tg_combine (TG IG1) (TG IG23)"
          using ig12_def ig23_def ig_combine_def instance_graph.select_convs(1) tg_combine_assoc
          by metis
      next
        show "ig_combine_ident (Id IG12) (ident IG12) (Id IG3) (ident IG3) = ig_combine_ident (Id IG1) (ident IG1) (Id IG23) (ident IG23)"
          using ig12_def ig23_def ig_combine_ident_assoc
          by blast
      qed (simp_all add: ig12_def ig23_def sup_assoc ig_combine_def)
    qed
  qed
  then show ?thesis
    by blast
qed

lemma ig_combine_correct[intro]:
  assumes first_instance_graph_valid: "instance_graph IG1"
  assumes second_instance_graph_valid: "instance_graph IG2"
  assumes validity_identity: "\<And>i. i \<in> Id IG1 \<Longrightarrow> i \<in> Id IG2 \<Longrightarrow> ident IG1 i = ident IG2 i"
  assumes validity_type_graph: "type_graph (tg_combine (TG IG1) (TG IG2))"
  assumes validity_outgoing_mult: "\<And>et n. et \<in> ET (TG IG1) \<union> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow>
    (type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et} in m_out (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et)"
  assumes validity_ingoing_mult: "\<And>et n. et \<in> ET (TG IG1) \<union> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow>
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et} in m_in (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et)"
  assumes validity_contained_node: "\<And>n. n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    card { e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2) } \<le> 1"
  assumes validity_containment: "irrefl ((edge_to_tuple ` {e \<in> E IG1 \<union> E IG2. type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)})\<^sup>+)"
  shows "instance_graph (ig_combine IG1 IG2)"
proof (intro instance_graph.intro)
  fix n
  assume "n \<in> N (ig_combine IG1 IG2)"
  then have "n \<in> N IG1 \<union> N IG2"
    unfolding ig_combine_def
    by simp
  then show "n \<in> Node"
    using first_instance_graph_valid second_instance_graph_valid instance_graph.structure_nodes_wellformed
    by auto
next
  fix s l t
  assume "(s, l, t) \<in> E (ig_combine IG1 IG2)"
  then have "(s, l, t) \<in> E IG1 \<union> E IG2"
    unfolding ig_combine_def
    by simp
  then show "s \<in> N (ig_combine IG1 IG2) \<and> l \<in> ET (TG (ig_combine IG1 IG2)) \<and> t \<in> N (ig_combine IG1 IG2)"
  proof (intro conjI)
    assume "(s, l, t) \<in> E IG1 \<union> E IG2"
    then have "s \<in> N IG1 \<union> N IG2"
      using first_instance_graph_valid second_instance_graph_valid instance_graph.structure_edges_wellformed_src_node
      by blast
    then show "s \<in> N (ig_combine IG1 IG2)"
      unfolding ig_combine_def
      by simp
  next
    assume "(s, l, t) \<in> E IG1 \<union> E IG2"
    then have "l \<in> ET (TG IG1) \<union> ET (TG IG2)"
      using first_instance_graph_valid second_instance_graph_valid instance_graph.structure_edges_wellformed_edge_type
      by blast
    then show "l \<in> ET (TG (ig_combine IG1 IG2))"
      unfolding ig_combine_def tg_combine_def
      by simp
  next
    assume "(s, l, t) \<in> E IG1 \<union> E IG2"
    then have "t \<in> N IG1 \<union> N IG2"
      using first_instance_graph_valid second_instance_graph_valid instance_graph.structure_edges_wellformed_tgt_node
      by blast
    then show "t \<in> N (ig_combine IG1 IG2)"
      unfolding ig_combine_def
      by simp
  qed
next
  fix i
  assume "i \<in> Id (ig_combine IG1 IG2)"
  then have "i \<in> Id IG1 \<union> Id IG2"
    unfolding ig_combine_def
    by simp
  then have "i \<in> Id IG1 \<inter> Id IG2 \<or> i \<in> Id IG1 - Id IG2 \<or> i \<in> Id IG2 - Id IG1"
    by blast
  then have "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i \<in> N IG1 \<union> N IG2 \<and> 
    type\<^sub>n (ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i) \<in> Lab\<^sub>t"
  proof (elim disjE)
    assume i_in_both: "i \<in> Id IG1 \<inter> Id IG2"
    then have "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG1 i"
      unfolding ig_combine_ident_def
      using validity_identity
      by simp
    then show ?thesis
    proof (intro conjI)
      assume  "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG1 i"
      then have "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i \<in> N IG1"
        using i_in_both first_instance_graph_valid instance_graph.structure_ident_wellformed_node
        by fastforce
      then show "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i \<in> N IG1 \<union> N IG2"
        by simp
    next
      assume  "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG1 i"
      then show "type\<^sub>n (ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i) \<in> Lab\<^sub>t"
        using i_in_both first_instance_graph_valid instance_graph.structure_ident_wellformed_node_type
        by fastforce
    qed
  next
    assume i_in_ig1: "i \<in> Id IG1 - Id IG2"
    then have "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG1 i"
      unfolding ig_combine_ident_def
      by simp
    then show ?thesis
    proof (intro conjI)
      assume  "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG1 i"
      then have "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i \<in> N IG1"
        using i_in_ig1 first_instance_graph_valid instance_graph.structure_ident_wellformed_node
        by fastforce
      then show "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i \<in> N IG1 \<union> N IG2"
        by simp
    next
      assume  "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG1 i"
      then show "type\<^sub>n (ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i) \<in> Lab\<^sub>t"
        using i_in_ig1 first_instance_graph_valid instance_graph.structure_ident_wellformed_node_type
        by fastforce
    qed
  next
    assume i_in_ig2: "i \<in> Id IG2 - Id IG1"
    then have "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG2 i"
      unfolding ig_combine_ident_def
      by simp
    then show ?thesis
    proof (intro conjI)
      assume  "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG2 i"
      then have "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i \<in> N IG2"
        using i_in_ig2 second_instance_graph_valid instance_graph.structure_ident_wellformed_node
        by fastforce
      then show "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i \<in> N IG1 \<union> N IG2"
        by simp
    next
      assume  "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG2 i"
      then show "type\<^sub>n (ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i) \<in> Lab\<^sub>t"
        using i_in_ig2 second_instance_graph_valid instance_graph.structure_ident_wellformed_node_type
        by fastforce
    qed
  qed
  then show "ident (ig_combine IG1 IG2) i \<in> N (ig_combine IG1 IG2) \<and> type\<^sub>n (ident (ig_combine IG1 IG2) i) \<in> Lab\<^sub>t"
    unfolding ig_combine_def
    by simp
next
  fix i
  assume "i \<notin> Id (ig_combine IG1 IG2)"
  then have "i \<notin> Id IG1 \<and> i \<notin> Id IG2"
    unfolding ig_combine_def
    by simp
  then have "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = undefined"
    unfolding ig_combine_ident_def
    by simp
  then show "ident (ig_combine IG1 IG2) i = undefined"
    unfolding ig_combine_def
    by simp
next
  have "type_graph (tg_combine (TG IG1) (TG IG2))"
    by (fact assms)
  then show "type_graph (TG (ig_combine IG1 IG2))"
    unfolding ig_combine_def
    by simp
next
  fix n
  assume "n \<in> N (ig_combine IG1 IG2)"
  then have "n \<in> N IG1 \<union> N IG2"
    unfolding ig_combine_def
    by simp
  then have "type\<^sub>n n \<in> NT (TG IG1) \<union> NT (TG IG2)"
  proof (elim UnE)
    assume "n \<in> N IG1"
    then show "type\<^sub>n n \<in> NT (TG IG1) \<union> NT (TG IG2)"
      using first_instance_graph_valid instance_graph.validity_node_typed
      by blast
  next
    assume "n \<in> N IG2"
    then show "type\<^sub>n n \<in> NT (TG IG1) \<union> NT (TG IG2)"
      using second_instance_graph_valid instance_graph.validity_node_typed
      by blast
  qed
  then show "type\<^sub>n n \<in> NT (TG (ig_combine IG1 IG2))"
    unfolding ig_combine_def tg_combine_def
    by simp
next
  fix e
  assume "e \<in> E (ig_combine IG1 IG2)"
  then have "e \<in> E IG1 \<union> E IG2"
    unfolding ig_combine_def
    by simp
  then have "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
  proof (elim UnE)
    assume "e \<in> E IG1"
    then have "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG IG1)"
      using first_instance_graph_valid instance_graph.validity_edge_src_typed
      by blast
    then have "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG IG1) \<union> inh (TG IG2)"
      by simp
    then show "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
      by auto
  next
    assume "e \<in> E IG2"
    then have "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG IG2)"
      using second_instance_graph_valid instance_graph.validity_edge_src_typed
      by blast
    then have "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG IG1) \<union> inh (TG IG2)"
      by simp
    then show "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
      by auto
  qed
  then show "(type\<^sub>n (src e), src (type\<^sub>e e)) \<in> inh (TG (ig_combine IG1 IG2))"
    unfolding ig_combine_def tg_combine_def
    by simp
next
  fix e
  assume "e \<in> E (ig_combine IG1 IG2)"
  then have "e \<in> E IG1 \<union> E IG2"
    unfolding ig_combine_def
    by simp
  then have "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
  proof (elim UnE)
    assume "e \<in> E IG1"
    then have "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG IG1)"
      using first_instance_graph_valid instance_graph.validity_edge_tgt_typed
      by blast
    then have "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG IG1) \<union> inh (TG IG2)"
      by simp
    then show "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
      by auto
  next
    assume "e \<in> E IG2"
    then have "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG IG2)"
      using second_instance_graph_valid instance_graph.validity_edge_tgt_typed
      by blast
    then have "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG IG1) \<union> inh (TG IG2)"
      by simp
    then show "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
      by auto
  qed
  then show "(type\<^sub>n (tgt e), tgt (type\<^sub>e e)) \<in> inh (TG (ig_combine IG1 IG2))"
    unfolding ig_combine_def tg_combine_def
    by simp
next
  fix n
  assume "n \<in> N (ig_combine IG1 IG2)"
  then have "n \<in> N IG1 \<union> N IG2"
    unfolding ig_combine_def
    by simp
  then have "type\<^sub>n n \<notin> (abs (TG IG1) - NT (TG IG2)) \<union> (abs (TG IG2) - NT (TG IG1)) \<union> (abs (TG IG1) \<inter> abs (TG IG2))"
  proof (elim UnE)
    assume n_in_ig1: "n \<in> N IG1"
    then have "type\<^sub>n n \<notin> abs (TG IG1)"
      using first_instance_graph_valid instance_graph.validity_abs_no_instances
      by blast
    then show "type\<^sub>n n \<notin> (abs (TG IG1) - NT (TG IG2)) \<union> (abs (TG IG2) - NT (TG IG1)) \<union> (abs (TG IG1) \<inter> abs (TG IG2))"
      using n_in_ig1 instance_graph.validity_node_typed first_instance_graph_valid 
      by fastforce
  next
    assume n_in_ig2: "n \<in> N IG2"
    then have "type\<^sub>n n \<notin> abs (TG IG2)"
      using second_instance_graph_valid instance_graph.validity_abs_no_instances
      by blast
    then show "type\<^sub>n n \<notin> (abs (TG IG1) - NT (TG IG2)) \<union> (abs (TG IG2) - NT (TG IG1)) \<union> (abs (TG IG1) \<inter> abs (TG IG2))"
      using n_in_ig2 instance_graph.validity_node_typed second_instance_graph_valid 
      by fastforce
  qed
  then show "type\<^sub>n n \<notin> abs (TG (ig_combine IG1 IG2))"
    unfolding ig_combine_def tg_combine_def
    by simp
next
  fix et n
  assume "et \<in> ET (TG (ig_combine IG1 IG2))"
  then have et_in_ef: "et \<in> ET (TG IG1) \<union> ET (TG IG2)"
    unfolding ig_combine_def tg_combine_def
    by simp
  assume "n \<in> N (ig_combine IG1 IG2)"
  then have n_in_in: "n \<in> N IG1 \<union> N IG2"
    unfolding ig_combine_def
    by simp
  assume "(type\<^sub>n n, src et) \<in> inh (TG (ig_combine IG1 IG2))"
  then have type_extend: "(type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
    unfolding ig_combine_def tg_combine_def
    by simp
  have "card {e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et} in
       m_out (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et)"
    using et_in_ef n_in_in type_extend
    by (fact assms)
  then show "card {e \<in> E (ig_combine IG1 IG2). src e = n \<and> type\<^sub>e e = et} in 
      m_out (mult (TG (ig_combine IG1 IG2)) et)"
    unfolding ig_combine_def tg_combine_def
    by simp
next
  fix et n
  assume "et \<in> ET (TG (ig_combine IG1 IG2))"
  then have et_in_ef: "et \<in> ET (TG IG1) \<union> ET (TG IG2)"
    unfolding ig_combine_def tg_combine_def
    by simp
  assume "n \<in> N (ig_combine IG1 IG2)"
  then have n_in_in: "n \<in> N IG1 \<union> N IG2"
    unfolding ig_combine_def
    by simp
  assume "(type\<^sub>n n, tgt et) \<in> inh (TG (ig_combine IG1 IG2))"
  then have type_extend: "(type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
    unfolding ig_combine_def tg_combine_def
    by simp
  have "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et} in
       m_in (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et)"
    using et_in_ef n_in_in type_extend
    by (fact assms)
  then show "card {e \<in> E (ig_combine IG1 IG2). tgt e = n \<and> type\<^sub>e e = et} in 
      m_in (mult (TG (ig_combine IG1 IG2)) et)"
    unfolding ig_combine_def tg_combine_def
    by simp
next
  fix n
  assume "n \<in> N (ig_combine IG1 IG2)"
  then have "n \<in> N IG1 \<union> N IG2"
    unfolding ig_combine_def tg_combine_def
    by simp
  then have "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<le> 1"
    by (fact assms)
  then show "card {e \<in> E (ig_combine IG1 IG2). tgt e = n \<and> type\<^sub>e e \<in> contains (TG (ig_combine IG1 IG2))} \<le> 1"
    unfolding ig_combine_def tg_combine_def
    by simp
next
  fix p
  show "\<not>pre_digraph.cycle (instance_graph_containment_proj (ig_combine IG1 IG2)) p"
  proof (intro validity_containmentI)
    show "\<And>e. e \<in> E (ig_combine IG1 IG2) \<Longrightarrow> type\<^sub>e e \<in> contains (TG (ig_combine IG1 IG2)) \<Longrightarrow> src e \<in> N (ig_combine IG1 IG2) \<and> tgt e \<in> N (ig_combine IG1 IG2)"
    proof (intro conjI)
      fix e
      assume "e \<in> E (ig_combine IG1 IG2)"
      then have "e \<in> E IG1 \<union> E IG2"
        unfolding ig_combine_def
        by simp
      then have "src e \<in> N IG1 \<union> N IG2"
        using first_instance_graph_valid second_instance_graph_valid instance_graph.structure_edges_wellformed_src_node_alt
        by blast
      then show "src e \<in> N (ig_combine IG1 IG2)"
        unfolding ig_combine_def
        by simp
    next
      fix e
      assume "e \<in> E (ig_combine IG1 IG2)"
      then have "e \<in> E IG1 \<union> E IG2"
        unfolding ig_combine_def
        by simp
      then have "tgt e \<in> N IG1 \<union> N IG2"
        using first_instance_graph_valid second_instance_graph_valid instance_graph.structure_edges_wellformed_tgt_node_alt
        by blast
      then show "tgt e \<in> N (ig_combine IG1 IG2)"
        unfolding ig_combine_def
        by simp
    qed
  next
    have "irrefl ((edge_to_tuple ` {e \<in> E IG1 \<union> E IG2. type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)})\<^sup>+)"
      by (fact validity_containment)
    then show "irrefl ((edge_to_tuple ` {e \<in> E (ig_combine IG1 IG2). type\<^sub>e e \<in> contains (TG (ig_combine IG1 IG2))})\<^sup>+)"
      unfolding ig_combine_def tg_combine_def
      by simp
  qed
qed

lemma ig_combine_merge_correct[intro]:
  assumes first_instance_graph_valid: "instance_graph IG1"
  assumes second_instance_graph_valid: "instance_graph IG2"
  assumes type_graph_combination_valid: "type_graph (tg_combine (TG IG1) (TG IG2))"
  assumes combine_edges_distinct: "ET (TG IG1) \<inter> ET (TG IG2) = {}"
  assumes validity_identity: "\<And>i. i \<in> Id IG1 \<Longrightarrow> i \<in> Id IG2 \<Longrightarrow> ident IG1 i = ident IG2 i"
  assumes validity_outgoing_mult_first: "\<And>et n. et \<in> ET (TG IG1) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG1) et)"
  assumes validity_outgoing_mult_second: "\<And>et n. et \<in> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG2. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG2) et)"
  assumes validity_ingoing_mult_first: "\<And>et n. et \<in> ET (TG IG1) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG1) et)"
  assumes validity_ingoing_mult_second: "\<And>et n. et \<in> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG2) et)"
  assumes validity_contained_node: "\<And>n. n \<in> N IG1 \<inter> N IG2 \<Longrightarrow> 
    card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<le> 1"
  assumes validity_containment: "irrefl ((edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> 
    edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+)"
  shows "instance_graph (ig_combine IG1 IG2)"
proof (intro ig_combine_correct)
  fix et n
  assume et_in_tg_e: "et \<in> ET (TG IG1) \<union> ET (TG IG2)"
  assume n_in_in_igs: "n \<in> N IG1 \<union> N IG2"
  assume edge_of_type: "(type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
  show "card {e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et} in
      m_out (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et)"
    using et_in_tg_e edge_of_type
  proof (elim UnE)
    assume et_in_e: "et \<in> ET (TG IG1)"
    then have mult_et: "m_out (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et) = m_out (mult (TG IG1) et)"
      unfolding tg_combine_mult_def
      using combine_edges_distinct
      by auto
    have set_et: "{e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et} = {e \<in> E IG1. src e = n \<and> type\<^sub>e e = et}"
    proof
      show "{e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et} \<subseteq> {e \<in> E IG1. src e = n \<and> type\<^sub>e e = et}"
      proof
        fix x
        assume "x \<in> {e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et}"
        then show "x \<in> {e \<in> E IG1. src e = n \<and> type\<^sub>e e = et}"
        proof
          assume assumpt: "x \<in> E IG1 \<union> E IG2 \<and> src x = n \<and> type\<^sub>e x = et"
          then have "x \<notin> E IG2"
            using et_in_e combine_edges_distinct first_instance_graph_valid second_instance_graph_valid
            using instance_graph.structure_edges_wellformed_edge_type_alt
            by blast
          then have "x \<in> E IG1 \<and> src x = n \<and> type\<^sub>e x = et"
            using assumpt
            by simp
          then show "x \<in> {e \<in> E IG1. src e = n \<and> type\<^sub>e e = et}"
            by simp
        qed
      qed
    next
      show "{e \<in> E IG1. src e = n \<and> type\<^sub>e e = et} \<subseteq> {e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et}"
        by auto
    qed
    have "card {e \<in> E IG1. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG1) et)"
      using et_in_e n_in_in_igs edge_of_type
      by (fact validity_outgoing_mult_first)
    then show "card {e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et} in m_out (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et)"
      using mult_et set_et
      by simp
  next
    assume et_in_e: "et \<in> ET (TG IG2)"
    then have mult_et: "m_out (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et) = m_out (mult (TG IG2) et)"
      unfolding tg_combine_mult_def
      using combine_edges_distinct
      by auto
    have set_et: "{e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et} = {e \<in> E IG2. src e = n \<and> type\<^sub>e e = et}"
    proof
      show "{e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et} \<subseteq> {e \<in> E IG2. src e = n \<and> type\<^sub>e e = et}"
      proof
        fix x
        assume "x \<in> {e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et}"
        then show "x \<in> {e \<in> E IG2. src e = n \<and> type\<^sub>e e = et}"
        proof
          assume assumpt: "x \<in> E IG1 \<union> E IG2 \<and> src x = n \<and> type\<^sub>e x = et"
          then have "x \<notin> E IG1"
            using et_in_e combine_edges_distinct first_instance_graph_valid second_instance_graph_valid
            using instance_graph.structure_edges_wellformed_edge_type_alt
            by blast
          then have "x \<in> E IG2 \<and> src x = n \<and> type\<^sub>e x = et"
            using assumpt
            by simp
          then show "x \<in> {e \<in> E IG2. src e = n \<and> type\<^sub>e e = et}"
            by simp
        qed
      qed
    next
      show "{e \<in> E IG2. src e = n \<and> type\<^sub>e e = et} \<subseteq> {e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et}"
        by auto
    qed
    have "card {e \<in> E IG2. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG2) et)"
      using et_in_e n_in_in_igs edge_of_type
      by (fact validity_outgoing_mult_second)
    then show "card {e \<in> E IG1 \<union> E IG2. src e = n \<and> type\<^sub>e e = et} in m_out (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et)"
      using mult_et set_et
      by simp
  qed
next
  fix et n
  assume et_in_tg_e: "et \<in> ET (TG IG1) \<union> ET (TG IG2)"
  assume n_in_in_igs: "n \<in> N IG1 \<union> N IG2"
  assume edge_of_type: "(type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
  show "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et} in
      m_in (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et)"
    using et_in_tg_e edge_of_type
  proof (elim UnE)
    assume et_in_e: "et \<in> ET (TG IG1)"
    then have mult_et: "m_in (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et) = m_in (mult (TG IG1) et)"
      unfolding tg_combine_mult_def
      using combine_edges_distinct
      by auto
    have set_et: "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et} = {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et}"
    proof
      show "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et} \<subseteq> {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et}"
      proof
        fix x
        assume "x \<in> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et}"
        then show "x \<in> {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et}"
        proof
          assume assumpt: "x \<in> E IG1 \<union> E IG2 \<and> tgt x = n \<and> type\<^sub>e x = et"
          then have "x \<notin> E IG2"
            using et_in_e combine_edges_distinct first_instance_graph_valid second_instance_graph_valid
            using instance_graph.structure_edges_wellformed_edge_type_alt
            by blast
          then have "x \<in> E IG1 \<and> tgt x = n \<and> type\<^sub>e x = et"
            using assumpt
            by simp
          then show "x \<in> {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et}"
            by simp
        qed
      qed
    next
      show "{e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et} \<subseteq> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et}"
        by auto
    qed
    have "card {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG1) et)"
      using et_in_e n_in_in_igs edge_of_type
      by (fact validity_ingoing_mult_first)
    then show "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et} in m_in (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et)"
      using mult_et set_et
      by simp
  next
    assume et_in_e: "et \<in> ET (TG IG2)"
    then have mult_et: "m_in (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et) = m_in (mult (TG IG2) et)"
      unfolding tg_combine_mult_def
      using combine_edges_distinct
      by auto
    have set_et: "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et} = {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et}"
    proof
      show "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et} \<subseteq> {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et}"
      proof
        fix x
        assume "x \<in> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et}"
        then show "x \<in> {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et}"
        proof
          assume assumpt: "x \<in> E IG1 \<union> E IG2 \<and> tgt x = n \<and> type\<^sub>e x = et"
          then have "x \<notin> E IG1"
            using et_in_e combine_edges_distinct first_instance_graph_valid second_instance_graph_valid
            using instance_graph.structure_edges_wellformed_edge_type_alt
            by blast
          then have "x \<in> E IG2 \<and> tgt x = n \<and> type\<^sub>e x = et"
            using assumpt
            by simp
          then show "x \<in> {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et}"
            by simp
        qed
      qed
    next
      show "{e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et} \<subseteq> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et}"
        by auto
    qed
    have "card {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG2) et)"
      using et_in_e n_in_in_igs edge_of_type
      by (fact validity_ingoing_mult_second)
    then show "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e = et} in m_in (tg_combine_mult (ET (TG IG1)) (mult (TG IG1)) (ET (TG IG2)) (mult (TG IG2)) et)"
      using mult_et set_et
      by simp
  qed
next
  fix n
  assume "n \<in> N IG1 \<union> N IG2"
  then have n_in_in_igs: "n \<in> N IG1 \<inter> N IG2 \<or> n \<in> N IG1 - N IG2 \<or> n \<in> N IG2 - N IG1"
    by auto
  then show "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<le> 1"
  proof (elim disjE)
    assume "n \<in> N IG1 \<inter> N IG2"
    then show "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<le> 1"
      by (fact assms)
  next
    assume n_in_ig1_not_ig2: "n \<in> N IG1 - N IG2"
    have set_ie_eq: "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} = 
        {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1)}"
    proof
      show "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}
        \<subseteq> {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1)}"
      proof
        fix x
        assume "x \<in> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
        then show "x \<in> {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1)}"
        proof
          assume assumpt: "x \<in> E IG1 \<union> E IG2 \<and> tgt x = n \<and> type\<^sub>e x \<in> contains (TG IG1) \<union> contains (TG IG2)"
          then have x_not_in_ig2: "x \<notin> E IG2"
            using n_in_ig1_not_ig2 second_instance_graph_valid instance_graph.structure_edges_wellformed_tgt_node_alt
            by blast
          then have x_in_ig1: "x \<in> E IG1"
            using assumpt
            by simp
          then have "type\<^sub>e x \<in> ET (TG IG1)"
            using first_instance_graph_valid instance_graph.structure_edges_wellformed_edge_type_alt
            by blast
          then have "type\<^sub>e x \<notin> contains (TG IG2)"
            using combine_edges_distinct second_instance_graph_valid 
            using instance_graph.validity_type_graph type_graph.structure_contains_wellformed
            by blast
          then have "type\<^sub>e x \<in> contains (TG IG1)"
            using assumpt
            by simp
          then show "x \<in> {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1)}"
            using assumpt x_in_ig1
            by simp
        qed
      qed
    next
      show "{e \<in> E IG1. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1)}
        \<subseteq> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
        by auto
    qed
    have "n \<in> N IG1"
      using n_in_ig1_not_ig2
      by simp
    then have "card {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1)} \<le> 1"
      using first_instance_graph_valid instance_graph.validity_contained_node
      by simp
    then show "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<le> 1"
      using set_ie_eq
      by simp
  next
    assume n_in_ig2_not_ig1: "n \<in> N IG2 - N IG1"
    have set_ie_eq: "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} = 
        {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG2)}"
    proof
      show "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}
        \<subseteq> {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG2)}"
      proof
        fix x
        assume "x \<in> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
        then show "x \<in> {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG2)}"
        proof
          assume assumpt: "x \<in> E IG1 \<union> E IG2 \<and> tgt x = n \<and> type\<^sub>e x \<in> contains (TG IG1) \<union> contains (TG IG2)"
          then have x_not_in_ig1: "x \<notin> E IG1"
            using n_in_ig2_not_ig1 first_instance_graph_valid instance_graph.structure_edges_wellformed_tgt_node_alt
            by blast
          then have x_in_ig2: "x \<in> E IG2"
            using assumpt
            by simp
          then have "type\<^sub>e x \<in> ET (TG IG2)"
            using second_instance_graph_valid instance_graph.structure_edges_wellformed_edge_type_alt
            by blast
          then have "type\<^sub>e x \<notin> contains (TG IG1)"
            using combine_edges_distinct first_instance_graph_valid 
            using instance_graph.validity_type_graph type_graph.structure_contains_wellformed
            by blast
          then have "type\<^sub>e x \<in> contains (TG IG2)"
            using assumpt
            by simp
          then show "x \<in> {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG2)}"
            using assumpt x_in_ig2
            by simp
        qed
      qed
    next
      show "{e \<in> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG2)}
        \<subseteq> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
        by auto
    qed
    have "n \<in> N IG2"
      using n_in_ig2_not_ig1
      by simp
    then have "card {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG2)} \<le> 1"
      using second_instance_graph_valid instance_graph.validity_contained_node
      by simp
    then show "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<le> 1"
      using set_ie_eq
      by simp
  qed
next
  have containment_relation_def: "{e \<in> E IG1 \<union> E IG2. type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} = 
    {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
  proof
    show "{e \<in> E IG1 \<union> E IG2. type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<subseteq> 
      {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
    proof
      fix x
      assume "x \<in> {e \<in> E IG1 \<union> E IG2. 
        type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
      then show "x \<in> {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> 
        {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
      proof
        assume assump: "x \<in> E IG1 \<union> E IG2 \<and> type\<^sub>e x \<in> contains (TG IG1) \<union> contains (TG IG2)"
        then have in_e_cases: "x \<in> E IG1 \<union> E IG2"
          by simp
        have type_cases: "type\<^sub>e x \<in> contains (TG IG1) \<union> contains (TG IG2)"
          using assump
          by simp
        show "x \<in> {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> 
          {e \<in> E IG2. 
          type\<^sub>e e \<in> contains (TG IG2)}"
          using in_e_cases type_cases
        proof (elim UnE)
          assume x_def: "x \<in> E IG1"
          assume type_x_def: "type\<^sub>e x \<in> contains (TG IG1)"
          show ?thesis
            using x_def type_x_def
            by blast
        next
          assume "x \<in> E IG1"
          then have type_in_ig: "type\<^sub>e x \<in> ET (TG IG1)"
            using assms(1) instance_graph.structure_edges_wellformed_edge_type_alt
            by blast
          assume "type\<^sub>e x \<in> contains (TG IG2)"
          then have "type\<^sub>e x \<in> ET (TG IG2)"
            by (simp add: instance_graph.validity_type_graph second_instance_graph_valid type_graph.structure_contains_wellformed)
          then have "type\<^sub>e x \<notin> ET (TG IG1)"
            using combine_edges_distinct
            by blast
          then show ?thesis
            using type_in_ig
            by simp
        next
          assume "x \<in> E IG2"
          then have "type\<^sub>e x \<in> ET (TG IG2)"
            using second_instance_graph_valid instance_graph.structure_edges_wellformed_edge_type_alt
            by blast
          then have "type\<^sub>e x \<notin> ET (TG IG1)"
            using combine_edges_distinct
            by blast
          then have type_not_in_ig: "type\<^sub>e x \<notin> contains (TG IG1)"
            using instance_graph.validity_type_graph first_instance_graph_valid type_graph.structure_contains_wellformed
            by blast
          assume "type\<^sub>e x \<in> contains (TG IG1)"
          then show ?thesis
            using type_not_in_ig
            by simp
        next
          assume x_def: "x \<in> E IG2"
          assume type_x_def: "type\<^sub>e x \<in> contains (TG IG2)"
          show ?thesis
            using x_def type_x_def
            by blast
        qed
      qed
    qed
  next
    show "{e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}
      \<subseteq> {e \<in> E IG1 \<union> E IG2. type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
    proof
      fix x
      assume "x \<in> {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
      then show "x \<in> {e \<in> E IG1 \<union> E IG2. type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
      proof (elim UnE)
        assume "x \<in> {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)}"
        then show ?thesis
          by simp
      next
        assume "x \<in> {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
        then show ?thesis
          by simp
      qed
    qed
  qed
  have "irrefl ((edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+)"
    by (fact validity_containment)
  then have "irrefl ((edge_to_tuple ` ({e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}))\<^sup>+)"
    using image_Un
    by metis
  then show "irrefl ((edge_to_tuple ` {e \<in> E IG1 \<union> E IG2. type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)})\<^sup>+)"
    using containment_relation_def
    by simp
qed (simp_all add: assms)

lemma ig_combine_merge_no_containment_imod1_correct[intro]:
  assumes first_instance_graph_valid: "instance_graph IG1"
  assumes second_instance_graph_valid: "instance_graph IG2"
  assumes type_graph_combination_valid: "type_graph (tg_combine (TG IG1) (TG IG2))"
  assumes combine_edges_distinct: "ET (TG IG1) \<inter> ET (TG IG2) = {}"
  assumes combine_no_containment: "contains (TG IG1) = {}"
  assumes validity_identity: "\<And>i. i \<in> Id IG1 \<Longrightarrow> i \<in> Id IG2 \<Longrightarrow> ident IG1 i = ident IG2 i"
  assumes validity_outgoing_mult_first: "\<And>et n. et \<in> ET (TG IG1) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG1) et)"
  assumes validity_outgoing_mult_second: "\<And>et n. et \<in> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG2. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG2) et)"
  assumes validity_ingoing_mult_first: "\<And>et n. et \<in> ET (TG IG1) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG1) et)"
  assumes validity_ingoing_mult_second: "\<And>et n. et \<in> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG2) et)"
  shows "instance_graph (ig_combine IG1 IG2)"
proof (intro ig_combine_merge_correct)
  show "\<And>et n. et \<in> ET (TG IG1) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG1) et)"
    by (fact validity_outgoing_mult_first)
next
  show "\<And>et n. et \<in> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG2. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG2) et)"
    by (fact validity_outgoing_mult_second)
next
  show "\<And>et n. et \<in> ET (TG IG1) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG1) et)"
    by (fact validity_ingoing_mult_first)
next
  show "\<And>et n. et \<in> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG2) et)"
    by (fact validity_ingoing_mult_second)
next
  fix n
  assume n_in_both: "n \<in> N IG1 \<inter> N IG2"
  have "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} = {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG2)}"
  proof
    show "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<subseteq> {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG2)}"
    proof
      fix x
      assume x_in_edges: "x \<in> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
      then have "type\<^sub>e x \<in> contains (TG IG1) \<union> contains (TG IG2)"
        by blast
      then have type_x_in_contains_tg2: "type\<^sub>e x \<in> contains (TG IG2)"
        using combine_no_containment
        by blast
      have tgt_x_is_n: "tgt x = n"
        using x_in_edges
        by simp
      have "x \<in> E IG1 \<union> E IG2"
        using x_in_edges
        by simp
      then show "x \<in> {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG2)}"
      proof (elim UnE)
        assume x_in_ig1: "x \<in> E IG1"
        then have "type\<^sub>e x \<in> ET (TG IG1)"
          using first_instance_graph_valid instance_graph.structure_edges_wellformed_edge_type_alt
          by blast
        then have "type\<^sub>e x \<notin> ET (TG IG2)"
          using combine_edges_distinct
          by blast
        then have "type\<^sub>e x \<notin> contains (TG IG2)"
          using second_instance_graph_valid instance_graph.validity_type_graph type_graph.structure_contains_wellformed
          by blast
        then show ?thesis
          using type_x_in_contains_tg2
          by simp
      next
        assume x_in_ig2: "x \<in> E IG2"
        then show ?thesis
          using type_x_in_contains_tg2 tgt_x_is_n
          by simp
      qed
    qed
  next
    show "{e \<in> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG2)} \<subseteq> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
    proof
      fix x
      assume "x \<in> {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG2)}"
      then have "x \<in> E IG2 \<and> tgt x = n \<and> type\<^sub>e x \<in> contains (TG IG2)"
        by blast
      then show "x \<in> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
        by simp
    qed
  qed
  then show "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<le> 1"
    using second_instance_graph_valid instance_graph.validity_contained_node n_in_both
    by fastforce
next
  have "{e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} = {}"
  proof
    show "{e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<subseteq> {}"
    proof
      fix x
      assume x_in_edges: "x \<in> {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)}"
      then have "type\<^sub>e x \<in> contains (TG IG1)"
        by blast
      then show "x \<in> {}"
        using combine_no_containment
        by simp
    qed
  next
    show "{} \<subseteq> {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)}"
      by simp
  qed
  then have "edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} = {}"
    by blast
  then have "edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)} = 
    edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
    by blast
  then have containment_ig1_empty: "(edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+ = 
    (edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
    by fastforce
  have "irrefl ((edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+)"
  proof (intro validity_containment_alt)
    fix e
    assume e_in_ig2: "e \<in> E IG2"
    then show "src e \<in> N IG2 \<and> tgt e \<in> N IG2"
      using second_instance_graph_valid instance_graph.structure_edges_wellformed_src_node_alt instance_graph.structure_edges_wellformed_tgt_node_alt
      by metis
  next
    fix p
    show "\<not>pre_digraph.cycle (instance_graph_containment_proj IG2) p"
      using second_instance_graph_valid instance_graph.validity_containment
      by blast
  qed
  then show "irrefl ((edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+)"
    using second_instance_graph_valid instance_graph.validity_contained_node containment_ig1_empty
    by simp
qed (simp_all add: assms)

lemma ig_combine_merge_no_containment_imod2_correct[intro]:
  assumes first_instance_graph_valid: "instance_graph IG1"
  assumes second_instance_graph_valid: "instance_graph IG2"
  assumes type_graph_combination_valid: "type_graph (tg_combine (TG IG1) (TG IG2))"
  assumes combine_edges_distinct: "ET (TG IG1) \<inter> ET (TG IG2) = {}"
  assumes combine_no_containment: "contains (TG IG2) = {}"
  assumes validity_identity: "\<And>i. i \<in> Id IG1 \<Longrightarrow> i \<in> Id IG2 \<Longrightarrow> ident IG1 i = ident IG2 i"
  assumes validity_outgoing_mult_first: "\<And>et n. et \<in> ET (TG IG1) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG1) et)"
  assumes validity_outgoing_mult_second: "\<And>et n. et \<in> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG2. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG2) et)"
  assumes validity_ingoing_mult_first: "\<And>et n. et \<in> ET (TG IG1) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG1) et)"
  assumes validity_ingoing_mult_second: "\<And>et n. et \<in> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG2) et)"
  shows "instance_graph (ig_combine IG1 IG2)"
proof (intro ig_combine_merge_correct)
  show "\<And>et n. et \<in> ET (TG IG1) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG1) et)"
    by (fact validity_outgoing_mult_first)
next
  show "\<And>et n. et \<in> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG2. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG2) et)"
    by (fact validity_outgoing_mult_second)
next
  show "\<And>et n. et \<in> ET (TG IG1) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG1) et)"
    by (fact validity_ingoing_mult_first)
next
  show "\<And>et n. et \<in> ET (TG IG2) \<Longrightarrow> n \<in> N IG1 \<union> N IG2 \<Longrightarrow> 
    (type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+ \<Longrightarrow> 
    card {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG2) et)"
    by (fact validity_ingoing_mult_second)
next
  fix n
  assume n_in_both: "n \<in> N IG1 \<inter> N IG2"
  have "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} = {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1)}"
  proof
    show "{e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<subseteq> {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1)}"
    proof
      fix x
      assume x_in_edges: "x \<in> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
      then have "type\<^sub>e x \<in> contains (TG IG1) \<union> contains (TG IG2)"
        by blast
      then have type_x_in_contains_tg1: "type\<^sub>e x \<in> contains (TG IG1)"
        using combine_no_containment
        by blast
      have tgt_x_is_n: "tgt x = n"
        using x_in_edges
        by simp
      have "x \<in> E IG1 \<union> E IG2"
        using x_in_edges
        by simp
      then show "x \<in> {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1)}"
      proof (elim UnE)
        assume x_in_ig1: "x \<in> E IG1"
        then show ?thesis
          using type_x_in_contains_tg1 tgt_x_is_n
          by simp
      next
        assume x_in_ig2: "x \<in> E IG2"
        then have "type\<^sub>e x \<in> ET (TG IG2)"
          using second_instance_graph_valid instance_graph.structure_edges_wellformed_edge_type_alt
          by blast
        then have "type\<^sub>e x \<notin> ET (TG IG1)"
          using combine_edges_distinct
          by blast
        then have "type\<^sub>e x \<notin> contains (TG IG1)"
          using first_instance_graph_valid instance_graph.validity_type_graph type_graph.structure_contains_wellformed
          by blast
        then show ?thesis
          using type_x_in_contains_tg1
          by simp
      qed
    qed
  next
    show "{e \<in> E IG1. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1)} \<subseteq> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
    proof
      fix x
      assume "x \<in> {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1)}"
      then have "x \<in> E IG1 \<and> tgt x = n \<and> type\<^sub>e x \<in> contains (TG IG1)"
        by blast
      then show "x \<in> {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)}"
        by simp
    qed
  qed
  then show "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<le> 1"
    using first_instance_graph_valid instance_graph.validity_contained_node n_in_both
    by fastforce
next
  have "{e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)} = {}"
  proof
    show "{e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)} \<subseteq> {}"
    proof
      fix x
      assume x_in_edges: "x \<in> {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
      then have "type\<^sub>e x \<in> contains (TG IG2)"
        by blast
      then show "x \<in> {}"
        using combine_no_containment
        by simp
    qed
  next
    show "{} \<subseteq> {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
      by simp
  qed
  then have "edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)} = {}"
    by blast
  then have "edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)} = 
    edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)}"
    by blast
  then have containment_ig2_empty: "(edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+ = 
    (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+"
    by fastforce
  have "irrefl ((edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+)"
  proof (intro validity_containment_alt)
    fix e
    assume e_in_ig2: "e \<in> E IG1"
    then show "src e \<in> N IG1 \<and> tgt e \<in> N IG1"
      using first_instance_graph_valid instance_graph.structure_edges_wellformed_src_node_alt instance_graph.structure_edges_wellformed_tgt_node_alt
      by metis
  next
    fix p
    show "\<not>pre_digraph.cycle (instance_graph_containment_proj IG1) p"
      using first_instance_graph_valid instance_graph.validity_containment
      by blast
  qed
  then show "irrefl ((edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+)"
    using second_instance_graph_valid instance_graph.validity_contained_node containment_ig2_empty
    by simp
qed (simp_all add: assms)

lemma ig_combine_distinct_correct[intro]:
  assumes first_instance_graph_valid: "instance_graph IG1"
  assumes second_instance_graph_valid: "instance_graph IG2"
  assumes combine_nodes_distinct: "NT (TG IG1) \<inter> NT (TG IG2) = {}"
  assumes validity_identity: "\<And>i. i \<in> Id IG1 \<Longrightarrow> i \<in> Id IG2 \<Longrightarrow> ident IG1 i = ident IG2 i"
  shows "instance_graph (ig_combine IG1 IG2)"
proof (intro ig_combine_merge_correct)
  show "type_graph (tg_combine (TG IG1) (TG IG2))"
  proof (intro tg_combine_distinct_correct)
    show "type_graph (TG IG1)"
      using first_instance_graph_valid
      by (fact instance_graph.validity_type_graph)
  next
    show "type_graph (TG IG2)"
      using second_instance_graph_valid
      by (fact instance_graph.validity_type_graph)
  qed (simp_all add: assms)
next
  show "ET (TG IG1) \<inter> ET (TG IG2) = {}"
    using combine_nodes_distinct disjoint_iff_not_equal first_instance_graph_valid instance_graph.validity_type_graph 
    using second_instance_graph_valid type_graph.structure_edges_wellformed_tgt_node_alt
    by metis
next
  fix et n
  assume et_in_tg_ig: "et \<in> ET (TG IG1)"
  then have "src et \<in> NT (TG IG1)"
    using instance_graph.validity_type_graph first_instance_graph_valid type_graph.structure_edges_wellformed_alt 
    by blast
  then have src_et_not_tg2: "src et \<notin> NT (TG IG2)"
    using combine_nodes_distinct
    by blast
  assume n_in_in_ig: "n \<in> N IG1 \<union> N IG2"
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG1) \<union> inh (TG IG2)"
    using combine_nodes_distinct instance_graph.validity_type_graph 
    using first_instance_graph_valid second_instance_graph_valid tg_combine_distinct_inh 
    by blast
  then have type_in_inh_ig: "(type\<^sub>n n, src et) \<in> inh (TG IG1)"
    using UnE type_graph.structure_inheritance_wellformed_second_node second_instance_graph_valid 
    using instance_graph.validity_type_graph src_et_not_tg2
    by metis
  then have "type\<^sub>n n \<in> NT (TG IG1)"
    using first_instance_graph_valid instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node
    by blast
  then have "type\<^sub>n n \<notin> NT (TG IG2)"
    using combine_nodes_distinct
    by blast
  then have "n \<notin> N IG2"
    using second_instance_graph_valid instance_graph.validity_node_typed
    by blast
  then have "n \<in> N IG1"
    using n_in_in_ig
    by simp
  then show "card {e \<in> E IG1. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG1) et)"
    using type_in_inh_ig et_in_tg_ig first_instance_graph_valid instance_graph.validity_outgoing_mult
    by simp
next
  fix et n
  assume et_in_tg_ig: "et \<in> ET (TG IG2)"
  then have "src et \<in> NT (TG IG2)"
    using instance_graph.validity_type_graph second_instance_graph_valid type_graph.structure_edges_wellformed_alt 
    by blast
  then have src_et_not_tg1: "src et \<notin> NT (TG IG1)"
    using combine_nodes_distinct
    by blast
  assume n_in_in_ig: "n \<in> N IG1 \<union> N IG2"
  assume "(type\<^sub>n n, src et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
  then have "(type\<^sub>n n, src et) \<in> inh (TG IG1) \<union> inh (TG IG2)"
    using combine_nodes_distinct instance_graph.validity_type_graph 
    using first_instance_graph_valid second_instance_graph_valid tg_combine_distinct_inh 
    by blast
  then have type_in_inh_ig: "(type\<^sub>n n, src et) \<in> inh (TG IG2)"
    using UnE type_graph.structure_inheritance_wellformed_second_node first_instance_graph_valid 
    using instance_graph.validity_type_graph src_et_not_tg1
    by metis
  then have "type\<^sub>n n \<in> NT (TG IG2)"
    using second_instance_graph_valid instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node
    by blast
  then have "type\<^sub>n n \<notin> NT (TG IG1)"
    using combine_nodes_distinct
    by blast
  then have "n \<notin> N IG1"
    using first_instance_graph_valid instance_graph.validity_node_typed
    by blast
  then have "n \<in> N IG2"
    using n_in_in_ig
    by simp
  then show "card {e \<in> E IG2. src e = n \<and> type\<^sub>e e = et} in m_out (mult (TG IG2) et)"
    using type_in_inh_ig et_in_tg_ig second_instance_graph_valid instance_graph.validity_outgoing_mult
    by simp
next
  fix et n
  assume et_in_tg_ig: "et \<in> ET (TG IG1)"
  then have "tgt et \<in> NT (TG IG1)"
    using instance_graph.validity_type_graph first_instance_graph_valid type_graph.structure_edges_wellformed_alt 
    by blast
  then have tgt_et_not_tg2: "tgt et \<notin> NT (TG IG2)"
    using combine_nodes_distinct
    by blast
  assume n_in_in_ig: "n \<in> N IG1 \<union> N IG2"
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
  then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG1) \<union> inh (TG IG2)"
    using combine_nodes_distinct instance_graph.validity_type_graph 
    using first_instance_graph_valid second_instance_graph_valid tg_combine_distinct_inh 
    by blast
  then have type_in_inh_ig: "(type\<^sub>n n, tgt et) \<in> inh (TG IG1)"
    using UnE type_graph.structure_inheritance_wellformed_second_node second_instance_graph_valid 
    using instance_graph.validity_type_graph tgt_et_not_tg2
    by metis
  then have "type\<^sub>n n \<in> NT (TG IG1)"
    using first_instance_graph_valid instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node
    by blast
  then have "type\<^sub>n n \<notin> NT (TG IG2)"
    using combine_nodes_distinct
    by blast
  then have "n \<notin> N IG2"
    using second_instance_graph_valid instance_graph.validity_node_typed
    by blast
  then have "n \<in> N IG1"
    using n_in_in_ig
    by simp
  then show "card {e \<in> E IG1. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG1) et)"
    using type_in_inh_ig et_in_tg_ig first_instance_graph_valid instance_graph.validity_ingoing_mult
    by simp
next
  fix et n
  assume et_in_tg_ig: "et \<in> ET (TG IG2)"
  then have "tgt et \<in> NT (TG IG2)"
    using instance_graph.validity_type_graph second_instance_graph_valid type_graph.structure_edges_wellformed_alt 
    by blast
  then have tgt_et_not_tg1: "tgt et \<notin> NT (TG IG1)"
    using combine_nodes_distinct
    by blast
  assume n_in_in_ig: "n \<in> N IG1 \<union> N IG2"
  assume "(type\<^sub>n n, tgt et) \<in> (inh (TG IG1) \<union> inh (TG IG2))\<^sup>+"
  then have "(type\<^sub>n n, tgt et) \<in> inh (TG IG1) \<union> inh (TG IG2)"
    using combine_nodes_distinct instance_graph.validity_type_graph 
    using first_instance_graph_valid second_instance_graph_valid tg_combine_distinct_inh 
    by blast
  then have type_in_inh_ig: "(type\<^sub>n n, tgt et) \<in> inh (TG IG2)"
    using UnE type_graph.structure_inheritance_wellformed_second_node first_instance_graph_valid 
    using instance_graph.validity_type_graph tgt_et_not_tg1
    by metis
  then have "type\<^sub>n n \<in> NT (TG IG2)"
    using second_instance_graph_valid instance_graph.validity_type_graph type_graph.structure_inheritance_wellformed_first_node
    by blast
  then have "type\<^sub>n n \<notin> NT (TG IG1)"
    using combine_nodes_distinct
    by blast
  then have "n \<notin> N IG1"
    using first_instance_graph_valid instance_graph.validity_node_typed
    by blast
  then have "n \<in> N IG2"
    using n_in_in_ig
    by simp
  then show "card {e \<in> E IG2. tgt e = n \<and> type\<^sub>e e = et} in m_in (mult (TG IG2) et)"
    using type_in_inh_ig et_in_tg_ig second_instance_graph_valid instance_graph.validity_ingoing_mult
    by simp
next
  fix n
  assume "n \<in> N IG1 \<inter> N IG2"
  then have "type\<^sub>n n \<in> NT (TG IG1) \<inter> NT (TG IG2)"
    using first_instance_graph_valid second_instance_graph_valid instance_graph.validity_node_typed
    by blast
  then show "card {e \<in> E IG1 \<union> E IG2. tgt e = n \<and> type\<^sub>e e \<in> contains (TG IG1) \<union> contains (TG IG2)} \<le> 1"
    using combine_nodes_distinct
    by simp
next
  have irrefl_ig1: "irrefl ((edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+)"
    using first_instance_graph_valid instance_graph.validity_containment_alt'
    by blast
  have irrefl_ig2: "irrefl ((edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+)"
    using second_instance_graph_valid instance_graph.validity_containment_alt'
    by blast
  have "(edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+ = 
    (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+ \<union> (edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
  proof
    show "(edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+ \<subseteq> 
      (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+ \<union> (edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
    proof
      fix x
      assume "x \<in> (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
      then show "x \<in> (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+ \<union> (edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
      proof (induct x)
        case (Pair a b)
        then show ?case
        proof (induct)
          case (base y)
          then show ?case
            by blast
        next
          case (step y z)
          show ?case
            using step.hyps(3)
          proof (elim UnE)
            assume ay_in_containment_set: "(a, y) \<in> (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+"
            then have "y \<in> N IG1"
            proof (induct)
              case (base m)
              then show ?case
              proof
                fix x
                assume x_in_set: "x \<in> {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)}"
                assume tuple_def: "(a, m) = edge_to_tuple x"
                show "m \<in> N IG1"
                  using tuple_def x_in_set first_instance_graph_valid instance_graph.structure_edges_wellformed_tgt_node_alt
                  by fastforce
              qed
            next
              case (step m n)
              show ?case
                using step.hyps(2)
              proof
                fix x
                assume x_in_set: "x \<in> {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)}"
                assume tuple_def: "(m, n) = edge_to_tuple x"
                show "n \<in> N IG1"
                  using tuple_def x_in_set first_instance_graph_valid instance_graph.structure_edges_wellformed_tgt_node_alt
                  by fastforce
              qed
            qed
            then have "type\<^sub>n y \<in> NT (TG IG1)"
              using first_instance_graph_valid instance_graph.validity_node_typed
              by blast
            then have "type\<^sub>n y \<notin> NT (TG IG2)"
              using combine_nodes_distinct
              by blast
            then have "y \<notin> N IG2"
              using second_instance_graph_valid instance_graph.validity_node_typed
              by blast
            then have "(y, z) \<notin> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
              using second_instance_graph_valid instance_graph.structure_edges_wellformed_src_node_alt
              by fastforce
            then have "(y, z) \<in> edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)}"
              using step.hyps(2)
              by simp
            then have "(a, z) \<in> (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+"
              using ay_in_containment_set
              by simp
            then show ?thesis
              by simp
          next
            assume ay_in_containment_set: "(a, y) \<in> (edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
            then have "y \<in> N IG2"
            proof (induct)
              case (base m)
              then show ?case
              proof
                fix x
                assume x_in_set: "x \<in> {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
                assume tuple_def: "(a, m) = edge_to_tuple x"
                show "m \<in> N IG2"
                  using tuple_def x_in_set second_instance_graph_valid instance_graph.structure_edges_wellformed_tgt_node_alt
                  by fastforce
              qed
            next
              case (step m n)
              show ?case
                using step.hyps(2)
              proof
                fix x
                assume x_in_set: "x \<in> {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
                assume tuple_def: "(m, n) = edge_to_tuple x"
                show "n \<in> N IG2"
                  using tuple_def x_in_set second_instance_graph_valid instance_graph.structure_edges_wellformed_tgt_node_alt
                  by fastforce
              qed
            qed
            then have "type\<^sub>n y \<in> NT (TG IG2)"
              using second_instance_graph_valid instance_graph.validity_node_typed
              by blast
            then have "type\<^sub>n y \<notin> NT (TG IG1)"
              using combine_nodes_distinct
              by blast
            then have "y \<notin> N IG1"
              using first_instance_graph_valid instance_graph.validity_node_typed
              by blast
            then have "(y, z) \<notin> edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)}"
              using first_instance_graph_valid instance_graph.structure_edges_wellformed_src_node_alt
              by fastforce
            then have "(y, z) \<in> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)}"
              using step.hyps(2)
              by simp
            then have "(a, z) \<in> (edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
              using ay_in_containment_set
              by simp
            then show ?thesis
              by simp
          qed
        qed
      qed
    qed
  next
    show "(edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+ \<union> (edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+ \<subseteq> 
      (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
    proof
      fix x
      assume "x \<in> (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+ \<union> (edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
      then show "x \<in> (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
      proof (elim UnE)
        assume "x \<in> (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+"
        then show "x \<in> (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
        proof (induct x)
          case (Pair a b)
          then show ?case
          proof (induct)
            case (base y)
            then show ?case
              by blast
          next
            case (step y z)
            then have "(a, z) \<in> (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)})\<^sup>+"
              by simp
            then show ?case
              using step.hyps(2) step.hyps(3)
              by (simp add: trancl.trancl_into_trancl)
          qed
        qed
      next
        assume "x \<in> (edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
        then show "x \<in> (edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
        proof (induct x)
          case (Pair a b)
          then show ?case
          proof (induct)
            case (base y)
            then show ?case
              by blast
          next
            case (step y z)
            then have "(a, z) \<in> (edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+"
              by simp
            then show ?case
              using step.hyps(2) step.hyps(3)
              by (simp add: trancl.trancl_into_trancl)
          qed
        qed
      qed
    qed
  qed
  then show "irrefl ((edge_to_tuple ` {e \<in> E IG1. type\<^sub>e e \<in> contains (TG IG1)} \<union> edge_to_tuple ` {e \<in> E IG2. type\<^sub>e e \<in> contains (TG IG2)})\<^sup>+)"
    using irrefl_ig1 irrefl_ig2
    by (simp add: irrefl_def)
qed (simp_all add: assms)

end
