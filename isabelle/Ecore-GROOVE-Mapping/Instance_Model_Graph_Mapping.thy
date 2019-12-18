theory Instance_Model_Graph_Mapping
  imports 
    Main
    Type_Model_Graph_Mapping
    Ecore.Instance_Model_Combination
    GROOVE.Instance_Graph_Combination
begin

section "Merging mapping functions from instance models to instance graphs"

locale ig_combine_mapping_function =
  fixes f :: "('o, 't) instance_model \<Rightarrow> ('nt, 'lt, 'id) instance_graph"
  fixes Imod :: "('o, 't) instance_model"
  fixes IG :: "('nt, 'lt, 'id) instance_graph"
  assumes mapping_correct: "f Imod = IG"
  assumes func_tg: "\<And>ImodX. TG (f Imod) = TG (f (imod_combine Imod ImodX))"
  assumes subset_ids: "\<And>ImodX. Id (f Imod) \<subseteq> Id (f (imod_combine Imod ImodX))"
  assumes subset_nodes: "\<And>ImodX. N (f Imod) \<subseteq> N (f (imod_combine Imod ImodX))"
  assumes subset_edges: "\<And>ImodX. E (f Imod) \<subseteq> E (f (imod_combine Imod ImodX))"
  assumes func_ident: "\<And>ImodX i. i \<in> Id (f Imod) \<Longrightarrow> ident (f Imod) i = ident (f (imod_combine Imod ImodX)) i"

definition ig_combine_mapping :: "(('o, 't) instance_model \<Rightarrow> ('nt, 'lt, 'id) instance_graph) \<Rightarrow> ('nt, 'lt, 'id) instance_graph \<Rightarrow> (('o, 't) instance_model \<Rightarrow> ('nt, 'lt, 'id) instance_graph) \<Rightarrow> ('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('nt, 'lt, 'id) instance_graph" where
  "ig_combine_mapping f1 IG1 f2 IG2 Imod \<equiv> \<lparr>
    TG = tg_combine (TG (f1 Imod)) (TG (f2 Imod)),
    Id = {i \<in> Id (f1 Imod). i \<in> Id IG1} \<union> {i \<in> Id (f2 Imod). i \<in> Id IG2},
    N = {n \<in> N (f1 Imod). n \<in> N IG1} \<union> {n \<in> N (f2 Imod). n \<in> N IG2},
    E = {e \<in> E (f1 Imod). e \<in> E IG1} \<union> {e \<in> E (f2 Imod). e \<in> E IG2},
    ident = ig_combine_ident {i \<in> Id (f1 Imod). i \<in> Id IG1} (ident (f1 Imod)) {i \<in> Id (f2 Imod). i \<in> Id IG2} (ident (f2 Imod))
  \<rparr>"

lemma ig_combine_mapping_correct:
  assumes mapping_imod1: "ig_combine_mapping_function f1 Imod1 IG1"
  assumes mapping_imod2: "ig_combine_mapping_function f2 Imod2 IG2"
  shows "ig_combine_mapping (f1) IG1 (f2) IG2 (imod_combine Imod1 Imod2) = ig_combine IG1 IG2"
  unfolding ig_combine_mapping_def ig_combine_def
proof
  have ids_ig1: "{i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} = Id IG1"
  proof
    show "{i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} \<subseteq> Id IG1"
      by blast
  next
    show "Id IG1 \<subseteq> {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1}"
      using mapping_imod1 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_ids
      by blast
  qed
  have ids_ig2: "{i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} = Id IG2"
  proof
    show "{i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} \<subseteq> Id IG2"
      by blast
  next
    have "Id IG2 \<subseteq> {i \<in> Id (f2 (imod_combine Imod2 Imod1)). i \<in> Id IG2}"
      using mapping_imod2 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_ids
      by blast
    then show "Id IG2 \<subseteq> {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2}"
      using imod_combine_commute
      by metis
  qed
  show "tg_combine (TG (f1 (imod_combine Imod1 Imod2))) (TG (f2 (imod_combine Imod1 Imod2))) = tg_combine (TG IG1) (TG IG2) \<and>
    {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} \<union> {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} = Id IG1 \<union> Id IG2 \<and>
    {n \<in> N (f1 (imod_combine Imod1 Imod2)). n \<in> N IG1} \<union> {n \<in> N (f2 (imod_combine Imod1 Imod2)). n \<in> N IG2} = N IG1 \<union> N IG2 \<and>
    {e \<in> E (f1 (imod_combine Imod1 Imod2)). e \<in> E IG1} \<union> {e \<in> E (f2 (imod_combine Imod1 Imod2)). e \<in> E IG2} = E IG1 \<union> E IG2 \<and>
    ig_combine_ident {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} (ident (f1 (imod_combine Imod1 Imod2))) {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} (ident (f2 (imod_combine Imod1 Imod2))) = 
      ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) \<and>
    () = ()"
  proof (intro conjI)
    have "tg_combine (TG (f1 Imod1)) (TG (f2 Imod2)) = tg_combine (TG IG1) (TG IG2)"
      using ig_combine_mapping_function.mapping_correct mapping_imod1 mapping_imod2
      by blast
    then show "tg_combine (TG (f1 (imod_combine Imod1 Imod2))) (TG (f2 (imod_combine Imod1 Imod2))) = tg_combine (TG IG1) (TG IG2)"
      using ig_combine_mapping_function.func_tg imod_combine_commute mapping_imod1 mapping_imod2
      by metis
  next
    show "{i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} \<union> {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} = Id IG1 \<union> Id IG2"
      using ids_ig1 ids_ig2
      by blast
  next
    have nodes_ig1: "{n \<in> N (f1 (imod_combine Imod1 Imod2)). n \<in> N IG1} = N IG1"
    proof
      show "{n \<in> N (f1 (imod_combine Imod1 Imod2)). n \<in> N IG1} \<subseteq> N IG1"
        by blast
    next
      show "N IG1 \<subseteq> {n \<in> N (f1 (imod_combine Imod1 Imod2)). n \<in> N IG1}"
        using mapping_imod1 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_nodes
        by blast
    qed
    have nodes_ig2: "{n \<in> N (f2 (imod_combine Imod1 Imod2)). n \<in> N IG2} = N IG2"
    proof
      show "{n \<in> N (f2 (imod_combine Imod1 Imod2)). n \<in> N IG2} \<subseteq> N IG2"
        by blast
    next
      have "N IG2 \<subseteq> {n \<in> N (f2 (imod_combine Imod2 Imod1)). n \<in> N IG2}"
        using mapping_imod2 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_nodes
        by blast
      then show "N IG2 \<subseteq> {n \<in> N (f2 (imod_combine Imod1 Imod2)). n \<in> N IG2}"
        using imod_combine_commute
        by metis
    qed
    show "{n \<in> N (f1 (imod_combine Imod1 Imod2)). n \<in> N IG1} \<union> {n \<in> N (f2 (imod_combine Imod1 Imod2)). n \<in> N IG2} = N IG1 \<union> N IG2"
      using nodes_ig1 nodes_ig2
      by blast
  next
    have edges_ig1: "{e \<in> E (f1 (imod_combine Imod1 Imod2)). e \<in> E IG1} = E IG1"
    proof
      show "{e \<in> E (f1 (imod_combine Imod1 Imod2)). e \<in> E IG1} \<subseteq> E IG1"
        by blast
    next
      show "E IG1 \<subseteq> {e \<in> E (f1 (imod_combine Imod1 Imod2)). e \<in> E IG1}"
        using mapping_imod1 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_edges
        by blast
    qed
    have edges_ig2: "{e \<in> E (f2 (imod_combine Imod1 Imod2)). e \<in> E IG2} = E IG2"
    proof
      show "{e \<in> E (f2 (imod_combine Imod1 Imod2)). e \<in> E IG2} \<subseteq> E IG2"
        by blast
    next
      have "E IG2 \<subseteq> {e \<in> E (f2 (imod_combine Imod2 Imod1)). e \<in> E IG2}"
        using mapping_imod2 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_edges
        by blast
      then show "E IG2 \<subseteq> {e \<in> E (f2 (imod_combine Imod1 Imod2)). e \<in> E IG2}"
        using imod_combine_commute
        by metis
    qed
    show "{e \<in> E (f1 (imod_combine Imod1 Imod2)). e \<in> E IG1} \<union> {e \<in> E (f2 (imod_combine Imod1 Imod2)). e \<in> E IG2} = E IG1 \<union> E IG2"
      using edges_ig1 edges_ig2
      by blast
  next
    have "ig_combine_ident (Id IG1) (ident (f1 (imod_combine Imod1 Imod2))) (Id IG2) (ident (f2 (imod_combine Imod1 Imod2))) =
      ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2)"
    proof
      fix i
      have "i \<in> Id IG1 \<inter> Id IG2 \<or> i \<in> Id IG1 - Id IG2 \<or> i \<in> Id IG2 - Id IG1 \<or> i \<notin> Id IG1 \<union> Id IG2"
        by blast
      then show "ig_combine_ident (Id IG1) (ident (f1 (imod_combine Imod1 Imod2))) (Id IG2) (ident (f2 (imod_combine Imod1 Imod2))) i =
        ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i"
      proof (elim disjE)
        assume i_in_both: "i \<in> Id IG1 \<inter> Id IG2"
        show ?thesis
        proof (induct "ident IG1 i = ident IG2 i")
          case True
          then have ident_combine_def: "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG1 i"
            unfolding ig_combine_ident_def
            using i_in_both
            by simp
          have "ident (f1 (imod_combine Imod1 Imod2)) i = ident (f2 (imod_combine Imod1 Imod2)) i"
            using Int_iff True.hyps i_in_both ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.func_ident imod_combine_commute mapping_imod1 mapping_imod2
            by metis
          then have "ig_combine_ident (Id IG1) (ident (f1 (imod_combine Imod1 Imod2))) (Id IG2) (ident (f2 (imod_combine Imod1 Imod2))) i = ident (f1 (imod_combine Imod1 Imod2)) i"
            unfolding ig_combine_ident_def
            using i_in_both
            by simp
          then have "ig_combine_ident (Id IG1) (ident (f1 (imod_combine Imod1 Imod2))) (Id IG2) (ident (f2 (imod_combine Imod1 Imod2))) i = ident IG1 i"
            using i_in_both ig_combine_mapping_function.func_ident ig_combine_mapping_function.mapping_correct mapping_imod1
            by fastforce
          then show ?case
            by (simp add: ident_combine_def)
        next
          case False
          then have ident_combine_def: "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = invalid"
            unfolding ig_combine_ident_def
            using i_in_both
            by simp
          have "ident (f1 (imod_combine Imod1 Imod2)) i \<noteq> ident (f2 (imod_combine Imod1 Imod2)) i"
            using Int_iff False.hyps i_in_both ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.func_ident imod_combine_commute mapping_imod1 mapping_imod2
            by metis
          then have "ig_combine_ident (Id IG1) (ident (f1 (imod_combine Imod1 Imod2))) (Id IG2) (ident (f2 (imod_combine Imod1 Imod2))) i = invalid"
            unfolding ig_combine_ident_def
            using i_in_both
            by simp
          then show ?case
            by (simp add: ident_combine_def)
        qed
      next
        assume i_in_ig1: "i \<in> Id IG1 - Id IG2"
        then have ident_combine_def: "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG1 i"
          unfolding ig_combine_ident_def
          by simp
        have "ig_combine_ident (Id IG1) (ident (f1 (imod_combine Imod1 Imod2))) (Id IG2) (ident (f2 (imod_combine Imod1 Imod2))) i = ident (f1 (imod_combine Imod1 Imod2)) i"
          unfolding ig_combine_ident_def
          using i_in_ig1
          by simp
        then have "ig_combine_ident (Id IG1) (ident (f1 (imod_combine Imod1 Imod2))) (Id IG2) (ident (f2 (imod_combine Imod1 Imod2))) i = ident IG1 i"
          using i_in_ig1 ig_combine_mapping_function.func_ident ig_combine_mapping_function.mapping_correct mapping_imod1
          by fastforce
        then show ?thesis
          by (simp add: ident_combine_def)
      next
        assume i_in_ig2: "i \<in> Id IG2 - Id IG1"
        then have ident_combine_def: "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = ident IG2 i"
          unfolding ig_combine_ident_def
          by simp
        have "ig_combine_ident (Id IG1) (ident (f1 (imod_combine Imod1 Imod2))) (Id IG2) (ident (f2 (imod_combine Imod1 Imod2))) i = ident (f2 (imod_combine Imod1 Imod2)) i"
          unfolding ig_combine_ident_def
          using i_in_ig2
          by simp
        then have "ig_combine_ident (Id IG1) (ident (f1 (imod_combine Imod1 Imod2))) (Id IG2) (ident (f2 (imod_combine Imod1 Imod2))) i = ident IG2 i"
          using Diff_iff i_in_ig2 ig_combine_mapping_function.func_ident ig_combine_mapping_function.mapping_correct imod_combine_commute mapping_imod2
          by metis
        then show ?thesis
          by (simp add: ident_combine_def)
      next
        assume i_in_ig2: "i \<notin> Id IG1 \<union> Id IG2"
        then have ident_combine_def: "ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2) i = undefined"
          unfolding ig_combine_ident_def
          by simp
        have "ig_combine_ident (Id IG1) (ident (f1 (imod_combine Imod1 Imod2))) (Id IG2) (ident (f2 (imod_combine Imod1 Imod2))) i = undefined"
          unfolding ig_combine_ident_def
          using i_in_ig2
          by simp
        then show ?thesis
          by (simp add: ident_combine_def)
      qed
    qed
    then show "ig_combine_ident {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} (ident (f1 (imod_combine Imod1 Imod2))) {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} (ident (f2 (imod_combine Imod1 Imod2))) =
      ig_combine_ident (Id IG1) (ident IG1) (Id IG2) (ident IG2)"
      by (simp add: ids_ig1 ids_ig2)
  qed (simp)
qed

lemma ig_combine_mapping_function_correct:
  assumes mapping_imod1: "ig_combine_mapping_function f1 Imod1 IG1"
  assumes mapping_imod2: "ig_combine_mapping_function f2 Imod2 IG2"
  shows "ig_combine_mapping_function (ig_combine_mapping (f1) IG1 (f2) IG2) (imod_combine Imod1 Imod2) (ig_combine IG1 IG2)"
proof (intro ig_combine_mapping_function.intro)
  show "ig_combine_mapping f1 IG1 f2 IG2 (imod_combine Imod1 Imod2) = ig_combine IG1 IG2"
    using assms ig_combine_mapping_correct
    by blast
next
  fix Imod3
  have "TG (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine Imod1 Imod2)) = tg_combine (TG (f1 (imod_combine Imod1 Imod2))) (TG (f2 (imod_combine Imod1 Imod2)))"
    unfolding ig_combine_mapping_def
    by simp
  then have "TG (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine Imod1 Imod2)) = tg_combine (TG (f1 Imod1)) (TG (f2 Imod2))"
    using ig_combine_mapping_function.func_tg imod_combine_commute mapping_imod1 mapping_imod2
    by metis
  then have "TG (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine Imod1 Imod2)) = tg_combine (TG (f1 (imod_combine Imod1 (imod_combine Imod2 Imod3)))) (TG (f2 (imod_combine Imod2 (imod_combine Imod1 Imod3))))"
    using ig_combine_mapping_function.func_tg mapping_imod1 mapping_imod2
    by metis
  then have "TG (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine Imod1 Imod2)) = tg_combine (TG (f1 (imod_combine Imod1 (imod_combine Imod2 Imod3)))) (TG (f2 (imod_combine Imod1 (imod_combine Imod2 Imod3))))"
    using imod_combine_assoc imod_combine_commute
    by metis
  then show "TG (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine Imod1 Imod2)) = TG (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine (imod_combine Imod1 Imod2) Imod3))"
    unfolding ig_combine_mapping_def
    by (simp add: imod_combine_assoc)
next
  fix Imod3
  have "{i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} \<union> {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} \<subseteq>
    {i \<in> Id (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG1} \<union> {i \<in> Id (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG2}"
  proof
    fix x
    assume "x \<in> {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} \<union> {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2}"
    then show "x \<in> {i \<in> Id (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG1} \<union> {i \<in> Id (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG2}"
    proof (elim UnE)
      assume "x \<in> {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1}"
      then have "x \<in> Id IG1"
        by simp
      then have "x \<in> {i \<in> Id (f1 (imod_combine Imod1 (imod_combine Imod2 Imod3))). i \<in> Id IG1}"
        using ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_ids mapping_imod1
        by blast
      then have "x \<in> {i \<in> Id (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG1}"
        by (simp add: imod_combine_assoc)
      then show ?thesis
        by simp
    next
      assume "x \<in> {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2}"
      then have "x \<in> Id IG2"
        by simp
      then have "x \<in> {i \<in> Id (f2 (imod_combine Imod2 (imod_combine Imod1 Imod3))). i \<in> Id IG2}"
        using ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_ids mapping_imod2
        by blast
      then have "x \<in> {i \<in> Id (f2 (imod_combine (imod_combine Imod2 Imod1) Imod3)). i \<in> Id IG2}"
        by (simp add: imod_combine_assoc)
      then have "x \<in> {i \<in> Id (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG2}"
        by (simp add: imod_combine_commute)
      then show ?thesis
        by simp
    qed
  qed
  then show "Id (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine Imod1 Imod2)) \<subseteq> Id (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine (imod_combine Imod1 Imod2) Imod3))"
    unfolding ig_combine_mapping_def
    by simp
next
  fix Imod3
  have "{n \<in> N (f1 (imod_combine Imod1 Imod2)). n \<in> N IG1} \<union> {n \<in> N (f2 (imod_combine Imod1 Imod2)). n \<in> N IG2} \<subseteq>
    {n \<in> N (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). n \<in> N IG1} \<union> {n \<in> N (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). n \<in> N IG2}"
  proof
    fix x
    assume "x \<in> {n \<in> N (f1 (imod_combine Imod1 Imod2)). n \<in> N IG1} \<union> {n \<in> N (f2 (imod_combine Imod1 Imod2)). n \<in> N IG2}"
    then show "x \<in> {n \<in> N (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). n \<in> N IG1} \<union> {n \<in> N (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). n \<in> N IG2}"
    proof (elim UnE)
      assume "x \<in> {n \<in> N (f1 (imod_combine Imod1 Imod2)). n \<in> N IG1}"
      then have "x \<in> N IG1"
        by simp
      then have "x \<in> {n \<in> N (f1 (imod_combine Imod1 (imod_combine Imod2 Imod3))). n \<in> N IG1}"
        using ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_nodes mapping_imod1
        by blast
      then have "x \<in> {n \<in> N (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). n \<in> N IG1}"
        by (simp add: imod_combine_assoc)
      then show ?thesis
        by simp
    next
      assume "x \<in> {n \<in> N (f2 (imod_combine Imod1 Imod2)). n \<in> N IG2}"
      then have "x \<in> N IG2"
        by simp
      then have "x \<in> {n \<in> N (f2 (imod_combine Imod2 (imod_combine Imod1 Imod3))). n \<in> N IG2}"
        using ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_nodes mapping_imod2
        by blast
      then have "x \<in> {n \<in> N (f2 (imod_combine (imod_combine Imod2 Imod1) Imod3)). n \<in> N IG2}"
        by (simp add: imod_combine_assoc)
      then have "x \<in> {n \<in> N (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). n \<in> N IG2}"
        by (simp add: imod_combine_commute)
      then show ?thesis
        by simp
    qed
  qed
  then show "N (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine Imod1 Imod2)) \<subseteq> N (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine (imod_combine Imod1 Imod2) Imod3))"
    unfolding ig_combine_mapping_def
    by simp
next
  fix Imod3
  have "{e \<in> E (f1 (imod_combine Imod1 Imod2)). e \<in> E IG1} \<union> {e \<in> E (f2 (imod_combine Imod1 Imod2)). e \<in> E IG2} \<subseteq>
    {e \<in> E (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). e \<in> E IG1} \<union> {e \<in> E (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). e \<in> E IG2}"
  proof
    fix x
    assume "x \<in> {e \<in> E (f1 (imod_combine Imod1 Imod2)). e \<in> E IG1} \<union> {e \<in> E (f2 (imod_combine Imod1 Imod2)). e \<in> E IG2}"
    then show "x \<in> {e \<in> E (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). e \<in> E IG1} \<union> {e \<in> E (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). e \<in> E IG2}"
    proof (elim UnE)
      assume "x \<in> {e \<in> E (f1 (imod_combine Imod1 Imod2)). e \<in> E IG1}"
      then have "x \<in> E IG1"
        by simp
      then have "x \<in> {e \<in> E (f1 (imod_combine Imod1 (imod_combine Imod2 Imod3))). e \<in> E IG1}"
        using ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_edges mapping_imod1
        by blast
      then have "x \<in> {e \<in> E (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). e \<in> E IG1}"
        by (simp add: imod_combine_assoc)
      then show ?thesis
        by simp
    next
      assume "x \<in> {e \<in> E (f2 (imod_combine Imod1 Imod2)). e \<in> E IG2}"
      then have "x \<in> E IG2"
        by simp
      then have "x \<in> {e \<in> E (f2 (imod_combine Imod2 (imod_combine Imod1 Imod3))). e \<in> E IG2}"
        using ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_edges mapping_imod2
        by blast
      then have "x \<in> {e \<in> E (f2 (imod_combine (imod_combine Imod2 Imod1) Imod3)). e \<in> E IG2}"
        by (simp add: imod_combine_assoc)
      then have "x \<in> {e \<in> E (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). e \<in> E IG2}"
        by (simp add: imod_combine_commute)
      then show ?thesis
        by simp
    qed
  qed
  then show "E (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine Imod1 Imod2)) \<subseteq> E (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine (imod_combine Imod1 Imod2) Imod3))"
    unfolding ig_combine_mapping_def
    by simp
next
  fix Imod3 i
  have f1_id_altdef: "{i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} = {i \<in> Id (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG1}"
  proof
    show "{i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} \<subseteq> {i \<in> Id (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG1}"
    proof
      fix y
      assume "y \<in> {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1}"
      then have "y \<in> Id IG1"
        by blast
      then have "y \<in> {i \<in> Id (f1 (imod_combine Imod1 (imod_combine Imod2 Imod3))). i \<in> Id IG1}"
        using mapping_imod1 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_ids
        by blast
      then show "y \<in> {i \<in> Id (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG1}"
        by (simp add: imod_combine_assoc)
    qed
  next
    show "{i \<in> Id (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG1} \<subseteq> {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1}"
    proof
      fix y
      assume "y \<in> {i \<in> Id (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG1}"
      then have "y \<in> Id IG1"
        by blast
      then show "y \<in> {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1}"
        using mapping_imod1 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_ids
        by blast
    qed
  qed
  have f1_ident_altdef: "\<And>y. y \<in> Id IG1 \<Longrightarrow> ident (f1 (imod_combine Imod1 Imod2)) y = ident (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)) y"
  proof-
    fix y
    assume "y \<in> Id IG1"
    then have ident_imod1_imod12: "ident (f1 Imod1) y = ident (f1 (imod_combine Imod1 Imod2)) y"
      using mapping_imod1 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.func_ident
      by metis
    assume "y \<in> Id IG1"
    then have ident_imod1_imod123: "ident (f1 Imod1) y = ident (f1 (imod_combine Imod1 (imod_combine Imod2 Imod3))) y"
      using mapping_imod1 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.func_ident
      by metis
    show "ident (f1 (imod_combine Imod1 Imod2)) y = ident (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)) y"
      using ident_imod1_imod12 ident_imod1_imod123
      by (simp add: imod_combine_assoc)
  qed
  have f2_id_altdef: "{i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} = {i \<in> Id (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG2}"
  proof
    show "{i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} \<subseteq> {i \<in> Id (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG2}"
    proof
      fix y
      assume "y \<in> {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2}"
      then have "y \<in> Id IG2"
        by blast
      then have "y \<in> {i \<in> Id (f2 (imod_combine Imod2 (imod_combine Imod1 Imod3))). i \<in> Id IG2}"
        using mapping_imod2 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_ids
        by blast
      then have "y \<in> {i \<in> Id (f2 (imod_combine (imod_combine Imod2 Imod1) Imod3)). i \<in> Id IG2}"
        by (simp add: imod_combine_assoc)
      then show "y \<in> {i \<in> Id (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG2}"
        by (simp add: imod_combine_commute)
    qed
  next
    show "{i \<in> Id (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG2} \<subseteq> {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2}"
    proof
      fix y
      assume "y \<in> {i \<in> Id (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG2}"
      then have "y \<in> Id IG2"
        by blast
      then have "y \<in> {i \<in> Id (f2 (imod_combine Imod2 Imod1)). i \<in> Id IG2}"
        using mapping_imod2 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.subset_ids
        by blast
      then show "y \<in> {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2}"
        by (simp add: imod_combine_commute)
    qed
  qed
  have f2_ident_altdef: "\<And>y. y \<in> Id IG2 \<Longrightarrow> ident (f2 (imod_combine Imod1 Imod2)) y = ident (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)) y"
  proof-
    fix y
    assume "y \<in> Id IG2"
    then have "ident (f2 Imod2) y = ident (f2 (imod_combine Imod2 Imod1)) y"
      using mapping_imod2 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.func_ident
      by metis
    then have ident_imod1_imod12: "ident (f2 Imod2) y = ident (f2 (imod_combine Imod1 Imod2)) y"
      by (simp add: imod_combine_commute)
    assume "y \<in> Id IG2"
    then have "ident (f2 Imod2) y = ident (f2 (imod_combine Imod2 (imod_combine Imod1 Imod3))) y"
      using mapping_imod2 ig_combine_mapping_function.mapping_correct ig_combine_mapping_function.func_ident
      by metis
    then have ident_imod1_imod123: "ident (f2 Imod2) y = ident (f2 (imod_combine (imod_combine Imod2 Imod1) Imod3)) y"
      by (simp add: imod_combine_assoc)
    show "ident (f2 (imod_combine Imod1 Imod2)) y = ident (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)) y"
      using ident_imod1_imod12 ident_imod1_imod123
      by (simp add: imod_combine_commute)
  qed
  assume "i \<in> Id (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine Imod1 Imod2))"
  then have "i \<in> {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} \<union> {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2}"
    unfolding ig_combine_mapping_def
    by simp
  then have "i \<in> Id IG1 \<union> Id IG2"
    by blast
  then have "i \<in> Id IG1 \<inter> Id IG2 \<or> i \<in> Id IG1 - Id IG2 \<or> i \<in> Id IG2 - Id IG1"
    by blast
  then have "ig_combine_ident {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} (ident (f1 (imod_combine Imod1 Imod2))) {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} (ident (f2 (imod_combine Imod1 Imod2))) i = 
    ig_combine_ident {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} (ident (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3))) {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} (ident (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3))) i"
    unfolding ig_combine_ident_def
    using f1_ident_altdef f2_ident_altdef
    by fastforce
  then have "ig_combine_ident {i \<in> Id (f1 (imod_combine Imod1 Imod2)). i \<in> Id IG1} (ident (f1 (imod_combine Imod1 Imod2))) {i \<in> Id (f2 (imod_combine Imod1 Imod2)). i \<in> Id IG2} (ident (f2 (imod_combine Imod1 Imod2))) i = 
    ig_combine_ident {i \<in> Id (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG1} (ident (f1 (imod_combine (imod_combine Imod1 Imod2) Imod3))) {i \<in> Id (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3)). i \<in> Id IG2} (ident (f2 (imod_combine (imod_combine Imod1 Imod2) Imod3))) i"
    by (simp add: f1_id_altdef f2_id_altdef)
  then show "ident (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine Imod1 Imod2)) i = ident (ig_combine_mapping f1 IG1 f2 IG2 (imod_combine (imod_combine Imod1 Imod2) Imod3)) i"
    unfolding ig_combine_mapping_def
    by simp
qed

definition ig_empty_mapping :: "('o, 't) instance_model \<Rightarrow> ('nt, 'lt, 'id) instance_graph" where
  "ig_empty_mapping Imod \<equiv> ig_empty"

lemma ig_empty_mapping_function[simp]: "ig_combine_mapping_function ig_empty_mapping imod_empty ig_empty"
  unfolding ig_empty_mapping_def ig_empty_def imod_empty_def
  by (intro ig_combine_mapping_function.intro) (simp_all)



section "Merging mapping functions from instance graphs to instance models"

locale imod_combine_mapping_function =
  fixes f :: "('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model"
  fixes IG :: "('nt, 'lt, 'id) instance_graph"
  fixes Imod :: "('o, 't) instance_model"
  assumes mapping_correct: "f IG = Imod"
  assumes func_tm: "\<And>IGX. Tm (f IG) = Tm (f (ig_combine IG IGX))"
  assumes subset_object: "\<And>IGX. Object (f IG) \<subseteq> Object (f (ig_combine IG IGX))"
  assumes func_object_class: "\<And>IGX ob. ob \<in> Object (f IG) \<Longrightarrow> ObjectClass (f IG) ob = ObjectClass (f (ig_combine IG IGX)) ob"
  assumes func_object_id: "\<And>IGX ob. ob \<in> Object (f IG) \<Longrightarrow> ObjectId (f IG) ob = ObjectId (f (ig_combine IG IGX)) ob"
  assumes func_field_value: "\<And>IGX ob fd. ob \<in> Object (f IG) \<Longrightarrow> fd \<in> Field (Tm (f IG)) \<Longrightarrow> FieldValue (f IG) (ob, fd) = FieldValue (f (ig_combine IG IGX)) (ob, fd)"
  assumes func_default_value: "\<And>IGX c. c \<in> Constant (Tm (f IG)) \<Longrightarrow> DefaultValue (f IG) c = DefaultValue (f (ig_combine IG IGX)) c"

definition imod_combine_object_class_mapping :: "(('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> (('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('nt, 'lt, 'id) instance_graph \<Rightarrow> 'o \<Rightarrow> 't Id" where
  "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 IG ob \<equiv>
    if ob \<in> {ob \<in> Object (f1 IG). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 IG). ob \<in> Object Imod2} \<and> ObjectClass (f1 IG) ob = ObjectClass (f2 IG) ob then
      ObjectClass (f1 IG) ob
    else if ob \<in> {ob \<in> Object (f1 IG). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 IG). ob \<in> Object Imod2} then
      undefined
    else if ob \<in> {ob \<in> Object (f1 IG). ob \<in> Object Imod1} then
      ObjectClass (f1 IG) ob
    else if ob \<in> {ob \<in> Object (f2 IG). ob \<in> Object Imod2} then
      ObjectClass (f2 IG) ob
    else
      undefined"

definition imod_combine_object_id_mapping :: "(('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> (('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('nt, 'lt, 'id) instance_graph \<Rightarrow> 'o \<Rightarrow> 't" where
  "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 IG ob \<equiv>
    if ob \<in> {ob \<in> Object (f1 IG). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 IG). ob \<in> Object Imod2} \<and> ObjectId (f1 IG) ob = ObjectId (f2 IG) ob then
      ObjectId (f1 IG) ob
    else if ob \<in> {ob \<in> Object (f1 IG). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 IG). ob \<in> Object Imod2} then
      undefined
    else if ob \<in> {ob \<in> Object (f1 IG). ob \<in> Object Imod1} then
      ObjectId (f1 IG) ob
    else if ob \<in> {ob \<in> Object (f2 IG). ob \<in> Object Imod2} then
      ObjectId (f2 IG) ob
    else
      undefined"

definition imod_combine_field_value_mapping :: "(('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> (('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o \<times> ('t Id \<times> 't)) \<Rightarrow> ('o, 't) ValueDef" where
  "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 IG f \<equiv>
    if fst f \<in> {ob \<in> Object (f1 IG). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 IG). ob \<in> Object Imod2} \<and> snd f \<in> {f \<in> Field (Tm (f1 IG)). f \<in> Field (Tm Imod1)} \<inter> {f \<in> Field (Tm (f2 IG)). f \<in> Field (Tm Imod2)} then
      if FieldValue (f1 IG) f = FieldValue (f2 IG) f then
        FieldValue (f1 IG) f
      else if FieldValue (f1 IG) f = unspecified then
        FieldValue (f2 IG) f
      else if FieldValue (f2 IG) f = unspecified then
        FieldValue (f1 IG) f
      else
        ValueDef.invalid
    else if fst f \<in> {ob \<in> Object (f1 IG). ob \<in> Object Imod1} \<and> snd f \<in> {f \<in> Field (Tm (f1 IG)). f \<in> Field (Tm Imod1)} then
      FieldValue (f1 IG) f
    else if fst f \<in> {ob \<in> Object (f2 IG). ob \<in> Object Imod2} \<and> snd f \<in> {f \<in> Field (Tm (f2 IG)). f \<in> Field (Tm Imod2)} then
      FieldValue (f2 IG) f
    else if fst f \<in> {ob \<in> Object (f1 IG). ob \<in> Object Imod1} \<union> {ob \<in> Object (f2 IG). ob \<in> Object Imod2} \<and> snd f \<in> {f \<in> Field (Tm (f1 IG)). f \<in> Field (Tm Imod1)} \<union> {f \<in> Field (Tm (f2 IG)). f \<in> Field (Tm Imod2)} then
      unspecified
    else
      undefined"

definition imod_combine_default_value_mapping :: "(('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> (('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('nt, 'lt, 'id) instance_graph \<Rightarrow> 't Id \<Rightarrow> ('o, 't) ValueDef" where
  "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 IG c \<equiv>
    if c \<in> {c \<in> Constant (Tm (f1 IG)). c \<in> Constant (Tm Imod1)} \<inter> {c \<in> Constant (Tm (f2 IG)). c \<in> Constant (Tm Imod2)} \<and> DefaultValue (f1 IG) c = DefaultValue (f2 IG) c then
      DefaultValue (f1 IG) c
    else if c \<in> {c \<in> Constant (Tm (f1 IG)). c \<in> Constant (Tm Imod1)} \<inter> {c \<in> Constant (Tm (f2 IG)). c \<in> Constant (Tm Imod2)} \<and> DefaultValue (f1 IG) c \<noteq> DefaultValue (f2 IG) c then
      ValueDef.invalid
    else if c \<in> {c \<in> Constant (Tm (f1 IG)). c \<in> Constant (Tm Imod1)} \<and> c \<notin> {c \<in> Constant (Tm (f2 IG)). c \<in> Constant (Tm Imod2)} then
      DefaultValue (f1 IG) c
    else if c \<in> {c \<in> Constant (Tm (f2 IG)). c \<in> Constant (Tm Imod2)} \<and> c \<notin> {c \<in> Constant (Tm (f1 IG)). c \<in> Constant (Tm Imod1)} then
      DefaultValue (f2 IG) c
    else
      undefined"

definition imod_combine_mapping :: "(('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> (('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model) \<Rightarrow> ('o, 't) instance_model \<Rightarrow> ('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "imod_combine_mapping f1 Imod1 f2 Imod2 IG \<equiv> \<lparr>
    Tm = tmod_combine (Tm (f1 IG)) (Tm (f2 IG)),
    Object = {ob \<in> Object (f1 IG). ob \<in> Object Imod1} \<union> {ob \<in> Object (f2 IG). ob \<in> Object Imod2},
    ObjectClass = imod_combine_object_class_mapping f1 Imod1 f2 Imod2 IG,
    ObjectId = imod_combine_object_id_mapping f1 Imod1 f2 Imod2 IG,
    FieldValue = imod_combine_field_value_mapping f1 Imod1 f2 Imod2 IG,
    DefaultValue = imod_combine_default_value_mapping f1 Imod1 f2 Imod2 IG
  \<rparr>"

lemma imod_combine_mapping_correct:
  assumes mapping_ig1: "imod_combine_mapping_function f1 IG1 Imod1"
  assumes mapping_ig2: "imod_combine_mapping_function f2 IG2 Imod2"
  shows "imod_combine_mapping (f1) Imod1 (f2) Imod2 (ig_combine IG1 IG2) = imod_combine Imod1 Imod2"
  unfolding imod_combine_mapping_def imod_combine_def
proof
  have object_imod1: "{ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} = Object Imod1"
  proof
    show "{ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<subseteq> Object Imod1"
      by blast
  next
    show "Object Imod1 \<subseteq> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
      using mapping_ig1 imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object
      by blast
  qed
  have object_imod2: "{ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} = Object Imod2"
  proof
    show "{ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<subseteq> Object Imod2"
      by blast
  next
    have "Object Imod2 \<subseteq> {ob \<in> Object (f2 (ig_combine IG2 IG1)). ob \<in> Object Imod2}"
      using mapping_ig2 imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object
      by blast
    then show "Object Imod2 \<subseteq> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
      by simp
  qed
  have tmod1_def: "Tm (f1 IG1) = Tm (f1 (ig_combine IG1 IG2))"
    using mapping_ig1 imod_combine_mapping_function.func_tm
    by blast
  have tmod2_def: "Tm (f2 IG2) = Tm (f2 (ig_combine IG1 IG2))"
    using mapping_ig2 imod_combine_mapping_function.func_tm ig_combine_commute
    by metis
  show "tmod_combine (Tm (f1 (ig_combine IG1 IG2))) (Tm (f2 (ig_combine IG1 IG2))) = tmod_combine (Tm Imod1) (Tm Imod2) \<and>
    {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<union> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} = Object Imod1 \<union> Object Imod2 \<and>
    imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) = imod_combine_object_class Imod1 Imod2 \<and>
    imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) = imod_combine_object_id Imod1 Imod2 \<and> 
    imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) = imod_combine_field_value Imod1 Imod2 \<and> 
    imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) = imod_combine_default_value Imod1 Imod2 \<and> 
    () = ()"
  proof (intro conjI)
    show "tmod_combine (Tm (f1 (ig_combine IG1 IG2))) (Tm (f2 (ig_combine IG1 IG2))) = tmod_combine (Tm Imod1) (Tm Imod2)"
      using imod_combine_mapping_function.mapping_correct mapping_ig1 mapping_ig2 tmod1_def tmod2_def
      by metis
  next
    show "{ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<union> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} = Object Imod1 \<union> Object Imod2"
      by (simp add: object_imod1 object_imod2)
  next
    show "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) = imod_combine_object_class Imod1 Imod2"
    proof
      fix ob
      have ob_imod1_cases: "ob \<in> Object Imod1 \<or> ob \<notin> Object Imod1"
        by simp
      have ob_imod2_cases: "ob \<in> Object Imod2 \<or> ob \<notin> Object Imod2"
        by simp
      show "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = imod_combine_object_class Imod1 Imod2 ob"
        using ob_imod1_cases ob_imod2_cases
      proof (elim disjE)
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        show ?thesis
        proof (induct "ObjectClass Imod1 ob = ObjectClass Imod2 ob")
          case True
          then have "ObjectClass (f1 (ig_combine IG1 IG2)) ob = ObjectClass (f2 (ig_combine IG1 IG2)) ob"
            using ig_combine_commute imod_combine_mapping_function.func_object_class imod_combine_mapping_function.mapping_correct mapping_ig1 mapping_ig2 ob_in_imod1 ob_in_imod2
            by metis
          then have "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectClass (f1 (ig_combine IG1 IG2)) ob"
            unfolding imod_combine_object_class_mapping_def
            by (simp add: ob_in_imod1 object_imod1)
          then have mapping_def: "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectClass Imod1 ob"
            using imod_combine_mapping_function.func_object_class imod_combine_mapping_function.mapping_correct mapping_ig1 ob_in_imod1
            by metis
          have "imod_combine_object_class Imod1 Imod2 ob = ObjectClass Imod1 ob"
            unfolding imod_combine_object_class_def
            using True.hyps ob_in_imod1
            by simp
          then show ?case
            by (simp add: mapping_def)
        next
          case False
          then have "ObjectClass (f1 (ig_combine IG1 IG2)) ob \<noteq> ObjectClass (f2 (ig_combine IG1 IG2)) ob"
            using ig_combine_commute imod_combine_mapping_function.func_object_class imod_combine_mapping_function.mapping_correct mapping_ig1 mapping_ig2 ob_in_imod1 ob_in_imod2
            by metis
          then have mapping_def: "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = undefined"
            unfolding imod_combine_object_class_mapping_def
            by (simp add: ob_in_imod1 ob_in_imod2 object_imod1 object_imod2)
          have "imod_combine_object_class Imod1 Imod2 ob = undefined"
            unfolding imod_combine_object_class_def
            using False.hyps ob_in_imod1 ob_in_imod2
            by simp
          then show ?case
            by (simp add: mapping_def)
        qed
      next
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        have "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectClass (f1 (ig_combine IG1 IG2)) ob"
          unfolding imod_combine_object_class_mapping_def
          by (simp add: ob_in_imod1 ob_not_in_imod2 object_imod1)
        then have mapping_def: "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectClass Imod1 ob"
          using imod_combine_mapping_function.func_object_class imod_combine_mapping_function.mapping_correct mapping_ig1 ob_in_imod1
          by metis
        have "imod_combine_object_class Imod1 Imod2 ob = ObjectClass Imod1 ob"
          unfolding imod_combine_object_class_def
          by (simp add: ob_in_imod1 ob_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        have "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectClass (f2 (ig_combine IG1 IG2)) ob"
          unfolding imod_combine_object_class_mapping_def
          by (simp add: ob_in_imod2 ob_not_in_imod1 object_imod2)
        then have mapping_def: "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectClass Imod2 ob"
          using imod_combine_mapping_function.func_object_class imod_combine_mapping_function.mapping_correct mapping_ig2 ob_in_imod2
          by fastforce
        have "imod_combine_object_class Imod1 Imod2 ob = ObjectClass Imod2 ob"
          unfolding imod_combine_object_class_def
          by (simp add: ob_in_imod2 ob_not_in_imod1)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        have mapping_def: "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = undefined"
          unfolding imod_combine_object_class_mapping_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        have "imod_combine_object_class Imod1 Imod2 ob = undefined"
          unfolding imod_combine_object_class_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      qed
    qed
  next
    show "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) = imod_combine_object_id Imod1 Imod2"
    proof
      fix ob
      have ob_imod1_cases: "ob \<in> Object Imod1 \<or> ob \<notin> Object Imod1"
        by simp
      have ob_imod2_cases: "ob \<in> Object Imod2 \<or> ob \<notin> Object Imod2"
        by simp
      show "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = imod_combine_object_id Imod1 Imod2 ob"
        using ob_imod1_cases ob_imod2_cases
      proof (elim disjE)
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        show ?thesis
        proof (induct "ObjectId Imod1 ob = ObjectId Imod2 ob")
          case True
          then have "ObjectId (f1 (ig_combine IG1 IG2)) ob = ObjectId (f2 (ig_combine IG1 IG2)) ob"
            using ig_combine_commute imod_combine_mapping_function.func_object_id imod_combine_mapping_function.mapping_correct mapping_ig1 mapping_ig2 ob_in_imod1 ob_in_imod2
            by metis
          then have "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectId (f1 (ig_combine IG1 IG2)) ob"
            unfolding imod_combine_object_id_mapping_def
            by (simp add: ob_in_imod1 object_imod1)
          then have mapping_def: "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectId Imod1 ob"
            using imod_combine_mapping_function.func_object_id imod_combine_mapping_function.mapping_correct mapping_ig1 ob_in_imod1
            by metis
          have "imod_combine_object_id Imod1 Imod2 ob = ObjectId Imod1 ob"
            unfolding imod_combine_object_id_def
            using True.hyps ob_in_imod1
            by simp
          then show ?case
            by (simp add: mapping_def)
        next
          case False
          then have "ObjectId (f1 (ig_combine IG1 IG2)) ob \<noteq> ObjectId (f2 (ig_combine IG1 IG2)) ob"
            using ig_combine_commute imod_combine_mapping_function.func_object_id imod_combine_mapping_function.mapping_correct mapping_ig1 mapping_ig2 ob_in_imod1 ob_in_imod2
            by metis
          then have mapping_def: "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = undefined"
            unfolding imod_combine_object_id_mapping_def
            by (simp add: ob_in_imod1 ob_in_imod2 object_imod1 object_imod2)
          have "imod_combine_object_id Imod1 Imod2 ob = undefined"
            unfolding imod_combine_object_id_def
            using False.hyps ob_in_imod1 ob_in_imod2
            by simp
          then show ?case
            by (simp add: mapping_def)
        qed
      next
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        have "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectId (f1 (ig_combine IG1 IG2)) ob"
          unfolding imod_combine_object_id_mapping_def
          by (simp add: ob_in_imod1 ob_not_in_imod2 object_imod1)
        then have mapping_def: "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectId Imod1 ob"
          using imod_combine_mapping_function.func_object_id imod_combine_mapping_function.mapping_correct mapping_ig1 ob_in_imod1
          by metis
        have "imod_combine_object_id Imod1 Imod2 ob = ObjectId Imod1 ob"
          unfolding imod_combine_object_id_def
          by (simp add: ob_in_imod1 ob_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        have "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectId (f2 (ig_combine IG1 IG2)) ob"
          unfolding imod_combine_object_id_mapping_def
          by (simp add: ob_in_imod2 ob_not_in_imod1 object_imod2)
        then have mapping_def: "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectId Imod2 ob"
          using imod_combine_mapping_function.func_object_id imod_combine_mapping_function.mapping_correct mapping_ig2 ob_in_imod2
          by fastforce
        have "imod_combine_object_id Imod1 Imod2 ob = ObjectId Imod2 ob"
          unfolding imod_combine_object_id_def
          by (simp add: ob_in_imod2 ob_not_in_imod1)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        have mapping_def: "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = undefined"
          unfolding imod_combine_object_id_mapping_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        have "imod_combine_object_id Imod1 Imod2 ob = undefined"
          unfolding imod_combine_object_id_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      qed
    qed
  next
    have field_tmod1: "{f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} = Field (Tm Imod1)"
    proof
      show "{f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} \<subseteq> Field (Tm Imod1)"
        by blast
    next
      have "Field (Tm Imod1) \<subseteq> {f \<in> Field (Tm (f1 IG1)). f \<in> Field (Tm Imod1)}"
        using mapping_ig1 imod_combine_mapping_function.mapping_correct
        by blast
      then show "Field (Tm Imod1) \<subseteq> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)}"
        using tmod1_def
        by simp
    qed
    have field_tmod2: "{f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)} = Field (Tm Imod2)"
    proof
      show "{f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)} \<subseteq> Field (Tm Imod2)"
        by blast
    next
      have "Field (Tm Imod2) \<subseteq> {f \<in> Field (Tm (f2 IG2)). f \<in> Field (Tm Imod2)}"
        using mapping_ig2 imod_combine_mapping_function.mapping_correct
        by blast
      then show "Field (Tm Imod2) \<subseteq> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
        using tmod2_def
        by simp
    qed
    have "\<And>ob f. imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = imod_combine_field_value Imod1 Imod2 (ob, f)"
    proof-
      fix ob f
      have ob_imod1_cases: "ob \<in> Object Imod1 \<or> ob \<notin> Object Imod1"
        by simp
      have ob_imod2_cases: "ob \<in> Object Imod2 \<or> ob \<notin> Object Imod2"
        by simp
      have f_imod1_cases: "f \<in> Field (Tm Imod1) \<or> f \<notin> Field (Tm Imod1)"
        by simp
      have f_imod2_cases: "f \<in> Field (Tm Imod2) \<or> f \<notin> Field (Tm Imod2)"
        by simp
      show "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = imod_combine_field_value Imod1 Imod2 (ob, f)"
        using ob_imod1_cases ob_imod2_cases f_imod1_cases f_imod2_cases
      proof (elim disjE)
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        assume f_in_imod1: "f \<in> Field (Tm Imod1)"
        assume f_in_imod2: "f \<in> Field (Tm Imod2)"
        show ?thesis
        proof (induct "FieldValue Imod1 (ob, f) = FieldValue Imod2 (ob, f)")
          case True
          then have "FieldValue (f1 (ig_combine IG1 IG2)) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
            using f_in_imod1 f_in_imod2 ig_combine_commute imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig1 mapping_ig2 ob_in_imod1 ob_in_imod2
            by metis
          then have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
            unfolding imod_combine_field_value_mapping_def
            by (simp add: f_in_imod1 field_tmod1 ob_in_imod1 object_imod1)
          then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue Imod1 (ob, f)"
            using f_in_imod1 imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig1 ob_in_imod1
            by metis
          have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
            unfolding imod_combine_field_value_def
            using True.hyps f_in_imod1 ob_in_imod1
            by simp
          then show ?case
            by (simp add: mapping_def)
        next
          case False
          then show ?case
          proof (induct "FieldValue Imod1 (ob, f) = unspecified")
            case True
            then have "FieldValue (f1 (ig_combine IG1 IG2)) (ob, f) = unspecified"
              using f_in_imod1 imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig1 ob_in_imod1
              by metis
            then have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
              unfolding imod_combine_field_value_mapping_def
              by (simp add: f_in_imod2 field_tmod2 ob_in_imod2 object_imod2)
            then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue Imod2 (ob, f)"
              using f_in_imod2 ig_combine_commute imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig2 ob_in_imod2
              by metis
            have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
              unfolding imod_combine_field_value_def
              using True.hyps f_in_imod2 ob_in_imod2
              by simp
            then show ?case
              by (simp add: mapping_def)
          next
            case False
            then show ?case
            proof (induct "FieldValue Imod2 (ob, f) = unspecified")
              case True
              then have "FieldValue (f2 (ig_combine IG1 IG2)) (ob, f) = unspecified"
                using f_in_imod2 ig_combine_commute imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig2 ob_in_imod2
                by metis
              then have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
                unfolding imod_combine_field_value_mapping_def
                by (simp add: f_in_imod1 field_tmod1 ob_in_imod1 object_imod1)
              then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue Imod1 (ob, f)"
                using f_in_imod1 imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig1 ob_in_imod1
                by metis
              have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
                unfolding imod_combine_field_value_def
                using True.hyps f_in_imod1 ob_in_imod1
                by simp
              then show ?case
                by (simp add: mapping_def)
            next
              case False
              then have values_neq: "FieldValue (f1 (ig_combine IG1 IG2)) (ob, f) \<noteq> FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
                using f_in_imod1 f_in_imod2 ig_combine_commute imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig1 mapping_ig2 ob_in_imod1 ob_in_imod2
                by metis
              have value_f1: "FieldValue (f1 (ig_combine IG1 IG2)) (ob, f) \<noteq> unspecified"
                using False.prems f_in_imod1 imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig1 ob_in_imod1
                by metis
              have value_f2: "FieldValue (f2 (ig_combine IG1 IG2)) (ob, f) \<noteq> unspecified"
                using False.hyps f_in_imod2 ig_combine_commute imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig2 ob_in_imod2
                by metis
              have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = ValueDef.invalid"
                unfolding imod_combine_field_value_mapping_def
                by (simp add: f_in_imod1 f_in_imod2 field_tmod1 field_tmod2 ob_in_imod1 ob_in_imod2 object_imod1 object_imod2 value_f1 value_f2 values_neq)
              have "imod_combine_field_value Imod1 Imod2 (ob, f) = ValueDef.invalid"
                unfolding imod_combine_field_value_def
                using False.hyps False.prems f_in_imod1 f_in_imod2 ob_in_imod1 ob_in_imod2
                by simp
              then show ?case
                by (simp add: mapping_def)
            qed
          qed
        qed
      next
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        assume f_in_imod1: "f \<in> Field (Tm Imod1)"
        assume f_not_in_imod2: "f \<notin> Field (Tm Imod2)"
        have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: f_in_imod1 f_not_in_imod2 field_tmod1 ob_in_imod1 object_imod1)
        then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue Imod1 (ob, f)"
          using f_in_imod1 imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig1 ob_in_imod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_in_imod1 f_not_in_imod2 ob_in_imod1)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        assume f_not_in_imod1: "f \<notin> Field (Tm Imod1)"
        assume f_in_imod2: "f \<in> Field (Tm Imod2)"
        have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: f_in_imod2 f_not_in_imod1 field_tmod2 ob_in_imod2 object_imod2)
        then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue Imod2 (ob, f)"
          using f_in_imod2 ig_combine_commute imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig2 ob_in_imod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_in_imod2 f_not_in_imod1 ob_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        assume f_not_in_imod1: "f \<notin> Field (Tm Imod1)"
        assume f_not_in_imod2: "f \<notin> Field (Tm Imod2)"
        have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = undefined"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: f_not_in_imod1 f_not_in_imod2)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: f_not_in_imod1 f_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        assume f_in_imod1: "f \<in> Field (Tm Imod1)"
        assume f_in_imod2: "f \<in> Field (Tm Imod2)"
        have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: f_in_imod1 field_tmod1 ob_in_imod1 ob_not_in_imod2 object_imod1)
        then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue Imod1 (ob, f)"
          using f_in_imod1 imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig1 ob_in_imod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_in_imod1 ob_in_imod1 ob_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        assume f_in_imod1: "f \<in> Field (Tm Imod1)"
        assume f_not_in_imod2: "f \<notin> Field (Tm Imod2)"
        have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: f_in_imod1 field_tmod1 ob_in_imod1 ob_not_in_imod2 object_imod1)
        then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue Imod1 (ob, f)"
          using f_in_imod1 imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig1 ob_in_imod1
          by metis
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod1 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_in_imod1 ob_in_imod1 ob_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        assume f_not_in_imod1: "f \<notin> Field (Tm Imod1)"
        assume f_in_imod2: "f \<in> Field (Tm Imod2)"
        have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = unspecified"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: f_in_imod2 f_not_in_imod1 field_tmod2 ob_in_imod1 ob_not_in_imod2 object_imod1)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_in_imod2 f_not_in_imod1 ob_in_imod1 ob_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_in_imod1: "ob \<in> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        assume f_not_in_imod1: "f \<notin> Field (Tm Imod1)"
        assume f_not_in_imod2: "f \<notin> Field (Tm Imod2)"
        have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = undefined"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: f_not_in_imod1 f_not_in_imod2)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: f_not_in_imod1 f_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        assume f_in_imod1: "f \<in> Field (Tm Imod1)"
        assume f_in_imod2: "f \<in> Field (Tm Imod2)"
        have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: f_in_imod2 field_tmod2 ob_in_imod2 ob_not_in_imod1 object_imod2)
        then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue Imod2 (ob, f)"
          using f_in_imod2 ig_combine_commute imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig2 ob_in_imod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_in_imod2 ob_in_imod2 ob_not_in_imod1)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        assume f_in_imod1: "f \<in> Field (Tm Imod1)"
        assume f_not_in_imod2: "f \<notin> Field (Tm Imod2)"
        have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = unspecified"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: f_in_imod1 f_not_in_imod2 field_tmod1 ob_in_imod2 ob_not_in_imod1 object_imod2)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = unspecified"
          unfolding imod_combine_field_value_def
          by (simp add: f_in_imod1 f_not_in_imod2 ob_in_imod2 ob_not_in_imod1)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        assume f_not_in_imod1: "f \<notin> Field (Tm Imod1)"
        assume f_in_imod2: "f \<in> Field (Tm Imod2)"
        have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: f_in_imod2 field_tmod2 ob_in_imod2 ob_not_in_imod1 object_imod2)
        then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue Imod2 (ob, f)"
          using f_in_imod2 ig_combine_commute imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig2 ob_in_imod2
          by metis
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = FieldValue Imod2 (ob, f)"
          unfolding imod_combine_field_value_def
          by (simp add: f_in_imod2 ob_in_imod2 ob_not_in_imod1)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_in_imod2: "ob \<in> Object Imod2"
        assume f_not_in_imod1: "f \<notin> Field (Tm Imod1)"
        assume f_not_in_imod2: "f \<notin> Field (Tm Imod2)"
        have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = undefined"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: f_not_in_imod1 f_not_in_imod2)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: f_not_in_imod1 f_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        assume f_in_imod1: "f \<in> Field (Tm Imod1)"
        assume f_in_imod2: "f \<in> Field (Tm Imod2)"
        have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = undefined"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        assume f_in_imod1: "f \<in> Field (Tm Imod1)"
        assume f_not_in_imod2: "f \<notin> Field (Tm Imod2)"
        have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = undefined"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        assume f_not_in_imod1: "f \<notin> Field (Tm Imod1)"
        assume f_in_imod2: "f \<in> Field (Tm Imod2)"
        have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = undefined"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume ob_not_in_imod1: "ob \<notin> Object Imod1"
        assume ob_not_in_imod2: "ob \<notin> Object Imod2"
        assume f_not_in_imod1: "f \<notin> Field (Tm Imod1)"
        assume f_not_in_imod2: "f \<notin> Field (Tm Imod2)"
        have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = undefined"
          unfolding imod_combine_field_value_mapping_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        have "imod_combine_field_value Imod1 Imod2 (ob, f) = undefined"
          unfolding imod_combine_field_value_def
          by (simp add: ob_not_in_imod1 ob_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      qed
    qed
    then show "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) = imod_combine_field_value Imod1 Imod2"
      by fastforce
  next
    have constant_tmod1: "{c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)} = Constant (Tm Imod1)"
    proof
      show "{c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)} \<subseteq> Constant (Tm Imod1)"
        by blast
    next
      have "Constant (Tm Imod1) \<subseteq> {c \<in> Constant (Tm (f1 IG1)). c \<in> Constant (Tm Imod1)}"
        using mapping_ig1 imod_combine_mapping_function.mapping_correct
        by blast
      then show "Constant (Tm Imod1) \<subseteq> {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)}"
        using tmod1_def
        by simp
    qed
    have constant_tmod2: "{c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)} = Constant (Tm Imod2)"
    proof
      show "{c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)} \<subseteq> Constant (Tm Imod2)"
        by blast
    next
      have "Constant (Tm Imod2) \<subseteq> {c \<in> Constant (Tm (f2 IG2)). c \<in> Constant (Tm Imod2)}"
        using mapping_ig2 imod_combine_mapping_function.mapping_correct
        by blast
      then show "Constant (Tm Imod2) \<subseteq> {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)}"
        using tmod2_def
        by simp
    qed
    show "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) = imod_combine_default_value Imod1 Imod2"
    proof
      fix c
      have c_imod1_cases: "c \<in> Constant (Tm Imod1) \<or> c \<notin> Constant (Tm Imod1)"
        by simp
      have c_imod2_cases: "c \<in> Constant (Tm Imod2) \<or> c \<notin> Constant (Tm Imod2)"
        by simp
      show "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = imod_combine_default_value Imod1 Imod2 c"
        using c_imod1_cases c_imod2_cases
      proof (elim disjE)
        assume c_in_imod1: "c \<in> Constant (Tm Imod1)"
        assume c_in_imod2: "c \<in> Constant (Tm Imod2)"
        show ?thesis
        proof (induct "DefaultValue Imod1 c = DefaultValue Imod2 c")
          case True
          then have "DefaultValue (f1 (ig_combine IG1 IG2)) c = DefaultValue (f2 (ig_combine IG1 IG2)) c"
            using c_in_imod1 c_in_imod2 ig_combine_commute imod_combine_mapping_function.func_default_value imod_combine_mapping_function.mapping_correct mapping_ig1 mapping_ig2
            by metis
          then have "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = DefaultValue (f1 (ig_combine IG1 IG2)) c"
            unfolding imod_combine_default_value_mapping_def
            by (simp add: c_in_imod1 constant_tmod1)
          then have mapping_def: "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = DefaultValue Imod1 c"
            using c_in_imod1 imod_combine_mapping_function.func_default_value imod_combine_mapping_function.mapping_correct mapping_ig1
            by metis
          have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod1 c"
            unfolding imod_combine_default_value_def
            using True.hyps c_in_imod2
            by simp
          then show ?case
            by (simp add: mapping_def)
        next
          case False
          then have "DefaultValue (f1 (ig_combine IG1 IG2)) c \<noteq> DefaultValue (f2 (ig_combine IG1 IG2)) c"
            using c_in_imod1 c_in_imod2 ig_combine_commute imod_combine_mapping_function.func_default_value imod_combine_mapping_function.mapping_correct mapping_ig1 mapping_ig2
            by metis
          then have mapping_def: "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = ValueDef.invalid"
            unfolding imod_combine_default_value_mapping_def
            by (simp add: c_in_imod1 c_in_imod2 constant_tmod1 constant_tmod2)
          have "imod_combine_default_value Imod1 Imod2 c = ValueDef.invalid"
            unfolding imod_combine_default_value_def
            using False.hyps c_in_imod1 c_in_imod2
            by simp
          then show ?case
            by (simp add: mapping_def)
        qed
      next
        assume c_in_imod1: "c \<in> Constant (Tm Imod1)"
        assume c_not_in_imod2: "c \<notin> Constant (Tm Imod2)"
        have "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = DefaultValue (f1 (ig_combine IG1 IG2)) c"
          unfolding imod_combine_default_value_mapping_def
          by (simp add: c_in_imod1 c_not_in_imod2 constant_tmod1)
        then have mapping_def: "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = DefaultValue Imod1 c"
          using c_in_imod1 imod_combine_mapping_function.func_default_value imod_combine_mapping_function.mapping_correct mapping_ig1
          by metis
        have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod1 c"
          unfolding imod_combine_default_value_def
          by (simp add: c_in_imod1 c_not_in_imod2)
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume c_not_in_imod1: "c \<notin> Constant (Tm Imod1)"
        assume c_in_imod2: "c \<in> Constant (Tm Imod2)"
        have "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = DefaultValue (f2 (ig_combine IG1 IG2)) c"
          unfolding imod_combine_default_value_mapping_def
          by (simp add: c_in_imod2 c_not_in_imod1 constant_tmod2)
        then have mapping_def: "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = DefaultValue Imod2 c"
          using c_in_imod2 ig_combine_commute imod_combine_mapping_function.func_default_value imod_combine_mapping_function.mapping_correct mapping_ig2
          by metis
        have "imod_combine_default_value Imod1 Imod2 c = DefaultValue Imod2 c"
          unfolding imod_combine_default_value_def
          using c_in_imod2 c_not_in_imod1
          by simp
        then show ?thesis
          by (simp add: mapping_def)
      next
        assume c_not_in_imod1: "c \<notin> Constant (Tm Imod1)"
        assume c_not_in_imod2: "c \<notin> Constant (Tm Imod2)"
        have mapping_def: "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = undefined"
          unfolding imod_combine_default_value_mapping_def
          by (simp add: c_not_in_imod1 c_not_in_imod2)
        have "imod_combine_default_value Imod1 Imod2 c = undefined"
          unfolding imod_combine_default_value_def
          using c_not_in_imod1 c_not_in_imod2
          by simp
        then show ?thesis
          by (simp add: mapping_def)
      qed
    qed
  qed (simp)
qed

lemma imod_combine_mapping_function_correct:
  assumes mapping_ig1: "imod_combine_mapping_function f1 IG1 Imod1"
  assumes mapping_ig2: "imod_combine_mapping_function f2 IG2 Imod2"
  shows "imod_combine_mapping_function (imod_combine_mapping (f1) Imod1 (f2) Imod2) (ig_combine IG1 IG2) (imod_combine Imod1 Imod2)"
proof (intro imod_combine_mapping_function.intro)
  show "imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) = imod_combine Imod1 Imod2"
    using assms imod_combine_mapping_correct
    by blast
next
  fix IG3
  have "Tm (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)) = tmod_combine (Tm (f1 (ig_combine IG1 IG2))) (Tm (f2 (ig_combine IG1 IG2)))"
    by (simp add: imod_combine_mapping_def)
  then have "Tm (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)) = tmod_combine (Tm (f1 IG1)) (Tm (f2 IG2))"
    using ig_combine_commute imod_combine_mapping_function.func_tm mapping_ig1 mapping_ig2
    by metis
  then have "Tm (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)) = tmod_combine (Tm (f1 (ig_combine IG1 (ig_combine IG2 IG3)))) (Tm (f2 (ig_combine IG2 (ig_combine IG1 IG3))))"
    using imod_combine_mapping_function.func_tm mapping_ig1 mapping_ig2
    by metis
  then have "Tm (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)) = tmod_combine (Tm (f1 (ig_combine (ig_combine IG1 IG2) IG3))) (Tm (f2 (ig_combine (ig_combine IG1 IG2) IG3)))"
    using ig_combine_assoc ig_combine_commute
    by metis
  then show "Tm (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)) = Tm (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3))"
    by (simp add: imod_combine_mapping_def)
next
  fix IG3
  show "Object (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)) \<subseteq> Object (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3))"
  proof
    fix x
    assume "x \<in> Object (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2))"
    then have "x \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<union> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
      unfolding imod_combine_mapping_def
      by simp
    then have "x \<in> {ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1} \<union> {ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2}"
    proof (elim UnE)
      assume "x \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
      then have "x \<in> Object Imod1"
        by simp
      then have "x \<in> {ob \<in> Object (f1 (ig_combine IG1 (ig_combine IG2 IG3))). ob \<in> Object Imod1}"
        using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig1
        by fastforce
      then have "x \<in> {ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1}"
        using ig_combine_assoc
        by metis
      then show ?thesis
        by simp
    next
      assume "x \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
      then have "x \<in> Object Imod2"
        by simp
      then have "x \<in> {ob \<in> Object (f2 (ig_combine IG2 (ig_combine IG1 IG3))). ob \<in> Object Imod2}"
        using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig2
        by fastforce
      then have "x \<in> {ob \<in> Object (f2 (ig_combine (ig_combine IG2 IG1) IG3)). ob \<in> Object Imod2}"
        using ig_combine_assoc
        by metis
      then show ?thesis
        by simp
    qed
    then show "x \<in> Object (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3))"
      unfolding imod_combine_mapping_def
      by simp
  qed
next
  fix IG3 ob
  have object_imod1: "{ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} = {ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1}"
  proof
    show "{ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<subseteq> 
      {ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1}"
    proof
      fix x
      assume "x \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
      then have "x \<in> Object Imod1"
        by simp
      then have "x \<in> {ob \<in> Object (f1 (ig_combine IG1 (ig_combine IG2 IG3))). ob \<in> Object Imod1}"
        using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig1
        by fastforce
      then show "x \<in> {ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1}"
        using ig_combine_assoc
        by metis
    qed
  next
    show "{ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1} \<subseteq> 
      {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
      using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig1
      by fastforce
  qed
  have f1_objectclass_altdef: "\<And>x. x \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<Longrightarrow>
    ObjectClass (f1 (ig_combine IG1 IG2)) x = ObjectClass (f1 (ig_combine (ig_combine IG1 IG2) IG3)) x"
  proof-
    fix x
    assume "x \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
    then have x_in_imod1: "x \<in> Object Imod1"
      by simp
    have imod1_imod12: "ObjectClass (f1 IG1) x = ObjectClass (f1 (ig_combine IG1 IG2)) x"
      using imod_combine_mapping_function.func_object_class imod_combine_mapping_function.mapping_correct mapping_ig1 x_in_imod1
      by metis
    have imod1_imod123: "ObjectClass (f1 IG1) x = ObjectClass (f1 (ig_combine IG1 (ig_combine IG2 IG3))) x"
      using imod_combine_mapping_function.func_object_class imod_combine_mapping_function.mapping_correct mapping_ig1 x_in_imod1
      by metis
    show "ObjectClass (f1 (ig_combine IG1 IG2)) x = ObjectClass (f1 (ig_combine (ig_combine IG1 IG2) IG3)) x"
      using imod1_imod12 imod1_imod123 ig_combine_assoc
      by metis
  qed
  have object_imod2: "{ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} = {ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2}"
  proof
    show "{ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<subseteq> 
      {ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2}"
    proof
      fix x
      assume "x \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
      then have "x \<in> Object Imod2"
        by simp
      then have "x \<in> {ob \<in> Object (f2 (ig_combine IG2 (ig_combine IG1 IG3))). ob \<in> Object Imod2}"
        using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig2
        by fastforce
      then have "x \<in> {ob \<in> Object (f2 (ig_combine (ig_combine IG2 IG1) IG3)). ob \<in> Object Imod2}"
        using ig_combine_assoc
        by metis
      then show "x \<in> {ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2}"
        by simp
    qed
  next
    show "{ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2} \<subseteq> 
      {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
      using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig2
      by fastforce
  qed
  have f2_objectclass_altdef: "\<And>x. x \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<Longrightarrow> 
    ObjectClass (f2 (ig_combine IG1 IG2)) x = ObjectClass (f2 (ig_combine (ig_combine IG1 IG2) IG3)) x"
  proof-
    fix x
    assume "x \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    then have x_in_imod2: "x \<in> Object Imod2"
      by simp
    have imod1_imod12: "ObjectClass (f2 IG2) x = ObjectClass (f2 (ig_combine IG2 IG1)) x"
      using imod_combine_mapping_function.func_object_class imod_combine_mapping_function.mapping_correct mapping_ig2 x_in_imod2
      by metis
    have "ObjectClass (f2 IG2) x = ObjectClass (f2 (ig_combine IG2 (ig_combine IG1 IG3))) x"
      using imod_combine_mapping_function.func_object_class imod_combine_mapping_function.mapping_correct mapping_ig2 x_in_imod2
      by metis
    then have imod1_imod123: "ObjectClass (f2 IG2) x = ObjectClass (f2 (ig_combine (ig_combine IG2 IG1) IG3)) x"
      using ig_combine_assoc
      by metis
    show "ObjectClass (f2 (ig_combine IG1 IG2)) x = ObjectClass (f2 (ig_combine (ig_combine IG1 IG2) IG3)) x"
      using imod1_imod12 imod1_imod123
      by simp
  qed
  assume "ob \<in> Object (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2))"
  then have "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<union> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    unfolding imod_combine_mapping_def
    by simp
  then have "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<or> 
    ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} - {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<or> 
    ob \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} - {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
    by blast
  then have "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob"
  proof (elim disjE)
    assume ob_in_both: "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    show ?thesis
    proof (induct "ObjectClass (f1 (ig_combine IG1 IG2)) ob = ObjectClass (f2 (ig_combine IG1 IG2)) ob")
      case True
      then have "ObjectClass (f1 (ig_combine (ig_combine IG1 IG2) IG3)) ob = ObjectClass (f2 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
        using f1_objectclass_altdef f2_objectclass_altdef ob_in_both
        by simp
      then have "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectClass (f1 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
        unfolding imod_combine_object_class_mapping_def
        using ob_in_both object_imod2
        by simp
      then have mapping_def: "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectClass (f1 (ig_combine IG1 IG2)) ob"
        using f1_objectclass_altdef ob_in_both
        by simp
      have "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectClass (f1 (ig_combine IG1 IG2)) ob"
        unfolding imod_combine_object_class_mapping_def
        using True.hyps ob_in_both
        by simp
      then show ?case
        using mapping_def
        by simp
    next
      case False
      then have "ObjectClass (f1 (ig_combine (ig_combine IG1 IG2) IG3)) ob \<noteq> ObjectClass (f2 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
        using f1_objectclass_altdef f2_objectclass_altdef ob_in_both
        by simp
      then have mapping_def: "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = undefined"
        unfolding imod_combine_object_class_mapping_def
        using ob_in_both object_imod1 object_imod2
        by simp
      have "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = undefined"
        unfolding imod_combine_object_class_mapping_def
        using False.hyps ob_in_both
        by simp
      then show ?case
        using mapping_def
        by simp
    qed
  next
    assume ob_in_imod1: "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} - {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    have "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectClass (f1 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
      unfolding imod_combine_object_class_mapping_def
      using ob_in_imod1 object_imod1 object_imod2
      by auto
    then have mapping_def: "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectClass (f1 (ig_combine IG1 IG2)) ob"
      using f1_objectclass_altdef ob_in_imod1
      by simp
    have "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectClass (f1 (ig_combine IG1 IG2)) ob"
      unfolding imod_combine_object_class_mapping_def
      using ob_in_imod1
      by auto
    then show ?thesis
      using mapping_def
      by simp
  next
    assume ob_in_imod2: "ob \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} - {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
    have "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectClass (f2 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
      unfolding imod_combine_object_class_mapping_def
      using ob_in_imod2 object_imod1 object_imod2
      by auto
    then have mapping_def: "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectClass (f2 (ig_combine IG1 IG2)) ob"
      using f2_objectclass_altdef ob_in_imod2
      by simp
    have "imod_combine_object_class_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectClass (f2 (ig_combine IG1 IG2)) ob"
      unfolding imod_combine_object_class_mapping_def
      using ob_in_imod2
      by auto
    then show ?thesis
      using mapping_def
      by simp
  qed
  then show "ObjectClass (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)) ob = ObjectClass (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
    unfolding imod_combine_mapping_def
    by simp
next
  fix IG3 ob
  have object_imod1: "{ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} = {ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1}"
  proof
    show "{ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<subseteq> 
      {ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1}"
    proof
      fix x
      assume "x \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
      then have "x \<in> Object Imod1"
        by simp
      then have "x \<in> {ob \<in> Object (f1 (ig_combine IG1 (ig_combine IG2 IG3))). ob \<in> Object Imod1}"
        using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig1
        by fastforce
      then show "x \<in> {ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1}"
        using ig_combine_assoc
        by metis
    qed
  next
    show "{ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1} \<subseteq> 
      {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
      using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig1
      by fastforce
  qed
  have f1_objectid_altdef: "\<And>x. x \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<Longrightarrow>
    ObjectId (f1 (ig_combine IG1 IG2)) x = ObjectId (f1 (ig_combine (ig_combine IG1 IG2) IG3)) x"
  proof-
    fix x
    assume "x \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
    then have x_in_imod1: "x \<in> Object Imod1"
      by simp
    have imod1_imod12: "ObjectId (f1 IG1) x = ObjectId (f1 (ig_combine IG1 IG2)) x"
      using imod_combine_mapping_function.func_object_id imod_combine_mapping_function.mapping_correct mapping_ig1 x_in_imod1
      by metis
    have imod1_imod123: "ObjectId (f1 IG1) x = ObjectId (f1 (ig_combine IG1 (ig_combine IG2 IG3))) x"
      using imod_combine_mapping_function.func_object_id imod_combine_mapping_function.mapping_correct mapping_ig1 x_in_imod1
      by metis
    show "ObjectId (f1 (ig_combine IG1 IG2)) x = ObjectId (f1 (ig_combine (ig_combine IG1 IG2) IG3)) x"
      using imod1_imod12 imod1_imod123 ig_combine_assoc
      by metis
  qed
  have object_imod2: "{ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} = {ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2}"
  proof
    show "{ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<subseteq> 
      {ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2}"
    proof
      fix x
      assume "x \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
      then have "x \<in> Object Imod2"
        by simp
      then have "x \<in> {ob \<in> Object (f2 (ig_combine IG2 (ig_combine IG1 IG3))). ob \<in> Object Imod2}"
        using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig2
        by fastforce
      then have "x \<in> {ob \<in> Object (f2 (ig_combine (ig_combine IG2 IG1) IG3)). ob \<in> Object Imod2}"
        using ig_combine_assoc
        by metis
      then show "x \<in> {ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2}"
        by simp
    qed
  next
    show "{ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2} \<subseteq> 
      {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
      using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig2
      by fastforce
  qed
  have f2_objectid_altdef: "\<And>x. x \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<Longrightarrow> 
    ObjectId (f2 (ig_combine IG1 IG2)) x = ObjectId (f2 (ig_combine (ig_combine IG1 IG2) IG3)) x"
  proof-
    fix x
    assume "x \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    then have x_in_imod2: "x \<in> Object Imod2"
      by simp
    have imod1_imod12: "ObjectId (f2 IG2) x = ObjectId (f2 (ig_combine IG2 IG1)) x"
      using imod_combine_mapping_function.func_object_id imod_combine_mapping_function.mapping_correct mapping_ig2 x_in_imod2
      by metis
    have "ObjectId (f2 IG2) x = ObjectId (f2 (ig_combine IG2 (ig_combine IG1 IG3))) x"
      using imod_combine_mapping_function.func_object_id imod_combine_mapping_function.mapping_correct mapping_ig2 x_in_imod2
      by metis
    then have imod1_imod123: "ObjectId (f2 IG2) x = ObjectId (f2 (ig_combine (ig_combine IG2 IG1) IG3)) x"
      using ig_combine_assoc
      by metis
    show "ObjectId (f2 (ig_combine IG1 IG2)) x = ObjectId (f2 (ig_combine (ig_combine IG1 IG2) IG3)) x"
      using imod1_imod12 imod1_imod123
      by simp
  qed
  assume "ob \<in> Object (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2))"
  then have "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<union> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    unfolding imod_combine_mapping_def
    by simp
  then have "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<or> 
    ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} - {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<or> 
    ob \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} - {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
    by blast
  then have "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob"
  proof (elim disjE)
    assume ob_in_both: "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    show ?thesis
    proof (induct "ObjectId (f1 (ig_combine IG1 IG2)) ob = ObjectId (f2 (ig_combine IG1 IG2)) ob")
      case True
      then have "ObjectId (f1 (ig_combine (ig_combine IG1 IG2) IG3)) ob = ObjectId (f2 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
        using f1_objectid_altdef f2_objectid_altdef ob_in_both
        by simp
      then have "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectId (f1 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
        unfolding imod_combine_object_id_mapping_def
        using ob_in_both object_imod2
        by simp
      then have mapping_def: "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectId (f1 (ig_combine IG1 IG2)) ob"
        using f1_objectid_altdef ob_in_both
        by simp
      have "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectId (f1 (ig_combine IG1 IG2)) ob"
        unfolding imod_combine_object_id_mapping_def
        using True.hyps ob_in_both
        by simp
      then show ?case
        using mapping_def
        by simp
    next
      case False
      then have "ObjectId (f1 (ig_combine (ig_combine IG1 IG2) IG3)) ob \<noteq> ObjectId (f2 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
        using f1_objectid_altdef f2_objectid_altdef ob_in_both
        by simp
      then have mapping_def: "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = undefined"
        unfolding imod_combine_object_id_mapping_def
        using ob_in_both object_imod1 object_imod2
        by simp
      have "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = undefined"
        unfolding imod_combine_object_id_mapping_def
        using False.hyps ob_in_both
        by simp
      then show ?case
        using mapping_def
        by simp
    qed
  next
    assume ob_in_imod1: "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} - {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    have "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectId (f1 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
      unfolding imod_combine_object_id_mapping_def
      using ob_in_imod1 object_imod1 object_imod2
      by auto
    then have mapping_def: "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectId (f1 (ig_combine IG1 IG2)) ob"
      using f1_objectid_altdef ob_in_imod1
      by simp
    have "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectId (f1 (ig_combine IG1 IG2)) ob"
      unfolding imod_combine_object_id_mapping_def
      using ob_in_imod1
      by auto
    then show ?thesis
      using mapping_def
      by simp
  next
    assume ob_in_imod2: "ob \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} - {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
    have "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectId (f2 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
      unfolding imod_combine_object_id_mapping_def
      using ob_in_imod2 object_imod1 object_imod2
      by auto
    then have mapping_def: "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) ob = ObjectId (f2 (ig_combine IG1 IG2)) ob"
      using f2_objectid_altdef ob_in_imod2
      by simp
    have "imod_combine_object_id_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) ob = ObjectId (f2 (ig_combine IG1 IG2)) ob"
      unfolding imod_combine_object_id_mapping_def
      using ob_in_imod2
      by auto
    then show ?thesis
      using mapping_def
      by simp
  qed
  then show "ObjectId (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)) ob = ObjectId (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3)) ob"
    unfolding imod_combine_mapping_def
    by simp
next
  fix IG3 ob f
  have object_imod1: "{ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} = {ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1}"
  proof
    show "{ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<subseteq> 
      {ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1}"
    proof
      fix x
      assume "x \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
      then have "x \<in> Object Imod1"
        by simp
      then have "x \<in> {ob \<in> Object (f1 (ig_combine IG1 (ig_combine IG2 IG3))). ob \<in> Object Imod1}"
        using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig1
        by fastforce
      then show "x \<in> {ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1}"
        using ig_combine_assoc
        by metis
    qed
  next
    show "{ob \<in> Object (f1 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod1} \<subseteq> 
      {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
      using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig1
      by fastforce
  qed
  have field_imod1: "{f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} = {f \<in> Field (Tm (f1 (ig_combine (ig_combine IG1 IG2) IG3))). f \<in> Field (Tm Imod1)}"
  proof
    show "{f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} \<subseteq> 
      {f \<in> Field (Tm (f1 (ig_combine (ig_combine IG1 IG2) IG3))). f \<in> Field (Tm Imod1)}"
    proof
      fix x
      assume "x \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)}"
      then have "x \<in> Field (Tm Imod1)"
        by simp
      then have "x \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 (ig_combine IG2 IG3)))). f \<in> Field (Tm Imod1)}"
        using Collect_conj_eq Collect_mem_eq Int_iff imod_combine_mapping_function_def mapping_ig1
        by metis
      then show "x \<in> {f \<in> Field (Tm (f1 (ig_combine (ig_combine IG1 IG2) IG3))). f \<in> Field (Tm Imod1)}"
        using ig_combine_assoc
        by metis
    qed
  next
    show "{f \<in> Field (Tm (f1 (ig_combine (ig_combine IG1 IG2) IG3))). f \<in> Field (Tm Imod1)} \<subseteq> 
      {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)}"
    proof
      fix x
      assume "x \<in> {f \<in> Field (Tm (f1 (ig_combine (ig_combine IG1 IG2) IG3))). f \<in> Field (Tm Imod1)}"
      then have "x \<in> Field (Tm Imod1)"
        by simp
      then show "x \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)}"
        using Collect_conj_eq Collect_mem_eq Int_iff imod_combine_mapping_function_def mapping_ig1
        by metis
    qed
  qed
  have f1_fieldvalue_altdef: "\<And>x y. x \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<Longrightarrow> 
    y \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} \<Longrightarrow> 
    FieldValue (f1 (ig_combine IG1 IG2)) (x, y) = FieldValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) (x, y)"
  proof-
    fix x y
    assume "x \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
    then have x_in_imod1: "x \<in> Object Imod1"
      by simp
    assume "y \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)}"
    then have y_in_imod1: "y \<in> Field (Tm Imod1)"
      by simp
    have imod1_imod12: "FieldValue (f1 IG1) (x, y) = FieldValue (f1 (ig_combine IG1 IG2)) (x, y)"
      using imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig1 x_in_imod1 y_in_imod1
      by metis
    have imod1_imod123: "FieldValue (f1 IG1) (x, y) = FieldValue (f1 (ig_combine IG1 (ig_combine IG2 IG3))) (x, y)"
      using imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig1 x_in_imod1 y_in_imod1
      by metis
    show "FieldValue (f1 (ig_combine IG1 IG2)) (x, y) = FieldValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) (x, y)"
      using imod1_imod12 imod1_imod123 ig_combine_assoc
      by metis
  qed
  have object_imod2: "{ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} = {ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2}"
  proof
    show "{ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<subseteq> 
      {ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2}"
    proof
      fix x
      assume "x \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
      then have "x \<in> Object Imod2"
        by simp
      then have "x \<in> {ob \<in> Object (f2 (ig_combine IG2 (ig_combine IG1 IG3))). ob \<in> Object Imod2}"
        using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig2
        by fastforce
      then have "x \<in> {ob \<in> Object (f2 (ig_combine (ig_combine IG2 IG1) IG3)). ob \<in> Object Imod2}"
        using ig_combine_assoc
        by metis
      then show "x \<in> {ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2}"
        by simp
    qed
  next
    show "{ob \<in> Object (f2 (ig_combine (ig_combine IG1 IG2) IG3)). ob \<in> Object Imod2} \<subseteq> 
      {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
      using imod_combine_mapping_function.mapping_correct imod_combine_mapping_function.subset_object mapping_ig2
      by fastforce
  qed
  have field_imod2: "{f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)} = {f \<in> Field (Tm (f2 (ig_combine (ig_combine IG1 IG2) IG3))). f \<in> Field (Tm Imod2)}"
  proof
    show "{f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)} \<subseteq> 
      {f \<in> Field (Tm (f2 (ig_combine (ig_combine IG1 IG2) IG3))). f \<in> Field (Tm Imod2)}"
    proof
      fix x
      assume "x \<in> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
      then have "x \<in> Field (Tm Imod2)"
        by simp
      then have "x \<in> {f \<in> Field (Tm (f2 (ig_combine IG2 (ig_combine IG1 IG3)))). f \<in> Field (Tm Imod2)}"
        using Collect_conj_eq Collect_mem_eq Int_iff imod_combine_mapping_function_def mapping_ig2
        by metis
      then have "x \<in> {f \<in> Field (Tm (f2 (ig_combine (ig_combine IG2 IG1) IG3))). f \<in> Field (Tm Imod2)}"
        using ig_combine_assoc
        by metis
      then show "x \<in> {f \<in> Field (Tm (f2 (ig_combine (ig_combine IG1 IG2) IG3))). f \<in> Field (Tm Imod2)}"
        by simp
    qed
  next
    show "{f \<in> Field (Tm (f2 (ig_combine (ig_combine IG1 IG2) IG3))). f \<in> Field (Tm Imod2)} \<subseteq> 
      {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
    proof
      fix x
      assume "x \<in> {f \<in> Field (Tm (f2 (ig_combine (ig_combine IG1 IG2) IG3))). f \<in> Field (Tm Imod2)}"
      then have "x \<in> Field (Tm Imod2)"
        by simp
      then have "x \<in> {f \<in> Field (Tm (f2 (ig_combine IG2 IG1))). f \<in> Field (Tm Imod2)}"
        using Collect_conj_eq Collect_mem_eq Int_iff imod_combine_mapping_function_def mapping_ig2
        by metis
      then show "x \<in> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
        by simp
    qed
  qed
  have f2_fieldvalue_altdef: "\<And>x y. x \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<Longrightarrow> 
    y \<in> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)} \<Longrightarrow> 
    FieldValue (f2 (ig_combine IG1 IG2)) (x, y) = FieldValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) (x, y)"
  proof-
    fix x y
    assume "x \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    then have x_in_imod2: "x \<in> Object Imod2"
      by simp
    assume "y \<in> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
    then have y_in_imod2: "y \<in> Field (Tm Imod2)"
      by simp
    have imod1_imod12: "FieldValue (f2 IG2) (x, y) = FieldValue (f2 (ig_combine IG2 IG1)) (x, y)"
      using imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig2 x_in_imod2 y_in_imod2
      by metis
    have "FieldValue (f2 IG2) (x, y) = FieldValue (f2 (ig_combine IG2 (ig_combine IG1 IG3))) (x, y)"
      using imod_combine_mapping_function.func_field_value imod_combine_mapping_function.mapping_correct mapping_ig2 x_in_imod2 y_in_imod2
      by metis
    then have imod1_imod123: "FieldValue (f2 IG2) (x, y) = FieldValue (f2 (ig_combine (ig_combine IG2 IG1) IG3)) (x, y)"
      using ig_combine_assoc
      by metis
    show "FieldValue (f2 (ig_combine IG1 IG2)) (x, y) = FieldValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) (x, y)"
      using imod1_imod12 imod1_imod123
      by simp
  qed
  assume "ob \<in> Object (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2))"
  then have "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<union> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    unfolding imod_combine_mapping_def
    by simp
  then have ob_cases: "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<or> 
    ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} - {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} \<or> 
    ob \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} - {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
    by blast
  assume "f \<in> Field (Tm (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)))"
  then have "f \<in> Field (tmod_combine (Tm (f1 (ig_combine IG1 IG2))) (Tm (f2 (ig_combine IG1 IG2))))"
    unfolding imod_combine_mapping_def
    by simp
  then have "f \<in> Field (Tm (f1 (ig_combine IG1 IG2))) \<union> Field (Tm (f2 (ig_combine IG1 IG2)))"
    unfolding tmod_combine_def
    by simp
  then have "f \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} \<union> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
  proof (elim UnE)
    assume "f \<in> Field (Tm (f1 (ig_combine IG1 IG2)))"
    then have "f \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)}"
      using imod_combine_mapping_function.func_tm imod_combine_mapping_function.mapping_correct mapping_ig1
      by fastforce
    then show ?thesis
      by simp
  next
    assume "f \<in> Field (Tm (f2 (ig_combine IG1 IG2)))"
    then have "f \<in> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
      using imod_combine_mapping_function.func_tm imod_combine_mapping_function.mapping_correct mapping_ig2
      by fastforce
    then show ?thesis
      by simp
  qed
  then have f_cases: "f \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} \<inter> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)} \<or>
    f \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} - {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)} \<or>
    f \<in> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)} - {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)}"
    by blast
  have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f)"
    using ob_cases f_cases
  proof (elim disjE)
    assume ob_in_both: "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    assume f_in_both: "f \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} \<inter> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
    show ?thesis
    proof (induct "FieldValue (f1 (ig_combine IG1 IG2)) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)")
      case True
      then have "FieldValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f) = FieldValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f)"
        using f1_fieldvalue_altdef f2_fieldvalue_altdef f_in_both ob_in_both
        by simp
      then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
        unfolding imod_combine_field_value_mapping_def
        using f_in_both field_imod2 ob_in_both object_imod2 f1_fieldvalue_altdef
        by simp
      have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
        unfolding imod_combine_field_value_mapping_def
        using True.hyps f_in_both ob_in_both
        by simp
      then show ?case
        using mapping_def
        by simp
    next
      case False
      then show ?case
      proof (induct "FieldValue (f1 (ig_combine IG1 IG2)) (ob, f) = unspecified")
        case True
        then have "FieldValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f) = unspecified"
          using f1_fieldvalue_altdef f_in_both ob_in_both
          by simp
        then have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f)"
          unfolding imod_combine_field_value_mapping_def
          using f_in_both ob_in_both field_imod2 object_imod2
          by simp
        then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
          using f2_fieldvalue_altdef f_in_both ob_in_both
          by simp
        have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
          unfolding imod_combine_field_value_mapping_def
          using True.hyps f_in_both ob_in_both
          by simp
        then show ?case
          using mapping_def
          by simp
      next
        case False
        then show ?case
        proof (induct "FieldValue (f2 (ig_combine IG1 IG2)) (ob, f) = unspecified")
          case True
          then have "FieldValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f) = unspecified"
            using f2_fieldvalue_altdef f_in_both ob_in_both
            by simp
          then have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f)"
            unfolding imod_combine_field_value_mapping_def
            using f_in_both ob_in_both field_imod1 object_imod1
            by simp
          then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
            using f1_fieldvalue_altdef f_in_both ob_in_both
            by simp
          have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
            unfolding imod_combine_field_value_mapping_def
            using True.hyps f_in_both ob_in_both
            by simp
          then show ?case
            using mapping_def
            by simp
        next
          case False
          then have value_neq: "FieldValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f) \<noteq> FieldValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f)"
            using f1_fieldvalue_altdef f2_fieldvalue_altdef f_in_both ob_in_both
            by simp
          have value_f1: "FieldValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f) \<noteq> unspecified"
            using False.prems f1_fieldvalue_altdef f_in_both ob_in_both
            by simp
          have value_f2: "FieldValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f) \<noteq> unspecified"
            using False.hyps f2_fieldvalue_altdef f_in_both ob_in_both
            by simp
          have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = ValueDef.invalid"
            unfolding imod_combine_field_value_mapping_def
            using f_in_both field_imod1 field_imod2 ob_in_both object_imod1 object_imod2 value_f1 value_f2 value_neq
            by simp
          have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = ValueDef.invalid"
            unfolding imod_combine_field_value_mapping_def
            using False.hyps False.prems f_in_both ob_in_both
            by simp
          then show ?case
            using mapping_def
            by simp
        qed
      qed
    qed
  next
    assume ob_in_both: "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    assume f_in_f1: "f \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} - {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f1 field_imod1 field_imod2 ob_in_both object_imod1
      by auto
    then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
      using f1_fieldvalue_altdef f_in_f1 ob_in_both
      by simp
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f1 ob_in_both
      by auto
    then show ?thesis
      using mapping_def
      by simp
  next
    assume ob_in_both: "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} \<inter> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    assume f_in_f2: "f \<in> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)} - {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)}"
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f2 field_imod1 field_imod2 ob_in_both object_imod2
      by auto
    then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
      using f2_fieldvalue_altdef f_in_f2 ob_in_both
      by simp
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f2 ob_in_both
      by auto
    then show ?thesis
      using mapping_def
      by simp
  next
    assume ob_in_f1: "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} - {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    assume f_in_both: "f \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} \<inter> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_both field_imod1 ob_in_f1 object_imod1 object_imod2
      by auto
    then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
      using f1_fieldvalue_altdef f_in_both ob_in_f1
      by simp
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_both ob_in_f1
      by auto
    then show ?thesis
      using mapping_def
      by simp
  next
    assume ob_in_f2: "ob \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} - {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
    assume f_in_both: "f \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} \<inter> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_both field_imod2 ob_in_f2 object_imod1 object_imod2
      by auto
    then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
      using f2_fieldvalue_altdef f_in_both ob_in_f2
      by simp
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_both ob_in_f2
      by auto
    then show ?thesis
      using mapping_def
      by simp
  next
    assume ob_in_f1: "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} - {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    assume f_in_f1: "f \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} - {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f1 field_imod1 ob_in_f1 object_imod1 object_imod2
      by auto
    then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
      using f1_fieldvalue_altdef f_in_f1 ob_in_f1
      by simp
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f1 (ig_combine IG1 IG2)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f1 ob_in_f1
      by auto
    then show ?thesis
      using mapping_def
      by simp
  next
    assume ob_in_f1: "ob \<in> {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1} - {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2}"
    assume f_in_f2: "f \<in> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)} - {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)}"
    have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = unspecified"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f2 field_imod1 field_imod2 ob_in_f1 object_imod1 object_imod2
      by auto
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = unspecified"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f2 ob_in_f1
      by simp
    then show ?thesis
      using mapping_def
      by simp
  next
    assume ob_in_f2: "ob \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} - {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
    assume f_in_f1: "f \<in> {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)} - {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)}"
    have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = unspecified"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f1 field_imod1 field_imod2 ob_in_f2 object_imod1 object_imod2
      by auto
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = unspecified"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f1 ob_in_f2
      by simp
    then show ?thesis
      using mapping_def
      by simp
  next
    assume ob_in_f2: "ob \<in> {ob \<in> Object (f2 (ig_combine IG1 IG2)). ob \<in> Object Imod2} - {ob \<in> Object (f1 (ig_combine IG1 IG2)). ob \<in> Object Imod1}"
    assume f_in_f2: "f \<in> {f \<in> Field (Tm (f2 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod2)} - {f \<in> Field (Tm (f1 (ig_combine IG1 IG2))). f \<in> Field (Tm Imod1)}"
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f2 field_imod2 ob_in_f2 object_imod1 object_imod2
      by auto
    then have mapping_def: "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
      using f2_fieldvalue_altdef f_in_f2 ob_in_f2
      by simp
    have "imod_combine_field_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) (ob, f) = FieldValue (f2 (ig_combine IG1 IG2)) (ob, f)"
      unfolding imod_combine_field_value_mapping_def
      using f_in_f2 ob_in_f2
      by auto
    then show ?thesis
      using mapping_def
      by simp
  qed
  then show "FieldValue (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)) (ob, f) = FieldValue (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3)) (ob, f)"
    unfolding imod_combine_mapping_def
    by simp
next
  fix IG3 c
  have constant_imod1: "{c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)} = {c \<in> Constant (Tm (f1 (ig_combine (ig_combine IG1 IG2) IG3))). c \<in> Constant (Tm Imod1)}"
  proof
    show "{c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)} \<subseteq> 
      {c \<in> Constant (Tm (f1 (ig_combine (ig_combine IG1 IG2) IG3))). c \<in> Constant (Tm Imod1)}"
    proof
      fix x
      assume "x \<in> {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)}"
      then have "x \<in> Constant (Tm Imod1)"
        by simp
      then have "x \<in> {c \<in> Constant (Tm (f1 (ig_combine IG1 (ig_combine IG2 IG3)))). c \<in> Constant (Tm Imod1)}"
        using Collect_conj_eq Collect_mem_eq Int_iff imod_combine_mapping_function_def mapping_ig1
        by metis
      then show "x \<in> {c \<in> Constant (Tm (f1 (ig_combine (ig_combine IG1 IG2) IG3))). c \<in> Constant (Tm Imod1)}"
        using ig_combine_assoc
        by metis
    qed
  next
    show "{c \<in> Constant (Tm (f1 (ig_combine (ig_combine IG1 IG2) IG3))). c \<in> Constant (Tm Imod1)} \<subseteq> 
      {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)}"
    proof
      fix x
      assume "x \<in> {c \<in> Constant (Tm (f1 (ig_combine (ig_combine IG1 IG2) IG3))). c \<in> Constant (Tm Imod1)}"
      then have "x \<in> Constant (Tm Imod1)"
        by simp
      then show "x \<in> {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)}"
        using Collect_conj_eq Collect_mem_eq Int_iff imod_combine_mapping_function_def mapping_ig1
        by metis
    qed
  qed
  have f1_defaultvalue_altdef: "\<And>x. x \<in> {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)} \<Longrightarrow>
    DefaultValue (f1 (ig_combine IG1 IG2)) x = DefaultValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) x"
  proof-
    fix x
    assume "x \<in> {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)}"
    then have x_in_imod1: "x \<in> Constant (Tm Imod1)"
      by simp
    have imod1_imod12: "DefaultValue (f1 IG1) x = DefaultValue (f1 (ig_combine IG1 IG2)) x"
      using imod_combine_mapping_function.func_default_value imod_combine_mapping_function.mapping_correct mapping_ig1 x_in_imod1
      by metis
    have imod1_imod123: "DefaultValue (f1 IG1) x = DefaultValue (f1 (ig_combine IG1 (ig_combine IG2 IG3))) x"
      using imod_combine_mapping_function.func_default_value imod_combine_mapping_function.mapping_correct mapping_ig1 x_in_imod1
      by metis
    show "DefaultValue (f1 (ig_combine IG1 IG2)) x = DefaultValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) x"
      using imod1_imod12 imod1_imod123 ig_combine_assoc
      by metis
  qed
  have constant_imod2: "{c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)} = {c \<in> Constant (Tm (f2 (ig_combine (ig_combine IG1 IG2) IG3))). c \<in> Constant (Tm Imod2)}"
  proof
    show "{c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)} \<subseteq> 
      {c \<in> Constant (Tm (f2 (ig_combine (ig_combine IG1 IG2) IG3))). c \<in> Constant (Tm Imod2)}"
    proof
      fix x
      assume "x \<in> {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)}"
      then have "x \<in> Constant (Tm Imod2)"
        by simp
      then have "x \<in> {c \<in> Constant (Tm (f2 (ig_combine IG2 (ig_combine IG1 IG3)))). c \<in> Constant (Tm Imod2)}"
        using Collect_conj_eq Collect_mem_eq Int_iff imod_combine_mapping_function_def mapping_ig2
        by metis
      then have "x \<in> {c \<in> Constant (Tm (f2 (ig_combine (ig_combine IG2 IG1) IG3))). c \<in> Constant (Tm Imod2)}"
        using ig_combine_assoc
        by metis
      then show "x \<in> {c \<in> Constant (Tm (f2 (ig_combine (ig_combine IG1 IG2) IG3))). c \<in> Constant (Tm Imod2)}"
        by simp
    qed
  next
    show "{c \<in> Constant (Tm (f2 (ig_combine (ig_combine IG1 IG2) IG3))). c \<in> Constant (Tm Imod2)} \<subseteq> 
      {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)}"
    proof
      fix x
      assume "x \<in> {c \<in> Constant (Tm (f2 (ig_combine (ig_combine IG1 IG2) IG3))). c \<in> Constant (Tm Imod2)}"
      then have "x \<in> Constant (Tm Imod2)"
        by simp
      then have "x \<in> {c \<in> Constant (Tm (f2 (ig_combine IG2 IG1))). c \<in> Constant (Tm Imod2)}"
        using Collect_conj_eq Collect_mem_eq Int_iff imod_combine_mapping_function_def mapping_ig2
        by metis
      then show "x \<in> {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)}"
        by simp
    qed
  qed
  have f2_defaultvalue_altdef: "\<And>x. x \<in> {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)} \<Longrightarrow> 
    DefaultValue (f2 (ig_combine IG1 IG2)) x = DefaultValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) x"
  proof-
    fix x
    assume "x \<in> {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)}"
    then have x_in_imod2: "x \<in> Constant (Tm Imod2)"
      by simp
    have imod1_imod12: "DefaultValue (f2 IG2) x = DefaultValue (f2 (ig_combine IG2 IG1)) x"
      using imod_combine_mapping_function.func_default_value imod_combine_mapping_function.mapping_correct mapping_ig2 x_in_imod2
      by metis
    have "DefaultValue (f2 IG2) x = DefaultValue (f2 (ig_combine IG2 (ig_combine IG1 IG3))) x"
      using imod_combine_mapping_function.func_default_value imod_combine_mapping_function.mapping_correct mapping_ig2 x_in_imod2
      by metis
    then have imod1_imod123: "DefaultValue (f2 IG2) x = DefaultValue (f2 (ig_combine (ig_combine IG2 IG1) IG3)) x"
      using ig_combine_assoc
      by metis
    show "DefaultValue (f2 (ig_combine IG1 IG2)) x = DefaultValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) x"
      using imod1_imod12 imod1_imod123
      by simp
  qed
  assume "c \<in> Constant (Tm (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)))"
  then have "c \<in> Constant (tmod_combine (Tm (f1 (ig_combine IG1 IG2))) (Tm (f2 (ig_combine IG1 IG2))))"
    unfolding imod_combine_mapping_def
    by simp
  then have "c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))) \<union> Constant (Tm (f2 (ig_combine IG1 IG2)))"
    unfolding tmod_combine_def
    by simp
  then have "c \<in> {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)} \<union> {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)}"
  proof (elim UnE)
    assume "c \<in> Constant (Tm (f1 (ig_combine IG1 IG2)))"
    then have "c \<in> {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)}"
      using imod_combine_mapping_function.func_tm imod_combine_mapping_function.mapping_correct mapping_ig1
      by fastforce
    then show ?thesis
      by simp
  next
    assume "c \<in> Constant (Tm (f2 (ig_combine IG1 IG2)))"
    then have "c \<in> {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)}"
      using imod_combine_mapping_function.func_tm imod_combine_mapping_function.mapping_correct mapping_ig2
      by fastforce
    then show ?thesis
      by simp
  qed
  then have f_cases: "c \<in> {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)} \<inter> {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)} \<or>
    c \<in> {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)} - {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)} \<or>
    c \<in> {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)} - {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)}"
    by blast
  then have "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) c"
  proof (elim disjE)
    assume c_in_both: "c \<in> {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)} \<inter> {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)}"
    show ?thesis
    proof (induct "DefaultValue (f1 (ig_combine IG1 IG2)) c = DefaultValue (f2 (ig_combine IG1 IG2)) c")
      case True
      then have "DefaultValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) c = DefaultValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) c"
        using c_in_both f1_defaultvalue_altdef f2_defaultvalue_altdef
        by simp
      then have "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) c = DefaultValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) c"
        unfolding imod_combine_default_value_mapping_def
        using c_in_both constant_imod2
        by simp
      then have mapping_def: "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) c = DefaultValue (f1 (ig_combine IG1 IG2)) c"
        using c_in_both f1_defaultvalue_altdef
        by simp
      have "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = DefaultValue (f1 (ig_combine IG1 IG2)) c"
        unfolding imod_combine_default_value_mapping_def
        using True.hyps c_in_both
        by simp
      then show ?case
        using mapping_def
        by simp
    next
      case False
      then have "DefaultValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) c \<noteq> DefaultValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) c"
        using c_in_both f1_defaultvalue_altdef f2_defaultvalue_altdef
        by simp
      then have mapping_def: "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) c = ValueDef.invalid"
        unfolding imod_combine_default_value_mapping_def
        using c_in_both constant_imod1 constant_imod2
        by simp
      have "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = ValueDef.invalid"
        unfolding imod_combine_default_value_mapping_def
        using False.hyps c_in_both
        by simp
      then show ?case
        using mapping_def
        by simp
    qed
  next
    assume c_in_imod1: "c \<in> {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)} - {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)}"
    have "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) c = DefaultValue (f1 (ig_combine (ig_combine IG1 IG2) IG3)) c"
      unfolding imod_combine_default_value_mapping_def
      using c_in_imod1 constant_imod1 constant_imod2
      by auto
    then have mapping_def: "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) c = DefaultValue (f1 (ig_combine IG1 IG2)) c"
      using c_in_imod1 f1_defaultvalue_altdef
      by simp
    have "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = DefaultValue (f1 (ig_combine IG1 IG2)) c"
      unfolding imod_combine_default_value_mapping_def
      using c_in_imod1
      by auto
    then show ?thesis
      using mapping_def
      by simp
  next
    assume c_in_imod2: "c \<in> {c \<in> Constant (Tm (f2 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod2)} - {c \<in> Constant (Tm (f1 (ig_combine IG1 IG2))). c \<in> Constant (Tm Imod1)}"
    have "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) c = DefaultValue (f2 (ig_combine (ig_combine IG1 IG2) IG3)) c"
      unfolding imod_combine_default_value_mapping_def
      using c_in_imod2 constant_imod1 constant_imod2
      by auto
    then have mapping_def: "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3) c = DefaultValue (f2 (ig_combine IG1 IG2)) c"
      using c_in_imod2 f2_defaultvalue_altdef
      by simp
    have "imod_combine_default_value_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2) c = DefaultValue (f2 (ig_combine IG1 IG2)) c"
      unfolding imod_combine_default_value_mapping_def
      using c_in_imod2
      by auto
    then show ?thesis
      using mapping_def
      by simp
  qed
  then show "DefaultValue (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine IG1 IG2)) c = DefaultValue (imod_combine_mapping f1 Imod1 f2 Imod2 (ig_combine (ig_combine IG1 IG2) IG3)) c"
    unfolding imod_combine_mapping_def
    by simp
qed

definition imod_empty_mapping :: "('nt, 'lt, 'id) instance_graph \<Rightarrow> ('o, 't) instance_model" where
  "imod_empty_mapping IG \<equiv> imod_empty"

lemma imod_empty_mapping_function[simp]: "imod_combine_mapping_function imod_empty_mapping ig_empty imod_empty"
  unfolding imod_empty_mapping_def ig_empty_def imod_empty_def
  by (intro imod_combine_mapping_function.intro) (simp_all)

end