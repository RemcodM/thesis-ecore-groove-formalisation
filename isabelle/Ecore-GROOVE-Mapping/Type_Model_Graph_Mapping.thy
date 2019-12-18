theory Type_Model_Graph_Mapping
  imports 
    Main
    Ecore.Type_Model_Combination
    GROOVE.Type_Graph_Combination
begin

section "Merging mapping functions from type models to type graphs"

locale tg_combine_mapping_function =
  fixes f :: "('nt) type_model \<Rightarrow> ('lt) type_graph"
  fixes Tmod :: "('nt) type_model"
  fixes TG :: "('lt) type_graph"
  assumes mapping_correct: "f Tmod = TG"
  assumes subset_nodes: "\<And>TmodX. NT (f Tmod) \<subseteq> NT (f (tmod_combine Tmod TmodX))"
  assumes subset_edges: "\<And>TmodX. ET (f Tmod) \<subseteq> ET (f (tmod_combine Tmod TmodX))"
  assumes subset_inh: "\<And>TmodX. inh (f Tmod) \<subseteq> inh (f (tmod_combine Tmod TmodX))"
  assumes subset_abs: "\<And>TmodX. abs (f Tmod) \<subseteq> abs (f (tmod_combine Tmod TmodX))"
  assumes func_mult: "\<And>TmodX e. e \<in> ET (f Tmod) \<Longrightarrow> mult (f Tmod) e = mult (f (tmod_combine Tmod TmodX)) e"
  assumes subset_contains: "\<And>TmodX. contains (f Tmod) \<subseteq> contains (f (tmod_combine Tmod TmodX))"

definition tg_combine_mapping :: "(('nt) type_model \<Rightarrow> ('lt) type_graph) \<Rightarrow> ('lt) type_graph \<Rightarrow> (('nt) type_model \<Rightarrow> ('lt) type_graph) \<Rightarrow> ('lt) type_graph \<Rightarrow> ('nt) type_model \<Rightarrow> ('lt) type_graph" where
  "tg_combine_mapping f1 TG1 f2 TG2 Tmod \<equiv> \<lparr>
    NT = {n \<in> NT (f1 Tmod). n \<in> NT TG1} \<union> {n \<in> NT (f2 Tmod). n \<in> NT TG2},
    ET = {e \<in> ET (f1 Tmod). e \<in> ET TG1} \<union> {e \<in> ET (f2 Tmod). e \<in> ET TG2},
    inh = ({i \<in> inh (f1 Tmod). i \<in> inh TG1} \<union> {i \<in> inh (f2 Tmod). i \<in> inh TG2})\<^sup>+,
    abs = ({n \<in> abs (f1 Tmod). n \<in> abs TG1} - {n \<in> NT (f2 Tmod). n \<in> NT TG2}) \<union> ({n \<in> abs (f2 Tmod). n \<in> abs TG2} - {n \<in> NT (f1 Tmod). n \<in> NT TG1}) \<union> ({n \<in> abs (f1 Tmod). n \<in> abs TG1} \<inter> {n \<in> abs (f2 Tmod). n \<in> abs TG2}),
    mult = tg_combine_mult {e \<in> ET (f1 Tmod). e \<in> ET TG1} (mult (f1 Tmod)) {e \<in> ET (f2 Tmod). e \<in> ET TG2} (mult (f2 Tmod)),
    contains = {e \<in> contains (f1 Tmod). e \<in> contains TG1} \<union> {e \<in> contains (f2 Tmod). e \<in> contains TG2}
  \<rparr>"

lemma tg_combine_mapping_correct:
  assumes mapping_tmod1: "tg_combine_mapping_function f1 Tmod1 TG1"
  assumes mapping_tmod2: "tg_combine_mapping_function f2 Tmod2 TG2"
  shows "tg_combine_mapping (f1) TG1 (f2) TG2 (tmod_combine Tmod1 Tmod2) = tg_combine TG1 TG2"
  unfolding tg_combine_mapping_def tg_combine_def
proof
  have nodes_tg1: "{n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1} = NT TG1"
  proof
    show "{n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1} \<subseteq> NT TG1"
      by blast
  next
    show "NT TG1 \<subseteq> {n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1}"
      using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_nodes
      by blast
  qed
  have nodes_tg2: "{n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2} = NT TG2"
  proof
    show "{n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2} \<subseteq> NT TG2"
      by blast
  next
    have "NT TG2 \<subseteq> {n \<in> NT (f2 (tmod_combine Tmod2 Tmod1)). n \<in> NT TG2}"
      using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_nodes
      by blast
    then show "NT TG2 \<subseteq> {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2}"
      using tmod_combine_commute
      by metis
  qed
  have edges_tg1: "{e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} = ET TG1"
  proof
    show "{e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} \<subseteq> ET TG1"
      by blast
  next
    show "ET TG1 \<subseteq> {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1}"
      using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_edges
      by blast
  qed
  have edges_tg2: "{e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2} = ET TG2"
  proof
    show "{e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2} \<subseteq> ET TG2"
      by blast
  next
    have "ET TG2 \<subseteq> {e \<in> ET (f2 (tmod_combine Tmod2 Tmod1)). e \<in> ET TG2}"
      using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_edges
      by blast
    then show "ET TG2 \<subseteq> {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2}"
      using tmod_combine_commute
      by metis
  qed
  show "{n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1} \<union> {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2} = NT TG1 \<union> NT TG2 \<and>
    {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} \<union> {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2} = ET TG1 \<union> ET TG2 \<and>
    ({i \<in> inh (f1 (tmod_combine Tmod1 Tmod2)). i \<in> inh TG1} \<union> {i \<in> inh (f2 (tmod_combine Tmod1 Tmod2)). i \<in> inh TG2})\<^sup>+ = (inh TG1 \<union> inh TG2)\<^sup>+ \<and>
    {n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1} - {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2} \<union> 
      ({n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2} - {n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1}) \<union> 
      {n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1} \<inter> {n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2} = 
      abs TG1 - NT TG2 \<union> (abs TG2 - NT TG1) \<union> abs TG1 \<inter> abs TG2 \<and>
    tg_combine_mult {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} (mult (f1 (tmod_combine Tmod1 Tmod2))) {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2} (mult (f2 (tmod_combine Tmod1 Tmod2))) = 
      tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2) \<and> 
    {e \<in> contains (f1 (tmod_combine Tmod1 Tmod2)). e \<in> contains TG1} \<union> {e \<in> contains (f2 (tmod_combine Tmod1 Tmod2)). e \<in> contains TG2} = contains TG1 \<union> contains TG2 \<and> 
    () = ()"
  proof (intro conjI)
    show "{n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1} \<union> {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2} = NT TG1 \<union> NT TG2"
      by (simp add: nodes_tg1 nodes_tg2)
  next
    show "{e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} \<union> {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2} = ET TG1 \<union> ET TG2"
      by (simp add: edges_tg1 edges_tg2)
  next
    have inh_tg1: "{i \<in> inh (f1 (tmod_combine Tmod1 Tmod2)). i \<in> inh TG1} = inh TG1"
    proof
      show "{i \<in> inh (f1 (tmod_combine Tmod1 Tmod2)). i \<in> inh TG1} \<subseteq> inh TG1"
        by blast
    next
      show "inh TG1 \<subseteq> {i \<in> inh (f1 (tmod_combine Tmod1 Tmod2)). i \<in> inh TG1}"
        using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_inh
        by blast
    qed
    have inh_tg2: "{i \<in> inh (f2 (tmod_combine Tmod1 Tmod2)). i \<in> inh TG2} = inh TG2"
    proof
      show "{i \<in> inh (f2 (tmod_combine Tmod1 Tmod2)). i \<in> inh TG2} \<subseteq> inh TG2"
        by blast
    next
      have "inh TG2 \<subseteq> {i \<in> inh (f2 (tmod_combine Tmod2 Tmod1)). i \<in> inh TG2}"
        using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_inh
        by blast
      then show "inh TG2 \<subseteq> {i \<in> inh (f2 (tmod_combine Tmod1 Tmod2)). i \<in> inh TG2}"
        using tmod_combine_commute
        by metis
    qed
    show "({i \<in> inh (f1 (tmod_combine Tmod1 Tmod2)). i \<in> inh TG1} \<union> {i \<in> inh (f2 (tmod_combine Tmod1 Tmod2)). i \<in> inh TG2})\<^sup>+ = (inh TG1 \<union> inh TG2)\<^sup>+"
      by (simp add: inh_tg1 inh_tg2)
  next
    have abs_tg1: "{i \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). i \<in> abs TG1} = abs TG1"
    proof
      show "{i \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). i \<in> abs TG1} \<subseteq> abs TG1"
        by blast
    next
      show "abs TG1 \<subseteq> {i \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). i \<in> abs TG1}"
        using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_abs
        by blast
    qed
    have abs_tg2: "{i \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). i \<in> abs TG2} = abs TG2"
    proof
      show "{i \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). i \<in> abs TG2} \<subseteq> abs TG2"
        by blast
    next
      have "abs TG2 \<subseteq> {i \<in> abs (f2 (tmod_combine Tmod2 Tmod1)). i \<in> abs TG2}"
        using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_abs
        by blast
      then show "abs TG2 \<subseteq> {i \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). i \<in> abs TG2}"
        using tmod_combine_commute
        by metis
    qed
    show "{n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1} - {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2} \<union> 
      ({n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2} - {n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1}) \<union>
      {n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1} \<inter> {n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2} =
      abs TG1 - NT TG2 \<union> (abs TG2 - NT TG1) \<union> abs TG1 \<inter> abs TG2"
      by (simp add: abs_tg1 abs_tg2 nodes_tg1 nodes_tg2)
  next
    show "tg_combine_mult {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} (mult (f1 (tmod_combine Tmod1 Tmod2))) {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2} (mult (f2 (tmod_combine Tmod1 Tmod2))) = 
      tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2)"
    proof
      fix e
      have "e \<in> ET TG1 \<inter> ET TG2 \<or> e \<in> ET TG1 - ET TG2 \<or> e \<in> ET TG2 - ET TG1 \<or> e \<notin> ET TG1 \<union> ET TG2"
        by blast
      then have "tg_combine_mult (ET TG1) (mult (f1 (tmod_combine Tmod1 Tmod2))) (ET TG2) (mult (f2 (tmod_combine Tmod1 Tmod2))) e = tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2) e"
      proof (elim disjE)
        assume x_in_both: "e \<in> ET TG1 \<inter> ET TG2"
        have tg1_mult_def: "mult (f1 (tmod_combine Tmod1 Tmod2)) e = mult (f1 Tmod1) e"
          using Int_iff mapping_tmod1 tg_combine_mapping_function.func_mult tg_combine_mapping_function.mapping_correct x_in_both
          by metis
        have "mult (f2 (tmod_combine Tmod2 Tmod1)) e = mult (f2 Tmod2) e"
          using Int_iff mapping_tmod2 tg_combine_mapping_function.func_mult tg_combine_mapping_function.mapping_correct x_in_both
          by metis
        then have tg2_mult_def: "mult (f2 (tmod_combine Tmod1 Tmod2)) e = mult (f2 Tmod2) e"
          using tmod_combine_commute
          by metis
        have "tg_combine_mult (ET TG1) (mult (f1 (tmod_combine Tmod1 Tmod2))) (ET TG2) (mult (f2 (tmod_combine Tmod1 Tmod2))) e = 
          mult_pair_intersect (mult (f1 (tmod_combine Tmod1 Tmod2)) e) (mult (f2 (tmod_combine Tmod1 Tmod2)) e)"
          unfolding tg_combine_mult_def
          using x_in_both
          by simp
        then have merge_mult_def: "tg_combine_mult (ET TG1) (mult (f1 (tmod_combine Tmod1 Tmod2))) (ET TG2) (mult (f2 (tmod_combine Tmod1 Tmod2))) e = 
          mult_pair_intersect (mult (f1 Tmod1) e) (mult (f2 Tmod2) e)"
          using tg1_mult_def tg2_mult_def
          by simp
        have "tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2) e = mult_pair_intersect (mult (f1 Tmod1) e) (mult (f2 Tmod2) e)"
          unfolding tg_combine_mult_def
          using x_in_both mapping_tmod1 mapping_tmod2 tg_combine_mapping_function.mapping_correct
          by metis
        then show ?thesis
          using merge_mult_def
          by simp
      next
        assume x_in_tg1: "e \<in> ET TG1 - ET TG2"
        then have "mult (f1 Tmod1) e = mult (f1 (tmod_combine Tmod1 Tmod2)) e"
          using mapping_tmod1 tg_combine_mapping_function.func_mult tg_combine_mapping_function.mapping_correct
          by blast
        then show ?thesis
          unfolding tg_combine_mult_def
          using x_in_tg1 mapping_tmod1 tg_combine_mapping_function.mapping_correct
          by fastforce
      next
        assume x_in_tg2: "e \<in> ET TG2 - ET TG1"
        then have "mult (f2 Tmod2) e = mult (f2 (tmod_combine Tmod2 Tmod1)) e"
          using mapping_tmod2 tg_combine_mapping_function.func_mult tg_combine_mapping_function.mapping_correct
          by blast
        then have "mult (f2 Tmod2) e = mult (f2 (tmod_combine Tmod1 Tmod2)) e"
          using tmod_combine_commute
          by metis
        then show ?thesis
          unfolding tg_combine_mult_def
          using x_in_tg2 mapping_tmod2 tg_combine_mapping_function.mapping_correct
          by fastforce
      next
        assume "e \<notin> ET TG1 \<union> ET TG2"
        then show ?thesis
          unfolding tg_combine_mult_def
          by simp
      qed
      then show "tg_combine_mult {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} (mult (f1 (tmod_combine Tmod1 Tmod2))) {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2} (mult (f2 (tmod_combine Tmod1 Tmod2))) e = 
        tg_combine_mult (ET TG1) (mult TG1) (ET TG2) (mult TG2) e"
        by (simp add: edges_tg1 edges_tg2)
    qed
  next
    have contains_tg1: "{i \<in> contains (f1 (tmod_combine Tmod1 Tmod2)). i \<in> contains TG1} = contains TG1"
    proof
      show "{i \<in> contains (f1 (tmod_combine Tmod1 Tmod2)). i \<in> contains TG1} \<subseteq> contains TG1"
        by blast
    next
      show "contains TG1 \<subseteq> {i \<in> contains (f1 (tmod_combine Tmod1 Tmod2)). i \<in> contains TG1}"
        using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_contains
        by blast
    qed
    have contains_tg2: "{i \<in> contains (f2 (tmod_combine Tmod1 Tmod2)). i \<in> contains TG2} = contains TG2"
    proof
      show "{i \<in> contains (f2 (tmod_combine Tmod1 Tmod2)). i \<in> contains TG2} \<subseteq> contains TG2"
        by blast
    next
      have "contains TG2 \<subseteq> {i \<in> contains (f2 (tmod_combine Tmod2 Tmod1)). i \<in> contains TG2}"
        using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_contains
        by blast
      then show "contains TG2 \<subseteq> {i \<in> contains (f2 (tmod_combine Tmod1 Tmod2)). i \<in> contains TG2}"
        using tmod_combine_commute
        by metis
    qed
    show "{e \<in> contains (f1 (tmod_combine Tmod1 Tmod2)). e \<in> contains TG1} \<union> {e \<in> contains (f2 (tmod_combine Tmod1 Tmod2)). e \<in> contains TG2} = contains TG1 \<union> contains TG2"
      by (simp add: contains_tg1 contains_tg2)
  qed (simp)
qed

lemma tg_combine_mapping_function_correct:
  assumes mapping_tmod1: "tg_combine_mapping_function f1 Tmod1 TG1"
  assumes mapping_tmod2: "tg_combine_mapping_function f2 Tmod2 TG2"
  shows "tg_combine_mapping_function (tg_combine_mapping (f1) TG1 (f2) TG2) (tmod_combine Tmod1 Tmod2) (tg_combine TG1 TG2)"
proof (intro tg_combine_mapping_function.intro)
  show "tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2) = tg_combine TG1 TG2"
    using assms tg_combine_mapping_correct
    by blast
next
  fix Tmod3
  show "NT (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2)) \<subseteq> NT (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))"
  proof
    fix x
    assume "x \<in> NT (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2))"
    then have "x \<in> {n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1} \<union> {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2}"
      unfolding tg_combine_mapping_def
      by simp
    then have "x \<in> {n \<in> NT (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG1} \<union> {n \<in> NT (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG2}"
    proof (elim UnE)
      assume "x \<in> {n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1}"
      then have "x \<in> NT TG1"
        by blast
      then have "x \<in> {n \<in> NT (f1 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))). n \<in> NT TG1}"
        using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_nodes
        by blast
      then have "x \<in> {n \<in> NT (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG1}"
        by (simp add: tmod_combine_assoc)
      then show ?thesis
        by simp
    next
      assume "x \<in> {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2}"
      then have "x \<in> NT TG2"
        by blast
      then have "x \<in> {n \<in> NT (f2 (tmod_combine Tmod2 (tmod_combine Tmod1 Tmod3))). n \<in> NT TG2}"
        using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_nodes
        by blast
      then have "x \<in> {n \<in> NT (f2 (tmod_combine (tmod_combine Tmod2 Tmod1) Tmod3)). n \<in> NT TG2}"
        by (simp add: tmod_combine_assoc)
      then have "x \<in> {n \<in> NT (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG2}"
        by (simp add: tmod_combine_commute)
      then show ?thesis
        by simp
    qed
    then show "x \<in> NT (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))"
      unfolding tg_combine_mapping_def
      by simp
  qed
next
  fix Tmod3
  show "ET (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2)) \<subseteq> ET (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))"
  proof
    fix x
    assume "x \<in> ET (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2))"
    then have "x \<in> {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} \<union> {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2}"
      unfolding tg_combine_mapping_def
      by simp
    then have "x \<in> {e \<in> ET (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG1} \<union> {e \<in> ET (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG2}"
    proof (elim UnE)
      assume "x \<in> {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1}"
      then have "x \<in> ET TG1"
        by blast
      then have "x \<in> {e \<in> ET (f1 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))). e \<in> ET TG1}"
        using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_edges
        by blast
      then have "x \<in> {e \<in> ET (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG1}"
        by (simp add: tmod_combine_assoc)
      then show ?thesis
        by simp
    next
      assume "x \<in> {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2}"
      then have "x \<in> ET TG2"
        by blast
      then have "x \<in> {e \<in> ET (f2 (tmod_combine Tmod2 (tmod_combine Tmod1 Tmod3))). e \<in> ET TG2}"
        using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_edges
        by blast
      then have "x \<in> {e \<in> ET (f2 (tmod_combine (tmod_combine Tmod2 Tmod1) Tmod3)). e \<in> ET TG2}"
        by (simp add: tmod_combine_assoc)
      then have "x \<in> {e \<in> ET (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG2}"
        by (simp add: tmod_combine_commute)
      then show ?thesis
        by simp
    qed
    then show "x \<in> ET (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))"
      unfolding tg_combine_mapping_def
      by simp
  qed
next
  fix Tmod3
  show "inh (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2)) \<subseteq> inh (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))"
  proof
    fix x
    have f1_inh_altdef: "{e \<in> inh (f1 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG1} = {e \<in> inh (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG1}"
    proof
      show "{e \<in> inh (f1 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG1} \<subseteq> {e \<in> inh (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG1}"
      proof
        fix y
        assume "y \<in> {e \<in> inh (f1 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG1}"
        then have "y \<in> inh TG1"
          by blast
        then have "y \<in> {e \<in> inh (f1 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))). e \<in> inh TG1}"
          using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_inh
          by blast
        then show "y \<in> {e \<in> inh (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG1}"
          by (simp add: tmod_combine_assoc)
      qed
    next
      show "{e \<in> inh (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG1} \<subseteq> {e \<in> inh (f1 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG1}"
      proof
        fix y
        assume "y \<in> {e \<in> inh (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG1}"
        then have "y \<in> inh TG1"
          by blast
        then show "y \<in> {e \<in> inh (f1 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG1}"
          using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_inh
          by blast
      qed
    qed
    have f2_inh_altdef: "{e \<in> inh (f2 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG2} = {e \<in> inh (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG2}"
    proof
      show "{e \<in> inh (f2 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG2} \<subseteq> {e \<in> inh (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG2}"
      proof
        fix y
        assume "y \<in> {e \<in> inh (f2 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG2}"
        then have "y \<in> inh TG2"
          by blast
        then have "y \<in> {e \<in> inh (f2 (tmod_combine Tmod2 (tmod_combine Tmod1 Tmod3))). e \<in> inh TG2}"
          using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_inh
          by blast
        then have "y \<in> {e \<in> inh (f2 (tmod_combine (tmod_combine Tmod2 Tmod1) Tmod3)). e \<in> inh TG2}"
          by (simp add: tmod_combine_assoc)
        then show "y \<in> {e \<in> inh (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG2}"
          by (simp add: tmod_combine_commute)
      qed
    next
      show "{e \<in> inh (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG2} \<subseteq> {e \<in> inh (f2 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG2}"
      proof
        fix y
        assume "y \<in> {e \<in> inh (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG2}"
        then have "y \<in> inh TG2"
          by blast
        then have "y \<in> {e \<in> inh (f2 (tmod_combine Tmod2 Tmod1)). e \<in> inh TG2}"
          using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_inh
          by blast
        then show "y \<in> {e \<in> inh (f2 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG2}"
          by (simp add: tmod_combine_commute)
      qed
    qed
    assume "x \<in> inh (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2))"
    then have "x \<in> ({e \<in> inh (f1 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG1} \<union> {e \<in> inh (f2 (tmod_combine Tmod1 Tmod2)). e \<in> inh TG2})\<^sup>+"
      unfolding tg_combine_mapping_def
      by simp
    then have "x \<in> ({e \<in> inh (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG1} \<union> 
      {e \<in> inh (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> inh TG2})\<^sup>+"
      by (simp add: f1_inh_altdef f2_inh_altdef)
    then show "x \<in> inh (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))"
      unfolding tg_combine_mapping_def
      by simp
  qed
next
  fix Tmod3
  show "abs (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2)) \<subseteq> abs (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))"
  proof
    fix x
    have f1_n_altdef: "{n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1} = {n \<in> NT (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG1}"
    proof
      show "{n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1} \<subseteq> {n \<in> NT (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG1}"
      proof
        fix y
        assume "y \<in> {n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1}"
        then have "y \<in> NT TG1"
          by blast
        then have "y \<in> {n \<in> NT (f1 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))). n \<in> NT TG1}"
          using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_nodes
          by blast
        then show "y \<in> {n \<in> NT (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG1}"
          by (simp add: tmod_combine_assoc)
      qed
    next
      show "{n \<in> NT (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG1} \<subseteq> {n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1}"
      proof
        fix y
        assume "y \<in> {n \<in> NT (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG1}"
        then have "y \<in> NT TG1"
          by blast
        then show "y \<in> {n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1}"
          using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_nodes
          by blast
      qed
    qed
    have f1_abs_altdef: "{n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1} = {n \<in> abs (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG1}"
    proof
      show "{n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1} \<subseteq> {n \<in> abs (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG1}"
      proof
        fix y
        assume "y \<in> {n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1}"
        then have "y \<in> abs TG1"
          by blast
        then have "y \<in> {n \<in> abs (f1 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))). n \<in> abs TG1}"
          using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_abs
          by blast
        then show "y \<in> {n \<in> abs (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG1}"
          by (simp add: tmod_combine_assoc)
      qed
    next
      show "{n \<in> abs (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG1} \<subseteq> {n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1}"
      proof
        fix y
        assume "y \<in> {n \<in> abs (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG1}"
        then have "y \<in> abs TG1"
          by blast
        then show "y \<in> {n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1}"
          using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_abs
          by blast
      qed
    qed
    have f2_n_altdef: "{n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2} = {n \<in> NT (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG2}"
    proof
      show "{n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2} \<subseteq> {n \<in> NT (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG2}"
      proof
        fix y
        assume "y \<in> {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2}"
        then have "y \<in> NT TG2"
          by blast
        then have "y \<in> {n \<in> NT (f2 (tmod_combine Tmod2 (tmod_combine Tmod1 Tmod3))). n \<in> NT TG2}"
          using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_nodes
          by blast
        then have "y \<in> {n \<in> NT (f2 (tmod_combine (tmod_combine Tmod2 Tmod1) Tmod3)). n \<in> NT TG2}"
          by (simp add: tmod_combine_assoc)
        then show "y \<in> {n \<in> NT (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG2}"
          by (simp add: tmod_combine_commute)
      qed
    next
      show "{n \<in> NT (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG2} \<subseteq> {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2}"
      proof
        fix y
        assume "y \<in> {n \<in> NT (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG2}"
        then have "y \<in> NT TG2"
          by blast
        then have "y \<in> {n \<in> NT (f2 (tmod_combine Tmod2 Tmod1)). n \<in> NT TG2}"
          using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_nodes
          by blast
        then show "y \<in> {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2}"
          by (simp add: tmod_combine_commute)
      qed
    qed
    have f2_abs_altdef: "{n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2} = {n \<in> abs (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG2}"
    proof
      show "{n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2} \<subseteq> {n \<in> abs (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG2}"
      proof
        fix y
        assume "y \<in> {n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2}"
        then have "y \<in> abs TG2"
          by blast
        then have "y \<in> {n \<in> abs (f2 (tmod_combine Tmod2 (tmod_combine Tmod1 Tmod3))). n \<in> abs TG2}"
          using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_abs
          by blast
        then have "y \<in> {n \<in> abs (f2 (tmod_combine (tmod_combine Tmod2 Tmod1) Tmod3)). n \<in> abs TG2}"
          by (simp add: tmod_combine_assoc)
        then show "y \<in> {n \<in> abs (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG2}"
          by (simp add: tmod_combine_commute)
      qed
    next
      show "{n \<in> abs (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG2} \<subseteq> {n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2}"
      proof
        fix y
        assume "y \<in> {n \<in> abs (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG2}"
        then have "y \<in> abs TG2"
          by blast
        then have "y \<in> {n \<in> abs (f2 (tmod_combine Tmod2 Tmod1)). n \<in> abs TG2}"
          using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_abs
          by blast
        then show "y \<in> {n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2}"
          by (simp add: tmod_combine_commute)
      qed
    qed
    assume "x \<in> abs (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2))"
    then have "x \<in> ({n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1} - {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2}) \<union> 
        ({n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2} - {n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1}) \<union> 
        ({n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1} \<inter> {n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2})"
      unfolding tg_combine_mapping_def
      by simp
    then have "x \<in> ({n \<in> abs (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG1} - {n \<in> NT (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG2}) \<union> 
        ({n \<in> abs (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG2} - {n \<in> NT (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG1}) \<union> 
        ({n \<in> abs (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG1} \<inter> {n \<in> abs (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG2})"
    proof (elim UnE)
      assume x_in_tg1: "x \<in> {n \<in> type_graph.abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1} - {n \<in> NT (f2 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG2}"
      then have "x \<in> {n \<in> abs (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG1} - {n \<in> NT (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG2}"
        by (simp add: f1_abs_altdef f2_n_altdef)
      then show ?thesis
        by simp
    next
      assume x_in_tg2: "x \<in> {n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2} - {n \<in> NT (f1 (tmod_combine Tmod1 Tmod2)). n \<in> NT TG1}"
      then have "x \<in> {n \<in> abs (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG2} - {n \<in> NT (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> NT TG1}"
        by (simp add: f1_n_altdef f2_abs_altdef)
      then show ?thesis
        by simp
    next
      assume "x \<in> {n \<in> abs (f1 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG1} \<inter> {n \<in> abs (f2 (tmod_combine Tmod1 Tmod2)). n \<in> abs TG2}"
      then have "x \<in> {n \<in> abs (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG1} \<inter> {n \<in> abs (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). n \<in> abs TG2}"
        using f1_abs_altdef f2_abs_altdef
        by blast
      then show ?thesis
        by simp
    qed
    then show "x \<in> abs (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))"
      unfolding tg_combine_mapping_def
      by simp
  qed
next
  fix Tmod3 x
  have f1_e_altdef: "{e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} = {e \<in> ET (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG1}"
  proof
    show "{e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} \<subseteq> {e \<in> ET (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG1}"
    proof
      fix y
      assume "y \<in> {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1}"
      then have "y \<in> ET TG1"
        by blast
      then have "y \<in> {e \<in> ET (f1 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))). e \<in> ET TG1}"
        using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_edges
        by blast
      then show "y \<in> {e \<in> ET (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG1}"
        by (simp add: tmod_combine_assoc)
    qed
  next
    show "{e \<in> ET (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG1} \<subseteq> {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1}"
    proof
      fix y
      assume "y \<in> {e \<in> ET (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG1}"
      then have "y \<in> ET TG1"
        by blast
      then show "y \<in> {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1}"
        using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_edges
        by blast
    qed
  qed
  have f1_mult_altdef: "\<And>y. y \<in> ET TG1 \<Longrightarrow> mult (f1 (tmod_combine Tmod1 Tmod2)) y = mult (f1 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))) y"
  proof-
    fix y
    assume "y \<in> ET TG1"
    then have mult_tmod1_tmod12: "mult (f1 Tmod1) y = mult (f1 (tmod_combine Tmod1 Tmod2)) y"
      using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.func_mult
      by blast
    assume "y \<in> ET TG1"
    then have mult_tmod1_tmod123: "mult (f1 Tmod1) y = mult (f1 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))) y"
      using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.func_mult
      by blast
    show "mult (f1 (tmod_combine Tmod1 Tmod2)) y = mult (f1 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))) y"
      using mult_tmod1_tmod12 mult_tmod1_tmod123
      by simp
  qed
  have f2_e_altdef: "{e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2} = {e \<in> ET (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG2}"
  proof
    show "{e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2} \<subseteq> {e \<in> ET (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG2}"
    proof
      fix y
      assume "y \<in> {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2}"
      then have "y \<in> ET TG2"
        by blast
      then have "y \<in> {e \<in> ET (f2 (tmod_combine Tmod2 (tmod_combine Tmod1 Tmod3))). e \<in> ET TG2}"
        using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_edges
        by blast
      then have "y \<in> {e \<in> ET (f2 (tmod_combine (tmod_combine Tmod2 Tmod1) Tmod3)). e \<in> ET TG2}"
        by (simp add: tmod_combine_assoc)
      then show "y \<in> {e \<in> ET (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG2}"
        by (simp add: tmod_combine_commute)
    qed
  next
    show "{e \<in> ET (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG2} \<subseteq> {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2}"
    proof
      fix y
      assume "y \<in> {e \<in> ET (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG2}"
      then have "y \<in> ET TG2"
        by blast
      then have "y \<in> {e \<in> ET (f2 (tmod_combine Tmod2 Tmod1)). e \<in> ET TG2}"
        using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_edges
        by blast
      then show "y \<in> {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2}"
        by (simp add: tmod_combine_commute)
    qed
  qed
  have f2_mult_altdef: "\<And>y. y \<in> ET TG2 \<Longrightarrow> mult (f2 (tmod_combine Tmod1 Tmod2)) y = mult (f2 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))) y"
  proof-
    fix y
    assume "y \<in> ET TG2"
    then have "mult (f2 Tmod2) y = mult (f2 (tmod_combine Tmod2 Tmod1)) y"
      using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.func_mult
      by blast
    then have mult_tmod1_tmod12: "mult (f2 Tmod2) y = mult (f2 (tmod_combine Tmod1 Tmod2)) y"
      by (simp add: tmod_combine_commute)
    assume "y \<in> ET TG2"
    then have "mult (f2 Tmod2) y = mult (f2 (tmod_combine Tmod2 (tmod_combine Tmod1 Tmod3))) y"
      using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.func_mult
      by blast
    then have mult_tmod1_tmod123: "mult (f2 Tmod2) y = mult (f2 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))) y"
      using tmod_combine_assoc tmod_combine_commute
      by metis
    show "mult (f2 (tmod_combine Tmod1 Tmod2)) y = mult (f2 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))) y"
      using mult_tmod1_tmod12 mult_tmod1_tmod123
      by simp
  qed
  assume "x \<in> ET (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2))"
  then have "x \<in> {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} \<union> {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2}"
    unfolding tg_combine_mapping_def
    by simp
  then have "x \<in> ET TG1 \<union> ET TG2"
    by blast
  then have "tg_combine_mult {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} (mult (f1 (tmod_combine Tmod1 Tmod2))) {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2} (mult (f2 (tmod_combine Tmod1 Tmod2))) x = 
    tg_combine_mult {e \<in> ET (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG1} (mult (f1 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3)))) {e \<in> ET (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG2} (mult (f2 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3)))) x"
    unfolding tg_combine_mult_def
    using f1_e_altdef f1_mult_altdef f2_e_altdef f2_mult_altdef
    by simp
  then have "tg_combine_mult {e \<in> ET (f1 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG1} (mult (f1 (tmod_combine Tmod1 Tmod2))) {e \<in> ET (f2 (tmod_combine Tmod1 Tmod2)). e \<in> ET TG2} (mult (f2 (tmod_combine Tmod1 Tmod2))) x = 
    tg_combine_mult {e \<in> ET (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG1} (mult (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))) {e \<in> ET (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> ET TG2} (mult (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))) x"
    by (simp add: tmod_combine_assoc)
  then show "mult (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2)) x = 
    mult (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)) x"
    unfolding tg_combine_mapping_def
    by simp
next
  fix Tmod3
  show "contains (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2)) \<subseteq> contains (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))"
  proof
    fix x
    assume "x \<in> contains (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine Tmod1 Tmod2))"
    then have "x \<in> {e \<in> contains (f1 (tmod_combine Tmod1 Tmod2)). e \<in> contains TG1} \<union> {e \<in> contains (f2 (tmod_combine Tmod1 Tmod2)). e \<in> contains TG2}"
      unfolding tg_combine_mapping_def
      by simp
    then have "x \<in> {e \<in> contains (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> contains TG1} \<union> {e \<in> contains (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> contains TG2}"
    proof (elim UnE)
      assume "x \<in> {e \<in> contains (f1 (tmod_combine Tmod1 Tmod2)). e \<in> contains TG1}"
      then have "x \<in> contains TG1"
        by blast
      then have "x \<in> {e \<in> contains (f1 (tmod_combine Tmod1 (tmod_combine Tmod2 Tmod3))). e \<in> contains TG1}"
        using mapping_tmod1 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_contains
        by blast
      then have "x \<in> {e \<in> contains (f1 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> contains TG1}"
        by (simp add: tmod_combine_assoc)
      then show ?thesis
        by simp
    next
      assume "x \<in> {e \<in> contains (f2 (tmod_combine Tmod1 Tmod2)). e \<in> contains TG2}"
      then have "x \<in> contains TG2"
        by blast
      then have "x \<in> {e \<in> contains (f2 (tmod_combine Tmod2 (tmod_combine Tmod1 Tmod3))). e \<in> contains TG2}"
        using mapping_tmod2 tg_combine_mapping_function.mapping_correct tg_combine_mapping_function.subset_contains
        by blast
      then have "x \<in> {e \<in> contains (f2 (tmod_combine (tmod_combine Tmod2 Tmod1) Tmod3)). e \<in> contains TG2}"
        by (simp add: tmod_combine_assoc)
      then have "x \<in> {e \<in> contains (f2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3)). e \<in> contains TG2}"
        by (simp add: tmod_combine_commute)
      then show ?thesis
        by simp
    qed
    then show "x \<in> contains (tg_combine_mapping f1 TG1 f2 TG2 (tmod_combine (tmod_combine Tmod1 Tmod2) Tmod3))"
      unfolding tg_combine_mapping_def
      by simp
  qed
qed

definition tg_empty_mapping :: "'nt type_model \<Rightarrow> 'lt type_graph" where
  "tg_empty_mapping Tmod \<equiv> tg_empty"

lemma tg_empty_mapping_function[simp]: "tg_combine_mapping_function tg_empty_mapping tmod_empty tg_empty"
  unfolding tg_empty_mapping_def tg_empty_def tmod_empty_def
  by (intro tg_combine_mapping_function.intro) (simp_all)



section "Merging mapping functions from type graphs to type models"

locale tmod_combine_mapping_function =
  fixes f :: "('lt) type_graph \<Rightarrow> ('nt) type_model"
  fixes TG :: "('lt) type_graph"
  fixes Tmod :: "('nt) type_model"
  assumes mapping_correct: "f TG = Tmod"
  assumes subset_class: "\<And>TGX. Class (f TG) \<subseteq> Class (f (tg_combine TG TGX))"
  assumes subset_enum: "\<And>TGX. Enum (f TG) \<subseteq> Enum (f (tg_combine TG TGX))"
  assumes subset_userdatatype: "\<And>TGX. UserDataType (f TG) \<subseteq> UserDataType (f (tg_combine TG TGX))"
  assumes subset_field: "\<And>TGX. Field (f TG) \<subseteq> Field (f (tg_combine TG TGX))"
  assumes func_fieldsig: "\<And>TGX s. s \<in> Field (f TG) \<Longrightarrow> FieldSig (f TG) s = FieldSig (f (tg_combine TG TGX)) s"
  assumes subset_enumvalue: "\<And>TGX. EnumValue (f TG) \<subseteq> EnumValue (f (tg_combine TG TGX))"
  assumes subset_inh: "\<And>TGX. Inh (f TG) \<subseteq> Inh (f (tg_combine TG TGX))"
  assumes subset_prop: "\<And>TGX. Prop (f TG) \<subseteq> Prop (f (tg_combine TG TGX))"
  assumes subset_constant: "\<And>TGX. Constant (f TG) \<subseteq> Constant (f (tg_combine TG TGX))"
  assumes func_consttype: "\<And>TGX t. t \<in> Constant (f TG) \<Longrightarrow> ConstType (f TG) t = ConstType (f (tg_combine TG TGX)) t"

definition tmod_combine_fieldsig_mapping :: "(('lt) type_graph \<Rightarrow> ('nt) type_model) \<Rightarrow> ('nt) type_model \<Rightarrow> (('lt) type_graph \<Rightarrow> ('nt) type_model) \<Rightarrow> ('nt) type_model \<Rightarrow> ('lt) type_graph \<Rightarrow> 'nt Id \<times> 'nt \<Rightarrow> 'nt TypeDef \<times> multiplicity" where
  "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 TG f \<equiv> (
    if f \<in> {f \<in> Field (f1 TG). f \<in> Field Tmod1} \<inter> {f \<in> Field (f2 TG). f \<in> Field Tmod2} \<and> fst (FieldSig (f1 TG) f) = fst (FieldSig (f2 TG) f) then
      (fst (FieldSig (f1 TG) f), snd (FieldSig (f1 TG) f) \<sqinter> snd (FieldSig (f2 TG) f))
    else if f \<in> {f \<in> Field (f1 TG). f \<in> Field Tmod1} \<inter> {f \<in> Field (f2 TG). f \<in> Field Tmod2} \<and> fst (FieldSig (f1 TG) f) \<noteq> fst (FieldSig (f2 TG) f) then
      (invalid, \<^emph>..\<^bold>0)
    else if f \<in> {f \<in> Field (f1 TG). f \<in> Field Tmod1} - {f \<in> Field (f2 TG). f \<in> Field Tmod2} then
      FieldSig (f1 TG) f
    else if f \<in> {f \<in> Field (f2 TG). f \<in> Field Tmod2} - {f \<in> Field (f1 TG). f \<in> Field Tmod1} then
      FieldSig (f2 TG) f
    else
      undefined)"

definition tmod_combine_const_type_mapping :: "(('lt) type_graph \<Rightarrow> ('nt) type_model) \<Rightarrow> ('nt) type_model \<Rightarrow> (('lt) type_graph \<Rightarrow> ('nt) type_model) \<Rightarrow> ('nt) type_model \<Rightarrow> ('lt) type_graph \<Rightarrow> 'nt Id \<Rightarrow> 'nt TypeDef" where
  "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 TG c \<equiv> (
    if c \<in> {c \<in> Constant (f1 TG). c \<in> Constant Tmod1} \<inter> {c \<in> Constant (f2 TG). c \<in> Constant Tmod2} \<and> ConstType (f1 TG) c = ConstType (f2 TG) c then
      ConstType (f1 TG) c
    else if c \<in> {c \<in> Constant (f1 TG). c \<in> Constant Tmod1} \<inter> {c \<in> Constant (f2 TG). c \<in> Constant Tmod2} \<and> ConstType (f1 TG) c \<noteq> ConstType (f2 TG) c then
      invalid
    else if c \<in> {c \<in> Constant (f1 TG). c \<in> Constant Tmod1} - {c \<in> Constant (f2 TG). c \<in> Constant Tmod2} then
      ConstType (f1 TG) c
    else if c \<in> {c \<in> Constant (f2 TG). c \<in> Constant Tmod2} - {c \<in> Constant (f1 TG). c \<in> Constant Tmod1} then
      ConstType (f2 TG) c
    else
      undefined)"

inductive_set tmod_combine_prop_mapping :: "(('lt) type_graph \<Rightarrow> ('nt) type_model) \<Rightarrow> ('nt) type_model \<Rightarrow> (('lt) type_graph \<Rightarrow> ('nt) type_model) \<Rightarrow> ('nt) type_model \<Rightarrow> ('lt) type_graph \<Rightarrow> 'nt PropertyDef set"
  for f1 :: "('lt) type_graph \<Rightarrow> ('nt) type_model"
  and Tmod1 :: "'nt type_model"
  and f2 :: "('lt) type_graph \<Rightarrow> ('nt) type_model"
  and Tmod2 :: "'nt type_model"
  and TG :: "'lt type_graph"
  where
    abstract_property_tmod1: "abstract c \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> c \<notin> {c \<in> Class (f2 TG). c \<in> Class Tmod2} \<Longrightarrow> abstract c \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    abstract_property_tmod2: "abstract c \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> c \<notin> {c \<in> Class (f1 TG). c \<in> Class Tmod1} \<Longrightarrow> abstract c \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    abstract_property_both: "abstract c \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> abstract c \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> abstract c \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    containment_property_tmod1: "containment r \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> containment r \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    containment_property_tmod2: "containment r \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> containment r \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    default_value_property_tmod1: "defaultValue f v \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> f \<notin> {f \<in> Field (f2 TG). f \<in> Field Tmod2} \<Longrightarrow> defaultValue f v \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    default_value_property_tmod2: "defaultValue f v \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> f \<notin> {f \<in> Field (f1 TG). f \<in> Field Tmod1} \<Longrightarrow> defaultValue f v \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    default_value_property_both: "defaultValue f v \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> defaultValue f v \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> defaultValue f v \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    identity_property_tmod1: "identity c A \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> c \<notin> {c \<in> Class (f2 TG). c \<in> Class Tmod2} \<Longrightarrow> identity c A \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    identity_property_tmod2: "identity c A \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> c \<notin> {c \<in> Class (f1 TG). c \<in> Class Tmod1} \<Longrightarrow> identity c A \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    identity_property_both: "identity c A \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> identity c A \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> identity c A \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    keyset_property_tmod1: "keyset r A \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> r \<notin> {f \<in> Field (f2 TG). f \<in> Field Tmod2} \<Longrightarrow> keyset r A \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    keyset_property_tmod2: "keyset r A \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> r \<notin> {f \<in> Field (f1 TG). f \<in> Field Tmod1} \<Longrightarrow> keyset r A \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    keyset_property_both: "keyset r A \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> keyset r A \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> keyset r A \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    opposite_property_tmod1: "opposite r1 r2 \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> r1 \<notin> {f \<in> Field (f2 TG). f \<in> Field Tmod2} \<Longrightarrow> r2 \<notin> {f \<in> Field (f2 TG). f \<in> Field Tmod2} \<Longrightarrow> opposite r1 r2 \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    opposite_property_tmod2: "opposite r1 r2 \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> r1 \<notin> {f \<in> Field (f1 TG). f \<in> Field Tmod1} \<Longrightarrow> r2 \<notin> {f \<in> Field (f1 TG). f \<in> Field Tmod1} \<Longrightarrow> opposite r1 r2 \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    opposite_property_both: "opposite r1 r2 \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> opposite r1 r2 \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> opposite r1 r2 \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    readonly_property_tmod1: "readonly f \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> f \<notin> {f \<in> Field (f2 TG). f \<in> Field Tmod2} \<Longrightarrow> readonly f \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    readonly_property_tmod2: "readonly f \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> f \<notin> {f \<in> Field (f1 TG). f \<in> Field Tmod1} \<Longrightarrow> readonly f \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG" |
    readonly_property_both: "readonly f \<in> {p \<in> Prop (f1 TG). p \<in> Prop Tmod1} \<Longrightarrow> readonly f \<in> {p \<in> Prop (f2 TG). p \<in> Prop Tmod2} \<Longrightarrow> readonly f \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG"

definition tmod_combine_mapping :: "(('lt) type_graph \<Rightarrow> ('nt) type_model) \<Rightarrow> ('nt) type_model \<Rightarrow> (('lt) type_graph \<Rightarrow> ('nt) type_model) \<Rightarrow> ('nt) type_model \<Rightarrow> ('lt) type_graph \<Rightarrow> ('nt) type_model" where
  "tmod_combine_mapping f1 Tmod1 f2 Tmod2 TG \<equiv> \<lparr>
    Class = {c \<in> Class (f1 TG). c \<in> Class Tmod1} \<union> {c \<in> Class (f2 TG). c \<in> Class Tmod2},
    Enum = {e \<in> Enum (f1 TG). e \<in> Enum Tmod1} \<union> {e \<in> Enum (f2 TG). e \<in> Enum Tmod2},
    UserDataType = {u \<in> UserDataType (f1 TG). u \<in> UserDataType Tmod1} \<union> {u \<in> UserDataType (f2 TG). u \<in> UserDataType Tmod2},
    Field = {f \<in> Field (f1 TG). f \<in> Field Tmod1} \<union> {f \<in> Field (f2 TG). f \<in> Field Tmod2},
    FieldSig = tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 TG,
    EnumValue = {ev \<in> EnumValue (f1 TG). ev \<in> EnumValue Tmod1} \<union> {ev \<in> EnumValue (f2 TG). ev \<in> EnumValue Tmod2},
    Inh = {i \<in> Inh (f1 TG). i \<in> Inh Tmod1} \<union> {i \<in> Inh (f2 TG). i \<in> Inh Tmod2},
    Prop = tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 TG,
    Constant = {c \<in> Constant (f1 TG). c \<in> Constant Tmod1} \<union> {c \<in> Constant (f2 TG). c \<in> Constant Tmod2},
    ConstType = tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 TG
  \<rparr>"

lemma tmod_combine_mapping_correct:
  assumes mapping_tg1: "tmod_combine_mapping_function f1 TG1 Tmod1"
  assumes mapping_tg2: "tmod_combine_mapping_function f2 TG2 Tmod2"
  shows "tmod_combine_mapping (f1) Tmod1 (f2) Tmod2 (tg_combine TG1 TG2) = tmod_combine Tmod1 Tmod2"
  unfolding tmod_combine_mapping_def tmod_combine_def
proof
  have class_tmod1: "{c \<in> Class (f1 (tg_combine TG1 TG2)). c \<in> Class Tmod1} = Class Tmod1"
  proof
    show "{c \<in> Class (f1 (tg_combine TG1 TG2)). c \<in> Class Tmod1} \<subseteq> Class Tmod1"
      by blast
  next
    show "Class Tmod1 \<subseteq> {c \<in> Class (f1 (tg_combine TG1 TG2)). c \<in> Class Tmod1}"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_class
      by blast
  qed
  have class_tmod2: "{c \<in> Class (f2 (tg_combine TG1 TG2)). c \<in> Class Tmod2} = Class Tmod2"
  proof
    show "{c \<in> Class (f2 (tg_combine TG1 TG2)). c \<in> Class Tmod2} \<subseteq> Class Tmod2"
      by blast
  next
    have "Class Tmod2 \<subseteq> {c \<in> Class (f2 (tg_combine TG2 TG1)). c \<in> Class Tmod2}"
      using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_class
      by blast
    then show "Class Tmod2 \<subseteq> {c \<in> Class (f2 (tg_combine TG1 TG2)). c \<in> Class Tmod2}"
      by simp
  qed
  have field_tmod1: "{f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} = Field Tmod1"
  proof
    show "{f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} \<subseteq> Field Tmod1"
      by blast
  next
    show "Field Tmod1 \<subseteq> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
      by blast
  qed
  have field_tmod2: "{f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} = Field Tmod2"
  proof
    show "{f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} \<subseteq> Field Tmod2"
      by blast
  next
    have "Field Tmod2 \<subseteq> {f \<in> Field (f2 (tg_combine TG2 TG1)). f \<in> Field Tmod2}"
      using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
      by blast
    then show "Field Tmod2 \<subseteq> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
      by simp
  qed
  have constant_tmod1: "{c \<in> Constant (f1 (tg_combine TG1 TG2)). c \<in> Constant Tmod1} = Constant Tmod1"
  proof
    show "{c \<in> Constant (f1 (tg_combine TG1 TG2)). c \<in> Constant Tmod1} \<subseteq> Constant Tmod1"
      by blast
  next
    show "Constant Tmod1 \<subseteq> {c \<in> Constant (f1 (tg_combine TG1 TG2)). c \<in> Constant Tmod1}"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_constant
      by blast
  qed
  have constant_tmod2: "{c \<in> Constant (f2 (tg_combine TG1 TG2)). c \<in> Constant Tmod2} = Constant Tmod2"
  proof
    show "{c \<in> Constant (f2 (tg_combine TG1 TG2)). c \<in> Constant Tmod2} \<subseteq> Constant Tmod2"
      by blast
  next
    have "Constant Tmod2 \<subseteq> {c \<in> Constant (f2 (tg_combine TG2 TG1)). c \<in> Constant Tmod2}"
      using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_constant
      by blast
    then show "Constant Tmod2 \<subseteq> {c \<in> Constant (f2 (tg_combine TG1 TG2)). c \<in> Constant Tmod2}"
      by simp
  qed
  show "{c \<in> Class (f1 (tg_combine TG1 TG2)). c \<in> Class Tmod1} \<union> {c \<in> Class (f2 (tg_combine TG1 TG2)). c \<in> Class Tmod2} = Class Tmod1 \<union> Class Tmod2 \<and>
    {e \<in> Enum (f1 (tg_combine TG1 TG2)). e \<in> Enum Tmod1} \<union> {e \<in> Enum (f2 (tg_combine TG1 TG2)). e \<in> Enum Tmod2} = Enum Tmod1 \<union> Enum Tmod2 \<and>
    {u \<in> UserDataType (f1 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod1} \<union> {u \<in> UserDataType (f2 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod2} = UserDataType Tmod1 \<union> UserDataType Tmod2 \<and>
    {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} \<union> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} = Field Tmod1 \<union> Field Tmod2 \<and>
    tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) = tmod_combine_fieldsig Tmod1 Tmod2 \<and>
    {ev \<in> EnumValue (f1 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod1} \<union> {ev \<in> EnumValue (f2 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod2} = EnumValue Tmod1 \<union> EnumValue Tmod2 \<and>
    {i \<in> Inh (f1 (tg_combine TG1 TG2)). i \<in> Inh Tmod1} \<union> {i \<in> Inh (f2 (tg_combine TG1 TG2)). i \<in> Inh Tmod2} = Inh Tmod1 \<union> Inh Tmod2 \<and>
    tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) = tmod_combine_prop Tmod1 Tmod2 \<and>
    {c \<in> Constant (f1 (tg_combine TG1 TG2)). c \<in> Constant Tmod1} \<union> {c \<in> Constant (f2 (tg_combine TG1 TG2)). c \<in> Constant Tmod2} = Constant Tmod1 \<union> Constant Tmod2 \<and>
    tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) = tmod_combine_const_type Tmod1 Tmod2 \<and> 
    () = ()"
  proof (intro conjI)
    show "{c \<in> Class (f1 (tg_combine TG1 TG2)). c \<in> Class Tmod1} \<union> {c \<in> Class (f2 (tg_combine TG1 TG2)). c \<in> Class Tmod2} = Class Tmod1 \<union> Class Tmod2"
      by (simp add: class_tmod1 class_tmod2)
  next
    have enum_tmod1: "{e \<in> Enum (f1 (tg_combine TG1 TG2)). e \<in> Enum Tmod1} = Enum Tmod1"
    proof
      show "{e \<in> Enum (f1 (tg_combine TG1 TG2)). e \<in> Enum Tmod1} \<subseteq> Enum Tmod1"
        by blast
    next
      show "Enum Tmod1 \<subseteq> {e \<in> Enum (f1 (tg_combine TG1 TG2)). e \<in> Enum Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_enum
        by blast
    qed
    have enum_tmod2: "{e \<in> Enum (f2 (tg_combine TG1 TG2)). e \<in> Enum Tmod2} = Enum Tmod2"
    proof
      show "{e \<in> Enum (f2 (tg_combine TG1 TG2)). e \<in> Enum Tmod2} \<subseteq> Enum Tmod2"
        by blast
    next
      have "Enum Tmod2 \<subseteq> {e \<in> Enum (f2 (tg_combine TG2 TG1)). e \<in> Enum Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_enum
        by blast
      then show "Enum Tmod2 \<subseteq> {e \<in> Enum (f2 (tg_combine TG1 TG2)). e \<in> Enum Tmod2}"
        by simp
    qed
    show "{e \<in> Enum (f1 (tg_combine TG1 TG2)). e \<in> Enum Tmod1} \<union> {e \<in> Enum (f2 (tg_combine TG1 TG2)). e \<in> Enum Tmod2} = Enum Tmod1 \<union> Enum Tmod2"
      by (simp add: enum_tmod1 enum_tmod2)
  next
    have userdatatype_tmod1: "{u \<in> UserDataType (f1 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod1} = UserDataType Tmod1"
    proof
      show "{u \<in> UserDataType (f1 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod1} \<subseteq> UserDataType Tmod1"
        by blast
    next
      show "UserDataType Tmod1 \<subseteq> {u \<in> UserDataType (f1 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_userdatatype
        by blast
    qed
    have userdatatype_tmod2: "{u \<in> UserDataType (f2 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod2} = UserDataType Tmod2"
    proof
      show "{u \<in> UserDataType (f2 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod2} \<subseteq> UserDataType Tmod2"
        by blast
    next
      have "UserDataType Tmod2 \<subseteq> {u \<in> UserDataType (f2 (tg_combine TG2 TG1)). u \<in> UserDataType Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_userdatatype
        by blast
      then show "UserDataType Tmod2 \<subseteq> {u \<in> UserDataType (f2 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod2}"
        by simp
    qed
    show "{u \<in> UserDataType (f1 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod1} \<union> {u \<in> UserDataType (f2 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod2} = UserDataType Tmod1 \<union> UserDataType Tmod2"
      by (simp add: userdatatype_tmod1 userdatatype_tmod2)
  next
    show "{f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} \<union> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} = Field Tmod1 \<union> Field Tmod2"
      by (simp add: field_tmod1 field_tmod2)
  next
    show "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) = tmod_combine_fieldsig Tmod1 Tmod2"
    proof
      fix f
      have "f \<in> Field Tmod1 \<inter> Field Tmod2 \<or> f \<in> Field Tmod1 - Field Tmod2 \<or> f \<in> Field Tmod2 - Field Tmod1 \<or> f \<notin> Field Tmod1 \<union> Field Tmod2"
        by blast
      then show "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) f = tmod_combine_fieldsig Tmod1 Tmod2 f"
      proof (elim disjE)
        assume f_in_both: "f \<in> Field Tmod1 \<inter> Field Tmod2"
        then have f_in_both_alt: "f \<in> Field (f1 TG1) \<inter> Field (f2 TG2)"
          using mapping_tg1 mapping_tg2 tmod_combine_mapping_function.mapping_correct
          by blast
        have f_in_merge: "f \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} \<inter> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
          using f_in_both field_tmod1 field_tmod2
          by blast
        have "fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f) \<or> fst (FieldSig Tmod1 f) \<noteq> fst (FieldSig Tmod2 f)"
          by simp
        then show ?thesis
        proof (elim disjE)
          assume "fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)"
          then have combine_def: "tmod_combine_fieldsig Tmod1 Tmod2 f = (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f))"
            unfolding tmod_combine_fieldsig_def
            using f_in_both
            by simp
          assume "fst (FieldSig Tmod1 f) = fst (FieldSig Tmod2 f)"
          then have "fst (FieldSig (f1 TG1) f) = fst (FieldSig (f2 TG2) f)"
            using mapping_tg1 mapping_tg2 tmod_combine_mapping_function.mapping_correct
            by blast
          then have "fst (FieldSig (f1 (tg_combine TG1 TG2)) f) = fst (FieldSig (f2 (tg_combine TG1 TG2)) f)"
            using IntD1 IntD2 f_in_both_alt mapping_tg1 mapping_tg2 tg_combine_commute tmod_combine_mapping_function.func_fieldsig
            by metis
          then have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) f = 
            (fst (FieldSig (f1 (tg_combine TG1 TG2)) f), snd (FieldSig (f1 (tg_combine TG1 TG2)) f) \<sqinter> snd (FieldSig (f2 (tg_combine TG1 TG2)) f))"
            unfolding tmod_combine_fieldsig_mapping_def
            using f_in_merge
            by simp
          then have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) f = 
            (fst (FieldSig (f1 TG1) f), snd (FieldSig (f1 TG1) f) \<sqinter> snd (FieldSig (f2 TG2) f))"
            using IntD1 IntD2 f_in_both_alt mapping_tg1 mapping_tg2 tg_combine_commute tmod_combine_mapping_function.func_fieldsig
            by metis
          then have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) f = 
            (fst (FieldSig Tmod1 f), snd (FieldSig Tmod1 f) \<sqinter> snd (FieldSig Tmod2 f))"
            using mapping_tg1 mapping_tg2 tmod_combine_mapping_function.mapping_correct
            by blast
          then show ?thesis
            using combine_def
            by simp
        next
          assume "fst (FieldSig Tmod1 f) \<noteq> fst (FieldSig Tmod2 f)"
          then have combine_def: "tmod_combine_fieldsig Tmod1 Tmod2 f = (invalid, \<^emph>..\<^bold>0)"
            unfolding tmod_combine_fieldsig_def
            using f_in_both
            by simp
          assume "fst (FieldSig Tmod1 f) \<noteq> fst (FieldSig Tmod2 f)"
          then have "fst (FieldSig (f1 TG1) f) \<noteq> fst (FieldSig (f2 TG2) f)"
            using mapping_tg1 mapping_tg2 tmod_combine_mapping_function.mapping_correct
            by blast
          then have "fst (FieldSig (f1 (tg_combine TG1 TG2)) f) \<noteq> fst (FieldSig (f2 (tg_combine TG1 TG2)) f)"
            using IntD1 IntD2 f_in_both_alt mapping_tg1 mapping_tg2 tg_combine_commute tmod_combine_mapping_function.func_fieldsig
            by metis
          then have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) f = (invalid, \<^emph>..\<^bold>0)"
            unfolding tmod_combine_fieldsig_mapping_def
            using f_in_merge
            by simp
          then show ?thesis
            using combine_def
            by simp
        qed
      next
        assume "f \<in> Field Tmod1 - Field Tmod2"
        then have combine_def: "tmod_combine_fieldsig Tmod1 Tmod2 f = FieldSig Tmod1 f"
          unfolding tmod_combine_fieldsig_def
          by simp
        assume "f \<in> Field Tmod1 - Field Tmod2"
        then have "f \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} - {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
          using field_tmod1
          by blast
        then have mapping_def: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) f = FieldSig (f1 (tg_combine TG1 TG2)) f"
          unfolding tmod_combine_fieldsig_mapping_def
          by auto
        assume "f \<in> Field Tmod1 - Field Tmod2"
        then have "f \<in> Field (f1 TG1)"
          using mapping_tg1 tmod_combine_mapping_function.mapping_correct
          by blast
        then have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) f = FieldSig (f1 TG1) f"
          using mapping_def mapping_tg1 tmod_combine_mapping_function.func_fieldsig
          by metis
        then have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) f = FieldSig Tmod1 f"
          using mapping_tg1 tmod_combine_mapping_function.mapping_correct
          by blast
        then show ?thesis
          using combine_def
          by simp
      next
        assume "f \<in> Field Tmod2 - Field Tmod1"
        then have combine_def: "tmod_combine_fieldsig Tmod1 Tmod2 f = FieldSig Tmod2 f"
          unfolding tmod_combine_fieldsig_def
          by simp
        assume "f \<in> Field Tmod2 - Field Tmod1"
        then have "f \<in> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} - {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
          using field_tmod2
          by blast
        then have mapping_def: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) f = FieldSig (f2 (tg_combine TG1 TG2)) f"
          unfolding tmod_combine_fieldsig_mapping_def
          by auto
        assume "f \<in> Field Tmod2 - Field Tmod1"
        then have "f \<in> Field (f2 TG2)"
          using mapping_tg2 tmod_combine_mapping_function.mapping_correct
          by blast
        then have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) f = FieldSig (f2 TG2) f"
          using mapping_def mapping_tg2 tg_combine_commute tmod_combine_mapping_function.func_fieldsig
          by metis
        then have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) f = FieldSig Tmod2 f"
          using mapping_tg2 tmod_combine_mapping_function.mapping_correct
          by blast
        then show ?thesis
          using combine_def
          by simp
      next
        assume "f \<notin> Field Tmod1 \<union> Field Tmod2"
        then show ?thesis
          unfolding tmod_combine_fieldsig_mapping_def tmod_combine_fieldsig_def
          by simp
      qed
    qed
  next
    have enumvalue_tmod1: "{ev \<in> EnumValue (f1 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod1} = EnumValue Tmod1"
    proof
      show "{ev \<in> EnumValue (f1 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod1} \<subseteq> EnumValue Tmod1"
        by blast
    next
      show "EnumValue Tmod1 \<subseteq> {ev \<in> EnumValue (f1 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_enumvalue
        by blast
    qed
    have enumvalue_tmod2: "{ev \<in> EnumValue (f2 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod2} = EnumValue Tmod2"
    proof
      show "{ev \<in> EnumValue (f2 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod2} \<subseteq> EnumValue Tmod2"
        by blast
    next
      have "EnumValue Tmod2 \<subseteq> {ev \<in> EnumValue (f2 (tg_combine TG2 TG1)). ev \<in> EnumValue Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_enumvalue
        by blast
      then show "EnumValue Tmod2 \<subseteq> {ev \<in> EnumValue (f2 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod2}"
        by simp
    qed
    show "{ev \<in> EnumValue (f1 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod1} \<union> {ev \<in> EnumValue (f2 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod2} = EnumValue Tmod1 \<union> EnumValue Tmod2"
      by (simp add: enumvalue_tmod1 enumvalue_tmod2)
  next
    have inh_tmod1: "{i \<in> Inh (f1 (tg_combine TG1 TG2)). i \<in> Inh Tmod1} = Inh Tmod1"
    proof
      show "{i \<in> Inh (f1 (tg_combine TG1 TG2)). i \<in> Inh Tmod1} \<subseteq> Inh Tmod1"
        by blast
    next
      show "Inh Tmod1 \<subseteq> {i \<in> Inh (f1 (tg_combine TG1 TG2)). i \<in> Inh Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_inh
        by blast
    qed
    have inh_tmod2: "{i \<in> Inh (f2 (tg_combine TG1 TG2)). i \<in> Inh Tmod2} = Inh Tmod2"
    proof
      show "{i \<in> Inh (f2 (tg_combine TG1 TG2)). i \<in> Inh Tmod2} \<subseteq> Inh Tmod2"
        by blast
    next
      have "Inh Tmod2 \<subseteq> {i \<in> Inh (f2 (tg_combine TG2 TG1)). i \<in> Inh Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_inh
        by blast
      then show "Inh Tmod2 \<subseteq> {i \<in> Inh (f2 (tg_combine TG1 TG2)). i \<in> Inh Tmod2}"
        by simp
    qed
    show "{i \<in> Inh (f1 (tg_combine TG1 TG2)). i \<in> Inh Tmod1} \<union> {i \<in> Inh (f2 (tg_combine TG1 TG2)). i \<in> Inh Tmod2} = Inh Tmod1 \<union> Inh Tmod2"
      by (simp add: inh_tmod1 inh_tmod2)
  next
    have prop_tmod1: "{p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1} = Prop Tmod1"
    proof
      show "{p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1} \<subseteq> Prop Tmod1"
        by blast
    next
      show "Prop Tmod1 \<subseteq> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_prop
        by blast
    qed
    have prop_tmod2: "{p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2} = Prop Tmod2"
    proof
      show "{p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2} \<subseteq> Prop Tmod2"
        by blast
    next
      have "Prop Tmod2 \<subseteq> {p \<in> Prop (f2 (tg_combine TG2 TG1)). p \<in> Prop Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_prop
        by blast
      then show "Prop Tmod2 \<subseteq> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
        by simp
    qed
    show "tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) = tmod_combine_prop Tmod1 Tmod2"
    proof
      show "tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) \<subseteq> tmod_combine_prop Tmod1 Tmod2"
      proof
        fix x
        assume "x \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)"
        then show "x \<in> tmod_combine_prop Tmod1 Tmod2"
        proof (induct)
          case (abstract_property_tmod1 c)
          have abstract_prop: "abstract c \<in> Prop Tmod1"
            using abstract_property_tmod1.hyps
            by blast
          have no_class: "c \<notin> Class Tmod2"
            using abstract_property_tmod1.hyps class_tmod2
            by blast
          show ?case
            by (simp add: abstract_prop no_class tmod_combine_prop.abstract_property_tmod1)
        next
          case (abstract_property_tmod2 c)
          have abstract_prop: "abstract c \<in> Prop Tmod2"
            using abstract_property_tmod2.hyps
            by blast
          have no_class: "c \<notin> Class Tmod1"
            using abstract_property_tmod2.hyps class_tmod1
            by blast
          show ?case
            by (simp add: abstract_prop no_class tmod_combine_prop.abstract_property_tmod2)
        next
          case (abstract_property_both c)
          have abstract_prop1: "abstract c \<in> Prop Tmod1"
            using abstract_property_both.hyps
            by blast
          have abstract_prop2: "abstract c \<in> Prop Tmod2"
            using abstract_property_both.hyps
            by blast
          show ?case
            by (simp add: abstract_prop1 abstract_prop2 tmod_combine_prop.abstract_property_both)
        next
          case (containment_property_tmod1 r)
          then have "containment r \<in> Prop Tmod1"
            using containment_property_tmod1.hyps
            by blast
          then show ?case
            by (fact tmod_combine_prop.containment_property_tmod1)
        next
          case (containment_property_tmod2 r)
          then have "containment r \<in> Prop Tmod2"
            using containment_property_tmod2.hyps
            by blast
          then show ?case
            by (fact tmod_combine_prop.containment_property_tmod2)
        next
          case (default_value_property_tmod1 f v)
          have default_value_prop: "defaultValue f v \<in> Prop Tmod1"
            using default_value_property_tmod1.hyps
            by blast
          have no_field: "f \<notin> Field Tmod2"
            using default_value_property_tmod1.hyps field_tmod2
            by blast
          show ?case
            by (simp add: default_value_prop no_field tmod_combine_prop.default_value_property_tmod1)
        next
          case (default_value_property_tmod2 f v)
          have default_value_prop: "defaultValue f v \<in> Prop Tmod2"
            using default_value_property_tmod2.hyps
            by blast
          have no_field: "f \<notin> Field Tmod1"
            using default_value_property_tmod2.hyps field_tmod1
            by blast
          show ?case
            by (simp add: default_value_prop no_field tmod_combine_prop.default_value_property_tmod2)
        next
          case (default_value_property_both f v)
          have default_value_prop1: "defaultValue f v \<in> Prop Tmod1"
            using default_value_property_both.hyps
            by blast
          have default_value_prop2: "defaultValue f v \<in> Prop Tmod2"
            using default_value_property_both.hyps
            by blast
          show ?case
            by (simp add: default_value_prop1 default_value_prop2 tmod_combine_prop.default_value_property_both)
        next
          case (identity_property_tmod1 c A)
          have identity_prop: "identity c A \<in> Prop Tmod1"
            using identity_property_tmod1.hyps
            by blast
          have no_class: "c \<notin> Class Tmod2"
            using identity_property_tmod1.hyps class_tmod2
            by blast
          show ?case
            by (simp add: identity_prop no_class tmod_combine_prop.identity_property_tmod1)
        next
          case (identity_property_tmod2 c A)
          have identity_prop: "identity c A \<in> Prop Tmod2"
            using identity_property_tmod2.hyps
            by blast
          have no_class: "c \<notin> Class Tmod1"
            using identity_property_tmod2.hyps class_tmod1
            by blast
          show ?case
            by (simp add: identity_prop no_class tmod_combine_prop.identity_property_tmod2)
        next
          case (identity_property_both c A)
          have identity_prop1: "identity c A \<in> Prop Tmod1"
            using identity_property_both.hyps
            by blast
          have identity_prop2: "identity c A \<in> Prop Tmod2"
            using identity_property_both.hyps
            by blast
          show ?case
            by (simp add: identity_prop1 identity_prop2 tmod_combine_prop.identity_property_both)
        next
          case (keyset_property_tmod1 r A)
          have keyset_prop: "keyset r A \<in> Prop Tmod1"
            using keyset_property_tmod1.hyps
            by blast
          have no_field: "r \<notin> Field Tmod2"
            using keyset_property_tmod1.hyps field_tmod2
            by blast
          show ?case
            by (simp add: keyset_prop no_field tmod_combine_prop.keyset_property_tmod1)
        next
          case (keyset_property_tmod2 r A)
          have keyset_prop: "keyset r A \<in> Prop Tmod2"
            using keyset_property_tmod2.hyps
            by blast
          have no_field: "r \<notin> Field Tmod1"
            using keyset_property_tmod2.hyps field_tmod1
            by blast
          show ?case
            by (simp add: keyset_prop no_field tmod_combine_prop.keyset_property_tmod2)
        next
          case (keyset_property_both r A)
          have keyset_prop1: "keyset r A \<in> Prop Tmod1"
            using keyset_property_both.hyps
            by blast
          have keyset_prop2: "keyset r A \<in> Prop Tmod2"
            using keyset_property_both.hyps
            by blast
          show ?case
            by (simp add: keyset_prop1 keyset_prop2 tmod_combine_prop.keyset_property_both)
        next
          case (opposite_property_tmod1 r1 r2)
          have opposite_prop: "opposite r1 r2 \<in> Prop Tmod1"
            using opposite_property_tmod1.hyps
            by blast
          have no_field_r1: "r1 \<notin> Field Tmod2"
            using opposite_property_tmod1.hyps field_tmod2
            by blast
          have no_field_r2: "r2 \<notin> Field Tmod2"
            using opposite_property_tmod1.hyps field_tmod2
            by blast
          show ?case
            by (simp add: opposite_prop no_field_r1 no_field_r2 tmod_combine_prop.opposite_property_tmod1)
        next
          case (opposite_property_tmod2 r1 r2)
          have opposite_prop: "opposite r1 r2 \<in> Prop Tmod2"
            using opposite_property_tmod2.hyps
            by blast
          have no_field_r1: "r1 \<notin> Field Tmod1"
            using opposite_property_tmod2.hyps field_tmod1
            by blast
          have no_field_r2: "r2 \<notin> Field Tmod1"
            using opposite_property_tmod2.hyps field_tmod1
            by blast
          show ?case
            by (simp add: opposite_prop no_field_r1 no_field_r2 tmod_combine_prop.opposite_property_tmod2)
        next
          case (opposite_property_both r1 r2)
          have opposite_prop1: "opposite r1 r2 \<in> Prop Tmod1"
            using opposite_property_both.hyps
            by blast
          have opposite_prop2: "opposite r1 r2 \<in> Prop Tmod2"
            using opposite_property_both.hyps
            by blast
          show ?case
            by (simp add: opposite_prop1 opposite_prop2 tmod_combine_prop.opposite_property_both)
        next
          case (readonly_property_tmod1 f)
          have readonly_prop: "readonly f \<in> Prop Tmod1"
            using readonly_property_tmod1.hyps
            by blast
          have no_field: "f \<notin> Field Tmod2"
            using readonly_property_tmod1.hyps field_tmod2
            by blast
          show ?case
            by (simp add: readonly_prop no_field tmod_combine_prop.readonly_property_tmod1)
        next
          case (readonly_property_tmod2 f)
          have readonly_prop: "readonly f \<in> Prop Tmod2"
            using readonly_property_tmod2.hyps
            by blast
          have no_field: "f \<notin> Field Tmod1"
            using readonly_property_tmod2.hyps field_tmod1
            by blast
          show ?case
            by (simp add: readonly_prop no_field tmod_combine_prop.readonly_property_tmod2)
        next
          case (readonly_property_both f)
          have readonly_prop1: "readonly f \<in> Prop Tmod1"
            using readonly_property_both.hyps
            by blast
          have readonly_prop2: "readonly f \<in> Prop Tmod2"
            using readonly_property_both.hyps
            by blast
          show ?case
            by (simp add: readonly_prop1 readonly_prop2 tmod_combine_prop.readonly_property_both)
        qed
      qed
    next
      show "tmod_combine_prop Tmod1 Tmod2 \<subseteq> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)"
      proof
        fix x
        assume "x \<in> tmod_combine_prop Tmod1 Tmod2"
        then show "x \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)"
        proof (induct)
          case (abstract_property_tmod1 c)
          have abstract_prop: "abstract c \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using abstract_property_tmod1.hyps prop_tmod1
            by blast
          have no_class: "c \<notin> {c \<in> Class (f2 (tg_combine TG1 TG2)). c \<in> Class Tmod2}"
            using abstract_property_tmod1.hyps
            by blast
          show ?case
            using abstract_prop no_class tmod_combine_prop_mapping.abstract_property_tmod1
            by blast
        next
          case (abstract_property_tmod2 c)
          have abstract_prop: "abstract c \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using abstract_property_tmod2.hyps prop_tmod2
            by blast
          have no_class: "c \<notin> {c \<in> Class (f1 (tg_combine TG1 TG2)). c \<in> Class Tmod1}"
            using abstract_property_tmod2.hyps
            by blast
          show ?case
            using abstract_prop no_class tmod_combine_prop_mapping.abstract_property_tmod2
            by blast
        next
          case (abstract_property_both c)
          have abstract_prop1: "abstract c \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using abstract_property_both.hyps prop_tmod1
            by blast
          have abstract_prop2: "abstract c \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using abstract_property_both.hyps prop_tmod2
            by blast
          show ?case
            using abstract_prop1 abstract_prop2 tmod_combine_prop_mapping.abstract_property_both
            by blast
        next
          case (containment_property_tmod1 r)
          have "containment r \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using containment_property_tmod1.hyps prop_tmod1
            by blast
          then show ?case
            using tmod_combine_prop_mapping.containment_property_tmod1
            by blast
        next
          case (containment_property_tmod2 r)
          have "containment r \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using containment_property_tmod2.hyps prop_tmod2
            by blast
          then show ?case
            using tmod_combine_prop_mapping.containment_property_tmod2
            by blast
        next
          case (default_value_property_tmod1 f v)
          have default_value_prop: "defaultValue f v \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using default_value_property_tmod1.hyps prop_tmod1
            by blast
          have no_field: "f \<notin> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
            using default_value_property_tmod1.hyps
            by blast
          show ?case
            using default_value_prop no_field tmod_combine_prop_mapping.default_value_property_tmod1
            by blast
        next
          case (default_value_property_tmod2 f v)
          have default_value_prop: "defaultValue f v \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using default_value_property_tmod2.hyps prop_tmod2
            by blast
          have no_field: "f \<notin> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
            using default_value_property_tmod2.hyps
            by blast
          show ?case
            using default_value_prop no_field tmod_combine_prop_mapping.default_value_property_tmod2
            by blast
        next
          case (default_value_property_both f v)
          have default_value_prop1: "defaultValue f v \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using default_value_property_both.hyps prop_tmod1
            by blast
          have default_value_prop2: "defaultValue f v \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using default_value_property_both.hyps prop_tmod2
            by blast
          show ?case
            using default_value_prop1 default_value_prop2 tmod_combine_prop_mapping.default_value_property_both
            by blast
        next
          case (identity_property_tmod1 c A)
          have identity_prop: "identity c A \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using identity_property_tmod1.hyps prop_tmod1
            by blast
          have no_class: "c \<notin> {c \<in> Class (f2 (tg_combine TG1 TG2)). c \<in> Class Tmod2}"
            using identity_property_tmod1.hyps
            by blast
          show ?case
            using identity_prop no_class tmod_combine_prop_mapping.identity_property_tmod1
            by blast
        next
          case (identity_property_tmod2 c A)
          have identity_prop: "identity c A \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using identity_property_tmod2.hyps prop_tmod2
            by blast
          have no_class: "c \<notin> {c \<in> Class (f1 (tg_combine TG1 TG2)). c \<in> Class Tmod1}"
            using identity_property_tmod2.hyps
            by blast
          show ?case
            using identity_prop no_class tmod_combine_prop_mapping.identity_property_tmod2
            by blast
        next
          case (identity_property_both c A)
          have identity_prop1: "identity c A \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using identity_property_both.hyps prop_tmod1
            by blast
          have identity_prop2: "identity c A \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using identity_property_both.hyps prop_tmod2
            by blast
          show ?case
            using identity_prop1 identity_prop2 tmod_combine_prop_mapping.identity_property_both
            by blast
        next
          case (keyset_property_tmod1 r A)
          have keyset_prop: "keyset r A \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using keyset_property_tmod1.hyps prop_tmod1
            by blast
          have no_field: "r \<notin> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
            using keyset_property_tmod1.hyps
            by blast
          show ?case
            using keyset_prop no_field tmod_combine_prop_mapping.keyset_property_tmod1
            by blast
        next
          case (keyset_property_tmod2 r A)
          have keyset_prop: "keyset r A \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using keyset_property_tmod2.hyps prop_tmod2
            by blast
          have no_field: "r \<notin> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
            using keyset_property_tmod2.hyps
            by blast
          show ?case
            using keyset_prop no_field tmod_combine_prop_mapping.keyset_property_tmod2
            by blast
        next
          case (keyset_property_both r A)
          have keyset_prop1: "keyset r A \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using keyset_property_both.hyps prop_tmod1
            by blast
          have keyset_prop2: "keyset r A \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using keyset_property_both.hyps prop_tmod2
            by blast
          show ?case
            using keyset_prop1 keyset_prop2 tmod_combine_prop_mapping.keyset_property_both
            by blast
        next
          case (opposite_property_tmod1 r1 r2)
          have opposite_prop: "opposite r1 r2 \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using opposite_property_tmod1.hyps prop_tmod1
            by blast
          have no_field_r1: "r1 \<notin> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
            using opposite_property_tmod1.hyps
            by blast
          have no_field_r2: "r2 \<notin> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
            using opposite_property_tmod1.hyps
            by blast
          show ?case
            using opposite_prop no_field_r1 no_field_r2 tmod_combine_prop_mapping.opposite_property_tmod1
            by blast
        next
          case (opposite_property_tmod2 r1 r2)
          have opposite_prop: "opposite r1 r2 \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using opposite_property_tmod2.hyps prop_tmod2
            by blast
          have no_field_r1: "r1 \<notin> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
            using opposite_property_tmod2.hyps
            by blast
          have no_field_r2: "r2 \<notin> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
            using opposite_property_tmod2.hyps
            by blast
          show ?case
            using opposite_prop no_field_r1 no_field_r2 tmod_combine_prop_mapping.opposite_property_tmod2
            by blast
        next
          case (opposite_property_both r1 r2)
          have opposite_prop1: "opposite r1 r2 \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using opposite_property_both.hyps prop_tmod1
            by blast
          have opposite_prop2: "opposite r1 r2 \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using opposite_property_both.hyps prop_tmod2
            by blast
          show ?case
            using opposite_prop1 opposite_prop2 tmod_combine_prop_mapping.opposite_property_both
            by blast
        next
          case (readonly_property_tmod1 f)
          have readonly_prop: "readonly f \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using readonly_property_tmod1.hyps prop_tmod1
            by blast
          have no_field: "f \<notin> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
            using readonly_property_tmod1.hyps
            by blast
          show ?case
            using readonly_prop no_field tmod_combine_prop_mapping.readonly_property_tmod1
            by blast
        next
          case (readonly_property_tmod2 f)
          have readonly_prop: "readonly f \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using readonly_property_tmod2.hyps prop_tmod2
            by blast
          have no_field: "f \<notin> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
            using readonly_property_tmod2.hyps
            by blast
          show ?case
            using readonly_prop no_field tmod_combine_prop_mapping.readonly_property_tmod2
            by blast
        next
          case (readonly_property_both f)
          have readonly_prop1: "readonly f \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
            using readonly_property_both.hyps prop_tmod1
            by blast
          have readonly_prop2: "readonly f \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
            using readonly_property_both.hyps prop_tmod2
            by blast
          then show ?case
            using readonly_prop1 readonly_prop2 tmod_combine_prop_mapping.readonly_property_both
            by blast
        qed
      qed
    qed
  next
    show "{c \<in> Constant (f1 (tg_combine TG1 TG2)). c \<in> Constant Tmod1} \<union> {c \<in> Constant (f2 (tg_combine TG1 TG2)). c \<in> Constant Tmod2} = Constant Tmod1 \<union> Constant Tmod2"
      by (simp add: constant_tmod1 constant_tmod2)
  next
    show "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) = tmod_combine_const_type Tmod1 Tmod2"
    proof
      fix c
      have "c \<in> Constant Tmod1 \<inter> Constant Tmod2 \<or> c \<in> Constant Tmod1 - Constant Tmod2 \<or> c \<in> Constant Tmod2 - Constant Tmod1 \<or> c \<notin> Constant Tmod1 \<union> Constant Tmod2"
        by blast
      then show "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) c = tmod_combine_const_type Tmod1 Tmod2 c"
      proof (elim disjE)
        assume c_in_both: "c \<in> Constant Tmod1 \<inter> Constant Tmod2"
        then have c_in_both_alt: "c \<in> Constant (f1 TG1) \<inter> Constant (f2 TG2)"
          using mapping_tg1 mapping_tg2 tmod_combine_mapping_function.mapping_correct
          by blast
        have c_in_merge: "c \<in> {c \<in> Constant (f1 (tg_combine TG1 TG2)). c \<in> Constant Tmod1} \<inter> {c \<in> Constant (f2 (tg_combine TG1 TG2)). c \<in> Constant Tmod2}"
          using c_in_both constant_tmod1 constant_tmod2
          by blast
        have "ConstType Tmod1 c = ConstType Tmod2 c \<or> ConstType Tmod1 c \<noteq> ConstType Tmod2 c"
          by simp
        then show ?thesis
        proof (elim disjE)
          assume "ConstType Tmod1 c = ConstType Tmod2 c"
          then have combine_def: "tmod_combine_const_type Tmod1 Tmod2 c = ConstType Tmod1 c"
            unfolding tmod_combine_const_type_def
            using c_in_both
            by simp
          assume "ConstType Tmod1 c = ConstType Tmod2 c"
          then have "ConstType (f1 TG1) c = ConstType (f2 TG2) c"
            using mapping_tg1 mapping_tg2 tmod_combine_mapping_function.mapping_correct
            by blast
          then have "ConstType (f1 (tg_combine TG1 TG2)) c = ConstType (f2 (tg_combine TG1 TG2)) c"
            using IntD1 IntD2 c_in_both_alt mapping_tg1 mapping_tg2 tg_combine_commute tmod_combine_mapping_function.func_consttype
            by metis
          then have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) c = ConstType (f1 (tg_combine TG1 TG2)) c"
            unfolding tmod_combine_const_type_mapping_def
            using c_in_merge
            by simp
          then have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) c = ConstType (f1 TG1) c"
            using IntD1 c_in_both_alt mapping_tg1 tmod_combine_mapping_function.func_consttype
            by metis
          then have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) c = ConstType Tmod1 c"
            using mapping_tg1 tmod_combine_mapping_function.mapping_correct
            by blast
          then show ?thesis
            using combine_def
            by simp
        next
          assume "ConstType Tmod1 c \<noteq> ConstType Tmod2 c"
          then have combine_def: "tmod_combine_const_type Tmod1 Tmod2 c = invalid"
            unfolding tmod_combine_const_type_def
            using c_in_both
            by simp
          assume "ConstType Tmod1 c \<noteq> ConstType Tmod2 c"
          then have "ConstType (f1 TG1) c \<noteq> ConstType (f2 TG2) c"
            using mapping_tg1 mapping_tg2 tmod_combine_mapping_function.mapping_correct
            by blast
          then have "ConstType (f1 (tg_combine TG1 TG2)) c \<noteq> ConstType (f2 (tg_combine TG1 TG2)) c"
            using IntD1 IntD2 c_in_both_alt mapping_tg1 mapping_tg2 tg_combine_commute tmod_combine_mapping_function.func_consttype
            by metis
          then have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) c = invalid"
            unfolding tmod_combine_const_type_mapping_def
            using c_in_merge
            by simp
          then show ?thesis
            using combine_def
            by simp
        qed
      next
        assume "c \<in> Constant Tmod1 - Constant Tmod2"
        then have combine_def: "tmod_combine_const_type Tmod1 Tmod2 c = ConstType Tmod1 c"
          unfolding tmod_combine_const_type_def
          by simp
        assume "c \<in> Constant Tmod1 - Constant Tmod2"
        then have "c \<in> {c \<in> Constant (f1 (tg_combine TG1 TG2)). c \<in> Constant Tmod1} - {c \<in> Constant (f2 (tg_combine TG1 TG2)). c \<in> Constant Tmod2}"
          using constant_tmod1
          by blast
        then have mapping_def: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) c = ConstType (f1 (tg_combine TG1 TG2)) c"
          unfolding tmod_combine_const_type_mapping_def
          by auto
        assume "c \<in> Constant Tmod1 - Constant Tmod2"
        then have "c \<in> Constant (f1 TG1)"
          using mapping_tg1 tmod_combine_mapping_function.mapping_correct
          by blast
        then have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) c = ConstType (f1 TG1) c"
          using mapping_def mapping_tg1 tmod_combine_mapping_function.func_consttype
          by metis
        then have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) c = ConstType Tmod1 c"
          using mapping_tg1 tmod_combine_mapping_function.mapping_correct
          by blast
        then show ?thesis
          using combine_def
          by simp
      next
        assume "c \<in> Constant Tmod2 - Constant Tmod1"
        then have combine_def: "tmod_combine_const_type Tmod1 Tmod2 c = ConstType Tmod2 c"
          unfolding tmod_combine_const_type_def
          by simp
        assume "c \<in> Constant Tmod2 - Constant Tmod1"
        then have "c \<in> {c \<in> Constant (f2 (tg_combine TG1 TG2)). c \<in> Constant Tmod2} - {c \<in> Constant (f1 (tg_combine TG1 TG2)). c \<in> Constant Tmod1}"
          using constant_tmod2
          by blast
        then have mapping_def: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) c = ConstType (f2 (tg_combine TG1 TG2)) c"
          unfolding tmod_combine_const_type_mapping_def
          by auto
        assume "c \<in> Constant Tmod2 - Constant Tmod1"
        then have "c \<in> Constant (f2 TG2)"
          using mapping_tg2 tmod_combine_mapping_function.mapping_correct
          by blast
        then have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) c = ConstType (f2 TG2) c"
          using mapping_def mapping_tg2 tg_combine_commute tmod_combine_mapping_function.func_consttype
          by metis
        then have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) c = ConstType Tmod2 c"
          using mapping_tg2 tmod_combine_mapping_function.mapping_correct
          by blast
        then show ?thesis
          using combine_def
          by simp
      next
        assume "c \<notin> Constant Tmod1 \<union> Constant Tmod2"
        then show ?thesis
          unfolding tmod_combine_const_type_mapping_def tmod_combine_const_type_def
          by simp
      qed
    qed
  qed (simp)
qed

lemma tmod_combine_mapping_function_correct:
  assumes mapping_tg1: "tmod_combine_mapping_function f1 TG1 Tmod1"
  assumes mapping_tg2: "tmod_combine_mapping_function f2 TG2 Tmod2"
  shows "tmod_combine_mapping_function (tmod_combine_mapping (f1) Tmod1 (f2) Tmod2) (tg_combine TG1 TG2) (tmod_combine Tmod1 Tmod2)"
proof (intro tmod_combine_mapping_function.intro)
  show "tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) = tmod_combine Tmod1 Tmod2"
    using assms tmod_combine_mapping_correct
    by blast
next
  fix TG3
  show "Class (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)) \<subseteq> 
    Class (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
  proof
    fix x
    assume "x \<in> Class (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2))"
    then have "x \<in> {c \<in> Class (f1 (tg_combine TG1 TG2)). c \<in> Class Tmod1} \<union> {c \<in> Class (f2 (tg_combine TG1 TG2)). c \<in> Class Tmod2}"
      unfolding tmod_combine_mapping_def
      by simp
    then have "x \<in> {c \<in> Class (f1 (tg_combine (tg_combine TG1 TG2) TG3)). c \<in> Class Tmod1} \<union> {c \<in> Class (f2 (tg_combine (tg_combine TG1 TG2) TG3)). c \<in> Class Tmod2}"
    proof (elim UnE)
      assume "x \<in> {c \<in> Class (f1 (tg_combine TG1 TG2)). c \<in> Class Tmod1}"
      then have "x \<in> Class Tmod1"
        by simp
      then have "x \<in> {c \<in> Class (f1 (tg_combine TG1 (tg_combine TG2 TG3))). c \<in> Class Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_class
        by blast
      then have "x \<in> {c \<in> Class (f1 (tg_combine (tg_combine TG1 TG2) TG3)). c \<in> Class Tmod1}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    next
      assume "x \<in> {c \<in> Class (f2 (tg_combine TG1 TG2)). c \<in> Class Tmod2}"
      then have "x \<in> Class Tmod2"
        by simp
      then have "x \<in> {c \<in> Class (f2 (tg_combine TG2 (tg_combine TG1 TG3))). c \<in> Class Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_class
        by blast
      then have "x \<in> {c \<in> Class (f2 (tg_combine (tg_combine TG2 TG1) TG3)). c \<in> Class Tmod2}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    qed
    then show "x \<in> Class (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
      unfolding tmod_combine_mapping_def
      by simp
  qed
next
  fix TG3
  show "Enum (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)) \<subseteq> 
    Enum (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
  proof
    fix x
    assume "x \<in> Enum (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2))"
    then have "x \<in> {e \<in> Enum (f1 (tg_combine TG1 TG2)). e \<in> Enum Tmod1} \<union> {e \<in> Enum (f2 (tg_combine TG1 TG2)). e \<in> Enum Tmod2}"
      unfolding tmod_combine_mapping_def
      by simp
    then have "x \<in> {e \<in> Enum (f1 (tg_combine (tg_combine TG1 TG2) TG3)). e \<in> Enum Tmod1} \<union> {e \<in> Enum (f2 (tg_combine (tg_combine TG1 TG2) TG3)). e \<in> Enum Tmod2}"
    proof (elim UnE)
      assume "x \<in> {e \<in> Enum (f1 (tg_combine TG1 TG2)). e \<in> Enum Tmod1}"
      then have "x \<in> Enum Tmod1"
        by simp
      then have "x \<in> {e \<in> Enum (f1 (tg_combine TG1 (tg_combine TG2 TG3))). e \<in> Enum Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_enum
        by blast
      then have "x \<in> {e \<in> Enum (f1 (tg_combine (tg_combine TG1 TG2) TG3)). e \<in> Enum Tmod1}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    next
      assume "x \<in> {e \<in> Enum (f2 (tg_combine TG1 TG2)). e \<in> Enum Tmod2}"
      then have "x \<in> Enum Tmod2"
        by simp
      then have "x \<in> {e \<in> Enum (f2 (tg_combine TG2 (tg_combine TG1 TG3))). e \<in> Enum Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_enum
        by blast
      then have "x \<in> {e \<in> Enum (f2 (tg_combine (tg_combine TG2 TG1) TG3)). e \<in> Enum Tmod2}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    qed
    then show "x \<in> Enum (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
      unfolding tmod_combine_mapping_def
      by simp
  qed
next
  fix TG3
  show "UserDataType (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)) \<subseteq> 
    UserDataType (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
  proof
    fix x
    assume "x \<in> UserDataType (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2))"
    then have "x \<in> {u \<in> UserDataType (f1 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod1} \<union> {u \<in> UserDataType (f2 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod2}"
      unfolding tmod_combine_mapping_def
      by simp
    then have "x \<in> {u \<in> UserDataType (f1 (tg_combine (tg_combine TG1 TG2) TG3)). u \<in> UserDataType Tmod1} \<union> {u \<in> UserDataType (f2 (tg_combine (tg_combine TG1 TG2) TG3)). u \<in> UserDataType Tmod2}"
    proof (elim UnE)
      assume "x \<in> {u \<in> UserDataType (f1 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod1}"
      then have "x \<in> UserDataType Tmod1"
        by simp
      then have "x \<in> {u \<in> UserDataType (f1 (tg_combine TG1 (tg_combine TG2 TG3))). u \<in> UserDataType Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_userdatatype
        by blast
      then have "x \<in> {u \<in> UserDataType (f1 (tg_combine (tg_combine TG1 TG2) TG3)). u \<in> UserDataType Tmod1}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    next
      assume "x \<in> {u \<in> UserDataType (f2 (tg_combine TG1 TG2)). u \<in> UserDataType Tmod2}"
      then have "x \<in> UserDataType Tmod2"
        by simp
      then have "x \<in> {u \<in> UserDataType (f2 (tg_combine TG2 (tg_combine TG1 TG3))). u \<in> UserDataType Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_userdatatype
        by blast
      then have "x \<in> {u \<in> UserDataType (f2 (tg_combine (tg_combine TG2 TG1) TG3)). u \<in> UserDataType Tmod2}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    qed
    then show "x \<in> UserDataType (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
      unfolding tmod_combine_mapping_def
      by simp
  qed
next
  fix TG3
  show "Field (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)) \<subseteq> 
    Field (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
  proof
    fix x
    assume "x \<in> Field (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2))"
    then have "x \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} \<union> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
      unfolding tmod_combine_mapping_def
      by simp
    then have "x \<in> {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1} \<union> {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
    proof (elim UnE)
      assume "x \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
      then have "x \<in> Field Tmod1"
        by simp
      then have "x \<in> {f \<in> Field (f1 (tg_combine TG1 (tg_combine TG2 TG3))). f \<in> Field Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by blast
      then have "x \<in> {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    next
      assume "x \<in> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
      then have "x \<in> Field Tmod2"
        by simp
      then have "x \<in> {f \<in> Field (f2 (tg_combine TG2 (tg_combine TG1 TG3))). f \<in> Field Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by blast
      then have "x \<in> {f \<in> Field (f2 (tg_combine (tg_combine TG2 TG1) TG3)). f \<in> Field Tmod2}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    qed
    then show "x \<in> Field (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
      unfolding tmod_combine_mapping_def
      by simp
  qed
next
  fix TG3 x
  have field_tmod1: "{f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} = {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1}"
  proof
    show "{f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} \<subseteq> 
      {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1}"
    proof
      fix x
      assume "x \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
      then have "x \<in> Field Tmod1"
        by simp
      then have "x \<in> {f \<in> Field (f1 (tg_combine TG1 (tg_combine TG2 TG3))). f \<in> Field Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by blast
      then show "x \<in> {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1}"
        using tg_combine_assoc
        by metis
    qed
  next
    show "{f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1} \<subseteq> 
      {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
      by blast
  qed
  have f1_fieldsig_altdef: "\<And>y. y \<in> Field Tmod1 \<Longrightarrow> FieldSig (f1 (tg_combine TG1 TG2)) y = FieldSig (f1 (tg_combine TG1 (tg_combine TG2 TG3))) y"
  proof-
    fix y
    assume "y \<in> Field Tmod1"
    then have tmod1_tmod12: "FieldSig (f1 TG1) y = FieldSig (f1 (tg_combine TG1 TG2)) y"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.func_fieldsig
      by blast
    assume "y \<in> Field Tmod1"
    then have tmod1_tmod123: "FieldSig (f1 TG1) y = FieldSig (f1 (tg_combine TG1 (tg_combine TG2 TG3))) y"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.func_fieldsig
      by blast
    show "FieldSig (f1 (tg_combine TG1 TG2)) y = FieldSig (f1 (tg_combine TG1 (tg_combine TG2 TG3))) y"
      using tmod1_tmod12 tmod1_tmod123
      by simp
  qed
  have field_tmod2: "{f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} = {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
  proof
    show "{f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} \<subseteq> 
      {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
    proof
      fix x
      assume "x \<in> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
      then have "x \<in> Field Tmod2"
        by simp
      then have "x \<in> {f \<in> Field (f2 (tg_combine TG2 (tg_combine TG1 TG3))). f \<in> Field Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by blast
      then have "x \<in> {f \<in> Field (f2 (tg_combine (tg_combine TG2 TG1) TG3)). f \<in> Field Tmod2}"
        using tg_combine_assoc
        by metis
      then show "x \<in> {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
        by simp
    qed
  next
    show "{f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2} \<subseteq> 
      {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
    proof
      fix x
      assume "x \<in> {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
      then have "x \<in> Field Tmod2"
        by simp
      then have "x \<in> {f \<in> Field (f2 (tg_combine TG2 TG1)). f \<in> Field Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by blast
      then show "x \<in> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
        by simp
    qed
  qed
  have f2_fieldsig_altdef: "\<And>y. y \<in> Field Tmod2 \<Longrightarrow> FieldSig (f2 (tg_combine TG1 TG2)) y = FieldSig (f2 (tg_combine TG1 (tg_combine TG2 TG3))) y"
  proof-
    fix y
    assume "y \<in> Field Tmod2"
    then have "FieldSig (f2 TG2) y = FieldSig (f2 (tg_combine TG2 TG1)) y"
      using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.func_fieldsig
      by blast
    then have tmod1_tmod12: "FieldSig (f2 TG2) y = FieldSig (f2 (tg_combine TG1 TG2)) y"
      by simp
    assume "y \<in> Field Tmod2"
    then have "FieldSig (f2 TG2) y = FieldSig (f2 (tg_combine TG2 (tg_combine TG1 TG3))) y"
      using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.func_fieldsig
      by blast
    then have tmod1_tmod123: "FieldSig (f2 TG2) y = FieldSig (f2 (tg_combine TG1 (tg_combine TG2 TG3))) y"
      using tg_combine_assoc tg_combine_commute
      by metis
    show "FieldSig (f2 (tg_combine TG1 TG2)) y = FieldSig (f2 (tg_combine TG1 (tg_combine TG2 TG3))) y"
      using tmod1_tmod12 tmod1_tmod123
      by simp
  qed
  assume "x \<in> Field (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2))"
  then have "x \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} \<union> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
    unfolding tmod_combine_mapping_def
    by simp
  then have "x \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} \<inter> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} \<or>
    x \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} - {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} \<or>
    x \<in> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} - {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
    by blast
  then have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = 
    tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x"
  proof (elim disjE)
    assume x_in_tg12: "x \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} \<inter>
      {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
    then have x_in_tg123: "x \<in> {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1} \<inter>
      {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
      using field_tmod1 field_tmod2
      by simp
    then have x_in_fields: "x \<in> Field Tmod1 \<inter> Field Tmod2"
      by simp
    then show "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x =
      tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x"
    proof (induct "fst (FieldSig (f1 TG1) x) = fst (FieldSig (f2 TG2) x)")
      case True
      then have tg12_eq: "fst (FieldSig (f1 (tg_combine TG1 TG2)) x) = fst (FieldSig (f2 (tg_combine TG1 TG2)) x)"
        using IntD1 IntD2 mapping_tg1 mapping_tg2 tg_combine_commute tmod_combine_mapping_function.func_fieldsig tmod_combine_mapping_function.mapping_correct
        by metis
      then have tg123_eq: "fst (FieldSig (f1 (tg_combine (tg_combine TG1 TG2) TG3)) x) = fst (FieldSig (f2 (tg_combine (tg_combine TG1 TG2) TG3)) x)"
        using Int_iff f1_fieldsig_altdef f2_fieldsig_altdef tg_combine_assoc x_in_fields
        by metis
      have tg12_unfold: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = 
        (fst (FieldSig (f1 (tg_combine TG1 TG2)) x), snd (FieldSig (f1 (tg_combine TG1 TG2)) x) \<sqinter> snd (FieldSig (f2 (tg_combine TG1 TG2)) x))"
        unfolding tmod_combine_fieldsig_mapping_def
        using tg12_eq x_in_tg12
        by simp
      then have tg12_def: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = 
        (fst (FieldSig (f1 TG1) x), snd (FieldSig (f1 TG1) x) \<sqinter> snd (FieldSig (f2 TG2) x))"
        using IntD1 IntD2 mapping_tg1 mapping_tg2 tg_combine_commute tmod_combine_mapping_function_def x_in_fields
        by metis
      have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = 
        (fst (FieldSig (f1 (tg_combine (tg_combine TG1 TG2) TG3)) x), snd (FieldSig (f1 (tg_combine (tg_combine TG1 TG2) TG3)) x) \<sqinter> snd (FieldSig (f2 (tg_combine (tg_combine TG1 TG2) TG3)) x))"
        unfolding tmod_combine_fieldsig_mapping_def
        using tg123_eq x_in_tg123
        by simp
      then have tg123_def: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = 
        (fst (FieldSig (f1 TG1) x), snd (FieldSig (f1 TG1) x) \<sqinter> snd (FieldSig (f2 TG2) x))"
        using IntD1 IntD2 tg12_unfold f1_fieldsig_altdef f2_fieldsig_altdef tg12_def tg_combine_assoc x_in_fields
        by metis
      show ?case
        using tg12_def tg123_def
        by simp
    next
      case False
      then have tg12_not_eq: "fst (FieldSig (f1 (tg_combine TG1 TG2)) x) \<noteq> fst (FieldSig (f2 (tg_combine TG1 TG2)) x)"
        using IntD1 IntD2 mapping_tg1 mapping_tg2 tg_combine_commute tmod_combine_mapping_function.func_fieldsig tmod_combine_mapping_function.mapping_correct
        by metis
      then have tg123_not_eq: "fst (FieldSig (f1 (tg_combine (tg_combine TG1 TG2) TG3)) x) \<noteq> fst (FieldSig (f2 (tg_combine (tg_combine TG1 TG2) TG3)) x)"
        using Int_iff f1_fieldsig_altdef f2_fieldsig_altdef tg_combine_assoc x_in_fields
        by metis
      have tg12_def: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = (invalid, \<^emph>..\<^bold>0)"
        unfolding tmod_combine_fieldsig_mapping_def
        using tg12_not_eq x_in_tg12
        by simp
      have tg123_def: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = (invalid, \<^emph>..\<^bold>0)"
        unfolding tmod_combine_fieldsig_mapping_def
        using tg123_not_eq x_in_tg123
        by simp
      show ?case
        using tg12_def tg123_def
        by simp
    qed
  next
    assume "x \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} - {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
    then have x_in_fields_def: "x \<in> Field Tmod1 - Field Tmod2"
      using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
      by fastforce
    assume "x \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} - {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
    then have tg12_unfold: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = FieldSig (f1 (tg_combine TG1 TG2)) x"
      unfolding tmod_combine_fieldsig_mapping_def
      by auto
    then have tg12_def: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = FieldSig (f1 TG1) x"
      using Diff_iff x_in_fields_def mapping_tg1 tmod_combine_mapping_function_def
      by metis
    assume "x \<in> {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1} - {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2}"
    then have "x \<in> {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1} - {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
      using field_tmod1 field_tmod2
      by blast
    then have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = FieldSig (f1 (tg_combine (tg_combine TG1 TG2) TG3)) x"
      unfolding tmod_combine_fieldsig_mapping_def
      by auto
    then have tg123_def: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = FieldSig (f1 TG1) x"
      using Diff_iff f1_fieldsig_altdef tg12_def tg12_unfold tg_combine_assoc x_in_fields_def
      by metis
    show ?thesis
      using tg12_def tg123_def
      by simp
  next
    assume "x \<in> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} - {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
    then have x_in_fields_def: "x \<in> Field Tmod2 - Field Tmod1"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
      by fastforce
    assume "x \<in> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} - {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
    then have tg12_unfold: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = FieldSig (f2 (tg_combine TG1 TG2)) x"
      unfolding tmod_combine_fieldsig_mapping_def
      by auto
    then have tg12_def: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = FieldSig (f2 TG2) x"
      using Diff_iff mapping_tg2 tg_combine_commute tmod_combine_mapping_function_def x_in_fields_def
      by metis
    assume "x \<in> {f \<in> Field (f2 (tg_combine TG1 TG2)). f \<in> Field Tmod2} - {f \<in> Field (f1 (tg_combine TG1 TG2)). f \<in> Field Tmod1}"
    then have "x \<in> {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2} - {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1}"
      using field_tmod1 field_tmod2
      by blast
    then have "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = FieldSig (f2 (tg_combine (tg_combine TG1 TG2) TG3)) x"
      unfolding tmod_combine_fieldsig_mapping_def
      by auto
    then have tg123_def: "tmod_combine_fieldsig_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = FieldSig (f2 TG2) x"
      using Diff_iff f2_fieldsig_altdef tg12_def tg12_unfold tg_combine_assoc x_in_fields_def
      by metis
    show ?thesis
      using tg12_def tg123_def
      by simp
  qed
  then show "FieldSig (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)) x =
    FieldSig (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3)) x"
    unfolding tmod_combine_mapping_def
    by simp
next
  fix TG3
  show "EnumValue (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)) \<subseteq> 
    EnumValue (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
  proof
    fix x
    assume "x \<in> EnumValue (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2))"
    then have "x \<in> {ev \<in> EnumValue (f1 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod1} \<union> {ev \<in> EnumValue (f2 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod2}"
      unfolding tmod_combine_mapping_def
      by simp
    then have "x \<in> {ev \<in> EnumValue (f1 (tg_combine (tg_combine TG1 TG2) TG3)). ev \<in> EnumValue Tmod1} \<union> {ev \<in> EnumValue (f2 (tg_combine (tg_combine TG1 TG2) TG3)). ev \<in> EnumValue Tmod2}"
    proof (elim UnE)
      assume "x \<in> {ev \<in> EnumValue (f1 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod1}"
      then have "x \<in> EnumValue Tmod1"
        by simp
      then have "x \<in> {ev \<in> EnumValue (f1 (tg_combine TG1 (tg_combine TG2 TG3))). ev \<in> EnumValue Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_enumvalue
        by blast
      then have "x \<in> {ev \<in> EnumValue (f1 (tg_combine (tg_combine TG1 TG2) TG3)). ev \<in> EnumValue Tmod1}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    next
      assume "x \<in> {ev \<in> EnumValue (f2 (tg_combine TG1 TG2)). ev \<in> EnumValue Tmod2}"
      then have "x \<in> EnumValue Tmod2"
        by simp
      then have "x \<in> {ev \<in> EnumValue (f2 (tg_combine TG2 (tg_combine TG1 TG3))). ev \<in> EnumValue Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_enumvalue
        by blast
      then have "x \<in> {ev \<in> EnumValue (f2 (tg_combine (tg_combine TG2 TG1) TG3)). ev \<in> EnumValue Tmod2}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    qed
    then show "x \<in> EnumValue (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
      unfolding tmod_combine_mapping_def
      by simp
  qed
next
  fix TG3
  show "Inh (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)) \<subseteq> 
    Inh (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
  proof
    fix x
    assume "x \<in> Inh (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2))"
    then have "x \<in> {i \<in> Inh (f1 (tg_combine TG1 TG2)). i \<in> Inh Tmod1} \<union> {i \<in> Inh (f2 (tg_combine TG1 TG2)). i \<in> Inh Tmod2}"
      unfolding tmod_combine_mapping_def
      by simp
    then have "x \<in> {i \<in> Inh (f1 (tg_combine (tg_combine TG1 TG2) TG3)). i \<in> Inh Tmod1} \<union> {i \<in> Inh (f2 (tg_combine (tg_combine TG1 TG2) TG3)). i \<in> Inh Tmod2}"
    proof (elim UnE)
      assume "x \<in> {i \<in> Inh (f1 (tg_combine TG1 TG2)). i \<in> Inh Tmod1}"
      then have "x \<in> Inh Tmod1"
        by simp
      then have "x \<in> {i \<in> Inh (f1 (tg_combine TG1 (tg_combine TG2 TG3))). i \<in> Inh Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_inh
        by blast
      then have "x \<in> {i \<in> Inh (f1 (tg_combine (tg_combine TG1 TG2) TG3)). i \<in> Inh Tmod1}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    next
      assume "x \<in> {i \<in> Inh (f2 (tg_combine TG1 TG2)). i \<in> Inh Tmod2}"
      then have "x \<in> Inh Tmod2"
        by simp
      then have "x \<in> {i \<in> Inh (f2 (tg_combine TG2 (tg_combine TG1 TG3))). i \<in> Inh Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_inh
        by blast
      then have "x \<in> {i \<in> Inh (f2 (tg_combine (tg_combine TG2 TG1) TG3)). i \<in> Inh Tmod2}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    qed
    then show "x \<in> Inh (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
      unfolding tmod_combine_mapping_def
      by simp
  qed
next
  fix TG3
  have prop_tmod1: "{p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1} = {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
  proof
    show "{p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1} \<subseteq> 
      {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
    proof
      fix x
      assume "x \<in> {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
      then have "x \<in> Prop Tmod1"
        by simp
      then have "x \<in> {p \<in> Prop (f1 (tg_combine TG1 (tg_combine TG2 TG3))). p \<in> Prop Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_prop
        by blast
      then show "x \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using tg_combine_assoc
        by metis
    qed
  next
    show "{p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1} \<subseteq> 
      {p \<in> Prop (f1 (tg_combine TG1 TG2)). p \<in> Prop Tmod1}"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_prop
      by blast
  qed
  have prop_tmod2: "{p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2} = {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
  proof
    show "{p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2} \<subseteq> 
      {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
    proof
      fix x
      assume "x \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
      then have "x \<in> Prop Tmod2"
        by simp
      then have "x \<in> {p \<in> Prop (f2 (tg_combine TG2 (tg_combine TG1 TG3))). p \<in> Prop Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_prop
        by blast
      then have "x \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG2 TG1) TG3)). p \<in> Prop Tmod2}"
        using tg_combine_assoc
        by metis
      then show "x \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        by simp
    qed
  next
    show "{p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2} \<subseteq> 
      {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
    proof
      fix x
      assume "x \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
      then have "x \<in> Prop Tmod2"
        by simp
      then have "x \<in> {p \<in> Prop (f2 (tg_combine TG2 TG1)). p \<in> Prop Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_prop
        by blast
      then show "x \<in> {p \<in> Prop (f2 (tg_combine TG1 TG2)). p \<in> Prop Tmod2}"
        by simp
    qed
  qed
  show "Prop (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)) \<subseteq> 
    Prop (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
  proof
    fix x
    assume "x \<in> Prop (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2))"
    then have "x \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)"
      by (simp add: tmod_combine_mapping_def)
    then have "x \<in> tmod_combine_prop_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3)"
    proof (induct)
      case (abstract_property_tmod1 c)
      have abstract_prop: "abstract c \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using abstract_property_tmod1.hyps prop_tmod1
        by blast
      have no_class: "c \<notin> {c \<in> Class (f2 (tg_combine (tg_combine TG1 TG2) TG3)). c \<in> Class Tmod2}"
        using abstract_property_tmod1.hyps mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_class
        by fastforce
      show ?case
        using abstract_prop no_class tmod_combine_prop_mapping.abstract_property_tmod1
        by blast
    next
      case (abstract_property_tmod2 c)
      have abstract_prop: "abstract c \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using abstract_property_tmod2.hyps prop_tmod2
        by blast
      have no_class: "c \<notin> {c \<in> Class (f1 (tg_combine (tg_combine TG1 TG2) TG3)). c \<in> Class Tmod1}"
        using abstract_property_tmod2.hyps mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_class
        by fastforce
      show ?case
        using abstract_prop no_class tmod_combine_prop_mapping.abstract_property_tmod2
        by blast
    next
      case (abstract_property_both c)
      have abstract_prop1: "abstract c \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using abstract_property_both.hyps prop_tmod1
        by blast
      have abstract_prop2: "abstract c \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using abstract_property_both.hyps prop_tmod2
        by blast
      show ?case
        using abstract_prop1 abstract_prop2 tmod_combine_prop_mapping.abstract_property_both
        by blast
    next
      case (containment_property_tmod1 r)
      have "containment r \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using containment_property_tmod1.hyps prop_tmod1
        by blast
      then show ?case
        using tmod_combine_prop_mapping.containment_property_tmod1
        by blast
    next
      case (containment_property_tmod2 r)
      have "containment r \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using containment_property_tmod2.hyps prop_tmod2
        by blast
      then show ?case
        using tmod_combine_prop_mapping.containment_property_tmod2
        by blast
    next
      case (default_value_property_tmod1 f v)
      have default_value_prop: "defaultValue f v \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using default_value_property_tmod1.hyps prop_tmod1
        by blast
      have no_field: "f \<notin> {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
        using default_value_property_tmod1.hyps mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by fastforce
      show ?case
        using default_value_prop no_field tmod_combine_prop_mapping.default_value_property_tmod1
        by blast
    next
      case (default_value_property_tmod2 f v)
      have default_value_prop: "defaultValue f v \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using default_value_property_tmod2.hyps prop_tmod2
        by blast
      have no_field: "f \<notin> {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1}"
        using default_value_property_tmod2.hyps mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by fastforce
      show ?case
        using default_value_prop no_field tmod_combine_prop_mapping.default_value_property_tmod2
        by blast
    next
      case (default_value_property_both f v)
      have default_value_prop1: "defaultValue f v \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using default_value_property_both.hyps prop_tmod1
        by blast
      have default_value_prop2: "defaultValue f v \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using default_value_property_both.hyps prop_tmod2
        by blast
      show ?case
        using default_value_prop1 default_value_prop2 tmod_combine_prop_mapping.default_value_property_both
        by blast
    next
      case (identity_property_tmod1 c A)
      have identity_prop: "identity c A \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using identity_property_tmod1.hyps prop_tmod1
        by blast
      have no_class: "c \<notin> {c \<in> Class (f2 (tg_combine (tg_combine TG1 TG2) TG3)). c \<in> Class Tmod2}"
        using identity_property_tmod1.hyps mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_class
        by fastforce
      show ?case
        using identity_prop no_class tmod_combine_prop_mapping.identity_property_tmod1
        by blast
    next
      case (identity_property_tmod2 c A)
      have identity_prop: "identity c A \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using identity_property_tmod2.hyps prop_tmod2
        by blast
      have no_class: "c \<notin> {c \<in> Class (f1 (tg_combine (tg_combine TG1 TG2) TG3)). c \<in> Class Tmod1}"
        using identity_property_tmod2.hyps mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_class
        by fastforce
      show ?case
        using identity_prop no_class tmod_combine_prop_mapping.identity_property_tmod2
        by blast
    next
      case (identity_property_both c A)
      have identity_prop1: "identity c A \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using identity_property_both.hyps prop_tmod1
        by blast
      have identity_prop2: "identity c A \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using identity_property_both.hyps prop_tmod2
        by blast
      show ?case
        using identity_prop1 identity_prop2 tmod_combine_prop_mapping.identity_property_both
        by blast
    next
      case (keyset_property_tmod1 r A)
      have keyset_prop: "keyset r A \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using keyset_property_tmod1.hyps prop_tmod1
        by blast
      have no_field: "r \<notin> {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
        using keyset_property_tmod1.hyps mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by fastforce
      show ?case
        using keyset_prop no_field tmod_combine_prop_mapping.keyset_property_tmod1
        by blast
    next
      case (keyset_property_tmod2 r A)
      have keyset_prop: "keyset r A \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using keyset_property_tmod2.hyps prop_tmod2
        by blast
      have no_field: "r \<notin> {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1}"
        using keyset_property_tmod2.hyps mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by fastforce
      show ?case
        using keyset_prop no_field tmod_combine_prop_mapping.keyset_property_tmod2
        by blast
    next
      case (keyset_property_both r A)
      have keyset_prop1: "keyset r A \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using keyset_property_both.hyps prop_tmod1
        by blast
      have keyset_prop2: "keyset r A \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using keyset_property_both.hyps prop_tmod2
        by blast
      show ?case
        using keyset_prop1 keyset_prop2 tmod_combine_prop_mapping.keyset_property_both
        by blast
    next
      case (opposite_property_tmod1 r1 r2)
      have opposite_prop: "opposite r1 r2 \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using opposite_property_tmod1.hyps prop_tmod1
        by blast
      have no_field_r1: "r1 \<notin> {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
        using opposite_property_tmod1.hyps mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by fastforce
      have no_field_r2: "r2 \<notin> {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
        using opposite_property_tmod1.hyps mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by fastforce
      show ?case
        using opposite_prop no_field_r1 no_field_r2 tmod_combine_prop_mapping.opposite_property_tmod1
        by blast
    next
      case (opposite_property_tmod2 r1 r2)
      have opposite_prop: "opposite r1 r2 \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using opposite_property_tmod2.hyps prop_tmod2
        by blast
      have no_field_r1: "r1 \<notin> {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1}"
        using opposite_property_tmod2.hyps mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by fastforce
      have no_field_r2: "r2 \<notin> {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1}"
        using opposite_property_tmod2.hyps mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by fastforce
      show ?case
        using opposite_prop no_field_r1 no_field_r2 tmod_combine_prop_mapping.opposite_property_tmod2
        by blast
    next
      case (opposite_property_both r1 r2)
      have opposite_prop1: "opposite r1 r2 \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using opposite_property_both.hyps prop_tmod1
        by blast
      have opposite_prop2: "opposite r1 r2 \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using opposite_property_both.hyps prop_tmod2
        by blast
      show ?case
        using opposite_prop1 opposite_prop2 tmod_combine_prop_mapping.opposite_property_both
        by blast
    next
      case (readonly_property_tmod1 f)
      have readonly_prop: "readonly f \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using readonly_property_tmod1.hyps prop_tmod1
        by blast
      have no_field: "f \<notin> {f \<in> Field (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod2}"
        using readonly_property_tmod1.hyps mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by fastforce
      show ?case
        using readonly_prop no_field tmod_combine_prop_mapping.readonly_property_tmod1
        by blast
    next
      case (readonly_property_tmod2 f)
      have readonly_prop: "readonly f \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using readonly_property_tmod2.hyps prop_tmod2
        by blast
      have no_field: "f \<notin> {f \<in> Field (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Field Tmod1}"
        using readonly_property_tmod2.hyps mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_field
        by fastforce
      show ?case
        using readonly_prop no_field tmod_combine_prop_mapping.readonly_property_tmod2
        by blast
    next
      case (readonly_property_both f)
      have readonly_prop1: "readonly f \<in> {p \<in> Prop (f1 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod1}"
        using readonly_property_both.hyps prop_tmod1
        by blast
      have readonly_prop2: "readonly f \<in> {p \<in> Prop (f2 (tg_combine (tg_combine TG1 TG2) TG3)). p \<in> Prop Tmod2}"
        using readonly_property_both.hyps prop_tmod2
        by blast
      then show ?case
        using readonly_prop1 readonly_prop2 tmod_combine_prop_mapping.readonly_property_both
        by blast
    qed
    then show "x \<in> Prop (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
      by (simp add: tmod_combine_mapping_def)
  qed
next
  fix TG3
  show "Constant (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)) \<subseteq>
    Constant (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
  proof
    fix x
    assume "x \<in> Constant (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2))"
    then have "x \<in> {c \<in> Constant (f1 (tg_combine TG1 TG2)). c \<in> Constant Tmod1} \<union> {c \<in> Constant (f2 (tg_combine TG1 TG2)). c \<in> Constant Tmod2}"
      unfolding tmod_combine_mapping_def
      by simp
    then have "x \<in> {c \<in> Constant (f1 (tg_combine (tg_combine TG1 TG2) TG3)). c \<in> Constant Tmod1} \<union> {c \<in> Constant (f2 (tg_combine (tg_combine TG1 TG2) TG3)). c \<in> Constant Tmod2}"
    proof (elim UnE)
      assume "x \<in> {c \<in> Constant (f1 (tg_combine TG1 TG2)). c \<in> Constant Tmod1}"
      then have "x \<in> Constant Tmod1"
        by simp
      then have "x \<in> {c \<in> Constant (f1 (tg_combine TG1 (tg_combine TG2 TG3))). c \<in> Constant Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_constant
        by blast
      then have "x \<in> {c \<in> Constant (f1 (tg_combine (tg_combine TG1 TG2) TG3)). c \<in> Constant Tmod1}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    next
      assume "x \<in> {c \<in> Constant (f2 (tg_combine TG1 TG2)). c \<in> Constant Tmod2}"
      then have "x \<in> Constant Tmod2"
        by simp
      then have "x \<in> {c \<in> Constant (f2 (tg_combine TG2 (tg_combine TG1 TG3))). c \<in> Constant Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_constant
        by blast
      then have "x \<in> {c \<in> Constant (f2 (tg_combine (tg_combine TG2 TG1) TG3)). c \<in> Constant Tmod2}"
        using tg_combine_assoc
        by metis
      then show ?thesis
        by simp
    qed
    then show "x \<in> Constant (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3))"
      unfolding tmod_combine_mapping_def
      by simp
  qed
next
  fix TG3 x
  have constant_tmod1: "{f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1} = {f \<in> Constant (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod1}"
  proof
    show "{f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1} \<subseteq> 
      {f \<in> Constant (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod1}"
    proof
      fix x
      assume "x \<in> {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1}"
      then have "x \<in> Constant Tmod1"
        by simp
      then have "x \<in> {f \<in> Constant (f1 (tg_combine TG1 (tg_combine TG2 TG3))). f \<in> Constant Tmod1}"
        using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_constant
        by blast
      then show "x \<in> {f \<in> Constant (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod1}"
        using tg_combine_assoc
        by metis
    qed
  next
    show "{f \<in> Constant (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod1} \<subseteq> 
      {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1}"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_constant
      by blast
  qed
  have f1_consttype_altdef: "\<And>y. y \<in> Constant Tmod1 \<Longrightarrow> ConstType (f1 (tg_combine TG1 TG2)) y = ConstType (f1 (tg_combine TG1 (tg_combine TG2 TG3))) y"
  proof-
    fix y
    assume "y \<in> Constant Tmod1"
    then have tmod1_tmod12: "ConstType (f1 TG1) y = ConstType (f1 (tg_combine TG1 TG2)) y"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.func_consttype
      by blast
    assume "y \<in> Constant Tmod1"
    then have tmod1_tmod123: "ConstType (f1 TG1) y = ConstType (f1 (tg_combine TG1 (tg_combine TG2 TG3))) y"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.func_consttype
      by blast
    show "ConstType (f1 (tg_combine TG1 TG2)) y = ConstType (f1 (tg_combine TG1 (tg_combine TG2 TG3))) y"
      using tmod1_tmod12 tmod1_tmod123
      by simp
  qed
  have constant_tmod2: "{f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2} = {f \<in> Constant (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod2}"
  proof
    show "{f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2} \<subseteq> 
      {f \<in> Constant (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod2}"
    proof
      fix x
      assume "x \<in> {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2}"
      then have "x \<in> Constant Tmod2"
        by simp
      then have "x \<in> {f \<in> Constant (f2 (tg_combine TG2 (tg_combine TG1 TG3))). f \<in> Constant Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_constant
        by blast
      then have "x \<in> {f \<in> Constant (f2 (tg_combine (tg_combine TG2 TG1) TG3)). f \<in> Constant Tmod2}"
        using tg_combine_assoc
        by metis
      then show "x \<in> {f \<in> Constant (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod2}"
        by simp
    qed
  next
    show "{f \<in> Constant (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod2} \<subseteq> 
      {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2}"
    proof
      fix x
      assume "x \<in> {f \<in> Constant (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod2}"
      then have "x \<in> Constant Tmod2"
        by simp
      then have "x \<in> {f \<in> Constant (f2 (tg_combine TG2 TG1)). f \<in> Constant Tmod2}"
        using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_constant
        by blast
      then show "x \<in> {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2}"
        by simp
    qed
  qed
  have f2_consttype_altdef: "\<And>y. y \<in> Constant Tmod2 \<Longrightarrow> ConstType (f2 (tg_combine TG1 TG2)) y = ConstType (f2 (tg_combine TG1 (tg_combine TG2 TG3))) y"
  proof-
    fix y
    assume "y \<in> Constant Tmod2"
    then have "ConstType (f2 TG2) y = ConstType (f2 (tg_combine TG2 TG1)) y"
      using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.func_consttype
      by blast
    then have tmod1_tmod12: "ConstType (f2 TG2) y = ConstType (f2 (tg_combine TG1 TG2)) y"
      by simp
    assume "y \<in> Constant Tmod2"
    then have "ConstType (f2 TG2) y = ConstType (f2 (tg_combine TG2 (tg_combine TG1 TG3))) y"
      using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.func_consttype
      by blast
    then have tmod1_tmod123: "ConstType (f2 TG2) y = ConstType (f2 (tg_combine TG1 (tg_combine TG2 TG3))) y"
      using tg_combine_assoc tg_combine_commute
      by metis
    show "ConstType (f2 (tg_combine TG1 TG2)) y = ConstType (f2 (tg_combine TG1 (tg_combine TG2 TG3))) y"
      using tmod1_tmod12 tmod1_tmod123
      by simp
  qed
  assume "x \<in> Constant (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2))"
  then have "x \<in> {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1} \<union> {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2}"
    unfolding tmod_combine_mapping_def
    by simp
  then have "x \<in> {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1} \<inter> {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2} \<or>
    x \<in> {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1} - {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2} \<or>
    x \<in> {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2} - {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1}"
    by blast
  then have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = 
    tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x"
  proof (elim disjE)
    assume x_in_tg12: "x \<in> {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1} \<inter>
      {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2}"
    then have x_in_tg123: "x \<in> {f \<in> Constant (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod1} \<inter>
      {f \<in> Constant (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod2}"
      using constant_tmod1 constant_tmod2
      by simp
    then have x_in_constants: "x \<in> Constant Tmod1 \<inter> Constant Tmod2"
      by simp
    then show "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x =
      tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x"
    proof (induct "ConstType (f1 TG1) x = ConstType (f2 TG2) x")
      case True
      then have tg12_eq: "ConstType (f1 (tg_combine TG1 TG2)) x = ConstType (f2 (tg_combine TG1 TG2)) x"
        using IntD1 IntD2 mapping_tg1 mapping_tg2 tg_combine_commute tmod_combine_mapping_function.func_consttype tmod_combine_mapping_function.mapping_correct
        by metis
      then have tg123_eq: "ConstType (f1 (tg_combine (tg_combine TG1 TG2) TG3)) x = ConstType (f2 (tg_combine (tg_combine TG1 TG2) TG3)) x"
        using Int_iff f1_consttype_altdef f2_consttype_altdef tg_combine_assoc x_in_constants
        by metis
      have tg12_unfold: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = ConstType (f1 (tg_combine TG1 TG2)) x"
        unfolding tmod_combine_const_type_mapping_def
        using tg12_eq x_in_tg12
        by simp
      then have tg12_def: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = ConstType (f1 TG1) x"
        using IntD1 mapping_tg1 tmod_combine_mapping_function_def x_in_constants
        by metis
      have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = ConstType (f1 (tg_combine (tg_combine TG1 TG2) TG3)) x"
        unfolding tmod_combine_const_type_mapping_def
        using tg123_eq x_in_tg123
        by simp
      then have tg123_def: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = ConstType (f1 TG1) x"
        using IntD1 tg12_unfold f1_consttype_altdef f2_consttype_altdef tg12_def tg_combine_assoc x_in_constants
        by metis
      show ?case
        using tg12_def tg123_def
        by simp
    next
      case False
      then have tg12_not_eq: "ConstType (f1 (tg_combine TG1 TG2)) x \<noteq> ConstType (f2 (tg_combine TG1 TG2)) x"
        using IntD1 IntD2 mapping_tg1 mapping_tg2 tg_combine_commute tmod_combine_mapping_function.func_consttype tmod_combine_mapping_function.mapping_correct
        by metis
      then have tg123_not_eq: "ConstType (f1 (tg_combine (tg_combine TG1 TG2) TG3)) x \<noteq> ConstType (f2 (tg_combine (tg_combine TG1 TG2) TG3)) x"
        using Int_iff f1_consttype_altdef f2_consttype_altdef tg_combine_assoc x_in_constants
        by metis
      have tg12_def: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = invalid"
        unfolding tmod_combine_const_type_mapping_def
        using tg12_not_eq x_in_tg12
        by simp
      have tg123_def: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = invalid"
        unfolding tmod_combine_const_type_mapping_def
        using tg123_not_eq x_in_tg123
        by simp
      show ?case
        using tg12_def tg123_def
        by simp
    qed
  next
    assume "x \<in> {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1} - {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2}"
    then have x_in_constants_def: "x \<in> Constant Tmod1 - Constant Tmod2"
      using mapping_tg2 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_constant
      by fastforce
    assume "x \<in> {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1} - {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2}"
    then have tg12_unfold: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = ConstType (f1 (tg_combine TG1 TG2)) x"
      unfolding tmod_combine_const_type_mapping_def
      by auto
    then have tg12_def: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = ConstType (f1 TG1) x"
      using Diff_iff x_in_constants_def mapping_tg1 tmod_combine_mapping_function_def
      by metis
    assume "x \<in> {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1} - {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2}"
    then have "x \<in> {f \<in> Constant (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod1} - {f \<in> Constant (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod2}"
      using constant_tmod1 constant_tmod2
      by blast
    then have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = ConstType (f1 (tg_combine (tg_combine TG1 TG2) TG3)) x"
      unfolding tmod_combine_const_type_mapping_def
      by auto
    then have tg123_def: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = ConstType (f1 TG1) x"
      using Diff_iff f1_consttype_altdef tg12_def tg12_unfold tg_combine_assoc x_in_constants_def
      by metis
    show ?thesis
      using tg12_def tg123_def
      by simp
  next
    assume "x \<in> {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2} - {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1}"
    then have x_in_constants_def: "x \<in> Constant Tmod2 - Constant Tmod1"
      using mapping_tg1 tmod_combine_mapping_function.mapping_correct tmod_combine_mapping_function.subset_constant
      by fastforce
    assume "x \<in> {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2} - {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1}"
    then have tg12_unfold: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = ConstType (f2 (tg_combine TG1 TG2)) x"
      unfolding tmod_combine_const_type_mapping_def
      by auto
    then have tg12_def: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2) x = ConstType (f2 TG2) x"
      using Diff_iff mapping_tg2 tg_combine_commute tmod_combine_mapping_function_def x_in_constants_def
      by metis
    assume "x \<in> {f \<in> Constant (f2 (tg_combine TG1 TG2)). f \<in> Constant Tmod2} - {f \<in> Constant (f1 (tg_combine TG1 TG2)). f \<in> Constant Tmod1}"
    then have "x \<in> {f \<in> Constant (f2 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod2} - {f \<in> Constant (f1 (tg_combine (tg_combine TG1 TG2) TG3)). f \<in> Constant Tmod1}"
      using constant_tmod1 constant_tmod2
      by blast
    then have "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = ConstType (f2 (tg_combine (tg_combine TG1 TG2) TG3)) x"
      unfolding tmod_combine_const_type_mapping_def
      by auto
    then have tg123_def: "tmod_combine_const_type_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3) x = ConstType (f2 TG2) x"
      using Diff_iff f2_consttype_altdef tg12_def tg12_unfold tg_combine_assoc x_in_constants_def
      by metis
    show ?thesis
      using tg12_def tg123_def
      by simp
  qed
  then show "ConstType (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine TG1 TG2)) x =
    ConstType (tmod_combine_mapping f1 Tmod1 f2 Tmod2 (tg_combine (tg_combine TG1 TG2) TG3)) x"
    unfolding tmod_combine_mapping_def
    by simp
qed

definition tmod_empty_mapping :: "'lt type_graph \<Rightarrow> 'nt type_model" where
  "tmod_empty_mapping TG \<equiv> tmod_empty"

lemma tmod_empty_mapping_function[simp]: "tmod_combine_mapping_function tmod_empty_mapping tg_empty tmod_empty"
  unfolding tmod_empty_mapping_def tg_empty_def tmod_empty_def
  by (intro tmod_combine_mapping_function.intro) (simp_all)

end