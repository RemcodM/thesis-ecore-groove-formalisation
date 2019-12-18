theory Extended_Graph_Theory
  imports 
    Main
    Graph_Theory.Arc_Walk
begin

section "Additional theorems for the Graph Theory library"

text \<open>
  This section contains lemmas that are not directly related to GROOVE graphs but are
  relevant for directed graphs in Graph Theory. It is very similar to the 'Stuff' theory 
  included with Graph Theory, but then with theorems that could be interesting for
  Graph Theory.
\<close>

inductive_set (in wf_digraph) awalks :: "'b awalk set"
  where
    rule_awalks: "\<And>u v p. awalk u p v \<Longrightarrow> p \<in> awalks"

inductive (in wf_digraph) awalk_altdef :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool"
  where
    rule_awalk_empty_walk: "\<And>u. u \<in> verts G \<Longrightarrow> awalk_altdef u [] u" |
    rule_awalk_first_edge: "\<And>a. a \<in> arcs G \<Longrightarrow> awalk_altdef (tail G a) [a] (head G a)" |
    rule_awalk_add_edge: "\<And>p ps a v. awalk_altdef (tail G p) (p # ps) v \<Longrightarrow> a \<in> arcs G \<Longrightarrow> 
      head G a = tail G p \<Longrightarrow> awalk_altdef (tail G a) (a # p # ps) v"

lemma (in wf_digraph) awalk_altdef_correct:
  shows "\<And>u p v. awalk u p v = awalk_altdef u p v"
proof
  fix u p v
  assume awalk_valid: "awalk u p v"
  have "\<And>u v. awalk u p v \<Longrightarrow> awalk_altdef u p v"
  proof (induct p)
    case Nil
    then show ?case
      using wf_digraph.rule_awalk_empty_walk wf_digraph_axioms 
      by fastforce
  next
    case (Cons p1 ps)
    then show ?case
    proof (induct ps)
      case Nil
      show ?case
        using Nil.prems(2) awalk_Cons_iff rule_awalk_first_edge
        by fastforce
    next
      case (Cons p2 ps)
      then have "awalk (tail G p2) (p2 # ps) v"
        by (simp add: awalk_Cons_iff)
      then show ?case
        using Cons.prems(1) Cons.prems(2) awalk_Cons_iff rule_awalk_add_edge
        by fastforce
    qed
  qed
  then show "awalk_altdef u p v"
    using awalk_valid
    by simp
next
  fix u p v
  assume "awalk_altdef u p v"
  then show "awalk u p v"
  proof (induct rule: awalk_altdef.induct)
    case (rule_awalk_empty_walk u)
    then show ?case
      by (simp add: awalk_Nil_iff)
  next
    case (rule_awalk_first_edge a)
    then show ?case
      by (fact arc_implies_awalk)
  next
    case (rule_awalk_add_edge p ps a v)
    then show ?case
      by (simp add: awalk_Cons_iff)
  qed
qed

inductive_set (in wf_digraph) apaths :: "'b awalk set"
  where
    rule_apaths: "\<And>u v p. apath u p v \<Longrightarrow> p \<in> apaths"

inductive (in wf_digraph) apath_altdef :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool"
  where
    rule_apath_empty_walk: "\<And>u. u \<in> verts G \<Longrightarrow> apath_altdef u [] u" |
    rule_apath_first_edge: "\<And>a. a \<in> arcs G \<Longrightarrow> tail G a \<noteq> head G a \<Longrightarrow> apath_altdef (tail G a) [a] (head G a)" |
    rule_apath_add_edge: "\<And>p ps a v. apath_altdef (tail G p) (p # ps) v \<Longrightarrow> a \<in> arcs G \<Longrightarrow> 
      head G a = tail G p \<Longrightarrow> tail G a \<notin> set (awalk_verts (tail G p) (p # ps)) \<Longrightarrow> apath_altdef (tail G a) (a # p # ps) v"

lemma (in wf_digraph) apath_altdef_correct:
  shows "\<And>u p v. apath u p v = apath_altdef u p v"
proof
  fix u p v
  assume apath_valid: "apath u p v"
  have "\<And>u v. apath u p v \<Longrightarrow> apath_altdef u p v"
  proof (induct p)
    case Nil
    then show ?case
      using wf_digraph.rule_apath_empty_walk wf_digraph_axioms apath_Nil_iff
      by fastforce
  next
    case (Cons p1 ps)
    then show ?case
    proof (induct ps)
      case Nil
      then have "u \<noteq> v"
        using apath_nonempty_ends
        by blast
      then show ?case
        using Nil.prems(2) apath_Cons_iff apath_Nil_iff rule_apath_first_edge
        by fastforce
    next
      case (Cons p2 ps)
      then have "apath (tail G p2) (p2 # ps) v"
        using apath_Cons_iff
        by fastforce
      then show ?case
        using Cons.prems(1) Cons.prems(2) apath_Cons_iff rule_apath_add_edge
        by fastforce
    qed
  qed
  then show "apath_altdef u p v"
    using apath_valid
    by simp
next
  fix u p v
  assume "apath_altdef u p v"
  then show "apath u p v"
  proof (induct rule: apath_altdef.induct)
    case (rule_apath_empty_walk u)
    then show ?case
      by (simp add: apath_Nil_iff)
  next
    case (rule_apath_first_edge a)
    then show ?case
      by (simp add: apath_Cons_iff wf_digraph.apath_Nil_iff wf_digraph_axioms)
  next
    case (rule_apath_add_edge p ps a v)
    then show ?case
      by (simp add: apath_Cons_iff)
  qed
qed

lemma (in wf_digraph) all_apaths_are_awalks: "apaths \<subseteq> awalks"
proof
  fix x
  assume "x \<in> apaths"
  then show "x \<in> awalks"
  proof (induct x)
    case (rule_apaths u v p)
    then have "apath_altdef u p v"
      by (simp add: apath_altdef_correct)
    then show ?case
    proof (induct)
      case (rule_apath_empty_walk u)
      then show ?case
        using awalk_Nil_iff awalks.rule_awalks
        by simp
    next
      case (rule_apath_first_edge a)
      then show ?case
        using arc_implies_awalk awalks.rule_awalks
        by blast
    next
      case (rule_apath_add_edge p ps a v)
      then have "awalk_altdef (tail G a) (a # p # ps) v"
        using apath_altdef_correct awalkI_apath awalk_altdef_correct rule_awalk_add_edge
        by blast
      then show ?case
        using awalk_altdef_correct awalks.rule_awalks
        by simp
    qed
  qed
qed

definition (in pre_digraph) arc_to_tuple :: "'b \<Rightarrow> 'a \<times> 'a" where
  "arc_to_tuple a \<equiv> (head G a, tail G a)"

lemma (in wf_digraph) edge_in_arc_to_tuple_is_edge:
  shows "\<And>x y. (x, y) \<in> arc_to_tuple ` arcs G \<Longrightarrow> \<exists>a. head G a = x \<and> tail G a = y \<and> a \<in> arcs G"
  using arc_to_tuple_def
  by auto

lemma (in wf_digraph) edge_in_arc_to_tuple_head_vertice:
  shows "\<And>x y. (x, y) \<in> (arc_to_tuple ` arcs G)\<^sup>+ \<Longrightarrow> x \<in> verts G"
proof-
  fix x y
  assume "(x, y) \<in> (arc_to_tuple ` arcs G)\<^sup>+"
  then show "x \<in> verts G"
  proof (induct)
    case (base a)
    then show ?case
      using edge_in_arc_to_tuple_is_edge head_in_verts
      by blast
  next
    case (step a b)
    then show ?case
      by blast
  qed
qed

lemma (in wf_digraph) edge_in_arc_to_tuple_tail_vertice:
  shows "\<And>x y. (x, y) \<in> (arc_to_tuple ` arcs G)\<^sup>+ \<Longrightarrow> y \<in> verts G"
proof-
  fix x y
  assume "(x, y) \<in> (arc_to_tuple ` arcs G)\<^sup>+"
  then show "y \<in> verts G"
  proof (induct)
    case (base a)
    then show ?case
      using edge_in_arc_to_tuple_is_edge tail_in_verts
      by blast
  next
    case (step a b)
    then show ?case
      using edge_in_arc_to_tuple_is_edge tail_in_verts
      by blast
  qed
qed

primrec awalk_subset :: "'b \<Rightarrow> 'b awalk \<Rightarrow> 'b awalk" where
  "awalk_subset q [] = []" |
  "awalk_subset q (e # es) = (if e = q then [e] else e # awalk_subset q es)"

lemma (in wf_digraph) non_distinct_awalk_impl_shorter_walk:
  shows "\<And>u v w. p \<noteq> [] \<Longrightarrow> apath u p v \<Longrightarrow> awalk v [q] w \<Longrightarrow> \<not>distinct (tl (awalk_verts u (q#p))) \<Longrightarrow> apath u (awalk_subset q p) w"
proof-
  fix u v w
  assume p_not_empty: "p \<noteq> []"
  assume apath_p: "apath u p v"
  then have apath_altdef: "apath_altdef u p v"
    by (simp add: apath_altdef_correct)
  have awalk_p: "awalk u p v"
    using apath_p
    unfolding apath_def
    by simp
  have distinct_awalk_p: "distinct (awalk_verts u p)"
    using apath_p
    unfolding apath_def
    by simp
  assume "awalk v [q] w"
  then have awalk_q: "awalk_altdef v [q] w"
    by (simp add: awalk_altdef_correct)
  assume non_distinct_awalk_qp: "\<not>distinct (tl (awalk_verts u (q#p)))"
  then have "q \<in> set p"
    using awalk_verts.simps(2) awalk_verts_ne_eq distinct_awalk_p list.sel(3) p_not_empty
    by metis
  show "apath u (awalk_subset q p) w"
    using awalk_verts.simps(2) awalk_verts_ne_eq distinct_awalk_p list.sel(3) non_distinct_awalk_qp p_not_empty
    by metis
qed

lemma (in wf_digraph) tail_distinct_awalk_impl_shorter_path:
  shows "\<And>u v. apath u p v \<Longrightarrow> apath v [q] u \<Longrightarrow> cycle (q # p)"
proof-
  fix u v
  assume apath_uv: "apath u p v"
  assume apath_vu: "apath v [q] u"
  show "cycle (q # p)"
    unfolding cycle_def
    using apath_def apath_uv apath_vu awalk_Cons_iff
    by auto
qed

lemma (in wf_digraph) awalk_impl_rtrancl: 
  shows "\<And>u v. awalk u p v \<Longrightarrow> (v, u) \<in> (arc_to_tuple ` arcs G)\<^sup>*"
proof (induct p)
  case Nil
  then show ?case
    by auto
next
  case (Cons a p)
  then have shorter_walk: "awalk (head G a) p v"
    by (simp add: awalk_Cons_iff)
  have "(head G a, u) \<in> (arc_to_tuple ` arcs G)\<^sup>*"
    using Cons.prems arc_to_tuple_def awalk_Cons_iff 
    by auto
  then show ?case
    using Cons.hyps rtrancl_trans shorter_walk
    by metis
qed

lemma (in wf_digraph) no_rtrancl_impl_no_awalk: 
  shows "\<And>u v. (v, u) \<notin> (arc_to_tuple ` arcs G)\<^sup>* \<Longrightarrow> \<not>awalk u p v"
  using awalk_impl_rtrancl 
  by blast

lemma (in wf_digraph) rtrancl_impl_awalk:
  shows "\<And>u v. u \<in> verts G \<Longrightarrow> v \<in> verts G \<Longrightarrow> (v, u) \<in> (arc_to_tuple ` arcs G)\<^sup>* \<Longrightarrow> \<exists>p. awalk u p v"
proof-
  fix u v
  assume u_in_verts: "u \<in> verts G"
  assume v_in_verts: "v \<in> verts G"
  assume "(v, u) \<in> (arc_to_tuple ` arcs G)\<^sup>*"
  then have "\<exists>p. awalk_altdef u p v"
  proof (induct)
    case base
    then show ?case
      using rule_awalk_empty_walk v_in_verts
      by blast
  next
    case (step y z)
    then have "\<exists>p. awalk_altdef z p y"
      using arc_to_tuple_def rule_awalk_first_edge
      by fastforce
    then show ?case
      using step.hyps(3) awalk_altdef_correct reachable_awalk reachable_trans
      by metis
  qed
  then show "\<exists>p. awalk u p v"
    by (simp add: awalk_altdef_correct)
qed

lemma (in wf_digraph) no_awalk_impl_no_rtrancl: 
  shows "\<And>u v. u \<in> verts G \<Longrightarrow> v \<in> verts G \<Longrightarrow> \<forall>p. \<not>awalk u p v \<Longrightarrow> (v, u) \<notin> (arc_to_tuple ` arcs G)\<^sup>*"
  using rtrancl_impl_awalk
  by blast

inductive_set (in wf_digraph) cycles :: "'b awalk set"
  where
    rule_cycles: "\<And>u p. awalk u p u \<Longrightarrow> p \<noteq> [] \<Longrightarrow> distinct (tl (awalk_verts u p)) \<Longrightarrow> p \<in> cycles"

lemma (in wf_digraph) all_cycles_are_awalks: "cycles \<subseteq> awalks"
proof
  fix x
  assume "x \<in> cycles"
  then show "x \<in> awalks"
    using awalks.rule_awalks cycles.cases
    by metis
qed

lemma (in wf_digraph) valid_cycle_in_cycles: "\<And>p. p \<in> cycles \<longleftrightarrow> cycle p"
proof
  fix p
  assume "p \<in> cycles"
  then show "cycle p"
  proof (induct)
    case (rule_cycles u p)
    then show ?case
      using pre_digraph.cycle_def 
      by blast
  qed
next
  fix p
  assume "cycle p"
  then show "p \<in> cycles"
    using pre_digraph.cycle_def wf_digraph.cycles.simps wf_digraph_axioms
    by metis
qed

lemma (in wf_digraph) non_empty_awalk_impl_trancl:
  shows "\<And>u v. p \<noteq> [] \<Longrightarrow> awalk u p v \<Longrightarrow> (v, u) \<in> (arc_to_tuple ` arcs G)\<^sup>+"
proof (induct p)
  case Nil
  then show ?case
    by simp
next
  case (Cons a p)
  then have shorter_walk: "awalk (head G a) p v"
    by (simp add: awalk_Cons_iff)
  have "(head G a, u) \<in> (arc_to_tuple ` arcs G)\<^sup>*"
    using Cons.prems(2) arc_implies_awalk awalk_Cons_iff wf_digraph.awalk_impl_rtrancl wf_digraph_axioms
    by metis
  then show ?case
    using Cons.prems(2) awalk_Cons_iff no_rtrancl_impl_no_awalk pre_digraph.arc_to_tuple_def 
    using rev_image_eqI rtrancl_eq_or_trancl trancl.r_into_trancl trancl_rtrancl_trancl
    by metis
qed

lemma (in wf_digraph) no_trancl_impl_no_non_empty_awalk:
  shows "\<And>u v. p \<noteq> [] \<Longrightarrow> (v, u) \<notin> (arc_to_tuple ` arcs G)\<^sup>+ \<Longrightarrow> \<not>awalk u p v"
  using non_empty_awalk_impl_trancl
  by blast

lemma (in wf_digraph) trancl_impl_awalk:
  shows "\<And>u v. (v, u) \<in> (arc_to_tuple ` arcs G)\<^sup>+ \<Longrightarrow> \<exists>p. awalk u p v"
proof-
  fix u v
  assume "(v, u) \<in> (arc_to_tuple ` arcs G)\<^sup>+"
  then have "\<exists>p. awalk_altdef u p v"
  proof (induct)
    case (base y)
    then show ?case
      using arc_to_tuple_def rule_awalk_first_edge
      by fastforce
  next
    case (step y z)
    then have "\<exists>p. p \<noteq> [] \<and> awalk_altdef z p y"
      using arc_to_tuple_def rule_awalk_first_edge
      by fastforce
    then have awalk_z_y: "\<exists>p. p \<noteq> [] \<and> awalk z p y"
      by (simp add: awalk_altdef_correct)
    have "\<exists>p. awalk y p v"
      using step.hyps(3)
      by (simp add: awalk_altdef_correct)
    then have "\<exists>p. awalk z p v"
      using awalk_z_y awalk_appendI
      by blast
    then show ?case
      by (simp add: awalk_altdef_correct)
  qed
  then show "\<exists>p. awalk u p v"
    by (simp add: awalk_altdef_correct)
qed

lemma (in wf_digraph) no_awalk_impl_no_trancl:
  shows "\<And>u v. \<forall>p. \<not>awalk u p v \<Longrightarrow> (v, u) \<notin> (arc_to_tuple ` arcs G)\<^sup>+"
  using trancl_impl_awalk
  by blast

lemma (in wf_digraph) irrefl_trancl_impl_apath:
  shows "\<And>u v. (v, u) \<in> (arc_to_tuple ` arcs G)\<^sup>+ \<Longrightarrow> irrefl ((arc_to_tuple ` arcs G)\<^sup>+) \<Longrightarrow> \<exists>p. apath u p v"
proof-
  fix u v
  assume irrefl_edges: "irrefl ((arc_to_tuple ` arcs G)\<^sup>+)"
  assume "(v, u) \<in> (arc_to_tuple ` arcs G)\<^sup>+"
  then have "\<exists>p. apath_altdef u p v"
    using irrefl_edges
  proof (induct)
    case (base y)
    then have "irrefl (arc_to_tuple ` arcs G)"
      unfolding irrefl_def
      by blast
    then have "v \<noteq> y"
      unfolding irrefl_def
      using base.hyps
      by blast
    then show ?case
      using base.hyps arc_to_tuple_def rule_apath_first_edge
      by fastforce
  next
    case (step y z)
    then have "irrefl (arc_to_tuple ` arcs G)"
      unfolding irrefl_def
      by blast
    then have "y \<noteq> z"
      unfolding irrefl_def
      using step.hyps
      by blast
    then have zy_apath: "\<exists>p. apath_altdef z p y"
      using step.hyps arc_to_tuple_def rule_apath_first_edge
      by fastforce
    have yv_apath: "\<exists>p. apath_altdef y p v"
      using step.hyps step.prems
      by blast
    then show ?case
      using zy_apath apath_altdef_correct reachable_apath reachable_trans
      by metis
  qed
  then show "\<exists>p. apath u p v"
    by (simp add: apath_altdef_correct)
qed

lemma (in wf_digraph) no_apath_impl_no_irrefl_trancl:
  shows "\<And>u v. (v, u) \<in> (arc_to_tuple ` arcs G)\<^sup>+ \<Longrightarrow> \<forall>p. \<not>apath u p v \<Longrightarrow> \<not>irrefl ((arc_to_tuple ` arcs G)\<^sup>+)"
  using irrefl_trancl_impl_apath
  by blast

lemma (in wf_digraph) loop_edge_trancl_impl_cyclic_awalk: "(u, u) \<in> arc_to_tuple ` arcs G \<Longrightarrow> \<exists>p. p \<noteq> [] \<and> awalk u p u"
proof-
  fix u
  assume edge_def: "(u, u) \<in> arc_to_tuple ` arcs G"
  then have "u \<in> verts G"
  proof
    fix x
    assume "(u, u) = arc_to_tuple x"
    then have u_is_head_x: "u = head G x"
      using arc_to_tuple_def
      by simp
    assume x_in_arcs: "x \<in> arcs G"
    then have "head G x \<in> verts G"
      by simp
    then show "u \<in> verts G"
      by (simp add: u_is_head_x)
  qed
  have "\<exists>a. head G a = u \<and> tail G a = u \<and> awalk u [a] u"
    using edge_def arc_implies_awalk edge_in_arc_to_tuple_is_edge
    by metis
  then show "\<exists>p. p \<noteq> [] \<and> awalk u p u"
    by blast
qed

lemma (in wf_digraph) non_irrefl_trancl_impl_cyclic_awalk: "\<not>irrefl ((arc_to_tuple ` arcs G)\<^sup>+) \<Longrightarrow> \<exists>p v. p \<noteq> [] \<and> awalk v p v"
proof-
  assume "\<not>irrefl ((arc_to_tuple ` arcs G)\<^sup>+)"
  then have "\<exists>u. (u, u) \<in> (arc_to_tuple ` arcs G)\<^sup>+"
    using irrefl_def
    by blast
  then have "\<exists>u v. (u, u) \<in> arc_to_tuple ` arcs G \<or> (u, v) \<in> (arc_to_tuple ` arcs G)\<^sup>+ \<and> (v, u) \<in> arc_to_tuple ` arcs G"
    using tranclE
    by metis
  then show "\<exists>p v. p \<noteq> [] \<and> awalk v p v"
    using loop_edge_trancl_impl_cyclic_awalk reachable1_awalk reachable_awalkI reachable_neq_reachable1 reachable_reachable1_trans trancl.r_into_trancl trancl_impl_awalk
    by metis
qed

lemma (in wf_digraph) no_cyclic_awalk_impl_no_cycle: "(\<And>p v. \<not>awalk v p v) \<Longrightarrow> \<not>cycle p"
  unfolding cycle_def
  by simp

lemma (in wf_digraph) no_cycle_impl_no_cyclic_awalk: "(\<And>p. \<not>cycle p) \<Longrightarrow> p \<noteq> [] \<Longrightarrow> \<not>awalk v p v"
  unfolding cycle_def
proof-
  assume no_cycle_def: "\<And>p. \<nexists>u. awalk u p u \<and> distinct (tl (awalk_verts u p)) \<and> p \<noteq> []"
  then have "\<And>p u. \<not>awalk u p u \<or> \<not>distinct (tl (awalk_verts u p)) \<or> p = []"
    by simp
  assume "p \<noteq> []"
  then show "\<not>awalk v p v"
    using no_cycle_def awalk_cyc_decompE' closed_w_imp_cycle cycle_conv distinct_tl
    by metis
qed

lemma (in wf_digraph) no_cyclic_awalk_impl_irrefl_trancl: "(\<And>p v. p = [] \<or> \<not>awalk v p v) \<Longrightarrow> irrefl ((arc_to_tuple ` arcs G)\<^sup>+)"
  using non_irrefl_trancl_impl_cyclic_awalk
  by blast

lemma (in wf_digraph) acyclic_impl_irrefl_trancl: "(\<And>p. \<not>cycle p) \<Longrightarrow> irrefl ((arc_to_tuple ` arcs G)\<^sup>+)"
proof (intro no_cyclic_awalk_impl_irrefl_trancl)
  fix p v
  assume no_cycles: "\<And>p. \<not>cycle p"
  then show "p = [] \<or> \<not>awalk v p v"
    unfolding cycle_def
    using no_cycle_impl_no_cyclic_awalk no_cycles
    by blast
qed

lemma (in wf_digraph) irrefl_trancl_impl_acyclic:
  shows "\<And>p. irrefl ((arc_to_tuple ` arcs G)\<^sup>+) \<Longrightarrow> \<not>cycle p"
  unfolding cycle_def
  using irrefl_def non_empty_awalk_impl_trancl
  by metis

lemma (in wf_digraph) cycle_impl_not_irrefl_trancl:
  shows "cycle p \<Longrightarrow> \<not>irrefl ((arc_to_tuple ` arcs G)\<^sup>+)"
  using irrefl_trancl_impl_acyclic 
  by blast

end