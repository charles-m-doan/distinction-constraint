theory DistinctionConstraint
  imports Main
begin

typedecl Thing
consts Applies :: "(Thing \<Rightarrow> bool) \<Rightarrow> Thing \<Rightarrow> bool"

definition DC_Det :: bool where
  "DC_Det \<longleftrightarrow> (\<exists>P x. Applies P x) \<and> (\<exists>Q y. \<not> Applies Q y)"

definition DC_Dist :: bool where
  "DC_Dist \<longleftrightarrow> (\<exists>x y :: Thing. x \<noteq> y)"

axiomatization where
  DC_bridge:
    "((\<exists>P x. Applies P x) \<and> (\<exists>Q y. \<not> Applies Q y)) \<longrightarrow> (\<exists>x y :: Thing. x \<noteq> y)"

lemma det_implies_dist: "DC_Det \<longrightarrow> DC_Dist"
  by (simp add: DC_Det_def DC_Dist_def DC_bridge)

end
