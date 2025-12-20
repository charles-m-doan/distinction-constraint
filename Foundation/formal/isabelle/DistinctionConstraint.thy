theory DistinctionConstraint
  imports Main
begin

typedecl Thing
consts Applies :: "(Thing \<Rightarrow> bool) \<Rightarrow> Thing \<Rightarrow> bool"

definition DC_Det :: bool where
  "DC_Det \<longleftrightarrow> (\<exists>P x. Applies P x \<and> \<not> Applies P x)"

definition DC_Dist :: bool where
  "DC_Dist \<longleftrightarrow> (\<exists>x y :: Thing. x \<noteq> y)"


lemma det_implies_dist: "DC_Det \<longrightarrow> DC_Dist"
proof
  assume h: DC_Det
  show DC_Dist sorry
qed

end
