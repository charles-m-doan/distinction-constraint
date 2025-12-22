theory Distinction_Constraint_Foundations_Minimal
  imports Main
begin

typedecl claim
typedecl obj
typedecl pred

locale DC_Foundations_Minimal =
  fixes
    Claim          :: "claim ⇒ bool"
    and Distinction    :: "claim ⇒ bool"
    and Meaningful     :: "claim ⇒ bool"
    and Applies        :: "pred ⇒ obj ⇒ claim"
    and HasAppCond     :: "pred ⇒ obj ⇒ bool"
    and PriorToAllDist :: "obj ⇒ bool"
    and Exists         :: pred
  assumes
    F1_Claim_requires_distinction:
      "Claim φ ⟹ Distinction φ"
    and Meaningful_implies_Claim:
      "Meaningful φ ⟹ Claim φ"
    and F2_Predication_requires_app_conditions:
      "Meaningful (Applies P x) ⟹ HasAppCond P x"
    and F3_PriorToAllDist_has_no_app_conditions:
      "PriorToAllDist x ⟹ (∀P. ¬ HasAppCond P x)"
begin

definition Real :: "obj ⇒ bool" where
  "Real x ⟷ (∃P. Meaningful (Applies P x))"

lemma L1_Meaningful_implies_Distinction:
  assumes "Meaningful φ"
  shows   "Distinction φ"
proof -
  have "Claim φ" using assms Meaningful_implies_Claim by blast
  thus "Distinction φ" using F1_Claim_requires_distinction by blast
qed

lemma L2_No_meaningful_predication_if_PriorToAllDist:
  assumes "PriorToAllDist x"
  shows   "¬ Meaningful (Applies P x)"
proof
  assume m: "Meaningful (Applies P x)"
  have h: "HasAppCond P x" using m F2_Predication_requires_app_conditions by blast
  have n: "∀Q. ¬ HasAppCond Q x" using assms F3_PriorToAllDist_has_no_app_conditions by blast
  from n have "¬ HasAppCond P x" by blast
  with h show False by blast
qed

lemma L2_1_No_meaningful_existence_if_PriorToAllDist:
  assumes "PriorToAllDist x"
  shows   "¬ Meaningful (Applies Exists x)"
  using assms L2_No_meaningful_predication_if_PriorToAllDist by blast

lemma L3_Not_Real_if_PriorToAllDist:
  assumes "PriorToAllDist x"
  shows   "¬ Real x"
proof
  assume "Real x"
  then obtain P where "Meaningful (Applies P x)"
    unfolding Real_def by blast
  thus False using assms L2_No_meaningful_predication_if_PriorToAllDist by blast
qed

lemma L4_No_reality_without_meaningful_predication:
  assumes "∀P. ¬ Meaningful (Applies P x)"
  shows   "¬ Real x"
  using assms unfolding Real_def by blast

lemma L5_PriorToAllDist_blocks_all_predication_attempts:
  assumes "PriorToAllDist x"
  shows   "∀P. ¬ Meaningful (Applies P x)"
  using assms L2_No_meaningful_predication_if_PriorToAllDist by blast

lemma L6_Reality_as_exhaustion_of_admissible:
  shows "Real x ⟷ (∃P. Meaningful (Applies P x))"
  unfolding Real_def by simp

end

end