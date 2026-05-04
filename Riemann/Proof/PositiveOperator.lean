import Riemann.Basic
import Riemann.Tools.UnboundedOperator
import Riemann.WeilSpace.WeilFunctionalCalculus

open Complex MeasureTheory


variable {ℋ : Type*}
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
[CompleteSpace ℋ]


variable (D : UnboundedOperator ℋ)
variable (hD_sa : D.IsSelfAdjoint) (hD_cr : D.HasCompactResolvent)

/-- **Opérateur positif** : `⟨T x, x⟩ ≥ 0` pour tout `x`. -/
def IsPositiveOp (T : ℋ →L[ℂ] ℋ) : Prop :=
  ∀ x : ℋ, 0 ≤ (@inner ℂ _ _ (T x) x).re

/-- **Opérateur positif `P_f = f(D) f*(D)`**. -/
noncomputable def positiveOp (f : 𝒲) (D : UnboundedOperator ℋ)
    (hD_sa : D.IsSelfAdjoint) : ℋ →L[ℂ] ℋ :=
  (WeilFunctionalCalculus f D hD_sa) *
    (WeilFunctionalCalculus (weilStarW f) D hD_sa)

/-- **Axiome** : `f*(D) = (f(D))*` -/
axiom weilStar_calculus_eq_adjoint (f : 𝒲) (D : UnboundedOperator ℋ)
    (hD_sa : D.IsSelfAdjoint) :
    WeilFunctionalCalculus (weilStarW f) D hD_sa =
      ContinuousLinearMap.adjoint (WeilFunctionalCalculus f D hD_sa)



/-- L'opérateur `P_f = f(D) ∘ f*(D)` est positif. -/
lemma positiveOp_isPositive (f : 𝒲) (D : UnboundedOperator ℋ)
    (hD_sa : D.IsSelfAdjoint) :
    IsPositiveOp (positiveOp f D hD_sa) := by
  intro x
  unfold positiveOp
  rw [weilStar_calculus_eq_adjoint f D hD_sa]
  -- But : 0 ≤ (⟨(A * A†) x, x⟩).re
  -- où A = WeilFunctionalCalculus f D hD_sa
  set A := WeilFunctionalCalculus f D hD_sa
  -- (A * A†) x = A (A† x)
  change 0 ≤ (@inner ℂ _ _ ((A * ContinuousLinearMap.adjoint A) x) x).re
  rw [ContinuousLinearMap.mul_apply]
  -- ⟨A (A† x), x⟩ = ⟨A† x, A† x⟩ par définition de l'adjoint
  rw [← ContinuousLinearMap.adjoint_inner_right A
  (ContinuousLinearMap.adjoint A x) x]
  -- But : 0 ≤ (⟨A† x, A† x⟩).re = ‖A† x‖²
  rw [inner_self_eq_norm_sq_to_K]
  have h : (0 : ℝ) ≤ ‖ContinuousLinearMap.adjoint A x‖ ^ 2 :=
  by positivity
  exact_mod_cast h
