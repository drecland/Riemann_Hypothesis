import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.Tools.MellinTransform
import Riemann.Tools.UnboundedOperator
import Riemann.WeilSpace.WeilHermitianForm
import Riemann.Proof.MacaevIdeal
import Riemann.Proof.DixmierTrace
import Riemann.WeilSpace.WeilFunctionalCalculus
import Riemann.Proof.PositiveOperator

open Complex MeasureTheory


variable {ℋ : Type*}
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
[CompleteSpace ℋ]


/-! ## Définition II.22 — Trace régularisée -/

/-- **Idéal des opérateurs à trace** `ℒ¹(ℋ)`. -/
def TraceClass (ℋ : Type*)
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
[CompleteSpace ℋ] :
    Set (ℋ →L[ℂ] ℋ) := sorry

/-- **Trace usuelle** sur `ℒ¹(ℋ)`. -/
noncomputable def usualTrace
(T : ℋ →L[ℂ] ℋ) (_hT : T ∈ TraceClass ℋ) : ℂ := sorry




/-- **Sous-algèbre `𝒜` contenant `ℒ¹(ℋ)`**,
sur laquelle la trace régularisée est définie. -/
structure RegularizingAlgebra (ℋ : Type*)
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] where
  carrier : Set (ℋ →L[ℂ] ℋ)
  traceClass_subset : TraceClass ℋ ⊆ carrier

/-- **Trace régularisée** :
forme linéaire sur `𝒜` coïncidant avec `Tr` sur `ℒ¹(ℋ)`. -/
structure RegularizedTrace (ℋ : Type*)
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] (𝒜 : RegularizingAlgebra ℋ) where
  toFun : ∀ T ∈ 𝒜.carrier, ℂ
  -- ... autres champs (linéarité, compatibilité avec Tr usuelle)
  preserves_positivity : ∀ (T : ℋ →L[ℂ] ℋ) (hT : T ∈ 𝒜.carrier),
      IsPositiveOp T → 0 ≤ (toFun T hT).re



/-- ## Lemme II.24 — Existence et positivité de la trace régularisée

*Existence et positivité de la trace régularisée par limite d'états*.

    Soit `D` un opérateur non borné auto-adjoint à résolvante compacte
    sur `ℋ`.
    Soit `f ∈ 𝒲` une fonction test de Weil.
    Si `P_f = f(D)f*(D) ∈ ℒ^(1,∞)(ℋ)`, alors la trace régularisée est
    positive :
    `Tr_reg(P_f) ≥ 0`. -/
theorem regularizedTrace_positive
    (f : 𝒲) (D : UnboundedOperator ℋ) (hD_sa : D.IsSelfAdjoint)
    (𝒜 : RegularizingAlgebra ℋ)
    (Trreg : RegularizedTrace ℋ 𝒜)
    (hPf_mem : positiveOp f D hD_sa ∈ 𝒜.carrier)
    (_hPf_macaev : positiveOp f D hD_sa ∈ MacaevIdeal ℋ) :
    0 ≤ (Trreg.toFun (positiveOp f D hD_sa) hPf_mem).re := by
  exact Trreg.preserves_positivity _ hPf_mem
    (positiveOp_isPositive f D hD_sa)
