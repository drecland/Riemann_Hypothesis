import Riemann.Basic
import Riemann.WeilSpace.WeilHermitianForm


open Complex MeasureTheory


variable {ℋ : Type*}
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
[CompleteSpace ℋ]


/-! ## Définition II.23 — Idéal de Macaev-/

/-- **Suite des valeurs singulières** d'un opérateur compact
(ordre décroissant). -/
noncomputable def singularValues (T : ℋ →L[ℂ] ℋ) : ℕ → ℝ := sorry

/-- **Idéal de Macaev** `ℒ^(1,∞)(ℋ)`. -/
def MacaevIdeal (ℋ : Type*)
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
[CompleteSpace ℋ] :
    Set (ℋ →L[ℂ] ℋ) :=
  { T | IsCompactOperator T ∧
        ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
          (1 / Real.log N) *
          (∑ n ∈ Finset.range N, singularValues T n) ≤ C }
