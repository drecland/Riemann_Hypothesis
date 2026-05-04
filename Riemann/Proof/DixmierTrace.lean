import Riemann.Basic
import Riemann.WeilSpace.WeilHermitianForm
import Riemann.Proof.MacaevIdeal
import Riemann.Proof.PositiveOperator

open Complex MeasureTheory


variable {ℋ : Type*}
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
[CompleteSpace ℋ]


/-! ## Définition II.23 — Trace de Dixmier -/
/-- **Trace de Dixmier** `Tr_ω` sur les opérateurs positifs
    de l'idéal de Macaev, construite via une limite de Banach `ω`. -/
noncomputable axiom dixmierTrace (T : ℋ →L[ℂ] ℋ)
    (_hT : T ∈ MacaevIdeal ℋ)
    (_hPos : ∀ x : ℋ, 0 ≤ (@inner ℂ _ _ (T x) x).re) : ℝ

axiom dixmierTrace_nonneg (T : ℋ →L[ℂ] ℋ)
    (hMac : T ∈ MacaevIdeal ℋ)
    (hPos : IsPositiveOp T) :
    0 ≤ dixmierTrace T hMac hPos

/-- Si deux opérateurs sont égaux,
leurs traces de Dixmier coïncident. -/
lemma dixmierTrace_congr
    {T₁ T₂ : ℋ →L[ℂ] ℋ} (hT : T₁ = T₂)
    (h₁ : T₁ ∈ MacaevIdeal ℋ) (h₂ : T₂ ∈ MacaevIdeal ℋ)
    (hp₁ : ∀ x : ℋ, 0 ≤ (@inner ℂ _ _ (T₁ x) x).re)
    (hp₂ : ∀ x : ℋ, 0 ≤ (@inner ℂ _ _ (T₂ x) x).re) :
    dixmierTrace T₁ h₁ hp₁ = dixmierTrace T₂ h₂ hp₂ := by
  subst hT; rfl
