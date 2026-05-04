import Riemann.Basic

open Real Complex SchwartzMap
open MeasureTheory
open scoped MeasureTheory

/-- **Définition II.1 — Espace de Schwartz.**

On adopte la définition standard de Mathlib :
`𝒮(ℝ) := SchwartzMap ℝ ℂ`. -/
abbrev SchwartzSpace : Type := SchwartzMap ℝ ℂ

@[inherit_doc]
notation "𝒮(ℝ)" => SchwartzSpace

/-- **Caractérisation (Définition II.1).**


Une fonction `f : ℝ → ℂ` est (sous-jacente à) un élément de `𝒮(ℝ)` si et
seulement si elle est `C∞` et, pour tout `(α, β) ∈ ℕ²`, la quantité
`‖x‖^α · ‖f^{(β)}(x)‖` est bornée uniformément en `x`. -/
theorem mem_schwartzSpace_iff (f : ℝ → ℂ) :
    (∃ g : 𝒮(ℝ), (g : ℝ → ℂ) = f) ↔
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ α β : ℕ, ∃ C : ℝ, ∀ x : ℝ,
        ‖x‖^α * ‖iteratedDeriv β f x‖ ≤ C := by
  constructor
  · -- Sens ⇒
    rintro ⟨g, rfl⟩
    refine ⟨g.smooth (⊤ : ℕ∞), ?_⟩
    intro α β
    obtain ⟨C, _hC_pos, hC⟩ := g.decay α β
    refine ⟨C, fun x => ?_⟩
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC x
  · -- Sens ⇐
    rintro ⟨hf_smooth, hf_decay⟩
    refine ⟨⟨f, hf_smooth, ?_⟩, rfl⟩
    intro k n
    obtain ⟨C, hC⟩ := hf_decay k n
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC x

lemma schwartz_oscillatory_integral_rapidDecay (φ : SchwartzMap ℝ ℂ) (N : ℕ) :
    ∃ C : ℝ, ∀ a : ℝ,
      ‖∫ t : ℝ, (φ : ℝ → ℂ) t * Complex.exp (I * a * t) ∂volume‖
        * (1 + |a|)^N ≤ C := by
  sorry
