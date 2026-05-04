import Riemann.Basic
import Riemann.Tools.SchwartzSpace
import Riemann.Tools.MellinTransform
import Riemann.WeilSpace.WeilSpace
import Riemann.WeilSpace.WeilRapidDecayPos

open Real Complex SchwartzMap
open MeasureTheory
open scoped MeasureTheory


/-- La fonction `t ↦ f(eᵗ) · e^{-t/2}` appartient à 𝒮(ℝ). -/
lemma weil_times_exp_half_schwartz (f : 𝒲) :
    ∃ φ : SchwartzMap ℝ ℂ, ∀ t : ℝ,
      (φ : ℝ → ℂ) t = (WeilSpace.toFun f) (Real.exp t) *
                       Complex.exp (-(t : ℂ) / 2) := by
  sorry

/-- Pour `f ∈ 𝒲`, la fonction `t ↦ f(eᵗ) · e^{t/2}` est Schwartz.
    Ceci utilise la décroissance rapide de `f` en tant que fonction de Schwartz :
    `f(x) = O(x⁻ᴺ)` pour tout `N`, ce qui compense la croissance de `e^{t/2}`. -/
lemma weil_times_exp_plus_half_schwartz (f : 𝒲) :
    ∃ ψ : SchwartzMap ℝ ℂ, ∀ t : ℝ,
      (ψ : ℝ → ℂ) t = (WeilSpace.toFun f) (Real.exp t) *
                       Complex.exp ((t : ℂ) / 2) := by
  refine ⟨{
    toFun := fun t => (WeilSpace.toFun f) (Real.exp t) *
                      Complex.exp ((t : ℂ) / 2)
    smooth' := ?_
    decay' := ?_ }, ?_⟩
  · -- Lissité
    sorry
  · -- Décroissance : on utilise weil_rapid_decay_pos
    -- Pour t → +∞ : |f(eᵗ)| ≤ C · e^{-Nt}, donc |f(eᵗ)·e^{t/2}| ≤ C·e^{-(N-1/2)t} → 0
    -- Pour t → -∞ : e^{t/2} → 0, et f bornée
    intro k n
    obtain ⟨C, _hC, hbound⟩ := weil_rapid_decay_pos f (k + n + 2)
    sorry
  · intro t
    rfl
