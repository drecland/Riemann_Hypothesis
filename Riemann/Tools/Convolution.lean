import Riemann.Basic
import Riemann.Tools.HaarMeasure

open MeasureTheory Complex Real
open scoped MeasureTheory


/-- **Convolution multiplicative** sur `ℝ*₊` :
`(f ⋆ g)(x) = ∫₀^∞ f(x/y) · g(y) · dy/y`. -/
noncomputable def mulConv (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∫ y in Set.Ioi (0:ℝ), f (x / y) * g y ∂haarMul

@[inherit_doc]
infixl:70 " ⋆ₘ " => mulConv


/-- **Définition** : involution de convolution sur `ℝ*₊`,
    `f*(x) = x⁻¹ · conj(f(x⁻¹))`. -/
noncomputable def convStar (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (x : ℂ)⁻¹ * star (f x⁻¹)

/-- La norme de la dérivée itérée de `star ∘ f ∘ neg` au point `t`
    égale celle de `D^n f` au point `-t`. -/
lemma norm_iteratedFDeriv_star_comp_neg
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n (fun s : ℝ => star (f (-s))) t‖
      = ‖iteratedFDeriv ℝ n f (-t)‖ := by
  have hfneg : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => f (-s)) t := by
    have heq : (fun s : ℝ => f (-s)) = f ∘ fun s : ℝ => -s := by ext; rfl
    rw [heq]
    exact (hf.comp contDiff_neg).contDiffAt
  have key1 : ‖iteratedFDeriv ℝ n (fun s : ℝ => star (f (-s))) t‖
            = ‖iteratedFDeriv ℝ n (fun s : ℝ => f (-s)) t‖ := by
    have heq : (fun s : ℝ => star (f (-s)))
             = ⇑Complex.conjLIE ∘ (fun s : ℝ => f (-s)) := by ext; rfl
    rw [heq]
    exact Complex.conjLIE.toLinearIsometry.norm_iteratedFDeriv_comp_left
            hfneg (by exact_mod_cast le_top)
  have key2 : ‖iteratedFDeriv ℝ n (fun s : ℝ => f (-s)) t‖
            = ‖iteratedFDeriv ℝ n f (-t)‖ := by
    have heq : (fun s : ℝ => f (-s))
             = f ∘ ⇑(LinearIsometryEquiv.neg ℝ (E := ℝ)) := by ext; rfl
    rw [heq]
    exact (LinearIsometryEquiv.neg ℝ (E := ℝ)).norm_iteratedFDeriv_comp_right f t n
  rw [key1, key2]


-- Lemme 1 : pousser star sous l'intégrale restreinte
lemma star_integral_restrict {s : Set ℝ} (_hs : MeasurableSet s)
    (g : ℝ → ℂ) (μ : Measure ℝ) :
    star (∫ y in s, g y ∂μ) =
    ∫ y in s, star (g y) ∂μ := by
  change starRingEnd ℂ _ = ∫ y in s, starRingEnd ℂ (g y) ∂μ
  exact (integral_conj).symm


-- Lemme 2 : star(a * (b * star c)) = star(a) * (b * c)
-- quand b est réel (b = ↑(r : ℝ))
lemma star_mul_real_mul_star (a c : ℂ) (r : ℝ) :
    star (a * (↑r * star c)) = star a * (↑r * c) := by
  simp [star_mul, RCLike.star_def]
  ring

/-- **Convolution additive** sur `ℝ` (mesure de Lebesgue) :
    `(f ∗ g)(t) = ∫_ℝ f(t - s) · g(s) ds`.

    Reliée à `mulConv` via l'isométrie `J(f) = f ∘ exp` :
    `J(f ⋆ₘ g) = J(f) ∗ J(g)`. -/
noncomputable def addConv (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ∫ s : ℝ, f (t - s) * g s

@[inherit_doc]
infixl:70 " ⋆ₐ " => addConv
