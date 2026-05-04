import Riemann.Basic
import Riemann.Tools.HaarMeasure
-- Refaire les import lorsque le lemme sera à faire


/- Nécessite :

hcv_rhs_inv
hcv_lhs_mul

/-- **Symétrie de Weil** :
    `(f ⋆ₘ f⁎)(1/x) = ↑x · star((f ⋆ₘ f⁎)(x))`. -/
lemma conv_self_star_symmetry (f : ℝ → ℂ) (hf : Measurable f)
    (x : ℝ) (hx : 0 < x) :
    (f ⋆ₘ (weilStarInvolution f)) (1/x) =
    (x : ℂ) * star ((f ⋆ₘ (weilStarInvolution f)) x) := by
  unfold mulConv weilStarInvolution
  -- Étape 1 : pousser star sous l'intégrale du RHS
  rw [star_integral_restrict measurableSet_Ioi]
  -- Étape 2 : simplifier star dans l'intégrande du RHS
  simp_rw [star_mul, star_star]
  try simp_rw [RCLike.star_def, Complex.conj_ofReal]
  -- Réassocier les produits pour matcher les lemmes hcv_*
  simp_rw [← mul_assoc]
  -- Étape 3 : CV y ↦ 1/y dans LHS
  rw [hcv_lhs_inv f hf x hx]
    -- Étape 4 : réordonner RHS puis CV y ↦ 1/y
  have hrhs_reorder : ∫ y in Set.Ioi (0:ℝ),
      f (1/y) * star (1/(↑y:ℂ)) * star (f (x/y)) ∂haarMul =
    ∫ y in Set.Ioi (0:ℝ),
      star (f (x/y)) * (1/(↑y:ℂ)) * f (1/y) ∂haarMul := by
    congr 1; ext y
    simp [RCLike.star_def, Complex.conj_ofReal]
    ring
  rw [hrhs_reorder]
  rw [hcv_rhs_inv f hf x hx]
  -- Étape 5 : CV y ↦ xy dans LHS
  rw [hcv_lhs_mul f hf x hx]
  -- Étape 6 : sortir ↑x et conclure
  have : ↑x * ∫ y in Set.Ioi (0:ℝ), star (f (x*y)) * ↑y * f y ∂haarMul =
         ∫ y in Set.Ioi (0:ℝ), (↑x : ℂ) * (star (f (x*y)) * ↑y * f y) ∂haarMul :=
    (MeasureTheory.integral_const_mul (↑x : ℂ) _).symm
  rw [this]
  congr 1; ext y
  push_cast
  ring
-/
