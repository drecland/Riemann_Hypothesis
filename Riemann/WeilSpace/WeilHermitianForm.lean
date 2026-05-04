import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.Tools.MellinTransform
import Riemann.Tools.EulerMascheroni
import Riemann.WeilSpace.InvolutionWeil

open Real
open Complex MeasureTheory
open scoped MeasureTheory Topology BigOperators




/-!
### Les trois fonctionnelles de la formule explicite de Weil

Agissant sur la fonction test `Φ = f ⋆ g*`.
-/

/-- **Terme polaire** : `W_pol(Φ) = ℳ[Φ](1) + ℳ[Φ](0)`.

Il provient des pôles de la fonction `ζ` en `s = 1` et de son
prolongement en `s = 0`. -/
noncomputable def weilPolar (Φ : ℝ → ℂ) : ℂ :=
  mellinTransform Φ 1 + mellinTransform Φ 0


/-- **Terme arithmétique** : somme sur les premiers `p` et les
entiers `n ≥ 1`, faisant intervenir `ln(p) / p^{n/2}`.

$$W_{\mathrm{arith}}(\Phi) = \sum_{p \in \mathbb{P}} \sum_{n=1}^{\infty}
\frac{\ln(p)}{p^{n/2}} \left( \Phi(p^n) + \Phi(p^{-n}) \right)$$ -/
noncomputable def weilArith (Φ : ℝ → ℂ) : ℂ :=
  ∑' p : Nat.Primes, ∑' n : ℕ,
    if n = 0 then 0
    else
      ((Real.log (p : ℕ) / ((p : ℕ) : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) *
        (Φ (((p : ℕ) : ℝ) ^ n) + Φ (1 / ((p : ℕ) : ℝ) ^ n))


/-- **Terme archimédien** : contribution de la place archimédienne.

$$W_{\mathrm{arch}}(\Phi) = (\ln\pi + \gamma) \Phi(1) +
\int_1^\infty \frac{\Phi(x) + \Phi(1/x) - 2\Phi(1)}{x - 1/x} \, \frac{dx}{x}$$ -/
noncomputable def weilArch (Φ : ℝ → ℂ) : ℂ :=
  ((Real.log Real.pi + eulerMascheroni : ℂ)) * Φ 1 +
  ∫ x in Set.Ioi (1:ℝ),
    (Φ x + Φ (1/x) - 2 * Φ 1) / ((x : ℂ) - 1/x) ∂haarMul

/-- **Forme hermitienne de Weil** :
`⟨f, g⟩_HP := W_pol(Φ) - W_arith(Φ) - W_arch(Φ)` où `Φ = f ⋆ g*`. -/
noncomputable def weilHermitianForm (f g : ℝ → ℂ) : ℂ :=
  let Φ := f ⋆ₘ (weilStarInvolution g)
  weilPolar Φ - weilArith Φ - weilArch Φ

@[inherit_doc]
notation "⟪" f ", " g "⟫_HP" => weilHermitianForm f g



/-- Le terme polaire appliqué à `f ⋆ₘ (weilStar f)` est réel. -/
lemma weilPolar_self_isReal (f : ℝ → ℂ) :
    (weilPolar (f ⋆ₘ (weilStarInvolution  f))).im = 0 := by
  unfold weilPolar
  rw [Complex.add_im]
  rw [mellin_conv_self_star_at_one_isReal f,
      mellin_conv_self_star_at_zero_isReal f]
  ring


/-- Le terme arithmétique appliqué à `f ⋆ₘ (weilStar f)` est réel. -/
lemma weilArith_self_isReal (f : ℝ → ℂ) :
    (weilArith (f ⋆ₘ (weilStarInvolution f))).im = 0 := by
  -- Étape 1 : montrer que chaque terme (Φ(p^n) + Φ(p^{-n})) · poids
  --          est de partie imaginaire nulle (via symétrie de Weil)
  -- Étape 2 : utiliser que la somme d'une série de termes réels est réelle
  --          via tsum_im ou un lemme analogue
  unfold weilArith
  sorry


/-- Le terme archimédien appliqué à `f ⋆ₘ (weilStar f)` est réel. -/
lemma weilArch_self_isReal (f : ℝ → ℂ) :
    (weilArch (f ⋆ₘ (weilStarInvolution f))).im = 0 := by
  -- Étape 1 : déplier weilArch (intégrale sur ℝ)
  -- Étape 2 : changement de variable t ↦ -t, utiliser symétrie
  -- Étape 3 : utiliser integral_im pour pousser .im sous l'intégrale
  unfold weilArch
  sorry



lemma weilHermitianForm_self_isReal (f : ℝ → ℂ) :
    (weilHermitianForm f f).im = 0 := by
  unfold weilHermitianForm
  simp only [Complex.sub_im]
  rw [weilPolar_self_isReal f, weilArith_self_isReal f, weilArch_self_isReal f]
  ring

-- Travaux d'André Weil
