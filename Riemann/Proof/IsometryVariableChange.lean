import Riemann.basic
import Riemann.Tools.Convolution


open MeasureTheory Complex Real
open scoped MeasureTheory




/-- **Isométrie de changement de variable** `J : (ℝ*₊ → ℂ) → (ℝ → ℂ)`.
    `J(f)(t) = f(exp t)`.
    Relie les fonctions sur `ℝ*₊` (variable multiplicative)
    aux fonctions sur `ℝ` (variable additive). -/
noncomputable def isoJ (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => f (Real.exp t)

/-- **Inverse de J** : `J⁻¹(g)(x) = g(log x)` pour `x > 0`. -/
noncomputable def isoJ_inv (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => g (Real.log x)

/-- **J intertwine mulConv et addConv** :
    `J(f ⋆ₘ g) = J(f) ⋆ₐ J(g)`
    où `⋆ₐ` est la convolution additive `(h₁ ⋆ₐ h₂)(t) = ∫ h₁(t-s)·h₂(s) ds`.

    Preuve : changement de variable `y = exp u`, `x = exp t` dans
    `(f ⋆ₘ g)(x) = ∫₀^∞ f(x/y) g(y) dy/y`. -/
lemma isoJ_mulConv (f g : ℝ → ℂ) :
    isoJ (mulConv f g) = addConv (isoJ f) (isoJ g) := by
  funext t
  unfold isoJ mulConv addConv
  simp only []
  -- But : f(exp t / exp u) = f(exp(t - u)) par propriété de l'exp
  -- ∫ f(exp t / y) g(y) dy/y  avec y = exp u, dy/y = du
  --   = ∫ f(exp(t-u)) g(exp u) du
  sorry

/-- **J transforme convStar en weilStarW** :
    Pour tout `f : ℝ → ℂ` et tout `t : ℝ` :
    `J(convStar f)(t) = (weilStarW (isoJ f))(t)`

    Preuve :
    `J(convStar f)(t) = convStar f (exp t)`
                     `= (exp t)⁻¹ · star(f(exp(-t)))`
                     `= (exp t)⁻¹ · star(J(f)(-t))`
    et `weilStarW(J(f))(t) = star(J(f)(-t))`.

    NB : le facteur `(exp t)⁻¹` est absorbé dans la mesure
    de Haar `d×x = dx/x` lors de l'identification L². -/
lemma isoJ_convStar (f : ℝ → ℂ) (t : ℝ) :
    isoJ (convStar f) t
      = (Real.exp t : ℂ)⁻¹ * star (f (Real.exp (-t))) := by
  unfold isoJ convStar
  congr 1; congr 1; congr 1
  exact (Real.exp_neg t).symm
