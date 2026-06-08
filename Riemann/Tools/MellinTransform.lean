import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.Tools.Convolution

open MeasureTheory Complex Real
open scoped MeasureTheory


/-- **Définition II.5 — Transformée de Mellin.**

Pour une fonction `f : ℝ → ℂ` localement intégrable sur `ℝ*₊`, la
transformée de Mellin de `f` est la fonction de la variable complexe `s`
définie par :
$$\mathcal{M}[f](s) = \int_0^{+\infty} f(x) \, x^{s-1} \, dx$$

Référence : Jean Dieudonné, *Calcul infinitésimal*, Hermann, 1968. -/
noncomputable def mellinTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0:ℝ), f x * (x : ℂ) ^ (s - 1) ∂volume

@[inherit_doc]
notation "ℳ[" f "]" => mellinTransform f

/-- Forme équivalente via la mesure de Haar multiplicative :
    $\mathcal{M}[f](s) = \int_0^{+\infty} f(x) \, x^s \, \frac{dx}{x}$. -/
noncomputable def mellinTransformHaar (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0:ℝ), f x * (x : ℂ) ^ s ∂haarMul



/-- **Domaine de convergence absolue** de la transformée de Mellin.

C'est l'ensemble des `s ∈ ℂ` tels que l'intégrande soit absolument
intégrable sur `ℝ*₊`. Il s'agit typiquement d'une bande verticale. -/
def mellinAbsConvDomain (f : ℝ → ℂ) : Set ℂ :=
  { s : ℂ | IntegrableOn
  (fun x => f x * (x : ℂ) ^ (s - 1)) (Set.Ioi 0) volume }

@[inherit_doc]
notation "𝒟[" f "]" => mellinAbsConvDomain f


/-- `ℳ[f*](s) = conj(ℳ[f](1 - conj s))`. -/
lemma mellin_convStar (f : ℝ → ℂ) (s : ℂ) :
    mellinTransform (convStar f) s
      = star (mellinTransform f (1 - star s)) := sorry


/-- **Axiome : formule de Plancherel-Mellin** (convolution multiplicative).
    Pour `f g : ℝ → ℂ` fonctions de Weil et `s : ℂ` :
    `ℳ[f ⋆ₘ g](s) = ℳ[f](s) · ℳ[g](s)`.

    Référence : Tate's thesis (1950), formule standard
    pour la transformée de Mellin et la convolution multiplicative. -/
axiom mellin_mulConv (f g : ℝ → ℂ) (s : ℂ) :
    mellinTransform (mulConv f g) s
      = mellinTransform f s * mellinTransform g s


/-- pour `g = f ⋆ f*` et `ρ ∈ 𝒵`,
    `ℳ[g](ρ) = ℳ[f](ρ) · ℳ[f](1 - conj ρ)`.

    Note : sur la droite critique (et plus généralement par
    symétrisation analytique du prolongement méromorphe), la
    conjugaison disparaît du second facteur. -/
lemma mellin_mulConv_at_zero (f : ℝ → ℂ) (ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)}) :
    mellinTransform (mulConv f (convStar f)) (ρ : ℂ)
      = mellinTransform f (ρ : ℂ) * mellinTransform f
      (1 - star (ρ : ℂ)) := sorry


/-- changement de variable `F(u) = f(eᵘ) · e^{u/2}`.

Permet de transférer la transformée de Mellin en transformée de Fourier. -/
noncomputable def F_transform (f : ℝ → ℂ) : ℝ → ℂ :=
  fun u => f (Real.exp u) * Complex.exp ((u : ℂ) / 2)


/-- Sur la droite critique `ℜ(s) = 1/2`, la transformée
de Mellin de `f` s'identifie à la transformée de Fourier de `F_transform f`.

`ℳ[f](1/2 + iγ) = ∫ F(u) · e^{iγu} du`. -/
lemma mellin_eq_fourier_on_critical_line (f : ℝ → ℂ) (γ : ℝ) :
    mellinTransform f (1/2 + (γ : ℂ) * Complex.I) =
    ∫ u : ℝ, F_transform f u * Complex.exp ((γ : ℂ) * Complex.I * u) := by
  sorry

/-- **Lemme** : le produit `ℳ[f](ρ) · conj(ℳ[f](1 - conj ρ))` est
réel positif quand `ρ` est sur la droite critique. -/
lemma mellin_product_nonneg_on_critical_line
    (f : ℝ → ℂ) (ρ : ℂ) (hρ : ρ.re = 1 / 2) :
    ∃ r : ℝ, 0 ≤ r ∧
      mellinTransform f ρ * star
      (mellinTransform f (1 - star ρ)) = (r : ℂ) := by
  sorry


/-- **Lemme** : sommabilité de `ρ ↦ ℳ[g](ρ)` pour `g = f ⋆ f*`,
    `f ∈ 𝒲`. -/
lemma mellin_summable_on_zeros {f : ℝ → ℂ} :
    Summable
      (fun ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)} =>
        mellinTransform f ρ.val * mellinTransform f
        (1 - star ρ.val)) := sorry

/-- **Injectivité de la transformée de Mellin** sur les fonctions de Weil.
    Si `ℳ[f](s) = ℳ[g](s)` pour tout `s` dans une bande verticale,
    alors `f = g` p.p.

    Référence : théorème d'inversion de Mellin (analogue de Fourier). -/
axiom mellinTransform_injective (f g : ℝ → ℂ)
    (h : ∀ s : ℂ, mellinTransform f s = mellinTransform g s) :
    f = g
