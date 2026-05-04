import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.Tools.MellinTransform
import Riemann.Tools.DiracDistribution
import Riemann.WeilSpace.WeilHermitianForm
import Riemann.WeilSpace.WeilZeros
import Riemann.WeilSpace.WeilSpace


/-! ## Distribution de Weil `𝒦_Γ` -/

/-- **Distribution de Weil `𝒦_Γ`** agissant
      sur le produit tensoriel `f ⊗ ḡ`.

    Décomposée en trois composantes :
    - **Identité** : noyau diagonal `δ(x-y)`.
    - **Arithmétique** : somme pondérée par `Λ(n)/√n` des translations
      multiplicatives par `n` (partie premiers).
    - **Archimédienne** : noyau `K_∞` issu du facteur gamma.

    La définition géométrique est encapsulée axiomatiquement ici : on
    postule son existence et sa valeur via la formule explicite de Weil
    (cf. lemme `weilKernel_spectral` ci-dessous). -/
opaque weilKernel (f g : ℝ → ℂ) : ℂ

@[inherit_doc]
notation "⟨𝒦_Γ," f "," g "⟩" => weilKernel f g

/-! ## Axiome : Formule explicite de Weil

    **Référence** : André Weil, *Sur les "formules explicites"
    de la théorie des nombres premiers*,
    Comm. Sém. Math. Univ. Lund, 1952.

    Ce résultat relie l'action géométrique de `𝒦_Γ` à une somme
    spectrale sur les zéros non triviaux de `ζ`,
    via la transformée de Mellin de la convolution multiplicative
    `h(u) = ∫ f(uy)·conj(g(y)) dy/y`.
-/

/-- **Formule explicite de Weil (axiome)** :
    réduction de l'action géométrique
    de `𝒦_Γ` à l'évaluation unidimensionnelle sur la
    convolution `h`. -/
axiom weilExplicitFormula (f g : 𝒲) :
    weilKernel (WeilSpace.toFun f) (WeilSpace.toFun g) =
      ∑' ρ : 𝒵, mellinTransform (WeilSpace.toFun f) ρ.val *
        star (mellinTransform (WeilSpace.toFun g) (1 - star ρ.val))




/-! ## Lemme principal : équivalence spectrale -/

/-- **Lemme II.18 — Action de la distribution de Weil**
    **et équivalence spectrale.**

    L'action de la distribution `𝒦_Γ` sur `f ⊗ ḡ` coïncide avec la somme
    spectrale sur les zéros non triviaux de `ζ`, et coïncide donc avec la
    forme sesquilinéaire de Weil `⟨f, g⟩_{HP}`. -/
theorem weilKernel_spectral (f g : 𝒲) :
    weilKernel (WeilSpace.toFun f) (WeilSpace.toFun g) =
      ∑' ρ : 𝒵, mellinTransform (WeilSpace.toFun f) ρ.val *
        star (mellinTransform (WeilSpace.toFun g) (1 - star ρ.val)) := by
  -- Conséquence directe de la formule explicite de Weil.
  exact weilExplicitFormula f g

/-- **Corollaire — Équivalence avec la forme de Weil `⟨·,·⟩_{HP}`.**

    Sous réserve que la forme hermitienne `weilHermitianForm`
    soit définie par
    la même somme spectrale (cf. `HermitianForm.lean`),
    les deux coïncident. -/
theorem weilKernel_eq_hermForm (f g : 𝒲)
    (hHP : ∀ f g : 𝒲,
      weilHermitianForm f g =
        ∑' ρ : 𝒵, mellinTransform (WeilSpace.toFun f) ρ.val *
          star (mellinTransform (WeilSpace.toFun g) (1 - star ρ.val))) :
    weilKernel (WeilSpace.toFun f) (WeilSpace.toFun g)
    = weilHermitianForm f g := by
  rw [weilKernel_spectral, hHP]
