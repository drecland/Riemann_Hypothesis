import Riemann.Basic


open Real Complex MeasureTheory
open scoped MeasureTheory

/-- **Place de ℚ** : soit la place archimédienne `∞`,
    soit une place finie correspondant à un nombre premier. -/
inductive Place : Type
  | infinite : Place
  | finite : Nat.Primes → Place

/-- Notation pour la place archimédienne. -/
notation "∞_pl" => Place.infinite




/-- **Complété local** de ℚ à la place `v`.

- Si `v = ∞`, c'est `ℝ`.
- Si `v = p` (premier), c'est le corps `p`-adique `ℚ_p`.

Pour l'instant, on pose ces objets en `opaque`. -/
opaque LocalField : Place → Type


/-- Structure de corps sur le complété local. -/
axiom LocalField.field : ∀ v : Place, Field (LocalField v)

/-- Structure topologique localement compacte. -/
axiom LocalField.topology : ∀ v : Place, TopologicalSpace (LocalField v)
attribute [instance] LocalField.field LocalField.topology





/-- **Anneau des adèles de ℚ** : produit restreint des `ℚ_v`
    relativement aux entiers locaux `ℤ_v`.

    `𝔸_ℚ = ℝ × ∏'_p ℚ_p` (produit restreint).

    Construction posée en `opaque` pour l'instant. -/
opaque AdeleRing : Type

notation "𝔸_ℚ" => AdeleRing



/-- Structure d'anneau topologique sur les adèles. -/
axiom AdeleRing.commRing : CommRing 𝔸_ℚ
axiom AdeleRing.topology : TopologicalSpace 𝔸_ℚ
axiom AdeleRing.locallyCompact :
  @LocallyCompactSpace 𝔸_ℚ AdeleRing.topology

attribute [instance] AdeleRing.commRing AdeleRing.topology
AdeleRing.locallyCompact
