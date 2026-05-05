import Riemann.Basic


open Real Complex MeasureTheory
open scoped MeasureTheory



/-- **Groupe des idèles** : éléments inversibles de `𝔸_ℚ`. -/
opaque IdeleGroup : Type

notation "𝕀_ℚ" => IdeleGroup

axiom IdeleGroup.commGroup : CommGroup 𝕀_ℚ
axiom IdeleGroup.topology : TopologicalSpace 𝕀_ℚ

attribute [instance] IdeleGroup.commGroup IdeleGroup.topology

/-- Plongement diagonal de `ℚ*` dans les idèles. -/
axiom rationalEmbedding : ℚˣ →* 𝕀_ℚ


/-- **Espace quotient** `𝕀_ℚ / ℚ*` : espace de classes d'idèles. -/
opaque IdeleClassGroup : Type

notation "𝒞_ℚ" => IdeleClassGroup

axiom IdeleClassGroup.topology : TopologicalSpace 𝒞_ℚ
attribute [instance] IdeleClassGroup.topology

axiom IdeleClassGroup.measure :
    @MeasureTheory.Measure 𝒞_ℚ (borel 𝒞_ℚ)

attribute [instance] IdeleClassGroup.topology
