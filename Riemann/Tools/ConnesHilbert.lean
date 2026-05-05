import Riemann.Basic


open Real Complex MeasureTheory
open scoped MeasureTheory


/-- **Espace de Hilbert de Connes** :
    `L²(𝒞_ℚ)` avec la mesure de Haar quotient.

    espace sur lequel agit naturellement
    l'opérateur de Dirac arithmétique. -/
opaque ConnesHilbert : Type

notation "ℋ_C" => ConnesHilbert

axiom ConnesHilbert.normedAddCommGroup : NormedAddCommGroup ℋ_C
attribute [instance] ConnesHilbert.normedAddCommGroup

axiom ConnesHilbert.innerProductSpace : InnerProductSpace ℂ ℋ_C
attribute [instance] ConnesHilbert.innerProductSpace

axiom ConnesHilbert.completeSpace : CompleteSpace ℋ_C
attribute [instance] ConnesHilbert.completeSpace

attribute [instance]
  ConnesHilbert.normedAddCommGroup
  ConnesHilbert.innerProductSpace
  ConnesHilbert.completeSpace
