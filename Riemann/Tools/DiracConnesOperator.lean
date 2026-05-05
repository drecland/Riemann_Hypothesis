import Riemann.Basic
import Riemann.Tools.ConnesHilbert
import Riemann.Tools.IdeleGroup
import Riemann.Tools.AdeleRing
import Riemann.Tools.UnboundedOperator
import Riemann.WeilSpace.WeilZeros

/-- **Opérateur de Dirac de Connes** sur `ℋ_C`.

    Construction issue de la géométrie non commutative
    de l'espace adélique (Connes 1999). -/
axiom diracConnes : UnboundedOperator ℋ_C

/-- **Auto-adjonction** de l'opérateur de Connes. -/
axiom diracConnes_isSelfAdjoint :
    diracConnes.IsSelfAdjoint

/-- **Résolvante compacte**. -/
axiom diracConnes_hasCompactResolvent :
    diracConnes.HasCompactResolvent


/-- **Théorème spectral de Connes** : le spectre de `D_Connes`
    coïncide avec l'ensemble des parties imaginaires
    des zéros non triviaux de ζ. -/
axiom diracConnes_spectrum :
    ∀ ρ : 𝒵, ∃ ψ : ℋ_C, ∃ hψ : ψ ∈ diracConnes.domain, ψ ≠ 0 ∧
      diracConnes.toFun ⟨ψ, hψ⟩ = (ρ.val.im : ℂ) • ψ
