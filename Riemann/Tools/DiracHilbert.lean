import Riemann.Basic
import Riemann.WeilSpace.WeilZeros

/-- **Espace de Hilbert diagonal** : `ℓ²(𝒵)`. -/
noncomputable abbrev DiracHilbert : Type :=
  lp (fun _ : 𝒵 => ℂ) 2
