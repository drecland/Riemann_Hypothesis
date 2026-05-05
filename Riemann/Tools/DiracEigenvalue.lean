import Riemann.Basic
import Riemann.WeilSpace.WeilZeros

/-- Valeur propre associée au zéro `ρ ∈ 𝒵` : la partie imaginaire `γ_ρ`. -/
noncomputable def diracEigenvalue (ρ : 𝒵) : ℝ := ρ.val.im
