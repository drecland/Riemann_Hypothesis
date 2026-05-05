import Riemann.Basic

/-- Ensemble des zéros non triviaux de ζ -/
def nonTrivialZetaZeros : Set ℂ :=
  { ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 }

notation "𝒵" => nonTrivialZetaZeros
