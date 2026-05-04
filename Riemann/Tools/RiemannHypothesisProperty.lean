import Riemann.Basic
import Riemann.WeilSpace.WeilZeros


/-- **Hypothèse de Riemann** :
tous les zéros non triviaux sont sur la droite critique
`ℜ(s) = 1/2`. -/
def RiemannHypothesisProp : Prop :=
  ∀ ρ ∈ 𝒵, ρ.re = 1/2


lemma nonTrivial_zero_re_lt_one (s : ℂ)
    (h_zero : riemannZeta s = 0)
    (_ : s ≠ 1) :
    s.re < 1 := by
  by_contra h
  push Not at h
  -- h : 1 ≤ s.re
  exact riemannZeta_ne_zero_of_one_le_re h h_zero


lemma nonTrivial_zero_re_pos (s : ℂ)
    (h_zero : riemannZeta s = 0)
    (h_ntriv : ¬∃ n : ℕ, s = -2 * (↑n + 1))
    (h_ne_one : s ≠ 1) :
    0 < s.re := by
  sorry

lemma RiemannHypothesisProp_iff_RiemannHypothesis :
    RiemannHypothesisProp ↔ RiemannHypothesis := by
  constructor
  · -- Sens ⟹ : RiemannHypothesisProp → RiemannHypothesis
    intro h s h_zero h_ntriv h_ne_one
    have hs_mem : s ∈ 𝒵 := by
      refine ⟨h_zero, ?_, ?_⟩
      · exact nonTrivial_zero_re_pos s h_zero h_ntriv h_ne_one
      · exact nonTrivial_zero_re_lt_one s h_zero h_ne_one
    exact h s hs_mem
  · -- Sens ⟸ : RiemannHypothesis → RiemannHypothesisProp
    intro h ρ hρ
    obtain ⟨h_zero, h_pos, h_lt⟩ := hρ
    refine h ρ h_zero ?_ ?_
    · -- ¬∃ n, ρ = -2*(↑n+1)
      rintro ⟨n, hn⟩
      rw [hn] at h_pos
      simp at h_pos
      linarith
    · -- ρ ≠ 1
      intro hρ_eq
      rw [hρ_eq] at h_lt
      norm_num at h_lt
