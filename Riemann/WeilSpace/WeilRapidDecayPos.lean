import Riemann.Basic
import Riemann.WeilSpace.WeilSpace
import Riemann.Tools.SchwartzSpace


open Complex MeasureTheory Real

/-- **Lemme préliminaire** —
La constante de décroissance de Schwartz est positive.

Pour `f ∈ 𝒮(ℝ)`, la constante `C` issue de `f.decay N 0` est positive
car c'est un supremum de normes. -/
lemma schwartz_decay_const_nonneg
    (f : 𝒲) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖x‖^N * ‖iteratedFDeriv ℝ 0 (f : ℝ → ℂ) x‖ ≤ C := by
  use (SchwartzMap.seminorm ℝ N 0) f
  constructor
  · exact apply_nonneg (SchwartzMap.seminorm ℝ N 0) f
  · intro x
    exact SchwartzMap.le_seminorm ℝ N 0 f x


/-- (1 + |t|)^N ≤ 2^N * (1 + |t|^N) pour tout t : ℝ -/
lemma one_add_abs_pow_le (t : ℝ) (N : ℕ) :
    (1 + |t|)^N ≤ 2^N * (1 + |t|^N) := by
  sorry
/-
  have h1 : 1 + |t| ≤ 2 * max 1 |t| := by
    rcases le_or_lt 1 |t| with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h.le]; linarith [abs_nonneg t]
  calc (1 + |t|)^N
      ≤ (2 * max 1 |t|)^N := pow_le_pow_left (by positivity) h1 N
    _ = 2^N * (max 1 |t|)^N := by rw [mul_pow]
    _ ≤ 2^N * (1 + |t|^N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_or_lt 1 |t| with h | h
        · rw [max_eq_right h]
          linarith [show (0:ℝ) ≤ |t|^N from by positivity]
        · rw [max_eq_left h.le, one_pow]
          linarith [show (0:ℝ) ≤ |t|^N from by positivity]
-/

/-- Pour f ∈ 𝒮(ℝ), ∃ C₀ C₁, ∀ t,
    ‖f t‖ * (1 + |t|^N) ≤ C₀ + C₁ -/
lemma schwartz_decay_one_add_pow
    (f : 𝒲) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖(f : ℝ → ℂ) t‖ * (1 + |t|^N) ≤ C := by
  -- Bornitude : f ∈ 𝒮(ℝ) ⟹ ∃ C₁, ∀ t, ‖f t‖ ≤ C₁
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := f.decay 0 0
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at hC₁
  -- Décroissance : ∃ C₀, ∀ t, ‖t‖^N · ‖f t‖ ≤ C₀
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := f.decay N 0
  simp only [norm_iteratedFDeriv_zero] at hC₀
  refine ⟨C₁ + C₀, by linarith, fun t => ?_⟩
  have h1 : ‖(f : ℝ → ℂ) t‖ ≤ C₁ := hC₁ t
  have h0 : |t|^N * ‖(f : ℝ → ℂ) t‖ ≤ C₀ := by
    have := hC₀ t
    rwa [Real.norm_eq_abs] at this
  -- ‖f t‖ * (1 + |t|^N) = ‖f t‖ + |t|^N * ‖f t‖ ≤ C₁ + C₀
  have hft_nn : 0 ≤ ‖(f : ℝ → ℂ) t‖ := norm_nonneg _
  nlinarith


/-- Pour f ∈ 𝒲, ∃ C, ∀ x > 0,
    ‖(WeilSpace.toFun f) x‖ * (1 + |log x|)^N ≤ C -/
lemma weil_rapid_decay_pos_log
    (f : 𝒲) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖(WeilSpace.toFun f) x‖ * (1 + |Real.log x|)^N ≤ C := by
  -- Étape 1 : décroissance Schwartz avec (1 + |t|^N)
  obtain ⟨C, hC_nn, hC⟩ := schwartz_decay_one_add_pow f N
  -- Étape 2 : constante finale 2^N * C
  refine ⟨2^N * C, by positivity, fun x hx => ?_⟩
  simp only [WeilSpace.toFun]
  set t := Real.log x
  -- Étape 3 : majorer (1 + |t|)^N par 2^N * (1 + |t|^N)
  have hkey := one_add_abs_pow_le t N
  -- Étape 4 : combiner
  have hft_nn : 0 ≤ ‖(f : ℝ → ℂ) t‖ := norm_nonneg _
  have hCt := hC t
  calc ‖(f : ℝ → ℂ) t‖ * (1 + |t|)^N
      ≤ ‖(f : ℝ → ℂ) t‖ * (2^N * (1 + |t|^N)) :=
        mul_le_mul_of_nonneg_left hkey hft_nn
    _ = 2^N * (‖(f : ℝ → ℂ) t‖ * (1 + |t|^N)) := by ring
    _ ≤ 2^N * C := by
        apply mul_le_mul_of_nonneg_left hCt
        positivity
/-
/-- Pour x ≥ 1, |log x| = log x ≥ 0, donc
    (1 + |log x|)^N ≥ (log x)^N.
    On ne peut pas obtenir x⁻ᴺ directement,
    mais on peut obtenir une décroissance en (log x)^{-N}. -/
lemma weil_rapid_decay_large
    (f : 𝒲) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖(WeilSpace.toFun f) x‖ * (Real.log x)^N ≤ C := by
  obtain ⟨C, hC_nn, hC⟩ := weil_rapid_decay_pos_log f N
  refine ⟨C, hC_nn, fun x hx => ?_⟩
  have hx_pos : 0 < x := by linarith
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  -- (log x)^N ≤ (1 + |log x|)^N car log x ≤ 1 + |log x|
  have hle : (Real.log x)^N ≤ (1 + |Real.log x|)^N := by
    apply pow_le_pow_left hlog_nn
    rw [abs_of_nonneg hlog_nn]
    linarith
  calc ‖(WeilSpace.toFun f) x‖ * (Real.log x)^N
      ≤ ‖(WeilSpace.toFun f) x‖ * (1 + |Real.log x|)^N :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ ≤ C := hC x hx_pos

/-- Pour 0 < x ≤ 1, |log x| = -log x ≥ 0. -/
lemma weil_rapid_decay_small
    (f : 𝒲) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖(WeilSpace.toFun f) x‖ * (-Real.log x)^N ≤ C := by
  obtain ⟨C, hC_nn, hC⟩ := weil_rapid_decay_pos_log f N
  refine ⟨C, hC_nn, fun x hx hx1 => ?_⟩
  have hlog_nonpos : Real.log x ≤ 0 := Real.log_nonpos hx1
  have hlog_abs : |Real.log x| = -Real.log x := abs_of_nonpos hlog_nonpos
  have hle : (-Real.log x)^N ≤ (1 + |Real.log x|)^N := by
    apply pow_le_pow_left (by linarith)
    rw [hlog_abs]; linarith
  calc ‖(WeilSpace.toFun f) x‖ * (-Real.log x)^N
      ≤ ‖(WeilSpace.toFun f) x‖ * (1 + |Real.log x|)^N :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ ≤ C := hC x hx
-/
/-- Hypothèse : la décroissance via l'opérateur D de Weil
    implique f(x) = O(x⁻ᴺ) pour x → +∞.
    Ceci est plus fort que la simple décroissance Schwartz
    et utilise la structure multiplicative de 𝒲. -/
lemma weil_rapid_decay_pos
    (f : 𝒲) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖(WeilSpace.toFun f) x‖ ≤ C * x⁻¹ ^ N := by
  sorry -- Nécessite la caractérisation via weilOp
