import Riemann.Basic
import Riemann.Tools.MellinTransform
import Riemann.Tools.RiemannHypothesisProperty
import Riemann.WeilSpace.WeilZeros
import Riemann.WeilSpace.WeilHermitianForm

/-- **Axiome — Formule explicite de Weil.**

Pour toute fonction test `Φ ∈ 𝒲` (vue comme fonction sur `ℝ*₊`),
la combinaison `W_pol(Φ) - W_arith(Φ) - W_arch(Φ)` est égale à la somme
des transformées de Mellin sur les zéros non triviaux.

Ce résultat est dû à André Weil (1952). -/
axiom weil_explicit_formula (Φ : ℝ → ℂ) :
    weilPolar Φ - weilArith Φ - weilArch Φ =
    ∑' ρ : 𝒵, mellinTransform Φ (ρ : ℂ)



/-- **Axiome— Localisation analytique de Weil.**

Pour tout couple de zéros non triviaux distincts `ρ₀ ≠ ρ₁` et pour tout
`ε > 0`, il existe une fonction test `f ∈ 𝒲` telle que :
- `ℳ[f](ρ₀) = 1`,
- `ℳ[f](ρ₁) = -1`,
- la somme sur les autres zéros est bornée en module par `ε`. -/
axiom weil_localization
    (ρ₀ ρ₁ : ℂ) (hρ₀ : ρ₀ ∈ 𝒵) (hρ₁ : ρ₁ ∈ 𝒵) (hne : ρ₀ ≠ ρ₁)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ℝ → ℂ, mellinTransform f ρ₀ = 1 ∧
      mellinTransform f ρ₁ = -1 ∧
      ‖∑' ρ : ({ρ₀, ρ₁}ᶜ ∩ 𝒵 : Set ℂ),
          mellinTransform f (ρ : ℂ) *
            star (mellinTransform f (1 - star (ρ : ℂ)))‖ ≤ ε



/-- **Lemme — Identité fondamentale sur la diagonale.**

Pour toute `f ∈ 𝒲`, on a :
`⟨f, f⟩_HP = ∑_{ρ ∈ 𝒵} ℳ[f](ρ) · conj(ℳ[f](1 - conj ρ))`. -/
lemma weilHermitian_diag_eq_sum (f : ℝ → ℂ) :
    weilHermitianForm f f =
    ∑' ρ : 𝒵,
      mellinTransform f (ρ : ℂ) * star
      (mellinTransform f (1 - star (ρ : ℂ))) := by
  sorry


/-- **Lemme** : sous RH, pour tout `ρ ∈ 𝒵`, on a `1 - conj ρ = ρ`. -/
lemma one_sub_conj_eq_self_of_RH (h : RiemannHypothesis)
(ρ : ℂ) (hρ : ρ ∈ 𝒵) :
    1 - star ρ = ρ := by
  sorry


/-- **Théorème— Sens direct du critère de positivité.**

Si l'Hypothèse de Riemann est vérifiée, alors la forme hermitienne de Weil
est positive sur l'espace de Weil. -/
theorem positivity_of_RH (h : RiemannHypothesis) (f : ℝ → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ weilHermitianForm f f = (r : ℂ) := by
  sorry

/-- **Lemme — Symétrie fonctionnelle.**

Si `ρ ∈ 𝒵`, alors `1 - conj ρ ∈ 𝒵`. -/
lemma one_sub_conj_mem_zeros (ρ : ℂ) (hρ : ρ ∈ 𝒵) :
    1 - star ρ ∈ 𝒵 := by
  sorry

/-- **Lemme** — Les deux zéros `ρ₀` et `ρ₁ = 1 - conj ρ₀` sont distincts
quand `ρ₀.re ≠ 1/2`. -/
lemma rho_ne_one_sub_conj (ρ : ℂ) (hρ : ρ.re ≠ 1 / 2) :
    ρ ≠ 1 - star ρ := by
  sorry


/-- **Lemme — Calcul de la contribution des deux zéros jumeaux.**

Quand `ℳ[f](ρ₀) = 1` et `ℳ[f](ρ₁) = -1` avec `ρ₁ = 1 - conj ρ₀`, la
contribution du couple `{ρ₀, ρ₁}` dans la somme vaut `-2`. -/
lemma twin_zeros_contribution
    (f : ℝ → ℂ) (ρ₀ ρ₁ : ℂ)
    (h₁ : ρ₁ = 1 - star ρ₀)
    (hf₀ : mellinTransform f ρ₀ = 1)
    (hf₁ : mellinTransform f ρ₁ = -1) :
    mellinTransform f ρ₀ * star (mellinTransform f (1 - star ρ₀)) +
    mellinTransform f ρ₁ * star (mellinTransform f (1 - star ρ₁)) = -2 := by
  sorry

/-- **Théorème — Sens réciproque du critère de positivité.**

Si l'Hypothèse de Riemann est fausse, il existe `f ∈ 𝒲` telle que
`⟨f, f⟩_HP` n'est pas réel positif. -/
theorem negativity_if_not_RH (h : ¬ RiemannHypothesis) :
    ∃ f : 𝒲, ∃ r : ℝ, r < 0 ∧
      weilHermitianForm (WeilSpace.toFun f) (WeilSpace.toFun f) = (r : ℂ) := by
  sorry


/-!
### Théorème principal
-/

/-- **Théorème — Critère de positivité de Weil.**

L'Hypothèse de Riemann est équivalente à la positivité de la forme
hermitienne de Weil sur l'espace de Weil. -/
theorem weil_positivity_criterion :
    RiemannHypothesis ↔
    ∀ f : 𝒲, ∃ r : ℝ, 0 ≤ r ∧
      weilHermitianForm (WeilSpace.toFun f) (WeilSpace.toFun f) = (r : ℂ) := by
  constructor
  · intro h f
    exact positivity_of_RH h (WeilSpace.toFun f)
  · intro hpos
    by_contra hRH
    obtain ⟨f, r, hr_neg, hfr⟩ := negativity_if_not_RH hRH
    obtain ⟨r', hr'_nn, hfr'⟩ := hpos f
    rw [hfr] at hfr'
    have hrr_eq : (r : ℂ) = (r' : ℂ) := hfr'
    have hrr : r = r' := by exact_mod_cast hrr_eq
    linarith
