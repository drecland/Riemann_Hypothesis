import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.Tools.SchwartzSpace
import Riemann.Tools.MellinTransform
import Riemann.WeilSpace.WeilOperator

open Real Complex SchwartzMap
open MeasureTheory
open scoped MeasureTheory


/-- **Définition II.2 — Espace des fonctions tests de Weil.**
**(Caracterisation A)** -/
abbrev WeilSpace : Type := SchwartzSpace

/-
Cette caracterisation passe par le fait de dire que l'espace des
fonctions tests est un espace de fonction de Schwartz

-/
@[inherit_doc]
notation "𝒲" => WeilSpace


/-- Représentation d'une fonction de Weil comme fonction sur `ℝ*₊`. -/
noncomputable def WeilSpace.toFun (g : 𝒲) : ℝ → ℂ :=
  fun x => g (Real.log x)


/-- Cohérence : `(toFun g)(eᵗ) = g(t)`. -/
theorem WeilSpace.toFun_exp (g : 𝒲) (t : ℝ) :
    WeilSpace.toFun g (Real.exp t) = g t := by
  unfold WeilSpace.toFun
  rw [Real.log_exp]




/-- **Lemme de cohérence** — `WeilSpace.toFun f x = (f : ℝ → ℂ) (Real.log x)`. -/
lemma weilSpace_toFun_eq
    (f : 𝒲) (x : ℝ) :
    WeilSpace.toFun f x = (f : ℝ → ℂ) (Real.log x) := by
  -- C'est exactement la définition de WeilSpace.toFun
  unfold WeilSpace.toFun
  rfl



/-- **Espace de Weil défini nativement sur `ℝ*₊`.**
**(Caracterisation B)**

Un élément est une fonction `f : ℝ → ℂ` lisse sur `(0, ∞)` et satisfaisant
les bornes uniformes `sup_{x > 0} |(log x)^k · Dᵐ(f)(x)| < +∞` pour tout
`(k, m) ∈ ℕ²`, conformément à la Définition II.2 du document. -/
structure WeilSpaceOnPos where
  toFun : ℝ → ℂ
  smooth_on_pos : ContDiffOn ℝ (⊤ : ℕ∞) toFun (Set.Ioi 0)
  decay_on_pos : ∀ k m : ℕ, ∃ C : ℝ, ∀ x : ℝ, 0 < x →
      ‖(Real.log x : ℂ)^k * (weilOp^[m] toFun) x‖ ≤ C

@[inherit_doc]
notation "𝒲₊" => WeilSpaceOnPos



/-- **Espace de Weil défini comme sous-ensemble de `ℝ → ℂ`.**
**(Caractérisation C)**

La même condition que l'Option B, mais formulée comme un prédicat sur
les fonctions `f : ℝ → ℂ`. Cette forme est utile pour raisonner sur
des fonctions déjà données (plutôt que sur des éléments d'un type). -/
def WeilSpaceSet : Set (ℝ → ℂ) :=
  { f : ℝ → ℂ |
      ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioi 0) ∧
      ∀ k m : ℕ, ∃ C : ℝ, ∀ x : ℝ, 0 < x →
          ‖(Real.log x : ℂ)^k * (weilOp^[m] f) x‖ ≤ C }

@[inherit_doc]
notation "𝒲ₛ" => WeilSpaceSet



/-
## Equivalence A ↔ B
-/

/-! ## Lemmes auxiliaires pour l'équivalence A ↔ B -/
/-- **Lemme 1** : `weilOp (toFun g) x = (deriv g) (log x)`
      pour `x > 0`. -/
theorem WeilSpace.weilOp_toFun (g : 𝒲) {x : ℝ} (hx : 0 < x) :
    weilOp (WeilSpace.toFun g) x = deriv (g : ℝ → ℂ) (Real.log x) := by
  unfold weilOp WeilSpace.toFun
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx_ne
  have hg :
  HasDerivAt (g : ℝ → ℂ) (deriv (g : ℝ → ℂ) (Real.log x)) (Real.log x) :=
    (g.differentiable).differentiableAt.hasDerivAt
  -- On utilise `HasDerivAt.scomp` pour la composition
  -- avec un scalaire réel
  have hcomp : HasDerivAt (fun y => (g : ℝ → ℂ) (Real.log y))
      (x⁻¹ • deriv (g : ℝ → ℂ) (Real.log x)) x := hg.scomp x hlog
  rw [hcomp.deriv]
  -- But : ↑x * (x⁻¹ • deriv g (log x)) = deriv g (log x)
  rw [Complex.real_smul]
  -- But : ↑x * (↑x⁻¹ * deriv g (log x)) = deriv g (log x)
  rw [← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hx_ne, Complex.ofReal_one, one_mul]


/-- **Lemme 1 bis** : identité fonctionnelle
`weilOp ∘ toFun g = toFun (deriv g)` sur `ℝ*₊`.
    Version nécessaire pour la récurrence. -/
theorem WeilSpace.weilOp_toFun_eq (g : 𝒲) :
    Set.EqOn (weilOp (WeilSpace.toFun g))
             (fun x => deriv (g : ℝ → ℂ) (Real.log x))
             (Set.Ioi 0) := by
  intro x hx
  exact WeilSpace.weilOp_toFun g hx



/-- **Lemme 2** : itération.
    `(weilOp^[m] (toFun g)) x = (iteratedDeriv m g) (log x)`
    pour `x > 0`. -/
theorem WeilSpace.weilOp_iterate_toFun (m : ℕ) (g : 𝒲) {x : ℝ}
    (hx : 0 < x) :
    (weilOp^[m] (WeilSpace.toFun g)) x =
      iteratedDeriv m (g : ℝ → ℂ) (Real.log x) := by
  induction m generalizing x with
  | zero =>
    simp [iteratedDeriv_zero, WeilSpace.toFun]
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    rw [iteratedDeriv_succ]
    -- But : weilOp (weilOp^[n] (toFun g)) x = deriv (iteratedDeriv n g)
    -- (log x)
    -- Étape A : déplier weilOp sur le membre de gauche
    change x * deriv (weilOp^[n] (WeilSpace.toFun g)) x
         = deriv (iteratedDeriv n (g : ℝ → ℂ)) (Real.log x)
    -- Étape B : égalité des dérivées via EventuallyEq
    have h_eventually : (weilOp^[n] (WeilSpace.toFun g))
        =ᶠ[nhds x] (fun y => iteratedDeriv n (g : ℝ → ℂ)
        (Real.log y)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ih hy
    rw [h_eventually.deriv_eq]
    -- But : x * deriv (fun y => iteratedDeriv n g (log y)) x
    --       = deriv (iteratedDeriv n g) (log x)
    -- Étape C : calcul de la dérivée de la composition
    have hx_ne : x ≠ 0 := ne_of_gt hx
    have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx_ne
    have hdiff :
    DifferentiableAt ℝ (iteratedDeriv n (g : ℝ → ℂ)) (Real.log x) := by
      have hCD : ContDiff ℝ (⊤ : ℕ∞) (g : ℝ → ℂ) := g.smooth _
      have : Differentiable ℝ (iteratedDeriv n (g : ℝ → ℂ)) :=
        hCD.differentiable_iteratedDeriv n
        (by exact_mod_cast WithTop.coe_lt_top n)
      exact this.differentiableAt
    have hg : HasDerivAt (iteratedDeriv n (g : ℝ → ℂ))
        (deriv (iteratedDeriv n (g : ℝ → ℂ)) (Real.log x)) (Real.log x) :=
      hdiff.hasDerivAt
    have hcomp :
    HasDerivAt (fun y => iteratedDeriv n (g : ℝ → ℂ) (Real.log y))
        (x⁻¹ • deriv (iteratedDeriv n (g : ℝ → ℂ)) (Real.log x)) x :=
      hg.scomp x hlog
    rw [hcomp.deriv]
    -- But : x * (x⁻¹ • deriv ...) = deriv ...
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hx_ne, Complex.ofReal_one, one_mul]


/-- **Lemme 3** : `(log (eᵗ))^k = tᵏ` -/
theorem Real.log_exp_pow (t : ℝ) (k : ℕ) :
    (Real.log (Real.exp t))^k = t^k := by
  rw [Real.log_exp]

/-- Caractérisation équivalente (bornes uniformes). -/
theorem WeilSpace.iff_weilOp_bounded (g : 𝒲) :
    ∀ k m : ℕ, ∃ C : ℝ, ∀ x : ℝ, 0 < x →
      ‖(Real.log x : ℂ)^k * (weilOp^[m] (WeilSpace.toFun g)) x‖ ≤ C := by
  intro k m
  obtain ⟨C, _, hC⟩ := (g : SchwartzMap ℝ ℂ).decay k m
  refine ⟨C, ?_⟩
  intro x hx
  rw [WeilSpace.weilOp_iterate_toFun m g hx, norm_mul, norm_pow, Complex.norm_real,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hC (Real.log x)




/-- Tout élément de l'Option A donne (via sa fonction sous-jacente)
    un élément de l'Option B. -/
theorem WeilSpaceOnPos.toFun_mem_weilSpaceSet (f : 𝒲₊) :
    f.toFun ∈ 𝒲ₛ :=
  ⟨f.smooth_on_pos, f.decay_on_pos⟩

/-- Toute fonction dans l'Option B produit un élément de l'Option A. -/
def WeilSpaceSet.toWeilSpaceOnPos {f : ℝ → ℂ} (hf : f ∈ 𝒲ₛ) : 𝒲₊ where
  toFun := f
  smooth_on_pos := hf.1
  decay_on_pos := hf.2

/-- **Équivalence B ↔ C** : les deux définitions sont en bijection. -/
def weilSpaceEquivSet : 𝒲₊ ≃ 𝒲ₛ where
  toFun f := ⟨f.toFun, f.toFun_mem_weilSpaceSet⟩
  invFun p := WeilSpaceSet.toWeilSpaceOnPos p.2
  left_inv _ := rfl
  right_inv _ := rfl


/-!
### Note sur les équivalences

Nous avons établi :
* **B ↔ C** via `weilSpaceEquivSet` (bijection constructive).
* **C → caractérisation uniforme sur ℝ*₊** via
`WeilSpace.iff_weilOp_bounded`.

L'équivalence complète **A ↔ B** nécessite de passer par
le difféomorphisme
`Φ : ℝ → ℝ*₊, t ↦ eᵗ`, qui identifie `SchwartzMap ℝ ℂ` avec
l'espace A modulo
extension par 0 sur `(-∞, 0]`.
Cette construction sera développée si nécessaire
dans la suite du formalisme
(cf. Lemme II.4 du document : densité de 𝒲 dans L²).
-/
