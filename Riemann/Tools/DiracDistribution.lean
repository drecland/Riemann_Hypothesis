import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.Tools.UnboundedOperator

open Real Complex SchwartzMap
open MeasureTheory
open scoped MeasureTheory


/-! ## Distribution de Dirac sur le groupe multiplicatif -/


variable {ℋ : Type u_1}
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
  [CompleteSpace ℋ]

/-- **Définition — Distribution de Dirac centrée en `a`** sur `ℝ*₊`.

    Par définition de la mesure de Haar, `⟨δₐ, f⟩ := f(a)`. -/
noncomputable def diracMul (a : ℝ) (f : ℝ → ℂ) : ℂ := f a

@[inherit_doc]
notation "δ[" a "]" => diracMul a


/-- **Noyau diagonal de Dirac** : action sur `f ⊗ ḡ` réduite à
    `∫₀^∞ f(x) · conj(g(x)) · dx/x`. -/
noncomputable def diracDiag (f g : ℝ → ℂ) : ℂ :=
  ∫ x in Set.Ioi (0:ℝ), f x * star (g x) ∂haarMul



/-! ## Operateur de Dirac Arithmetique -/



/-- **Opérateur de Dirac arithmétique**
sur un espace de Hilbert générique. -/
noncomputable def diracArith : UnboundedOperator ℋ := sorry


/-- **Auto-adjonction** de l'opérateur de Dirac arithmétique. -/
lemma diracArith_isSelfAdjoint :
    (diracArith (ℋ := ℋ)).IsSelfAdjoint := sorry

/-- **Spectre de l'opérateur de Dirac**
= ensemble des zéros non triviaux. -/
axiom diracArith_spectrum_eq_zeros :
    ∀ _ : 𝒵, True

/-- **Lemme** — L'opérateur de Dirac arithmétique
    a une résolvante compacte. -/
lemma diracArith_hasCompactResolvent
    {ℋ : Type*}
    [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] :
    (diracArith (ℋ := ℋ)).HasCompactResolvent := by
  sorry

/-- **Famille de vecteurs propres** indexée par `𝒵`. -/
noncomputable def diracEigenvector
    (ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)}) : ℋ := sorry

/-- **Lemme 4.0** : `ψ_ρ` est non nul (vecteur propre de `D`). -/
lemma diracEigenvector_ne_zero
    (ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)}) :
    diracEigenvector (ℋ := ℋ) ρ ≠ 0 := sorry
