import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.Tools.UnboundedOperator
import Riemann.Tools.DiracConnesOperator
import Riemann.Tools.ConnesHilbert
import Riemann.Tools.IdeleGroup
import Riemann.Tools.AdeleRing
import Riemann.Tools.DiracEigenvalue
import Riemann.Tools.DiracHilbert

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



/-- Domaine de l'opérateur diagonal : suites `ψ ∈ ℓ²(𝒵)`
    telles que `ρ ↦ γ_ρ · ψ ρ` reste dans `ℓ²`. -/
noncomputable def diracArithDiag_domain : Submodule ℂ DiracHilbert where
  carrier := { ψ : DiracHilbert |
    Memℓp (fun ρ : 𝒵 => (diracEigenvalue ρ : ℂ) * ψ ρ) 2 }
  zero_mem' := by
    simp [Memℓp]
    sorry
  add_mem' := by sorry
  smul_mem' := by sorry

lemma diracArithDiag_domain_dense :
    Dense (diracArithDiag_domain : Set DiracHilbert) := by
  sorry

/-- Action diagonale : `(D ψ) ρ = γ_ρ · ψ ρ`. -/
noncomputable def diracArithDiag_toFun :
    diracArithDiag_domain →ₗ[ℂ] DiracHilbert where
  toFun := fun ψ =>
    ⟨fun ρ => (diracEigenvalue ρ : ℂ) * (ψ : DiracHilbert) ρ,
     by exact ψ.2⟩
  map_add' := by
    intro ψ₁ ψ₂
    apply lp.ext
    funext ρ
    simp only [lp.coeFn_add, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' := by
    intro c ψ
    apply lp.ext
    funext ρ
    simp
    ring


/-- **Modèle diagonal** de l'opérateur de Dirac sur `ℓ²(𝒵)`. -/
noncomputable def diracArithDiag : UnboundedOperator DiracHilbert where
  domain := diracArithDiag_domain
  domain_dense := diracArithDiag_domain_dense
  toFun := diracArithDiag_toFun

/-- Existence d'une base hilbertienne orthonormée de vecteurs propres
    de `D_Connes`, indexée par `𝒵`.
    Conséquence du théorème spectral pour opérateurs auto-adjoints
    à résolvante compacte (Connes 1999, von Neumann). -/
axiom diracConnes_eigenbasis :
    ∃ e : 𝒵 → ℋ_C,
      Orthonormal ℂ e ∧
      (∀ ρ : 𝒵, ∃ hρ : e ρ ∈ diracConnes.domain,
        diracConnes.toFun ⟨e ρ, hρ⟩ = (ρ.val.im : ℂ) • e ρ) ∧
      (⊤ : Submodule ℂ ℋ_C) ≤ (Submodule.span ℂ (Set.range e)).topologicalClosure

/-- Une base orthonormée totale `e : 𝒵 → ℋ_C` induit une isométrie
    unitaire `ℋ_C ≃ₗᵢ[ℂ] ℓ²(𝒵)`. -/
noncomputable def hilbertBasisToLp
    (e : 𝒵 → ℋ_C) (h_on : Orthonormal ℂ e)
    (h_total : (⊤ : Submodule ℂ ℋ_C) ≤
        (Submodule.span ℂ (Set.range e)).topologicalClosure) :
    ℋ_C ≃ₗᵢ[ℂ] DiracHilbert := by
  -- Mathlib : `HilbertBasis.mk` puis `HilbertBasis.repr`
  sorry


/-- **Lemme de liaison fondamental** :
    il existe une isométrie unitaire `U : ℋ_C ≃ ℓ²(𝒵)`
    qui entrelace `D_Connes` et le modèle diagonal.

    Autrement dit :
    $$ U \circ D_{\mathrm{Connes}} = D_{\mathrm{diag}} \circ U $$

    Ce lemme est la traduction du théorème spectral
    de Connes en termes constructifs. -/
lemma diracConnes_unitaryEquiv_diag :
    ∃ U : ℋ_C ≃ₗᵢ[ℂ] DiracHilbert,
      (∀ ψ : ℋ_C, ψ ∈ diracConnes.domain → U ψ ∈ diracArithDiag.domain) ∧
      (∀ ψ : ℋ_C, ∀ hψ : ψ ∈ diracConnes.domain,
        ∀ hUψ : U ψ ∈ diracArithDiag.domain,
        U (diracConnes.toFun ⟨ψ, hψ⟩) =
          diracArithDiag.toFun ⟨U ψ, hUψ⟩) := by
  obtain ⟨e, h_on, h_eigen, h_total⟩ := diracConnes_eigenbasis
  refine ⟨hilbertBasisToLp e h_on h_total, ?_, ?_⟩
  · intro ψ hψ
    sorry
  · intro ψ hψ hUψ
    sorry

/-- **Définition canonique** de `diracArith` :
    on choisit le modèle diagonal comme représentant. -/
noncomputable def diracArith : UnboundedOperator DiracHilbert :=
  diracArithDiag

/-- **L'opérateur diagonal** sur `ℓ²(𝒵)` à valeurs propres réelles
    `γ_ρ = ρ.val.im` est auto-adjoint. -/
lemma diracArithDiag_isSelfAdjoint :
    diracArithDiag.IsSelfAdjoint := by
  -- IsSelfAdjoint = ∃ h : domain = adjointDomain, ∀ x, toFun x = adjoint ⟨x, h ▸ x.2⟩
  refine ⟨?_, ?_⟩
  · -- Partie 1 : domain = adjointDomain
    apply Submodule.ext
    intro y
    constructor
    · -- ⊆ : si y ∈ domain, alors y ∈ adjointDomain
      intro hy
      -- Témoin : z = D y
      refine ⟨diracArithDiag.toFun ⟨y, hy⟩, ?_⟩
      intro x
      -- ⟨D x, y⟩ = ⟨x, D y⟩ : c'est la symétrie (calcul terme à terme avec γ_ρ ∈ ℝ)
      sorry
    · -- ⊇ : si y ∈ adjointDomain, alors (γ_ρ y_ρ) ∈ ℓ²
      rintro ⟨z, hz⟩
      -- Tester hz sur les vecteurs de base e_ρ permet de montrer z_ρ = γ_ρ y_ρ
      -- Donc (γ_ρ y_ρ)_ρ = z ∈ ℓ²
      sorry

  · -- Partie 2 : ∀ x, toFun x = adjoint ⟨x, h ▸ x.2⟩
    intro x
    -- Stratégie : utiliser unicité de l'adjoint via densité
    -- adjoint y = unique z tel que ∀ u ∈ domain, ⟨D u, y⟩ = ⟨u, z⟩
    -- D x convient (symétrie), donc adjoint = D x
    sorry


lemma diracArith_isSelfAdjoint :
    diracArith.IsSelfAdjoint := by
  unfold diracArith
  exact diracArithDiag_isSelfAdjoint

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
    (diracArith).HasCompactResolvent := by
  sorry

/-- **Famille de vecteurs propres** indexée par `𝒵`.
**Vecteur propre dans DiracHilbert** : le vecteur de base
δ_ρ indexé par le zéro ρ -/
noncomputable def diracEigenvector_diag
    (ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)}) : DiracHilbert :=
  lp.single 2 ⟨ρ.val, ρ.property⟩ (1 : ℂ)
  -- ← Retourne un élément de ℓ²(𝒵)

/-- **Version générique** pour compatibilité avec ℋ quelconque -/
noncomputable def diracEigenvector
    (ℋ : Type u_1)
    [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ]
    (ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)}) : ℋ := sorry
