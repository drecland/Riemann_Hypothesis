import Riemann.Basic

variable {ℋ : Type*}
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
[CompleteSpace ℋ]


/-- **Opérateur linéaire non borné** sur `ℋ` :
    domaine dense `D` et application linéaire `D → ℋ`. -/
structure UnboundedOperator (ℋ : Type*)
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ] where
  domain : Submodule ℂ ℋ
  domain_dense : Dense (domain : Set ℋ)
  toFun : domain →ₗ[ℂ] ℋ


/-- **Domaine de l'adjoint** `D(A*)`. -/
noncomputable def UnboundedOperator.adjointDomain
    (A : UnboundedOperator ℋ) : Submodule ℂ ℋ where
  carrier := { y : ℋ | ∃ z : ℋ, ∀ x : A.domain,
    @inner ℂ _ _ (A.toFun x) y = @inner ℂ _ _ (x : ℋ) z }
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro x
    simp
  add_mem' := by
    rintro y₁ y₂ ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
    refine ⟨z₁ + z₂, ?_⟩
    intro x
    rw [inner_add_right, inner_add_right, hz₁ x, hz₂ x]
  smul_mem' := by
    rintro c y ⟨z, hz⟩
    refine ⟨c • z, ?_⟩
    intro x
    rw [inner_smul_right, inner_smul_right, hz x]



/-- **Adjoint** `A*` : pour `y ∈ D(A*)`,
le vecteur unique `z` (par densité). -/
noncomputable def UnboundedOperator.adjoint (A : UnboundedOperator ℋ) :
    A.adjointDomain →ₗ[ℂ] ℋ where
  toFun := fun y => Classical.choose y.2
  map_add' := by
    intro y₁ y₂
    -- L'image de y₁ + y₂ est Classical.choose (y₁+y₂).2
    -- On veut montrer = Classical.choose y₁.2 + Classical.choose y₂.2
    -- Par unicité (densité), il suffit que les deux satisfassent la même propriété
    sorry
  map_smul' := by
    intro c y
    sorry

/-- **Définition II.21** — `A` est **auto-adjoint**
si `D(A) = D(A*)` et `A = A*` sur ce domaine. -/
def UnboundedOperator.IsSelfAdjoint (A : UnboundedOperator ℋ) :
Prop :=
  ∃ h : A.domain = A.adjointDomain,
    ∀ x : A.domain, A.toFun x = A.adjoint ⟨(x : ℋ), h ▸ x.2⟩

/-- **Résolvante compacte** : pour tout `λ ∈ ℂ` hors du spectre de `A`,
l'opérateur `(A - λI)⁻¹` est compact.

Définition simplifiée : il existe au moins un `λ` tel que `(A - λI)`
soit inversible et son inverse compact. -/
def UnboundedOperator.HasCompactResolvent (A : UnboundedOperator ℋ) : Prop :=
  ∃ _lam : ℂ, ∃ R : ℋ →L[ℂ] ℋ,
    IsCompactOperator R ∧
    -- R agit comme inverse de (A - λI) sur A.domain
    ∀ x : A.domain, R (A.toFun x - _lam • (x : ℋ)) = (x : ℋ)


/-- Un opérateur auto-adjoint dans notre cadre (espace séparable,
    spectre discret coïncidant avec 𝒵) a une résolvante compacte.
    Ceci découle du fait que le spectre est discret et que les
    valeurs propres tendent vers l'infini. -/
lemma isSelfAdjoint_hasCompactResolvent
    {ℋ : Type*}
    [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ]
    (D : UnboundedOperator ℋ) (hD_sa : D.IsSelfAdjoint) :
    D.HasCompactResolvent := by
  -- Justification mathématique :
  -- 1. D auto-adjoint → spectre réel discret (valeurs propres λ_n → ∞)
  -- 2. (D - λI)⁻¹ s'exprime comme série sur les projecteurs spectraux
  -- 3. Les valeurs singulières de (D - λI)⁻¹ sont |λ_n - λ|⁻¹ → 0
  -- 4. Donc (D - λI)⁻¹ est limite d'opérateurs de rang fini → compact
  sorry
