import Riemann.Basic
import Riemann.Tools.UnboundedOperator
import Riemann.WeilSpace.WeilHermitianForm


variable {ℋ : Type*}
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
[CompleteSpace ℋ]


variable (D : UnboundedOperator ℋ)
variable (hD_sa : D.IsSelfAdjoint) (hD_cr : D.HasCompactResolvent)

/-- **Calcul fonctionnel borélien** :
pour `f : 𝒲`, l'opérateur `f(D)` borné. -/
noncomputable def WeilFunctionalCalculus (f : 𝒲)
(D : UnboundedOperator ℋ)
    (hD_sa : D.IsSelfAdjoint) : ℋ →L[ℂ] ℋ := sorry


@[inherit_doc]
notation:max f "⟦" D "⟧" => WeilFunctionalCalculus f D

/-- **Lemme** : pour `f ∈ 𝒲` et `D` auto-adjoint à résolvante compacte,
    l'opérateur `f(D)` issu du calcul fonctionnel de Weil est compact.

    Justification : `f ∈ 𝒲` ⟹ `ℳ[f]` à décroissance rapide.
    Or `D` à résolvante compacte ⟹ spectre discret `(λ_n)` avec `|λ_n| → ∞`.
    Donc les valeurs propres `ℳ[f](λ_n)` de `f(D)` tendent vers `0`,
    ce qui caractérise un opérateur compact diagonal. -/
lemma weilFunctionalCalculus_isCompact
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (f : 𝒲) (D : UnboundedOperator ℋ) (hD_sa : D.IsSelfAdjoint)
    (hD_cr : D.HasCompactResolvent) :
    IsCompactOperator (WeilFunctionalCalculus f D hD_sa) := by
  sorry


/-- **Lemme** : le produit `f(D) · f*(D)` est compact dès que `f(D)` l'est.

    Justification :
    - `f*(D) = (f(D))*` est l'adjoint d'un compact, donc compact.
    - La composition `compact ∘ borné` (ou `borné ∘ compact`) reste compacte. -/
lemma weilFunctionalCalculus_mul_star_isCompact
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (f : 𝒲) (D : UnboundedOperator ℋ) (hD_sa : D.IsSelfAdjoint)
    (hfD_compact : IsCompactOperator (WeilFunctionalCalculus f D hD_sa)) :
    IsCompactOperator
      ((WeilFunctionalCalculus f D hD_sa) *
       (WeilFunctionalCalculus (weilStarW f) D hD_sa)) := by
  sorry
