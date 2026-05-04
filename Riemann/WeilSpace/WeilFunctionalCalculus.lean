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
