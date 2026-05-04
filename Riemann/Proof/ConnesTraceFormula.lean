import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.Tools.MellinTransform
import Riemann.Tools.UnboundedOperator
import Riemann.Tools.DiracDistribution
import Riemann.WeilSpace.WeilHermitianForm
import Riemann.Proof.MacaevIdeal
import Riemann.Proof.DixmierTrace
import Riemann.Proof.RegularizedTraceOperator



variable {ℋ : Type u_1}
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
[CompleteSpace ℋ]


@[inherit_doc]
notation "Trω" => dixmierTrace


/-! ### — Appartenance à l'idéal de Dixmier -/

/-- **Lemme** : le volume des classes d'idèles est infini, donc
    `f(D) f*(D)` n'appartient pas à `ℒ¹(ℋ)`. -/
lemma positiveOp_not_traceClass (f : 𝒲) :
    True := sorry  -- placeholder : "P_f ∉ ℒ¹(ℋ)"

/-- **Lemme** (von Mangoldt) : asymptotique `N(T) ∼ (T/2π) ln T`. -/
lemma vonMangoldt_zeros_asymptotic :
    True := sorry  -- placeholder pour l'asymptotique

/-- **Lemme** : `f(D) f*(D) ∈ ℒ^{1,∞}(ℋ)` (idéal de Macaev/Dixmier). -/
lemma positiveOp_mem_macaev (f : 𝒲) :
    positiveOp f (diracArith (ℋ := ℋ)) diracArith_isSelfAdjoint
      ∈ MacaevIdeal ℋ := sorry


/-- **Lemme** : `g(D)` agit comme la multiplication par `ℳ[g](ρ)`
    sur le vecteur propre `ψ_ρ`. -/
lemma functionalCalculus_eigenvalues
    (g : 𝒲) (ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)}) :
    WeilFunctionalCalculus g (diracArith (ℋ := ℋ))
        diracArith_isSelfAdjoint (diracEigenvector (ℋ := ℋ) ρ)
      = (mellinTransform (g : ℝ → ℂ) ρ.val) • diracEigenvector (ℋ := ℋ) ρ := by
  sorry


/-- **Lemme** (théorème de la trace de Connes) : pour `g ∈ 𝒲` telle
    que `g(D) ∈ ℒ^{1,∞}(ℋ)` est positif et que `ρ ↦ ℳ[g](ρ)` est
    sommable, la trace de Dixmier coïncide avec la somme spectrale. -/
lemma dixmierTrace_eq_sum_eigenvalues
    (g : 𝒲)
    (hMac : WeilFunctionalCalculus g (diracArith (ℋ := ℋ))
              diracArith_isSelfAdjoint ∈ MacaevIdeal ℋ)
    (hPos : ∀ x : ℋ, 0 ≤ (@inner ℂ _ _
              (WeilFunctionalCalculus g diracArith diracArith_isSelfAdjoint x)
              x).re)
    (_hsum : Summable
      (fun ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)} =>
        mellinTransform (g : ℝ → ℂ) ρ.val)) :
    (dixmierTrace
        (WeilFunctionalCalculus g diracArith diracArith_isSelfAdjoint)
        hMac hPos : ℂ)
      = ∑' ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)},
          mellinTransform (g : ℝ → ℂ) ρ.val := by
  sorry


/-- **Lemme** : le calcul fonctionnel transforme la convolution
    multiplicative en produit d'opérateurs :
    `(f ⋆ f*)(D) = f(D) · f*(D) = positiveOp f D`. -/
lemma weilFunctionalCalculus_mulConv (f : 𝒲) (g_conv : 𝒲)
    (hg : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ))) :
    WeilFunctionalCalculus g_conv (diracArith (ℋ := ℋ))
        diracArith_isSelfAdjoint
      = positiveOp f diracArith diracArith_isSelfAdjoint := by
  sorry



/-- **Théorème — Évaluation de la trace régularisée (Connes).**

    Pour toute `f ∈ 𝒲`, l'opérateur `f(D) f*(D)` appartient à l'idéal
    de Dixmier, et :
    `Trω(f(D) f*(D)) = ∑_{ρ ∈ 𝒵} ℳ[f](ρ) · ℳ[f](1 - conj ρ)`. -/
theorem dixmierTrace_positiveOp_eq_sum {f : 𝒲}
    (g_conv : 𝒲)
    (hg_conv : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ)))
    (hsum : Summable
      (fun ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)} =>
        mellinTransform (g_conv : ℝ → ℂ) ρ.val)) :
    ∃ (h : positiveOp f (diracArith (ℋ := ℋ)) diracArith_isSelfAdjoint
        ∈ MacaevIdeal ℋ),
    (dixmierTrace
        (positiveOp f diracArith diracArith_isSelfAdjoint) h
        (positiveOp_isPositive f diracArith diracArith_isSelfAdjoint) : ℂ)
      = ∑' ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)},
          mellinTransform (f : ℝ → ℂ) ρ.val
            * mellinTransform (f : ℝ → ℂ) (1 - star ρ.val) := by
  refine ⟨positiveOp_mem_macaev f, ?_⟩
  have hD : WeilFunctionalCalculus g_conv (diracArith (ℋ := ℋ))
              diracArith_isSelfAdjoint
            = positiveOp f diracArith diracArith_isSelfAdjoint :=
    weilFunctionalCalculus_mulConv f g_conv hg_conv
  have hMac : WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint
                ∈ MacaevIdeal ℋ := by
    rw [hD]; exact positiveOp_mem_macaev f
  have hPos : ∀ x : ℋ, 0 ≤ (@inner ℂ _ _
                (WeilFunctionalCalculus g_conv diracArith
                  diracArith_isSelfAdjoint x) x).re := by
    rw [hD]; exact positiveOp_isPositive f diracArith diracArith_isSelfAdjoint
  have hC := dixmierTrace_eq_sum_eigenvalues g_conv hMac hPos hsum
  have hB : ∀ ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)},
      mellinTransform (g_conv : ℝ → ℂ) ρ.val
        = mellinTransform (f : ℝ → ℂ) ρ.val
          * mellinTransform (f : ℝ → ℂ) (1 - star ρ.val) := by
    intro ρ
    rw [hg_conv]
    exact mellin_mulConv_at_zero (f : ℝ → ℂ) ρ
  have hTrEq : dixmierTrace
                (positiveOp f diracArith diracArith_isSelfAdjoint)
                (positiveOp_mem_macaev f)
                (positiveOp_isPositive f diracArith diracArith_isSelfAdjoint)
             = dixmierTrace
                (WeilFunctionalCalculus g_conv diracArith
                  diracArith_isSelfAdjoint)
                hMac hPos :=
    dixmierTrace_congr hD.symm _ _ _ _
  -- Cast en ℂ
  have hTrEqℂ : ((dixmierTrace
                (positiveOp f (diracArith (ℋ := ℋ)) diracArith_isSelfAdjoint)
                (positiveOp_mem_macaev f)
                (positiveOp_isPositive f (diracArith (ℋ := ℋ))
                  diracArith_isSelfAdjoint)
                : ℝ) : ℂ)
              = ((dixmierTrace
                (WeilFunctionalCalculus g_conv (diracArith (ℋ := ℋ))
                  diracArith_isSelfAdjoint)
                hMac hPos : ℝ) : ℂ) := by
    exact_mod_cast hTrEq
  rw [hTrEqℂ, hC]
  exact tsum_congr hB
