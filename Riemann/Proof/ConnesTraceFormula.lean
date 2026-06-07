import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.Tools.MellinTransform
import Riemann.Tools.UnboundedOperator
import Riemann.Tools.DiracDistribution
import Riemann.WeilSpace.WeilHermitianForm
import Riemann.Proof.MacaevIdeal
import Riemann.Proof.DixmierTrace
import Riemann.Proof.RegularizedTraceOperator
import Riemann.Tools.ConnesHilbert
import Riemann.Proof.PositiveOperator


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

-- Lemme 1 : positiveOp appartient à MacaevIdeal
lemma positiveOp_mem_macaev (f : 𝒲) :
    positiveOp f diracArith diracArith_isSelfAdjoint ∈ MacaevIdeal DiracHilbert := by
  sorry


-- Lemme 2 : calcul fonctionnel préserve la convolution
lemma weilFunctionalCalculus_mulConv (f : 𝒲) (g_conv : 𝒲)
    (hg : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ))) :
    WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint
      = positiveOp f diracArith diracArith_isSelfAdjoint := by
  sorry




/-- **Lemme** : `g(D)` agit comme la multiplication par `ℳ[g](ρ)`
    sur le vecteur propre `ψ_ρ`. -/
lemma functionalCalculus_eigenvalues
    (g : 𝒲) (ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)}) :
    let D := diracArith
    let ψ := diracEigenvector_diag ρ
    -- vecteur de base dans ℓ²(𝒵)
    WeilFunctionalCalculus g D diracArith_isSelfAdjoint ψ
      = (mellinTransform (g : ℝ → ℂ) ρ.val) • ψ := by
  sorry


/-- **Lemme** (théorème de la trace de Connes) : pour `g ∈ 𝒲` telle
    que `g(D) ∈ ℒ^{1,∞}(ℋ)` est positif et que `ρ ↦ ℳ[g](ρ)` est
    sommable, la trace de Dixmier coïncide avec la somme spectrale. -/
lemma dixmierTrace_eq_sum_eigenvalues
    (g : 𝒲)
    (hPos : ∀ x : DiracHilbert, 0 ≤ (@inner ℂ _ _
              (WeilFunctionalCalculus g
              diracArith diracArith_isSelfAdjoint x)
              x).re)
    (_hsum : Summable
      (fun ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)} =>
        mellinTransform (g : ℝ → ℂ) ρ.val)) :
    let op := WeilFunctionalCalculus g diracArith diracArith_isSelfAdjoint
    let hMac : op ∈ MacaevIdeal DiracHilbert := by
      -- À prouver : op appartient à l'idéal de Macaev
      sorry  -- ou une vraie preuve selon ta théorie
    (dixmierTrace op hMac hPos : ℂ)
      = ∑' ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)},
          mellinTransform (g : ℝ → ℂ) ρ.val := by
  sorry

/-! ### — Lemmes intermédiaires pour la preuve principale -/

/-- **Lemme 5.1** : Relier `g_conv` à `positiveOp` via le calcul fonctionnel. -/
lemma step_relate_gconv_to_positiveOp (f : 𝒲) (g_conv : 𝒲)
    (hg_conv : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ))) :
    WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint
      = positiveOp f diracArith diracArith_isSelfAdjoint :=
  weilFunctionalCalculus_mulConv f g_conv hg_conv

/-- **Lemme 5.2** : Montrer que `g_conv[D]` est positif. -/
lemma step_gconv_is_positive (f : 𝒲) (g_conv : 𝒲)
    (hg_conv : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ))) :
    ∀ x : DiracHilbert, 0 ≤ (@inner ℂ _ _
      (WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint x)
      x).re := by
  intro x
  have hD := step_relate_gconv_to_positiveOp f g_conv hg_conv
  rw [hD]
  exact positiveOp_isPositive f diracArith diracArith_isSelfAdjoint x

/-- **Lemme 5.2b** : `g_conv[D]` appartient à MacaevIdeal. -/
lemma step_gconv_mem_macaev (f : 𝒲) (g_conv : 𝒲)
    (hg_conv : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ))) :
    WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint ∈
    MacaevIdeal DiracHilbert := by
  have hD := step_relate_gconv_to_positiveOp f g_conv hg_conv
  rw [hD]
  exact positiveOp_mem_macaev f

/-- **Lemme 5.3** : Appliquer le théorème de la trace de Connes. -/
lemma step_apply_connes_trace (f : 𝒲) (g_conv : 𝒲)
    (hg_conv : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ)))
    (hsum : Summable
      (fun ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)} =>
        mellinTransform (g_conv : ℝ → ℂ) ρ.val)) :
    (dixmierTrace
      (WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint)
      (step_gconv_mem_macaev f g_conv hg_conv)
      (step_gconv_is_positive f g_conv hg_conv) : ℂ)
      = ∑' ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)},
          mellinTransform (g_conv : ℝ → ℂ) ρ.val :=
  dixmierTrace_eq_sum_eigenvalues g_conv (step_gconv_is_positive f g_conv hg_conv) hsum


/-- **Lemme 5.4** : Relier les transformations de Mellin via la convolution. -/
lemma step_mellin_from_convolution (f : 𝒲) (g_conv : 𝒲)
    (hg_conv : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ))) :
    ∀ ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)},
      mellinTransform (g_conv : ℝ → ℂ) ρ.val
        = mellinTransform (f : ℝ → ℂ) ρ.val
          * mellinTransform (f : ℝ → ℂ) (1 - star ρ.val) := by
  intro ρ
  rw [hg_conv]
  exact mellin_mulConv_at_zero (f : ℝ → ℂ) ρ


/-- **Lemme 5.5** : Unifier les deux traces (ℝ et ℂ). -/
lemma step_unify_traces (f : 𝒲) (g_conv : 𝒲)
    (hg_conv : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ))) :
    (dixmierTrace
      (positiveOp f diracArith diracArith_isSelfAdjoint)
      (positiveOp_mem_macaev f)
      (positiveOp_isPositive f diracArith diracArith_isSelfAdjoint) : ℂ)
    = (dixmierTrace
      (WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint)
      (by sorry : WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint ∈
                  MacaevIdeal DiracHilbert)
      (step_gconv_is_positive f g_conv hg_conv) : ℂ) := by
  have hD := step_relate_gconv_to_positiveOp f g_conv hg_conv
  convert rfl

/-- **Lemme 5.6** : Égalité des sommes spectrales. -/
lemma step_spectral_sum_equality (f : 𝒲) (g_conv : 𝒲)
    (hg_conv : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ)))
    (_ : Summable
      (fun ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)} =>
        mellinTransform (g_conv : ℝ → ℂ) ρ.val)) :
    ∑' ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)},
      mellinTransform (g_conv : ℝ → ℂ) ρ.val
    = ∑' ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)},
        mellinTransform (f : ℝ → ℂ) ρ.val
          * mellinTransform (f : ℝ → ℂ) (1 - star ρ.val) :=
  tsum_congr (step_mellin_from_convolution f g_conv hg_conv)


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
    (dixmierTrace
        (positiveOp f diracArith diracArith_isSelfAdjoint)
        (positiveOp_mem_macaev f)
        (positiveOp_isPositive f diracArith diracArith_isSelfAdjoint) : ℂ)
      = ∑' ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)},
          mellinTransform (f : ℝ → ℂ) ρ.val
            * mellinTransform (f : ℝ → ℂ) (1 - star ρ.val) := by
  calc (dixmierTrace
        (positiveOp f diracArith diracArith_isSelfAdjoint)
        (positiveOp_mem_macaev f)
        (positiveOp_isPositive f diracArith diracArith_isSelfAdjoint) : ℂ)
      = (dixmierTrace
        (WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint)
        (step_gconv_mem_macaev f g_conv hg_conv)
        (step_gconv_is_positive f g_conv hg_conv) : ℂ) :=
        step_unify_traces f g_conv hg_conv
    _ = ∑' ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)},
          mellinTransform (g_conv : ℝ → ℂ) ρ.val :=
        step_apply_connes_trace f g_conv hg_conv hsum
    _ = ∑' ρ : {z : ℂ // z ∈ (𝒵 : Set ℂ)},
          mellinTransform (f : ℝ → ℂ) ρ.val
            * mellinTransform (f : ℝ → ℂ) (1 - star ρ.val) :=
        step_spectral_sum_equality f g_conv hg_conv hsum
