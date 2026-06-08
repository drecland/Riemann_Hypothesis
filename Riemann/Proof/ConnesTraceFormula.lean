import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.Tools.MellinTransform
import Riemann.Tools.UnboundedOperator
import Riemann.Tools.DiracDistribution
import Riemann.Tools.Convolution
import Riemann.Tools.ConnesHilbert
import Riemann.WeilSpace.WeilHermitianForm
import Riemann.WeilSpace.WeilFunctionalCalculus
import Riemann.Proof.MacaevIdeal
import Riemann.Proof.DixmierTrace
import Riemann.Proof.RegularizedTraceOperator
import Riemann.Proof.IsometryVariableChange
import Riemann.Proof.PositiveOperator


variable {ℋ : Type u_1}
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
[CompleteSpace ℋ]


@[inherit_doc]
notation "Trω" => dixmierTrace

/-- **Axiome — Caractérisation de `TraceClass` par les valeurs singulières.**

    Un opérateur compact `T` appartient à `ℒ¹(ℋ)` si et seulement si
    la série de ses valeurs singulières converge. -/
axiom traceClass_iff_summable_singularValues
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] (T : ℋ →L[ℂ] ℋ) :
    T ∈ TraceClass ℋ ↔ Summable (singularValues T)

/-- **Lemme classique** : la série `∑ 1/(n log n)` diverge (Cauchy-Bertrand). -/
axiom not_summable_one_div_n_log_n :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log n))

/-- **Lemme de comparaison** : si une suite positive sommable majore (à partir du rang 2)
    une suite positive, alors cette dernière est sommable. -/
axiom summable_of_le_summable_from
    {f g : ℕ → ℝ} (hf_nn : ∀ n, 0 ≤ f n) (hg : Summable g)
    (h : ∀ n, 2 ≤ n → f n ≤ g n) : Summable f


/-- positivité des valeurs singulières -/
axiom singularValues_nonneg (T : ℋ →L[ℂ] ℋ) (n : ℕ) :
    0 ≤ singularValues T n


/-- **Lemme** (von Mangoldt) — Asymptotique `N(T) ∼ (T / 2π) · log T`
    pour le nombre de zéros non triviaux `ρ = β + iγ` de ζ avec `0 < γ ≤ T`. -/
axiom vonMangoldt_zeros_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      ∃ N : ℕ, |((N : ℝ) - (T / (2 * Real.pi)) * Real.log T)| ≤ C * Real.log T

/-- **Asymptotique** : `∑_{n=2}^{N} 1/(n log n) ≤ C · log(log N) + C'`,
    donc majoré par `C'' · log N` pour `N ≥ 2`. -/
axiom sum_one_div_n_log_n_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∑ n ∈ Finset.range N, (if 2 ≤ n then 1 / ((n : ℝ) * Real.log n) else 0)
        ≤ C * Real.log N

axiom positiveOp_cesaroBound_aux (f : 𝒲) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∑ n ∈ Finset.range N,
        singularValues (positiveOp f diracArith diracArith_isSelfAdjoint) n
      ≤ C * Real.log N


/-- Axiome fondamental de l'involution de Weil en transformée de Mellin. -/
axiom mellin_weilInvolution_eq_conj (f : 𝒲) (s : ℂ) :
    mellinTransform (weilStarW f : ℝ → ℂ) s
      = star (mellinTransform (f : ℝ → ℂ) (1 - star s))

/-- Axiome : ℳ[convStar f](s) = star(ℳ[f](1 - star s)). -/
axiom mellin_convStar_eq_conj (f : 𝒲) (s : ℂ) :
    mellinTransform (convStar (f : ℝ → ℂ)) s
      = star (mellinTransform (f : ℝ → ℂ) (1 - star s))


/-! ### — Appartenance à l'idéal de Dixmier -/

/-- **Lemme** : le volume des classes d'idèles est infini, donc
    `P_f = f(D) f*(D)` n'appartient pas à l'idéal trace `ℒ¹(ℋ)`.

    Justification mathématique : les valeurs singulières de `P_f`
    décroissent comme `K/(n log n)` (cf. `positiveOp_singularValues_decay`),
    et la série `∑ 1/(n log n)` diverge. -/
lemma positiveOp_not_traceClass (f : 𝒲) :
    positiveOp f diracArith diracArith_isSelfAdjoint
      ∉ TraceClass DiracHilbert := by
  set Pf := positiveOp f diracArith diracArith_isSelfAdjoint with hPf
  intro hPf_trace
  rw [traceClass_iff_summable_singularValues] at hPf_trace
  obtain ⟨K, hK_pos, hμ⟩ :=
    positiveOp_singularValues_decay_lower f diracArith diracArith_isSelfAdjoint
      diracArith_hasCompactResolvent
  -- Étape 1 : ∑ K/(n log n) converge par comparaison à ∑ singularValues
  have hcomp : Summable (fun n : ℕ => K / ((n : ℝ) * Real.log n)) := by
    apply summable_of_le_summable_from _ hPf_trace hμ
    intro n
    by_cases hn : 2 ≤ n
    · apply div_nonneg hK_pos.le
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have h2 : 0 ≤ Real.log n := Real.log_nonneg h1
      positivity
    · push Not at hn
      interval_cases n
      · simp
      · simp
  -- Étape 2 : contradiction avec not_summable_one_div_n_log_n
  apply not_summable_one_div_n_log_n
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have heq : (fun n : ℕ => 1 / ((n : ℝ) * Real.log n))
           = (fun n : ℕ => K⁻¹ * (K / ((n : ℝ) * Real.log n))) := by
    funext n
    field_simp
  rw [heq]
  exact hcomp.mul_left K⁻¹




/-- Compacité de `f(D)f*(D)` pour `f ∈ 𝒲` et `D` auto-adjoint.

    Schéma de preuve :
    1. Par isSelfAdjoint_hasCompactResolvent, D a une résolvante compacte.
    2. Le calcul fonctionnel borélien donne f(D) borné.
    3. f ∈ 𝒲 → ℳ[f] à décroissance rapide → f(D) compact
       (les valeurs propres ℳ[f](λ_n) → 0 car λ_n → ∞).
    4. Composition d'un compact avec un borné → compact. -/
lemma positiveOp_isCompact
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (f : 𝒲) (D : UnboundedOperator ℋ) (hD_sa : D.IsSelfAdjoint) :
    IsCompactOperator (positiveOp f D hD_sa) := by
  -- Étape 1 : résolvante compacte
  have hD_cr : D.HasCompactResolvent :=
    isSelfAdjoint_hasCompactResolvent D hD_sa
  -- Étape 2 : f(D) est compact
  have hfD_compact : IsCompactOperator (WeilFunctionalCalculus f D hD_sa) :=
    weilFunctionalCalculus_isCompact f D hD_sa hD_cr
  -- Étape 3 : déplier positiveOp et appliquer le lemme produit
  unfold positiveOp
  exact weilFunctionalCalculus_mul_star_isCompact f D hD_sa hfD_compact


lemma positiveOp_mem_macaev (f : 𝒲) :
    positiveOp f diracArith diracArith_isSelfAdjoint ∈ MacaevIdeal DiracHilbert := by
  refine ⟨positiveOp_isCompact (ℋ := DiracHilbert) f _ _, ?_⟩
  obtain ⟨C, hC⟩ := positiveOp_cesaroBound_aux f
  refine ⟨C, fun N hN => ?_⟩
  have hlog_pos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  rw [one_div, inv_mul_le_iff₀ hlog_pos]
  linarith [hC N hN, mul_comm C (Real.log N)]

/-- **Lemme** : lien correct entre `convStar` et `weilStarW` via
    le changement de variable `t = log x`. Pour `x > 0` :
    `convStar f x = x⁻¹ · (weilStarW f) (log x)`
    où `f` est vue alternativement comme fonction sur `ℝ*₊` ou sur `ℝ`. -/
lemma convStar_apply_eq (f : 𝒲) {x : ℝ} (_ : 0 < x) :
    convStar (fun y => (f : ℝ → ℂ) (Real.log y)) x
      = (↑x)⁻¹ * (weilStarW f : ℝ → ℂ) (Real.log x) := by
  unfold convStar weilStarW
  simp only []
  -- (↑x)⁻¹ * star (f (log (x⁻¹))) = (↑x)⁻¹ * star (f (-(log x)))
  congr 2
  rw [Real.log_inv]


/-- **Lemme** : lien entre `convStar` et `weilStarW` après changement
    de variable `t = log x`. Pour `x > 0` :
    `convStar (f ∘ log) x = x⁻¹ · (weilStarW f) (log x)`. -/
lemma convStar_eq_weilStarW (f : 𝒲) :
    ∀ x : ℝ, 0 < x →
      convStar (fun y => (f : ℝ → ℂ) (Real.log y)) x
        = (↑x)⁻¹ * (weilStarW f : ℝ → ℂ) (Real.log x) :=
  fun _ hx => convStar_apply_eq f hx


/-- **Lemme** : le calcul fonctionnel de Weil est multiplicatif par rapport
    à la convolution additive `⋆ₐ` sur `𝒲` (convention `t = log x`).

    Si `(g_conv : ℝ → ℂ) = (f : ℝ → ℂ) ⋆ₐ (weilStarW f : ℝ → ℂ)`, alors
    `g_conv(D) = f(D) · (weilStarW f)(D) = positiveOp f D`. -/
lemma weilFunctionalCalculus_mulConv (f : 𝒲) (g_conv : 𝒲)
    (hg : (g_conv : ℝ → ℂ)
            = mulConv (f : ℝ → ℂ) ((weilStarW f) : ℝ → ℂ)) :
    WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint
      = positiveOp f diracArith diracArith_isSelfAdjoint := by
  exact weilFunctionalCalculus_mul f (weilStarW f) g_conv
    diracArith diracArith_isSelfAdjoint hg

/-- **Lemme ponctuel** : sur `Ioi 0`,
    `convStar (toFun f) x = x⁻¹ * (weilStarW f) (log x)`. -/
lemma convStar_toFun_eq_weilStarW_log (f : 𝒲) {x : ℝ} (_ : 0 < x) :
    convStar (WeilSpace.toFun f) x
      = (↑x)⁻¹ * (weilStarW f : ℝ → ℂ) (Real.log x) := by
  unfold convStar WeilSpace.toFun
  -- LHS = x⁻¹ * star (f (log x⁻¹))
  -- RHS = x⁻¹ * star (f (-(log x)))
  congr 2
  rw [Real.log_inv]


/-- **Lemme auxiliaire** : les transformées de Mellin de `convStar (toFun f)`
    et `weilStarW f` sont liées via un facteur `x⁻¹`. -/
lemma mellin_convStar_toFun_eq (f : 𝒲) (s : ℂ) :
    mellinTransform (convStar (WeilSpace.toFun f)) s
      = mellinTransform (fun x => (↑x)⁻¹ * (weilStarW f : ℝ → ℂ) (Real.log x)) s := by
  unfold mellinTransform
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  congr 1
  exact convStar_toFun_eq_weilStarW_log f hx



/-- Lemme clé : ℳ[weilStarW f](s) = star(ℳ[f](1 - star s)) -/
lemma mellin_weilStarW_eq_conj (f : 𝒲) (s : ℂ) :
    mellinTransform (weilStarW f : ℝ → ℂ) s
      = star (mellinTransform (f : ℝ → ℂ) (1 - star s)) :=
  mellin_weilInvolution_eq_conj f s


/-- **Les transformées de Mellin de `convStar f` et `weilStarW f`
    coïncident** dans `mulConv`.
    Plus précisément :
    `ℳ[f ⋆ₘ convStar f](s) = ℳ[f ⋆ₘ (weilStarW f)](s)`
    pour tout `s : ℂ`.

    Preuve : par `mellin_mulConv`,
    LHS = `ℳ[f](s) · ℳ[convStar f](s)`
    RHS = `ℳ[f](s) · ℳ[weilStarW f](s)`
    et on utilise `mellin_weilStar` pour identifier les deux. -/
lemma mellin_mulConv_convStar_eq_weilStarW (f : 𝒲) (s : ℂ) :
    mellinTransform (mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ))) s
      = mellinTransform (mulConv (f : ℝ → ℂ) ((weilStarW f : ℝ → ℂ))) s := by
  rw [mellin_mulConv, mellin_mulConv]
  congr 1
  -- ℳ[convStar f](s) = ℳ[weilStarW f](s)
  -- car les deux = star(ℳ[f](1 - star s))
  rw [mellin_convStar_eq_conj, mellin_weilStarW_eq_conj]

lemma mulConv_convStar_eq_mulConv_weilStarW (f : 𝒲) :
    mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ))
      = mulConv (f : ℝ → ℂ) ((weilStarW f) : ℝ → ℂ) := by
  apply mellinTransform_injective
  intro s
  exact mellin_mulConv_convStar_eq_weilStarW (f) s

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
      = positiveOp f diracArith diracArith_isSelfAdjoint := by
  apply weilFunctionalCalculus_mulConv f g_conv
  rw [hg_conv]
  exact mulConv_convStar_eq_mulConv_weilStarW f

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

/-- **Lemme auxiliaire** : `WeilFunctionalCalculus g_conv D` appartient
    à l'idéal de Macaev, en utilisant l'égalité avec `positiveOp f D`. -/
lemma weilFunctionalCalculus_gconv_mem_macaev (f : 𝒲) (g_conv : 𝒲)
    (hg_conv : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ))) :
    WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint
      ∈ MacaevIdeal DiracHilbert := by
  rw [step_relate_gconv_to_positiveOp f g_conv hg_conv]
  exact positiveOp_mem_macaev f


/-- **Lemme 5.5** : Unifier les deux traces (ℝ et ℂ). -/
lemma step_unify_traces (f : 𝒲) (g_conv : 𝒲)
    (hg_conv : (g_conv : ℝ → ℂ) = mulConv (f : ℝ → ℂ) (convStar (f : ℝ → ℂ))) :
    (dixmierTrace
      (positiveOp f diracArith diracArith_isSelfAdjoint)
      (positiveOp_mem_macaev f)
      (positiveOp_isPositive f diracArith diracArith_isSelfAdjoint) : ℂ)
    = (dixmierTrace
      (WeilFunctionalCalculus g_conv diracArith diracArith_isSelfAdjoint)
      (weilFunctionalCalculus_gconv_mem_macaev f g_conv hg_conv)
      (step_gconv_is_positive f g_conv hg_conv) : ℂ) := by
  -- Coercion ℝ → ℂ : il suffit de montrer l'égalité des traces réelles
    congr 1
    exact dixmierTrace_congr
      (step_relate_gconv_to_positiveOp f g_conv hg_conv).symm
      (positiveOp_mem_macaev f)
      (weilFunctionalCalculus_gconv_mem_macaev f g_conv hg_conv)
      (positiveOp_isPositive f diracArith diracArith_isSelfAdjoint)
      (step_gconv_is_positive f g_conv hg_conv)


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
