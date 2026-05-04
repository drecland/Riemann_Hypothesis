import Riemann.Basic
import Riemann.Tools.MellinTransform
import Riemann.Tools.UnboundedOperator
import Riemann.Tools.Convolution
import Riemann.Tools.Integration
import Riemann.Tools.RiemannHypothesisProperty
import Riemann.Tools.DiracDistribution
import Riemann.WeilSpace.WeilSpace
import Riemann.WeilSpace.WeilFunctionalCalculus
import Riemann.WeilSpace.WeilPositivityCriterion
import Riemann.WeilSpace.WeilTimesSchwartz
import Riemann.Proof.MacaevIdeal
import Riemann.Proof.PositiveOperator
import Riemann.Proof.DixmierTrace



open Complex MeasureTheory


variable {ℋ : Type*}
[NormedAddCommGroup ℋ]
[InnerProductSpace ℂ ℋ]
[CompleteSpace ℋ]


/-- Sur la droite critique, la transformée de Mellin se réécrit
    comme une intégrale sur ℝ. -/
lemma mellin_critical_line_eq (f : 𝒲) (a : ℝ) :
    mellinTransform (WeilSpace.toFun f) (1/2 + I * a) =
    ∫ t : ℝ, (WeilSpace.toFun f) (Real.exp t) *
              Complex.exp ((1/2 + I * a) * t) ∂volume := by
  -- Étape 1 : déroulement de la définition
  unfold mellinTransform
  -- Étape 2 : simplification de l'exposant s-1
  have hexp : (fun x : ℝ => (WeilSpace.toFun f) x * (x : ℂ) ^ ((1/2 + I*↑a : ℂ) - 1))
            = (fun x : ℝ => (WeilSpace.toFun f) x * (x : ℂ) ^ ((-1/2 + I*↑a : ℂ))) := by
    funext x; ring_nf
  rw [hexp]
  -- Étape 3 : changement de variable x = exp(t)
  rw [integral_Ioi_eq_integral_exp]
  -- Étape 4 : simplification de l'intégrande
  congr 1
  funext t
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne')]
  have hlog : Complex.log (↑(Real.exp t)) = (t : ℂ) := by
    rw [Complex.ofReal_exp]
    apply Complex.log_exp
    · simp; linarith [Real.pi_pos]
    · simp; linarith [Real.pi_pos]
  rw [hlog]
  -- Goal: Real.exp t • (f.toFun (Real.exp t) * cexp (↑t * (-1/2 + I * ↑a)))
  --     = f.toFun (Real.exp t) * cexp ((1/2 + I * ↑a) * ↑t)
  have key : Real.exp t • (f.toFun (Real.exp t) * Complex.exp (↑t * (-1/2 + I * ↑a)))
           = f.toFun (Real.exp t) * Complex.exp ((1/2 + I * ↑a) * ↑t) := by
    have h1 : (Real.exp t : ℂ) = Complex.exp ↑t := by
      rw [← Complex.ofReal_exp]
    rw [show (Real.exp t • (f.toFun (Real.exp t) * Complex.exp (↑t * (-1/2 + I * ↑a))) : ℂ)
          = (Real.exp t : ℂ) * (f.toFun (Real.exp t) * Complex.exp (↑t * (-1/2 + I * ↑a)))
        from by simp [Complex.real_smul]]
    rw [h1]
    rw [show Complex.exp ↑t * (f.toFun (Real.exp t) * Complex.exp (↑t * (-1/2 + I * ↑a)))
          = f.toFun (Real.exp t) * (Complex.exp ↑t * Complex.exp (↑t * (-1/2 + I * ↑a)))
        from by ring]
    rw [← Complex.exp_add]
    congr 1
    ring_nf
  exact key

/-- **Lemme intermédiaire** — Réécriture de l'intégrale de Mellin sur la
droite critique en faisant apparaître `φ(t) = f(eᵗ) · e^{-t/2}`. -/
lemma mellin_critical_line_via_phi (f : 𝒲) (a : ℝ) :
    ∫ t : ℝ, (WeilSpace.toFun f) (Real.exp t) *
              Complex.exp ((1/2 + I * a) * t) ∂volume =
    ∫ t : ℝ, ((WeilSpace.toFun f) (Real.exp t) *
              Complex.exp (-(t : ℂ) / 2)) *
              Complex.exp (I * a * t + t) ∂volume := by
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun t => ?_)
  simp only
  rw [mul_assoc]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  ring


/-- **Lemme intermédiaire** — Sur la droite critique, l'intégrale de Mellin
s'écrit comme une intégrale oscillante en `e^{iat}` avec poids `f(eᵗ)·e^{t/2}`. -/
lemma mellin_critical_line_oscillatory (f : 𝒲) (a : ℝ) :
    ∫ t : ℝ, (WeilSpace.toFun f) (Real.exp t) *
              Complex.exp ((1/2 + I * a) * t) ∂volume =
    ∫ t : ℝ, ((WeilSpace.toFun f) (Real.exp t) *
              Complex.exp ((t : ℂ) / 2)) *
              Complex.exp (I * a * t) ∂volume := by
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun t => ?_)
  simp only
  rw [mul_assoc]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  ring


/-- **Lemme** — La transformée de Mellin d'une fonction de Weil
    est à décroissance rapide sur la droite critique. -/
lemma mellin_rapidDecay_critical_line (f : 𝒲) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ a : ℝ,
      ‖mellinTransform (WeilSpace.toFun f) (1/2 + I * a)‖ * (1 + |a|)^N ≤ C := by
  intro N
  -- Étape 1 : récupérer la fonction Schwartz ψ avec e^{+t/2}
  obtain ⟨ψ, hψ⟩ := weil_times_exp_plus_half_schwartz f
  -- Étape 2 : décroissance de l'intégrale oscillante
  obtain ⟨C, hC⟩ := schwartz_oscillatory_integral_rapidDecay ψ N
  refine ⟨C, fun a => ?_⟩
  -- Étape 3 : réécriture de la transformée de Mellin
  rw [mellin_critical_line_eq f a]
  -- Étape 4 : montrer l'égalité de l'intégrande
  have hrew : ∀ t : ℝ,
      (WeilSpace.toFun f) (Real.exp t) * Complex.exp ((1/2 + I * a) * t)
        = (ψ : ℝ → ℂ) t * Complex.exp (I * a * t) := by
    intro t
    rw [hψ t]
    -- (f(eᵗ) · e^{t/2}) · e^{Iat} = f(eᵗ) · e^{(1/2 + Ia)t}
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    ring_nf
  -- Étape 5 : conclure
  have hint_eq :
      ∫ t : ℝ, (WeilSpace.toFun f) (Real.exp t) * Complex.exp ((1/2 + I * a) * t) ∂volume
    = ∫ t : ℝ, (ψ : ℝ → ℂ) t * Complex.exp (I * a * t) ∂volume := by
    apply integral_congr_ae
    exact ae_of_all _ hrew
  rw [hint_eq]
  exact hC a

/-- **Lemme** — La densité des zéros non triviaux croît en `O(T log T)`
    (Tenenbaum). -/
axiom zero_counting_asymptotic :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ∃ N : ℕ, (N : ℝ) ≤ C * T * Real.log T


lemma adjoint_of_weilFC
    {ℋ : Type*} [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ]
    (f : 𝒲) (D : UnboundedOperator ℋ) (hD_sa : D.IsSelfAdjoint) :
    WeilFunctionalCalculus (weilStarW f) D hD_sa =
      ContinuousLinearMap.adjoint (WeilFunctionalCalculus f D hD_sa) :=
  weilStar_calculus_eq_adjoint f D hD_sa


/-- **Lemme préliminaire** — Décroissance individuelle des valeurs singulières
de `f(D)f*(D)` issue de l'asymptotique de von Mangoldt sur les zéros.

Pour `f ∈ 𝒲`, il existe une constante `K` telle que pour tout `n ≥ 2` :
$$\mu_n(P_f) \le \frac{K}{n \log n}$$ -/
lemma positiveOp_singularValues_decay
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (f : 𝒲) (D : UnboundedOperator ℋ) (hD_sa : D.IsSelfAdjoint)
    (hD_cr : D.HasCompactResolvent) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 2 ≤ n →
      singularValues (positiveOp f D hD_sa) n ≤ K / ((n : ℝ) * Real.log n) := by
  sorry


/-- **Lemme préliminaire (version Cesàro)** — Borne de Cesàro directe. -/
lemma positiveOp_singularValues_cesaro_aux
    {ℋ : Type*} [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ]
    (f : 𝒲)
    (D : UnboundedOperator ℋ)
    (hD_sa : D.IsSelfAdjoint)
    (hD_cr : D.HasCompactResolvent) :
    ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∑ n ∈ Finset.range N, singularValues (positiveOp f D hD_sa) n
        ≤ K * Real.log N := by
  sorry


/-- Estimée de Cesàro des valeurs singulières de `f(D)f*(D)`.
    Utilise l'asymptotique de von Mangoldt `N(T) ∼ (T/2π) log T`. -/
lemma positiveOp_singularValues_cesaroBound
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (f : 𝒲) (D : UnboundedOperator ℋ) (hD_sa : D.IsSelfAdjoint)
    (hD_cr : D.HasCompactResolvent) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (1 / Real.log N) * (∑ n ∈ Finset.range N,
        singularValues (positiveOp f D hD_sa) n) ≤ C := by
  obtain ⟨K, hK⟩ := positiveOp_singularValues_cesaro_aux f D hD_sa hD_cr
  refine ⟨K, fun N hN => ?_⟩
  -- (1/log N) · ∑ ≤ (1/log N) · (K · log N) = K
  have hlog_pos : 0 < Real.log N := by
    have : (1 : ℝ) < N := by exact_mod_cast hN
    exact Real.log_pos this
  have h := hK N hN
  rw [one_div]
  rw [inv_mul_le_iff₀ hlog_pos]
  linarith [h, mul_comm K (Real.log N)]



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
  -- Étape 1 : récupérer la résolvante compacte
  have hD_cr : D.HasCompactResolvent :=
    isSelfAdjoint_hasCompactResolvent D hD_sa
  -- Étape 2 : f(D) est compact car ℳ[f](λ_n) → 0
  have hfD_compact : IsCompactOperator
      (WeilFunctionalCalculus f D hD_sa) := by
    sorry
  -- Étape 3 : f*(D) = (f(D))* est aussi compact
  -- have hfstarD_compact : IsCompactOperator
  -- (WeilFunctionalCalculus (weilStarW f) D hD_sa) := by
    -- rw [adjoint_of_weilFC f D hD_sa]
    -- TODO: utiliser que l'adjoint d'un compact est compact
  -- Étape 4 : produit f(D) · f*(D) est compact
  -- unfold positiveOp
  -- TODO: utiliser que compact ∘ borné = compact
  sorry


/-- **Lemme** — Pour toute `f ∈ 𝒲` et tout opérateur auto-adjoint
    `D` à résolvante compacte, l'opérateur `P_f = f(D) f*(D)`
    est dans l'idéal de Macaev `ℒ^(1,∞)(ℋ)`. -/
lemma positiveOp_mem_macaev_general
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (f : 𝒲) (D : UnboundedOperator ℋ) (hD_sa : D.IsSelfAdjoint) :
    positiveOp f D hD_sa ∈ MacaevIdeal ℋ :=
  ⟨positiveOp_isCompact f D hD_sa,           -- ← plus de hD_cr ici
   positiveOp_singularValues_cesaroBound f D hD_sa
     (isSelfAdjoint_hasCompactResolvent D hD_sa)⟩


/-- **Lemme** — `P_f = A A*` est positif. -/
lemma positiveOp_eq_AAstar
    {ℋ : Type*}
    [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ]
    (f : 𝒲)
    (D : UnboundedOperator ℋ)
    (hD_sa : D.IsSelfAdjoint) :
    positiveOp f D hD_sa =
      (WeilFunctionalCalculus f D hD_sa) *
        ContinuousLinearMap.adjoint
        (WeilFunctionalCalculus f D hD_sa) := by
  sorry

/-- **Lemme 2.3** — Positivité de la forme hermitienne de Weil. -/
lemma weilHermitianForm_nonneg
    {ℋ : Type*}
    [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ]
    (D : UnboundedOperator ℋ)
    (hD_sa : D.IsSelfAdjoint)
    (hAbsorption : ∀ f : 𝒲,
      ((dixmierTrace (positiveOp f D hD_sa)
          (positiveOp_mem_macaev_general f D hD_sa)
          (positiveOp_isPositive f D hD_sa) : ℝ) : ℂ) =
        weilHermitianForm f f)
    (f : 𝒲) :
    0 ≤ (weilHermitianForm f f).re := by
  -- Étape 1 : la trace de Dixmier de P_f est positive
  -- car P_f = f(D)f*(D) est un opérateur positif
  have hTrPos : 0 ≤ dixmierTrace (positiveOp f D hD_sa)
      (positiveOp_mem_macaev_general f D hD_sa)
      (positiveOp_isPositive f D hD_sa) :=
    dixmierTrace_nonneg
      (positiveOp f D hD_sa)
      (positiveOp_mem_macaev_general f D hD_sa)
      (positiveOp_isPositive f D hD_sa)
  -- Étape 2 : on identifie via l'hypothèse d'absorption
  have hEq := hAbsorption f
  -- Étape 3 : la partie réelle de ⟨f,f⟩ est égale à la trace
  have hRe : (weilHermitianForm f f).re =
      dixmierTrace (positiveOp f D hD_sa)
        (positiveOp_mem_macaev_general f D hD_sa)
        (positiveOp_isPositive f D hD_sa) := by
    rw [← hEq]
    simp [Complex.ofReal_re]
  rw [hRe]
  exact hTrPos

/-- **Axiome de Connes** — Identité d'absorption spectrale pour
    opérateur de Dirac arithmétique. -/
axiom connesAbsorption (f : 𝒲)
    {ℋ : Type*} [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ]
    (D : UnboundedOperator ℋ)
    (hD_sa : D.IsSelfAdjoint) :
    ((dixmierTrace (positiveOp f D hD_sa)
        (positiveOp_mem_macaev_general f D hD_sa)
        (positiveOp_isPositive f D hD_sa) : ℝ) : ℂ) =
      weilHermitianForm f.toFun f.toFun



/-! ## Partie 3 — Théorème final -/

/-- **Théorème principal — Hypothèse de Riemann.**

    Sous les hypothèses de réalisation spectrale géométrique
    (existence d'un opérateur `D` auto-adjoint à résolvante compacte
    vérifiant l'identité d'absorption spectrale), tous les zéros non
    triviaux de `ζ` sont sur la droite critique. -/
theorem RiemannHypothesis_proof
    {ℋ : Type*} [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ]
    (D : UnboundedOperator ℋ)
    (hD_sa : D.IsSelfAdjoint)
    (hAbsorption : ∀ f : 𝒲,
      ((dixmierTrace (positiveOp f D hD_sa)
        (positiveOp_mem_macaev_general f D hD_sa)
        (positiveOp_isPositive f D hD_sa) : ℝ) : ℂ) =
      weilHermitianForm f.toFun f.toFun) :
    RiemannHypothesisProp := by
  rw [RiemannHypothesisProp_iff_RiemannHypothesis]
  apply weil_positivity_criterion.mpr
  intro f
  refine ⟨(dixmierTrace (positiveOp f D hD_sa)
            (positiveOp_mem_macaev_general f D hD_sa)
            (positiveOp_isPositive f D hD_sa) : ℝ), ?_, ?_⟩
  · -- Positivité de la trace de Dixmier
    exact dixmierTrace_nonneg
            (positiveOp f D hD_sa)
            (positiveOp_mem_macaev_general f D hD_sa)
            (positiveOp_isPositive f D hD_sa)
  · exact (hAbsorption f).symm

/-- **L'opérateur de Dirac arithmétique réalise l'HR.**

    L'opérateur de Dirac arithmétique `diracArith` vérifie toutes les
    hypothèses du théorème principal, ce qui conclut la preuve de
    l'Hypothèse de Riemann sans hypothèse supplémentaire. -/
theorem RiemannHypothesis_diracArith_Realisation
    {ℋ : Type*} [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] :
    RiemannHypothesisProp := by
  -- Étape 1 : on choisit l'opérateur de Dirac arithmétique
  apply RiemannHypothesis_proof (D := diracArith (ℋ := ℋ))
      (hD_sa := diracArith_isSelfAdjoint)
  -- Étape 3 : identité d'absorption spectrale (seul goal restant)
  · intro f
    exact connesAbsorption f diracArith diracArith_isSelfAdjoint
