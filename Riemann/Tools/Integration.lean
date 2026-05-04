import Riemann.Basic
import Riemann.Tools.HaarMeasure

open Real Complex SchwartzMap
open MeasureTheory
open scoped MeasureTheory


/-- Convertit l'intégrale Bochner en lintegral côté haarMul -/
lemma integral_sq_haarMul_eq_lintegral (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2)
    (haarMul.restrict (Set.Ioi 0))) :
    ∫ x in Set.Ioi (0:ℝ), ‖f x‖^2 ∂haarMul =
    (∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal
    (‖f x‖^2) ∂haarMul).toReal := by
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · apply ae_of_all; intro x; positivity
  · exact hf

lemma restrict_withDensity_comm (f : ℝ → ENNReal)
    (_ : Measurable f)
    (s : Set ℝ)
    (hs : MeasurableSet s) :
    (volume.withDensity f).restrict s =
    (volume.restrict s).withDensity f := by
  ext t ht
  rw [Measure.restrict_apply ht]
  rw [MeasureTheory.withDensity_apply f (ht.inter hs)]
  rw [MeasureTheory.withDensity_apply f ht]
  rw [Measure.restrict_restrict ht]


lemma restrict_withDensity_eq (f : ℝ → ENNReal)
    (hf : Measurable f) (s : Set ℝ) (hs : MeasurableSet s) :
    (volume.withDensity f).restrict s =
    (volume.restrict s).withDensity f :=
  restrict_withDensity_comm f hf s hs


/-- Applique lintegral_withDensity_eq_lintegral_mul -/
lemma lintegral_sq_withDensity (f : ℝ → ℂ) (hf : Measurable f) :
    ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (‖f x‖^2) ∂haarMul =
    ∫⁻ x in Set.Ioi (0:ℝ),
      ENNReal.ofReal (1/x) * ENNReal.ofReal (‖f x‖^2) ∂volume := by
  unfold haarMul
  rw [restrict_withDensity_comm _ (by measurability) _ measurableSet_Ioi]
  have hg : AEMeasurable (fun x : ℝ => ENNReal.ofReal (1/x))
              (volume.restrict (Set.Ioi (0:ℝ))) :=
    (Measurable.ennreal_ofReal
      (measurable_const.div measurable_id)).aemeasurable
  have hh : AEMeasurable (fun x : ℝ => ENNReal.ofReal (‖f x‖^2))
              (volume.restrict (Set.Ioi (0:ℝ))) :=
    (Measurable.ennreal_ofReal ((hf.norm).pow_const 2)).aemeasurable
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hg hh]
  rfl


/-- Reconvertit le lintegral en intégrale Bochner -/
lemma lintegral_sq_volume_eq_integral (f : ℝ → ℂ) (hf : Measurable f) :
    (∫⁻ x in Set.Ioi (0:ℝ),
      ENNReal.ofReal (1/x) * ENNReal.ofReal (‖f x‖^2) ∂volume).toReal =
    ∫ x in Set.Ioi (0:ℝ), (1/x) * ‖f x‖^2 ∂volume := by
  -- Étape 1 : fusionner les deux ofReal en un seul, sur Ioi 0
  have hfuse : Set.EqOn
      (fun x => ENNReal.ofReal (1/x) * ENNReal.ofReal (‖f x‖^2))
      (fun x => ENNReal.ofReal ((1/x) * ‖f x‖^2))
      (Set.Ioi (0:ℝ)) := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    change ENNReal.ofReal (1/x) * ENNReal.ofReal (‖f x‖^2)
       = ENNReal.ofReal ((1/x) * ‖f x‖^2)
    rw [← ENNReal.ofReal_mul (by positivity)]
  -- Étape 2 : appliquer la congruence
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi hfuse]
  -- Étape 3 : convertir lintegral en integral
  rw [← MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · -- ae nonneg, restreint à Ioi 0
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ ?_)
    intro x hx
    simp only [Set.mem_Ioi] at hx
    positivity
  · -- AEStronglyMeasurable de (1/x) * ‖f x‖²
    apply Measurable.aestronglyMeasurable
    exact (measurable_const.div measurable_id).mul
            (hf.norm.pow_const 2)


/-- Étape intermédiaire : déplier `haarMul` sur `Ioi 0`. -/
lemma integral_sq_haarMul (f : ℝ → ℂ) (hf : Measurable f) :
    ∫ x in Set.Ioi (0:ℝ), ‖f x‖^2 ∂haarMul =
    ∫ x in Set.Ioi (0:ℝ), (1/x) * ‖f x‖^2 ∂volume := by
  have hfae : AEStronglyMeasurable (fun x => ‖f x‖^2)
      (haarMul.restrict (Set.Ioi 0)) :=
    (hf.norm.pow_const 2).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  rw [integral_sq_haarMul_eq_lintegral f hfae]
  rw [lintegral_sq_withDensity f hf]
  exact lintegral_sq_volume_eq_integral f hf


/-- Changement de variable `x = eᵗ`. -/
lemma integral_exp_change_of_var (g : ℝ → ℝ)
  (_ : Measurable g) :
    ∫ t : ℝ, g (Real.exp t) ∂volume =
    ∫ x in Set.Ioi (0:ℝ), (1/x) * g x ∂volume := by
  have h_image : Real.exp '' Set.univ = Set.Ioi (0:ℝ) := by
    ext x
    constructor
    · rintro ⟨t, _, rfl⟩
      exact Real.exp_pos t
    · intro hx
      exact ⟨Real.log x, Set.mem_univ _, Real.exp_log hx⟩
  have h_deriv : ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt Real.exp (Real.exp x) Set.univ x := by
    intro x _
    exact (Real.hasDerivAt_exp x).hasDerivWithinAt
  have h_inj : Set.InjOn Real.exp Set.univ := by
    intro a _ b _ hab
    exact Real.exp_injective hab
  have h_chg := integral_image_eq_integral_abs_deriv_smul
      (s := (Set.univ : Set ℝ)) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ h_deriv h_inj (fun x => (1/x) * g x)
  rw [h_image] at h_chg
  rw [h_chg, setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with t
  rw [smul_eq_mul, abs_of_pos (Real.exp_pos t)]
  rw [← mul_assoc, mul_one_div, div_self (Real.exp_pos t).ne', one_mul]

lemma integral_Ioi_eq_integral_exp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ x in Set.Ioi (0:ℝ), g x = ∫ t : ℝ, Real.exp t • g (Real.exp t) := by
  have himg : Real.exp '' Set.univ = Set.Ioi (0:ℝ) := by
    rw [Set.image_univ]; exact Real.range_exp
  rw [← himg]
  rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Real.exp_injective.injOn) g]
  rw [MeasureTheory.setIntegral_univ]  -- ← nom corrigé
  congr 1
  funext t
  rw [abs_of_pos (Real.exp_pos t)]
