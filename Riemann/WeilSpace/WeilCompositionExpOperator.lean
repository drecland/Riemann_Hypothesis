import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.Tools.Integration

open Real Complex SchwartzMap
open MeasureTheory
open scoped MeasureTheory

/-- Opérateur de composition avec l'exponentielle :
    J(f)(t) = f(eᵗ). -/
noncomputable def weilJ (f : ℝ → ℂ) : ℝ → ℂ := fun t => f (Real.exp t)

lemma weilJ_measurable {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (weilJ f) := by
  unfold weilJ
  exact hf.comp Real.measurable_exp


/-- Résultat principal. -/
lemma weilJ_integral_sq_eq (f : ℝ → ℂ) (hf : Measurable f) :
    ∫ t : ℝ, ‖f (Real.exp t)‖^2 ∂volume =
    ∫ x in Set.Ioi (0:ℝ), ‖f x‖^2 ∂haarMul := by
  rw [integral_sq_haarMul f hf]
  exact integral_exp_change_of_var (fun x => ‖f x‖^2) (by exact hf.norm.pow_const 2)
