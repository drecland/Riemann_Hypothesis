import Riemann.Basic


/-- **Opérateur `D` de Weil** : `D(f)(x) = x · f'(x)`. -/
noncomputable def weilOp (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => x * deriv f x
