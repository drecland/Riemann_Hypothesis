import Riemann.Basic

open MeasureTheory Measure Real
open scoped ENNReal

/-- **Mesure de Haar multiplicative** `d×x = dx/x` sur `ℝ*₊`.

    On la définit sur tout `ℝ` comme `volume.withDensity (fun x ↦ ‖x‖₊⁻¹)`
    (la densité `1/|x|` étend naturellement `1/x` sur `ℝ*₊`, mais seule
    la restriction à `(0, +∞)` nous intéressera). -/
noncomputable def haarMul : Measure ℝ :=
volume.withDensity (fun x => ENNReal.ofReal (1 / x))


/--
## Égalité de densité pour la mesure de Haar multiplicative

    Ce lemme établit l'égalité formelle entre les deux écritures
    de la densité
    `1/x` utilisée dans la définition de la mesure de Haar
    multiplicative `haarMul` :

    ```
    ENNReal.ofReal (1 / x) = ENNReal.ofReal x⁻¹
    ```

    ### Pourquoi ce lemme est utile

    Dans la définition de `haarMul`,
    on utilise la notation `1 / x` pour la densité.
    Cependant, Lean/Mathlib préfère souvent travailler avec la
    notation `x⁻¹`
    (inverse multiplicatif) dans les lemmes de réécriture
    et de simplification.
    Ce lemme sert donc de **pont de normalisation**
    entre les deux notations.
-/
lemma haarMul_density_pos {x : ℝ} :
    ENNReal.ofReal (1 / x) = ENNReal.ofReal x⁻¹ := by
  rw [one_div]

/- ## `Set.Ioi` — Intervalle ouvert vers l'infini

    `Set.Ioi a` désigne l'intervalle ouvert `(a, +∞)` dans un ordre,
    c'est-à-dire l'ensemble des éléments strictement supérieurs à `a` :

    ```
    Set.Ioi a = { x | a < x }
    ```

    ### Exemples typiques dans ce fichier

    - `Set.Ioi (0 : ℝ)` représente `ℝ*₊ = (0, +∞)`, le domaine naturel
      de la mesure de Haar multiplicative `haarMul`.

    ### Notation

    Le nom `Ioi` est l'abréviation de **I**nterval **o**pen **i**nfinity
    (intervalle ouvert vers l'infini). -/


/-- Sur `Ioi 0`, `(ENNReal.ofReal (1/x)).toReal = 1/x` -/
lemma haarMul_density_simp {x : ℝ} (hx : 0 < x) :
    (ENNReal.ofReal (1/x)).toReal = 1/x := by
  rw [ENNReal.toReal_ofReal (by positivity)]


/-- On peut remplacer la densité par sa valeur réelle dans
l'intégrale gauche -/
lemma haarMul_integral_left_simp {a : ℝ}
    (f : ℝ → ℝ) :
    ∫ x in Set.Ioi (0:ℝ), (ENNReal.ofReal (1/x)).toReal •
    f (a * x) ∂volume =
    ∫ x in Set.Ioi (0:ℝ), (1/x) * f (a * x) ∂volume := by
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only []
  simp only [Set.mem_Ioi] at hx
  rw [haarMul_density_simp hx, smul_eq_mul]

/-- On peut remplacer la densité par sa valeur réelle dans
l'intégrale droite -/
lemma haarMul_integral_right_simp {_ : ℝ}
    (f : ℝ → ℝ) :
    ∫ x in Set.Ioi (0:ℝ), (ENNReal.ofReal (1/x)).toReal • f x ∂volume =
    ∫ x in Set.Ioi (0:ℝ), (1/x) * f x ∂volume := by
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only []
  simp only [Set.mem_Ioi] at hx
  rw [haarMul_density_simp hx, smul_eq_mul]


/-- Réécriture algébrique : sur Ioi 0,
(1/x) * f(a*x) = a * ((1/(a*x)) * f(a*x)) -/
lemma haarMul_integrand_rw {a : ℝ} (ha : 0 < a)
    (f : ℝ → ℝ) :
    ∀ x ∈ Set.Ioi (0:ℝ),
    (1/x) * f (a*x) = a * ((1/(a*x)) * f (a*x)) := by
  intro x hx
  simp only [Set.mem_Ioi] at hx
  have hx' : x ≠ 0 := ne_of_gt hx
  have ha' : a ≠ 0 := ha.ne'
  field_simp

/-- La fonction x ↦ (1/(a*x)) * f(a*x) est
la composition de y ↦ (1/y)*f(y) avec x ↦ a*x -/
lemma haarMul_integrand_comp {a : ℝ} (f : ℝ → ℝ) :
    (fun x => (1/(a*x)) * f (a*x)) = (fun y => (1/y) * f y) ∘
    (fun x => a*x) := by
  rfl

/-- On sort la constante `a` devant l'intégrale -/
lemma haarMul_integral_factor {a : ℝ}
    (f : ℝ → ℝ) :
    ∫ x in Set.Ioi (0:ℝ), a * ((1/(a*x)) * f (a*x)) ∂volume =
    a * ∫ x in Set.Ioi (0:ℝ), (1/(a*x)) * f (a*x) ∂volume := by
  rw [MeasureTheory.integral_const_mul]

/-- Réécriture de l'intégrale sur Ioi 0 en intégrale totale
via indicatrice -/
lemma haarMul_integral_indicator_rw (g : ℝ → ℝ) :
    ∫ x in Set.Ioi (0:ℝ), g x ∂volume =
    ∫ x : ℝ, Set.indicator (Set.Ioi 0) g x ∂volume := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]


/-- Après passage aux indicatrices, applique integral_comp_mul_left -/
lemma haarMul_integral_comp_mul {a : ℝ}
    (g : ℝ → ℝ) :
    ∫ x : ℝ, Set.indicator (Set.Ioi 0) g (a * x) ∂volume =
    |a⁻¹| • ∫ x : ℝ, Set.indicator (Set.Ioi 0) g x ∂volume := by
  rw [integral_comp_mul_left]

/-- L'indicatrice de Ioi 0 est stable par x ↦ a*x quand a > 0 -/
lemma haarMul_indicator_comp {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) (x : ℝ) :
    Set.indicator (Set.Ioi 0) g (a * x) =
    Set.indicator (Set.Ioi 0) (g ∘ (· * a)) x := by
  simp [Set.indicator, Set.mem_Ioi, mul_comm a x,
        mul_pos_iff_of_pos_right ha]



/-- Changement de variable `y = a*x` :
    ∫ (1/x) * f(a*x) dx = ∫ (1/x) * f(x) dx sur Ioi 0 -/
lemma haarMul_integral_change_of_var {a : ℝ} (ha : 0 < a)
    (f : ℝ → ℝ) (_ : Measurable f) :
    ∫ x in Set.Ioi (0:ℝ), (1/x) * f (a * x) ∂volume =
    ∫ x in Set.Ioi (0:ℝ), (1/x) * f x ∂volume := by
  have ha_ne : a ≠ 0 := ha.ne'
  -- Étape 1 : réécrire (1/x) * f(a*x) = a * ((1/(a*x)) * f(a*x))
  have h1 : ∫ x in Set.Ioi (0:ℝ), (1/x) * f (a * x) ∂volume
          = ∫ x in Set.Ioi (0:ℝ), a * ((1/(a*x)) * f (a*x)) ∂volume := by
    apply setIntegral_congr_fun measurableSet_Ioi
    exact haarMul_integrand_rw ha f
  rw [h1]
  -- Étape 2 : sortir la constante a
  rw [integral_const_mul]
  -- Étape 3 : changement de variable y = a*x via integral_comp_mul_left_Ioi
  have h2 : ∫ x in Set.Ioi (0:ℝ), (1/(a*x)) * f (a*x) ∂volume
          = a⁻¹ • ∫ y in Set.Ioi (0:ℝ), (1/y) * f y ∂volume := by
    have := integral_comp_mul_left_Ioi (fun y => (1/y) * f y) 0 ha
    simp only [mul_zero] at this
    exact this
  rw [h2]
  -- Étape 4 : a * (a⁻¹ • I) = I
  rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha_ne, one_mul]


/-- **Invariance par dilatation** (version intégrale). -/
theorem haarMul_integral_invariant {a : ℝ} (ha : 0 < a)
    (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ x in Set.Ioi (0 : ℝ), f (a * x) ∂haarMul =
    ∫ x in Set.Ioi (0 : ℝ), f x ∂haarMul := by
  have hdens : Measurable (fun x : ℝ => ENNReal.ofReal (1 / x)) :=
    (measurable_const.div measurable_id).ennreal_ofReal
  have hdens_top : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ENNReal.ofReal (1 / x) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  simp only [haarMul]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul'
        (s := Set.Ioi 0) hdens hdens_top,
      setIntegral_withDensity_eq_setIntegral_toReal_smul'
        (s := Set.Ioi 0) hdens hdens_top]
  rw [haarMul_integral_left_simp f]
  rw [haarMul_integral_change_of_var ha f hf]
  rw [haarMul_integral_right_simp f]
  exact a


/-
/-- La mesure de Haar multiplicative est invariante par y ↦ c * y, pour c > 0. -/
lemma haarMul_smul_eq (c : ℝ) (hc : 0 < c) :
    Measure.map (fun y => c * y) haarMul = haarMul := by
  unfold haarMul
  -- Utilise le fait que map f (withDensity μ g) = withDensity (map f μ) (g ∘ f⁻¹)
  rw [← Measure.withDensity_map_equiv]
  · congr 1
    · -- map (c * ·) volume = c⁻¹ • volume (formule standard)
      rw [Real.map_volume_mul_left hc]
      ext s hs
      simp [Measure.smul_apply, ENNReal.ofReal_inv_of_pos hc]
    · ext x
      simp [one_div, mul_comm c]

lemma haarMul_inv_eq :
    Measure.map (fun y : ℝ => y⁻¹) haarMul = haarMul := by
  unfold haarMul
  rw [← Measure.withDensity_map_equiv]
  · congr 1
    · -- map inv volume : utilise la mesure image par inversion
      rw [Real.map_volume_inv]
      ext s hs
      simp [Measure.smul_apply]
    · ext x
      simp [one_div, inv_inv]
-/
/-
/-- La mesure de Haar sur ℝ*₊ est invariante par y ↦ c/y pour c > 0. -/
lemma haarMul_inv_smul_eq (c : ℝ) (hc : 0 < c) :
    Measure.map (fun y => c / y) haarMul = haarMul := by
  -- y ↦ c/y = (fun z => c * z) ∘ (fun y => y⁻¹)
  have hcomp : (fun y : ℝ => c / y) = (fun z => c * z) ∘ (fun y => y⁻¹) := by
    ext y; simp [div_eq_mul_inv]
  rw [hcomp, ← Measure.map_map]
  · rw [haarMul_inv_eq, haarMul_smul_eq c hc]
  · exact measurable_const.mul measurable_id
  · exact measurable_inv
-/


/- Nécessite haarMul_inv_smul_eq
/-- Changement de variable y ↦ 1/y dans une intégrale sur haarMul.
    L'invariance de haarMul par y ↦ 1/y permet de substituer. -/
lemma haarMul_integral_inv_sub (g : ℝ → ℂ)
    (hg_meas : AEStronglyMeasurable g haarMul) :
    ∫ y in Set.Ioi (0:ℝ), g (1/y) ∂haarMul =
    ∫ y in Set.Ioi (0:ℝ), g y ∂haarMul := by
  have hinv := haarMul_inv_smul_eq 1 one_pos
  simp only [one_div] at hinv
  simp_rw [one_div]
  conv_rhs => rw [← hinv]
  rw [MeasureTheory.setIntegral_map
      measurableSet_Ioi
      (hg_meas.mono_measure (by rw [hinv]))
      measurable_inv.aemeasurable]
  have hpreimage : Inv.inv ⁻¹' Set.Ioi (0:ℝ) = Set.Ioi 0 := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioi]
    exact inv_pos
  rw [hpreimage]
-/


/- Nécessite haarMul_integral_inv_sub
/-- Après CV y ↦ 1/y :
    ∫ y, f(1/(xy)) * (1/↑y) * star(f(1/y)) ∂haarMul
  = ∫ y, f(y/x) * ↑y * star(f(y)) ∂haarMul -/
lemma hcv_lhs_inv (f : ℝ → ℂ) (hf : Measurable f) (x : ℝ) (_ : 0 < x) :
    ∫ y in Set.Ioi (0:ℝ),
        f (1/x/y) * (1/(↑y : ℂ)) * star (f (1/y)) ∂haarMul
    = ∫ y in Set.Ioi (0:ℝ),
        f (y/x) * (↑y : ℂ) * star (f y) ∂haarMul := by
  rw [← haarMul_integral_inv_sub
      (fun y => f (y/x) * (↑y : ℂ) * star (f y))
      (by
        apply AEStronglyMeasurable.mul
        · apply AEStronglyMeasurable.mul
          · exact (hf.comp (measurable_id.div_const x)).aestronglyMeasurable
          · exact Complex.measurable_ofReal.aestronglyMeasurable
        · exact (Complex.continuous_conj.measurable.comp hf).aestronglyMeasurable)]
  congr 1; ext y
  simp only [one_div]
  push_cast
  field_simp
-/

/- Nécessite haarMul_integral_inv_sub
/-- Après CV y ↦ 1/y :
    ∫ y, star(f(x/y)) * (1/↑y) * f(1/y) ∂haarMul
  = ∫ y, star(f(xy)) * ↑y * f(y) ∂haarMul -/
lemma hcv_rhs_inv (f : ℝ → ℂ) (hf : Measurable f) (x : ℝ) (_ : 0 < x) :
    ∫ y in Set.Ioi (0:ℝ),
        star (f (x/y)) * (1/(↑y:ℂ)) * f (1/y) ∂haarMul
    = ∫ y in Set.Ioi (0:ℝ),
        star (f (x*y)) * (↑y:ℂ) * f y ∂haarMul := by
  rw [← haarMul_integral_inv_sub
      (fun y => star (f (x*y)) * (↑y:ℂ) * f y)
      (by
        apply AEStronglyMeasurable.mul
        · apply AEStronglyMeasurable.mul
          · exact (Complex.continuous_conj.measurable.comp
                    (hf.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
          · exact Complex.measurable_ofReal.aestronglyMeasurable
        · exact hf.aestronglyMeasurable)]
  congr 1; ext y
  simp only [one_div]
  push_cast
  field_simp
-/

/-
/-- Après CV y ↦ xy :
    ∫ y, f(y/x) * ↑y * star(f(y)) ∂haarMul
  = ∫ y, f(y) * ↑(xy) * star(f(xy)) ∂haarMul -/
lemma hcv_lhs_mul (f : ℝ → ℂ) (hf : Measurable f) (x : ℝ) (hx : 0 < x) :
    ∫ y in Set.Ioi (0:ℝ),
      f (y/x) * (↑y : ℂ) * star (f y) ∂haarMul
    = ∫ y in Set.Ioi (0:ℝ),
      f y * (↑(x*y) : ℂ) * star (f (x*y)) ∂haarMul := by
  -- haarMul_integral_invariant : ∫ f(ay) ∂haarMul = ∫ f(y) ∂haarMul
  -- On l'applique à g := y ↦ f(y) * ↑(xy) * star(f(xy))
  -- ce qui donne ∫ g(x*y) = ∫ g(y), i.e.
  -- ∫ f(xy) * ↑(x*xy) * star(f(x*xy)) = ∫ f(y) * ↑(xy) * star(f(xy))
  -- Mais on veut le sens inverse : LHS → RHS
  -- Donc on réécrit LHS = ∫ g(y) via g(y) = f(y/x) * ↑y * star(f(y))
  -- et RHS = ∫ g(xy)
  -- haarMul_integral_invariant hx g donne ∫ g(xy) = ∫ g(y)
  -- Donc RHS = LHS
  symm
  have := haarMul_integral_invariant hx
    (fun y => (f (y/x) * (↑y : ℂ) * star (f y)).re)
  -- On doit adapter pour ℂ : utiliser re + im séparément
  -- ou une version complexe de haarMul_integral_invariant
  -- Stratégie : montrer que les deux membres sont égaux
  -- en utilisant la version réelle sur re et im
  sorry
-/
