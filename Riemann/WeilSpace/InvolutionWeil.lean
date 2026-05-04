import Riemann.Basic
import Riemann.Tools.HaarMeasure
import Riemann.WeilSpace.WeilSpace
import Riemann.Tools.Convolution

/-- **Involution de Weil** : `g*(x) = (1/x) · conj(g(1/x))`.

Pour `x > 0`, cette involution joue le rôle d'un « adjoint »
pour la convolution multiplicative. -/
noncomputable def weilStarInvolution (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (1 / (x : ℂ)) * star (g (1 / x))

@[inherit_doc]
notation g "⋆ₛ" => weilStarInvolution g

lemma weilStarW_smooth (f : 𝒲) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => star ((f : ℝ → ℂ) (-t))) := by
  -- star est lisse sur ℂ (anti-linéaire continue = lisse)
  have h_star : ContDiff ℝ (⊤ : ℕ∞) (star : ℂ → ℂ) :=
    Complex.conjCLE.contDiff
  -- f est lisse
  have h_f : ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℂ) := f.smooth _
  -- t ↦ -t est lisse
  have h_neg : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => -t) :=
    contDiff_neg
  exact h_star.comp (h_f.comp h_neg)


lemma weilStarW_decay (f : 𝒲) (k n : ℕ) :
    ∃ C, ∀ t : ℝ,
      ‖t‖^k * ‖iteratedFDeriv ℝ n
        (fun t : ℝ => star ((f : ℝ → ℂ) (-t))) t‖ ≤ C := by
  obtain ⟨C, hC⟩ := f.decay' k n
  refine ⟨C, fun t => ?_⟩
  have hCt := hC (-t)
  rw [norm_neg] at hCt
  rw [norm_iteratedFDeriv_star_comp_neg (f : ℝ → ℂ) (f.smooth _) n t]
  exact hCt


noncomputable def weilStarW (f : 𝒲) : 𝒲 :=
  { toFun := fun t => star ((f : ℝ → ℂ) (-t))
    smooth' := weilStarW_smooth f
    decay' := fun k n => weilStarW_decay f k n }


-- Lemmes pour montrer que WeilArith est reel
-- Dans **WeilHermitianForm.lean**

/-- `ℳ[f ⋆ₘ f⋆](1)` est réel. -/
lemma mellin_conv_self_star_at_one_isReal (f : ℝ → ℂ) :
    (mellinTransform (f ⋆ₘ (weilStarInvolution f)) 1).im = 0 := by
  -- Stratégie : montrer que mellinTransform Φ 1 = star (mellinTransform Φ 1)
  rw [← Complex.conj_eq_iff_im]
  -- But : star (ℳ[Φ](1)) = ℳ[Φ](1)
  unfold mellinTransform
  -- ℳ[Φ](1) = ∫ x in Ioi 0, (x:ℂ)^((1:ℂ)-1) • Φ x
  --        = ∫ x in Ioi 0, Φ x  (car x^0 = 1)
  sorry


/-- `ℳ[f ⋆ₘ f⋆](0)` est réel. -/
lemma mellin_conv_self_star_at_zero_isReal (f : ℝ → ℂ) :
    (mellinTransform (f ⋆ₘ (weilStarInvolution f)) 0).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  unfold mellinTransform
  -- ℳ[Φ](0) = ∫ x in Ioi 0, (x:ℂ)^((0:ℂ)-1) • Φ x = ∫ Φ(x)/x dx
  sorry

-- Lemmes pour le critere de positivite de Weil
-- Dans **WeilPositivityCriterion.lean**

/-`ℳ[f*](s) = conj(ℳ[f](1 - conj s))`. -/
lemma mellin_weilStar (f : ℝ → ℂ) (s : ℂ) :
    mellinTransform (weilStarInvolution f) s
    = star (mellinTransform f (1 - star s)) := by
  sorry
