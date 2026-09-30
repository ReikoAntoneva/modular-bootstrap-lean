import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import GapFamily.Analytic.Foundation.SignedFubini
import GapFamily.Analytic.Foundation.SignedIntegralContinuousLinearMap

/-!
# Representatives of Bochner integrals in L²

Ordinary product integrability justifies identification by Hilbert pairings.
A uniform L² majorant supplies this integrability for finite input measures.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Filter Function

variable {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]

/-- A Hilbert-valued integral agrees with an ordinary pointwise integral
whenever its scalar test pairings satisfy ordinary Fubini. -/
theorem l2_integral_eq_of_pairing_integrable
    {F : ℝ → Lp ℂ 2 μ} {f : ℝ → ℝ → ℂ} {g : Lp ℂ 2 μ}
    (hF : Integrable F ν)
    (hrep : ∀ᵐ t ∂ν, (F t : ℝ → ℂ) =ᵐ[μ] f t)
    (hg : (g : ℝ → ℂ) =ᵐ[μ] fun x => ∫ t, f t x ∂ν)
    (hfi : ∀ᵐ x ∂μ, Integrable (fun t => f t x) ν)
    (hpair : ∀ u : Lp ℂ 2 μ,
      Integrable (fun p : ℝ × ℝ => inner ℂ (u p.2) (f p.1 p.2)) (ν.prod μ)) :
    (∫ t, F t ∂ν) = g := by
  apply ext_inner_left ℂ
  intro u
  calc
    inner ℂ u (∫ t, F t ∂ν) = ∫ t, inner ℂ u (F t) ∂ν :=
      (integral_inner hF u).symm
    _ = ∫ t, ∫ x, inner ℂ (u x) (f t x) ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [hrep] with t ht
      rw [L2.inner_def]
      exact integral_congr_ae (ht.mono fun x hx => by dsimp only; rw [hx])
    _ = ∫ x, ∫ t, inner ℂ (u x) (f t x) ∂ν ∂μ :=
      integral_integral_swap (hpair u)
    _ = inner ℂ u g := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg, hfi] with x hx hix
      rw [integral_inner hix, hx]

omit [SFinite ν] in
/-- A uniform square-integrable majorant gives integrable Hilbert test
pairings against a finite input measure. -/
theorem l2_pairing_integrable_of_dominated [IsFiniteMeasure ν]
    {f : ℝ → ℝ → ℂ} {h : ℝ → ℝ}
    (hf : AEStronglyMeasurable (uncurry f) (ν.prod μ))
    (hh : MemLp h 2 μ)
    (hb : ∀ᵐ p ∂ν.prod μ, ‖f p.1 p.2‖ ≤ h p.2)
    (u : Lp ℂ 2 μ) :
    Integrable (fun p : ℝ × ℝ => inner ℂ (u p.2) (f p.1 p.2)) (ν.prod μ) := by
  have hi : Integrable (fun x => ‖u x‖ * h x) μ := (Lp.memLp u).norm.integrable_mul hh
  have hip : Integrable (fun p : ℝ × ℝ => ‖u p.2‖ * h p.2) (ν.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := ν)).mul_prod hi
  apply hip.mono' ((Lp.aestronglyMeasurable u).comp_snd.inner hf)
  filter_upwards [hb] with p hp
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left hp (norm_nonneg _))

/-- The signed Hilbert integral has its literal signed pointwise representative
when scalar pairings are absolutely integrable against the variation. -/
theorem l2_signedIntegral_eq_of_pairing_integrable
    {σ : SignedMeasure ℝ} {F : ℝ → Lp ℂ 2 μ} {f : ℝ → ℝ → ℂ} {g : Lp ℂ 2 μ}
    (hF : σ.Integrable F)
    (hrep : ∀ᵐ t ∂σ.variation, (F t : ℝ → ℂ) =ᵐ[μ] f t)
    (hg : (g : ℝ → ℂ) =ᵐ[μ] fun x => ∫ᵛ t, f t x ∂<•σ)
    (hfi : ∀ᵐ x ∂μ, σ.Integrable (fun t => f t x))
    (hpair : ∀ u : Lp ℂ 2 μ,
      Integrable (fun p : ℝ × ℝ => inner ℂ (u p.2) (f p.1 p.2))
        (σ.variation.prod μ)) :
    (∫ᵛ t, F t ∂<•σ) = g := by
  apply ext_inner_left ℂ
  intro u
  calc
    inner ℂ u (∫ᵛ t, F t ∂<•σ) = ∫ᵛ t, inner ℂ u (F t) ∂<•σ :=
      complexContinuousLinearMap_signedIntegral (innerSL ℂ u) hF
    _ = ∫ᵛ t, (∫ x, inner ℂ (u x) (f t x) ∂μ) ∂<•σ := by
      apply VectorMeasure.integral_congr_ae
      filter_upwards [hrep] with t ht
      rw [L2.inner_def]
      exact integral_congr_ae (ht.mono fun x hx => by dsimp only; rw [hx])
    _ = ∫ x, (∫ᵛ t, inner ℂ (u x) (f t x) ∂<•σ) ∂μ :=
      signedIntegral_integral_swap (hpair u)
    _ = inner ℂ u g := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg, hfi] with x hx hix
      exact (complexContinuousLinearMap_signedIntegral (innerSL ℂ (u x)) hix).symm.trans
        (congrArg (inner ℂ (u x)) hx.symm)

/-- A finite signed superposition commutes with taking L² representatives
under a genuine square-integrable majorant. -/
theorem l2_signedIntegral_eq_of_dominated
    {σ : SignedMeasure ℝ} {F : ℝ → Lp ℂ 2 μ} {f : ℝ → ℝ → ℂ} {g : Lp ℂ 2 μ}
    {h : ℝ → ℝ}
    (hF : σ.Integrable F)
    (hrep : ∀ᵐ t ∂σ.variation, (F t : ℝ → ℂ) =ᵐ[μ] f t)
    (hg : (g : ℝ → ℂ) =ᵐ[μ] fun x => ∫ᵛ t, f t x ∂<•σ)
    (hfi : ∀ᵐ x ∂μ, σ.Integrable (fun t => f t x))
    (hf : AEStronglyMeasurable (uncurry f) (σ.variation.prod μ))
    (hh : MemLp h 2 μ)
    (hb : ∀ᵐ p ∂σ.variation.prod μ, ‖f p.1 p.2‖ ≤ h p.2) :
    (∫ᵛ t, F t ∂<•σ) = g := by
  let := signedMeasure_isFiniteMeasure_variation σ
  exact l2_signedIntegral_eq_of_pairing_integrable hF hrep hg hfi
    (l2_pairing_integrable_of_dominated hf hh hb)

end GapFamily.Analytic
