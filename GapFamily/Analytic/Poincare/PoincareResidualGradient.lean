import GapFamily.Analytic.Poincare.PoincareNonidentityGradientBound
import GapFamily.Analytic.Poincare.PoincareDirectRemnantGradient
import GapFamily.Analytic.Poincare.Seed.PoincareSeriesC1
import GapFamily.Analytic.Modular.ModularGradientCore
import GapFamily.Analytic.Modular.ModularBoundary

/-! Actual L² frame derivatives of the cutoff-subtracted convergent Poincare series. -/
noncomputable section
namespace GapFamily.Analytic.PoincareComplementGradient
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
  PoincareSeriesDifferentiable PoincareSeriesC1
  PoincareSeedGradient PoincareGreen PoincareNonidentityGradientBound
open scoped Topology ContDiff

/-- The actual Poincare series with its cutoff direct seed removed. -/
def residual (J : ℤ) (s : ℂ) (z : ℂ) : ℂ :=
  complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z) - rawSeed J s z + directRemnant J s z

theorem residual_eq_cutoff_subtraction (J : ℤ) (s : ℂ) (z : ℂ) :
    residual J s z = complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z) -
      (CuspFourierCutoff.cutoff z.im : ℂ) * rawSeed J s z := by
  simp only [residual, directRemnant, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- The identity quotient term has the actual seed derivative on the open upper plane. -/
theorem fderiv_term_identity (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    fderiv ℝ (PoincareTermGradient.term J s identityCuspCoset) (τ : ℂ) =
      fderiv ℝ (rawSeed J s) (τ : ℂ) := by
  have h : PoincareTermGradient.term J s identityCuspCoset =ᶠ[𝓝 (τ : ℂ)] rawSeed J s := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    calc
      PoincareTermGradient.term J s identityCuspCoset z =
          complexPoincareTerm 0 J s (⟨z, hz⟩ : UpperHalfPlane) identityCuspCoset :=
        PoincareTermGradient.term_apply J s identityCuspCoset ⟨z, hz⟩
      _ = complexPointSeed 0 J s (⟨z, hz⟩ : UpperHalfPlane) := complexPoincareTerm_identity 0 J s _
      _ = rawSeed J s z := (rawSeed_eq_complexPointSeed J s ⟨z, hz⟩).symm
  exact h.fderiv_eq

/-- Splitting the already norm-convergent actual derivative series isolates the direct seed. -/
theorem fderiv_series_direct_split (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (τ : UpperHalfPlane) :
    fderiv ℝ (fun z : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z)) (τ : ℂ) =
      fderiv ℝ (rawSeed J s) (τ : ℂ) +
        ∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
          fderiv ℝ (PoincareTermGradient.term J s q.val) (τ : ℂ) := by
  classical
  rw [fderiv_complexPoincareSeries J hs τ]
  have h := (summable_norm_fderiv_term J hs τ).of_norm.sum_add_tsum_compl
    (s := {identityCuspCoset})
  simp only [Finset.sum_singleton, fderiv_term_identity J s τ] at h
  let e : {q : CuspCoset // q ≠ identityCuspCoset} ≃
      ↑((↑({identityCuspCoset} : Finset CuspCoset) : Set CuspCoset)ᶜ) :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  calc
    _ = fderiv ℝ (rawSeed J s) (τ : ℂ) +
      ∑' q : ↑((↑({identityCuspCoset} : Finset CuspCoset) : Set CuspCoset)ᶜ),
        fderiv ℝ (PoincareTermGradient.term J s q.val) (τ : ℂ) := h.symm
    _ = _ := congrArg (fderiv ℝ (rawSeed J s) (τ : ℂ) + ·)
      (e.tsum_eq (fun q => fderiv ℝ (PoincareTermGradient.term J s q.val) (τ : ℂ))).symm

/-- Genuine C¹ regularity on the whole open upper half-plane. -/
theorem contDiffOn_residual (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    ContDiffOn ℝ 1 (residual J s) upperHalfPlaneSet :=
  ((contDiffOn_complexPoincareSeries J hs).sub
    ((contDiffOn_rawSeed J s).of_le (by simp))).add
      ((contDiffOn_directRemnant J s).of_le (by simp))

/-- The actual residual derivative is the direct-remnant derivative plus the
norm-summable series of actual nonidentity derivatives. -/
theorem fderiv_residual (J : ℤ) {s : ℂ} (hs : 1 < s.re) (τ : UpperHalfPlane) :
    fderiv ℝ (residual J s) (τ : ℂ) = fderiv ℝ (directRemnant J s) (τ : ℂ) +
      ∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
        fderiv ℝ (PoincareTermGradient.term J s q.val) (τ : ℂ) := by
  have hP := (hasFDerivAt_complexPoincareSeries J hs τ).differentiableAt
  have hR := differentiableAt_rawSeed J s τ
  have hD := differentiableAt_directRemnant J s τ
  change fderiv ℝ
    (((fun z : ℂ => complexPoincareSeries 0 J s (UpperHalfPlane.ofComplex z)) - rawSeed J s) +
      directRemnant J s) (τ : ℂ) = _
  rw [fderiv_add (hP.sub hR) hD, fderiv_sub hP hR, fderiv_series_direct_split J hs τ]
  abel

/-- One finite bound controls the actual residual frame derivatives on the entire FD. -/
theorem exists_residual_frame_bound (J : ℤ) {s : ℂ} (hs : 2 < s.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : UpperHalfPlane), τ ∈ ModularGroup.fd → ∀ v : ℂ,
      τ.im * ‖fderiv ℝ (residual J s) (τ : ℂ) v‖ ≤ B * ‖v‖ := by
  obtain ⟨A, hA, hAb⟩ := exists_frame_bound_directRemnant J s
  obtain ⟨B, hB, hBb⟩ := exists_nonidentity_fderiv_tsum_frame_bound J hs
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro τ hτ v
  rw [fderiv_residual J (by linarith) τ, add_apply]
  calc
    _ ≤ τ.im * (‖fderiv ℝ (directRemnant J s) (τ : ℂ) v‖ +
        ‖(∑' q : {q : CuspCoset // q ≠ identityCuspCoset},
          fderiv ℝ (PoincareTermGradient.term J s q.val) (τ : ℂ)) v‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) τ.im_pos.le
    _ ≤ A * ‖v‖ + B * ‖v‖ := by
      rw [mul_add]
      exact add_le_add (hAb τ hτ v) (hBb τ hτ v)
    _ = (A + B) * ‖v‖ := by ring

/-- The auxiliary actual residual frame field is globally continuous on the upper plane. -/
theorem continuous_directional_residual (J : ℤ) {s : ℂ} (hs : 1 < s.re) (v : ℂ) :
    Continuous (directional (residual J s) v) := by
  have hD := (contDiffOn_residual J hs).continuousOn_fderiv_of_isOpen
    isOpen_upperHalfPlaneSet (by norm_num)
  have hd : Continuous (fun τ : UpperHalfPlane => fderiv ℝ (residual J s) (τ : ℂ) v) :=
    (hD.clm_apply continuousOn_const).comp_continuous UpperHalfPlane.continuous_coe
      (fun τ => τ.im_pos)
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul hd

/-- The actual residual frame derivative is square-integrable for every real direction. -/
theorem directional_residual_memLp (J : ℤ) {s : ℂ} (hs : 2 < s.re) (v : ℂ) :
    MemLp (directional (residual J s) v) 2 modularMeasure := by
  obtain ⟨B, hB, hb⟩ := exists_residual_frame_bound J hs
  apply MemLp.of_bound (continuous_directional_residual J (by linarith) v).aestronglyMeasurable
    (B * ‖v‖)
  filter_upwards [ae_mem_fdo] with τ hτ
  simpa only [directional, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos τ.im_pos] using hb τ (ModularGroup.fdo_subset_fd hτ) v

end GapFamily.Analytic.PoincareComplementGradient
