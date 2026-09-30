import GapFamily.Analytic.Elliptic.LocalSobolevCompactRestriction
import GapFamily.Analytic.Elliptic.LocalSobolevCompactCriterion
import GapFamily.Analytic.Foundation.CompactKernelIntegralMollifierOperator

/-!
# Local compactness for smooth energy-bounded families

Actual compactly supported functions are placed in the literal source and target
L² spaces. The final compactness proof uses genuine normalized mollification.
-/

noncomputable section

namespace GapFamily.Analytic.LocalSobolev

open Set MeasureTheory

/-- Actual source class for the restricted ambient Lebesgue measure. -/
def sourceLp (K : Set ℂ) (f : ℂ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Lp ℂ 2 (volume.restrict K) :=
  ((hf.memLp_of_hasCompactSupport hc : MemLp f 2 volume).mono_measure
    Measure.restrict_le_self).toLp f

theorem sourceLp_ae (K : Set ℂ) (f : ℂ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    sourceLp K f hf hc =ᵐ[volume.restrict K] f :=
  MemLp.coeFn_toLp _

theorem sourceLp_norm_sq (K : Set ℂ) (f : ℂ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    ‖sourceLp K f hf hc‖ ^ 2 = ∫ z in K, ‖f z‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceLp_ae K f hf hc] with z hz
  simp only [hz, real_inner_self_eq_norm_sq]

theorem sourceLp_norm_le (K : Set ℂ) (f : ℂ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) {R : ℝ} (hR : 0 ≤ R)
    (hbound : (∫ z : ℂ, ‖f z‖ ^ 2) ≤ R ^ 2) :
    ‖sourceLp K f hf hc‖ ≤ R := by
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  rw [sourceLp_norm_sq]
  refine (integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) ?_).trans hbound
  exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp
    (hf.memLp_of_hasCompactSupport hc)


/-- A smooth family with fixed compact support and bounded value and derivative
energies is relatively compact in L² on every compact target. -/
theorem totallyBounded_restrictedLp_of_uniform_energy {ι : Type*}
    (K T : Set ℂ) [CompactSpace K] [CompactSpace T]
    (f : ι → ℂ → ℂ) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hs : ∀ i, tsupport (f i) ⊆ K) {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hvalue : ∀ i, (∫ z : ℂ, ‖f i z‖ ^ 2) ≤ R ^ 2)
    (henergy : ∀ i, (∫ z : ℂ, ‖fderiv ℝ (f i) z‖ ^ 2) ≤ M ^ 2) :
    TotallyBounded (range (fun i => restrictedLp T (f i) (hf i).continuous)) := by
  have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  have hc (i : ι) : HasCompactSupport (f i) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hs i)
  apply GapFamily.Analytic.totallyBounded_of_totallyBounded_approx
  intro ε hε
  let δ : ℝ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  let ρ : ContDiffBump (0 : ℂ) :=
    ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let A : Lp ℂ 2 (volume.restrict K) →L[ℂ] Lp ℂ 2 (restrictedVolume T) :=
    normedMollifierIntegralL2Operator ρ K hK T (restrictedVolume T)
  have hA : IsCompactOperator A :=
    isCompactOperator_normedMollifierIntegralL2Operator _ _ _ _ _
  have hAeq (i : ι) :
      A (sourceLp K (f i) (hf i).continuous (hc i)) =
        restrictedLp T (mollify ρ (f i)) (continuous_mollify ρ (f i) (hf i).continuous) := by
    exact normedMollifierIntegralL2Operator_toLp ρ K hK T (f i) (hf i).continuous
      (((hf i).continuous.memLp_of_hasCompactSupport (hc i) : MemLp (f i) 2 volume).mono_measure
        Measure.restrict_le_self) ((subset_tsupport _).trans (hs i))
  let B : Set (Lp ℂ 2 (volume.restrict K)) := Metric.closedBall 0 R
  refine ⟨A '' B, ?_, ?_⟩
  · exact (hA.isCompact_closure_image_of_bounded Metric.isBounded_closedBall).totallyBounded.subset
      subset_closure
  · rintro u ⟨i, rfl⟩
    refine ⟨A (sourceLp K (f i) (hf i).continuous (hc i)), ?_, ?_⟩
    · refine ⟨sourceLp K (f i) (hf i).continuous (hc i), ?_, rfl⟩
      change dist (sourceLp K (f i) (hf i).continuous (hc i)) 0 ≤ R
      simpa only [dist_zero_right] using
        sourceLp_norm_le K (f i) (hf i).continuous (hc i) hR (hvalue i)
    · rw [hAeq, dist_eq_norm, norm_sub_rev]
      have hsq := (restrictedLp_mollify_error_sq_le T ρ (f i) (hf i) (hc i)).trans
        (mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg ρ.rOut))
      have hn :
          ‖restrictedLp T (mollify ρ (f i)) (continuous_mollify ρ (f i) (hf i).continuous) -
            restrictedLp T (f i) (hf i).continuous‖ ≤ δ * M := by
        apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ.le hM)).mp
        simpa only [ρ, mul_pow] using hsq
      refine hn.trans_lt ?_
      have hscale : δ * (M + 1) = ε := div_mul_cancel₀ ε (by linarith : M + 1 ≠ 0)
      nlinarith

end GapFamily.Analytic.LocalSobolev
