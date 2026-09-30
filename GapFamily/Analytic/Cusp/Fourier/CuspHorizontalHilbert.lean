import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalHilbertBasic
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalHilbertMean
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Bounded averaging on the actual cusp Hilbert space

The map is constructed from the literal horizontal integrals on the dense
smooth automorphic core. Jensen's inequality supplies the norm bound used in
the extension. Its complementary residual has the literal core representative.
-/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane
open scoped ENNReal ContDiff

theorem cuspHorizontalAverage_core_add (F G : ModularGradient.smoothCore)
    {y : ℝ} (hy : 0 < y) :
    cuspHorizontalAverage (F + G).val y =
      cuspHorizontalAverage F.val y + cuspHorizontalAverage G.val y := by
  change (∫ x in (-1/2 : ℝ)..(1/2),
    cuspHorizontalSlice F.val y x + cuspHorizontalSlice G.val y x) = _
  exact intervalIntegral.integral_add
    ((contDiff_cuspHorizontalSlice F.property.1 hy).continuous.intervalIntegrable _ _)
    ((contDiff_cuspHorizontalSlice G.property.1 hy).continuous.intervalIntegrable _ _)

theorem cuspHorizontalAverage_core_smul (c : ℂ) (F : ModularGradient.smoothCore) (y : ℝ) :
    cuspHorizontalAverage (c • F).val y = c • cuspHorizontalAverage F.val y := by
  change (∫ x in (-1/2 : ℝ)..(1/2), c • cuspHorizontalSlice F.val y x) = _
  rw [intervalIntegral.integral_smul]
  rfl

/-- Literal ordinary horizontal averaging on smooth core restrictions. -/
def cuspCoreAverage (H : ℝ) (hH : 1 ≤ H) :
    ModularGradient.smoothCore →ₗ[ℂ] cuspHilbert H where
  toFun F := (cuspHorizontalAverage_memLp F hH).toLp
    (fun τ : UpperHalfPlane => cuspHorizontalAverage F.val τ.im)
  map_add' F G := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall
      (fun τ => cuspHorizontalAverage_core_add F G τ.im_pos)
  map_smul' c F := by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall
      (fun τ => cuspHorizontalAverage_core_smul c F τ.im)

theorem cuspCoreAverage_ae (H : ℝ) (hH : 1 ≤ H) (F : ModularGradient.smoothCore) :
    cuspCoreAverage H hH F =ᵐ[modularMeasure.restrict {τ | H < τ.im}]
      (fun τ : UpperHalfPlane => cuspHorizontalAverage F.val τ.im) :=
  MemLp.coeFn_toLp (cuspHorizontalAverage_memLp F hH)

theorem cuspCoreAverage_norm_le (H : ℝ) (hH : 1 ≤ H) (F : ModularGradient.smoothCore) :
    ‖cuspCoreAverage H hH F‖ ≤ ‖cuspCoreValue H F‖ := by
  have hA : ‖cuspCoreAverage H hH F‖^2 =
      ∫ τ : UpperHalfPlane in {τ | H < τ.im},
        ‖cuspHorizontalAverage F.val τ.im‖^2 ∂modularMeasure :=
    cuspMean_toLp_norm_sq (fun τ : UpperHalfPlane => cuspHorizontalAverage F.val τ.im)
      (cuspHorizontalAverage_memLp F hH)
  have hV : ‖cuspCoreValue H F‖^2 =
      ∫ τ : UpperHalfPlane in {τ | H < τ.im}, ‖F.val τ‖^2 ∂modularMeasure := by
    rw [cuspMean_l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [cuspCoreValue_ae H F] with τ hτ
    rw [hτ]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hA, hV]
  exact (cuspHorizontalAverage_integrable_and_le F hH).2

/-- The actual bounded extension of ordinary horizontal averaging to cusp L². -/
def cuspAverage (H : ℝ) (hH : 1 ≤ H) : cuspHilbert H →L[ℂ] cuspHilbert H :=
  (cuspCoreAverage H hH).extendOfNorm (cuspCoreValue H)

theorem cuspAverage_core (H : ℝ) (hH : 1 ≤ H) (F : ModularGradient.smoothCore) :
    cuspAverage H hH (cuspCoreValue H F) = cuspCoreAverage H hH F :=
  LinearMap.extendOfNorm_eq (cuspCoreValue_dense_range H)
    ⟨1, fun G => by simpa using cuspCoreAverage_norm_le H hH G⟩ F

theorem cuspAverage_core_ae (H : ℝ) (hH : 1 ≤ H) (F : ModularGradient.smoothCore) :
    cuspAverage H hH (cuspCoreValue H F) =ᵐ[modularMeasure.restrict {τ | H < τ.im}]
      (fun τ : UpperHalfPlane => cuspHorizontalAverage F.val τ.im) := by
  rw [cuspAverage_core]
  exact cuspCoreAverage_ae H hH F

theorem cuspAverage_norm_le_one (H : ℝ) (hH : 1 ≤ H) : ‖cuspAverage H hH‖ ≤ 1 :=
  LinearMap.opNorm_extendOfNorm_le (cuspCoreValue_dense_range H) zero_le_one
    (fun F => by simpa using cuspCoreAverage_norm_le H hH F)

theorem cuspAverage_norm_le (H : ℝ) (hH : 1 ≤ H) (u : cuspHilbert H) :
    ‖cuspAverage H hH u‖ ≤ ‖u‖ := by
  have h := (cuspAverage H hH).le_opNorm u
  have hb := cuspAverage_norm_le_one H hH
  nlinarith [norm_nonneg u]

/-- The bounded nonconstant horizontal part on the actual cusp Hilbert space. -/
def cuspResidual (H : ℝ) (hH : 1 ≤ H) : cuspHilbert H →L[ℂ] cuspHilbert H :=
  ContinuousLinearMap.id ℂ (cuspHilbert H) - cuspAverage H hH

theorem cuspResidual_apply (H : ℝ) (hH : 1 ≤ H) (u : cuspHilbert H) :
    cuspResidual H hH u = u - cuspAverage H hH u := rfl

theorem cuspResidual_norm_le (H : ℝ) (hH : 1 ≤ H) (u : cuspHilbert H) :
    ‖cuspResidual H hH u‖ ≤ 2 * ‖u‖ := by
  rw [cuspResidual_apply]
  have h := norm_sub_le u (cuspAverage H hH u)
  have hb := cuspAverage_norm_le H hH u
  linarith

theorem cuspResidual_core_ae (H : ℝ) (hH : 1 ≤ H) (F : ModularGradient.smoothCore) :
    cuspResidual H hH (cuspCoreValue H F) =ᵐ[modularMeasure.restrict {τ | H < τ.im}]
      (fun τ : UpperHalfPlane => cuspHorizontalResidual F.val τ) := by
  rw [cuspResidual_apply, cuspAverage_core]
  filter_upwards [Lp.coeFn_sub (cuspCoreValue H F) (cuspCoreAverage H hH F),
    cuspCoreValue_ae H F, cuspCoreAverage_ae H hH F] with τ hsub hF hA
  simp only [hsub, Pi.sub_apply, hF, hA, cuspHorizontalResidual]
  rfl

/-- The bounded residual agrees with the already proved literal core tail estimate. -/
theorem cuspResidual_core_norm_sq (H : ℝ) (hH : 1 ≤ H) (F : ModularGradient.smoothCore) :
    ‖cuspResidual H hH (cuspCoreValue H F)‖^2 ≤
      (1 / H^2) * ‖ModularGradient.coreGradient F‖^2 := by
  rw [cuspMean_l2_norm_sq]
  have heq :
      (∫ τ : UpperHalfPlane, ‖cuspResidual H hH (cuspCoreValue H F) τ‖^2
        ∂modularMeasure.restrict {τ | H < τ.im}) =
        ∫ τ : UpperHalfPlane in {τ | H < τ.im},
          ‖cuspHorizontalResidual F.val τ‖^2 ∂modularMeasure := by
    apply integral_congr_ae
    filter_upwards [cuspResidual_core_ae H hH F] with τ hτ
    rw [hτ]
  rw [heq]
  exact cuspHorizontal_tail_norm_bound F hH

end GapFamily.Analytic
