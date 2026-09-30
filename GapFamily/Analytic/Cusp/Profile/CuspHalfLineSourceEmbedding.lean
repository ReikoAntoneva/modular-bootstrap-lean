import GapFamily.Analytic.Cusp.Profile.CuspHalfLineSourceMeasure
import GapFamily.Analytic.Cusp.Profile.CuspHalfLineSourceAE
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The full positive logarithmic source isometry. No compact-support, decay,
continuity, or scalar form-domain hypothesis is imposed on the source. -/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory CuspHalfLineSource

/-- Exactly the ordinary logarithmic half-line L² space used by the Laplace functional. -/
abbrev cuspHalfLineSourceHilbert := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

def cuspHalfLineSourceValue (f : cuspHalfLineSourceHilbert) : ModularHilbert :=
  ((memLp_rawLift_iff (Lp.stronglyMeasurable f).measurable).mpr (Lp.memLp f)).toLp _

theorem cuspHalfLineSourceValue_ae (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceValue f =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then cuspLift (f : ℝ → ℂ) τ.im else 0) :=
  MemLp.coeFn_toLp _

private theorem rawLift_add (f g : ℝ → ℂ) (τ : UpperHalfPlane) :
    rawLift (f + g) τ = rawLift f τ + rawLift g τ := by
  by_cases ht : 1 < τ.im <;> simp [rawLift, ht, cuspLift, smul_add]

private theorem rawLift_smul (c : ℂ) (f : ℝ → ℂ) (τ : UpperHalfPlane) :
    rawLift (c • f) τ = c • rawLift f τ := by
  by_cases ht : 1 < τ.im
  · simp only [rawLift, ht, ite_true, cuspLift, Pi.smul_apply]
    exact smul_comm _ _ _
  · simp [rawLift, ht]

theorem cuspHalfLineSourceValue_add (f g : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceValue (f + g) = cuspHalfLineSourceValue f + cuspHalfLineSourceValue g := by
  have hinner := cuspHalfLine_lift_congr_ae (Lp.coeFn_add f g)
  apply Lp.ext
  filter_upwards [cuspHalfLineSourceValue_ae (f + g), cuspHalfLineSourceValue_ae f,
    cuspHalfLineSourceValue_ae g,
    Lp.coeFn_add (cuspHalfLineSourceValue f) (cuspHalfLineSourceValue g), hinner]
    with τ hfg hf hg hsum hi
  rw [hfg, hsum, Pi.add_apply, hf, hg, hi]
  exact rawLift_add f g τ

theorem cuspHalfLineSourceValue_smul (c : ℂ) (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceValue (c • f) = c • cuspHalfLineSourceValue f := by
  have hinner := cuspHalfLine_lift_congr_ae (Lp.coeFn_smul c f)
  apply Lp.ext
  filter_upwards [cuspHalfLineSourceValue_ae (c • f), cuspHalfLineSourceValue_ae f,
    Lp.coeFn_smul c (cuspHalfLineSourceValue f), hinner] with τ hcf hf hs hi
  rw [hcf, hs, Pi.smul_apply, hf, hi]
  exact rawLift_smul c f τ

theorem cuspHalfLineSourceValue_norm_sq (f : cuspHalfLineSourceHilbert) :
    ‖cuspHalfLineSourceValue f‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ τ : UpperHalfPlane, ‖rawLift f τ‖ ^ 2 ∂modularMeasure := by
      apply integral_congr_ae
      filter_upwards [cuspHalfLineSourceValue_ae f] with τ hτ
      simp only [hτ, real_inner_self_eq_norm_sq]
      rfl
    _ = ∫ t : ℝ in Ioi 0, ‖f t‖ ^ 2 :=
      integral_rawLift_norm_sq f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
    _ = ‖f‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]

theorem cuspHalfLineSourceValue_norm (f : cuspHalfLineSourceHilbert) :
    ‖cuspHalfLineSourceValue f‖ = ‖f‖ := by
  nlinarith [cuspHalfLineSourceValue_norm_sq f, norm_nonneg (cuspHalfLineSourceValue f),
    norm_nonneg f]

/-- The actual full half-line scalar source isometry. -/
def cuspHalfLineSourceEmbedding : cuspHalfLineSourceHilbert →ₗᵢ[ℂ] ModularHilbert where
  toFun := cuspHalfLineSourceValue
  map_add' := cuspHalfLineSourceValue_add
  map_smul' := cuspHalfLineSourceValue_smul
  norm_map' := cuspHalfLineSourceValue_norm

theorem cuspHalfLineSourceEmbedding_ae (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceEmbedding f =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then Real.sqrt τ.im • f (Real.log τ.im) else 0) :=
  cuspHalfLineSourceValue_ae f

theorem cuspHalfLineSourceEmbedding_norm (f : cuspHalfLineSourceHilbert) :
    ‖cuspHalfLineSourceEmbedding f‖ = ‖f‖ :=
  cuspHalfLineSourceEmbedding.norm_map f

theorem cuspHalfLineSourceEmbedding_norm_sq (f : cuspHalfLineSourceHilbert) :
    ‖cuspHalfLineSourceEmbedding f‖ ^ 2 = ∫ t : ℝ in Ioi 0, ‖f t‖ ^ 2 := by
  rw [cuspHalfLineSourceEmbedding_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- The global scalar logarithmic coefficient is the adjoint of the constructed isometry. -/
def cuspHalfLineSourceCoefficient : ModularHilbert →L[ℂ] cuspHalfLineSourceHilbert :=
  cuspHalfLineSourceEmbedding.toContinuousLinearMap.adjoint

theorem cuspHalfLineSourceCoefficient_inner_left (f : cuspHalfLineSourceHilbert)
    (F : ModularHilbert) :
    inner ℂ (cuspHalfLineSourceCoefficient F) f = inner ℂ F (cuspHalfLineSourceEmbedding f) :=
  cuspHalfLineSourceEmbedding.toContinuousLinearMap.adjoint_inner_left f F

theorem cuspHalfLineSourceCoefficient_inner_right (f : cuspHalfLineSourceHilbert)
    (F : ModularHilbert) :
    inner ℂ f (cuspHalfLineSourceCoefficient F) = inner ℂ (cuspHalfLineSourceEmbedding f) F :=
  cuspHalfLineSourceEmbedding.toContinuousLinearMap.adjoint_inner_right f F

@[simp] theorem cuspHalfLineSourceCoefficient_embedding (f : cuspHalfLineSourceHilbert) :
    cuspHalfLineSourceCoefficient (cuspHalfLineSourceEmbedding f) = f := by
  apply ext_inner_right ℂ
  intro g
  rw [cuspHalfLineSourceCoefficient_inner_left]
  exact cuspHalfLineSourceEmbedding.inner_map_map f g

theorem cuspHalfLineSourceCoefficient_opNorm_le : ‖cuspHalfLineSourceCoefficient‖ ≤ 1 := by
  unfold cuspHalfLineSourceCoefficient
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact cuspHalfLineSourceEmbedding.norm_toContinuousLinearMap_le

theorem cuspHalfLineSourceCoefficient_norm_le (F : ModularHilbert) :
    ‖cuspHalfLineSourceCoefficient F‖ ≤ ‖F‖ := by
  calc
    _ ≤ ‖cuspHalfLineSourceCoefficient‖ * ‖F‖ := cuspHalfLineSourceCoefficient.le_opNorm F
    _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right cuspHalfLineSourceCoefficient_opNorm_le
      (norm_nonneg F)
    _ = _ := one_mul _

theorem cuspHalfLineSourceCoefficient_residual_orthogonal (f : cuspHalfLineSourceHilbert)
    (F : ModularHilbert) :
    inner ℂ (cuspHalfLineSourceEmbedding f)
      (F - cuspHalfLineSourceEmbedding (cuspHalfLineSourceCoefficient F)) = 0 := by
  rw [inner_sub_right, ← cuspHalfLineSourceCoefficient_inner_right,
    cuspHalfLineSourceEmbedding.inner_map_map, sub_self]

end GapFamily.Analytic
