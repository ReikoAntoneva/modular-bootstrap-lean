import GapFamily.Analytic.Modular.Elliptic.ModularEllipticContinuousInput
import GapFamily.Analytic.Elliptic.LocalWeakHessianApproximationCoordinate

/-! # Centered rectangular neighborhoods for the actual local continuity argument -/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory Homogenization ModularElliptic LocalWeakHessian

/-- Pair coordinates centered at the specified physical point. -/
def ellipticPairChart (z : ℂ) : (ℝ × ℝ) ≃ₜ ℂ :=
  pairToVec.toHomeomorph.trans (ellipticChart z)

@[simp] theorem ellipticPairChart_apply (z : ℂ) (q : ℝ × ℝ) :
    ellipticPairChart z q = ellipticChart z (pairToVec q) := rfl

@[simp] theorem ellipticPairChart_zero (z : ℂ) : ellipticPairChart z 0 = z := by
  simp only [ellipticPairChart_apply, map_zero, ellipticChart_zero]

theorem ellipticPairChart_measurePreserving (z : ℂ) :
    MeasurePreserving (ellipticPairChart z) volume volume :=
  (ellipticChart_measurePreserving z).comp pairToVec_measurePreserving

theorem ellipticPairChart_measurePreserving_restrict_image
    (z : ℂ) (W : Set (ℝ × ℝ)) :
    MeasurePreserving (ellipticPairChart z) (volume.restrict W)
      (volume.restrict (ellipticPairChart z '' W)) :=
  (ellipticPairChart_measurePreserving z).restrict_image_emb
    (ellipticPairChart z).toMeasurableEquiv.measurableEmbedding W

def ellipticInnerRadius (Q : TriadicCube 2) : ℝ := cubeRadius Q / 4

theorem ellipticInnerRadius_pos (Q : TriadicCube 2) : 0 < ellipticInnerRadius Q :=
  div_pos (cubeRadius_pos Q) (by norm_num)

theorem ellipticInnerRadius_closedBall_subset (Q : TriadicCube 2)
    (hQ : cubeCenter Q = 0) :
    Metric.closedBall (0 : Vec 2) (ellipticInnerRadius Q) ⊆
      scaledOpenCubeSet Q (1 / 2) := by
  intro v hv i
  have hvn : ‖v‖ ≤ ellipticInnerRadius Q := by simpa using hv
  change |v i - cubeCenter Q i| < (1 / 2 : ℝ) * cubeRadius Q
  rw [hQ]
  simp only [Pi.zero_apply, sub_zero]
  have hvi : |v i| ≤ ‖v‖ := norm_le_pi_norm v i
  have hr := cubeRadius_pos Q
  dsimp [ellipticInnerRadius] at hvn
  linarith

/-- A fixed nondegenerate closed pair rectangle lies strictly inside the half cube. -/
theorem ellipticInnerRadius_rectangle_subset (Q : TriadicCube 2)
    (hQ : cubeCenter Q = 0) :
    Icc (-ellipticInnerRadius Q) (ellipticInnerRadius Q) ×ˢ
        Icc (-ellipticInnerRadius Q) (ellipticInnerRadius Q) ⊆
      pairToVec ⁻¹' scaledOpenCubeSet Q (1 / 2) := by
  intro q hq i
  rw [hQ]
  simp only [Pi.zero_apply, sub_zero]
  have hr := cubeRadius_pos Q
  rcases hq with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
  dsimp [ellipticInnerRadius] at hx0 hx1 hy0 hy1
  fin_cases i
  · change |q.1| < _
    rw [abs_lt]
    constructor <;> linarith
  · change |q.2| < _
    rw [abs_lt]
    constructor <;> linarith

end GapFamily.Analytic.ModularGradient
