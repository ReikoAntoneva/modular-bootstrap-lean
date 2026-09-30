import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRemainderBound
import GapFamily.Analytic.Poincare.PoincareRemainderAnalytic
import GapFamily.Analytic.Arithmetic.Kloosterman
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries

/-! The actual absolutely and normally convergent denominator remainder. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourierRemainder
open Set Filter MeasureTheory
open scoped Topology

/-- The phase-subtracted ordinary Fourier remainder, with the actual finite
Kloosterman sum at every positive denominator. -/
def fourierRemainder (y : ℝ) (j J : ℤ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, kloostermanSum j J n *
    ∫ t : ℝ, fourierRemainderKernel (n + 1 : ℕ) y j J s t


theorem rpow_neg_le_max_endpoints {y δ B σ : ℝ} (hy : 0 < y)
    (hδ : δ ≤ σ) (hB : σ ≤ B) :
    y ^ (-σ) ≤ max (y ^ (-δ)) (y ^ (-B)) := by
  rcases le_total 1 y with hy1 | hy1
  · exact (Real.rpow_le_rpow_of_exponent_le hy1 (neg_le_neg hδ)).trans
      (le_max_left _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge hy hy1 (neg_le_neg hB)).trans
      (le_max_right _ _)

theorem summable_remainder_power {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-2 * δ - 1)) := by
  exact (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith))

private theorem mul_remainder_rpow {c σ : ℝ} (hc : 0 < c) :
    c * c ^ (-2 * σ - 2) = c ^ (-2 * σ - 1) := by
  calc
    c * c ^ (-2 * σ - 2) = c ^ (1 : ℝ) * c ^ (-2 * σ - 2) := by rw [Real.rpow_one]
    _ = c ^ ((1 : ℝ) + (-2 * σ - 2)) := (Real.rpow_add hc _ _).symm
    _ = c ^ (-2 * σ - 1) := by congr 1; ring

private theorem remainder_rpow_majorant_mono {y δ B σ c : ℝ}
    (hy : 0 < y) (hδ : 0 < δ) (hδσ : δ ≤ σ) (hσB : σ ≤ B) (hc : 1 ≤ c)
    {A : ℝ} (hA : 0 ≤ A)
    :
    A / σ * y ^ (-σ) * c ^ (-2 * σ - 1) ≤
      A / δ * max (y ^ (-δ)) (y ^ (-B)) * c ^ (-2 * δ - 1) := by
  have hybound := rpow_neg_le_max_endpoints hy hδσ hσB
  have hcoeff : A / σ ≤ A / δ := div_le_div_of_nonneg_left hA hδ hδσ
  have hpower : c ^ (-2 * σ - 1) ≤ c ^ (-2 * δ - 1) :=
    Real.rpow_le_rpow_of_exponent_le hc (by linarith)
  exact mul_le_mul (mul_le_mul hcoeff hybound (Real.rpow_nonneg hy.le _)
    (div_nonneg hA hδ.le)) hpower
    (Real.rpow_nonneg (zero_le_one.trans hc) _) (by positivity)

/-- The actual finite arithmetic coefficient costs only one power of its denominator. -/
theorem norm_fourierRemainder_term_le {y : ℝ} (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖kloostermanSum j J n *
        ∫ t : ℝ, fourierRemainderKernel (n + 1 : ℕ) y j J s t‖ ≤
      (2 * Real.pi * |(J : ℝ)| / s.re) * y ^ (-s.re) *
        ((n + 1 : ℕ) : ℝ) ^ (-2 * s.re - 1) := by
  let c : ℝ := (n + 1 : ℕ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : ‖kloostermanSum j J n‖ ≤ c := by
    simpa only [c, Nat.cast_add, Nat.cast_one] using norm_kloostermanSum_le j J n
  rw [norm_mul]
  calc
    _ ≤ c * ((2 * Real.pi * |(J : ℝ)| / s.re) * y ^ (-s.re) *
        c ^ (-2 * s.re - 2)) :=
      mul_le_mul hK (norm_integral_fourierRemainderKernel_le hc hy j J hs)
        (norm_nonneg _) hc.le
    _ = (2 * Real.pi * |(J : ℝ)| / s.re) * y ^ (-s.re) *
        (c * c ^ (-2 * s.re - 2)) := by ring
    _ = _ := by rw [mul_remainder_rpow hc]

/-- One explicit summable majorant controls the actual remainder on a closed
parameter strip, without bounds on its imaginary part. -/
theorem fourierRemainder_normal_on_strip {y δ B : ℝ} (hy : 0 < y)
    (hδ : 0 < δ) (j J : ℤ) :
    ∃ u : ℕ → ℝ, Summable u ∧ (∀ n, 0 ≤ u n) ∧
      ∀ (n : ℕ) (s : ℂ), δ ≤ s.re → s.re ≤ B →
        ‖kloostermanSum j J n *
          ∫ t : ℝ, fourierRemainderKernel (n + 1 : ℕ) y j J s t‖ ≤ u n := by
  let A : ℝ := 2 * Real.pi * |(J : ℝ)|
  let C : ℝ := (A / δ) * max (y ^ (-δ)) (y ^ (-B))
  refine ⟨fun n => C * ((n + 1 : ℕ) : ℝ) ^ (-2 * δ - 1),
    (summable_remainder_power hδ).mul_left C, ?_, ?_⟩
  · intro n
    dsimp [C, A]
    positivity
  · intro n s hδs hsB
    refine (norm_fourierRemainder_term_le hy j J (hδ.trans_le hδs) n).trans ?_
    exact remainder_rpow_majorant_mono hy hδ hδs hsB
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (by positivity)

/-- Genuine absolute convergence at every point of the half-plane Re s > 0. -/
theorem summable_norm_fourierRemainder {y : ℝ} (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => ‖kloostermanSum j J n *
      ∫ t : ℝ, fourierRemainderKernel (n + 1 : ℕ) y j J s t‖) := by
  obtain ⟨u, hu, _, hb⟩ := fourierRemainder_normal_on_strip (B := s.re) hy hs j J
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hb n s le_rfl le_rfl)

/-- The defining tsum is the sum of the actual ordinary remainder integrals. -/
theorem hasSum_fourierRemainder {y : ℝ} (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => kloostermanSum j J n *
      ∫ t : ℝ, fourierRemainderKernel (n + 1 : ℕ) y j J s t)
      (fourierRemainder y j J s) :=
  (summable_norm_fourierRemainder hy j J hs).of_norm.hasSum

/-- Quantitative bound for the full actual remainder. -/
theorem norm_fourierRemainder_le {y : ℝ} (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    ‖fourierRemainder y j J s‖ ≤
      (2 * Real.pi * |(J : ℝ)| / s.re) * y ^ (-s.re) *
        ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-2 * s.re - 1) := by
  have hnorm := summable_norm_fourierRemainder hy j J hs
  have hmajorant := (summable_remainder_power hs).mul_left
    ((2 * Real.pi * |(J : ℝ)| / s.re) * y ^ (-s.re))
  calc
    _ ≤ ∑' n : ℕ, ‖kloostermanSum j J n *
        ∫ t : ℝ, fourierRemainderKernel (n + 1 : ℕ) y j J s t‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (2 * Real.pi * |(J : ℝ)| / s.re) * y ^ (-s.re) *
        ((n + 1 : ℕ) : ℝ) ^ (-2 * s.re - 1) :=
      hnorm.tsum_le_tsum (norm_fourierRemainder_term_le hy j J hs) hmajorant
    _ = _ := tsum_mul_left

/-- The denominator remainder is analytic throughout Re s > 0. The literal
ordinary integral and denominator series are both proved convergent. -/
theorem analyticAt_fourierRemainder {y : ℝ} (hy : 0 < y)
    (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fourierRemainder y j J) s := by
  let δ : ℝ := s.re / 2
  let B : ℝ := s.re + 1
  have hδ : 0 < δ := half_pos hs
  let U : Set ℂ := {z : ℂ | δ < z.re ∧ z.re < B}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hsU : s ∈ U := by dsimp [U, δ, B]; constructor <;> linarith
  obtain ⟨u, hu, _, hb⟩ := fourierRemainder_normal_on_strip (B := B) hy hδ j J
  have hd : DifferentiableOn ℂ (fourierRemainder y j J) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm hu
    · intro n z hz
      have hzpos : 0 < z.re := hδ.trans hz.1
      exact (analyticAt_const.mul
        (analyticAt_integral_fourierRemainderKernel (by positivity) hy j J hzpos)).differentiableAt.differentiableWithinAt
    · exact hU
    · intro n z hz
      exact hb n z hz.1.le hz.2.le
  exact hd.analyticAt (hU.mem_nhds hsU)

/-- Analyticity on the full open half-plane, including the target s = 1/2. -/
theorem analyticOnNhd_fourierRemainder {y : ℝ} (hy : 0 < y) (j J : ℤ) :
    AnalyticOnNhd ℂ (fourierRemainder y j J) {s : ℂ | 0 < s.re} :=
  fun _ hs => analyticAt_fourierRemainder hy j J hs

end GapFamily.Analytic.PoincareFourierRemainder
