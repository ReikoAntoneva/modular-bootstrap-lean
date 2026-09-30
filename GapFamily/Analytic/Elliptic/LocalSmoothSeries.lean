import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic

/-!
A local smooth-series theorem on an open preconnected complex-coordinate domain.
The scalar field is real, and the complete codomain may be any real normed space.
-/

noncomputable section
namespace GapFamily.Analytic.LocalSmoothSeries
open Set Filter
open scoped Topology ContDiff

universe u v

/-- Actual first differentiation from summable zeroth and first derivative bounds. -/
theorem hasFDerivAt_tsum_of_bounds {ι : Type v} {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (f : ι → ℂ → F) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (b : ℕ → ι → ℝ) (hb : ∀ n, Summable (b n))
    (hbound : ∀ (n : ℕ) (i : ι) (z : ℂ), z ∈ U →
      ‖iteratedFDeriv ℝ n (f i) z‖ ≤ b n i)
    {z : ℂ} (hz : z ∈ U) :
    HasFDerivAt (fun w => ∑' i, f i w) (∑' i, fderiv ℝ (f i) z) z := by
  have hd : ∀ (i : ι) (w : ℂ), w ∈ U →
      HasFDerivAt (f i) (fderiv ℝ (f i) w) w := by
    intro i w hw
    exact ((hf i).differentiableOn (by simp) w hw).differentiableAt
      (hU.mem_nhds hw) |>.hasFDerivAt
  have hb1 : ∀ (i : ι) (w : ℂ), w ∈ U → ‖fderiv ℝ (f i) w‖ ≤ b 1 i := by
    intro i w hw
    simpa only [norm_iteratedFDeriv_one] using hbound 1 i w hw
  have hsum : Summable (fun i => f i z) :=
    Summable.of_norm_bounded (hb 0) (fun i => by
      simpa only [norm_iteratedFDeriv_zero] using hbound 0 i z hz)
  exact hasFDerivAt_tsum_of_isPreconnected (hb 1) hU hconn hd hb1 hz hsum hz

private theorem contDiffOn_tsum_nat {ι : Type v} (n : ℕ) :
    ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      {U : Set ℂ}, IsOpen U → IsPreconnected U →
      ∀ (f : ι → ℂ → F), (∀ i, ContDiffOn ℝ ∞ (f i) U) →
      ∀ (b : ℕ → ι → ℝ), (∀ k, Summable (b k)) →
      (∀ (k : ℕ) (i : ι) (z : ℂ), z ∈ U →
        ‖iteratedFDeriv ℝ k (f i) z‖ ≤ b k i) →
      ContDiffOn ℝ n (fun z => ∑' i, f i z) U := by
  induction n with
  | zero =>
      intro F _ _ _ U hU hconn f hf b hb hbound
      apply contDiffOn_zero.mpr
      exact continuousOn_tsum (fun i => (hf i).continuousOn) (hb 0)
        (fun i z hz => by simpa only [norm_iteratedFDeriv_zero] using hbound 0 i z hz)
  | succ n ih =>
      intro F _ _ _ U hU hconn f hf b hb hbound
      have hD : ∀ {z : ℂ}, z ∈ U →
          HasFDerivAt (fun w => ∑' i, f i w) (∑' i, fderiv ℝ (f i) z) z :=
        fun hz => hasFDerivAt_tsum_of_bounds hU hconn f hf b hb hbound hz
      have hterms : ∀ i, ContDiffOn ℝ ∞ (fderiv ℝ (f i)) U := by
        intro i
        exact (hf i).fderiv_of_isOpen hU (by simp)
      have hshift : ∀ (k : ℕ) (i : ι) (z : ℂ), z ∈ U →
          ‖iteratedFDeriv ℝ k (fderiv ℝ (f i)) z‖ ≤ b (k + 1) i := by
        intro k i z hz
        rw [norm_iteratedFDeriv_fderiv]
        exact hbound (k + 1) i z hz
      have hI := ih (ℂ →L[ℝ] F) hU hconn (fun i => fderiv ℝ (f i)) hterms
        (fun k => b (k + 1)) (fun k => hb (k + 1)) hshift
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun z hz => (hD hz).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · intro hn
        simp at hn
      · exact hI.congr (fun z hz => (hD hz).fderiv)

/-- Smoothness on an open preconnected domain follows from actual term smoothness
and one summable uniform bound at every derivative order. -/
theorem contDiffOn_tsum_of_bounds {ι : Type v} {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (f : ι → ℂ → F) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (b : ℕ → ι → ℝ) (hb : ∀ n, Summable (b n))
    (hbound : ∀ (n : ℕ) (i : ι) (z : ℂ), z ∈ U →
      ‖iteratedFDeriv ℝ n (f i) z‖ ≤ b n i) :
    ContDiffOn ℝ ∞ (fun z => ∑' i, f i z) U := by
  apply contDiffOn_infty.mpr
  intro n
  exact contDiffOn_tsum_nat n F hU hconn f hf b hb hbound

end GapFamily.Analytic.LocalSmoothSeries
