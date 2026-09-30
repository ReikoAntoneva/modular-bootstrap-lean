import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdValue
import GapFamily.Analytic.Foundation.ScalarSeedContinuation

/-!
The zero-spin compact continuation is identified with the actual scalar
Eisenstein continuation by their common convergent series. Analytic uniqueness
is applied only after proving both pointwise families analytic on a connected
region containing the punctured physical half-plane and a neighborhood of zero.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareCanonical
open Set Filter UpperHalfPlane CuspFourierCutoff
open scoped Topology

/-- Pointwise scalar analyticity supplies both the physical region and the
threshold neighborhood; no scalar C(K)-valued analyticity is assumed. -/
theorem scalarEisenstein_shifted_analyticAt (τ : UpperHalfPlane) {κ : ℂ}
    (hκ : 0 ≤ κ.re) (hp : κ ≠ (1 / 2 : ℂ)) :
    AnalyticAt ℂ (fun k => scalarEisenstein τ (exponent k)) κ := by
  have hs : 1 / 2 ≤ (exponent κ).re := by
    norm_num [exponent]
    linarith
  have hs1 : exponent κ ≠ 1 := by
    intro h
    apply hp
    unfold exponent at h
    linear_combination h
  exact (scalarEisenstein_analyticAt τ hs hs1).comp_of_eq
    (show AnalyticAt ℂ exponent κ from analyticAt_const.add analyticAt_id) rfl

/-- At any actual upper point, the common original-series identity fixes every
compact zero-spin continuation on a connected neighborhood of the physical region. -/
theorem continuation_zero_spin_eq_scalar
    {K : Set ℂ} [CompactSpace K] (D : Continuation K)
    (τ : UpperHalfPlane) (hτ : (τ : ℂ) ∈ K) :
    ∃ r : ℝ, 0 < r ∧
      EqOn (fun κ => D.family 0 κ ⟨(τ : ℂ), hτ⟩)
        (fun κ => scalarEisenstein τ (exponent κ)) (continuationRegion r) := by
  obtain ⟨ε, hε, hscalar⟩ :=
    (scalarEisenstein_shifted_analyticAt τ (κ := 0) (by norm_num) (by norm_num)).exists_ball_analyticOnNhd
  let r : ℝ := min D.radius ε
  have hr : 0 < r := lt_min D.radius_pos hε
  have hD : AnalyticOnNhd ℂ (fun κ => D.family 0 κ ⟨(τ : ℂ), hτ⟩)
      (continuationRegion r) := by
    intro κ hκ
    exact ((ContinuousMap.evalCLM ℂ ⟨(τ : ℂ), hτ⟩).analyticAt _).comp
      (D.analytic_family 0 κ (continuationRegion_mono (min_le_left _ _) hκ))
  have hS : AnalyticOnNhd ℂ (fun κ => scalarEisenstein τ (exponent κ))
      (continuationRegion r) := by
    intro κ hκ
    rcases hκ with hκ | hκ
    · exact hscalar κ (Metric.ball_subset_ball (min_le_right _ _) hκ)
    · exact scalarEisenstein_shifted_analyticAt τ hκ.1.le hκ.2
  refine ⟨r, hr, eqOn_continuationRegion_of_common hr hD hS ?_⟩
  intro κ hκ
  rw [D.common_region 0 κ hκ ⟨(τ : ℂ), hτ⟩, UpperHalfPlane.ofComplex_apply]
  exact (scalarEisenstein_eq_complexPoincareSeries τ (by
    simp only [exponent, Complex.add_re]
    norm_num
    linarith)).symm

/-- Every compact continuation agrees pointwise with the scalar family across
the whole punctured physical region, independently of the continuation choices. -/
theorem continuation_zero_spin_eq_scalar_physical
    {K : Set ℂ} [CompactSpace K] (D : Continuation K)
    (τ : UpperHalfPlane) (hτ : (τ : ℂ) ∈ K)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) :
    D.family 0 κ ⟨(τ : ℂ), hτ⟩ = scalarEisenstein τ (exponent κ) := by
  obtain ⟨r, _, heq⟩ := continuation_zero_spin_eq_scalar D τ hτ
  exact heq (Or.inr ⟨hκ, hp⟩)

/-- Analytic uniqueness also fixes the threshold value, where the already
proved scalar Eisenstein family vanishes. -/
theorem continuation_zero_spin_at_zero
    {K : Set ℂ} [CompactSpace K] (D : Continuation K)
    (τ : UpperHalfPlane) (hτ : (τ : ℂ) ∈ K) :
    D.family 0 0 ⟨(τ : ℂ), hτ⟩ = scalarEisenstein τ (1 / 2) := by
  obtain ⟨r, hr, heq⟩ := continuation_zero_spin_eq_scalar D τ hτ
  have hz : (0 : ℂ) ∈ continuationRegion r := Or.inl (by
    simpa only [Metric.mem_ball, dist_self] using hr)
  simpa only [exponent, add_zero] using heq hz

/-- The canonical full zero-energy, zero-spin threshold seed has the actual
scalar normalization, with no compatible-choice assumption. -/
theorem thresholdSeed_zero_eq_scalarEisenstein (τ : UpperHalfPlane) :
    thresholdSeed 0 τ = scalarEisenstein τ (1 / 2) := by
  let D := chosenContinuation ({(τ : ℂ)} : Set ℂ) (singleton_subset_upper τ)
  rw [thresholdSeed_eq_continuation D 0 τ (Set.mem_singleton _)]
  exact continuation_zero_spin_at_zero D τ (Set.mem_singleton _)

@[simp] theorem thresholdSeed_zero (τ : UpperHalfPlane) : thresholdSeed 0 τ = 0 := by
  rw [thresholdSeed_zero_eq_scalarEisenstein, scalarEisenstein_half]

/-- Agreement with the pre-existing canonical scalar seed at zero energy. -/
theorem thresholdSeed_zero_eq_continuedScalarSeed (τ : UpperHalfPlane) :
    thresholdSeed 0 τ = continuedScalarSeed 0 τ := by
  rw [thresholdSeed_zero, continuedScalarSeed_zero]

end GapFamily.Analytic.PoincareCanonical
