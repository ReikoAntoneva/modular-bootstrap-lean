import BTZEntropy.Comparison.ReferenceLowBandDefinition
import BTZEntropy.Comparison.DiscreteReferenceSubexponential
import BTZEntropy.Comparison.DiscreteReferenceNormalize
import BTZEntropy.Comparison.DiscreteReferenceScale

/-!
# Negligible fixed low-energy reference band

The genuine leading-reference mass includes the scalar cancellation at the
origin. Adding every left/right descendant to this fixed band leaves only a
square-root exponential rate. The exact difference between the full integer
cone and its fixed cutoff is therefore negligible at every saddle-normalized
inverse charge order.
-/

noncomputable section

open Set Filter Real GapFamily

namespace BTZEntropy.Comparison

universe u

/-- The true low-band reference mass and complete descendant estimate give
an explicit square-root charge bound, uniform over bounded energy ratios. -/
theorem lowLeadingSmoothCount_le_exp_sqrt (φ : SmoothKernel)
    {a c T x U R H : ℝ} (ha : 2 ≤ a) (hc : 1 ≤ c) (hac : a ≤ c)
    (hT : 0 ≤ T) (hx : x ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ v, φ v ≠ 0 → v ≤ R) (hφ : ∀ v, φ v ≤ H) :
    lowLeadingSmoothCount φ a T (x * c) ≤
      (96 * π ^ 2 * (1 + T) ^ 2 * H) *
        exp (((U + R + 1 / 12 + 4) + (4 * π * sqrt T + 2)) * sqrt c) := by
  have hm := leadingMass_zero_le_exp_sqrt ha hT
  have hmodule (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) T) :
      fullPrimaryDescendantTest φ (x * c) v ≤
        H * exp ((U + R + 1 / 12 + 4) * sqrt c) :=
    primaryModuleSmoothCount_le_sqrt φ hv.1.le hc hx hR0 hH hR hφ
  have hcount := lowLeadingSmoothCount_le φ ha hT (x * c)
    (mul_nonneg hH (exp_nonneg _)) hmodule
  calc
    _ ≤ (H * exp ((U + R + 1 / 12 + 4) * sqrt c)) * leadingMass a 0 T := hcount
    _ ≤ (H * exp ((U + R + 1 / 12 + 4) * sqrt c)) *
        ((96 * π ^ 2 * (1 + T) ^ 2) * exp ((4 * π * sqrt T + 2) * sqrt a)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ (H * exp ((U + R + 1 / 12 + 4) * sqrt c)) *
        ((96 * π ^ 2 * (1 + T) ^ 2) * exp ((4 * π * sqrt T + 2) * sqrt c)) := by
      gcongr
    _ = _ := by
      rw [show ((U + R + 1 / 12 + 4) + (4 * π * sqrt T + 2)) * sqrt c =
        (U + R + 1 / 12 + 4) * sqrt c + (4 * π * sqrt T + 2) * sqrt c by ring,
        exp_add]
      ring

/-- The fixed cutoff and kernel supply all constants in the all-descendant
low-band bound. No estimate on an unweighted singular measure is assumed. -/
theorem exists_lowLeadingSmoothCount_sqrt_bound (φ : SmoothKernel) (T U : ℝ)
    (hT : 0 ≤ T) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∀ a c : ℝ, 2 ≤ a → 1 ≤ c → a ≤ c → ∀ x : ℝ, x ≤ U →
        lowLeadingSmoothCount φ a T (x * c) ≤ A * exp (D * sqrt c) := by
  obtain ⟨R, H, hR0, hH, hR, hφ⟩ := exists_kernel_upper_bound φ
  refine ⟨96 * π ^ 2 * (1 + T) ^ 2 * H,
    (max 0 U + R + 1 / 12 + 4) + (4 * π * sqrt T + 2),
    by positivity, by positivity, ?_⟩
  intro a c ha hc hac x hx
  exact lowLeadingSmoothCount_le_exp_sqrt φ ha hc hac hT
    (hx.trans (le_max_right _ _)) hR0 hH hR hφ

/-- The complete low-band descendant count is negligible to every requested
inverse charge order, retaining the Gaussian square-root normalization. -/
theorem lowLeadingSmoothCount_eventually_saddle_scale (φ : SmoothKernel)
    (T : ℝ) (hT : 0 ≤ T) {L U : ℝ} (hL : 0 < L) (P : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ x ∈ Icc L U,
      lowLeadingSmoothCount φ (shift (gapFamilyCharge a)) T (x * gapFamilyCharge a) ≤
        exp (leadingAction x (gapFamilyCharge a)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) := by
  obtain ⟨A, D, hA, _, hbound⟩ := exists_lowLeadingSmoothCount_sqrt_bound φ T U hT
  filter_upwards [subexponential_eventually_gapFamily_le (D := D) hL hA P,
    eventually_ge_atTop (2 : ℝ)] with a hscale ha
  intro x hx
  have ha' : 2 ≤ shift (gapFamilyCharge a) := by simpa using ha
  have hc : 1 ≤ gapFamilyCharge a := (gapFamilyCharge_gt_one (by linarith)).le
  have hac : shift (gapFamilyCharge a) ≤ gapFamilyCharge a := by
    unfold shift
    linarith
  have h := (hbound _ _ ha' hc hac x hx.2).trans (hscale x hx.1)
  simpa only [leadingAction_eq_btz] using h

/-- The error compares the exact full-cone and cutoff reference observables,
not a proxy based on their thermal transforms. -/
theorem integerLeadingSmoothCount_cutoff_eventually_saddle_scale (φ : SmoothKernel)
    (T : ℝ) (hT : 0 ≤ T) {L U : ℝ} (hL : 0 < L) (P : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ x ∈ Icc L U,
      |integerLeadingSmoothCount φ (shift (gapFamilyCharge a)) 0 (x * gapFamilyCharge a) -
        integerLeadingSmoothCount φ (shift (gapFamilyCharge a)) T (x * gapFamilyCharge a)| ≤
        exp (leadingAction x (gapFamilyCharge a)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) := by
  filter_upwards [lowLeadingSmoothCount_eventually_saddle_scale φ T hT (U := U) hL P,
    eventually_ge_atTop (2 : ℝ)] with a hcount ha
  intro x hx
  have ha' : 2 ≤ shift (gapFamilyCharge a) := by simpa using ha
  rw [integerLeadingSmoothCount_sub_cutoff φ ha' hT,
    abs_of_nonneg (lowLeadingSmoothCount_nonneg φ ha' T _)]
  exact hcount x hx

/-- Every fixed integer-reference cutoff is invisible to all finite orders
at the actual saddle count scale. The reference is independent of the
selector and marker, so the same bound holds for any specified class. -/
theorem integerLeadingSmoothCount_cutoff_uniformRemainder {ι : Type u}
    (B : ℝ) (selectors : Set ι) (φ : SmoothKernel) (T : ℝ) (hT : 0 ≤ T) (P : ℕ) :
    UniformRemainder B selectors P
      (fun _ a _ x =>
        (integerLeadingSmoothCount φ (shift (gapFamilyCharge a)) 0 (x * gapFamilyCharge a) -
          integerLeadingSmoothCount φ (shift (gapFamilyCharge a)) T (x * gapFamilyCharge a)) /
          saddleCountScale φ x (gapFamilyCharge a)) := by
  apply uniformRemainder_div_saddleCountScale_of_raw_bound
  intro L U hL _
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [integerLeadingSmoothCount_cutoff_eventually_saddle_scale φ T hT (U := U) hL P]
    with a hbound
  intro _ _ _ _ x hx
  simpa only [one_mul] using hbound x hx

end BTZEntropy.Comparison
