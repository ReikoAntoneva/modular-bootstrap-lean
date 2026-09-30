import BTZEntropy.Comparison.UniformEstimate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Transfer of uniform relative count errors to entropy

This module proves the logarithmic step of Proposition 2.3. Its inputs are
explicit relative count estimates and a positive reference; it does not
assume the desired entropy comparison. Separate construction and reference
saddle estimates supply these inputs.
-/

noncomputable section

open Set Filter

namespace BTZEntropy

universe u

theorem abs_log_le_two_mul_abs_sub_one {r : ℝ} (hr : |r - 1| ≤ 1 / 2) :
    |Real.log r| ≤ 2 * |r - 1| := by
  have hx : |1 - r| < 1 := by rw [abs_sub_comm]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 0
  have hid : 1 - (1 - r) = r := by ring
  simp only [Finset.sum_range_zero, zero_add, zero_add, pow_one, hid,
    abs_sub_comm (1 : ℝ) r] at h
  have hden : 0 < 1 - |r - 1| := by linarith
  refine h.trans ((div_le_iff₀ hden).2 ?_)
  nlinarith [abs_nonneg (r - 1)]

/-- A small relative count error proves positivity as well as log stability. -/
theorem count_pos_and_log_error {N R : ℝ} (hR : 0 < R)
    (hrel : |N / R - 1| ≤ 1 / 2) :
    0 < N ∧ |Real.log N - Real.log R| ≤ 2 * |N / R - 1| := by
  have hratio : 0 < N / R := by have := (abs_le.mp hrel).1; linarith
  have hN : 0 < N := (div_pos_iff_of_pos_right hR).mp hratio
  refine ⟨hN, ?_⟩
  rw [← Real.log_div hN.ne' hR.ne']
  exact abs_log_le_two_mul_abs_sub_one hrel

/-- Positivity of a reference count uniformly on each compact positive
energy-ratio interval. It is independent of the gap and node selector. -/
def UniformReferencePositive (reference : ℝ → ℝ → ℝ) : Prop :=
  ∀ L U : ℝ, 0 < L → L ≤ U →
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ a, a₀ ≤ a → ∀ x ∈ Icc L U, 0 < reference a x

/-- Uniform relative matching through each positive inverse-power order. -/
def UniformRelativeMatching {ι : Type u} (B : ℝ) (selectors : Set ι)
    (family : ι → ℝ → ℝ → GapFamily.Spectrum) (φ : SmoothKernel)
    (reference : ℝ → ℝ → ℝ) : Prop :=
  UniformReferencePositive reference ∧
    ∀ q : ℕ, 1 ≤ q → UniformRemainder B selectors q
      (fun σ a δ x => smoothCount φ (GapFamily.gapFamilyCharge a) (family σ a δ)
        (x * GapFamily.gapFamilyCharge a) / reference a x - 1)

theorem uniformCountPositive_of_relative_matching {ι : Type u} {B : ℝ}
    {selectors : Set ι} {family : ι → ℝ → ℝ → GapFamily.Spectrum}
    {φ : SmoothKernel} {reference : ℝ → ℝ → ℝ}
    (hmatch : UniformRelativeMatching B selectors family φ reference) :
    UniformCountPositive B selectors family φ := by
  intro L U hL hLU
  obtain ⟨Nr, hNr, hr⟩ := hmatch.1 L U hL hLU
  obtain ⟨C, hC, Ne, hNe, he⟩ := hmatch.2 1 (by omega) L U hL hLU
  obtain ⟨Ns, hs⟩ := eventually_atTop.1 (eventually_const_div_charge_pow_le_half C
    (q := 1) (by omega))
  refine ⟨max Nr (max Ne Ns), hNr.trans (le_max_left _ _), ?_⟩
  intro σ hσ a ha δ hδ x hx
  have har : Nr ≤ a := (le_max_left _ _).trans ha
  have hae : Ne ≤ a := (le_max_left Ne Ns).trans ((le_max_right _ _).trans ha)
  have has : Ns ≤ a := (le_max_right Ne Ns).trans ((le_max_right _ _).trans ha)
  exact (count_pos_and_log_error (hr a har x hx)
    ((he σ hσ a hae δ hδ x hx).trans (hs a has))).1

theorem uniform_log_error_of_relative_matching {ι : Type u} {B : ℝ}
    {selectors : Set ι} {family : ι → ℝ → ℝ → GapFamily.Spectrum}
    {φ : SmoothKernel} {reference : ℝ → ℝ → ℝ}
    (hmatch : UniformRelativeMatching B selectors family φ reference)
    (q : ℕ) (hq : 1 ≤ q) :
    UniformRemainder B selectors q (fun σ a δ x =>
      smoothEntropy φ (GapFamily.gapFamilyCharge a) (family σ a δ)
        (x * GapFamily.gapFamilyCharge a) - Real.log (reference a x)) := by
  intro L U hL hLU
  obtain ⟨Nr, hNr, hr⟩ := hmatch.1 L U hL hLU
  obtain ⟨C, hC, Ne, hNe, he⟩ := hmatch.2 q hq L U hL hLU
  obtain ⟨Ns, hs⟩ := eventually_atTop.1 (eventually_const_div_charge_pow_le_half C hq)
  refine ⟨2 * C, mul_pos (by norm_num) hC, max Nr (max Ne Ns),
    hNr.trans (le_max_left _ _), ?_⟩
  intro σ hσ a ha δ hδ x hx
  have har : Nr ≤ a := (le_max_left _ _).trans ha
  have hae : Ne ≤ a := (le_max_left Ne Ns).trans ((le_max_right _ _).trans ha)
  have has : Ns ≤ a := (le_max_right Ne Ns).trans ((le_max_right _ _).trans ha)
  have heb := he σ hσ a hae δ hδ x hx
  have hlog := (count_pos_and_log_error (hr a har x hx) (heb.trans (hs a has))).2
  dsimp [smoothEntropy]
  calc
    _ ≤ 2 * |smoothCount φ (GapFamily.gapFamilyCharge a) (family σ a δ)
        (x * GapFamily.gapFamilyCharge a) / reference a x - 1| := hlog
    _ ≤ 2 * (C / GapFamily.gapFamilyCharge a ^ q) :=
      mul_le_mul_of_nonneg_left heb (by norm_num)
    _ = (2 * C) / GapFamily.gapFamilyCharge a ^ q := by ring

/-- The relative count comparison and the reference log expansion give the
full entropy target with exactly the required `P+1` remainder order. -/
theorem uniformSmoothEntropyExpansion_of_relative_matching {ι : Type u} {B : ℝ}
    {selectors : Set ι} {family : ι → ℝ → ℝ → GapFamily.Spectrum}
    {φ : SmoothKernel} {reference : ℝ → ℝ → ℝ}
    (hmatch : UniformRelativeMatching B selectors family φ reference)
    (href : ∀ P : ℕ, UniformRemainder B selectors (P + 1)
      (fun _ a _ x => Real.log (reference a x) -
        entropyTruncation φ x (GapFamily.gapFamilyCharge a) P)) :
    UniformSmoothEntropyExpansion B selectors family φ := by
  refine ⟨uniformCountPositive_of_relative_matching hmatch, ?_⟩
  intro P
  have h := (uniform_log_error_of_relative_matching hmatch (P + 1) (by omega)).add
    (href P)
  simpa only [sub_add_sub_cancel] using h

end BTZEntropy
