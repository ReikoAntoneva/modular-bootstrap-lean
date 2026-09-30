import BTZEntropy.Comparison.InitialPacket
import BTZEntropy.Comparison.InitialPacketPartition
import BTZEntropy.Descendant

/-!
# Subexponential initial-packet estimates

A temperature of `1 / sqrt c` gives a bound uniform on every bounded energy
ratio interval. Polynomial prefactors are absorbed into `exp (C * sqrt c)`.
The actual Euler-product thermal bound supplies all partition estimates;
no Hardy--Ramanujan asymptotic formula is used.
-/

noncomputable section

open Real
open scoped BigOperators

namespace BTZEntropy.Comparison

/-- A fixed polynomial costs only a fixed multiple of `sqrt c` in the
exponent. This bound is valid already at `c = 0`. -/
theorem one_add_pow_le_exp_sqrt {c : ℝ} (hc : 0 ≤ c) (p : ℕ) :
    (1 + c) ^ p ≤ exp ((2 * p) * sqrt c) := by
  have hs := sq_sqrt hc
  have hexp : 1 + c ≤ exp (2 * sqrt c) := by
    have h := pow_le_pow_left₀ (show 0 ≤ sqrt c + 1 by positivity)
      (add_one_le_exp (sqrt c)) 2
    rw [← exp_nat_mul] at h
    exact (show 1 + c ≤ (sqrt c + 1) ^ 2 by nlinarith [sqrt_nonneg c]).trans h
  have h := pow_le_pow_left₀ (show 0 ≤ 1 + c by positivity) hexp p
  rw [← exp_nat_mul] at h
  convert h using 1
  congr 1
  ring

private theorem inverse_sqrt_exponent_le {c x U R σ : ℝ}
    (hc : 1 ≤ c) (hx : x ≤ U) (hR : 0 ≤ R) (hσ : 0 ≤ σ) :
    (1 / sqrt c) * (x * c + R + σ) + 4 / (1 / sqrt c) ≤
      (U + R + σ + 4) * sqrt c := by
  have hcp : 0 < c := by linarith
  have hsp := sqrt_pos.mpr hcp
  have hsq := sq_sqrt hcp.le
  have hmul : (1 / sqrt c) * c = sqrt c := by
    field_simp
    nlinarith
  have hβ : 1 / sqrt c ≤ sqrt c :=
    (div_le_iff₀ hsp).mpr (by nlinarith)
  have hx' := mul_le_mul_of_nonneg_right hx hsp.le
  have hrest := mul_le_mul_of_nonneg_right hβ (add_nonneg hR hσ)
  have hdiv : 4 / (1 / sqrt c) = 4 * sqrt c := by field_simp
  rw [hdiv]
  have heq : (1 / sqrt c) * (x * c + R + σ) =
      x * sqrt c + (1 / sqrt c) * (R + σ) := by
    calc
      _ = x * ((1 / sqrt c) * c) + (1 / sqrt c) * (R + σ) := by ring
      _ = _ := by rw [hmul]
  rw [heq]
  nlinarith

private theorem partitionThermal_sq_le_exp {β : ℝ}
    (hpart : partitionThermal β ≤ exp (2 / β)) :
    partitionThermal β ^ 2 ≤ exp (4 / β) := by
  have h0 : 0 ≤ partitionThermal β := tsum_nonneg (partitionThermalTerm_nonneg β)
  have h := pow_le_pow_left₀ h0 hpart 2
  rw [← exp_nat_mul] at h
  convert h using 1
  congr 1
  ring

/-- Explicit all-spin descendant bound for any finite primary packet with
nonnegative shifted ground energies. The ratio needs only a common upper
bound; in particular the constants are uniform on a positive compact interval. -/
theorem initialPacketSmoothCount_le_sqrt {ι : Type*} [Fintype ι]
    (φ : SmoothKernel) (energy : ι → ℝ) (weight : ι → ℕ)
    {c x U R H : ℝ} (hc : 1 ≤ c) (hx : x ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H)
    (he : ∀ i, 0 ≤ energy i) :
    initialPacketSmoothCount φ energy weight (x * c) ≤
      (∑ i, (weight i : ℝ)) * H * exp ((U + R + 1 / 12 + 4) * sqrt c) := by
  have hβp : 0 < 1 / sqrt c := by positivity
  have hβ := hβp.le
  have hs := summable_partitionThermalTerm hβp
  have hpart := partitionThermal_le_exp hβp
  calc
    _ ≤ (∑ i, (weight i : ℝ)) * H * exp ((1 / sqrt c) * (x * c + R + 1 / 12)) *
        partitionThermal (1 / sqrt c) ^ 2 :=
      initialPacketSmoothCount_le_thermal φ energy weight hβ hH hR hφ hs he
    _ ≤ (∑ i, (weight i : ℝ)) * H * exp ((1 / sqrt c) * (x * c + R + 1 / 12)) *
        exp (4 / (1 / sqrt c)) :=
      mul_le_mul_of_nonneg_left (partitionThermal_sq_le_exp hpart) (by positivity)
    _ = (∑ i, (weight i : ℝ)) * H *
        exp ((1 / sqrt c) * (x * c + R + 1 / 12) + 4 / (1 / sqrt c)) := by
      rw [exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (inverse_sqrt_exponent_le hc hx hR0 (by norm_num))) (by positivity)

/-- The single-primary version of the same estimate, convenient for integrating
against a continuum reference density. -/
theorem primaryModuleSmoothCount_le_sqrt (φ : SmoothKernel)
    {e c x U R H : ℝ} (he : 0 ≤ e) (hc : 1 ≤ c) (hx : x ≤ U)
    (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) :
    moduleSmoothCount φ (fun n => (partitionCount n : ℝ)) (e - 1 / 12) (x * c) ≤
      H * exp ((U + R + 1 / 12 + 4) * sqrt c) := by
  simpa [initialPacketSmoothCount] using
    initialPacketSmoothCount_le_sqrt φ (fun _ : Unit => e) (fun _ => 1)
      hc hx hR0 hH hR hφ (fun _ => he)

/-- The same subexponential bound holds for the unique vacuum module. Its
`-c/12` ground energy supplies the same `1/12` in the uniform coefficient. -/
theorem vacuumSmoothCount_le_sqrt (φ : SmoothKernel)
    {c x U R H : ℝ} (hc : 1 ≤ c) (hx : x ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) :
    vacuumSmoothCount φ c (x * c) ≤
      H * exp ((U + R + 1 / 12 + 4) * sqrt c) := by
  have hβp : 0 < 1 / sqrt c := by positivity
  have hβ := hβp.le
  have hs := summable_partitionThermalTerm hβp
  have hpart := partitionThermal_le_exp hβp
  have hexp : (1 / sqrt c) * (x * c + R + c / 12) + 4 / (1 / sqrt c) ≤
      (U + R + 1 / 12 + 4) * sqrt c := by
    convert inverse_sqrt_exponent_le hc (show x + 1 / 12 ≤ U + 1 / 12 by linarith)
      hR0 (show (0 : ℝ) ≤ 0 by norm_num) using 1 <;> ring
  calc
    _ ≤ H * exp ((1 / sqrt c) * (x * c + R + c / 12)) *
        partitionThermal (1 / sqrt c) ^ 2 :=
      vacuumSmoothCount_le_thermal φ hβ hH hR hφ hs
    _ ≤ H * exp ((1 / sqrt c) * (x * c + R + c / 12)) * exp (4 / (1 / sqrt c)) :=
      mul_le_mul_of_nonneg_left (partitionThermal_sq_le_exp hpart) (by positivity)
    _ = H * exp ((1 / sqrt c) * (x * c + R + c / 12) + 4 / (1 / sqrt c)) := by
      rw [exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp) hH

/-- The fixed kernel and a fixed energy-ratio upper bound supply all vacuum
constants; no spectral, partition, or analytic premise is left to discharge. -/
theorem exists_vacuumSmoothCount_sqrt_bound (φ : SmoothKernel) (X : ℝ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ x : ℝ, x ≤ X →
      vacuumSmoothCount φ c (x * c) ≤ A * exp (C * sqrt c) := by
  obtain ⟨R, H, hR0, hH, hR, hφ⟩ := exists_kernel_upper_bound φ
  refine ⟨H, max 0 X + R + 1 / 12 + 4, hH, by positivity, ?_⟩
  intro c hc x hx
  exact vacuumSmoothCount_le_sqrt φ hc (hx.trans (le_max_right _ _)) hR0 hH hR hφ

/-- A polynomial-times-root-exponential initial mass stays root exponential
after adding every left/right descendant. The mass hypothesis is kept
explicit until it is connected to the actual initial-cell mass theorem. -/
theorem initialPacketSmoothCount_le_sqrt_of_mass {ι : Type*} [Fintype ι]
    (φ : SmoothKernel) (energy : ι → ℝ) (weight : ι → ℕ)
    {c x U R H A D : ℝ} (p : ℕ) (hc : 1 ≤ c) (hx : x ≤ U)
    (hR0 : 0 ≤ R) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H)
    (he : ∀ i, 0 ≤ energy i)
    (hmass : (∑ i, (weight i : ℝ)) ≤ A * (1 + c) ^ p * exp (D * sqrt c)) :
    initialPacketSmoothCount φ energy weight (x * c) ≤
      A * H * exp (((2 * p) + D + U + R + 1 / 12 + 4) * sqrt c) := by
  have hmass' : (∑ i, (weight i : ℝ)) ≤ A * exp (((2 * p) + D) * sqrt c) := by
    calc
      _ ≤ A * (1 + c) ^ p * exp (D * sqrt c) := hmass
      _ ≤ A * exp ((2 * p) * sqrt c) * exp (D * sqrt c) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (one_add_pow_le_exp_sqrt (by linarith) p) hA)
          (exp_nonneg _)
      _ = _ := by rw [add_mul, exp_add]; ring
  calc
    _ ≤ (∑ i, (weight i : ℝ)) * H * exp ((U + R + 1 / 12 + 4) * sqrt c) :=
      initialPacketSmoothCount_le_sqrt φ energy weight hc hx hR0 hH hR hφ
        he
    _ ≤ (A * exp (((2 * p) + D) * sqrt c)) * H *
        exp ((U + R + 1 / 12 + 4) * sqrt c) := by gcongr
    _ = _ := by rw [show ((2 * (p : ℝ)) + D + U + R + 1 / 12 + 4) * sqrt c =
      (((2 * p) + D) * sqrt c) + ((U + R + 1 / 12 + 4) * sqrt c) by ring, exp_add]; ring

end BTZEntropy.Comparison
