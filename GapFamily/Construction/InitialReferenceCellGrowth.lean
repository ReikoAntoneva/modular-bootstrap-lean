import GapFamily.Construction.InitialReferenceCellResidual
import GapFamily.Construction.InitialReferenceCellTerminal
import GapFamily.Construction.InitialReferenceDensity
import GapFamily.Construction.InitialParameterReserve

/-!
# Uniform initial-cell existence from physical reference bounds

The proved integer parameter inequalities and exponential reserve supply
every numerical hypothesis of endpoint selection. Only ordinary density
estimates are inputs; the density may have a signed low-energy part.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A fixed positive upper-half coefficient and the ordinary negative-mass
budget supply all initial rows, with their actual natural moment degree,
at one common integer threshold. -/
theorem exists_initialReferenceCell_threshold_of_bounds
    {R₀ R s : ℕ} (hR₀ : 3 < R₀) (hR : 16 * R₀ ≤ R) (hs : 1 ≤ s)
    {c B C_N : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hC_N : C_N ≤ sqrt (R : ℝ)) (p : ℕ) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ j : ℤ,
      |(j : ℝ)| ≤ ((R₀ * n : ℕ) : ℝ) → ∀ q : ℝ → ℝ,
      IntegrableOn q (Ioo (max (n : ℝ) |(j : ℝ)|) (((R * n : ℕ) : ℝ) + 1))
        (referenceMeasure j) →
      (∫ E in Ioo (max (n : ℝ) |(j : ℝ)|) (((R * n : ℕ) : ℝ) + 1),
        max (-q E) 0 ∂referenceMeasure j) ≤
          B * (1 + ((R * s ^ 2 * n : ℕ) : ℝ)) ^ p *
            exp (C_N * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * (n : ℝ))) →
      (∀ E ∈ Icc (((R * n : ℕ) : ℝ) / 4) (((R * n : ℕ) : ℝ) + 1),
        c * (E ^ 2 - (j : ℝ) ^ 2) *
          exp (8 * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * E)) ≤ q E) →
      Nonempty (InitialReferenceCell j (max (n : ℝ) |(j : ℝ)|)
        ((R * n : ℕ) : ℝ) (R * s * n) q) := by
  have hR₀1 : 1 ≤ R₀ := by omega
  have hR16 : 16 ≤ R :=
    (show 16 ≤ 16 * R₀ by simpa using Nat.mul_le_mul_left 16 hR₀1).trans hR
  have hR1 : 1 ≤ R := by omega
  obtain ⟨n₁, hn₁⟩ := exists_initialParameter_variation_threshold R s hR1 hs
    (show 0 < c / 32 by positivity) hB hC_N p (1 / 2)
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (max 1 (2 / c))
  have hn₂1 : 1 ≤ n₂ := by exact_mod_cast (le_max_left _ _).trans_lt hn₂ |>.le
  refine ⟨max n₁ n₂, hn₂1.trans (le_max_right _ _), ?_⟩
  intro n hn j hj q hq hnegative hbound
  have hn1 : 1 ≤ n := hn₂1.trans ((le_max_right _ _).trans hn)
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hU1 : (1 : ℝ) ≤ ((R * n : ℕ) : ℝ) := by
    exact_mod_cast one_le_mul_of_one_le_of_one_le hR1 hn1
  have hUpos : (0 : ℝ) < ((R * n : ℕ) : ℝ) := by linarith
  have hbU : (n : ℝ) ≤ ((R * n : ℕ) : ℝ) / 16 := by
    have h := Nat.mul_le_mul_right n hR16
    have h' : (16 : ℝ) * n ≤ ((R * n : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hjU : |(j : ℝ)| ≤ ((R * n : ℕ) : ℝ) / 16 := by
    have h := Nat.mul_le_mul_right n hR
    have h' : (16 : ℝ) * ((R₀ * n : ℕ) : ℝ) ≤ ((R * n : ℕ) : ℝ) := by
      exact_mod_cast (show 16 * (R₀ * n) ≤ R * n by simpa [Nat.mul_assoc] using h)
    linarith
  have hLU : max (n : ℝ) |(j : ℝ)| < ((R * n : ℕ) : ℝ) :=
    (max_le hbU hjU).trans_lt (by linarith)
  let A : ℝ := c * ((R * n : ℕ) : ℝ) * sqrt ((R * n : ℕ) : ℝ) / 8 *
    exp (4 * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * ((R * n : ℕ) : ℝ)))
  let Nminus : ℝ := B * (1 + ((R * s ^ 2 * n : ℕ) : ℝ)) ^ p *
    exp (C_N * sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * (n : ℝ)))
  have hreserve : 1 / 2 < initialCellVariationReserve
      (rootCoord |(j : ℝ)| (max (n : ℝ) |(j : ℝ)|))
      (rootCoord |(j : ℝ)| ((R * n : ℕ) : ℝ)) A Nminus (R * s * n) := by
    apply (hn₁ n ((le_max_left _ _).trans hn) _ _ A Nminus
      (initialCell_density_length_lower (abs_nonneg _) hU1 hjU hbU hc.le) le_rfl).2
  have hupper := initialCell_coordinate_density_lower_of_edge_exponential j
    (Nat.cast_nonneg (R * s ^ 2 * n)) hUpos hjU hbU
    (show ((R * n : ℕ) : ℝ) ≤ ((R * n : ℕ) : ℝ) + 1 by linarith) hc.le q hbound
  have hlarge : 2 / c < ((R * n : ℕ) : ℝ) := by
    have hn₂n : (n₂ : ℝ) ≤ n := by exact_mod_cast (le_max_right n₁ n₂).trans hn
    have hnU : (n : ℝ) ≤ ((R * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left n hR1
    exact ((le_max_right _ _).trans_lt hn₂).trans_le (hn₂n.trans hnU)
  have hterminal : 1 < ∫ E in Ioo ((R * n : ℕ) : ℝ) (((R * n : ℕ) : ℝ) + 1),
      q E ∂referenceMeasure j := by
    apply initialReferenceCell_terminal_mass_gt_one j
      (Nat.cast_nonneg (R * s ^ 2 * n)) hU1 hjU hc hlarge q
      (hq.mono_set (Ioo_subset_Ioo hLU.le le_rfl))
    intro E hE
    exact hbound E ⟨(by linarith [hE.1]), hE.2⟩
  exact nonempty_initialReferenceCell_of_reserve j (A := A) (Nminus := Nminus)
    (le_max_right _ _) hLU (by dsimp [A]; positivity) q hq hnegative hupper hterminal hreserve

end GapFamily.Construction
