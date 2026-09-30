import GapFamily.Construction.TailReserve
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# The literal integer degree and charge schedule

The frozen construction uses `M = R * s²`, `a = M * n`, `T = R₀ * n`,
and the natural moment degree `K * (a + m + 1)` on layer `m`. These
identities transfer the real-charge estimates to that integer schedule.
-/

open Filter

namespace GapFamily.Construction

/-- The natural moment degree assigned to the entire integer energy layer. -/
def tailMomentDegree (K a m : ℕ) : ℕ := K * (a + m + 1)

/-- The degree is exactly the source expression, with no rounding. -/
@[simp]
theorem tailMomentDegree_cast (K a m : ℕ) :
    (tailMomentDegree K a m : ℝ) = (K : ℝ) * ((a : ℝ) + (m : ℝ) + 1) := by
  simp [tailMomentDegree]

/-- Lower comparison for every real left endpoint in the integer layer. -/
theorem tailMomentDegree_lower {K a m : ℕ} {L : ℝ} (hL : L < (m : ℝ) + 1) :
    (K : ℝ) * ((a : ℝ) + L) ≤ (tailMomentDegree K a m : ℝ) := by
  rw [tailMomentDegree_cast]
  exact tail_layer_degree_lower (Nat.cast_nonneg K) hL

/-- The upper comparison includes the constant polynomial coordinate. -/
theorem tailMomentDegree_add_one_le {K a m : ℕ} {L : ℝ}
    (ha : 1 ≤ a) (hm : (m : ℝ) ≤ L) :
    (tailMomentDegree K a m : ℝ) + 1 ≤
      (2 * ((K : ℝ) + 1)) * ((a : ℝ) + L) := by
  rw [tailMomentDegree_cast]
  exact tail_layer_degree_upper (Nat.cast_nonneg K) (by exact_mod_cast ha) hm

/-- Both degree comparisons apply throughout the same integer layer. -/
theorem tailMomentDegree_layer_bounds {K a m : ℕ} {L : ℝ}
    (ha : 1 ≤ a) (hm : (m : ℝ) ≤ L) (hL : L < (m : ℝ) + 1) :
    (K : ℝ) * ((a : ℝ) + L) ≤ (tailMomentDegree K a m : ℝ) ∧
      (tailMomentDegree K a m : ℝ) + 1 ≤
        (2 * ((K : ℝ) + 1)) * ((a : ℝ) + L) :=
  ⟨tailMomentDegree_lower hL, tailMomentDegree_add_one_le ha hm⟩

theorem schedule_multiplier_pos {R s : ℕ} (hR : 0 < R) (hs : 0 < s) :
    0 < R * s ^ 2 := mul_pos hR (pow_pos hs _)

/-- The source cutoff is precisely a fixed charge ray when `M > 0`. -/
theorem schedule_cutoff_eq_ray (R₀ M n : ℕ) (hM : 0 < M) :
    ((R₀ * n : ℕ) : ℝ) = ((R₀ : ℝ) / (M : ℝ)) * ((M * n : ℕ) : ℝ) := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  field_simp

theorem schedule_cutoff_ray_pos {R₀ M : ℕ} (hR₀ : 0 < R₀) (hM : 0 < M) :
    0 < (R₀ : ℝ) / (M : ℝ) := by
  exact div_pos (by exact_mod_cast hR₀) (by exact_mod_cast hM)

/-- The actual integer charges tend to infinity in the real parameter space. -/
theorem tendsto_scheduleCharge_atTop (M : ℕ) (hM : 0 < M) :
    Tendsto (fun n : ℕ => ((M * n : ℕ) : ℝ)) atTop atTop := by
  simpa only [Nat.cast_mul] using
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop
      (show 0 < (M : ℝ) by exact_mod_cast hM)

/-- Every fixed real charge threshold is eventually reached by the integer schedule. -/
theorem eventually_scheduleCharge_ge (M : ℕ) (hM : 0 < M) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A ≤ ((M * n : ℕ) : ℝ) :=
  (tendsto_scheduleCharge_atTop M hM).eventually_ge_atTop A

/-- Any proved eventual real-charge assertion transfers to the literal integer schedule. -/
theorem eventually_on_scheduleCharge (M : ℕ) (hM : 0 < M) {P : ℝ → Prop}
    (hP : ∀ᶠ a : ℝ in atTop, P a) :
    ∀ᶠ n : ℕ in atTop, P ((M * n : ℕ) : ℝ) :=
  (tendsto_scheduleCharge_atTop M hM).eventually hP

/-- One real-charge bound uniform above the source ray holds on all scheduled tail layers. -/
theorem eventually_schedule_uniform_tail (R₀ M : ℕ) (hM : 0 < M)
    {P : ℝ → ℝ → Prop}
    (hP : ∀ᶠ a : ℝ in atTop, ∀ L : ℝ, ((R₀ : ℝ) / (M : ℝ)) * a ≤ L → P a L) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, R₀ * n ≤ m →
      ∀ L : ℝ, (m : ℝ) ≤ L → P ((M * n : ℕ) : ℝ) L := by
  filter_upwards [eventually_on_scheduleCharge M hM hP] with n hn
  intro m hm L hL
  apply hn L
  rw [← schedule_cutoff_eq_ray R₀ M n hM]
  exact (show ((R₀ * n : ℕ) : ℝ) ≤ (m : ℝ) by exact_mod_cast hm).trans hL

end GapFamily.Construction
