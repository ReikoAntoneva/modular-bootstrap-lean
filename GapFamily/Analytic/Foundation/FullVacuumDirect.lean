import GapFamily.Character
import GapFamily.Analytic.Foundation.FullVacuumFourier

/-!
# The direct vacuum and the prescribed character

The four signed direct seeds are exactly the numerator of the single vacuum
character, including its two null subtractions and their common descendant.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped UpperHalfPlane

/-- The four signed direct terms in the vacuum completion, before induced output. -/
def vacuumDirectRow (a y x : ℝ) : ℂ :=
  (Real.sqrt y : ℂ) * Complex.exp (-2 * (Real.pi : ℂ) * (-a) * (y : ℂ)) -
    (Real.sqrt y : ℂ) * Complex.exp (-2 * (Real.pi : ℂ) * (1 - a) * (y : ℂ)) *
      cuspFourierMode 1 x -
    (Real.sqrt y : ℂ) * Complex.exp (-2 * (Real.pi : ℂ) * (1 - a) * (y : ℂ)) *
      cuspFourierMode (-1) x +
    (Real.sqrt y : ℂ) * Complex.exp (-2 * (Real.pi : ℂ) * (2 - a) * (y : ℂ))

/-- The prescribed direct vacuum is periodic in the horizontal coordinate. -/
theorem vacuumDirectRow_add_int (a y x : ℝ) (k : ℤ) :
    vacuumDirectRow a y (x + (k : ℝ)) = vacuumDirectRow a y x := by
  simp only [vacuumDirectRow, cuspFourierMode_add_int]

/-- Every direct vacuum row is continuous. -/
theorem continuous_vacuumDirectRow (a y : ℝ) : Continuous (vacuumDirectRow a y) := by
  exact (((continuous_const.sub
    (continuous_const.mul (contDiff_cuspFourierMode 1).continuous)).sub
    (continuous_const.mul (contDiff_cuspFourierMode (-1)).continuous)).add continuous_const)

/-- The actual direct seeds have precisely the prescribed single-vacuum
character numerator and no additional vacuum multiplicity. -/
theorem vacuumDirectRow_eq_vacuumNumerator (c : ℝ) (τ : ℍ) :
    vacuumDirectRow (GapFamily.shift c) τ.im τ.re =
      (Real.sqrt τ.im : ℂ) * GapFamily.vacuumNumerator c τ := by
  let a : ℝ := GapFamily.shift c
  let A : ℂ := Complex.exp (-2 * (Real.pi : ℂ) * (-a) * (τ.im : ℂ))
  let P : ℂ := Complex.exp (-2 * (Real.pi : ℂ) * (1 - a) * (τ.im : ℂ))
  let Q : ℂ := Complex.exp (-2 * (Real.pi : ℂ) * (2 - a) * (τ.im : ℂ))
  have hq : GapFamily.qPower 1 τ =
      Complex.exp (-2 * (Real.pi : ℂ) * (τ.im : ℂ)) * cuspFourierMode 1 τ.re := by
    unfold GapFamily.qPower cuspFourierMode
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hqs : star (GapFamily.qPower 1 τ) =
      Complex.exp (-2 * (Real.pi : ℂ) * (τ.im : ℂ)) * cuspFourierMode (-1) τ.re := by
    unfold GapFamily.qPower cuspFourierMode
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hn : (‖1 - GapFamily.qPower 1 τ‖ : ℂ) ^ 2 =
      (1 - GapFamily.qPower 1 τ) * (1 - star (GapFamily.qPower 1 τ)) := by
    simpa only [Complex.star_def, map_sub, map_one] using
      (Complex.mul_conj' (1 - GapFamily.qPower 1 τ)).symm
  have hA : (Real.exp (2 * Real.pi * τ.im * GapFamily.shift c) : ℂ) = A := by
    rw [Complex.ofReal_exp]
    congr 1
    dsimp [a]
    push_cast
    ring
  have hAP : A * Complex.exp (-2 * (Real.pi : ℂ) * (τ.im : ℂ)) = P := by
    dsimp [A, P]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hp : A * GapFamily.qPower 1 τ = P * cuspFourierMode 1 τ.re := by
    rw [hq, ← mul_assoc, hAP]
  have hm : A * star (GapFamily.qPower 1 τ) = P * cuspFourierMode (-1) τ.re := by
    rw [hqs, ← mul_assoc, hAP]
  have hqprod : A * (GapFamily.qPower 1 τ * star (GapFamily.qPower 1 τ)) = Q := by
    rw [GapFamily.qPower_mul_star]
    dsimp [A, Q]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (Real.sqrt τ.im : ℂ) *
        (A - A * GapFamily.qPower 1 τ - A * star (GapFamily.qPower 1 τ) +
          A * (GapFamily.qPower 1 τ * star (GapFamily.qPower 1 τ))) := by
      rw [hp, hm, hqprod]
      change vacuumDirectRow a τ.im τ.re = _
      dsimp [vacuumDirectRow, A, P, Q]
      ring
    _ = _ := by
      rw [GapFamily.vacuumNumerator, hA, hn]
      ring

end GapFamily.Analytic
