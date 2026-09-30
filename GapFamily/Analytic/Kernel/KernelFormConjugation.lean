import GapFamily.Analytic.Kernel.LowBandOperator

/-! Conjugation of the ordinary integral pairing of a real kernel. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory
open scoped ComplexConjugate

/-- Simultaneous conjugation of the two Hilbert rows conjugates the actual
ordinary kernel pairing when its kernel is real. -/
theorem lowBandKernelPairing_conj_rows (j J : ℤ) (B : ℝ)
    (K : ℝ × ℝ → ℂ) (hK : ∀ p, conj (K p) = K p)
    (f : LowBandRow j B) (g : LowBandRow J B) :
    lowBandKernelPairing j J B K (star f : LowBandRow j B) (star g : LowBandRow J B) =
      conj (lowBandKernelPairing j J B K f g) := by
  rw [lowBandKernelPairing_congr_ae (Lp.coeFn_star f) (Lp.coeFn_star g)]
  unfold lowBandKernelPairing
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    simp only [weakKernelIntegrand, Pi.star_apply, Complex.star_def,
      map_mul, starRingEnd_self_apply, hK]

/-- A one-row version useful for testing an operator against conjugated inputs. -/
theorem lowBandKernelPairing_conj_left (j J : ℤ) (B : ℝ)
    (K : ℝ × ℝ → ℂ) (hK : ∀ p, conj (K p) = K p)
    (f : LowBandRow j B) (g : LowBandRow J B) :
    lowBandKernelPairing j J B K (star f : LowBandRow j B) g =
      conj (lowBandKernelPairing j J B K f (star g : LowBandRow J B)) := by
  simpa only [star_star] using lowBandKernelPairing_conj_rows j J B K hK f (star g)

end GapFamily.Analytic
