import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Genuine L² normalized indicators and their ordinary averaging formulas. -/
noncomputable section
namespace GapFamily.Analytic.L2NormalizedIndicator
open MeasureTheory Set Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def vector (S : Set X) (hS : MeasurableSet S) : Lp ℂ 2 μ :=
  ((memLp_const (μ := μ) (p := 2) (((μ.real S)⁻¹ : ℝ) : ℂ)).indicator hS).toLp _

theorem vector_ae (S : Set X) (hS : MeasurableSet S) :
    vector μ S hS =ᵐ[μ] S.indicator (fun _ => (((μ.real S)⁻¹ : ℝ) : ℂ)) :=
  MemLp.coeFn_toLp _

/-- Pairing against the normalized indicator is exactly an ordinary set average. -/
theorem inner_vector (S : Set X) (hS : MeasurableSet S) (f : Lp ℂ 2 μ) :
    inner ℂ (vector μ S hS) f = ⨍ x in S, f x ∂μ := by
  rw [L2.inner_def]
  calc
    (∫ x, inner ℂ (vector μ S hS x) (f x) ∂μ) =
        ∫ x, S.indicator (fun x => (((μ.real S)⁻¹ : ℝ) : ℂ) * f x) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [vector_ae μ S hS] with x hx
      rw [hx]
      by_cases h : x ∈ S
      · simp only [Set.indicator_of_mem h, RCLike.inner_apply,
          Complex.star_def, Complex.conj_ofReal]
        ring
      · simp [Set.indicator_of_notMem h]
    _ = _ := by
      rw [integral_indicator hS, integral_const_mul, setAverage_eq]
      rfl

/-- Bochner integration against the same actual vector gives the same normalized
source average, in any complete complex normed space. -/
theorem integral_vector_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (S : Set X) (hS : MeasurableSet S) (f : X → E) :
    (∫ x, vector μ S hS x • f x ∂μ) = ⨍ x in S, f x ∂μ := by
  calc
    (∫ x, vector μ S hS x • f x ∂μ) =
        ∫ x, S.indicator (fun x => (((μ.real S)⁻¹ : ℝ) : ℂ) • f x) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [vector_ae μ S hS] with x hx
      rw [hx]
      by_cases h : x ∈ S <;> simp [h]
    _ = _ := by
      rw [integral_indicator hS, integral_smul, setAverage_eq]
      exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

end GapFamily.Analytic.L2NormalizedIndicator
