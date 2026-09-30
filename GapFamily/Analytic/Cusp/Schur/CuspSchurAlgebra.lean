import GapFamily.Analytic.Cusp.Schur.CuspSchurForm
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroPencilWeak
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroPencilRegular

/-!
# Literal Schur gluing in the actual form domain

The constrained response is the actual pencil solution. Scalar-response
equations and uniqueness remain separate explicit premises in this algebraic
module. The constant test gives the literal denominator with mass pi/3.
Actual form energy proves its nonvanishing off the nonnegative real ray.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchur
open ModularGradient

abbrev constantForm : FormDomain := coreForm (constantCore 1)

/-- Sum of the actual constrained response and an explicitly supplied scalar response. -/
def zeroTraceResponse (z : ℂ) (W : ModularHilbert →L[ℂ] cuspScalarForm) :
    ModularHilbert →L[ℂ] FormDomain :=
  cuspMeanZeroForm.subtypeL.comp (cuspMeanZeroPencilSolution z) +
    cuspScalarForm.subtypeL.comp W

@[simp] theorem zeroTraceResponse_apply (z : ℂ)
    (W : ModularHilbert →L[ℂ] cuspScalarForm) (f : ModularHilbert) :
    zeroTraceResponse z W f = (cuspMeanZeroPencilSolution z f : FormDomain) +
      (W f : FormDomain) := rfl

@[simp] theorem zeroTraceResponse_trace (z : ℂ)
    (W : ModularHilbert →L[ℂ] cuspScalarForm) (f : ModularHilbert) :
    cuspAverageTrace (zeroTraceResponse z W f) = 0 := by
  simp only [zeroTraceResponse_apply, map_add, cuspAverageTrace_eq_zero,
    cuspScalarForm_trace, add_zero]

theorem formPairing_meanZero_response {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (W : ModularHilbert →L[ℂ] cuspScalarForm) (f : ModularHilbert)
    (v : cuspMeanZeroForm) :
    formPairing z v (zeroTraceResponse z W f) = inner ℂ (formEmbedding v) f := by
  rw [zeroTraceResponse_apply, formPairing_add_right, formPairing_meanZero_scalar, add_zero]
  exact cuspMeanZeroPencilSolution_equation hz f v

theorem formPairing_scalar_response (z : ℂ)
    (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (hW : ∀ (f : ModularHilbert) (w : cuspScalarForm),
      formPairing z w (W f) = inner ℂ (formEmbedding w) f)
    (f : ModularHilbert) (w : cuspScalarForm) :
    formPairing z w (zeroTraceResponse z W f) = inner ℂ (formEmbedding w) f := by
  rw [zeroTraceResponse_apply, formPairing_add_right, formPairing_scalar_meanZero, zero_add]
  exact hW f w

def schurDenominator (z : ℂ) (W : ModularHilbert →L[ℂ] cuspScalarForm) : ℂ :=
  -z * inner ℂ modularConstant modularConstant -
    z ^ 2 * inner ℂ modularConstant (formEmbedding (zeroTraceResponse z W modularConstant))

theorem schurDenominator_normalization (z : ℂ)
    (W : ModularHilbert →L[ℂ] cuspScalarForm) :
    schurDenominator z W = -z * ((Real.pi / 3 : ℝ) : ℂ) -
      z ^ 2 * inner ℂ modularConstant (formEmbedding (zeroTraceResponse z W modularConstant)) := by
  rw [schurDenominator, modularConstant_inner_self, modularMeasure_real_univ]

def schurNumerator (z : ℂ) (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (f : ModularHilbert) : ℂ :=
  inner ℂ modularConstant f +
    z * inner ℂ modularConstant (formEmbedding (zeroTraceResponse z W f))

def schurVector (z : ℂ) (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (f : ModularHilbert) (c : ℂ) : FormDomain :=
  zeroTraceResponse z W f + c •
    (constantForm + z • zeroTraceResponse z W modularConstant)

@[simp] theorem schurVector_trace (z : ℂ)
    (W : ModularHilbert →L[ℂ] cuspScalarForm) (f : ModularHilbert) (c : ℂ) :
    cuspAverageTrace (schurVector z W f c) = c := by
  simp only [schurVector, map_add, map_smul, zeroTraceResponse_trace,
    constantForm, cuspAverageTrace_constantCore, smul_eq_mul, mul_zero, add_zero, mul_one, zero_add]

theorem schurVector_meanZero_equation {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (W : ModularHilbert →L[ℂ] cuspScalarForm) (f : ModularHilbert) (c : ℂ)
    (v : cuspMeanZeroForm) :
    formPairing z v (schurVector z W f c) = inner ℂ (formEmbedding v) f := by
  simp only [schurVector, formPairing_add_right, formPairing_smul_right,
    formPairing_meanZero_response hz, constantForm, formPairing_constant_right]
  ring

theorem schurVector_scalar_equation (z : ℂ)
    (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (hW : ∀ (f : ModularHilbert) (w : cuspScalarForm),
      formPairing z w (W f) = inner ℂ (formEmbedding w) f)
    (f : ModularHilbert) (c : ℂ) (w : cuspScalarForm) :
    formPairing z w (schurVector z W f c) = inner ℂ (formEmbedding w) f := by
  simp only [schurVector, formPairing_add_right, formPairing_smul_right,
    formPairing_scalar_response z W hW, constantForm, formPairing_constant_right]
  ring

theorem schurVector_constant_equation_iff (z : ℂ)
    (W : ModularHilbert →L[ℂ] cuspScalarForm) (f : ModularHilbert) (c : ℂ) :
    formPairing z constantForm (schurVector z W f c) = inner ℂ modularConstant f ↔
      schurDenominator z W * c = schurNumerator z W f := by
  have h : formPairing z constantForm (schurVector z W f c) - inner ℂ modularConstant f =
      schurDenominator z W * c - schurNumerator z W f := by
    simp only [constantForm, formPairing_constant_left, schurVector, map_add, map_smul,
      inner_add_right, inner_smul_right, formEmbedding_coreForm, value_constantCore_one,
      schurDenominator, schurNumerator]
    ring
  rw [← sub_eq_zero, h, sub_eq_zero]

/-- The actual V-coordinate of any full weak solution is forced by the actual pencil. -/
theorem meanZero_coordinate_of_weak {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (f : ModularHilbert) (u : FormDomain)
    (hu : ∀ t : FormDomain, formPairing z t u = inner ℂ (formEmbedding t) f) :
    cuspMeanZeroFormPart u = cuspMeanZeroPencilSolution z
      (f + (z * cuspAverageTrace u) • modularConstant) := by
  apply cuspMeanZeroPencilSolution_unique hz
  intro v
  change formPairing z v (cuspMeanZeroFormPart u) =
    inner ℂ (formEmbedding v) (f + (z * cuspAverageTrace u) • modularConstant)
  have h := hu (v : FormDomain)
  rw [← cuspForm_reconstruct u, formPairing_add_right, formPairing_add_right,
    formPairing_meanZero_scalar, formPairing_smul_right, formPairing_constant_right] at h
  rw [inner_add_right, inner_smul_right]
  linear_combination h

/-- The W-coordinate is forced only under the explicitly stated scalar uniqueness premise. -/
theorem scalar_coordinate_of_weak (z : ℂ)
    (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (hWU : ∀ (f : ModularHilbert) (u : cuspScalarForm),
      (∀ w : cuspScalarForm, formPairing z w u = inner ℂ (formEmbedding w) f) → u = W f)
    (f : ModularHilbert) (u : FormDomain)
    (hu : ∀ t : FormDomain, formPairing z t u = inner ℂ (formEmbedding t) f) :
    cuspScalarFormPart u = W (f + (z * cuspAverageTrace u) • modularConstant) := by
  apply hWU
  intro w
  have h := hu (w : FormDomain)
  rw [← cuspForm_reconstruct u, formPairing_add_right, formPairing_add_right,
    formPairing_scalar_meanZero, formPairing_smul_right, formPairing_constant_right] at h
  rw [inner_add_right, inner_smul_right]
  linear_combination h

/-- Every full weak solution has the literal constant-coordinate Schur form. -/
theorem eq_schurVector_of_weak {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (hWU : ∀ (f : ModularHilbert) (u : cuspScalarForm),
      (∀ w : cuspScalarForm, formPairing z w u = inner ℂ (formEmbedding w) f) → u = W f)
    (f : ModularHilbert) (u : FormDomain)
    (hu : ∀ t : FormDomain, formPairing z t u = inner ℂ (formEmbedding t) f) :
    u = schurVector z W f (cuspAverageTrace u) := by
  conv_lhs => rw [← cuspForm_reconstruct u,
    meanZero_coordinate_of_weak hz f u hu, scalar_coordinate_of_weak z W hWU f u hu]
  change zeroTraceResponse z W (f + (z * cuspAverageTrace u) • modularConstant) +
    cuspAverageTrace u • constantForm = _
  rw [map_add, map_smul]
  simp only [schurVector, smul_add, smul_smul]
  rw [mul_comm z (cuspAverageTrace u)]
  abel


open ModularGradient

/-- Actual subspace response identities reduce the full equation to one scalar equation. -/
theorem schurVector_equation_iff {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (hW : ∀ (f : ModularHilbert) (w : cuspScalarForm),
      formPairing z w (W f) = inner ℂ (formEmbedding w) f)
    (f : ModularHilbert) (c : ℂ) :
    (∀ t : FormDomain, formPairing z t (schurVector z W f c) =
      inner ℂ (formEmbedding t) f) ↔
      schurDenominator z W * c = schurNumerator z W f := by
  constructor
  · intro h
    apply (schurVector_constant_equation_iff z W f c).mp
    simpa only [constantForm, formEmbedding_coreForm, value_constantCore_one] using
      h constantForm
  · intro hc
    apply formPairing_eq_of_tests
    · exact schurVector_meanZero_equation hz W f c
    · exact schurVector_scalar_equation z W hW f c
    · exact (schurVector_constant_equation_iff z W f c).mpr hc

/-- Any full weak solution satisfies the literal constant-coordinate equation. -/
theorem schurDenominator_trace_of_weak {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (hWU : ∀ (f : ModularHilbert) (u : cuspScalarForm),
      (∀ w : cuspScalarForm, formPairing z w u = inner ℂ (formEmbedding w) f) → u = W f)
    (f : ModularHilbert) (u : FormDomain)
    (hu : ∀ t : FormDomain, formPairing z t u = inner ℂ (formEmbedding t) f) :
    schurDenominator z W * cuspAverageTrace u = schurNumerator z W f := by
  apply (schurVector_constant_equation_iff z W f (cuspAverageTrace u)).mp
  rw [← eq_schurVector_of_weak hz W hWU f u hu]
  simpa only [constantForm, formEmbedding_coreForm, value_constantCore_one] using hu constantForm

/-- Conditional full-form gluing: scalar existence and uniqueness are explicit premises. -/
theorem existsUnique_full_weak_of_schur {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (hW : ∀ (f : ModularHilbert) (w : cuspScalarForm),
      formPairing z w (W f) = inner ℂ (formEmbedding w) f)
    (hWU : ∀ (f : ModularHilbert) (u : cuspScalarForm),
      (∀ w : cuspScalarForm, formPairing z w u = inner ℂ (formEmbedding w) f) → u = W f)
    (hD : schurDenominator z W ≠ 0) (f : ModularHilbert) :
    ∃! u : FormDomain, ∀ t : FormDomain,
      formPairing z t u = inner ℂ (formEmbedding t) f := by
  refine ⟨schurVector z W f (schurNumerator z W f / schurDenominator z W), ?_, ?_⟩
  · apply (schurVector_equation_iff hz W hW f _).mpr
    field_simp [hD]
  · intro u hu
    have hc := schurDenominator_trace_of_weak hz W hWU f u hu
    have he : cuspAverageTrace u = schurNumerator z W f / schurDenominator z W := by
      apply (eq_div_iff hD).mpr
      simpa only [mul_comm] using hc
    rw [eq_schurVector_of_weak hz W hWU f u hu, he]

/-- The explicitly constructed Schur numerator is a bounded source functional. -/
def schurNumeratorMap (z : ℂ) (W : ModularHilbert →L[ℂ] cuspScalarForm) :
    ModularHilbert →L[ℂ] ℂ :=
  innerSL ℂ modularConstant + z • ((innerSL ℂ modularConstant).comp
    (formEmbedding.comp (zeroTraceResponse z W)))

@[simp] theorem schurNumeratorMap_apply (z : ℂ)
    (W : ModularHilbert →L[ℂ] cuspScalarForm) (f : ModularHilbert) :
    schurNumeratorMap z W f = schurNumerator z W f := rfl

/-- A bounded candidate source map; it solves the equation only under the displayed
scalar response and nonzero-denominator hypotheses below. -/
def schurSolution (z : ℂ) (W : ModularHilbert →L[ℂ] cuspScalarForm) :
    ModularHilbert →L[ℂ] FormDomain :=
  zeroTraceResponse z W + ((schurDenominator z W)⁻¹ • schurNumeratorMap z W).smulRight
    (constantForm + z • zeroTraceResponse z W modularConstant)

@[simp] theorem schurSolution_apply (z : ℂ)
    (W : ModularHilbert →L[ℂ] cuspScalarForm) (f : ModularHilbert) :
    schurSolution z W f =
      schurVector z W f (schurNumerator z W f / schurDenominator z W) := by
  change zeroTraceResponse z W f +
    ((schurDenominator z W)⁻¹ * schurNumerator z W f) •
      (constantForm + z • zeroTraceResponse z W modularConstant) = _
  simp only [schurVector, div_eq_mul_inv, mul_comm]

theorem schurSolution_equation {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (hW : ∀ (f : ModularHilbert) (w : cuspScalarForm),
      formPairing z w (W f) = inner ℂ (formEmbedding w) f)
    (hD : schurDenominator z W ≠ 0) (f : ModularHilbert) (t : FormDomain) :
    formPairing z t (schurSolution z W f) = inner ℂ (formEmbedding t) f := by
  rw [schurSolution_apply]
  apply (schurVector_equation_iff hz W hW f _).mpr ?_ t
  field_simp [hD]

theorem schurSolution_unique {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (hWU : ∀ (f : ModularHilbert) (u : cuspScalarForm),
      (∀ w : cuspScalarForm, formPairing z w u = inner ℂ (formEmbedding w) f) → u = W f)
    (hD : schurDenominator z W ≠ 0) (f : ModularHilbert) (u : FormDomain)
    (hu : ∀ t : FormDomain, formPairing z t u = inner ℂ (formEmbedding t) f) :
    u = schurSolution z W f := by
  have hc := schurDenominator_trace_of_weak hz W hWU f u hu
  have he : cuspAverageTrace u = schurNumerator z W f / schurDenominator z W := by
    apply (eq_div_iff hD).mpr
    simpa only [mul_comm] using hc
  rw [schurSolution_apply, eq_schurVector_of_weak hz W hWU f u hu, he]


open ModularGradient

/-- Actual full-form energy excludes homogeneous nonreal or negative-real parameters. -/
theorem eq_zero_of_formPairing_self (z : ℂ) (u : FormDomain)
    (hregion : z.im ≠ 0 ∨ z.re < 0) (hu : formPairing z u u = 0) : u = 0 := by
  have h : inner ℂ (formGradient u) (formGradient u) =
      z * inner ℂ (formEmbedding u) (formEmbedding u) := sub_eq_zero.mp hu
  have hiD : (inner ℂ (formGradient u) (formGradient u)).im = 0 :=
    inner_self_im (𝕜 := ℂ) (formGradient u)
  have hiV : (inner ℂ (formEmbedding u) (formEmbedding u)).im = 0 :=
    inner_self_im (𝕜 := ℂ) (formEmbedding u)
  have hrD : (inner ℂ (formGradient u) (formGradient u)).re = ‖formGradient u‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (formGradient u)
  have hrV : (inner ℂ (formEmbedding u) (formEmbedding u)).re = ‖formEmbedding u‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (formEmbedding u)
  have hmass : ‖formEmbedding u‖ ^ 2 = 0 := by
    rcases hregion with him | hre
    · have hi : z.im * ‖formEmbedding u‖ ^ 2 = 0 := by
        simpa only [Complex.mul_im, hiD, hiV, hrV,
          mul_zero, zero_add] using (congrArg Complex.im h).symm
      exact (mul_eq_zero.mp hi).resolve_left him
    · have hr : ‖formGradient u‖ ^ 2 = z.re * ‖formEmbedding u‖ ^ 2 := by
        simpa only [Complex.mul_re, hiV, hrD, hrV,
          mul_zero, sub_zero] using congrArg Complex.re h
      have hm : 0 ≤ ‖formEmbedding u‖ ^ 2 := sq_nonneg _
      by_contra hn
      have hpos : 0 < ‖formEmbedding u‖ ^ 2 := lt_of_le_of_ne hm (Ne.symm hn)
      have hneg := mul_neg_of_neg_of_pos hre hpos
      rw [← hr] at hneg
      exact (sq_nonneg _).not_gt hneg
  apply formEmbedding_injective
  rw [map_zero]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hmass)

/-- Nonvanishing follows from actual form energy, not any unproved threshold assertion. -/
theorem schurDenominator_ne_zero_of_physical {z : ℂ}
    (hz : IsUnit (cuspMeanZeroPencil z))
    (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (hW : ∀ (f : ModularHilbert) (w : cuspScalarForm),
      formPairing z w (W f) = inner ℂ (formEmbedding w) f)
    (hregion : z.im ≠ 0 ∨ z.re < 0) : schurDenominator z W ≠ 0 := by
  intro hD
  have hu : ∀ t : FormDomain, formPairing z t (schurVector z W 0 1) =
      inner ℂ (formEmbedding t) 0 := by
    apply (schurVector_equation_iff hz W hW 0 1).mpr
    simp only [hD, zero_mul, schurNumerator, map_zero, inner_zero_right, mul_zero, add_zero]
  have hzero : schurVector z W 0 1 = 0 :=
    eq_zero_of_formPairing_self z _ hregion (by simpa only [inner_zero_right] using
      (hu (schurVector z W 0 1)))
  have ht := schurVector_trace z W 0 1
  rw [hzero, map_zero] at ht
  exact zero_ne_one ht

/-- The actual V regularity discharges its premise on the physical nonreal/negative region.
The two explicit W-response hypotheses remain visible. -/
theorem existsUnique_full_weak_of_physical (z : ℂ)
    (W : ModularHilbert →L[ℂ] cuspScalarForm)
    (hW : ∀ (f : ModularHilbert) (w : cuspScalarForm),
      formPairing z w (W f) = inner ℂ (formEmbedding w) f)
    (hWU : ∀ (f : ModularHilbert) (u : cuspScalarForm),
      (∀ w : cuspScalarForm, formPairing z w u = inner ℂ (formEmbedding w) f) → u = W f)
    (hregion : z.im ≠ 0 ∨ z.re < 0) (f : ModularHilbert) :
    ∃! u : FormDomain, ∀ t : FormDomain,
      formPairing z t u = inner ℂ (formEmbedding t) f := by
  have hz : IsUnit (cuspMeanZeroPencil z) := hregion.elim
    (cuspMeanZeroPencil_isUnit_of_im_ne_zero z)
    (fun h => cuspMeanZeroPencil_isUnit_of_re_nonpos z h.le)
  exact existsUnique_full_weak_of_schur hz W hW hWU
    (schurDenominator_ne_zero_of_physical hz W hW hregion) f

end GapFamily.Analytic.CuspSchur
