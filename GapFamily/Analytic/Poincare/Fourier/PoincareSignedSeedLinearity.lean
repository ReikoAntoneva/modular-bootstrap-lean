import GapFamily.Analytic.Foundation.SignedPhysicalSupport
import GapFamily.Analytic.Poincare.Fourier.PoincareThermalOutputMeasure

/-! Ordinary linearity of the actual signed response and thermal output.
Common compact physical support supplies convergence for every additive
identity; the resulting equalities are identities of actual signed measures.
-/

noncomputable section
namespace GapFamily.Analytic

open MeasureTheory Set
open scoped Classical

/-- Addition of compact physical signed inputs commutes with the actual kernel response. -/
theorem correctedSignedRowResponse_add (ν μ : SignedMeasure ℝ) (J j : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ᵐ E ∂μ.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) (e : ℝ) :
    correctedSignedRowResponse (ν + μ) J j e =
      correctedSignedRowResponse ν J j e + correctedSignedRowResponse μ J j e := by
  exact VectorMeasure.integral_add_vectorMeasure
    (correctedSignedRowResponse_integrable ν J j M hν e)
    (correctedSignedRowResponse_integrable μ J j M hμ e)

/-- Subtraction of compact physical signed inputs commutes with the actual kernel response. -/
theorem correctedSignedRowResponse_sub (ν μ : SignedMeasure ℝ) (J j : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ᵐ E ∂μ.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) (e : ℝ) :
    correctedSignedRowResponse (ν - μ) J j e =
      correctedSignedRowResponse ν J j e - correctedSignedRowResponse μ J j e := by
  exact VectorMeasure.integral_sub_vectorMeasure
    (correctedSignedRowResponse_integrable ν J j M hν e)
    (correctedSignedRowResponse_integrable μ J j M hμ e)

theorem correctedSignedRowResponse_smul (ν : SignedMeasure ℝ) (c : ℝ) (J j : ℤ) (e : ℝ) :
    correctedSignedRowResponse (c • ν) J j e = c • correctedSignedRowResponse ν J j e :=
  VectorMeasure.integral_smul_vectorMeasure _ c

theorem correctedSignedRowResponse_neg (ν : SignedMeasure ℝ) (J j : ℤ) (e : ℝ) :
    correctedSignedRowResponse (-ν) J j e = -correctedSignedRowResponse ν J j e :=
  VectorMeasure.integral_neg_vectorMeasure

/-- The direct thermal tilt preserves actual addition of compact physical inputs. -/
theorem thermalSignedInputMeasure_add (ν μ : SignedMeasure ℝ) (J : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ᵐ E ∂μ.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) {t : ℝ} (ht : 0 < t) :
    thermalSignedInputMeasure (ν + μ) t =
      thermalSignedInputMeasure ν t + thermalSignedInputMeasure μ t := by
  ext s hs
  rw [thermalSignedInputMeasure_apply (ν + μ) J M (signedPhysicalSupport_add ν μ J M hν hμ) ht,
    _root_.add_apply, thermalSignedInputMeasure_apply ν J M hν ht,
    thermalSignedInputMeasure_apply μ J M hμ ht, VectorMeasure.restrict_add]
  exact VectorMeasure.integral_add_vectorMeasure
    (signedIntegrable_thermalInput ν J M hν ht).restrict
    (signedIntegrable_thermalInput μ J M hμ ht).restrict

theorem thermalSignedInputMeasure_smul (ν : SignedMeasure ℝ) (c : ℝ) (J : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) {t : ℝ} (ht : 0 < t) :
    thermalSignedInputMeasure (c • ν) t = c • thermalSignedInputMeasure ν t := by
  ext s hs
  rw [thermalSignedInputMeasure_apply (c • ν) J M (signedPhysicalSupport_smul ν J M c hν) ht,
    _root_.smul_apply, thermalSignedInputMeasure_apply ν J M hν ht,
    VectorMeasure.restrict_smul, VectorMeasure.integral_smul_vectorMeasure]

/-- The induced continuum is additive as an ordinary finite signed measure. -/
theorem correctedThermalContinuumMeasure_add (ν μ : SignedMeasure ℝ) (J j : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ᵐ E ∂μ.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) {t : ℝ} (ht : 0 < t) :
    correctedThermalContinuumMeasure (ν + μ) J j t =
      correctedThermalContinuumMeasure ν J j t + correctedThermalContinuumMeasure μ J j t := by
  have hd : correctedThermalRowDensity (ν + μ) J j t =
      correctedThermalRowDensity ν J j t + correctedThermalRowDensity μ J j t := by
    funext e
    simp only [correctedThermalRowDensity, correctedSignedRowResponse_add ν μ J j M hν hμ,
      Complex.add_re, mul_add, Pi.add_apply]
  unfold correctedThermalContinuumMeasure
  rw [hd, withDensityᵥ_add (integrable_correctedThermalRowDensity ν J j M hν ht)
    (integrable_correctedThermalRowDensity μ J j M hμ ht)]

theorem correctedThermalContinuumMeasure_smul (ν : SignedMeasure ℝ) (c : ℝ)
    (J j : ℤ) (t : ℝ) :
    correctedThermalContinuumMeasure (c • ν) J j t =
      c • correctedThermalContinuumMeasure ν J j t := by
  have hd : correctedThermalRowDensity (c • ν) J j t =
      c • correctedThermalRowDensity ν J j t := by
    funext e
    simp only [correctedThermalRowDensity, correctedSignedRowResponse_smul,
      Complex.smul_re, Pi.smul_apply, smul_eq_mul]
    ring
  unfold correctedThermalContinuumMeasure
  rw [hd, withDensityᵥ_smul]

private theorem signedDirac_add (x a b : ℝ) :
    VectorMeasure.dirac x (a + b) = VectorMeasure.dirac x a + VectorMeasure.dirac x b := by
  ext s hs
  by_cases hx : x ∈ s <;> simp [hx, hs]

private theorem signedDirac_smul (x a c : ℝ) :
    VectorMeasure.dirac x (c * a) = c • VectorMeasure.dirac x a := by
  ext s hs
  by_cases hx : x ∈ s <;> simp [hx, hs, smul_eq_mul]

/-- The complete actual thermal output is additive on compact physical inputs. -/
theorem correctedThermalRowOutputMeasure_add (ν μ : SignedMeasure ℝ) (J j : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ᵐ E ∂μ.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) {t : ℝ} (ht : 0 < t) :
    correctedThermalRowOutputMeasure (ν + μ) J j t =
      correctedThermalRowOutputMeasure ν J j t + correctedThermalRowOutputMeasure μ J j t := by
  unfold correctedThermalRowOutputMeasure
  rw [thermalSignedInputMeasure_add ν μ J M hν hμ ht,
    correctedThermalContinuumMeasure_add ν μ J j M hν hμ ht]
  simp only [_root_.add_apply, mul_add, signedDirac_add]
  split_ifs <;> abel

/-- Real scaling commutes with the complete actual thermal output. -/
theorem correctedThermalRowOutputMeasure_smul (ν : SignedMeasure ℝ) (c : ℝ)
    (J j : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) {t : ℝ} (ht : 0 < t) :
    correctedThermalRowOutputMeasure (c • ν) J j t =
      c • correctedThermalRowOutputMeasure ν J j t := by
  unfold correctedThermalRowOutputMeasure
  rw [thermalSignedInputMeasure_smul ν c J M hν ht,
    correctedThermalContinuumMeasure_smul]
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [mul_left_comm, signedDirac_smul]
  split_ifs <;> simp only [smul_add, smul_zero]

theorem correctedThermalRowOutputMeasure_neg (ν : SignedMeasure ℝ)
    (J j : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) {t : ℝ} (ht : 0 < t) :
    correctedThermalRowOutputMeasure (-ν) J j t =
      -correctedThermalRowOutputMeasure ν J j t := by
  have hn (σ : SignedMeasure ℝ) : (-1 : ℝ) • σ = -σ := by
    ext s hs
    change (-1 : ℝ) * σ s = -(σ s)
    ring
  simpa only [hn] using
    correctedThermalRowOutputMeasure_smul ν (-1) J j M hν ht

/-- Subtraction is literal signed-measure subtraction, including the threshold atom. -/
theorem correctedThermalRowOutputMeasure_sub (ν μ : SignedMeasure ℝ) (J j : ℤ) (M : ℝ)
    (hν : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ᵐ E ∂μ.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) {t : ℝ} (ht : 0 < t) :
    correctedThermalRowOutputMeasure (ν - μ) J j t =
      correctedThermalRowOutputMeasure ν J j t - correctedThermalRowOutputMeasure μ J j t := by
  rw [sub_eq_add_neg,
    correctedThermalRowOutputMeasure_add ν (-μ) J j M hν
      (signedPhysicalSupport_neg μ J M hμ) ht,
    correctedThermalRowOutputMeasure_neg μ J j M hμ ht, sub_eq_add_neg]

end GapFamily.Analytic
