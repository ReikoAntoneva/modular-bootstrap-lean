import GapFamily.Analytic.Cusp.CuspFormDecomposition

/-!
# Test-first pairing on the actual modular form domain

The actual three-part form decomposition supplies every test vector. Scalar
multiplication in the first slot is conjugated. The two cusp cross-pairings use
the already proved mass and energy orthogonality.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchur

open ModularGradient

def formPairing (z : ℂ) (t u : FormDomain) : ℂ :=
  inner ℂ (formGradient t) (formGradient u) -
    z * inner ℂ (formEmbedding t) (formEmbedding u)

theorem formPairing_add_left (z : ℂ) (t s u : FormDomain) :
    formPairing z (t + s) u = formPairing z t u + formPairing z s u := by
  simp only [formPairing, map_add, inner_add_left]
  ring

theorem formPairing_smul_left (z c : ℂ) (t u : FormDomain) :
    formPairing z (c • t) u = starRingEnd ℂ c * formPairing z t u := by
  simp only [formPairing, map_smul, inner_smul_left]
  ring

theorem formPairing_add_right (z : ℂ) (t u v : FormDomain) :
    formPairing z t (u + v) = formPairing z t u + formPairing z t v := by
  simp only [formPairing, map_add, inner_add_right]
  ring

theorem formPairing_smul_right (z c : ℂ) (t u : FormDomain) :
    formPairing z t (c • u) = c * formPairing z t u := by
  simp only [formPairing, map_smul, inner_smul_right]
  ring

@[simp] theorem formPairing_zero_left (z : ℂ) (u : FormDomain) :
    formPairing z 0 u = 0 := by
  simp [formPairing]

@[simp] theorem formPairing_zero_right (z : ℂ) (t : FormDomain) :
    formPairing z t 0 = 0 := by
  simp [formPairing]

/-- The actual constant has zero closed gradient and the actual ambient value. -/
theorem formPairing_constant_left (z : ℂ) (u : FormDomain) :
    formPairing z (coreForm (constantCore 1)) u =
      -z * inner ℂ modularConstant (formEmbedding u) := by
  simp only [formPairing, formGradient_coreForm, coreGradient_constantCore,
    inner_zero_left, formEmbedding_coreForm, value_constantCore_one, zero_sub, neg_mul]

theorem formPairing_constant_right (z : ℂ) (t : FormDomain) :
    formPairing z t (coreForm (constantCore 1)) =
      -z * inner ℂ (formEmbedding t) modularConstant := by
  simp only [formPairing, formGradient_coreForm, coreGradient_constantCore,
    inner_zero_right, formEmbedding_coreForm, value_constantCore_one, zero_sub, neg_mul]

theorem formPairing_scalar_meanZero (z : ℂ) (w : cuspScalarForm)
    (v : cuspMeanZeroForm) : formPairing z (w : FormDomain) (v : FormDomain) = 0 := by
  have he : inner ℂ (formGradient (w : FormDomain))
      (formGradient (v : FormDomain)) = 0 := cuspScalarForm_energy_orthogonal w v
  have hm : inner ℂ (formEmbedding (w : FormDomain))
      (formEmbedding (v : FormDomain)) = 0 := cuspScalarForm_mass_orthogonal w v
  simp only [formPairing, he, hm, mul_zero, sub_self]

theorem formPairing_meanZero_scalar (z : ℂ) (v : cuspMeanZeroForm)
    (w : cuspScalarForm) : formPairing z (v : FormDomain) (w : FormDomain) = 0 := by
  have he : inner ℂ (formGradient (w : FormDomain))
      (formGradient (v : FormDomain)) = 0 := cuspScalarForm_energy_orthogonal w v
  have hm : inner ℂ (formEmbedding (w : FormDomain))
      (formEmbedding (v : FormDomain)) = 0 := cuspScalarForm_mass_orthogonal w v
  have he' := inner_eq_zero_symm.mp he
  have hm' := inner_eq_zero_symm.mp hm
  simp only [formPairing, he', hm', mul_zero, sub_self]

/-- Tests in the two actual cusp subspaces and the genuine constant suffice. -/
theorem formPairing_eq_of_tests (z : ℂ) (u : FormDomain) (f : ModularHilbert)
    (hv : ∀ v : cuspMeanZeroForm,
      formPairing z (v : FormDomain) u = inner ℂ (meanZeroCuspEmbedding v) f)
    (hw : ∀ w : cuspScalarForm,
      formPairing z (w : FormDomain) u = inner ℂ (scalarCuspEmbedding w) f)
    (he : formPairing z (coreForm (constantCore 1)) u = inner ℂ modularConstant f)
    (t : FormDomain) :
    formPairing z t u = inner ℂ (formEmbedding t) f := by
  have h :
      formPairing z
        ((cuspMeanZeroFormPart t : FormDomain) + (cuspScalarFormPart t : FormDomain) +
          cuspAverageTrace t • coreForm (constantCore 1)) u =
      inner ℂ
        (formEmbedding
          ((cuspMeanZeroFormPart t : FormDomain) + (cuspScalarFormPart t : FormDomain) +
            cuspAverageTrace t • coreForm (constantCore 1))) f := by
    rw [formPairing_add_left, formPairing_add_left, formPairing_smul_left,
      hv (cuspMeanZeroFormPart t), hw (cuspScalarFormPart t), he]
    simp only [map_add, map_smul, inner_add_left, inner_smul_left,
      meanZeroCuspEmbedding_apply, scalarCuspEmbedding_apply,
      formEmbedding_coreForm, value_constantCore_one]
  simpa only [cuspForm_reconstruct t] using h

/-- The full test-first weak equation is exactly its three actual restrictions. -/
theorem formPairing_eq_iff_tests (z : ℂ) (u : FormDomain) (f : ModularHilbert) :
    (∀ t : FormDomain, formPairing z t u = inner ℂ (formEmbedding t) f) ↔
      (∀ v : cuspMeanZeroForm,
        formPairing z (v : FormDomain) u = inner ℂ (meanZeroCuspEmbedding v) f) ∧
      (∀ w : cuspScalarForm,
        formPairing z (w : FormDomain) u = inner ℂ (scalarCuspEmbedding w) f) ∧
      formPairing z (coreForm (constantCore 1)) u = inner ℂ modularConstant f := by
  constructor
  · intro h
    refine ⟨fun v => h (v : FormDomain), fun w => h (w : FormDomain), ?_⟩
    simpa only [formEmbedding_coreForm, value_constantCore_one] using
      h (coreForm (constantCore 1))
  · rintro ⟨hv, hw, he⟩
    exact formPairing_eq_of_tests z u f hv hw he

end GapFamily.Analytic.CuspSchur
