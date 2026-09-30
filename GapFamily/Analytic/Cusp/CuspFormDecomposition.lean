import GapFamily.Analytic.Cusp.Scalar.CuspScalarFormLift
import GapFamily.Analytic.Cusp.Fourier.CuspAverageTraceZero

/-!
# The actual bounded three-part decomposition of the modular form domain

The boundary trace is removed first. The scalar lift then separates the
zero-trace vector into its genuine scalar cusp part and its zero-average
part. All three coordinate maps are bounded in the actual form norm.
The constant summand is a trace complement, without mass orthogonality.
-/

noncomputable section
namespace GapFamily.Analytic
open ModularGradient

theorem mem_cuspMeanZeroForm_iff_scalarProjection_eq_zero (u : FormDomain) :
    u ∈ cuspMeanZeroForm ↔ cuspScalarProjection (formEmbedding u) = 0 := by
  constructor
  · intro hu
    exact cuspScalarProjection_meanZeroCuspEmbedding ⟨u, hu⟩
  · intro hu
    apply (mem_cuspMeanZeroForm u).mpr
    have h := congrArg (cuspRestrict 1) hu
    simpa only [cuspScalarProjection_apply, cuspRestrict_zeroExtend, map_zero] using h

@[simp] theorem cuspScalarFormLift_scalar (w : cuspScalarForm) :
    cuspScalarFormLift (w : FormDomain) = w := by
  apply formEmbedding_injective
  rw [cuspScalarFormLift_embedding_of_trace_eq_zero _ (cuspScalarForm_trace w)]
  exact cuspScalarProjection_formEmbedding w

@[simp] theorem cuspScalarFormLift_meanZero (v : cuspMeanZeroForm) :
    cuspScalarFormLift (v : FormDomain) = 0 := by
  apply formEmbedding_injective
  rw [map_zero, cuspScalarFormLift_embedding_of_trace_eq_zero _ (cuspAverageTrace_eq_zero v)]
  exact cuspScalarProjection_meanZeroCuspEmbedding v

@[simp] theorem cuspTraceFree_constant :
    cuspTraceFree (coreForm (constantCore 1)) = 0 := by
  simp only [cuspTraceFree_apply, cuspAverageTrace_constantCore, one_smul, sub_self]

@[simp] theorem cuspScalarFormLift_constant :
    cuspScalarFormLift (coreForm (constantCore 1)) = 0 := by
  apply formEmbedding_injective
  rw [cuspScalarFormLift_embedding, cuspTraceFree_constant, map_zero, map_zero]

theorem cuspTraceFree_sub_scalarLift_mem (u : FormDomain) :
    cuspTraceFree u - cuspScalarFormLift u ∈ cuspMeanZeroForm := by
  apply (mem_cuspMeanZeroForm_iff_scalarProjection_eq_zero _).mpr
  rw [map_sub, map_sub, cuspScalarFormLift_embedding, cuspScalarProjection_idempotent,
    sub_self]

/-- The bounded coordinate in the actual zero-average cusp form space. -/
def cuspMeanZeroFormPart : FormDomain →L[ℂ] cuspMeanZeroForm :=
  (cuspTraceFree - cuspScalarFormLift).codRestrict cuspMeanZeroForm
    cuspTraceFree_sub_scalarLift_mem

/-- The bounded coordinate in the actual closed scalar cusp form space. -/
def cuspScalarFormPart : FormDomain →L[ℂ] cuspScalarForm :=
  cuspScalarFormLift.codRestrict cuspScalarForm cuspScalarFormLift_mem

@[simp] theorem cuspMeanZeroFormPart_coe (u : FormDomain) :
    (cuspMeanZeroFormPart u : FormDomain) = cuspTraceFree u - cuspScalarFormLift u := rfl

@[simp] theorem cuspScalarFormPart_coe (u : FormDomain) :
    (cuspScalarFormPart u : FormDomain) = cuspScalarFormLift u := rfl

theorem cuspForm_reconstruct (u : FormDomain) :
    (cuspMeanZeroFormPart u : FormDomain) + (cuspScalarFormPart u : FormDomain) +
      cuspAverageTrace u • coreForm (constantCore 1) = u := by
  simp only [cuspMeanZeroFormPart_coe, cuspScalarFormPart_coe, cuspTraceFree_apply]
  abel

@[simp] theorem cuspMeanZeroFormPart_meanZero (v : cuspMeanZeroForm) :
    cuspMeanZeroFormPart (v : FormDomain) = v := by
  apply Subtype.ext
  simp only [cuspMeanZeroFormPart_coe, cuspTraceFree_eq_self (cuspAverageTrace_eq_zero v),
    cuspScalarFormLift_meanZero, sub_zero]

@[simp] theorem cuspMeanZeroFormPart_scalar (w : cuspScalarForm) :
    cuspMeanZeroFormPart (w : FormDomain) = 0 := by
  apply Subtype.ext
  simp only [cuspMeanZeroFormPart_coe, cuspTraceFree_eq_self (cuspScalarForm_trace w),
    cuspScalarFormLift_scalar, sub_self, ZeroMemClass.coe_zero]

@[simp] theorem cuspMeanZeroFormPart_constant :
    cuspMeanZeroFormPart (coreForm (constantCore 1)) = 0 := by
  apply Subtype.ext
  simp only [cuspMeanZeroFormPart_coe, cuspTraceFree_constant, cuspScalarFormLift_constant,
    sub_self, ZeroMemClass.coe_zero]

@[simp] theorem cuspScalarFormPart_meanZero (v : cuspMeanZeroForm) :
    cuspScalarFormPart (v : FormDomain) = 0 := by
  apply Subtype.ext
  exact cuspScalarFormLift_meanZero v

@[simp] theorem cuspScalarFormPart_scalar (w : cuspScalarForm) :
    cuspScalarFormPart (w : FormDomain) = w := by
  apply Subtype.ext
  exact cuspScalarFormLift_scalar w

@[simp] theorem cuspScalarFormPart_constant :
    cuspScalarFormPart (coreForm (constantCore 1)) = 0 := by
  apply Subtype.ext
  exact cuspScalarFormLift_constant

/-- The bounded three coordinates, using the literal boundary trace. -/
def cuspFormCoordinates : FormDomain →L[ℂ] (cuspMeanZeroForm × cuspScalarForm) × ℂ :=
  (cuspMeanZeroFormPart.prod cuspScalarFormPart).prod cuspAverageTrace

@[simp] theorem cuspFormCoordinates_apply (u : FormDomain) :
    cuspFormCoordinates u = ((cuspMeanZeroFormPart u, cuspScalarFormPart u),
      cuspAverageTrace u) := rfl

/-- Assembly of the two actual cusp subspaces and the genuine constant core. -/
def cuspFormAssembly : (cuspMeanZeroForm × cuspScalarForm) × ℂ →L[ℂ] FormDomain where
  toFun p := (p.1.1 : FormDomain) + (p.1.2 : FormDomain) +
    p.2 • coreForm (constantCore 1)
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, AddMemClass.coe_add, add_smul]; abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, smul_add, smul_smul,
      RingHom.id_apply, smul_eq_mul]
  cont := by fun_prop

@[simp] theorem cuspFormAssembly_apply (p : (cuspMeanZeroForm × cuspScalarForm) × ℂ) :
    cuspFormAssembly p = (p.1.1 : FormDomain) + (p.1.2 : FormDomain) +
      p.2 • coreForm (constantCore 1) := rfl

@[simp] theorem cuspFormAssembly_coordinates (u : FormDomain) :
    cuspFormAssembly (cuspFormCoordinates u) = u := cuspForm_reconstruct u

@[simp] theorem cuspFormCoordinates_assembly (p : (cuspMeanZeroForm × cuspScalarForm) × ℂ) :
    cuspFormCoordinates (cuspFormAssembly p) = p := by
  rcases p with ⟨⟨v, w⟩, c⟩
  simp only [cuspFormCoordinates_apply, cuspFormAssembly_apply, map_add, map_smul,
    cuspMeanZeroFormPart_meanZero, cuspMeanZeroFormPart_scalar, cuspMeanZeroFormPart_constant,
    cuspScalarFormPart_meanZero, cuspScalarFormPart_scalar, cuspScalarFormPart_constant,
    cuspAverageTrace_eq_zero, cuspScalarForm_trace, cuspAverageTrace_constantCore,
    Prod.mk_add_mk, Prod.smul_mk, add_zero, zero_add, smul_zero, smul_eq_mul, mul_one]

/-- The actual form domain is continuously linearly equivalent to the
zero-average form space, the scalar cusp form space, and one constant coordinate. -/
def cuspFormDecomposition : FormDomain ≃L[ℂ] (cuspMeanZeroForm × cuspScalarForm) × ℂ where
  toLinearMap := cuspFormCoordinates.toLinearMap
  invFun := cuspFormAssembly
  left_inv := cuspFormAssembly_coordinates
  right_inv := cuspFormCoordinates_assembly
  continuous_toFun := cuspFormCoordinates.continuous
  continuous_invFun := cuspFormAssembly.continuous

@[simp] theorem cuspFormDecomposition_apply (u : FormDomain) :
    cuspFormDecomposition u = ((cuspMeanZeroFormPart u, cuspScalarFormPart u),
      cuspAverageTrace u) := rfl

@[simp] theorem cuspFormDecomposition_symm_apply (p : (cuspMeanZeroForm × cuspScalarForm) × ℂ) :
    cuspFormDecomposition.symm p = (p.1.1 : FormDomain) + (p.1.2 : FormDomain) +
      p.2 • coreForm (constantCore 1) := rfl

/-- Every form vector has exactly one decomposition into these actual subspaces. -/
theorem existsUnique_cuspForm_decomposition (u : FormDomain) :
    ∃! p : (cuspMeanZeroForm × cuspScalarForm) × ℂ,
      (p.1.1 : FormDomain) + (p.1.2 : FormDomain) + p.2 • coreForm (constantCore 1) = u := by
  refine ⟨cuspFormCoordinates u, cuspForm_reconstruct u, ?_⟩
  intro p hp
  have h := congrArg cuspFormCoordinates hp
  exact (cuspFormCoordinates_assembly p).symm.trans h

end GapFamily.Analytic
