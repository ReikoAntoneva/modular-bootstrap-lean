import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroGap
import GapFamily.Analytic.Cusp.Scalar.CuspScalarQuarter
import GapFamily.Analytic.Modular.ModularLaplacian

/-!
# The actual modular quarter bound

The genuine trace-free V/W decomposition gives a quarter form bound on the
ordinary constant-orthogonal subspace. The actual operator energy inherits
it and excludes positive eigenvalues below one quarter. The endpoint at
one quarter and general resolvent existence are separate statements.
-/

noncomputable section
namespace GapFamily.Analytic
open ModularGradient

/-- The actual trace-removed form has the sharp scalar-channel quarter bound. -/
theorem cuspTraceFree_mass_le_four_energy (u : FormDomain) :
    ‖formEmbedding (cuspTraceFree u)‖ ^ 2 ≤ 4 * ‖formGradient u‖ ^ 2 := by
  let v := cuspMeanZeroFormPart u
  let w := cuspScalarFormPart u
  have hsum : (w : FormDomain) + (v : FormDomain) = cuspTraceFree u := by
    simp only [v, w, cuspMeanZeroFormPart_coe, cuspScalarFormPart_coe]
    abel
  have hm := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (formEmbedding (w : FormDomain)) (formEmbedding (v : FormDomain))
    (cuspScalarForm_mass_orthogonal w v)
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (formGradient (w : FormDomain)) (formGradient (v : FormDomain))
    (cuspScalarForm_energy_orthogonal w v)
  rw [← map_add, hsum] at hm
  rw [← map_add, hsum, formGradient_cuspTraceFree] at he
  have hv := cuspMeanZero_mass_le_five_halves_energy v
  have hw := cuspScalarForm_quarter_mass_le_energy w
  change ‖formEmbedding (v : FormDomain)‖ ^ 2 ≤
    (5 / 2 : ℝ) * ‖formGradient (v : FormDomain)‖ ^ 2 at hv
  change (1 / 4 : ℝ) * ‖formEmbedding (w : FormDomain)‖ ^ 2 ≤
    ‖formGradient (w : FormDomain)‖ ^ 2 at hw
  nlinarith [sq_nonneg ‖formGradient (v : FormDomain)‖]

/-- Removing the boundary trace cannot decrease mass of a constant-orthogonal vector. -/
theorem form_mass_le_traceFree_mass_of_constant_orthogonal (u : FormDomain)
    (hu : inner ℂ modularConstant (formEmbedding u) = 0) :
    ‖formEmbedding u‖ ^ 2 ≤ ‖formEmbedding (cuspTraceFree u)‖ ^ 2 := by
  have hi : inner ℂ (formEmbedding u) (-(cuspAverageTrace u • modularConstant)) = 0 := by
    rw [inner_neg_right, inner_smul_right, inner_eq_zero_symm.mpr hu, mul_zero, neg_zero]
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (formEmbedding u) (-(cuspAverageTrace u • modularConstant)) hi
  have he : formEmbedding (cuspTraceFree u) =
      formEmbedding u + -(cuspAverageTrace u • modularConstant) := by
    rw [cuspTraceFree_apply, map_sub, map_smul, formEmbedding_coreForm,
      value_constantCore_one]
    exact sub_eq_add_neg _ _
  rw [he]
  nlinarith [sq_nonneg ‖-(cuspAverageTrace u • modularConstant)‖]

/-- The actual full modular form has a quarter gap on the constant-orthogonal subspace. -/
theorem form_quarter_mass_le_energy_of_constant_orthogonal (u : FormDomain)
    (hu : inner ℂ modularConstant (formEmbedding u) = 0) :
    (1 / 4 : ℝ) * ‖formEmbedding u‖ ^ 2 ≤ ‖formGradient u‖ ^ 2 := by
  have h1 := form_mass_le_traceFree_mass_of_constant_orthogonal u hu
  have h2 := cuspTraceFree_mass_le_four_energy u
  linarith

/-- The actual operator energy obeys the same bound on its constant-orthogonal domain. -/
theorem laplacian_quarter_energy_of_constant_orthogonal (u : laplacian.domain)
    (hu : inner ℂ modularConstant (u : ModularHilbert) = 0) :
    (1 / 4 : ℝ) * ‖(u : ModularHilbert)‖ ^ 2 ≤
      (inner ℂ (laplacian u) (u : ModularHilbert)).re := by
  have hf := form_quarter_mass_le_energy_of_constant_orthogonal
    (formLift ⟨u, laplacian_domain_le u.property⟩) hu
  have he := laplacian_representation u ⟨u, laplacian_domain_le u.property⟩
  have hr : (inner ℂ (closedGradient ⟨u, laplacian_domain_le u.property⟩)
      (closedGradient ⟨u, laplacian_domain_le u.property⟩)).re =
      ‖closedGradient ⟨u, laplacian_domain_le u.property⟩‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (closedGradient ⟨u, laplacian_domain_le u.property⟩)
  rw [he, hr]
  exact hf

/-- No nonzero actual eigenvector has a real eigenvalue strictly between zero and one quarter. -/
theorem laplacian_eigenvector_eq_zero_of_pos_lt_quarter
    (u : laplacian.domain) {a : ℝ} (ha : 0 < a) (hlt : a < 1 / 4)
    (hu : laplacian u = (a : ℂ) • (u : ModularHilbert)) :
    (u : ModularHilbert) = 0 := by
  have hz : inner ℂ modularConstant (laplacian u) = 0 := by
    rw [modularConstant_inner]
    exact laplacian_integral u
  have hc : inner ℂ modularConstant (u : ModularHilbert) = 0 := by
    rw [hu, inner_smul_right] at hz
    exact (mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr ha.ne')
  have hg := laplacian_quarter_energy_of_constant_orthogonal u hc
  have hr : (inner ℂ (u : ModularHilbert) (u : ModularHilbert)).re =
      ‖(u : ModularHilbert)‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have he : (inner ℂ (laplacian u) (u : ModularHilbert)).re =
      a * ‖(u : ModularHilbert)‖ ^ 2 := by
    rw [hu, inner_smul_left]
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hr]
  rw [he] at hg
  have hn : ‖(u : ModularHilbert)‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖(u : ModularHilbert)‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

end GapFamily.Analytic
