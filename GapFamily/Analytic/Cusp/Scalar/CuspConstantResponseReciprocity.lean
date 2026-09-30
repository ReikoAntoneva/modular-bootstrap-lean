import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponsePencil
import GapFamily.Analytic.Cusp.Scalar.CuspScalarPencilRegular

noncomputable section
namespace GapFamily.Analytic

/-- Conjugation preserves the physical parameter half-plane. -/
theorem cuspPhysical_conj_re_pos {κ : ℂ} (hκ : 0 < κ.re) :
    0 < ((starRingEnd ℂ) κ).re := by
  simpa using hκ

/-- Reciprocity of the actual scalar pencil response follows from its two
true weak equations at conjugate physical parameters. -/
theorem cuspScalarPencilSolution_reciprocity_physical {κ : ℂ} (hκ : 0 < κ.re)
    (F G : ModularHilbert) :
    inner ℂ G
        (scalarCuspEmbedding (cuspScalarPencilSolution ((1 / 4 : ℂ) - κ ^ 2) F)) =
      inner ℂ
        (scalarCuspEmbedding
          (cuspScalarPencilSolution ((1 / 4 : ℂ) - ((starRingEnd ℂ) κ) ^ 2) G)) F := by
  have hF := cuspScalarPencilSolution_equation_physical hκ F
    (cuspScalarPencilSolution ((1 / 4 : ℂ) - ((starRingEnd ℂ) κ) ^ 2) G)
  have hG := cuspScalarPencilSolution_equation_physical (cuspPhysical_conj_re_pos hκ) G
    (cuspScalarPencilSolution ((1 / 4 : ℂ) - κ ^ 2) F)
  have hc := congrArg (starRingEnd ℂ) hG
  simp only [map_sub, map_mul, map_div₀, map_one, map_ofNat, map_pow,
    starRingEnd_self_apply, inner_conj_symm] at hc
  exact hc.symm.trans hF

/-- The constant observation of an arbitrary actual physical scalar response
is represented by the conjugate-parameter literal constant-source form. -/
theorem cuspScalarPencilSolution_constant_reciprocity {κ : ℂ} (hκ : 0 < κ.re)
    (F : ModularHilbert) :
    inner ℂ modularConstant
        (scalarCuspEmbedding (cuspScalarPencilSolution ((1 / 4 : ℂ) - κ ^ 2) F)) =
      inner ℂ
        (scalarCuspEmbedding
          (cuspConstantScalarForm (cuspPhysical_conj_re_pos hκ))) F := by
  rw [cuspConstantScalarForm_eq_pencilSolution (cuspPhysical_conj_re_pos hκ)]
  exact cuspScalarPencilSolution_reciprocity_physical hκ F modularConstant


end GapFamily.Analytic
