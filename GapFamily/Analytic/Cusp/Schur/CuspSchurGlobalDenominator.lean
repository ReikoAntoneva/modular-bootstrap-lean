import GapFamily.Analytic.Cusp.Schur.CuspSchurProjectedIdentification

noncomputable section
namespace GapFamily.Analytic.CuspSchurGlobalPhysical
open ModularGradient ModularProjected CuspSchur

/-- The independently proved actual full inverse excludes a trace-one
homogeneous Schur vector; no denominator regularity is assumed. -/
theorem actualSchurDenominator_ne_zero_of_projected_units {z : ℂ}
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z))
    (hQ : IsUnit (projectedPencil z)) (hz : z ≠ 0) :
    actualSchurDenominator z ≠ 0 := by
  intro hD
  let u := schurVector z (cuspScalarPencilSolution z) 0 1
  have hu : ∀ t : FormDomain, formPairing z t u = inner ℂ (formEmbedding t) 0 := by
    apply (schurVector_equation_iff hV (cuspScalarPencilSolution z)
      (actualScalar_formPairing hW) 0 1).mpr
    have hDz : schurDenominator z (cuspScalarPencilSolution z) = 0 := hD
    simp only [hDz, zero_mul, schurNumerator, map_zero, inner_zero_right, mul_zero, add_zero]
  let x : laplacian.domain :=
    ⟨formEmbedding u, formEmbedding_mem_laplacian_domain_of_formPairing z u 0 hu⟩
  have hA : laplacian x - z • (x : ModularHilbert) = 0 :=
    laplacian_sub_smul_of_formPairing z u 0 hu
  have hleft : fullResolvent z 0 = formEmbedding u := by
    simpa only [hA] using fullResolvent_leftInverse_of_isUnit hQ hz x
  have he : formEmbedding u = 0 := by simpa only [map_zero] using hleft.symm
  have hu0 : u = 0 := formEmbedding_injective (by simpa only [map_zero] using he)
  have ht : cuspAverageTrace u = 1 := schurVector_trace z (cuspScalarPencilSolution z) 0 1
  rw [hu0, map_zero] at ht
  exact zero_ne_one ht

end GapFamily.Analytic.CuspSchurGlobalPhysical
