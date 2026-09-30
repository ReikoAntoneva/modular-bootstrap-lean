import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroPencilBasic

/-!
# The genuine constrained weak equation at regular pencil parameters

The complex parameter multiplies the solution in the second, linear argument
of the Hilbert inner product. The equivalent solution-first equation therefore
contains the conjugated parameter. All inverse identities require actual units.
-/

noncomputable section

namespace GapFamily.Analytic

/-- The actual test-first weak equation has the holomorphic parameter z. -/
theorem cuspMeanZeroPencilSolution_equation {z : ℂ}
    (hz : IsUnit (cuspMeanZeroPencil z)) (f : ModularHilbert) (v : cuspMeanZeroForm) :
    inner ℂ (cuspMeanZeroGradient v) (cuspMeanZeroGradient (cuspMeanZeroPencilSolution z f)) -
      z * inner ℂ (meanZeroCuspEmbedding v)
        (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution z f)) =
      inner ℂ (meanZeroCuspEmbedding v) f := by
  let g := Ring.inverse (cuspMeanZeroPencil z) f
  have hq : g - (z + 1) • cuspMeanZeroWeakResolvent g = f :=
    cuspMeanZeroPencil_apply_inverse hz f
  have hw := cuspMeanZeroWeakSolution_equation_test_first g v
  change inner ℂ (cuspMeanZeroGradient v) (cuspMeanZeroGradient (cuspMeanZeroWeakSolution g)) -
    z * inner ℂ (meanZeroCuspEmbedding v)
      (meanZeroCuspEmbedding (cuspMeanZeroWeakSolution g)) = _
  rw [← cuspMeanZeroWeakResolvent_apply, ← hq, inner_sub_right, inner_smul_right]
  linear_combination hw

/-- Reversing the two inner-product arguments conjugates the spectral parameter. -/
theorem cuspMeanZeroPencilSolution_equation_solution_first {z : ℂ}
    (hz : IsUnit (cuspMeanZeroPencil z)) (f : ModularHilbert) (v : cuspMeanZeroForm) :
    inner ℂ (cuspMeanZeroGradient (cuspMeanZeroPencilSolution z f)) (cuspMeanZeroGradient v) -
      (starRingEnd ℂ z) * inner ℂ
        (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution z f)) (meanZeroCuspEmbedding v) =
      inner ℂ f (meanZeroCuspEmbedding v) := by
  have h := congrArg (starRingEnd ℂ) (cuspMeanZeroPencilSolution_equation hz f v)
  simpa only [map_sub, map_mul, inner_conj_symm] using h

/-- Every actual weak solution satisfies the same ambient pencil equation. -/
theorem cuspMeanZeroPencil_apply_embedding_of_weak (z : ℂ) (f : ModularHilbert)
    (u : cuspMeanZeroForm)
    (hu : ∀ v : cuspMeanZeroForm,
      inner ℂ (cuspMeanZeroGradient v) (cuspMeanZeroGradient u) -
        z * inner ℂ (meanZeroCuspEmbedding v) (meanZeroCuspEmbedding u) =
          inner ℂ (meanZeroCuspEmbedding v) f) :
    cuspMeanZeroPencil z (meanZeroCuspEmbedding u) = cuspMeanZeroWeakResolvent f := by
  have huS : u = cuspMeanZeroWeakSolution (f + (z + 1) • meanZeroCuspEmbedding u) := by
    apply cuspMeanZeroWeakSolution_unique_test_first _ u
    intro v
    rw [inner_add_right, inner_smul_right]
    linear_combination hu v
  have hi := congrArg meanZeroCuspEmbedding huS
  change meanZeroCuspEmbedding u =
    cuspMeanZeroWeakResolvent (f + (z + 1) • meanZeroCuspEmbedding u) at hi
  rw [map_add, map_smul] at hi
  rw [cuspMeanZeroPencil_apply]
  exact sub_eq_iff_eq_add.mpr hi

/-- The constrained weak solution is unique whenever its actual pencil is a unit. -/
theorem cuspMeanZeroPencilSolution_unique {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (f : ModularHilbert) (u : cuspMeanZeroForm)
    (hu : ∀ v : cuspMeanZeroForm,
      inner ℂ (cuspMeanZeroGradient v) (cuspMeanZeroGradient u) -
        z * inner ℂ (meanZeroCuspEmbedding v) (meanZeroCuspEmbedding u) =
          inner ℂ (meanZeroCuspEmbedding v) f) :
    u = cuspMeanZeroPencilSolution z f := by
  apply meanZeroCuspEmbedding_injective
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hz).1
  rw [cuspMeanZeroPencil_apply_embedding_of_weak z f u hu,
    cuspMeanZeroPencil_apply_embedding_of_weak z f (cuspMeanZeroPencilSolution z f)
      (cuspMeanZeroPencilSolution_equation hz f)]

/-- At zero the family agrees exactly with the previously constructed pure-energy solution. -/
theorem cuspMeanZeroPencilSolution_zero :
    cuspMeanZeroPencilSolution 0 = cuspMeanZeroEnergySolution := by
  apply ContinuousLinearMap.ext
  intro f
  apply cuspMeanZeroEnergySolution_unique f (cuspMeanZeroPencilSolution 0 f)
  intro v
  have h := congrArg (starRingEnd ℂ)
    (cuspMeanZeroPencilSolution_equation cuspMeanZeroPencil_isUnit_zero f v)
  simpa only [map_sub, map_mul, map_zero, zero_mul, sub_zero, inner_conj_symm] using h

end GapFamily.Analytic
