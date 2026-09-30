import GapFamily.Analytic.Kernel.FullKernelOperator
import GapFamily.Analytic.Spatial.SpatialOrbitLaplacePositivity
import GapFamily.Analytic.Transform.LaplaceFiniteKernelPairing
import GapFamily.Analytic.Transform.LaplaceFiniteIdentityPairing
import GapFamily.Analytic.Spatial.SpatialLaplaceEnergyPairing

/-! The actual finite energy quadratic form and its positive open-band
operator. The ordinary spatial/energy pairing identity, spatial positivity,
and the controlled passage to physical weighted rows are all proved. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory
open scoped ComplexOrder ComplexConjugate BigOperators

/-- Reordering the finite coefficient vector by its physical spin and degree. -/
private theorem sum_sigma_pair {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (F : (Σ i, Fin (m i)) → (Σ i, Fin (m i)) → ℂ) :
    (∑ a, ∑ b, F a b) = ∑ i, ∑ l, ∑ k : Fin (m i), ∑ q : Fin (m l), F ⟨i, k⟩ ⟨l, q⟩ := by
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

private theorem finite_coefficient_quadratic_eq_of_row
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
    (F : (Σ i, Fin (m i)) → (Σ i, Fin (m i)) → ℂ)
    (Q : ι → ℝ) (R : ι → ι → ℝ)
    (hrow : ∀ i l, (∑ k : Fin (m i), ∑ q : Fin (m l), F ⟨i, k⟩ ⟨l, q⟩).re =
      (if i = l then Q i else 0) + R i l) :
    (∑ a, ∑ b, F a b).re = (∑ i, Q i) + ∑ i, ∑ l, R i l := by
  classical
  rw [sum_sigma_pair]
  calc
    _ = ∑ i, ∑ l, (∑ k : Fin (m i), ∑ q : Fin (m l), F ⟨i, k⟩ ⟨l, q⟩).re := by
      simp only [Complex.re_sum]
    _ = _ := by simp_rw [hrow]; simp [Finset.sum_add_distrib]

private theorem finite_laplaceEnergyPairing_row
    {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι → ℤ) (hj : Function.Injective j)
    (m : ι → ℕ) (c : ∀ i, Fin (m i) → ℂ) (i l : ι) :
    (∑ k : Fin (m i), ∑ q : Fin (m l), star (c i k) *
      laplaceEnergyPairing (j i) (j l) k.val q.val * c l q).re =
      (if i = l then ∫ E, ‖finiteLaplaceSum (c i) E‖ ^ 2 ∂referenceMeasure (j i) else 0) +
      (weakKernelPairing (j i) (j l) (fun p => correctedKernel (j i) (j l) p.1 p.2)
        (finiteLaplaceSum (c i)) (finiteLaplaceSum (c l))).re := by
  simp only [laplaceEnergyPairing, mul_add, add_mul, Finset.sum_add_distrib, Complex.add_re]
  rw [← weakKernelPairing_correctedKernel_finiteLaplaceSum]
  by_cases hil : i = l
  · subst l
    simp only [ite_true, eq_self]
    rw [← integral_norm_sq_finiteLaplaceSum_referenceMeasure]
  · have hne : j i ≠ j l := fun h => hil (hj h)
    simp only [hne, hil, ite_false, mul_zero, zero_mul, Finset.sum_const_zero,
      Complex.zero_re, zero_add]

/-- The actual finite-spin energy form is exactly the coefficient quadratic
form of the physical energy pairing. Injectivity says each spin occurs once. -/
theorem identityPlusCorrectedKernelQuadratic_finiteLaplaceSum_eq
    {ι : Type*} [Fintype ι] (j : ι → ℤ) (hj : Function.Injective j)
    (m : ι → ℕ) (c : ∀ i, Fin (m i) → ℂ) :
    identityPlusKernelQuadratic j (fun i l p => correctedKernel (j i) (j l) p.1 p.2)
      (fun i => finiteLaplaceSum (c i)) =
      (∑ a : Σ i, Fin (m i), ∑ b : Σ i, Fin (m i),
        star (c a.1 a.2) * laplaceEnergyPairing (j a.1) (j b.1) a.2.val b.2.val * c b.1 b.2).re := by
  classical
  symm
  exact finite_coefficient_quadratic_eq_of_row m _
    (fun i => ∫ E, ‖finiteLaplaceSum (c i) E‖ ^ 2 ∂referenceMeasure (j i))
    (fun i l => (weakKernelPairing (j i) (j l)
      (fun p => correctedKernel (j i) (j l) p.1 p.2)
      (finiteLaplaceSum (c i)) (finiteLaplaceSum (c l))).re)
    (finite_laplaceEnergyPairing_row j hj m c)

/-- Every finite physical energy test is nonnegative by the proved actual
spatial/energy identity and the canonical corrected spatial positivity. -/
theorem identityPlusCorrectedKernelQuadratic_finiteLaplace_nonneg
    {ι : Type*} [Fintype ι] (j : ι → ℤ) (hj : Function.Injective j)
    (m : ι → ℕ) (c : ∀ i, Fin (m i) → ℂ) :
    0 ≤ identityPlusKernelQuadratic j (fun i l p => correctedKernel (j i) (j l) p.1 p.2)
      (fun i => finiteLaplaceSum (c i)) := by
  rw [identityPlusCorrectedKernelQuadratic_finiteLaplaceSum_eq j hj m c]
  have h := SpatialPoint.spatialLaplacePairing_quadratic_re_nonneg
    (fun a : Σ i, Fin (m i) => j a.1) (fun a => a.2.val) (fun a => c a.1 a.2)
  simpa only [SpatialPoint.spatialLaplacePairing_eq_laplaceEnergyPairing] using h

/-- The proved weighted density and weak-kernel continuity extend finite
physical Laplace positivity to all actual weighted energy rows. -/
theorem identityPlusCorrectedKernelQuadratic_nonneg
    {ι : Type*} [Fintype ι] (j : ι → ℤ) (hj : Function.Injective j)
    (f : ι → ℝ → ℂ) (hf : ∀ i, MemLp (f i) 2 (energySpaceMeasure (j i))) :
    0 ≤ identityPlusKernelQuadratic j (fun i l p => correctedKernel (j i) (j l) p.1 p.2) f :=
  identityPlusKernelQuadratic_nonneg_of_finiteLaplace j _ correctedKernelBound_pos.le
    (fun i l => correctedKernel_aestronglyMeasurable (j i) (j l))
    (fun i l => correctedKernel_ae_weak_bound (j i) (j l))
    (identityPlusCorrectedKernelQuadratic_finiteLaplace_nonneg
      j hj) f hf

/-- The actual full low-band `I + R_B` is positive on every finite physical
spin family, with no positivity or inverse supplied as an assumption. -/
theorem isPositive_correctedLowBandIdentityPlus
    {ι : Type*} [Fintype ι] (j : ι → ℤ) (hj : Function.Injective j) (B : ℝ) :
    (correctedLowBandIdentityPlus j B).IsPositive := by
  unfold correctedLowBandIdentityPlus correctedLowBandOperator
  apply isPositive_id_add_lowBandKernelOperator
  · intro i l
    exact Filter.Eventually.of_forall fun p => correctedKernel_hermitian (j i) (j l) p.1 p.2
  · exact identityPlusCorrectedKernelQuadratic_finiteLaplace_nonneg
      j hj

/-- In particular the positivity statement applies to every actual finite
set of physical spins, with no duplicated spin coordinate. -/
theorem isPositive_correctedLowBandIdentityPlus_finset
    (S : Finset ℤ) (B : ℝ) :
    (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B).IsPositive :=
  isPositive_correctedLowBandIdentityPlus
    _ Subtype.val_injective B

end GapFamily.Analytic
