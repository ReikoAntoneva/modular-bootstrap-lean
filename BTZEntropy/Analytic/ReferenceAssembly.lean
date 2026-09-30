import BTZEntropy.Analytic.ReferenceTransform
import BTZEntropy.Analytic.DescendantModular
import BTZEntropy.Analytic.DeterminantRegularity

/-!
# Exact full BTZ reference

Nonvacuum descendants and the cylinder shift are retained until the exact eta
identity cancels them. Thus the resulting exponent contains `c = 12a + 1`, with
no finite-charge shift dropped and no asymptotic replacement of the determinant.
-/

noncomputable section

namespace BTZEntropy

/-- Removing the actual level-one descendant factor leaves the vacuum determinant. -/
theorem boundaryGravitonFactor_eq_descendantEuler {u : ℝ} (hu : 0 < u) :
    boundaryGravitonFactor u =
      (1 - Real.exp (-u)) ^ 2 * descendantEuler u ^ 2 := by
  have heuler : (∏' m : ℕ, (1 - Real.exp (-((m + 1 : ℕ) : ℝ) * u))) =
      (descendantEuler u)⁻¹ := by
    calc
      _ = ∏' m : ℕ, (1 - thermalNome u ^ (m + 1)) := by
        apply tprod_congr
        intro m
        congr 1
        rw [thermalNome, ← Real.exp_nat_mul]
        congr 1
        ring
      _ = _ := (hasProd_thermalEuler hu).tprod_eq
  rw [boundaryGravitonFactor_eq_levelOneProduct hu, heuler]
  simp only [div_eq_mul_inv, inv_inv, mul_pow]

/-- The full reference thermal transform after adding all nonvacuum descendants
and converting shifted primary energy to cylinder energy. -/
def referenceFullTransform (a β : ℝ) : ℝ :=
  Real.exp (β / 12) * descendantEuler β ^ 2 * referencePrimaryTransform a β

/-- The perturbative BTZ transform with the actual convergent one-loop determinant. -/
def perturbativeBTZTransform (c β : ℝ) : ℝ :=
  Real.exp (Real.pi ^ 2 * c / (3 * β)) * boundaryGravitonFactor (4 * Real.pi ^ 2 / β)

/-- Both finite shifts cancel exactly: the continuous full reference equals the
perturbative BTZ partition function at central charge `12a+1`. -/
theorem referenceFullTransform_eq_btz {a β : ℝ} (ha : 2 ≤ a) (hβ : 0 < β) :
    referenceFullTransform a β = perturbativeBTZTransform (12 * a + 1) β := by
  have hdual : 0 < 4 * Real.pi ^ 2 / β := by positivity
  rw [referenceFullTransform, perturbativeBTZTransform,
    referencePrimaryTransform_eq ha hβ, descendantEuler_sq_inversion β hβ,
    boundaryGravitonFactor_eq_descendantEuler hdual]
  have hnull : -(4 * Real.pi ^ 2 / β) = -4 * Real.pi ^ 2 / β := by ring
  rw [hnull]
  have hfactor : β / (2 * Real.pi) * (2 * Real.pi / β) = 1 := by
    field_simp
  have hexp : Real.exp (β / 12) * Real.exp ((4 * Real.pi ^ 2 / β - β) / 12) *
      Real.exp (4 * Real.pi ^ 2 * a / β) =
      Real.exp (Real.pi ^ 2 * (12 * a + 1) / (3 * β)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  calc
    _ = (β / (2 * Real.pi) * (2 * Real.pi / β)) *
        (Real.exp (β / 12) * Real.exp ((4 * Real.pi ^ 2 / β - β) / 12) *
          Real.exp (4 * Real.pi ^ 2 * a / β)) *
        ((1 - Real.exp (-4 * Real.pi ^ 2 / β)) ^ 2 *
          descendantEuler (4 * Real.pi ^ 2 / β) ^ 2) := by ring
    _ = _ := by rw [hfactor, hexp, one_mul]

end BTZEntropy
