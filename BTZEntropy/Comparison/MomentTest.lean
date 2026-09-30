import BTZEntropy.Observable
import GapFamily.Analytic.Foundation.MomentCancellation
import GapFamily.Construction.InitialReferenceCellResidual
import GapFamily.Construction.TailCellAtomic

/-!
# A smooth test of a moment-matched physical cell

This is the local estimate in §6, equation `entropy-smooth-moment-bound`.
The polynomial approximation is a bound on the entire closed cell, including
its continuum measure. The nodes retain their literal unit weights. No
regularity of the signed continuum density is assumed beyond integrability.
-/

noncomputable section

open Set MeasureTheory
open GapFamily.Analytic GapFamily.Construction
open scoped BigOperators

namespace BTZEntropy.Comparison

/-- Cancelling an integrable real approximant costs only the actual variation
mass times the uniform approximation error. -/
theorem abs_signedIntegral_le_of_approximation {ν : SignedMeasure ℝ}
    {f p : ℝ → ℝ} {ε : ℝ} (hf : ν.Integrable f) (hp : ν.Integrable p)
    (hz : (∫ᵛ x, p x ∂<•ν) = 0)
    (he : ∀ᵐ x ∂ν.variation, |f x - p x| ≤ ε) :
    |∫ᵛ x, f x ∂<•ν| ≤ ν.variation.real univ * ε := by
  let := signedMeasure_isFiniteMeasure_variation ν
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip)
    (by simpa only [Real.norm_eq_abs] using he)
  rw [VectorMeasure.integral_fun_sub hf hp, hz, sub_zero] at h
  simpa only [Real.norm_eq_abs, ContinuousLinearMap.opNorm_flip,
    ContinuousLinearMap.opNorm_lsmul, mul_one, mul_comm] using h

/-- The physical unit-node sum minus the genuine signed continuum integral
satisfies `(M + TV) ε`. Every integrability assertion is proved from the
continuous test and the actual integrable density. -/
theorem cell_error_le_of_polynomial_approximation
    {N : ℕ} (j : ℤ) (L V : ℝ) {q f : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : IntegrableOn q (Ioo L V) (referenceMeasure j))
    (hnode : ∀ i, node i ∈ Icc L V) (hf : Continuous f)
    (p : Polynomial ℝ)
    (hm : (∫ᵛ E, p.eval (rootCoord |(j : ℝ)| E)
      ∂<•cellResidualMeasure j L V q node) = 0)
    {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ E ∈ Icc L V, |f E - p.eval (rootCoord |(j : ℝ)| E)| ≤ ε) :
    |(∑ i, f (node i)) - ∫ E in Ioo L V, q E * f E ∂referenceMeasure j| ≤
      ((N : ℝ) + ∫ E in Ioo L V, |q E| ∂referenceMeasure j) * ε := by
  obtain ⟨hfi, _, heq⟩ := cellResidualMeasure_integral_continuous j L V node hq hf
  obtain ⟨hpi, _, _⟩ := cellResidualMeasure_integral_coordinatePolynomial j L V node hq p
  have hs : ∀ᵐ E ∂(cellResidualMeasure j L V q node).variation, E ∈ Icc L V :=
    ae_iff.mpr (cellResidualMeasure_variation_compl_Icc j L V node hq hnode)
  have hb := abs_signedIntegral_le_of_approximation hfi hpi hm
    (hs.mono (fun E hE => happrox E hE))
  rw [heq] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (cellResidualMeasure_variation_le j L V node hq) hε)

/-- The normalized square-root coordinate used in the paper's test function. -/
def normalizedRootCoord (r L V E : ℝ) : ℝ :=
  (rootCoord r E - rootCoord r L) / cellCoordinateLength r L V

/-- Normalization maps every physical energy in the full closed cell to
`[0,1]`; this is not just a statement about the chosen nodes. -/
theorem normalizedRootCoord_mem {r L V E : ℝ} (hr : r ≤ L) (hLV : L < V)
    (hE : E ∈ Icc L V) : normalizedRootCoord r L V E ∈ Icc (0 : ℝ) 1 := by
  have hcoord := (rootCoord_mem_Icc_iff r hr (hr.trans hLV.le) (hr.trans hE.1)).mpr hE
  have hd : 0 < cellCoordinateLength r L V :=
    sub_pos.mpr (rootCoord_lt_rootCoord r hr hLV)
  refine ⟨div_nonneg (sub_nonneg.mpr hcoord.1) hd.le, ?_⟩
  change (rootCoord r E - rootCoord r L) / cellCoordinateLength r L V ≤ 1
  rw [div_le_one hd]
  exact sub_le_sub_right hcoord.2 _

/-- Reconstruct physical energy from the normalized coordinate. -/
def normalizedCellEnergy (r L V z : ℝ) : ℝ :=
  energyCoord r (rootCoord r L + cellCoordinateLength r L V * z)

theorem normalizedCellEnergy_normalizedRootCoord {r L V E : ℝ}
    (hr : r ≤ L) (hLV : L < V) (hE : E ∈ Icc L V) :
    normalizedCellEnergy r L V (normalizedRootCoord r L V E) = E := by
  have hd : cellCoordinateLength r L V ≠ 0 :=
    ne_of_gt (sub_pos.mpr (rootCoord_lt_rootCoord r hr hLV))
  simp only [normalizedCellEnergy, normalizedRootCoord, mul_div_cancel₀ _ hd,
    add_sub_cancel]
  exact energyCoord_rootCoord r (hr.trans hE.1)

/-- Pulling a polynomial in the unit coordinate back to the root coordinate
does not raise its degree. -/
def normalizedPolynomial (r L V : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  p.comp ((Polynomial.X - Polynomial.C (rootCoord r L)) *
    Polynomial.C (cellCoordinateLength r L V)⁻¹)

theorem normalizedPolynomial_natDegree_le (r L V : ℝ) (p : Polynomial ℝ) :
    (normalizedPolynomial r L V p).natDegree ≤ p.natDegree := by
  have ha : ((Polynomial.X - Polynomial.C (rootCoord r L)) *
      Polynomial.C (cellCoordinateLength r L V)⁻¹).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_mul_le).trans
    simpa only [Polynomial.natDegree_C, Nat.add_zero] using
      (Polynomial.natDegree_sub_le (Polynomial.X : Polynomial ℝ)
        (Polynomial.C (rootCoord r L))).trans (by simp)
  exact Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul_left p.natDegree ha).trans_eq (Nat.mul_one _))

theorem normalizedPolynomial_eval (r L V E : ℝ) (p : Polynomial ℝ) :
    (normalizedPolynomial r L V p).eval (rootCoord r E) =
      p.eval (normalizedRootCoord r L V E) := by
  simp only [normalizedPolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    normalizedRootCoord, div_eq_mul_inv]

/-- The paper's cell estimate with a polynomial approximant on `[0,1]`.
The moments are those of the actual construction in the root coordinate. -/
theorem cell_error_le_of_normalized_approximation
    {N k : ℕ} (j : ℤ) {L V : ℝ} {q f : ℝ → ℝ} (node : Fin N → ℝ)
    (hL : |(j : ℝ)| ≤ L) (hLV : L < V)
    (hq : IntegrableOn q (Ioo L V) (referenceMeasure j))
    (hnode : ∀ i, node i ∈ Icc L V) (hf : Continuous f)
    (hm : ∀ p : Polynomial ℝ, p.natDegree ≤ k →
      (∫ᵛ E, p.eval (rootCoord |(j : ℝ)| E)
        ∂<•cellResidualMeasure j L V q node) = 0)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ k) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ z ∈ Icc (0 : ℝ) 1,
      |f (normalizedCellEnergy |(j : ℝ)| L V z) - p.eval z| ≤ ε) :
    |(∑ i, f (node i)) - ∫ E in Ioo L V, q E * f E ∂referenceMeasure j| ≤
      ((N : ℝ) + ∫ E in Ioo L V, |q E| ∂referenceMeasure j) * ε := by
  apply cell_error_le_of_polynomial_approximation j L V node hq hnode hf
    (normalizedPolynomial |(j : ℝ)| L V p)
    (hm _ ((normalizedPolynomial_natDegree_le _ _ _ _).trans hp)) hε
  intro E hE
  have he := happrox _ (normalizedRootCoord_mem hL hLV hE)
  simpa only [normalizedCellEnergy_normalizedRootCoord hL hLV hE,
    normalizedPolynomial_eval] using he

/-- Tail-cell specialization using the stored, proved moment identities. -/
theorem tailCell_error_le {j : ℤ} {L : ℝ} {k : ℕ} {q f : ℝ → ℝ}
    (cell : TailCell j L k q) (hL : |(j : ℝ)| ≤ L) (hf : Continuous f)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ k) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ z ∈ Icc (0 : ℝ) 1,
      |f (normalizedCellEnergy |(j : ℝ)| L cell.right z) - p.eval z| ≤ ε) :
    |(∑ i, f (cell.node i)) - ∫ E in Ioo L cell.right, q E * f E ∂referenceMeasure j| ≤
      ((cell.count : ℝ) + ∫ E in Ioo L cell.right, |q E| ∂referenceMeasure j) * ε :=
  cell_error_le_of_normalized_approximation j cell.node hL
    (by linarith [cell.right_mem.1]) cell.density_integrable cell.node_mem hf
    (fun p hp => (cell.moment p hp).2) p hp hε happrox

/-- On a positive tail cell, the ordinary variation equals its matched unit
mass, so the paper's prefactor is exactly twice that mass. -/
theorem tailCell_error_le_twice_count {j : ℤ} {L : ℝ} {k : ℕ} {q f : ℝ → ℝ}
    (cell : TailCell j L k q) (hL : |(j : ℝ)| ≤ L) (hf : Continuous f)
    (hq : ∀ᵐ E ∂(referenceMeasure j).restrict (Ioo L cell.right), 0 ≤ q E)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ k) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ z ∈ Icc (0 : ℝ) 1,
      |f (normalizedCellEnergy |(j : ℝ)| L cell.right z) - p.eval z| ≤ ε) :
    |(∑ i, f (cell.node i)) - ∫ E in Ioo L cell.right, q E * f E ∂referenceMeasure j| ≤
      2 * (cell.count : ℝ) * ε := by
  have habs : (∫ E in Ioo L cell.right, |q E| ∂referenceMeasure j) =
      (cell.count : ℝ) := by
    rw [← cell.mass_eq]
    exact integral_congr_ae (hq.mono fun E hE => abs_of_nonneg hE)
  simpa only [habs, ← two_mul] using tailCell_error_le cell hL hf p hp hε happrox

/-- Initial-cell specialization; no positivity of its signed density is used. -/
theorem initialCell_error_le {j : ℤ} {L U : ℝ} {k : ℕ} {q f : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) (hL : |(j : ℝ)| ≤ L)
    (hLU : L < U) (hf : Continuous f)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ k) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ z ∈ Icc (0 : ℝ) 1,
      |f (normalizedCellEnergy |(j : ℝ)| L cell.right z) - p.eval z| ≤ ε) :
    |(∑ i, f (cell.node i)) - ∫ E in Ioo L cell.right, q E * f E ∂referenceMeasure j| ≤
      ((cell.count : ℝ) + ∫ E in Ioo L cell.right, |q E| ∂referenceMeasure j) * ε :=
  cell_error_le_of_normalized_approximation j cell.node hL
    (hLU.trans_le cell.right_mem.1) cell.density_integrable cell.node_mem hf
    (fun p hp => (cell.moment p hp).2) p hp hε happrox

/-- The actual descendant test uses the exact finite-charge shift `-1/12`. -/
def descendantTest (φ : SmoothKernel) (q : ℕ) (E : ℝ) (u : ℝ) : ℝ :=
  φ (u - 1 / 12 + (q : ℝ) - E)

theorem continuous_descendantTest (φ : SmoothKernel) (q : ℕ) (E : ℝ) :
    Continuous (descendantTest φ q E) := by
  apply φ.smooth.continuous.comp
  fun_prop

/-- Each descendant level satisfies the same signed-cell bound. The sole
approximation input concerns the prescribed smooth kernel on the full unit
interval; no evolving density is differentiated. -/
theorem tailCell_descendant_error_le {j : ℤ} {L : ℝ} {k : ℕ} {ρ : ℝ → ℝ}
    (cell : TailCell j L k ρ) (hL : |(j : ℝ)| ≤ L)
    (φ : SmoothKernel) (q : ℕ) (E : ℝ)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ k) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ z ∈ Icc (0 : ℝ) 1,
      |descendantTest φ q E (normalizedCellEnergy |(j : ℝ)| L cell.right z) -
        p.eval z| ≤ ε) :
    |(∑ i, descendantTest φ q E (cell.node i)) -
      ∫ u in Ioo L cell.right, ρ u * descendantTest φ q E u ∂referenceMeasure j| ≤
      ((cell.count : ℝ) + ∫ u in Ioo L cell.right, |ρ u| ∂referenceMeasure j) * ε :=
  tailCell_error_le cell hL (continuous_descendantTest φ q E) p hp hε happrox

end BTZEntropy.Comparison
