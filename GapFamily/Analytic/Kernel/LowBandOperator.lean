import GapFamily.Analytic.Kernel.PositiveCompression
import GapFamily.Analytic.Kernel.LowBandOperatorRiesz
import GapFamily.Analytic.Kernel.LowBandOperatorSymmetry
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual bounded operator on the open physical band

Each row is the `L²` space of the restricted physical reference measure.
The finite collection uses the Hilbert sum norm. The operator is constructed
from the ordinary kernel integrals by the Riesz representation theorem.
-/

noncomputable section

open MeasureTheory Real
open scoped ComplexConjugate BigOperators

namespace GapFamily.Analytic

/-- A physical `L²` row restricted to the open low band. -/
abbrev LowBandRow (j : ℤ) (B : ℝ) : Type :=
  Lp ℂ 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B))

/-- The Hilbert direct sum of finitely many physical low-band rows. -/
abbrev LowBandHilbert {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ) :=
  PiLp 2 (fun i => LowBandRow (j i) B)

section Row

variable {j J : ℤ} {B C : ℝ} {K : ℝ × ℝ → ℂ}
variable (hC : 0 ≤ C)
variable (hK : AEStronglyMeasurable K ((referenceMeasure j).prod (referenceMeasure J)))
variable (hbound : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
  ‖K p‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2))

include hC hK hbound in
theorem lowBandKernelPairing_add_left (f₁ f₂ : LowBandRow j B) (g : LowBandRow J B) :
    lowBandKernelPairing j J B K ⇑(f₁ + f₂) g =
      lowBandKernelPairing j J B K f₁ g + lowBandKernelPairing j J B K f₂ g := by
  rw [lowBandKernelPairing_congr_ae (Lp.coeFn_add f₁ f₂) ae_eq_rfl]
  have hfun : weakKernelIntegrand K (⇑f₁ + ⇑f₂) g =
      weakKernelIntegrand K f₁ g + weakKernelIntegrand K f₂ g := by
    funext p
    simp [weakKernelIntegrand, add_mul]
  simp only [lowBandKernelPairing, hfun]
  exact integral_add
    (lowBandKernel_integrable hC hK hbound (Lp.memLp f₁) (Lp.memLp g))
    (lowBandKernel_integrable hC hK hbound (Lp.memLp f₂) (Lp.memLp g))

include hC hK hbound in
theorem lowBandKernelPairing_add_right (f : LowBandRow j B) (g₁ g₂ : LowBandRow J B) :
    lowBandKernelPairing j J B K f ⇑(g₁ + g₂) =
      lowBandKernelPairing j J B K f g₁ + lowBandKernelPairing j J B K f g₂ := by
  rw [lowBandKernelPairing_congr_ae ae_eq_rfl (Lp.coeFn_add g₁ g₂)]
  have hfun : weakKernelIntegrand K f (⇑g₁ + ⇑g₂) =
      weakKernelIntegrand K f g₁ + weakKernelIntegrand K f g₂ := by
    funext p
    simp [weakKernelIntegrand, mul_add]
  simp only [lowBandKernelPairing, hfun]
  exact integral_add
    (lowBandKernel_integrable hC hK hbound (Lp.memLp f) (Lp.memLp g₁))
    (lowBandKernel_integrable hC hK hbound (Lp.memLp f) (Lp.memLp g₂))

theorem lowBandKernelPairing_smul_left (c : ℂ) (f : LowBandRow j B)
    (g : LowBandRow J B) :
    lowBandKernelPairing j J B K ⇑(c • f) g =
      conj c * lowBandKernelPairing j J B K f g := by
  rw [lowBandKernelPairing_congr_ae (Lp.coeFn_smul c f) ae_eq_rfl]
  have hfun : weakKernelIntegrand K (c • ⇑f) g =
      fun p => conj c * weakKernelIntegrand K f g p := by
    funext p
    simp [weakKernelIntegrand, mul_assoc]
  simp only [lowBandKernelPairing, hfun, integral_const_mul]

theorem lowBandKernelPairing_smul_right (c : ℂ) (f : LowBandRow j B)
    (g : LowBandRow J B) :
    lowBandKernelPairing j J B K f ⇑(c • g) =
      c * lowBandKernelPairing j J B K f g := by
  rw [lowBandKernelPairing_congr_ae ae_eq_rfl (Lp.coeFn_smul c g)]
  have hfun : weakKernelIntegrand K f (c • ⇑g) =
      fun p => c * weakKernelIntegrand K f g p := by
    funext p
    simp only [weakKernelIntegrand, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [lowBandKernelPairing, hfun, integral_const_mul]

include hC hK hbound in
theorem lowBandKernelPairing_Lp_norm_le (f : LowBandRow j B) (g : LowBandRow J B) :
    ‖lowBandKernelPairing j J B K f g‖ ≤
      C * weakKernelMomentConstant j J * (1 + |B|) ^ 4 * ‖f‖ * ‖g‖ := by
  simpa only [Lp.norm_def] using
    lowBandKernelPairing_norm_le hC hK hbound (Lp.memLp f) (Lp.memLp g)

end Row

/-- The actual ordinary-integral sesquilinear form on the finite Hilbert sum. -/
def lowBandHilbertForm {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (B : ℝ) (K : ι → ι → ℝ × ℝ → ℂ)
    (f g : LowBandHilbert j B) : ℂ :=
  ∑ i, ∑ l, lowBandKernelPairing (j i) (j l) B (K i l) (f i) (g l)

/-- An explicit finite bound for the compressed operator norm. -/
def lowBandOperatorBound {ι : Type*} [Fintype ι] (j : ι → ℤ) (B C : ℝ) : ℝ :=
  ∑ i, ∑ l, C * weakKernelMomentConstant (j i) (j l) * (1 + |B|) ^ 4

theorem lowBandOperatorBound_nonneg {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (B : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ lowBandOperatorBound j B C := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro l hl
  exact mul_nonneg (mul_nonneg hC (weakKernelMomentConstant_nonneg _ _)) (by positivity)

section Finite

variable {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
variable (K : ι → ι → ℝ × ℝ → ℂ) {C : ℝ} (hC : 0 ≤ C)
variable (hK : ∀ i l, AEStronglyMeasurable (K i l)
  ((referenceMeasure (j i)).prod (referenceMeasure (j l))))
variable (hbound : ∀ i l, ∀ᵐ p ∂(referenceMeasure (j i)).prod (referenceMeasure (j l)),
  ‖K i l p‖ ≤ C * (|(j i : ℝ)| * |(j l : ℝ)| + sqrt p.1 * sqrt p.2))

include hC hK hbound in
theorem lowBandHilbertForm_add_left (f₁ f₂ g : LowBandHilbert j B) :
    lowBandHilbertForm j B K (f₁ + f₂) g =
      lowBandHilbertForm j B K f₁ g + lowBandHilbertForm j B K f₂ g := by
  simp only [lowBandHilbertForm, PiLp.add_apply,
    lowBandKernelPairing_add_left hC (hK _ _) (hbound _ _), Finset.sum_add_distrib]

include hC hK hbound in
theorem lowBandHilbertForm_add_right (f g₁ g₂ : LowBandHilbert j B) :
    lowBandHilbertForm j B K f (g₁ + g₂) =
      lowBandHilbertForm j B K f g₁ + lowBandHilbertForm j B K f g₂ := by
  simp only [lowBandHilbertForm, PiLp.add_apply,
    lowBandKernelPairing_add_right hC (hK _ _) (hbound _ _), Finset.sum_add_distrib]

theorem lowBandHilbertForm_smul_left (c : ℂ) (f g : LowBandHilbert j B) :
    lowBandHilbertForm j B K (c • f) g = conj c * lowBandHilbertForm j B K f g := by
  simp only [lowBandHilbertForm, PiLp.smul_apply,
    lowBandKernelPairing_smul_left, Finset.mul_sum]

theorem lowBandHilbertForm_smul_right (c : ℂ) (f g : LowBandHilbert j B) :
    lowBandHilbertForm j B K f (c • g) = c * lowBandHilbertForm j B K f g := by
  simp only [lowBandHilbertForm, PiLp.smul_apply,
    lowBandKernelPairing_smul_right, Finset.mul_sum]

include hC hK hbound in
theorem lowBandHilbertForm_norm_le (f g : LowBandHilbert j B) :
    ‖lowBandHilbertForm j B K f g‖ ≤ lowBandOperatorBound j B C * ‖f‖ * ‖g‖ := by
  calc
    _ ≤ ∑ i, ∑ l, ‖lowBandKernelPairing (j i) (j l) B (K i l) (f i) (g l)‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ l, C * weakKernelMomentConstant (j i) (j l) *
        (1 + |B|) ^ 4 * ‖f‖ * ‖g‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro l hl
      refine (lowBandKernelPairing_Lp_norm_le hC (hK i l) (hbound i l) (f i) (g l)).trans ?_
      have hM : 0 ≤ C * weakKernelMomentConstant (j i) (j l) * (1 + |B|) ^ 4 :=
        mul_nonneg (mul_nonneg hC (weakKernelMomentConstant_nonneg _ _)) (by positivity)
      gcongr
      · exact PiLp.norm_apply_le f i
      · exact PiLp.norm_apply_le g l
    _ = _ := by simp only [lowBandOperatorBound, Finset.sum_mul]

/-- Continuous packaging of the proved ordinary-integral form. -/
def lowBandContinuousForm :
    LowBandHilbert j B →L⋆[ℂ] LowBandHilbert j B →L[ℂ] ℂ :=
  boundedSesquilinearForm (lowBandHilbertForm j B K)
    (lowBandHilbertForm_add_left j B K hC hK hbound)
    (lowBandHilbertForm_smul_left j B K)
    (lowBandHilbertForm_add_right j B K hC hK hbound)
    (lowBandHilbertForm_smul_right j B K)
    (lowBandOperatorBound j B C) (lowBandHilbertForm_norm_le j B K hC hK hbound)

@[simp]
theorem lowBandContinuousForm_apply (f g : LowBandHilbert j B) :
    lowBandContinuousForm j B K hC hK hbound f g = lowBandHilbertForm j B K f g := rfl

/-- The kernel operator obtained from the actual low-band integral by Riesz duality. -/
def lowBandKernelOperator : LowBandHilbert j B →L[ℂ] LowBandHilbert j B :=
  sesquilinearOperator (lowBandContinuousForm j B K hC hK hbound)

/-- The representing identity is an equality with the ordinary product integrals. -/
theorem inner_lowBandKernelOperator (f g : LowBandHilbert j B) :
    inner ℂ f (lowBandKernelOperator j B K hC hK hbound g) =
      ∑ i, ∑ l, lowBandKernelPairing (j i) (j l) B (K i l) (f i) (g l) := by
  exact inner_sesquilinearOperator _ f g

/-- Explicit norm control of the constructed operator. -/
theorem norm_lowBandKernelOperator_le :
    ‖lowBandKernelOperator j B K hC hK hbound‖ ≤ lowBandOperatorBound j B C :=
  norm_sesquilinearOperator_le_of_bound _ (lowBandOperatorBound_nonneg j B hC)
    (lowBandHilbertForm_norm_le j B K hC hK hbound)

theorem lowBandHilbertForm_hermitian
    (hHermitian : ∀ i l, ∀ᵐ p ∂(referenceMeasure (j i)).prod (referenceMeasure (j l)),
      conj (K l i p.swap) = K i l p) (f g : LowBandHilbert j B) :
    conj (lowBandHilbertForm j B K g f) = lowBandHilbertForm j B K f g := by
  simp only [lowBandHilbertForm, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  exact lowBandKernelPairing_conj_swap (f i) (g l) (hHermitian i l)

/-- Physical almost-everywhere Hermitian symmetry gives self-adjointness of
the constructed low-band operator. -/
theorem isSelfAdjoint_lowBandKernelOperator
    (hHermitian : ∀ i l, ∀ᵐ p ∂(referenceMeasure (j i)).prod (referenceMeasure (j l)),
      conj (K l i p.swap) = K i l p) :
    IsSelfAdjoint (lowBandKernelOperator j B K hC hK hbound) :=
  isSelfAdjoint_sesquilinearOperator _ (lowBandHilbertForm_hermitian j B K hHermitian)

omit [Fintype ι] in
theorem lowBandRow_norm_sq_eq_integral (i : ι) (f : LowBandRow (j i) B) :
    ‖f‖ ^ 2 = ∫ E, ‖f E‖ ^ 2 ∂(referenceMeasure (j i)).restrict (Set.Ioo |(j i : ℝ)| B) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

theorem lowBandHilbert_norm_sq_eq_integral (f : LowBandHilbert j B) :
    ‖f‖ ^ 2 = ∑ i, ∫ E, ‖f i E‖ ^ 2
      ∂(referenceMeasure (j i)).restrict (Set.Ioo |(j i : ℝ)| B) := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl (fun i _ => lowBandRow_norm_sq_eq_integral j B i (f i))

/-- The Hilbert quadratic form equals the actual compressed physical quadratic form. -/
theorem lowBandHilbert_quadratic_eq (f : LowBandHilbert j B) :
    ‖f‖ ^ 2 + (lowBandHilbertForm j B K f f).re =
      lowBandIdentityPlusKernelQuadratic j B K (fun i => ⇑(f i)) := by
  rw [lowBandHilbert_norm_sq_eq_integral]
  simp only [lowBandHilbertForm, lowBandIdentityPlusKernelQuadratic, Complex.re_sum]

/-- Actual finite-Laplace positivity makes identity plus the constructed
low-band operator positive. The kernel and finite-test hypotheses remain explicit. -/
theorem isPositive_id_add_lowBandKernelOperator
    (hHermitian : ∀ i l, ∀ᵐ p ∂(referenceMeasure (j i)).prod (referenceMeasure (j l)),
      conj (K l i p.swap) = K i l p)
    (hpositive : ∀ (m : ι → ℕ) (c : ∀ i, Fin (m i) → ℂ),
      0 ≤ identityPlusKernelQuadratic j K (fun i => finiteLaplaceSum (c i))) :
    (ContinuousLinearMap.id ℂ (LowBandHilbert j B) +
      lowBandKernelOperator j B K hC hK hbound).IsPositive := by
  apply isPositive_id_add_sesquilinearOperator
    (lowBandContinuousForm j B K hC hK hbound)
    (lowBandHilbertForm_hermitian j B K hHermitian)
  intro f
  rw [lowBandContinuousForm_apply, lowBandHilbert_quadratic_eq]
  exact lowBandIdentityPlusKernelQuadratic_nonneg_of_finiteLaplace j B K hC hK hbound
    hpositive (fun i => ⇑(f i)) (fun i => Lp.memLp (f i))

end Finite

end GapFamily.Analytic
