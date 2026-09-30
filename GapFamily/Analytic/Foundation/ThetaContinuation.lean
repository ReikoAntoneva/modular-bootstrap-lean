import GapFamily.Analytic.Foundation.ThetaTransform
import GapFamily.Analytic.Foundation.LatticeEisenstein
import GapFamily.Analytic.Foundation.SpectralScattering
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Mellin continuation of the actual determinant-one lattice theta series

The function is the Mellin transform of the actual lattice Gaussian after
removing its zero row. The factor one half is the normalization compatible
with the scalar cusp-coset Poincaré series.
-/

noncomputable section

namespace GapFamily.Analytic

open Real Complex Filter Asymptotics Set MeasureTheory
open scoped Topology MatrixGroups

/-- The actual lattice theta inversion formula is a self-dual weight-one FE pair. -/
def latticeThetaFEPair (z : UpperHalfPlane) : WeakFEPair ℂ where
  f := fun t ↦ (latticeTheta z t : ℂ)
  g := fun t ↦ (latticeTheta z t : ℂ)
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_latticeTheta z)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_latticeTheta z)).locallyIntegrableOn
    measurableSet_Ioi
  hk := zero_lt_one
  hε := one_ne_zero
  h_feq t ht := by
    simpa only [Real.rpow_one, one_mul, smul_eq_mul, ← Complex.ofReal_mul] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) (latticeTheta_functional_equation z ht)
  hf_top r := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
      Complex.isBigO_ofReal_left.mpr (isBigO_latticeTheta_sub_one_rpow z r)
  hg_top r := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
      Complex.isBigO_ofReal_left.mpr (isBigO_latticeTheta_sub_one_rpow z r)

@[simp] theorem latticeThetaFEPair_symm (z : UpperHalfPlane) :
    (latticeThetaFEPair z).symm = latticeThetaFEPair z := by
  unfold latticeThetaFEPair WeakFEPair.symm
  congr 1
  simp

/-- The entire, pole-subtracted completed scalar lattice function. -/
def completedLatticeEisenstein₀ (z : UpperHalfPlane) (s : ℂ) : ℂ :=
  (latticeThetaFEPair z).Λ₀ s / 2

/-- The actual theta-Mellin continuation, including the two prescribed simple poles. -/
def completedLatticeEisenstein (z : UpperHalfPlane) (s : ℂ) : ℂ :=
  (latticeThetaFEPair z).Λ s / 2

theorem differentiable_completedLatticeEisenstein₀ (z : UpperHalfPlane) :
    Differentiable ℂ (completedLatticeEisenstein₀ z) :=
  (latticeThetaFEPair z).differentiable_Λ₀.div_const 2

theorem completedLatticeEisenstein_eq (z : UpperHalfPlane) (s : ℂ) :
    completedLatticeEisenstein z s = completedLatticeEisenstein₀ z s -
      1 / (2 * s) - 1 / (2 * (1 - s)) := by
  simp only [completedLatticeEisenstein, completedLatticeEisenstein₀, WeakFEPair.Λ,
    latticeThetaFEPair, Complex.ofReal_one, smul_eq_mul, mul_one]
  simp only [one_div, mul_inv_rev]
  ring

theorem completedLatticeEisenstein_analyticAt (z : UpperHalfPlane) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (completedLatticeEisenstein z) s := by
  have heq : completedLatticeEisenstein z = fun w ↦ completedLatticeEisenstein₀ z w -
      1 / (2 * w) - 1 / (2 * (1 - w)) := funext (completedLatticeEisenstein_eq z)
  rw [heq]
  exact (((differentiable_completedLatticeEisenstein₀ z).analyticAt s).sub
    (analyticAt_const.div (analyticAt_const.mul analyticAt_id) (by simpa using hs0))).sub
      (analyticAt_const.div (analyticAt_const.mul (analyticAt_const.sub analyticAt_id))
        (by simpa using sub_ne_zero.mpr hs1.symm))

theorem completedLatticeEisenstein_functional_equation (z : UpperHalfPlane) (s : ℂ) :
    completedLatticeEisenstein z (1 - s) = completedLatticeEisenstein z s := by
  have h := (latticeThetaFEPair z).functional_equation s
  rw [latticeThetaFEPair_symm] at h
  change (latticeThetaFEPair z).Λ (1 - s) = 1 • (latticeThetaFEPair z).Λ s at h
  simpa only [one_smul, completedLatticeEisenstein] using congrArg (fun x : ℂ ↦ x / 2) h

theorem completedLatticeEisenstein_residue_one (z : UpperHalfPlane) :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedLatticeEisenstein z s)
      (𝓝[≠] 1) (𝓝 (1 / 2)) := by
  simpa only [latticeThetaFEPair, completedLatticeEisenstein, Complex.ofReal_one,
    smul_eq_mul, one_mul, mul_div_assoc] using
      (latticeThetaFEPair z).Λ_residue_k.div_const 2

theorem completedLatticeEisenstein_residue_zero (z : UpperHalfPlane) :
    Tendsto (fun s : ℂ ↦ s * completedLatticeEisenstein z s)
      (𝓝[≠] 0) (𝓝 (-(1 / 2))) := by
  simpa only [latticeThetaFEPair, completedLatticeEisenstein, smul_eq_mul,
    mul_div_assoc, neg_div] using (latticeThetaFEPair z).Λ_residue_zero.div_const 2

/-- The defining continuation equals the convergent Mellin transform in its original half-plane. -/
theorem completedLatticeEisenstein_hasMellin (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t ↦ (latticeTheta z t : ℂ) - 1) s
      (2 * completedLatticeEisenstein z s) := by
  simpa only [latticeThetaFEPair, completedLatticeEisenstein, mul_div_cancel₀ _ (by norm_num :
    (2 : ℂ) ≠ 0)] using (latticeThetaFEPair z).hasMellin hs

/-- Removing the actual zero row gives the Mellin integrand as a convergent Gaussian sum. -/
theorem hasSum_latticeTheta_sub_one (z : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    HasSum (fun v : Fin 2 → ℤ ↦ if latticeEnergy z v = 0 then (0 : ℂ)
      else Real.exp (-Real.pi * latticeEnergy z v * t)) ((latticeTheta z t : ℂ) - 1) := by
  classical
  have h := Complex.hasSum_ofReal.mpr (latticeTheta_hasSum z ht)
  have hsub := hasSum_ite_sub_hasSum h (0 : Fin 2 → ℤ)
  simp only [latticeThetaTerm_zero, Complex.ofReal_one] at hsub
  apply hsub.congr_fun
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · simp only [ite_eq_right hv, ne_of_gt (latticeEnergy_pos z hv), ite_false, latticeThetaTerm]
    congr 2
    ring

theorem summable_latticeEnergy_inv_rpow (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : Fin 2 → ℤ ↦ 1 / latticeEnergy z v ^ s.re) := by
  apply (summable_norm_latticeDirichletTerm z hs).congr
  intro v
  rw [latticeDirichletTerm, Complex.cpow_neg, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (latticeEnergy_nonneg z v)
      (ne_of_gt (lt_trans zero_lt_one hs)), one_div]

/-- The convergent theta Mellin transform has the exact gamma-factor lattice normalization. -/
theorem hasSum_completedLatticeEisenstein (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun v : Fin 2 → ℤ ↦ (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
      latticeDirichletTerm z s v) (2 * completedLatticeEisenstein z s) := by
  have h := hasSum_mellin_pi_mul₀ (a := fun _ : Fin 2 → ℤ ↦ (1 : ℂ))
    (p := latticeEnergy z) (F := fun t ↦ (latticeTheta z t : ℂ) - 1)
    (latticeEnergy_nonneg z) (lt_trans zero_lt_one hs)
    (by intro t ht; simpa only [one_mul] using hasSum_latticeTheta_sub_one z ht)
    (by simpa only [norm_one] using summable_latticeEnergy_inv_rpow z hs)
  rw [(completedLatticeEisenstein_hasMellin z hs).2] at h
  simpa only [mul_one, latticeDirichletTerm, Complex.cpow_neg, div_eq_mul_inv] using h

theorem completedLatticeEisenstein_eq_latticeDirichletSeries
    (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    completedLatticeEisenstein z s =
      (Real.pi : ℂ) ^ (-s) * Complex.Gamma s * latticeDirichletSeries z s / 2 := by
  have h := (hasSum_completedLatticeEisenstein z hs).tsum_eq
  rw [tsum_mul_left, ← latticeDirichletSeries_eq_tsum_all z hs] at h
  linear_combination -h / 2

/-- Exact identification with the original scalar Poincaré series in the common half-plane. -/
theorem completedLatticeEisenstein_eq_completedZeta_mul_poincare
    (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    completedLatticeEisenstein z s =
      completedRiemannZeta (2 * s) * complexPoincareSeries 0 0 s z := by
  rw [completedLatticeEisenstein_eq_latticeDirichletSeries z hs,
    latticeDirichletSeries_eq_two_zeta_mul_poincare z hs]
  have hs0 : 2 * s ≠ 0 := mul_ne_zero (by norm_num) (Complex.ne_zero_of_one_lt_re hs)
  have hgamma : Complex.Gammaℝ (2 * s) = (Real.pi : ℂ) ^ (-s) * Complex.Gamma s := by
    rw [Complex.Gammaℝ_def]
    congr 2 <;> ring
  have hgammanz : Complex.Gammaℝ (2 * s) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    norm_num [Complex.mul_re]
    linarith
  rw [riemannZeta_def_of_ne_zero hs0, ← hgamma]
  field_simp

/-- The canonical uncompleted scalar Eisenstein continuation, regular at the spectral threshold. -/
def scalarEisenstein (z : UpperHalfPlane) (s : ℂ) : ℂ :=
  completedLatticeEisenstein z s * spectralZetaReciprocal (2 * s)

/-- The entire functional-equation pair itself is unchanged by the modular action. -/
theorem latticeThetaFEPair_smul (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    latticeThetaFEPair (g • z) = latticeThetaFEPair z := by
  unfold latticeThetaFEPair
  simp only [latticeTheta_smul]

/-- Modularity of the continued completion follows from the actual theta integral. -/
theorem completedLatticeEisenstein_smul (g : SL(2, ℤ)) (z : UpperHalfPlane) (s : ℂ) :
    completedLatticeEisenstein (g • z) s = completedLatticeEisenstein z s := by
  simp only [completedLatticeEisenstein, latticeThetaFEPair_smul]

/-- The continued scalar Eisenstein family is fully modular at every parameter. -/
theorem scalarEisenstein_smul (g : SL(2, ℤ)) (z : UpperHalfPlane) (s : ℂ) :
    scalarEisenstein (g • z) s = scalarEisenstein z s := by
  simp only [scalarEisenstein, completedLatticeEisenstein_smul]

@[simp] theorem scalarEisenstein_half (z : UpperHalfPlane) :
    scalarEisenstein z (1 / 2) = 0 := by
  norm_num [scalarEisenstein]

theorem scalarEisenstein_analyticAt (z : UpperHalfPlane) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) : AnalyticAt ℂ (scalarEisenstein z) s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  exact (completedLatticeEisenstein_analyticAt z hs0 hs1).mul
    ((spectralZetaReciprocal_analyticAt (s := 2 * s) (by
      norm_num [Complex.mul_re]
      linarith)).comp (f := fun w : ℂ ↦ 2 * w) (analyticAt_const.mul analyticAt_id))

/-- In the convergence region the continued function is exactly the actual coset sum. -/
theorem scalarEisenstein_eq_complexPoincareSeries (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    scalarEisenstein z s = complexPoincareSeries 0 0 s z := by
  have h2re : 1 ≤ (2 * s).re := by
    norm_num [Complex.mul_re]
    linarith
  have h2s0 : 2 * s ≠ 0 := mul_ne_zero (by norm_num) (Complex.ne_zero_of_one_lt_re hs)
  have h2s1 : 2 * s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.mul_re] at hre
    linarith
  have hzeta : completedRiemannZeta (2 * s) ≠ 0 := by
    intro h
    apply riemannZeta_ne_zero_of_one_le_re h2re
    rw [riemannZeta_def_of_ne_zero h2s0, h, zero_div]
  rw [scalarEisenstein, completedLatticeEisenstein_eq_completedZeta_mul_poincare z hs,
    spectralZetaReciprocal_eq_inv h2s0 h2s1]
  field_simp

end GapFamily.Analytic
