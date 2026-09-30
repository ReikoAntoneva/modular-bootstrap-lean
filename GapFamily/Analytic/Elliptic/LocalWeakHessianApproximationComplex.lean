import GapFamily.Analytic.Elliptic.LocalWeakHessianApproximationLp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# One complex smooth approximation of an actual weak Hessian

Real and imaginary parts use the same normalized smoothing and the same scale.
The first and mixed classical derivatives of that one sequence converge in ordinary
L² to the given actual weak derivative fields.
-/

noncomputable section
namespace GapFamily.Analytic.LocalWeakHessian

open Set MeasureTheory Filter Homogenization
open scoped ENNReal Topology ContDiff

/-- The literal recombination of the two real smooth approximations. -/
def complexSmoothApprox {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℂ)
    (x0 : Vec d) (r : ℝ) (n : ℕ) : Vec d → ℂ := fun x =>
  (smoothApprox U (fun v => (f v).re) x0 r n x : ℂ) +
    (smoothApprox U (fun v => (f v).im) x0 r n x : ℂ) * Complex.I

@[simp] theorem complexSmoothApprox_re {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℂ)
    (x0 : Vec d) (r : ℝ) (n : ℕ) (x : Vec d) :
    (complexSmoothApprox U f x0 r n x).re = smoothApprox U (fun v => (f v).re) x0 r n x := by
  simp [complexSmoothApprox]

@[simp] theorem complexSmoothApprox_im {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℂ)
    (x0 : Vec d) (r : ℝ) (n : ℕ) (x : Vec d) :
    (complexSmoothApprox U f x0 r n x).im = smoothApprox U (fun v => (f v).im) x0 r n x := by
  simp [complexSmoothApprox]

variable {d : ℕ} {U : Set (Vec d)} {f gi hij : Vec d → ℂ}
  {x0 : Vec d} {r : ℝ}

private theorem complex_memLp_re (hf : MemLp f 2 (volume.restrict U)) :
    MemLpOn U 2 (fun x => (f x).re) := by
  simpa only [Function.comp_def, Complex.reCLM_apply] using Complex.reCLM.comp_memLp' hf

private theorem complex_memLp_im (hf : MemLp f 2 (volume.restrict U)) :
    MemLpOn U 2 (fun x => (f x).im) := by
  simpa only [Function.comp_def, Complex.imCLM_apply] using Complex.imCLM.comp_memLp' hf

theorem complexSmoothApprox_contDiff (hU : IsOpenBoundedConvexDomain U)
    (hf : MemLp f 2 (volume.restrict U)) (hr : 0 < r) (n : ℕ) :
    ContDiff ℝ ∞ (complexSmoothApprox U f x0 r n) :=
  (Complex.ofRealCLM.contDiff.comp (smoothApprox_contDiff (x0 := x0) hU (complex_memLp_re hf) hr n)).add
    ((Complex.ofRealCLM.contDiff.comp (smoothApprox_contDiff (x0 := x0) hU (complex_memLp_im hf) hr n)).mul contDiff_const)

theorem complexSmoothApprox_memLp (hU : IsOpenBoundedConvexDomain U)
    (hf : MemLp f 2 (volume.restrict U))
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (n : ℕ) :
    MemLp (complexSmoothApprox U f x0 r n) 2 (volume.restrict U) := by
  have hR : MemLp (fun x => (smoothApprox U (fun v => (f v).re) x0 r n x : ℂ))
      2 (volume.restrict U) :=
    (smoothApprox_memLp hU (complex_memLp_re hf) hball hr n).ofReal
  have hI : MemLp (fun x => (smoothApprox U (fun v => (f v).im) x0 r n x : ℂ))
      2 (volume.restrict U) :=
    (smoothApprox_memLp hU (complex_memLp_im hf) hball hr n).ofReal
  simpa only [complexSmoothApprox, Pi.add_def] using! hR.add (hI.mul_const Complex.I)

private theorem fderiv_recombine {R J : Vec d → ℝ} {x v : Vec d}
    (hR : DifferentiableAt ℝ R x) (hJ : DifferentiableAt ℝ J x) :
    fderiv ℝ (fun y => (R y : ℂ) + (J y : ℂ) * Complex.I) x v =
      (fderiv ℝ R x v : ℂ) + (fderiv ℝ J x v : ℂ) * Complex.I := by
  have hRc := Complex.ofRealCLM.hasFDerivAt.comp x hR.hasFDerivAt
  have hJc := Complex.ofRealCLM.hasFDerivAt.comp x hJ.hasFDerivAt
  simpa only [Pi.add_def, Function.comp_def, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, mul_comm] using
    congrArg (fun L => L v) (hRc.add (hJc.mul_const Complex.I)).fderiv

/-- Exact first derivative of the common complex approximation on the original domain. -/
theorem complexSmoothApprox_fderiv_basis (hU : IsOpenBoundedConvexDomain U)
    (hf : MemLp f 2 (volume.restrict U)) (hgi : MemLp gi 2 (volume.restrict U))
    {i : Fin d}
    (hR : HasWeakPartialDerivOn U i (fun x => (f x).re) (fun x => (gi x).re))
    (hI : HasWeakPartialDerivOn U i (fun x => (f x).im) (fun x => (gi x).im))
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (n : ℕ)
    {x : Vec d} (hx : x ∈ U) :
    fderiv ℝ (complexSmoothApprox U f x0 r n) x (basisVec i) =
      (1 - smoothApproxScale n) • complexSmoothApprox U gi x0 r n x := by
  unfold complexSmoothApprox
  rw [fderiv_recombine
    ((smoothApprox_contDiff (x0 := x0) hU (complex_memLp_re hf) hr n).differentiable (by simp) x)
    ((smoothApprox_contDiff (x0 := x0) hU (complex_memLp_im hf) hr n).differentiable (by simp) x)]
  rw [smoothApprox_fderiv_basis hU (complex_memLp_re hf) (complex_memLp_re hgi) hR hball hr n hx,
    smoothApprox_fderiv_basis hU (complex_memLp_im hf) (complex_memLp_im hgi) hI hball hr n hx]
  simp [Complex.real_smul, Complex.ofReal_mul, mul_assoc]

/-- Exact mixed derivative; no derivative of the Hessian field is assumed. -/
theorem complexSmoothApprox_second_fderiv_basis (hU : IsOpenBoundedConvexDomain U)
    (hf : MemLp f 2 (volume.restrict U)) (hgi : MemLp gi 2 (volume.restrict U))
    (hhij : MemLp hij 2 (volume.restrict U)) {i j : Fin d}
    (hR : HasWeakPartialDerivOn U i (fun x => (f x).re) (fun x => (gi x).re))
    (hI : HasWeakPartialDerivOn U i (fun x => (f x).im) (fun x => (gi x).im))
    (hR' : HasWeakPartialDerivOn U j (fun x => (gi x).re) (fun x => (hij x).re))
    (hI' : HasWeakPartialDerivOn U j (fun x => (gi x).im) (fun x => (hij x).im))
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (n : ℕ)
    {x : Vec d} (hx : x ∈ U) :
    fderiv ℝ (fun y => fderiv ℝ (complexSmoothApprox U f x0 r n) y (basisVec i))
        x (basisVec j) =
      (1 - smoothApproxScale n) ^ 2 • complexSmoothApprox U hij x0 r n x := by
  have heq : (fun y => fderiv ℝ (complexSmoothApprox U f x0 r n) y (basisVec i))
      =ᶠ[𝓝 x] (fun y => (1 - smoothApproxScale n) • complexSmoothApprox U gi x0 r n y) := by
    filter_upwards [hU.isOpen.mem_nhds hx] with y hy
    exact complexSmoothApprox_fderiv_basis hU hf hgi hR hI hball hr n hy
  rw [heq.fderiv_eq]
  change fderiv ℝ ((1 - smoothApproxScale n) • complexSmoothApprox U gi x0 r n)
    x (basisVec j) = _
  rw [(((complexSmoothApprox_contDiff (x0 := x0) hU hgi hr n).differentiable (by simp) x).hasFDerivAt.const_smul
      (1 - smoothApproxScale n)).fderiv]
  simp only [smul_apply,
    complexSmoothApprox_fderiv_basis hU hgi hhij hR' hI' hball hr n hx,
    smul_smul, pow_two]

/-- The complex norm is controlled by the two genuine scalar L² norms. -/
private theorem eLpNorm_le_re_add_im {g : Vec d → ℂ}
    (hg : MemLp g 2 (volume.restrict U)) :
    eLpNorm g 2 (volume.restrict U) ≤
      eLpNorm (fun x => (g x).re) 2 (volume.restrict U) +
        eLpNorm (fun x => (g x).im) 2 (volume.restrict U) := by
  have hR : MemLp (fun x => ((g x).re : ℂ)) 2 (volume.restrict U) := (complex_memLp_re hg).ofReal
  have hI : MemLp (fun x => ((g x).im : ℂ) * Complex.I) 2 (volume.restrict U) :=
    (complex_memLp_im hg).ofReal.mul_const Complex.I
  have hRn : eLpNorm (fun x => ((g x).re : ℂ)) 2 (volume.restrict U) =
      eLpNorm (fun x => (g x).re) 2 (volume.restrict U) :=
    eLpNorm_congr_norm_ae hR.aestronglyMeasurable (complex_memLp_re hg).aestronglyMeasurable
      (Eventually.of_forall fun x => Complex.norm_real _)
  have hIn : eLpNorm (fun x => ((g x).im : ℂ) * Complex.I) 2 (volume.restrict U) =
      eLpNorm (fun x => (g x).im) 2 (volume.restrict U) := by
    apply eLpNorm_congr_norm_ae hI.aestronglyMeasurable (complex_memLp_im hg).aestronglyMeasurable
    filter_upwards with x
    simp [Complex.norm_real]
  have heq : g = (fun x => ((g x).re : ℂ)) + (fun x => ((g x).im : ℂ) * Complex.I) := by
    funext x
    exact (Complex.re_add_im (g x)).symm
  nth_rw 1 [heq]
  exact (eLpNorm_add_le (by norm_num)).trans_eq (congrArg₂ (· + ·) hRn hIn)

private theorem tendsto_eLpNorm_complex_sub_of_re_im {F : ℕ → Vec d → ℂ}
    (hF : ∀ n, MemLp (F n) 2 (volume.restrict U)) (hf : MemLp f 2 (volume.restrict U))
    (hR : Tendsto (fun n => eLpNorm (fun x => (F n x).re - (f x).re)
      2 (volume.restrict U)) atTop (𝓝 0))
    (hI : Tendsto (fun n => eLpNorm (fun x => (F n x).im - (f x).im)
      2 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => F n x - f x) 2 (volume.restrict U)) atTop (𝓝 0) := by
  have hsum := hR.add hI
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  simpa only [Pi.sub_def, Complex.sub_re, Complex.sub_im] using
    eLpNorm_le_re_add_im ((hF n).sub hf)

/-- Value convergence of the one explicit complex sequence. -/
theorem tendsto_eLpNorm_complexSmoothApprox_sub (hU : IsOpenBoundedConvexDomain U)
    (hf : MemLp f 2 (volume.restrict U))
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto (fun n => eLpNorm (fun x => complexSmoothApprox U f x0 r n x - f x)
      2 (volume.restrict U)) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_complex_sub_of_re_im (complexSmoothApprox_memLp hU hf hball hr) hf
  · simpa only [complexSmoothApprox_re] using tendsto_eLpNorm_smoothApprox_sub hU (complex_memLp_re hf) hball hr
  · simpa only [complexSmoothApprox_im] using tendsto_eLpNorm_smoothApprox_sub hU (complex_memLp_im hf) hball hr

private theorem tendsto_eLpNorm_one_sub_smul_complexSmoothApprox_sub
    (hU : IsOpenBoundedConvexDomain U) (hf : MemLp f 2 (volume.restrict U))
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto (fun n => eLpNorm
      (fun x => (1 - smoothApproxScale n) • complexSmoothApprox U f x0 r n x - f x)
      2 (volume.restrict U)) atTop (𝓝 0) := by
  refine tendsto_eLpNorm_complex_sub_of_re_im
    (F := fun n x => (1 - smoothApproxScale n) • complexSmoothApprox U f x0 r n x)
    (fun n => (complexSmoothApprox_memLp hU hf hball hr n).const_smul
      (1 - smoothApproxScale n)) hf ?_ ?_
  · simpa only [Complex.smul_re, complexSmoothApprox_re, smul_eq_mul] using
      tendsto_eLpNorm_one_sub_mul_smoothApprox_sub hU (complex_memLp_re hf) hball hr
  · simpa only [Complex.smul_im, complexSmoothApprox_im, smul_eq_mul] using
      tendsto_eLpNorm_one_sub_mul_smoothApprox_sub hU (complex_memLp_im hf) hball hr

private theorem tendsto_eLpNorm_one_sub_sq_smul_complexSmoothApprox_sub
    (hU : IsOpenBoundedConvexDomain U) (hf : MemLp f 2 (volume.restrict U))
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto (fun n => eLpNorm
      (fun x => (1 - smoothApproxScale n) ^ 2 • complexSmoothApprox U f x0 r n x - f x)
      2 (volume.restrict U)) atTop (𝓝 0) := by
  refine tendsto_eLpNorm_complex_sub_of_re_im
    (F := fun n x => (1 - smoothApproxScale n) ^ 2 • complexSmoothApprox U f x0 r n x)
    (fun n => (complexSmoothApprox_memLp hU hf hball hr n).const_smul
      ((1 - smoothApproxScale n) ^ 2)) hf ?_ ?_
  · simpa only [Complex.smul_re, complexSmoothApprox_re, smul_eq_mul] using
      tendsto_eLpNorm_one_sub_sq_mul_smoothApprox_sub hU (complex_memLp_re hf) hball hr
  · simpa only [Complex.smul_im, complexSmoothApprox_im, smul_eq_mul] using
      tendsto_eLpNorm_one_sub_sq_mul_smoothApprox_sub hU (complex_memLp_im hf) hball hr

theorem complexSmoothApprox_fderiv_memLp (hU : IsOpenBoundedConvexDomain U)
    (hf : MemLp f 2 (volume.restrict U)) (hgi : MemLp gi 2 (volume.restrict U)) {i : Fin d}
    (hR : HasWeakPartialDerivOn U i (fun x => (f x).re) (fun x => (gi x).re))
    (hI : HasWeakPartialDerivOn U i (fun x => (f x).im) (fun x => (gi x).im))
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (n : ℕ) :
    MemLp (fun x => fderiv ℝ (complexSmoothApprox U f x0 r n) x (basisVec i))
      2 (volume.restrict U) := by
  apply ((complexSmoothApprox_memLp hU hgi hball hr n).const_smul
    (1 - smoothApproxScale n)).ae_eq
  filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
  exact (complexSmoothApprox_fderiv_basis hU hf hgi hR hI hball hr n hx).symm

theorem tendsto_eLpNorm_complexSmoothApprox_fderiv_sub (hU : IsOpenBoundedConvexDomain U)
    (hf : MemLp f 2 (volume.restrict U)) (hgi : MemLp gi 2 (volume.restrict U)) {i : Fin d}
    (hR : HasWeakPartialDerivOn U i (fun x => (f x).re) (fun x => (gi x).re))
    (hI : HasWeakPartialDerivOn U i (fun x => (f x).im) (fun x => (gi x).im))
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (complexSmoothApprox U f x0 r n) x (basisVec i) - gi x)
      2 (volume.restrict U)) atTop (𝓝 0) := by
  apply (tendsto_eLpNorm_one_sub_smul_complexSmoothApprox_sub hU hgi hball hr).congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
  rw [complexSmoothApprox_fderiv_basis hU hf hgi hR hI hball hr n hx]

theorem complexSmoothApprox_second_fderiv_memLp (hU : IsOpenBoundedConvexDomain U)
    (hf : MemLp f 2 (volume.restrict U)) (hgi : MemLp gi 2 (volume.restrict U))
    (hhij : MemLp hij 2 (volume.restrict U)) {i j : Fin d}
    (hR : HasWeakPartialDerivOn U i (fun x => (f x).re) (fun x => (gi x).re))
    (hI : HasWeakPartialDerivOn U i (fun x => (f x).im) (fun x => (gi x).im))
    (hR' : HasWeakPartialDerivOn U j (fun x => (gi x).re) (fun x => (hij x).re))
    (hI' : HasWeakPartialDerivOn U j (fun x => (gi x).im) (fun x => (hij x).im))
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (n : ℕ) :
    MemLp (fun x => fderiv ℝ
      (fun y => fderiv ℝ (complexSmoothApprox U f x0 r n) y (basisVec i)) x (basisVec j))
      2 (volume.restrict U) := by
  apply ((complexSmoothApprox_memLp hU hhij hball hr n).const_smul
    ((1 - smoothApproxScale n) ^ 2)).ae_eq
  filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
  exact (complexSmoothApprox_second_fderiv_basis hU hf hgi hhij hR hI hR' hI' hball hr n hx).symm

theorem tendsto_eLpNorm_complexSmoothApprox_second_fderiv_sub
    (hU : IsOpenBoundedConvexDomain U)
    (hf : MemLp f 2 (volume.restrict U)) (hgi : MemLp gi 2 (volume.restrict U))
    (hhij : MemLp hij 2 (volume.restrict U)) {i j : Fin d}
    (hR : HasWeakPartialDerivOn U i (fun x => (f x).re) (fun x => (gi x).re))
    (hI : HasWeakPartialDerivOn U i (fun x => (f x).im) (fun x => (gi x).im))
    (hR' : HasWeakPartialDerivOn U j (fun x => (gi x).re) (fun x => (hij x).re))
    (hI' : HasWeakPartialDerivOn U j (fun x => (gi x).im) (fun x => (hij x).im))
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (fun y => fderiv ℝ (complexSmoothApprox U f x0 r n) y (basisVec i))
        x (basisVec j) - hij x) 2 (volume.restrict U)) atTop (𝓝 0) := by
  apply (tendsto_eLpNorm_one_sub_sq_smul_complexSmoothApprox_sub hU hhij hball hr).congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
  rw [complexSmoothApprox_second_fderiv_basis hU hf hgi hhij hR hI hR' hI' hball hr n hx]

/-- All four limits belong to the same actual complex smooth sequence. -/
theorem complexSmoothApprox_four_convergence
    {U : Set (Vec 2)} {f g0 g1 h01 : Vec 2 → ℂ} {x0 : Vec 2} {r : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hf : MemLp f 2 (volume.restrict U)) (hg0 : MemLp g0 2 (volume.restrict U))
    (hg1 : MemLp g1 2 (volume.restrict U)) (hh01 : MemLp h01 2 (volume.restrict U))
    (hwR0 : HasWeakPartialDerivOn U 0 (fun x => (f x).re) (fun x => (g0 x).re))
    (hwI0 : HasWeakPartialDerivOn U 0 (fun x => (f x).im) (fun x => (g0 x).im))
    (hwR1 : HasWeakPartialDerivOn U 1 (fun x => (f x).re) (fun x => (g1 x).re))
    (hwI1 : HasWeakPartialDerivOn U 1 (fun x => (f x).im) (fun x => (g1 x).im))
    (hwR01 : HasWeakPartialDerivOn U 1 (fun x => (g0 x).re) (fun x => (h01 x).re))
    (hwI01 : HasWeakPartialDerivOn U 1 (fun x => (g0 x).im) (fun x => (h01 x).im))
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto (fun n => eLpNorm (fun x => complexSmoothApprox U f x0 r n x - f x)
      2 (volume.restrict U)) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (complexSmoothApprox U f x0 r n) x (basisVec 0) - g0 x)
      2 (volume.restrict U)) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (complexSmoothApprox U f x0 r n) x (basisVec 1) - g1 x)
      2 (volume.restrict U)) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (fun y => fderiv ℝ (complexSmoothApprox U f x0 r n) y (basisVec 0))
        x (basisVec 1) - h01 x) 2 (volume.restrict U)) atTop (𝓝 0) :=
  ⟨tendsto_eLpNorm_complexSmoothApprox_sub hU hf hball hr,
    tendsto_eLpNorm_complexSmoothApprox_fderiv_sub hU hf hg0 hwR0 hwI0 hball hr,
    tendsto_eLpNorm_complexSmoothApprox_fderiv_sub hU hf hg1 hwR1 hwI1 hball hr,
    tendsto_eLpNorm_complexSmoothApprox_second_fderiv_sub
      hU hf hg0 hh01 hwR0 hwI0 hwR01 hwI01 hball hr⟩

end GapFamily.Analytic.LocalWeakHessian
