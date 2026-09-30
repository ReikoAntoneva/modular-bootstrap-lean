import GapFamily.Analytic.Elliptic.LocalWeakHessianApproximationCoordinate
import GapFamily.Analytic.Elliptic.LocalWeakHessianApproximationComplex
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticHessianComplex
import GapFamily.Analytic.Elliptic.RectangleTraceApproximation
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior

/-!
# Actual smooth approximation and continuity from two real weak Hessians

The given real Sobolev functions supply the literal real and imaginary value,
gradient, and Hessian fields. One concrete complex smoothing sequence has the
four required ordinary L² limits and yields a continuous representative on an
inner rectangle.
-/

noncomputable section

namespace GapFamily.Analytic.LocalWeakHessian

open Set MeasureTheory Homogenization Filter
open scoped ContDiff Topology ENNReal

variable {U : Set (Vec 2)}

/-- The literal complex value obtained from the two real Sobolev values. -/
def combinedValue (uR uI : H1Function U) (v : Vec 2) : ℂ :=
  (uR.toFun v : ℂ) + (uI.toFun v : ℂ) * Complex.I

/-- The literal complex weak gradient obtained from the two real gradients. -/
def combinedGradient (uR uI : H1Function U) (i : Fin 2) (v : Vec 2) : ℂ :=
  (uR.grad v i : ℂ) + (uI.grad v i : ℂ) * Complex.I

/-- The weak derivative in direction one of the actual direction-zero gradient. -/
def combinedMixedHessian {uR uI : H1Function U}
    (HR : HasWeakHessianOn U uR) (HI : HasWeakHessianOn U uI) (v : Vec 2) : ℂ :=
  (HR.hess 0 1 v : ℂ) + (HI.hess 0 1 v : ℂ) * Complex.I

@[simp] theorem combinedValue_re (uR uI : H1Function U) (v : Vec 2) :
    (combinedValue uR uI v).re = uR.toFun v := by simp [combinedValue]

@[simp] theorem combinedValue_im (uR uI : H1Function U) (v : Vec 2) :
    (combinedValue uR uI v).im = uI.toFun v := by simp [combinedValue]

@[simp] theorem combinedGradient_re (uR uI : H1Function U) (i : Fin 2) (v : Vec 2) :
    (combinedGradient uR uI i v).re = uR.grad v i := by simp [combinedGradient]

@[simp] theorem combinedGradient_im (uR uI : H1Function U) (i : Fin 2) (v : Vec 2) :
    (combinedGradient uR uI i v).im = uI.grad v i := by simp [combinedGradient]

@[simp] theorem combinedMixedHessian_re {uR uI : H1Function U}
    (HR : HasWeakHessianOn U uR) (HI : HasWeakHessianOn U uI) (v : Vec 2) :
    (combinedMixedHessian HR HI v).re = HR.hess 0 1 v := by simp [combinedMixedHessian]

@[simp] theorem combinedMixedHessian_im {uR uI : H1Function U}
    (HR : HasWeakHessianOn U uR) (HI : HasWeakHessianOn U uI) (v : Vec 2) :
    (combinedMixedHessian HR HI v).im = HI.hess 0 1 v := by simp [combinedMixedHessian]

theorem combinedValue_memLp (uR uI : H1Function U) :
    MemLp (combinedValue uR uI) 2 (volume.restrict U) :=
  ModularElliptic.memLp_complex_of_memLp_re_im uR.memL2 uI.memL2

theorem combinedGradient_memLp (uR uI : H1Function U) (i : Fin 2) :
    MemLp (combinedGradient uR uI i) 2 (volume.restrict U) :=
  ModularElliptic.memLp_complex_of_memLp_re_im (uR.gradMemL2 i) (uI.gradMemL2 i)

theorem combinedMixedHessian_memLp {uR uI : H1Function U}
    (HR : HasWeakHessianOn U uR) (HI : HasWeakHessianOn U uI) :
    MemLp (combinedMixedHessian HR HI) 2 (volume.restrict U) :=
  ModularElliptic.memLp_complex_of_memLp_re_im (HR.hess_memL2 0 1) (HI.hess_memL2 0 1)

/-- A strong L² limit remains strong on every smaller measurable or nonmeasurable set. -/
theorem tendsto_eLpNorm_pair_restrict {F : ℕ → Vec 2 → ℂ} {f : Vec 2 → ℂ}
    {R : Set (ℝ × ℝ)} (hRU : R ⊆ pairToVec ⁻¹' U)
    (hF : Tendsto (fun n => eLpNorm (F n - f) 2 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun q => F n (pairToVec q) - f (pairToVec q))
      2 (volume.restrict R)) atTop (𝓝 0) := by
  have hfull : Tendsto (fun n => eLpNorm
      (fun q => F n (pairToVec q) - f (pairToVec q))
      2 (volume.restrict (pairToVec ⁻¹' U))) atTop (𝓝 0) := by
    apply hF.congr'
    filter_upwards with n
    exact (eLpNorm_comp_pairToVec U (F n - f) 2).symm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfull
    (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hRU))

private theorem memLp_pair_restrict {f : Vec 2 → ℂ} {R : Set (ℝ × ℝ)}
    (hf : MemLp f 2 (volume.restrict U)) (hRU : R ⊆ pairToVec ⁻¹' U) :
    MemLp (fun q => f (pairToVec q)) 2 (volume.restrict R) :=
  ((memLp_comp_pairToVec_iff U f 2).mpr hf).mono_measure
    (Measure.restrict_mono_set volume hRU)

private theorem dx_comp_pairToVec {f : Vec 2 → ℂ} (hf : ContDiff ℝ ∞ f) :
    RectangleTrace.dx (fun q => f (pairToVec q)) =
      fun q => fderiv ℝ f (pairToVec q) (basisVec 0) := by
  funext q
  simpa only [RectangleTrace.dx, Matrix.cons_val_zero, basisVec] using
    fderiv_comp_pairToVec_basis hf q 0

private theorem dy_comp_pairToVec {f : Vec 2 → ℂ} (hf : ContDiff ℝ ∞ f) :
    RectangleTrace.dy (fun q => f (pairToVec q)) =
      fun q => fderiv ℝ f (pairToVec q) (basisVec 1) := by
  funext q
  simpa only [RectangleTrace.dy, Matrix.cons_val_one, Matrix.cons_val_zero, basisVec] using
    fderiv_comp_pairToVec_basis hf q 1

private theorem dxy_comp_pairToVec {f : Vec 2 → ℂ} (hf : ContDiff ℝ ∞ f) :
    RectangleTrace.dxy (fun q => f (pairToVec q)) =
      fun q => fderiv ℝ (fun v => fderiv ℝ f v (basisVec 0))
        (pairToVec q) (basisVec 1) := by
  funext q
  change fderiv ℝ (fun p => fderiv ℝ (fun p' => f (pairToVec p')) p (1, 0)) q (0, 1) = _
  simpa only [Matrix.cons_val_zero,
    Matrix.cons_val_one, basisVec] using second_fderiv_comp_pairToVec hf q 0 1

/-- Actual real weak Hessians construct one globally smooth sequence with all four
ordinary L² limits in pair coordinates, on any smaller observation set. -/
theorem exists_smooth_pair_four_convergence
    (hU : IsOpenBoundedConvexDomain U) (uR uI : H1Function U)
    (HR : HasWeakHessianOn U uR) (HI : HasWeakHessianOn U uI)
    {x0 : Vec 2} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    {R : Set (ℝ × ℝ)} (hRU : R ⊆ pairToVec ⁻¹' U) :
    ∃ F : ℕ → ℝ × ℝ → ℂ,
      (∀ n, ContDiff ℝ ∞ (F n)) ∧
      MemLp (fun q => combinedValue uR uI (pairToVec q)) 2 (volume.restrict R) ∧
      MemLp (fun q => combinedGradient uR uI 0 (pairToVec q)) 2 (volume.restrict R) ∧
      MemLp (fun q => combinedGradient uR uI 1 (pairToVec q)) 2 (volume.restrict R) ∧
      MemLp (fun q => combinedMixedHessian HR HI (pairToVec q)) 2 (volume.restrict R) ∧
      Tendsto (fun n => eLpNorm (F n - fun q => combinedValue uR uI (pairToVec q))
        2 (volume.restrict R)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (RectangleTrace.dx (F n) -
        fun q => combinedGradient uR uI 0 (pairToVec q)) 2 (volume.restrict R)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (RectangleTrace.dy (F n) -
        fun q => combinedGradient uR uI 1 (pairToVec q)) 2 (volume.restrict R)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (RectangleTrace.dxy (F n) -
        fun q => combinedMixedHessian HR HI (pairToVec q)) 2 (volume.restrict R)) atTop (𝓝 0) := by
  have hf := combinedValue_memLp uR uI
  have hg0 := combinedGradient_memLp uR uI 0
  have hg1 := combinedGradient_memLp uR uI 1
  have hh01 := combinedMixedHessian_memLp HR HI
  obtain ⟨h0, hx, hy, hxy⟩ := complexSmoothApprox_four_convergence hU hf hg0 hg1 hh01
    (by simpa only [combinedValue_re, combinedGradient_re] using uR.hasWeakGradient 0)
    (by simpa only [combinedValue_im, combinedGradient_im] using uI.hasWeakGradient 0)
    (by simpa only [combinedValue_re, combinedGradient_re] using uR.hasWeakGradient 1)
    (by simpa only [combinedValue_im, combinedGradient_im] using uI.hasWeakGradient 1)
    (by simpa only [combinedGradient_re, combinedMixedHessian_re] using HR.weak_second 0 1)
    (by simpa only [combinedGradient_im, combinedMixedHessian_im] using HI.weak_second 0 1)
    hball hr
  let F : ℕ → ℝ × ℝ → ℂ := fun n q =>
    complexSmoothApprox U (combinedValue uR uI) x0 r n (pairToVec q)
  have hF (n : ℕ) : ContDiff ℝ ∞ (F n) :=
    (complexSmoothApprox_contDiff hU hf hr n).comp pairToVec.contDiff
  have hdx (n : ℕ) : RectangleTrace.dx (F n) = fun q =>
      fderiv ℝ (complexSmoothApprox U (combinedValue uR uI) x0 r n) (pairToVec q)
        (basisVec 0) := dx_comp_pairToVec (complexSmoothApprox_contDiff hU hf hr n)
  have hdy (n : ℕ) : RectangleTrace.dy (F n) = fun q =>
      fderiv ℝ (complexSmoothApprox U (combinedValue uR uI) x0 r n) (pairToVec q)
        (basisVec 1) := dy_comp_pairToVec (complexSmoothApprox_contDiff hU hf hr n)
  have hdxy (n : ℕ) : RectangleTrace.dxy (F n) = fun q =>
      fderiv ℝ (fun v => fderiv ℝ (complexSmoothApprox U (combinedValue uR uI) x0 r n)
        v (basisVec 0)) (pairToVec q) (basisVec 1) :=
    dxy_comp_pairToVec (complexSmoothApprox_contDiff hU hf hr n)
  refine ⟨F, hF, memLp_pair_restrict hf hRU, memLp_pair_restrict hg0 hRU,
    memLp_pair_restrict hg1 hRU, memLp_pair_restrict hh01 hRU, ?_, ?_, ?_, ?_⟩
  · exact tendsto_eLpNorm_pair_restrict hRU h0
  · apply (tendsto_eLpNorm_pair_restrict hRU hx).congr'
    filter_upwards with n
    congr 1
    funext q
    simp only [Pi.sub_apply, hdx]
  · apply (tendsto_eLpNorm_pair_restrict hRU hy).congr'
    filter_upwards with n
    congr 1
    funext q
    simp only [Pi.sub_apply, hdy]
  · apply (tendsto_eLpNorm_pair_restrict hRU hxy).congr'
    filter_upwards with n
    congr 1
    funext q
    simp only [Pi.sub_apply, hdxy]

/-- Two actual weak Hessians yield a continuous representative on every
nondegenerate inner rectangle strictly contained in the coordinate domain. -/
theorem exists_continuousOn_pair_of_weakHessian
    (hU : IsOpenBoundedConvexDomain U) (uR uI : H1Function U)
    (HR : HasWeakHessianOn U uR) (HI : HasWeakHessianOn U uI)
    {x0 : Vec 2} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    {A B C D h k : ℝ} (hRU : Icc A B ×ˢ Icc C D ⊆ pairToVec ⁻¹' U)
    (hh : 0 < h) (hk : 0 < k) (hAB : A < B - h) (hCD : C < D - k) :
    ∃ g : ℝ × ℝ → ℂ,
      ContinuousOn g (Icc A (B - h) ×ˢ Icc C (D - k)) ∧
      g =ᵐ[volume.restrict (Icc A (B - h) ×ˢ Icc C (D - k))]
        (fun q => combinedValue uR uI (pairToVec q)) := by
  obtain ⟨F, hF, hf, hfx, hfy, hfxy, h0, hx, hy, hxy⟩ :=
    exists_smooth_pair_four_convergence hU uR uI HR HI hball hr hRU
  obtain ⟨g, hgc, _hgu, hgf⟩ := RectangleTrace.exists_continuousOn_ae_eq_of_four_eLpNorm
    F (fun n => (hF n).of_le (by simp)) _ _ _ _ hh hk hAB hCD
    hf hfx hfy hfxy h0 hx hy hxy
  exact ⟨g, hgc, hgf⟩

end GapFamily.Analytic.LocalWeakHessian
