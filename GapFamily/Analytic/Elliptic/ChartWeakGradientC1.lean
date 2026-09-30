import GapFamily.Analytic.Elliptic.ContinuousWeakDerivative
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticChartWeak
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticHessianComplex
import Homogenization.Sobolev.H1.Definitions

noncomputable section
namespace GapFamily.Analytic.ChartWeakGradientC1
open Set MeasureTheory Homogenization ModularElliptic
open scoped ContDiff

def complexGradientField (g : Fin 2 → ℂ → ℂ) (w : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (g 0 w) + Complex.imCLM.smulRight (g 1 w)

theorem continuousOn_complexGradientField {V : Set ℂ} {g : Fin 2 → ℂ → ℂ}
    (hg : ∀ i, ContinuousOn (g i) V) : ContinuousOn (complexGradientField g) V := by
  exact (((ContinuousLinearMap.smulRightL ℝ ℂ ℂ) Complex.reCLM).continuous.continuousOn.comp
    (hg 0) (fun _ _ => Set.mem_univ _)).add
    (((ContinuousLinearMap.smulRightL ℝ ℂ ℂ) Complex.imCLM).continuous.continuousOn.comp
    (hg 1) (fun _ _ => Set.mem_univ _))

theorem weak_gradient_of_two_partials {V : Set ℂ} {f : ℂ → ℂ} {g : Fin 2 → ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict V))
    (hg : ∀ i, MemLp (g i) 2 (volume.restrict V))
    (hw : ∀ (i : Fin 2) (ψ : ℂ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ V →
      (∫ w in V, f w * (fderiv ℝ ψ w (![1, Complex.I] i) : ℂ)) =
        -(∫ w in V, g i w * (ψ w : ℂ)))
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ V) (v : ℂ) :
    (∫ w : ℂ, fderiv ℝ ψ w v • f w) =
      -(∫ w : ℂ, ψ w • complexGradientField g w v) := by
  have hD (e : ℂ) : IntegrableOn (fun w => f w * (fderiv ℝ ψ w e : ℂ)) V :=
    complex_mul_real_test_integrable hf _
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ e)
  have hgi (i : Fin 2) : IntegrableOn (fun w => g i w * (ψ w : ℂ)) V :=
    complex_mul_real_test_integrable (hg i) _ hψ.continuous hc
  have hzeroL : ∀ w, w ∉ V → fderiv ℝ ψ w v • f w = 0 := by
    intro w hw
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hw (hs h))]
    simp
  have hzeroR : ∀ w, w ∉ V → ψ w • complexGradientField g w v = 0 := by
    intro w hw
    rw [image_eq_zero_of_notMem_tsupport (fun h => hw (hs h)), zero_smul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzeroL,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzeroR]
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im v).symm
  have hleft : (∫ w in V, fderiv ℝ ψ w v • f w) =
      (v.re : ℂ) * (∫ w in V, f w * (fderiv ℝ ψ w 1 : ℂ)) +
      (v.im : ℂ) * (∫ w in V, f w * (fderiv ℝ ψ w Complex.I : ℂ)) := by
    calc
      _ = ∫ w in V, ((v.re : ℂ) * (f w * (fderiv ℝ ψ w 1 : ℂ)) +
          (v.im : ℂ) * (f w * (fderiv ℝ ψ w Complex.I : ℂ))) := by
        congr 1
        funext w
        conv_lhs => rw [hv]
        rw [map_add, map_smul, map_smul]
        simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul]
        ring
      _ = _ := by rw [integral_add ((hD 1).const_mul _) ((hD Complex.I).const_mul _),
        integral_const_mul, integral_const_mul]
  have hright : (∫ w in V, ψ w • complexGradientField g w v) =
      (v.re : ℂ) * (∫ w in V, g 0 w * (ψ w : ℂ)) +
      (v.im : ℂ) * (∫ w in V, g 1 w * (ψ w : ℂ)) := by
    calc
      _ = ∫ w in V, ((v.re : ℂ) * (g 0 w * (ψ w : ℂ)) +
          (v.im : ℂ) * (g 1 w * (ψ w : ℂ))) := by
        congr 1
        funext w
        simp only [complexGradientField, add_apply,
          ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.imCLM_apply,
          Complex.real_smul]
        ring
      _ = _ := by rw [integral_add ((hgi 0).const_mul _) ((hgi 1).const_mul _),
        integral_const_mul, integral_const_mul]
  have h0 := hw 0 ψ hψ hc hs
  have h1 := hw 1 ψ hψ hc hs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [hleft, hright, h0, h1]
  ring

/-- Continuous representatives of the actual coordinate gradients identify a
continuous chart-H1 value as a genuinely C1 function. -/
theorem contDiffOn_one_of_chart_h1 (z : ℂ) (V : Set (Vec 2)) (hV : IsOpen V)
    (uR uI : H1Function V) (f : ℂ → ℂ)
    (hf : ContinuousOn f (ellipticChart z '' V))
    (hv : (fun v => (uR v : ℂ) + (uI v : ℂ) * Complex.I) =ᵐ[volume.restrict V]
      (fun v => f (ellipticChart z v)))
    (g : Fin 2 → Vec 2 → ℂ) (hgc : ∀ i, ContinuousOn (g i) V)
    (hga : ∀ i, g i =ᵐ[volume.restrict V]
      (fun v => (uR.grad v i : ℂ) + (uI.grad v i : ℂ) * Complex.I)) :
    ContDiffOn ℝ 1 f (ellipticChart z '' V) := by
  let F : Vec 2 → ℂ := fun v => (uR v : ℂ) + (uI v : ℂ) * Complex.I
  let D : Fin 2 → Vec 2 → ℂ := fun i v =>
    (uR.grad v i : ℂ) + (uI.grad v i : ℂ) * Complex.I
  let gg : Fin 2 → ℂ → ℂ := fun i w => g i ((ellipticChart z).symm w)
  let W := ellipticChart z '' V
  have hinv := (ellipticChart_measurePreserving_restrict_image z V).symm
    (ellipticChart z).toMeasurableEquiv
  have hFae : (fun w => F ((ellipticChart z).symm w)) =ᵐ[volume.restrict W] f := by
    filter_upwards [hinv.quasiMeasurePreserving.ae hv] with w hw
    change F ((ellipticChart z).symm w) = f ((ellipticChart z) ((ellipticChart z).symm w)) at hw
    simpa only [Homeomorph.apply_symm_apply] using hw
  have hDae (i : Fin 2) : gg i =ᵐ[volume.restrict W]
      (fun w => D i ((ellipticChart z).symm w)) :=
    hinv.quasiMeasurePreserving.ae (hga i)
  have hFmem : MemLp F 2 (volume.restrict V) :=
    memLp_complex_of_memLp_re_im uR.memL2 uI.memL2
  have hDmem (i : Fin 2) : MemLp (D i) 2 (volume.restrict V) :=
    memLp_complex_of_memLp_re_im (uR.gradMemL2 i) (uI.gradMemL2 i)
  have hfmem : MemLp f 2 (volume.restrict W) :=
    MemLp.ae_eq hFae (memLp_ellipticChart_symm_image z V F 2 hFmem)
  have hgmem (i : Fin 2) : MemLp (gg i) 2 (volume.restrict W) :=
    MemLp.ae_eq (hDae i).symm (memLp_ellipticChart_symm_image z V (D i) 2 (hDmem i))
  have hggc (i : Fin 2) : ContinuousOn (gg i) W := by
    apply (hgc i).comp (ellipticChart z).symm.continuous.continuousOn
    rintro w ⟨v, hv, rfl⟩
    simpa only [Homeomorph.symm_apply_apply] using hv
  apply contDiffOn_one_of_continuousOn_weak_gradient ((ellipticChart z).isOpenMap V hV)
    hf (continuousOn_complexGradientField hggc)
  apply weak_gradient_of_two_partials hfmem hgmem
  intro i ψ hψ hc hs
  have hR : HasWeakPartialDerivOn V i (fun v => (F v).re) (fun v => (D i v).re) := by
    simpa [F, D] using uR.hasWeakGradient i
  have hI : HasWeakPartialDerivOn V i (fun v => (F v).im) (fun v => (D i v).im) := by
    simpa [F, D] using uI.hasWeakGradient i
  have hh := weakPartial_ellipticChart_image z V i F (D i)
    (complex_hasWeakPartialDerivOn i hFmem (hDmem i) hR hI) ψ hψ hc hs
  calc
    (∫ w in W, f w * (fderiv ℝ ψ w (![1, Complex.I] i) : ℂ)) =
        ∫ w in W, F ((ellipticChart z).symm w) *
          (fderiv ℝ ψ w (![1, Complex.I] i) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hFae] with w hw
      rw [hw]
    _ = -(∫ w in W, D i ((ellipticChart z).symm w) * (ψ w : ℂ)) := hh
    _ = -(∫ w in W, gg i w * (ψ w : ℂ)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hDae i] with w hw
      rw [hw]

end GapFamily.Analytic.ChartWeakGradientC1
