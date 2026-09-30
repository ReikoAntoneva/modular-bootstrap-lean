import GapFamily.Analytic.Elliptic.ChartWeakGradientC1
import GapFamily.Analytic.Foundation.FiniteDerivativeAssembly

noncomputable section
namespace GapFamily.Analytic.EllipticSobolev
open Set MeasureTheory Homogenization ModularElliptic ChartWeakGradientC1
open scoped ContDiff

theorem hasFDerivAt_of_chart_h1 (z : ℂ) (V : Set (Vec 2)) (hV : IsOpen V)
    (uR uI : H1Function V) (f : ℂ → ℂ)
    (hf : ContinuousOn f (ellipticChart z '' V))
    (hv : (fun v => (uR v : ℂ) + (uI v : ℂ) * Complex.I) =ᵐ[volume.restrict V]
      (fun v => f (ellipticChart z v)))
    (g : Fin 2 → Vec 2 → ℂ) (hgc : ∀ i, ContinuousOn (g i) V)
    (hga : ∀ i, g i =ᵐ[volume.restrict V]
      (fun v => (uR.grad v i : ℂ) + (uI.grad v i : ℂ) * Complex.I))
    {x : ℂ} (hx : x ∈ ellipticChart z '' V) :
    HasFDerivAt f (complexGradientField (fun i w => g i ((ellipticChart z).symm w)) x) x := by
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
  apply hasFDerivAt_of_continuousOn_weak_gradient ((ellipticChart z).isOpenMap V hV)
    hf (continuousOn_complexGradientField hggc) ?_ hx
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


/-- A continuous real representative of an H1 function, with continuous actual
weak coordinate gradients, has the literal assembled Fréchet derivative. -/
theorem hasFDerivAt_real_of_h1 {U : Set (Vec 2)} (hU : IsOpen U)
    (u : H1Function U) (f : Vec 2 → ℝ) (hf : ContinuousOn f U)
    (hfu : f =ᵐ[volume.restrict U] u.toFun)
    (g : Fin 2 → Vec 2 → ℝ) (hg : ∀ i, ContinuousOn (g i) U)
    (hgu : ∀ i, g i =ᵐ[volume.restrict U] (fun v => u.grad v i))
    {x : Vec 2} (hx : x ∈ U) : HasFDerivAt f (realGradientField g x) x := by
  let u0 : H1Function U := {
    toFun := 0
    grad := 0
    memL2 := MemLp.zero
    gradMemL2 := fun _ => MemLp.zero
    hasWeakGradient := by intro i ψ hψ hc hs; simp }
  let F : ℂ → ℂ := fun w => (f ((ellipticChart 0).symm w) : ℂ)
  let G : Fin 2 → Vec 2 → ℂ := fun i v => (g i v : ℂ)
  have hF : ContinuousOn F (ellipticChart 0 '' U) := by
    apply Complex.continuous_ofReal.continuousOn.comp
      (hf.comp (ellipticChart 0).symm.continuous.continuousOn ?_) (fun _ _ => Set.mem_univ _)
    rintro w ⟨v, hv, rfl⟩
    simpa only [Homeomorph.symm_apply_apply] using hv
  have hval : (fun v => (u v : ℂ) + (u0 v : ℂ) * Complex.I) =ᵐ[volume.restrict U]
      (fun v => F (ellipticChart 0 v)) := by
    filter_upwards [hfu] with v hv
    simp only [u0, F, Homeomorph.symm_apply_apply, Pi.zero_apply,
      Complex.ofReal_zero, zero_mul, add_zero]
    exact congrArg Complex.ofReal hv.symm
  have hG (i : Fin 2) : ContinuousOn (G i) U :=
    Complex.continuous_ofReal.comp_continuousOn (hg i)
  have hGae (i : Fin 2) : G i =ᵐ[volume.restrict U]
      (fun v => (u.grad v i : ℂ) + (u0.grad v i : ℂ) * Complex.I) := by
    filter_upwards [hgu i] with v hv
    simp only [u0, G, Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero]
    exact congrArg Complex.ofReal hv
  have hcomplex := hasFDerivAt_of_chart_h1 0 U hU u u0 F hF hval G hG hGae
    (x := ellipticChart 0 x) ⟨x, hx, rfl⟩
  have hcomposed := (Complex.reCLM.hasFDerivAt).comp x
    (hcomplex.comp x (ellipticChart_hasFDerivAt 0 x))
  have hfun : (fun v : Vec 2 => (F (ellipticChart 0 v)).re) = f := by
    funext v
    simp only [F, Homeomorph.symm_apply_apply, Complex.ofReal_re]
  have hlinear : Complex.reCLM.comp
      ((complexGradientField (fun i w => G i ((ellipticChart 0).symm w))
        (ellipticChart 0 x)).comp ellipticChartLinear.toContinuousLinearMap) =
      realGradientField g x := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [complexGradientField, Homeomorph.symm_apply_apply]
    simp [G, realGradientField_apply, Fin.sum_univ_two, ellipticChartLinear_apply, mul_comm]
  simpa only [Function.comp_def, Complex.reCLM_apply, hfun, hlinear] using hcomposed

end GapFamily.Analytic.EllipticSobolev
