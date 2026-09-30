import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdJet
import GapFamily.Analytic.Poincare.PoincareHighCuspH1
import Homogenization.Sobolev.H1.Algebra.H1Function

/-! Actual local H1 values for the global full threshold seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdJet
open Set Filter MeasureTheory UpperHalfPlane ModularGradient Homogenization
  PoincareCanonical PoincareHighCusp LocalPoisson
open scoped ContDiff Topology

/-- The actual residual L² value plus the smooth high term equals the literal
canonical seed almost everywhere in any centered chart contained in the plateau. -/
theorem chartH1_high_value_ae
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U) (J : ℤ)
    (j : JetSpace U)
    (hj : EqOn (fun w => thresholdSeed J (ofComplex w))
      (fun w => representative U hU j w + continuedHighCusp J 0 w) U)
    (L : ℂ →L[ℝ] ℝ) (z : ℂ) (S : Set (Fin 2 → ℝ)) (hS : IsOpen S)
    (hSU : ellipticChart z '' S ⊆ U) (u : H1Function S)
    (hu : u.toFun = fun v => L (valueCLM U j (ellipticChart z v))) :
    (u + highCuspChartH1 J χ hχ hc hs L z S hS).toFun =ᵐ[volume.restrict S]
      (fun v => L (thresholdSeed J (ofComplex (ellipticChart z v)))) := by
  have ha := ae_restrict_of_ae_restrict_of_subset hSU (representative_ae U hU j)
  have hp := (ellipticChart_measurePreserving_restrict_image z S).quasiMeasurePreserving.ae_eq_comp ha
  filter_upwards [hp, ae_restrict_mem hS.measurableSet] with v hv hvS
  have hvU : ellipticChart z v ∈ U := hSU (Set.mem_image_of_mem _ hvS)
  change u.toFun v + L (χ (ellipticChart z v) * continuedHighCusp J 0 (ellipticChart z v)) = _
  rw [hu, hχU hvU, one_mul]
  change L (valueCLM U j (ellipticChart z v)) + L (continuedHighCusp J 0 (ellipticChart z v)) = _
  change representative U hU j (ellipticChart z v) = valueCLM U j (ellipticChart z v) at hv
  rw [← hv, ← map_add]
  exact congrArg L (hj hvU).symm

/-- Actual H1 witnesses on each open chart plateau: no weak-gradient or
Sobolev premise for the canonical seed appears in this construction. -/
theorem exists_thresholdSeed_chartH1
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U) (J : ℤ)
    (L : ℂ →L[ℝ] ℝ) (z : ℂ) (S : Set (Fin 2 → ℝ)) (hS : IsOpen S)
    (hSU : ellipticChart z '' S ⊆ U) :
    ∃ u : H1Function S, u.toFun =ᵐ[volume.restrict S]
      (fun v => L (thresholdSeed J (ofComplex (ellipticChart z v)))) := by
  obtain ⟨j, hj⟩ := exists_thresholdResidualJet χ hχ hc hs U hU hχU J
  refine ⟨chartH1 L U j z S hSU + highCuspChartH1 J χ hχ hc hs L z S hS, ?_⟩
  exact chartH1_high_value_ae χ hχ hc hs U hU hχU J j hj L z S hS hSU _ rfl

end GapFamily.Analytic.PoincareThresholdJet
