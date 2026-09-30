import GapFamily.Analytic.Cusp.Schur.CuspSchurOperator
import GapFamily.Analytic.Cusp.Schur.CuspSchurThreshold

/-!
Actual full Schur inverse wherever both actual pencils are
units and the literal scalar denominator is nonzero. These explicit hypotheses
will be discharged on a physical neighborhood of the threshold parameter.
-/
noncomputable section
namespace GapFamily.Analytic.CuspSchur
open ModularGradient CuspSchur

/-- The concrete full-form equation requires only the three actual regularity conditions. -/
theorem actualSchurSolution_equation_of_units {z : ℂ}
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z))
    (hD : actualSchurDenominator z ≠ 0) (f : ModularHilbert) (t : FormDomain) :
    inner ℂ (formGradient t) (formGradient (actualSchurSolution z f)) -
      z * inner ℂ (formEmbedding t) (actualSchurResolvent z f) =
      inner ℂ (formEmbedding t) f :=
  schurSolution_equation hV (cuspScalarPencilSolution z)
    (actualScalar_formPairing hW) hD f t

/-- Uniqueness uses the actual scalar and constrained weak uniqueness theorems. -/
theorem actualSchurSolution_unique_of_units {z : ℂ}
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z))
    (hD : actualSchurDenominator z ≠ 0) (f : ModularHilbert) (u : FormDomain)
    (hu : ∀ t : FormDomain, inner ℂ (formGradient t) (formGradient u) -
      z * inner ℂ (formEmbedding t) (formEmbedding u) = inner ℂ (formEmbedding t) f) :
    u = actualSchurSolution z f :=
  schurSolution_unique hV (cuspScalarPencilSolution z)
    (actualScalar_formPairing_unique hW) hD f u hu

/-- Every actual Schur value belongs to the full modular operator domain. -/
theorem actualSchurResolvent_mem_domain_of_units {z : ℂ}
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z))
    (hD : actualSchurDenominator z ≠ 0) (f : ModularHilbert) :
    actualSchurResolvent z f ∈ laplacian.domain :=
  formEmbedding_mem_laplacian_domain_of_formPairing z (actualSchurSolution z f) f
    (actualSchurSolution_equation_of_units hV hW hD f)

theorem actualSchurResolvent_rightInverse_of_units {z : ℂ}
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z))
    (hD : actualSchurDenominator z ≠ 0) (f : ModularHilbert) :
    laplacian ⟨actualSchurResolvent z f, actualSchurResolvent_mem_domain_of_units hV hW hD f⟩ -
      z • actualSchurResolvent z f = f :=
  laplacian_sub_smul_of_formPairing z (actualSchurSolution z f) f
    (actualSchurSolution_equation_of_units hV hW hD f)

theorem actualSchurResolvent_leftInverse_of_units {z : ℂ}
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z))
    (hD : actualSchurDenominator z ≠ 0) (x : laplacian.domain) :
    actualSchurResolvent z (laplacian x - z • (x : ModularHilbert)) = x := by
  have h := actualSchurSolution_unique_of_units hV hW hD
    (laplacian x - z • (x : ModularHilbert))
    (formLift ⟨x, laplacian_domain_le x.property⟩) (formPairing_laplacian z x)
  exact (congrArg formEmbedding h).symm

end GapFamily.Analytic.CuspSchur


/-!
# Actual pencil units near the scalar threshold

The actual constrained quarter unit persists in a full neighborhood after the
polynomial spectral reparameterization. On the physical side, the independently
proved scalar unit and scalar denominator nonvanishing supply the other two
conditions used by the full Schur inverse identities.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchur

open Filter
open scoped Topology

theorem meanZeroPencil_eventually_isUnit_near_zero :
    ∀ᶠ κ in 𝓝 (0 : ℂ),
      IsUnit (cuspMeanZeroPencil ((1 / 4 : ℂ) - κ ^ 2)) := by
  have hV : ∀ᶠ z in 𝓝 (1 / 4 : ℂ), IsUnit (cuspMeanZeroPencil z) :=
    isOpen_cuspMeanZeroPencilRegularSet.mem_nhds
      (show (1 / 4 : ℂ) ∈ cuspMeanZeroPencilRegularSet from
        cuspMeanZeroPencil_isUnit_quarter)
  have ht : Tendsto (fun κ : ℂ => (1 / 4 : ℂ) - κ ^ 2)
      (𝓝 (0 : ℂ)) (𝓝 (1 / 4 : ℂ)) := by
    have hc : ContinuousAt (fun κ : ℂ => (1 / 4 : ℂ) - κ ^ 2) 0 := by fun_prop
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using hc.tendsto
  exact ht.eventually hV

theorem actualSchur_eventually_regular_near_zero :
    ∀ᶠ κ in 𝓝 (0 : ℂ), 0 < κ.re →
      IsUnit (cuspMeanZeroPencil ((1 / 4 : ℂ) - κ ^ 2)) ∧
      IsUnit (cuspScalarPencil ((1 / 4 : ℂ) - κ ^ 2)) ∧
      CuspSchur.actualSchurDenominator ((1 / 4 : ℂ) - κ ^ 2) ≠ 0 := by
  filter_upwards [meanZeroPencil_eventually_isUnit_near_zero,
    CuspSchur.actualSchurDenominator_eventually_ne_zero_physical]
      with κ hV hD hphysical
  exact ⟨hV, cuspScalarPencil_isUnit_physical hphysical, hD hphysical⟩

end GapFamily.Analytic.CuspSchur


noncomputable section
namespace GapFamily.Analytic.CuspSchur
open ModularGradient CuspSchur Filter
open scoped Topology

/-- Every sufficiently close physical parameter has the full actual test-first weak equation. -/
theorem actualSchurSolution_eventually_equation_near_zero :
    ∀ᶠ κ in 𝓝 (0 : ℂ), 0 < κ.re → ∀ (f : ModularHilbert) (t : FormDomain),
      inner ℂ (formGradient t)
          (formGradient (actualSchurSolution ((1 / 4 : ℂ) - κ ^ 2) f)) -
        ((1 / 4 : ℂ) - κ ^ 2) * inner ℂ (formEmbedding t)
          (actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f) =
        inner ℂ (formEmbedding t) f := by
  filter_upwards [actualSchur_eventually_regular_near_zero] with κ h hphysical
  obtain ⟨hV, hW, hD⟩ := h hphysical
  exact actualSchurSolution_equation_of_units hV hW hD

/-- The actual full-form solution is unique at every sufficiently close physical parameter. -/
theorem eventually_existsUnique_full_weak_near_zero :
    ∀ᶠ κ in 𝓝 (0 : ℂ), 0 < κ.re → ∀ f : ModularHilbert,
      ∃! u : FormDomain, ∀ t : FormDomain,
        inner ℂ (formGradient t) (formGradient u) -
          ((1 / 4 : ℂ) - κ ^ 2) * inner ℂ (formEmbedding t) (formEmbedding u) =
          inner ℂ (formEmbedding t) f := by
  filter_upwards [actualSchur_eventually_regular_near_zero] with κ h hphysical f
  obtain ⟨hV, hW, hD⟩ := h hphysical
  refine ⟨actualSchurSolution ((1 / 4 : ℂ) - κ ^ 2) f,
    actualSchurSolution_equation_of_units hV hW hD f, ?_⟩
  exact fun u hu => actualSchurSolution_unique_of_units hV hW hD f u hu

/-- Domain membership and both actual operator inverse identities hold on the physical side.
The existential witness is only the proved membership proof for the displayed value. -/
theorem actualSchurResolvent_eventually_inverse_near_zero :
    ∀ᶠ κ in 𝓝 (0 : ℂ), 0 < κ.re →
      (∀ f : ModularHilbert, ∃ hf :
          actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f ∈ laplacian.domain,
        laplacian ⟨actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f, hf⟩ -
          ((1 / 4 : ℂ) - κ ^ 2) • actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f = f) ∧
      (∀ x : laplacian.domain,
        actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2)
          (laplacian x - ((1 / 4 : ℂ) - κ ^ 2) • (x : ModularHilbert)) = x) := by
  filter_upwards [actualSchur_eventually_regular_near_zero] with κ h hphysical
  obtain ⟨hV, hW, hD⟩ := h hphysical
  refine ⟨?_, actualSchurResolvent_leftInverse_of_units hV hW hD⟩
  intro f
  exact ⟨actualSchurResolvent_mem_domain_of_units hV hW hD f,
    actualSchurResolvent_rightInverse_of_units hV hW hD f⟩

/-- An actual positive radius works for every source and every operator-domain vector.
The condition Re κ>0 excludes κ=0; no boundary form-valued inverse is claimed. -/
theorem exists_radius_actualSchur_inverse_physical :
    ∃ ε : ℝ, 0 < ε ∧ ∀ κ : ℂ, ‖κ‖ < ε → 0 < κ.re →
      (∀ f : ModularHilbert, ∃ hf :
          actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f ∈ laplacian.domain,
        laplacian ⟨actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f, hf⟩ -
          ((1 / 4 : ℂ) - κ ^ 2) • actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2) f = f) ∧
      (∀ x : laplacian.domain,
        actualSchurResolvent ((1 / 4 : ℂ) - κ ^ 2)
          (laplacian x - ((1 / 4 : ℂ) - κ ^ 2) • (x : ModularHilbert)) = x) := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp
    actualSchurResolvent_eventually_inverse_near_zero
  refine ⟨ε, hε, fun κ hκ => h ?_⟩
  simpa only [dist_zero_right] using hκ

end GapFamily.Analytic.CuspSchur
