import GapFamily.Analytic.Modular.Elliptic.ModularEllipticH1
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticCube

/-!
# Actual centered scalar Hessian data for local approximation

The two real Sobolev solutions and Hessians are constructed from the actual
modular operator-domain value. The equations below identify their literal
value and gradient fields before any smoothing or continuous representative is
introduced.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory Homogenization ModularElliptic

/-- The actual real and imaginary weak Hessians on one common centered cube. -/
theorem laplacian_exists_centered_hessian_data (u : laplacian.domain)
    (z : ℂ) (hz : z ∈ modularInterior) :
    ∃ Q : TriadicCube 2, cubeCenter Q = 0 ∧
      ellipticChart z '' scaledClosedCubeSet Q 1 ⊆ modularInterior ∧
      ∃ (uR uI : H1Function (scaledOpenCubeSet Q (1 / 2)))
        (_HR : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uR)
        (_HI : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uI),
        uR.toFun = (fun v =>
          (coordinateValue ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v)).re) ∧
        uI.toFun = (fun v =>
          (coordinateValue ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v)).im) ∧
        uR.grad = (fun v =>
          ![(coordinateDx ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v)).re,
            (coordinateDy ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v)).re]) ∧
        uI.grad = (fun v =>
          ![(coordinateDx ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v)).im,
            (coordinateDy ⟨u, laplacian_domain_le u.property⟩ (ellipticChart z v)).im]) := by
  obtain ⟨Q, hcenter, hQ, _⟩ := exists_centered_cube_closed_subset
    (isOpen_modularInterior.preimage (ellipticChart z).continuous)
    (by simpa using hz : (0 : Fin 2 → ℝ) ∈ ellipticChart z ⁻¹' modularInterior)
  let K := ellipticChart z '' scaledClosedCubeSet Q 1
  have hK : IsCompact K := (isCompact_scaledClosedCubeSet Q (by norm_num : (0 : ℝ) ≤ 1)).image
    (ellipticChart z).continuous
  have hKU : K ⊆ modularInterior := by
    rintro w ⟨v, hv, rfl⟩
    exact hQ hv
  have hUK : ellipticChart z '' openCubeSet Q ⊆ K := by
    apply Set.image_mono
    intro v hv
    have hv' : v ∈ scaledOpenCubeSet Q 1 := by
      simpa only [scaledOpenCubeSet_eq_metricBall Q (by norm_num : (0 : ℝ) < 1),
        one_mul, ball_cubeCenter_eq_openCubeSet] using hv
    exact fun i => (hv' i).le
  obtain ⟨uR, hRv, hRg, ⟨HR⟩⟩ := halfCube_weakHessian Q
    (ellipticH1 Complex.reCLM u z _ hK hKU hUK)
    (fun v => (coordinateSource u (ellipticChart z v)).re)
    (ellipticH1_weakPoisson Complex.reCLM u z _ hK hKU hUK)
    (ellipticH1_source_memL2 Complex.reCLM u z hK hKU hUK)
  obtain ⟨uI, hIv, hIg, ⟨HI⟩⟩ := halfCube_weakHessian Q
    (ellipticH1 Complex.imCLM u z _ hK hKU hUK)
    (fun v => (coordinateSource u (ellipticChart z v)).im)
    (ellipticH1_weakPoisson Complex.imCLM u z _ hK hKU hUK)
    (ellipticH1_source_memL2 Complex.imCLM u z hK hKU hUK)
  exact ⟨Q, hcenter, hKU, uR, uI, HR, HI, hRv, hIv, hRg, hIg⟩

end GapFamily.Analytic.ModularGradient
