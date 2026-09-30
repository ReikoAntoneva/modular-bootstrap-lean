import GapFamily.Analytic.Elliptic.WeakSobolevPotential
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdHessian
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdChartPoisson

/-! Every finite weak derivative order of the actual canonical threshold seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareThresholdAllOrders
open Set MeasureTheory UpperHalfPlane Homogenization ModularElliptic
  PoincareCanonical PoincareThresholdJet
  PoincareThresholdSourceCutoff PoincareThresholdSourceH1
  PoincareThresholdChartPoisson EllipticSobolev
open scoped ContDiff Topology

/-- An actual threshold H1 chart satisfies a constructed smooth compact
potential equation, so its canonical scalar value has every finite local weak order. -/
theorem thresholdSeed_chart_allOrders (J : ℤ) (L : ℂ →L[ℝ] ℝ)
    (z : ℂ) (S : Set (Fin 2 → ℝ)) (hS : IsOpen S) (h0 : (0 : Fin 2 → ℝ) ∈ S)
    (hSc : IsCompact (closure S))
    (hSH : ellipticChart z '' closure S ⊆ upperHalfPlaneSet)
    (u : H1Function S)
    (hu : u.toFun =ᵐ[volume.restrict S]
      (fun v => L (thresholdSeed J (ofComplex (ellipticChart z v))))) (n : ℕ) :
    ∃ V : Set (Fin 2 → ℝ), IsOpen V ∧ (0 : Fin 2 → ℝ) ∈ V ∧ V ⊆ S ∧
      weakSobolev n V (fun v => L (thresholdSeed J (ofComplex (ellipticChart z v)))) := by
  obtain ⟨m, hm, hc, hs, he⟩ :=
    exists_inverseHeightCutoff (hSc.image (ellipticChart z).continuous) hSH
  let a : (Fin 2 → ℝ) → ℝ := fun v => (1 / 4 : ℝ) * m (ellipticChart z v)
  let g : (Fin 2 → ℝ) → ℝ := fun v => localizedShiftedSource J L m (ellipticChart z v)
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul (hm.comp (ellipticChart_contDiff z))
  have hac : HasCompactSupport a := (hc.comp_homeomorph (ellipticChart z)).mul_left
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_localizedShiftedSource J L m hm hs).comp (ellipticChart_contDiff z)
  have hgc : HasCompactSupport g :=
    (hasCompactSupport_localizedShiftedSource J L m hc).comp_homeomorph (ellipticChart z)
  let F : H1Function S := thresholdSourceChartH1 J L m hm hc hs z S hS u
  have hF : F.toFun =ᵐ[volume.restrict S]
      (fun v => L (thresholdSource J (ellipticChart z v))) :=
    thresholdSourceChartH1_value_ae J L m hm hc hs z S hS u hu
      (he.mono (image_mono subset_closure))
  have hPF : WeakPoissonEquationOn S u F :=
    thresholdSeed_chart_weakPoisson J L z S ((image_mono subset_closure).trans hSH) u hu F hF
  have hvalue : F.toFun = (fun v => a v * u v + g v) := by
    funext v
    change (1 / 4 : ℝ) * (m (ellipticChart z v) * u.toFun v) +
      localizedShiftedSource J L m (ellipticChart z v) =
        ((1 / 4 : ℝ) * m (ellipticChart z v)) * u.toFun v +
          localizedShiftedSource J L m (ellipticChart z v)
    ring
  have hP : WeakPoissonEquationOn S u (fun v => a v * u v + g v) := by
    rw [← hvalue]
    exact hPF
  exact weakSobolev_potential_allOrders_zero_ae hS h0 u ha hac hg hgc hP
    (fun v => L (thresholdSeed J (ofComplex (ellipticChart z v)))) hu n

/-- At every upper point a single centered full chart cube lies inside positive
height, and both canonical scalar coordinates have every finite weak order on
some common neighborhood of its center. All H1 and PDE inputs are constructed. -/
theorem exists_thresholdSeed_chart_allOrders (J : ℤ) (τ : UpperHalfPlane) :
    ∃ Q : TriadicCube 2, cubeCenter Q = 0 ∧
      ellipticChart (τ : ℂ) '' scaledClosedCubeSet Q 1 ⊆ upperHalfPlaneSet ∧
      ∀ n : ℕ, ∃ V : Set (Fin 2 → ℝ), IsOpen V ∧ (0 : Fin 2 → ℝ) ∈ V ∧
        V ⊆ openCubeSet Q ∧
        weakSobolev n V
          (fun v => (thresholdSeed J (ofComplex (ellipticChart (τ : ℂ) v))).re) ∧
        weakSobolev n V
          (fun v => (thresholdSeed J (ofComplex (ellipticChart (τ : ℂ) v))).im) := by
  obtain ⟨Q, hcenter, hQH, uR, uI, _HR, _HI, hRv, hIv⟩ :=
    exists_thresholdSeed_openCube_hessian_data J τ
  have h0 : (0 : Fin 2 → ℝ) ∈ openCubeSet Q := by
    rw [← ball_cubeCenter_eq_openCubeSet, hcenter]
    exact Metric.mem_ball_self (cubeRadius_pos Q)
  have hsub : openCubeSet Q ⊆ scaledClosedCubeSet Q 1 := by
    intro v hv
    have hv' : v ∈ scaledOpenCubeSet Q 1 := by
      simpa only [scaledOpenCubeSet_eq_metricBall Q (by norm_num : (0 : ℝ) < 1),
        one_mul, ball_cubeCenter_eq_openCubeSet] using hv
    exact fun i => (hv' i).le
  have hcl : closure (openCubeSet Q) ⊆ scaledClosedCubeSet Q 1 :=
    closure_minimal hsub (isClosed_scaledClosedCubeSet Q 1)
  have hcompact : IsCompact (closure (openCubeSet Q)) :=
    (isCompact_scaledClosedCubeSet Q (by norm_num : (0 : ℝ) ≤ 1)).of_isClosed_subset
      isClosed_closure hcl
  have hclosedH : ellipticChart (τ : ℂ) '' closure (openCubeSet Q) ⊆ upperHalfPlaneSet :=
    (image_mono hcl).trans hQH
  refine ⟨Q, hcenter, hQH, ?_⟩
  intro n
  obtain ⟨VR, hVR, h0R, hRQ, hR⟩ := thresholdSeed_chart_allOrders J Complex.reCLM τ
    (openCubeSet Q) (isOpen_openCubeSet Q) h0 hcompact hclosedH uR hRv n
  obtain ⟨VI, hVI, h0I, _hIQ, hI⟩ := thresholdSeed_chart_allOrders J Complex.imCLM τ
    (openCubeSet Q) (isOpen_openCubeSet Q) h0 hcompact hclosedH uI hIv n
  refine ⟨VR ∩ VI, hVR.inter hVI, ⟨h0R, h0I⟩, inter_subset_left.trans hRQ, ?_, ?_⟩
  · exact weakSobolev_restrict hR (hVR.inter hVI) inter_subset_left
  · exact weakSobolev_restrict hI (hVR.inter hVI) inter_subset_right

end GapFamily.Analytic.PoincareThresholdAllOrders
