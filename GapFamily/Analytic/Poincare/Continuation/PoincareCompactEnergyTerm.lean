import GapFamily.Analytic.Poincare.Continuation.PoincareCompactTermAnalytic

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyConvergentAnalytic
open Set UpperHalfPlane PoincareConvergentAnalytic
open scoped Topology

/-- The actual compact orbit height with the original energy-exponential normalization. -/
def compactEnergyRate (K : Set ℂ) (hKH : K ⊆ upperHalfPlaneSet) (q : CuspCoset) :
    C(K, ℂ) :=
  ⟨fun z => -2 * (Real.pi : ℂ) * ((compactOrbit K hKH q z).im : ℂ),
    continuous_const.mul (Complex.continuous_ofReal.comp
      (UpperHalfPlane.continuous_im.comp (compactOrbit K hKH q).continuous))⟩

/-- The actual energy difference of one quotient term, before taking any series sum. -/
def compactEnergyTerm (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (E : ℂ) (J : ℤ) (s : ℂ) (q : CuspCoset) : C(K, ℂ) :=
  compactTerm K hKH J s q * (NormedSpace.exp (E • compactEnergyRate K hKH q) - 1)

/-- The Banach-valued energy difference is exactly the existing actual difference summand. -/
theorem compactEnergyTerm_apply (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) (s : ℂ) (q : CuspCoset) (z : K) :
    compactEnergyTerm K hKH E J s q z =
      complexPoincareDifferenceTerm E J s (UpperHalfPlane.ofComplex z.val) q := by
  have he : NormedSpace.exp (E • compactEnergyRate K hKH q) z =
      Complex.exp (-2 * (Real.pi : ℂ) * E * (compactOrbit K hKH q z).im) := by
    have hv : NormedSpace.exp (E • compactEnergyRate K hKH q) z =
        Complex.exp (E * compactEnergyRate K hKH q z) := by
      simpa only [Complex.exp_eq_exp_ℂ, ContinuousMap.evalAlgHom_apply,
        ContinuousMap.smul_apply, smul_eq_mul] using
        NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ z)
          (ContinuousMap.evalCLM ℂ z).continuous (E • compactEnergyRate K hKH q)
    rw [hv]
    simp only [compactEnergyRate, ContinuousMap.coe_mk]
    congr 1
    ring
  rw [compactEnergyTerm, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, he, compactTerm_apply, compactOrbit_apply,
    complexPoincareDifferenceTerm]
  simp only [complexPoincareTerm_out]
  rw [complexPointSeed_sub_zero_energy]
  simp only [complexPointSeed, mul_zero, zero_mul, zero_add]

/-- The individual difference term is jointly differentiable in energy and exponent
with values in the actual spatial uniform-norm Banach algebra. -/
theorem compactEnergyTerm_differentiable_joint (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (q : CuspCoset) :
    Differentiable ℂ (fun p : ℂ × ℂ => compactEnergyTerm K hKH p.1 J p.2 q) :=
  ((compactTerm_differentiable K hKH J q).comp differentiable_snd).mul
    (((differentiable_exp_smul_const ℂ (compactEnergyRate K hKH q)).comp
      differentiable_fst).sub (differentiable_const 1))

/-- Joint norm analyticity holds at every pair of complex parameters. -/
theorem compactEnergyTerm_analyticAt_joint (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (q : CuspCoset) (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun w : ℂ × ℂ => compactEnergyTerm K hKH w.1 J w.2 q) p := by
  have ht : AnalyticAt ℂ (fun w : ℂ × ℂ => compactTerm K hKH J w.2 q) p :=
    (compactTerm_analyticAt K hKH J q p.2).comp analyticAt_snd
  have hr : AnalyticAt ℂ (fun w : ℂ × ℂ => w.1 • compactEnergyRate K hKH q) p :=
    analyticAt_fst.smul analyticAt_const
  have he : AnalyticAt ℂ
      (fun w : ℂ × ℂ => NormedSpace.exp (w.1 • compactEnergyRate K hKH q)) p :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (p.1 • compactEnergyRate K hKH q)).comp_of_eq hr rfl
  exact ht.mul (he.sub analyticAt_const)

/-- For fixed energy, the actual single-term family is entire in the exponent. -/
theorem compactEnergyTerm_analyticAt_exponent (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) (q : CuspCoset) (s : ℂ) :
    AnalyticAt ℂ (fun w => compactEnergyTerm K hKH E J w q) s :=
  (compactTerm_analyticAt K hKH J q s).mul analyticAt_const

/-- For fixed exponent, the actual single-term family is entire in the energy. -/
theorem compactEnergyTerm_analyticAt_energy (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (s : ℂ) (q : CuspCoset) (E : ℂ) :
    AnalyticAt ℂ (fun w => compactEnergyTerm K hKH w J s q) E := by
  have hr : AnalyticAt ℂ (fun w : ℂ => w • compactEnergyRate K hKH q) E :=
    analyticAt_id.smul analyticAt_const
  have he : AnalyticAt ℂ (fun w : ℂ => NormedSpace.exp (w • compactEnergyRate K hKH q)) E :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (E • compactEnergyRate K hKH q)).comp_of_eq hr rfl
  exact analyticAt_const.mul (he.sub analyticAt_const)

end GapFamily.Analytic.PoincareEnergyConvergentAnalytic
