import GapFamily.Analytic.Foundation.ThetaContinuation

/-!
# Canonical continuation of the scalar point seeds

The input spin is exactly zero throughout this module. The continued
zero-energy Eisenstein family plus the genuinely convergent energy difference
agrees with the original cusp-coset Poincaré series in its convergence region.
Its value at one half is an actual convergent difference series, for every
complex input energy.
-/

noncomputable section

namespace GapFamily.Analytic

open Complex
open scoped MatrixGroups Topology

/-- The scalar-spin Poincaré family continued from its actual convergence region. -/
def scalarPoincareContinuation (E s : ℂ) (z : UpperHalfPlane) : ℂ :=
  scalarEisenstein z s + complexPoincareEnergyDifference E 0 s z

/-- The scalar canonical point seed at the physical continuation parameter. -/
def continuedScalarSeed (E : ℂ) (z : UpperHalfPlane) : ℂ :=
  scalarPoincareContinuation E (1 / 2) z

/-- The full continued scalar family is modular, not just its imaginary-axis restriction. -/
theorem scalarPoincareContinuation_smul (E s : ℂ) (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    scalarPoincareContinuation E s (g • z) = scalarPoincareContinuation E s z := by
  simp only [scalarPoincareContinuation, scalarEisenstein_smul,
    complexPoincareEnergyDifference_smul]

theorem continuedScalarSeed_smul (E : ℂ) (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    continuedScalarSeed E (g • z) = continuedScalarSeed E z :=
  scalarPoincareContinuation_smul E (1 / 2) g z

/-- The continued expression agrees with the original, absolutely convergent scalar seed sum. -/
theorem scalarPoincareContinuation_eq_series (E : ℂ) {s : ℂ}
    (hs : 1 < s.re) (z : UpperHalfPlane) :
    scalarPoincareContinuation E s z = complexPoincareSeries E 0 s z := by
  rw [scalarPoincareContinuation, scalarEisenstein_eq_complexPoincareSeries z hs,
    complexPoincareEnergyDifference_eq_sub E 0 hs z]
  ring

/-- Regularity of the canonical continuation throughout the physical half-plane away from one. -/
theorem scalarPoincareContinuation_analyticAt_exponent (E : ℂ) (z : UpperHalfPlane)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (fun s => scalarPoincareContinuation E s z) s := by
  exact (scalarEisenstein_analyticAt z hs hs1).add
    (complexPoincareEnergyDifference_analyticAt_exponent E 0 z (by linarith))

/-- The energy parameter is entire for every admissible continuation parameter. -/
theorem scalarPoincareContinuation_analyticAt_energy (E : ℂ) (z : UpperHalfPlane)
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun E => scalarPoincareContinuation E s z) E :=
  analyticAt_const.add (complexPoincareEnergyDifference_analyticAt_energy 0 hs z E)

/-- The zero-energy scalar family vanishes at one half, leaving the actual energy-difference sum. -/
theorem continuedScalarSeed_eq_difference (E : ℂ) (z : UpperHalfPlane) :
    continuedScalarSeed E z = complexPoincareEnergyDifference E 0 (1 / 2) z := by
  rw [continuedScalarSeed, scalarPoincareContinuation, scalarEisenstein_half, zero_add]

/-- The canonical scalar seed is a genuinely convergent series even at the continuation point. -/
theorem continuedScalarSeed_hasSum (E : ℂ) (z : UpperHalfPlane) :
    HasSum (fun q : CuspCoset => complexPoincareDifferenceTerm E 0 (1 / 2) z q)
      (continuedScalarSeed E z) := by
  rw [continuedScalarSeed_eq_difference]
  exact hasSum_complexPoincareEnergyDifference E 0 (by norm_num) z

/-- One summable majorant controls compact sets of complex energies and spatial points. -/
theorem continuedScalarSeed_normal_on_compact {K : Set (ℂ × UpperHalfPlane)}
    (hK : IsCompact K) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ ∀ q p, p ∈ K →
      ‖complexPoincareDifferenceTerm p.1 0 (1 / 2) p.2 q‖ ≤ u q := by
  let embed : ℂ × UpperHalfPlane → (ℂ × ℂ) × UpperHalfPlane :=
    fun p => ((p.1, 1 / 2), p.2)
  have hc : Continuous embed :=
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd
  obtain ⟨u, hu, hbound⟩ := complexPoincareDifferenceTerm_normal_on_compact_full
    (hK.image hc) (by rintro p ⟨q, hq, rfl⟩; norm_num [embed])
  exact ⟨u, hu, fun q p hp => hbound 0 q (embed p) (Set.mem_image_of_mem embed hp)⟩

/-- At the physical parameter the actual seed sum converges locally uniformly in energy and space. -/
theorem continuedScalarSeed_tendstoLocallyUniformly :
    TendstoLocallyUniformly
      (fun A : Finset CuspCoset => fun p : ℂ × UpperHalfPlane =>
        ∑ q ∈ A, complexPoincareDifferenceTerm p.1 0 (1 / 2) p.2 q)
      (fun p => continuedScalarSeed p.1 p.2) Filter.atTop := by
  let embed : ℂ × UpperHalfPlane → (ℂ × ℂ) × UpperHalfPlane :=
    fun p => ((p.1, 1 / 2), p.2)
  have hc : Continuous embed :=
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd
  have h := (complexPoincareEnergyDifference_tendstoLocallyUniformlyOn_full 0).comp embed
    (t := Set.univ) (by intro p hp; norm_num [embed]) hc.continuousOn
  rw [tendstoLocallyUniformlyOn_univ] at h
  simpa only [Function.comp_def, embed, continuedScalarSeed_eq_difference] using h

/-- Entire dependence includes the negative-energy scalar seeds in the vacuum numerator. -/
theorem continuedScalarSeed_analyticAt (E : ℂ) (z : UpperHalfPlane) :
    AnalyticAt ℂ (fun E => continuedScalarSeed E z) E := by
  exact scalarPoincareContinuation_analyticAt_energy E z (by norm_num)

/-- The scalar origin seed is identically zero under the canonical continuation. -/
@[simp] theorem continuedScalarSeed_zero (z : UpperHalfPlane) : continuedScalarSeed 0 z = 0 := by
  rw [continuedScalarSeed_eq_difference]
  simp [complexPoincareEnergyDifference, complexPoincareDifferenceTerm]

/-- Real inputs agree with the already convergent real-energy subtraction. -/
theorem continuedScalarSeed_ofReal (E : ℝ) (z : UpperHalfPlane) :
    continuedScalarSeed (E : ℂ) z = poincareEnergyDifference E 0 (1 / 2) z := by
  rw [continuedScalarSeed_eq_difference]
  simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using
    complexPoincareEnergyDifference_ofReal E 0 (1 / 2) z

/-- Positive scalar seeds have a uniform linear energy bound on every compact spatial set. -/
theorem exists_continuedScalarSeed_compact_linear {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, z ∈ K → ∀ E : ℝ, 0 ≤ E →
      ‖continuedScalarSeed (E : ℂ) z‖ ≤ C * E := by
  obtain ⟨C, hC, hbound⟩ := exists_poincareEnergyDifference_compact_linear hK
    (s := 1 / 2) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro z hz E hE
  rw [continuedScalarSeed_ofReal]
  exact hbound 0 z hz E hE

end GapFamily.Analytic
