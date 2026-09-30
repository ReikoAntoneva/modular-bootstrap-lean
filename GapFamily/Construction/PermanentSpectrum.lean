import GapFamily.Construction.PermanentSpectrumData
import GapFamily.Construction.PermanentSpectrumCharacter
import GapFamily.Construction.PermanentSpectrumSum
import GapFamily.Construction.PermanentSpectrumList

/-! The actual permanent node spectrum, its ordinary character expansion,
and the precise remainder criterion for complete modular corrections to give
the public admissible spectrum. No finite primary prefix is assumed modular. -/
noncomputable section
namespace GapFamily.Construction.PermanentSpectrumData
open Filter
open scoped Topology UpperHalfPlane
variable {b : ℝ} (D : PermanentSpectrumData b)

/-- Each permanent unit atom contributes exactly one threshold seed. -/
def unitSeed (i : D.Node) (τ : ℍ) : ℂ :=
  Analytic.pointSeed (D.energy i) (D.spin i) (1 / 2) τ

/-- The prescribed vacuum plus the actual finite permanent primary blocks. -/
def reducedPrefix (c : ℝ) (n : ℕ) (τ : ℍ) : ℂ :=
  (Real.sqrt τ.im : ℂ) * vacuumNumerator c τ +
    permanentNodePrefix (fun i => D.unitSeed i τ) n

theorem reducedPrefix_succ (c : ℝ) (n : ℕ) (τ : ℍ) :
    D.reducedPrefix c (n + 1) τ = D.reducedPrefix c n τ +
      ∑ i : Fin (D.layerCount n),
        Analytic.pointSeed (D.layerEnergy n i) (D.layerSpin n i) (1 / 2) τ := by
  rw [reducedPrefix, permanentNodePrefix_succ]
  simp only [reducedPrefix, add_assoc]
  rfl

theorem energyThermal_summable (y : ℝ)
    (hlayer : Summable (D.layerThermal (2 * Real.pi * y))) :
    Summable (fun i : D.Node => Real.exp (-2 * Real.pi * y * D.energy i)) := by
  convert D.thermal_summable (2 * Real.pi * y) hlayer using 1
  funext i
  congr 1
  ring

theorem unitSeed_norm_summable (τ : ℍ)
    (hlayer : Summable (D.layerThermal (2 * Real.pi * τ.im))) :
    Summable (fun i : D.Node => ‖D.unitSeed i τ‖) :=
  node_pointSeed_half_norm_summable D.energy D.spin τ (D.energyThermal_summable τ.im hlayer)

/-- Absolute character convergence is proved before any modularity conclusion. -/
theorem character_norm_summable (c : ℝ) (τ : ℍ)
    (hlayer : Summable (D.layerThermal (2 * Real.pi * τ.im))) :
    Summable (fun p : (D.spectrum c).support =>
      ‖((D.spectrum c).multiplicity p : ℂ) * primaryCharacter c p.val.1 τ *
        star (primaryCharacter c p.val.2 τ)‖) := by
  simp_rw [norm_primary_term]
  exact (D.spectrum_thermal_summable c τ.im hlayer).mul_right _

/-- The public character numerator is exactly the same actual unit-node sum. -/
theorem reducedNumerator_eq_unitSeed_tsum (c : ℝ) (τ : ℍ)
    (hlayer : Summable (D.layerThermal (2 * Real.pi * τ.im))) :
    reducedNumerator c (D.spectrum c) τ =
      (Real.sqrt τ.im : ℂ) * vacuumNumerator c τ + ∑' i : D.Node, D.unitSeed i τ :=
  reducedNumerator_nodeSpectrum_eq_pointSeed_tsum c D.energy D.spin
    D.energy_sublevel_finite τ (D.energyThermal_summable τ.im hlayer)

/-- Genuine finite permanent prefixes converge to the actual public reduced
numerator, with the marker and finite initial block retained at every stage. -/
theorem tendsto_reducedPrefix (c : ℝ) (τ : ℍ)
    (hlayer : Summable (D.layerThermal (2 * Real.pi * τ.im))) :
    Tendsto (fun n => D.reducedPrefix c n τ) atTop
      (𝓝 (reducedNumerator c (D.spectrum c) τ)) := by
  rw [D.reducedNumerator_eq_unitSeed_tsum c τ hlayer]
  exact tendsto_const_nhds.add
    (tendsto_permanentNodePrefix (fun i => D.unitSeed i τ) (D.unitSeed_norm_summable τ hlayer))

/-- Only the actual residual between a complete correction and its prescribed
permanent prefix must tend to zero; the spectral limit is then identified. -/
theorem tendsto_reducedNumerator_of_remainder (c : ℝ)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (F : ℕ → ℍ → ℂ)
    (hremainder : ∀ τ, Tendsto (fun n => F n τ - D.reducedPrefix c n τ) atTop (𝓝 0)) :
    ∀ τ, Tendsto (fun n => F n τ) atTop (𝓝 (reducedNumerator c (D.spectrum c) τ)) := by
  intro τ
  have hsum := D.tendsto_reducedPrefix c τ
    (hthermal (2 * Real.pi * τ.im) (by positivity))
  simpa only [sub_add_cancel, zero_add] using (hremainder τ).add hsum

/-- A genuine vanishing real error majorant supplies the required remainder
limit; this is the form used by the thermal envelope tail estimates. -/
theorem tendsto_reducedNumerator_of_remainder_bound (c : ℝ)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (F : ℕ → ℍ → ℂ) (error : ℕ → ℍ → ℝ)
    (hbound : ∀ n τ, ‖F n τ - D.reducedPrefix c n τ‖ ≤ error n τ)
    (herror : ∀ τ, Tendsto (fun n => error n τ) atTop (𝓝 0)) :
    ∀ τ, Tendsto (fun n => F n τ) atTop (𝓝 (reducedNumerator c (D.spectrum c) τ)) := by
  apply D.tendsto_reducedNumerator_of_remainder c hthermal F
  intro τ
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => hbound n τ) (herror τ)

/-- The complete modular corrections certify the original public character
conditions of this exact permanent spectrum, not an unspecified limit object. -/
theorem pureAdmissible_of_remainder {c : ℝ} (hc : 1 < c)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (F : ℕ → ℍ → ℂ)
    (hS : ∀ n τ, F n (ModularGroup.S • τ) = F n τ)
    (hT : ∀ n τ, F n (ModularGroup.T • τ) = F n τ)
    (hremainder : ∀ τ, Tendsto (fun n => F n τ - D.reducedPrefix c n τ) atTop (𝓝 0)) :
    PureAdmissible c (D.spectrum c) := by
  apply nodeSpectrum_pureAdmissible_of_pointwise_limit hc D.energy D.spin
    D.energy_cone D.energy_sublevel_finite _ F hS hT
    (D.tendsto_reducedNumerator_of_remainder c hthermal F hremainder)
  intro y hy
  exact D.energyThermal_summable y (hthermal (2 * Real.pi * y) (by positivity))

theorem pureAdmissible_and_hasGap_of_remainder {c : ℝ} (hc : 1 < c)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (F : ℕ → ℍ → ℂ)
    (hS : ∀ n τ, F n (ModularGroup.S • τ) = F n τ)
    (hT : ∀ n τ, F n (ModularGroup.T • τ) = F n τ)
    (hremainder : ∀ τ, Tendsto (fun n => F n τ - D.reducedPrefix c n τ) atTop (𝓝 0)) :
    PureAdmissible c (D.spectrum c) ∧ HasGap (D.spectrum c) (shift c + b) :=
  ⟨D.pureAdmissible_of_remainder hc hthermal F hS hT hremainder, D.hasGap c⟩

/-- The character prefix matches the schedule's literal list expression,
including the exact vacuum and marker terms. -/
theorem ofLists_reducedPrefix (hb : 0 ≤ b)
    (initial : List (ℝ × ℤ)) (layer : ℕ → List (ℝ × ℤ))
    (hinitial : ∀ p ∈ initial, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (hlayer : ∀ (m : ℕ) p, p ∈ layer m → b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1 ∧
      (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2)
    (c : ℝ) (n : ℕ) (τ : ℍ) :
    (ofLists hb initial layer hinitial hlayer).reducedPrefix c n τ =
      (Real.sqrt τ.im : ℂ) * vacuumNumerator c τ + Analytic.pointSeed b 0 (1 / 2) τ +
        (initial.map (fun p => Analytic.pointSeed p.1 p.2 (1 / 2) τ)).sum +
        ∑ m ∈ Finset.range n,
          ((layer m).map (fun p => Analytic.pointSeed p.1 p.2 (1 / 2) τ)).sum := by
  unfold reducedPrefix unitSeed
  rw [ofLists_permanentNodePrefix hb initial layer hinitial hlayer
    (fun p => Analytic.pointSeed p.1 p.2 (1 / 2) τ) n]
  ring

end GapFamily.Construction.PermanentSpectrumData
