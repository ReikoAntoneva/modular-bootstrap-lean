import GapFamily.Analytic.Elliptic.WeakSobolevContinuous
import GapFamily.Analytic.Elliptic.RealH1Derivative
import GapFamily.Analytic.Foundation.FiniteDerivativeAssembly

noncomputable section
namespace GapFamily.Analytic.EllipticSobolev
open Set Filter MeasureTheory Homogenization
open scoped Topology ContDiff

/-- Every finite weak order m+2 in a planar chart has a genuine local C^m
representative. The proof constructs the representatives by finite induction. -/
theorem exists_local_contDiffOn_of_weakSobolev (m : ℕ)
    {U : Set (Vec 2)} (hU : IsOpen U) (h0 : (0 : Vec 2) ∈ U) {f : Vec 2 → ℝ}
    (hf : weakSobolev (m + 2) U f) :
    ∃ V : Set (Vec 2), IsOpen V ∧ (0 : Vec 2) ∈ V ∧ V ⊆ U ∧
      ∃ g : Vec 2 → ℝ, ContDiffOn ℝ (m : ℕ∞ω) g V ∧ g =ᵐ[volume.restrict V] f := by
  induction m generalizing U f with
  | zero =>
    obtain ⟨V, hV, h0V, hVU, g, hgc, hga⟩ :=
      exists_local_continuous_of_weakSobolev_two hU h0 hf
    exact ⟨V, hV, h0V, hVU, g, contDiffOn_zero.mpr hgc, hga⟩
  | succ m ih =>
    have hf2 : weakSobolev 2 U f := weakSobolev_mono_order (by omega) hf
    obtain ⟨V0, hV0, h0V0, hV0U, g0, hg0c, hg0a⟩ :=
      exists_local_continuous_of_weakSobolev_two hU h0 hf2
    have hs : weakSobolev ((m + 2) + 1) U f := hf
    obtain ⟨u, hu, hgrad⟩ := hs
    have hex (i : Fin 2) :
        ∃ W : Set (Vec 2), IsOpen W ∧ (0 : Vec 2) ∈ W ∧ W ⊆ U ∧
          ∃ g : Vec 2 → ℝ, ContDiffOn ℝ (m : ℕ∞ω) g W ∧
            g =ᵐ[volume.restrict W] (fun x => u.grad x i) :=
      ih hU h0 (hgrad i)
    choose W hW h0W hWU g hgc hga using hex
    let V : Set (Vec 2) := V0 ∩ ⋂ i : Fin 2, W i
    have hV : IsOpen V := hV0.inter (isOpen_iInter_of_finite hW)
    have h0V : (0 : Vec 2) ∈ V := ⟨h0V0, mem_iInter.mpr h0W⟩
    have hVV0 : V ⊆ V0 := inter_subset_left
    have hVW (i : Fin 2) : V ⊆ W i := fun x hx => mem_iInter.mp hx.2 i
    have hVU : V ⊆ U := hVV0.trans hV0U
    let uV := u.restrict hV hVU
    have hvalue : g0 =ᵐ[volume.restrict V] uV.toFun := by
      have ha := ae_restrict_of_ae_restrict_of_subset hVV0 hg0a
      change g0 =ᵐ[volume.restrict V] u.toFun
      rw [hu]
      exact ha
    have hgradA (i : Fin 2) : g i =ᵐ[volume.restrict V] (fun x => uV.grad x i) :=
      ae_restrict_of_ae_restrict_of_subset (hVW i) (hga i)
    have hclassical : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) g0 V := by
      apply contDiffOn_succ_of_hasFDerivAt_realGradientField hV
      · intro x hx
        exact hasFDerivAt_real_of_h1 hV uV g0 (hg0c.mono hVV0)
          hvalue g (fun i => (hgc i).continuousOn.mono (hVW i)) hgradA hx
      · exact fun i => (hgc i).mono (hVW i)
    exact ⟨V, hV, h0V, hVU, g0, hclassical,
      ae_restrict_of_ae_restrict_of_subset hVV0 hg0a⟩

/-- The given continuous representative, rather than merely a chosen AE
representative, has the claimed finite classical derivative order at zero. -/
theorem contDiffAt_zero_of_continuousOn_weakSobolev (m : ℕ)
    {U : Set (Vec 2)} (hU : IsOpen U) (h0 : (0 : Vec 2) ∈ U) {f : Vec 2 → ℝ}
    (hfc : ContinuousOn f U) (hf : weakSobolev (m + 2) U f) :
    ContDiffAt ℝ (m : ℕ∞ω) f 0 := by
  obtain ⟨V, hV, h0V, hVU, g, hg, hga⟩ :=
    exists_local_contDiffOn_of_weakSobolev m hU h0 hf
  have heq : EqOn g f V := Measure.eqOn_open_of_ae_eq hga hV hg.continuousOn (hfc.mono hVU)
  have hnear : f =ᶠ[𝓝 (0 : Vec 2)] g := by
    filter_upwards [hV.mem_nhds h0V] with x hx
    exact (heq hx).symm
  exact (hg.contDiffAt (hV.mem_nhds h0V)).congr_of_eventuallyEq hnear

end GapFamily.Analytic.EllipticSobolev
