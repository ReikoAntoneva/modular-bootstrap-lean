import GapFamily.Quadrature.MomentCurve
import GapFamily.Quadrature.DensityCorrection
import GapFamily.Quadrature.AtomApproximation
import Mathlib.Analysis.Convex.Topology

/-!
# Positive density realization of interior moments

The normalized moment vectors of positive continuous interval densities form
an open convex set. Approximation of point masses then shows that this set
contains the interior of the classical moment body.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace GapFamily.Quadrature

/-- The nonconstant moments of an actual interval density. -/
def nonconstantDensityMoments (k : ℕ) (a b : ℝ) (f : ℝ → ℝ) : MomentVector k :=
  fun i => ∫ x in a..b, x ^ (i.val + 1) * f x

/-- Moment vectors realized by strictly positive continuous probability densities. -/
def positiveDensityMomentSet (k : ℕ) (a b : ℝ) : Set (MomentVector k) :=
  {z | ∃ f : ℝ → ℝ, ContinuousOn f (Icc a b) ∧
    (∀ x ∈ Icc a b, 0 < f x) ∧ (∫ x in a..b, f x) = 1 ∧
    nonconstantDensityMoments k a b f = z}

theorem nonconstantDensityMoments_add {k : ℕ} {a b : ℝ} (hab : a ≤ b)
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) :
    nonconstantDensityMoments k a b (fun x => f x + g x) =
      nonconstantDensityMoments k a b f + nonconstantDensityMoments k a b g := by
  ext i
  simp only [nonconstantDensityMoments, Pi.add_apply, mul_add]
  exact intervalIntegral.integral_add
    (((continuous_id.pow _).continuousOn.mul hf).intervalIntegrable_of_Icc hab)
    (((continuous_id.pow _).continuousOn.mul hg).intervalIntegrable_of_Icc hab)

theorem nonconstantDensityMoments_smul (k : ℕ) (a b c : ℝ) (f : ℝ → ℝ) :
    nonconstantDensityMoments k a b (fun x => c * f x) = c • nonconstantDensityMoments k a b f := by
  ext i
  simp only [nonconstantDensityMoments, Pi.smul_apply, smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  ring

theorem positiveDensityMomentSet_nonempty (k : ℕ) {a b : ℝ} (hab : a < b) :
    (positiveDensityMomentSet k a b).Nonempty := by
  refine ⟨nonconstantDensityMoments k a b (fun _ => (b - a)⁻¹), fun _ => (b - a)⁻¹,
    continuousOn_const, ?_, ?_, rfl⟩
  · intro x hx
    exact inv_pos.mpr (sub_pos.mpr hab)
  · simp [intervalIntegral.integral_const, ne_of_gt (sub_pos.mpr hab)]

theorem convex_positiveDensityMomentSet (k : ℕ) {a b : ℝ} (hab : a < b) :
    Convex ℝ (positiveDensityMomentSet k a b) := by
  rintro z ⟨f, hf, hfp, hfm, rfl⟩ w ⟨g, hg, hgp, hgm, rfl⟩ c d hc hd hcd
  refine ⟨fun x => c * f x + d * g x, (hf.const_mul c).add (hg.const_mul d), ?_, ?_, ?_⟩
  · intro x hx
    have hf' := hfp x hx
    have hg' := hgp x hx
    by_cases hcp : 0 < c
    · exact add_pos_of_pos_of_nonneg (mul_pos hcp hf') (mul_nonneg hd hg'.le)
    · have hd' : 0 < d := by linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg hc hf'.le) (mul_pos hd' hg')
  · rw [intervalIntegral.integral_add
      ((hf.const_mul c).intervalIntegrable_of_Icc hab.le)
      ((hg.const_mul d).intervalIntegrable_of_Icc hab.le)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hfm, hgm, mul_one, mul_one, hcd]
  · rw [nonconstantDensityMoments_add hab.le (hf.const_mul c) (hg.const_mul d),
      nonconstantDensityMoments_smul, nonconstantDensityMoments_smul]

/-- Adding unit mass to the nonconstant coordinates. -/
def probabilityMomentVector {k : ℕ} (z : MomentVector k) : Fin (k + 1) → ℝ :=
  Fin.cons 1 z

theorem continuous_probabilityMomentVector (k : ℕ) :
    Continuous (probabilityMomentVector (k := k)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · exact continuous_apply j

theorem probabilityMomentVector_densityMoments {k : ℕ} {a b : ℝ} {f : ℝ → ℝ}
    (hmass : (∫ x in a..b, f x) = 1) :
    probabilityMomentVector (nonconstantDensityMoments k a b f) =
      densityMoments a b (k + 1) f := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [probabilityMomentVector, densityMoments] using hmass.symm
  · rfl

/-- The actual Gram inverse makes the positive density moment range open. -/
theorem isOpen_positiveDensityMomentSet (k : ℕ) {a b : ℝ} (hab : a < b) :
    IsOpen (positiveDensityMomentSet k a b) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨f, hf, hp, hm, rfl⟩
  obtain ⟨δ, hδ, hnear⟩ := correctedDensity_positive_near hab (k + 1) f hf hp
  have hc : Continuous (fun w : MomentVector k =>
      ‖probabilityMomentVector w - densityMoments a b (k + 1) f‖) :=
    ((continuous_probabilityMomentVector k).sub continuous_const).norm
  have hevent : ∀ᶠ w in 𝓝 (nonconstantDensityMoments k a b f),
      ‖probabilityMomentVector w - densityMoments a b (k + 1) f‖ < δ :=
    hc.continuousAt.eventually (gt_mem_nhds (by
      simpa [probabilityMomentVector_densityMoments hm] using hδ))
  apply Filter.mem_of_superset hevent
  intro w hw
  refine ⟨correctedDensity hab (k + 1) f (probabilityMomentVector w),
    correctedDensity_continuousOn hab (k + 1) f hf _, hnear _ hw, ?_, ?_⟩
  · have h := congrFun (correctedDensity_moment hab (k + 1) f hf
      (probabilityMomentVector w)) 0
    simpa [densityMoments, probabilityMomentVector] using h
  · ext i
    exact congrFun (correctedDensity_moment hab (k + 1) f hf
      (probabilityMomentVector w)) i.succ

/-- Nonnegative continuous probability densities can be approached by positive ones. -/
theorem nonnegative_densityMoments_mem_closure {k : ℕ} {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hfp : ∀ x ∈ Icc a b, 0 ≤ f x) (hfm : (∫ x in a..b, f x) = 1) :
    nonconstantDensityMoments k a b f ∈ closure (positiveDensityMomentSet k a b) := by
  obtain ⟨w, g, hg, hgp, hgm, rfl⟩ := positiveDensityMomentSet_nonempty k hab
  apply closure_mono (s := openSegment ℝ (nonconstantDensityMoments k a b f)
    (nonconstantDensityMoments k a b g)) ?_
    (segment_subset_closure_openSegment (left_mem_segment ℝ _ _))
  rintro z ⟨c, d, hc, hd, hcd, rfl⟩
  refine ⟨fun x => c * f x + d * g x, (hf.const_mul c).add (hg.const_mul d), ?_, ?_, ?_⟩
  · intro x hx
    exact add_pos_of_nonneg_of_pos (mul_nonneg hc.le (hfp x hx))
      (mul_pos hd (hgp x hx))
  · rw [intervalIntegral.integral_add
      ((hf.const_mul c).intervalIntegrable_of_Icc hab.le)
      ((hg.const_mul d).intervalIntegrable_of_Icc hab.le)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hfm, hgm, mul_one, mul_one, hcd]
  · rw [nonconstantDensityMoments_add hab.le (hf.const_mul c) (hg.const_mul d),
      nonconstantDensityMoments_smul, nonconstantDensityMoments_smul]

/-- Every interval point mass is a limit of positive continuous density moments. -/
theorem momentCurve_mem_closure_positiveDensityMomentSet (k : ℕ) {a b : ℝ}
    (hab : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    momentCurve k x ∈ closure (positiveDensityMomentSet k a b) := by
  have hinterior : MapsTo (momentCurve k) (Ioo a b)
      (closure (positiveDensityMomentSet k a b)) := by
    intro y hy
    rw [← closure_closure (s := positiveDensityMomentSet k a b)]
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨f, hf, hpos, hmass, herr⟩ :=
      exists_continuous_density_moment_approximation k hy hε
    refine ⟨nonconstantDensityMoments k a b f,
      nonnegative_densityMoments_mem_closure hab hf.continuousOn
        (fun t _ => hpos t) hmass, ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    exact herr
  have h := hinterior.closure_of_continuousOn (continuous_momentCurve k).continuousOn
  rw [closure_Ioo hab.ne, closure_closure] at h
  exact h hx

/-- The entire classical moment body lies in the closure of positive density moments. -/
theorem momentBody_subset_closure_positiveDensityMomentSet (k : ℕ) {a b : ℝ}
    (hab : a < b) :
    momentBody k a b ⊆ closure (positiveDensityMomentSet k a b) := by
  apply convexHull_min
  · rintro z ⟨x, hx, rfl⟩
    exact momentCurve_mem_closure_positiveDensityMomentSet k hab hx
  · exact (convex_positiveDensityMomentSet k hab).closure

/-- Interior moments are actually represented by positive continuous densities. -/
theorem mem_positiveDensityMomentSet_of_mem_interior {k : ℕ} {a b : ℝ}
    (hab : a < b) {z : MomentVector k} (hz : z ∈ interior (momentBody k a b)) :
    z ∈ positiveDensityMomentSet k a b := by
  have hopen := isOpen_positiveDensityMomentSet k hab
  have hne : (interior (positiveDensityMomentSet k a b)).Nonempty := by
    rw [hopen.interior_eq]
    exact positiveDensityMomentSet_nonempty k hab
  have h := interior_mono (momentBody_subset_closure_positiveDensityMomentSet k hab) hz
  have heq := (convex_positiveDensityMomentSet k hab).interior_closure_eq_interior_of_nonempty_interior hne
  rwa [heq, hopen.interior_eq] at h

/-- No representing measure or density is assumed: every interior point of the
moment body has a strictly positive continuous probability density. -/
theorem exists_positiveDensity_of_mem_interior {k : ℕ} {a b : ℝ} (hab : a < b)
    {z : MomentVector k} (hz : z ∈ interior (momentBody k a b)) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Icc a b) ∧
      (∀ x ∈ Icc a b, 0 < f x) ∧ (∫ x in a..b, f x) = 1 ∧
      nonconstantDensityMoments k a b f = z :=
  mem_positiveDensityMomentSet_of_mem_interior hab hz

/-- The same realization includes the unit mass coordinate explicitly. -/
theorem exists_positiveDensity_with_all_moments {k : ℕ} {a b : ℝ} (hab : a < b)
    {z : MomentVector k} (hz : z ∈ interior (momentBody k a b)) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Icc a b) ∧
      (∀ x ∈ Icc a b, 0 < f x) ∧
      densityMoments a b (k + 1) f = probabilityMomentVector z := by
  obtain ⟨f, hf, hpos, hmass, hmom⟩ := exists_positiveDensity_of_mem_interior hab hz
  exact ⟨f, hf, hpos, (probabilityMomentVector_densityMoments hmass).symm.trans
    (congrArg probabilityMomentVector hmom)⟩

end GapFamily.Quadrature
