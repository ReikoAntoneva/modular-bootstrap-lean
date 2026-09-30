import GapFamily.Analytic.Modular.ModularPositiveResolventBasic

noncomputable section
namespace GapFamily.Analytic.ModularPositiveResolvent
open ModularGradient

/-- The resolvent identity for the actual unbounded modular Laplacian. The proof
applies the genuine left inverse to a genuine resolvent-domain vector. -/
theorem shiftedResolvent_identity (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 < t) :
    shiftedResolvent r - shiftedResolvent t =
      ((t - r : ℝ) : ℂ) • (shiftedResolvent r * shiftedResolvent t) := by
  apply ContinuousLinearMap.ext
  intro f
  change shiftedResolvent r f - shiftedResolvent t f =
    ((t - r : ℝ) : ℂ) • shiftedResolvent r (shiftedResolvent t f)
  have hleft := shiftedResolvent_leftInverse r hr
    ⟨shiftedResolvent t f, shiftedResolvent_mem_domain t f⟩
  have hright := shiftedResolvent_rightInverse t ht f
  have hA := eq_sub_of_add_eq hright
  rw [hA, map_add, map_sub, map_smul, map_smul] at hleft
  calc
    shiftedResolvent r f - shiftedResolvent t f =
        shiftedResolvent r f -
          (shiftedResolvent r f - (t : ℂ) • shiftedResolvent r (shiftedResolvent t f) +
            (r : ℂ) • shiftedResolvent r (shiftedResolvent t f)) :=
      congrArg (fun v => shiftedResolvent r f - v) hleft.symm
    _ = ((t - r : ℝ) : ℂ) • shiftedResolvent r (shiftedResolvent t f) := by
      rw [Complex.ofReal_sub]
      module

/-- Actual positive-shift resolvents commute; no bounded realization of the
Laplacian or commutation premise is used. -/
theorem shiftedResolvent_commute (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 < t) :
    Commute (shiftedResolvent r) (shiftedResolvent t) := by
  by_cases h : r = t
  · subst t
    exact Commute.refl _
  · change shiftedResolvent r * shiftedResolvent t =
      shiftedResolvent t * shiftedResolvent r
    have hne : ((t - r : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (fun htr => h htr.symm))
    apply smul_right_injective (ModularHilbert →L[ℂ] ModularHilbert) hne
    calc
      ((t - r : ℝ) : ℂ) • (shiftedResolvent r * shiftedResolvent t) =
          shiftedResolvent r - shiftedResolvent t :=
        (shiftedResolvent_identity r hr t ht).symm
      _ = -(shiftedResolvent t - shiftedResolvent r) := by abel
      _ = -(((r - t : ℝ) : ℂ) • (shiftedResolvent t * shiftedResolvent r)) := by
        rw [shiftedResolvent_identity t ht r hr]
      _ = ((t - r : ℝ) : ℂ) • (shiftedResolvent t * shiftedResolvent r) := by
        simp only [Complex.ofReal_sub]
        module

/-- The actual normalized resolvent factors commute at all positive parameters. -/
theorem resolventFactor_commute (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 < t) :
    Commute (resolventFactor r) (resolventFactor t) :=
  ((shiftedResolvent_commute r hr t ht).smul_left (r : ℂ)).smul_right (t : ℂ)

/-- Any family of positive parameters gives pairwise commuting actual factors. -/
theorem resolventFactor_pairwise_commute {ι : Type*} (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    Pairwise (fun i j => Commute (resolventFactor (r i)) (resolventFactor (r j))) :=
  fun i j _ => resolventFactor_commute (r i) (hr i) (r j) (hr j)

end GapFamily.Analytic.ModularPositiveResolvent
