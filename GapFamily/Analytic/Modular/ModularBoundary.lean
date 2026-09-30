import GapFamily.Analytic.Modular.ModularHilbert
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Null boundary of the modular fundamental domain

The unit-circle arc and the two vertical sides have zero hyperbolic volume.
Consequently the open and closed fundamental domains define exactly the same
restricted measure. This is a statement about `L²` measure classes, not an
identification of the automorphic energy-form domain with an arbitrary domain
on the open region.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

/-- A vertical line in the complex plane has zero two-dimensional volume. -/
theorem complex_verticalLine_volume_zero (a : ℝ) :
    (volume : Measure ℂ) {z | z.re = a} = 0 := by
  have hset : {z : ℂ | z.re = a} =
      Complex.measurableEquivRealProd ⁻¹' ({a} ×ˢ (univ : Set ℝ)) := by
    ext z
    simp
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  change (volume.prod volume) ({a} ×ˢ (univ : Set ℝ)) = 0
  simp [Measure.prod_prod]

/-- The unit circle has zero complex Lebesgue volume. -/
theorem complex_unitCircle_volume_zero :
    (volume : Measure ℂ) (Metric.sphere 0 1) = 0 :=
  Measure.addHaar_sphere volume 0 1

/-- The boundary maps into one circle and two straight lines. -/
theorem coe_fd_sdiff_fdo_subset :
    UpperHalfPlane.coe '' (ModularGroup.fd \ ModularGroup.fdo) ⊆
      Metric.sphere (0 : ℂ) 1 ∪
        ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)}) := by
  rintro z ⟨τ, ⟨hfd, hfdo⟩, rfl⟩
  by_cases hn : 1 < Complex.normSq (τ : ℂ)
  · have ha : |τ.re| = 1 / 2 :=
      le_antisymm hfd.2 (not_lt.mp fun h => hfdo ⟨hn, h⟩)
    right
    rcases le_total 0 τ.re with h | h
    · left
      simpa [abs_of_nonneg h] using ha
    · right
      have := ha
      rw [abs_of_nonpos h] at this
      change τ.re = -(1 / 2)
      linarith
  · have heq : Complex.normSq (τ : ℂ) = 1 := le_antisymm (not_lt.mp hn) hfd.1
    have hnorm : ‖(τ : ℂ)‖ = 1 := by
      rw [Complex.normSq_eq_norm_sq] at heq
      nlinarith [norm_nonneg (τ : ℂ)]
    left
    simpa [Metric.mem_sphere, dist_zero_right] using hnorm

/-- The image of the domain boundary is Lebesgue-null. -/
theorem complexVolume_coe_fd_sdiff_fdo :
    (volume : Measure ℂ) (UpperHalfPlane.coe '' (ModularGroup.fd \ ModularGroup.fdo)) = 0 := by
  apply measure_mono_null coe_fd_sdiff_fdo_subset
  exact measure_union_null complex_unitCircle_volume_zero
    (measure_union_null (complex_verticalLine_volume_zero _) (complex_verticalLine_volume_zero _))

/-- Weighting by the actual inverse-square density preserves the null boundary. -/
theorem volume_fd_sdiff_fdo :
    (volume : Measure UpperHalfPlane) (ModularGroup.fd \ ModularGroup.fdo) = 0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  exact setLIntegral_measure_zero _ _ complexVolume_coe_fd_sdiff_fdo

/-- The topological frontier of the closed fundamental domain has zero hyperbolic volume. -/
theorem volume_frontier_fd :
    (volume : Measure UpperHalfPlane) (frontier ModularGroup.fd) = 0 := by
  rw [frontier, ModularGroup.isClosed_fd.closure_eq, ← ModularGroup.fdo_eq_interior_fd]
  exact volume_fd_sdiff_fdo

/-- The closed and open domain agree almost everywhere in hyperbolic volume. -/
theorem fd_ae_eq_fdo :
    ModularGroup.fd =ᵐ[(volume : Measure UpperHalfPlane)] ModularGroup.fdo := by
  rw [ae_eq_set]
  exact ⟨volume_fd_sdiff_fdo,
    by rw [sdiff_eq_empty.mpr ModularGroup.fdo_subset_fd, measure_empty]⟩

/-- The actual modular measure is unchanged when restricted to the open domain. -/
theorem modularMeasure_eq_restrict_fdo :
    modularMeasure = (volume : Measure UpperHalfPlane).restrict ModularGroup.fdo :=
  Measure.restrict_congr_set fd_ae_eq_fdo

/-- Passing to the open fundamental domain preserves the exact area. -/
theorem volume_fdo_eq_pi_div_three :
    (volume : Measure UpperHalfPlane) ModularGroup.fdo = ENNReal.ofReal (Real.pi / 3) := by
  rw [← measure_congr fd_ae_eq_fdo]
  exact volume_fd_eq_pi_div_three

/-- A modular-measure almost-everywhere point lies in the open fundamental domain. -/
theorem ae_mem_fdo : ∀ᵐ τ ∂modularMeasure, τ ∈ ModularGroup.fdo := by
  rw [modularMeasure_eq_restrict_fdo]
  exact ae_restrict_mem ModularGroup.isOpen_fdo.measurableSet

/-- The boundary carries no mass for the restricted modular measure either. -/
theorem modularMeasure_frontier_fd : modularMeasure (frontier ModularGroup.fd) = 0 := by
  rw [modularMeasure, Measure.restrict_apply isClosed_frontier.measurableSet]
  exact measure_mono_null inter_subset_left volume_frontier_fd


open scoped ENNReal NNReal Topology

section InteriorApproximation

variable {α : Type*} [TopologicalSpace α] [NormalSpace α]
  [MeasurableSpace α] [BorelSpace α] [T2Space α]
  [LocallyCompactSpace α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} [μ.Regular] {p : ℝ≥0∞}

/-- Continuous compactly supported functions contained in a full-measure open set
approximate every Lp function. This is Lp density only, not energy-form density. -/
private theorem exists_interior_continuous_approximation
    {u : Set α} (hu : IsOpen u) (hfull : ∀ᵐ x ∂μ, x ∈ u)
    (hp : p ≠ ∞) {f : α → E} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α → E, HasCompactSupport g ∧ tsupport g ⊆ u ∧
      eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ := by
  suffices H : ∃ g : α → E, eLpNorm (f - g) p μ ≤ ε ∧
      Continuous g ∧ MemLp g p μ ∧ HasCompactSupport g ∧ tsupport g ⊆ u by
    rcases H with ⟨g, hg, gc, gm, gs, gu⟩
    exact ⟨g, gs, gu, hg, gc, gm⟩
  apply hf.induction_dense hp _ _ _ hε
  rotate_left
  · rintro f g ⟨fc, fm, fs, fu⟩ ⟨gc, gm, gs, gu⟩
    refine ⟨fc.add gc, fm.add gm, fs.add gs, ?_⟩
    exact (tsupport_binop_subset (· + ·) (add_zero (0 : E)) f g).trans
      (union_subset fu gu)
  intro c t ht htμ ε hε
  obtain ⟨δ, δpos, hδ⟩ := exists_Lp_half E μ p hε
  obtain ⟨η, ηpos, hη⟩ : ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η →
      NullMeasurableSet s μ → eLpNorm (s.indicator fun _x => c) p μ ≤ δ :=
    exists_eLpNorm_indicator_le hp c δpos.ne'
  have hηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
  have htumu : μ (t ∩ u) < ∞ := (measure_mono inter_subset_left).trans_lt htμ
  obtain ⟨s, stu, sc, scl, μs⟩ : ∃ s, s ⊆ t ∩ u ∧ IsCompact s ∧ IsClosed s ∧
      μ ((t ∩ u) \ s) < η :=
    (ht.inter hu.measurableSet).exists_isCompact_isClosed_sdiff_lt htumu.ne hηpos.ne'
  have st : s ⊆ t := stu.trans inter_subset_left
  have su : s ⊆ u := stu.trans inter_subset_right
  have μs' : μ (t \ s) < η := by
    have heq : (t \ s) =ᵐ[μ] ((t ∩ u) \ s) := by
      filter_upwards [hfull] with x hx
      simp [hx]
    rw [measure_congr heq]
    exact μs
  have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ
  have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) p μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
    exact hη _ μs'.le (ht.diff scl.measurableSet).nullMeasurableSet
  obtain ⟨k, kc, kcl, sk, ku⟩ := exists_compact_closed_between sc hu su
  obtain ⟨g, gc, I2, _gb, gs, gm⟩ :=
    exists_continuous_eLpNorm_sub_le_of_closed hp scl isOpen_interior sk hsμ.ne c δpos.ne'
  have I3 : eLpNorm (g - t.indicator fun _y => c) p μ ≤ ε := by
    convert! (hδ _ _ I2 I1).le using 2
    ext x
    simp
  have gk : tsupport g ⊆ k := by
    exact closure_minimal (gs.trans interior_subset) kcl
  refine ⟨g, I3, gc, gm, ?_, gk.trans ku⟩
  exact kc.of_isClosed_subset isClosed_closure gk


end InteriorApproximation

/-- L2 density in the actual modular Hilbert space of continuous functions
whose compact support avoids the fundamental-domain boundary. -/
theorem modularInteriorContinuous_dense :
    Dense {f : ModularHilbert | ∃ g : UpperHalfPlane → ℂ,
      Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ ModularGroup.fdo ∧
      f =ᵐ[modularMeasure] g} := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε ↦ ?_
  obtain ⟨g, gs, gu, hg, gc, gm⟩ :=
    exists_interior_continuous_approximation
      ModularGroup.isOpen_fdo ae_mem_fdo (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (Lp.memLp f) hε.ne'
  refine ⟨gm.toLp g, ⟨g, gc, gs, gu, gm.coeFn_toLp⟩, ?_⟩
  rwa [Metric.mem_closedEBall', ← Lp.toLp_coeFn f (Lp.memLp f), Lp.edist_toLp_toLp]


end GapFamily.Analytic
