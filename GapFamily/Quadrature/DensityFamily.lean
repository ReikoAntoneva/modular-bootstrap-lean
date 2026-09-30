import GapFamily.Quadrature.DensityCorrection
import GapFamily.Quadrature.PositiveDensity
import Mathlib.Topology.PartitionOfUnity

/-!
# Continuous families of positive interval densities

A polynomial right inverse gives positive local sections of finite moments.
A finite partition of unity then glues them over a compact parameter space;
convex combinations preserve both positivity and the exact target moments.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace GapFamily.Quadrature

/-- Joint continuity on the interval subtype gives the ambient-set form used
by the cumulative and quantile construction. -/
theorem continuousOn_uncurry_of_continuous_interval
    {P : Type*} [TopologicalSpace P] {a b : ℝ} (f : P → ℝ → ℝ)
    (hf : Continuous (fun q : P × Icc a b => f q.1 q.2)) :
    ContinuousOn (Function.uncurry f) (univ ×ˢ Icc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (fun q : (univ ×ˢ Icc a b : Set (P × ℝ)) =>
      (q.val.1, (⟨q.val.2, q.property.2⟩ : Icc a b))) := by fun_prop
  exact hf.comp hc


/-- A finite subordinate partition of unity on a compact Hausdorff space. -/
theorem exists_finite_continuous_partition
    {P : Type*} [TopologicalSpace P] [CompactSpace P] [T2Space P]
    (U : P → Set P) (hopen : ∀ p, IsOpen (U p)) (hself : ∀ p, p ∈ U p) :
    ∃ (n : ℕ) (index : Fin n → P) (weight : Fin n → C(P, ℝ)),
      (∀ i p, 0 ≤ weight i p) ∧
      (∀ p, ∑ i, weight i p = 1) ∧
      (∀ i p, weight i p ≠ 0 → p ∈ U (index i)) := by
  classical
  have hcover : (Set.univ : Set P) ⊆ ⋃ p, U p := by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p, hself p⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  let e : Fin s.card ≃ s := (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm
  let index : Fin s.card → P := fun i => e i
  have hfinite : (Set.univ : Set P) ⊆ ⋃ i, U (index i) := by
    intro p hp
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (hs hp)
    obtain ⟨hqs, hpq⟩ := Set.mem_iUnion.mp hq
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨q, hqs⟩, ?_⟩
    simpa only [index, e.apply_symm_apply] using hpq
  obtain ⟨weight, hsupp, hsum, hbound, _⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact
      (fun i => hopen (index i)) isCompact_univ hfinite
  refine ⟨s.card, index, weight, fun i p => (hbound i p).1, ?_, ?_⟩
  · intro p
    simpa using hsum (Set.mem_univ p)
  · intro i p hp
    exact hsupp i (subset_closure hp)

/-- Positive continuous realizations of individual moment vectors glue into
one jointly continuous positive family over any compact Hausdorff parameter
space. The local sections are constructed by the actual polynomial Gram inverse. -/
theorem exists_continuous_positive_density_family
    {P : Type*} [TopologicalSpace P] [CompactSpace P] [T2Space P]
    {a b : ℝ} (hab : a < b) (n : ℕ) (target : P → Fin n → ℝ)
    (htarget : Continuous target)
    (hrealize : ∀ p : P, ∃ f : ℝ → ℝ, ContinuousOn f (Icc a b) ∧
      (∀ x ∈ Icc a b, 0 < f x) ∧ densityMoments a b n f = target p) :
    ∃ density : P → ℝ → ℝ,
      ContinuousOn (Function.uncurry density) (univ ×ˢ Icc a b) ∧
      (∀ p x, x ∈ Icc a b → 0 < density p x) ∧
      (∀ p, densityMoments a b n (density p) = target p) := by
  classical
  choose f hfcont hfpos hfmom using hrealize
  choose δ hδ hlocal using fun p => correctedDensity_positive_near hab n (f p)
    (hfcont p) (hfpos p)
  let U : P → Set P := fun p => {q | ‖target q - target p‖ < δ p}
  have hopen : ∀ p, IsOpen (U p) := fun p =>
    isOpen_lt ((htarget.sub continuous_const).norm) continuous_const
  have hself : ∀ p, p ∈ U p := by
    intro p
    simpa [U] using hδ p
  obtain ⟨m, index, weight, hwpos, hwsum, hsupport⟩ :=
    exists_finite_continuous_partition U hopen hself
  let g : Fin m → P → ℝ → ℝ := fun i p =>
    correctedDensity hab n (f (index i)) (target p)
  have hgcont (i : Fin m) (p : P) : ContinuousOn (g i p) (Icc a b) :=
    correctedDensity_continuousOn hab n (f (index i)) (hfcont _) (target p)
  have hgjoint (i : Fin m) :
      Continuous (fun q : P × Icc a b => g i q.1 q.2) :=
    (correctedDensity_joint_continuous hab n (f (index i)) (hfcont _)).comp
      ((htarget.comp continuous_fst).prodMk continuous_snd)
  have hgmom (i : Fin m) (p : P) : densityMoments a b n (g i p) = target p :=
    correctedDensity_moment hab n (f (index i)) (hfcont _) (target p)
  have hgpos (i : Fin m) (p : P) (hp : weight i p ≠ 0) :
      ∀ x ∈ Icc a b, 0 < g i p x := by
    apply hlocal (index i) (target p)
    rw [hfmom]
    exact hsupport i p hp
  let density : P → ℝ → ℝ := fun p x => ∑ i, weight i p * g i p x
  refine ⟨density, ?_, ?_, ?_⟩
  · apply continuousOn_uncurry_of_continuous_interval
    apply continuous_finsetSum
    intro i _
    exact ((weight i).continuous.comp continuous_fst).mul (hgjoint i)
  · intro p x hx
    have hspos : 0 < ∑ i, weight i p := by rw [hwsum]; exact zero_lt_one
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hwpos j p)).mp hspos
    change 0 < ∑ j, weight j p * g j p x
    apply Finset.sum_pos'
    · intro j _
      by_cases hw : weight j p = 0
      · simp [hw]
      · exact mul_nonneg (hwpos j p) (hgpos j p hw x hx).le
    · exact ⟨i, Finset.mem_univ _, mul_pos hi (hgpos i p hi.ne' x hx)⟩
  · intro p
    ext j
    change (∫ x in a..b, x ^ j.val * ∑ i, weight i p * g i p x) = target p j
    have heq : (fun x : ℝ => x ^ j.val * ∑ i, weight i p * g i p x) =
        fun x => ∑ i, weight i p * (x ^ j.val * g i p x) := by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq, intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul]
      have hmoment (i : Fin m) : (∫ x in a..b, x ^ j.val * g i p x) = target p j :=
        congrFun (hgmom i p) j
      simp_rw [hmoment]
      rw [← Finset.sum_mul, hwsum, one_mul]
    · intro i _
      exact (continuousOn_const.mul ((continuous_id.pow j.val).continuousOn.mul
        (hgcont i p))).intervalIntegrable_of_Icc hab.le

/-- Every continuous family of interior moment vectors over a compact Hausdorff
parameter space has a jointly continuous strictly positive probability density
with exactly those moments. No density choice or representing measure is assumed. -/
theorem exists_positive_density_family_of_mem_interior
    {P : Type*} [TopologicalSpace P] [CompactSpace P] [T2Space P]
    {k : ℕ} {a b : ℝ} (hab : a < b) (target : P → MomentVector k)
    (htarget : Continuous target)
    (hinterior : ∀ p, target p ∈ interior (momentBody k a b)) :
    ∃ density : P → ℝ → ℝ,
      ContinuousOn (Function.uncurry density) (univ ×ˢ Icc a b) ∧
      (∀ p x, x ∈ Icc a b → 0 < density p x) ∧
      (∀ p, densityMoments a b (k + 1) (density p) = probabilityMomentVector (target p)) := by
  apply exists_continuous_positive_density_family hab (k + 1)
    (fun p => probabilityMomentVector (target p))
    ((continuous_probabilityMomentVector k).comp htarget)
  intro p
  exact exists_positiveDensity_with_all_moments hab (hinterior p)

end GapFamily.Quadrature
