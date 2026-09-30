import GapFamily.Analytic.Foundation.ReferenceMeasure
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Density of polynomials in the exponential energy coordinate

Every complex square-integrable function on an energy half-line for a finite
Borel measure is approximated by actual polynomials in `exp (-E)`. The proof
compactifies the half-line, applies polynomial and continuous-function density,
and pulls the approximation back without changing its L² error.
-/

open Set MeasureTheory Polynomial
open scoped Topology ENNReal

namespace GapFamily.Analytic

noncomputable def complexPolynomialOn (p q : ℝ[X]) : C(Icc (0 : ℝ) 1, ℂ) :=
  ⟨fun t => ((p.eval (t : ℝ) : ℝ) : ℂ) + Complex.I * ((q.eval (t : ℝ) : ℝ) : ℂ), by fun_prop⟩

theorem exists_complexPolynomialOn_near (f : C(Icc (0 : ℝ) 1, ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℝ[X], ‖complexPolynomialOn p q - f‖ < ε := by
  let fre : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun t => (f t).re, by fun_prop⟩
  let fim : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun t => (f t).im, by fun_prop⟩
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 fre (ε / 2) (half_pos hε)
  obtain ⟨q, hq⟩ := exists_polynomial_near_continuousMap 0 1 fim (ε / 2) (half_pos hε)
  refine ⟨p, q, ?_⟩
  rw [ContinuousMap.norm_lt_iff _ hε]
  intro t
  have hpt : |p.eval (t : ℝ) - (f t).re| < ε / 2 :=
    ((p.toContinuousMapOn (Icc (0 : ℝ) 1) - fre).norm_coe_le_norm t).trans_lt hp
  have hqt : |q.eval (t : ℝ) - (f t).im| < ε / 2 :=
    ((q.toContinuousMapOn (Icc (0 : ℝ) 1) - fim).norm_coe_le_norm t).trans_lt hq
  have heq : (complexPolynomialOn p q - f) t =
      ((p.eval (t : ℝ) - (f t).re : ℝ) : ℂ) +
        Complex.I * ((q.eval (t : ℝ) - (f t).im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [complexPolynomialOn]
  rw [heq]
  calc
    _ ≤ ‖((p.eval (t : ℝ) - (f t).re : ℝ) : ℂ)‖ +
        ‖Complex.I * ((q.eval (t : ℝ) - (f t).im : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |p.eval (t : ℝ) - (f t).re| + |q.eval (t : ℝ) - (f t).im| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    _ < ε := by linarith

theorem complexPolynomialOn_denseRange :
    DenseRange (fun pq : ℝ[X] × ℝ[X] => complexPolynomialOn pq.1 pq.2) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨p, q, h⟩ := exists_complexPolynomialOn_near f hε
  exact ⟨(p, q), by simpa only [dist_eq_norm, norm_sub_rev] using h⟩

theorem complexPolynomialOn_toLp_denseRange (μ : Measure (Icc (0 : ℝ) 1))
    [IsFiniteMeasure μ] :
    DenseRange (fun pq : ℝ[X] × ℝ[X] =>
      ContinuousMap.toLp (E := ℂ) 2 μ ℂ (complexPolynomialOn pq.1 pq.2)) := by
  exact (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).comp
    complexPolynomialOn_denseRange (ContinuousLinearMap.continuous _)

theorem exists_polynomial_eLpNorm_sub_lt (μ : Measure (Icc (0 : ℝ) 1))
    [IsFiniteMeasure μ] {f : Icc (0 : ℝ) 1 → ℂ} (hf : MemLp f 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℝ[X], eLpNorm (f - (complexPolynomialOn p q : _ → ℂ)) 2 μ < ENNReal.ofReal ε := by
  obtain ⟨⟨p, q⟩, h⟩ := (complexPolynomialOn_toLp_denseRange μ).exists_dist_lt (hf.toLp f) hε
  refine ⟨p, q, ?_⟩
  have heq : edist (hf.toLp f) (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (complexPolynomialOn p q)) =
      eLpNorm (f - (complexPolynomialOn p q : _ → ℂ)) 2 μ := by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae (hf.coeFn_toLp.sub (ContinuousMap.coeFn_toLp μ _))
  rw [← heq, edist_dist]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.mpr h

noncomputable def energyExpMap {a : ℝ} (ha : 0 ≤ a) (E : Ioi a) : Icc (0 : ℝ) 1 :=
  ⟨Real.exp (- (E : ℝ)), (Real.exp_pos _).le,
    (Real.exp_le_one_iff.mpr (by have hE : a < (E : ℝ) := E.property; linarith))⟩

lemma continuous_energyExpMap {a : ℝ} (ha : 0 ≤ a) : Continuous (energyExpMap ha) := by
  exact (Real.continuous_exp.comp continuous_subtype_val.neg).subtype_mk _

lemma injective_energyExpMap {a : ℝ} (ha : 0 ≤ a) : Function.Injective (energyExpMap ha) := by
  intro E E' h
  apply Subtype.ext
  have hexp : Real.exp (-(E : ℝ)) = Real.exp (-(E' : ℝ)) := congrArg Subtype.val h
  have hneg := Real.exp_injective hexp
  exact neg_injective hneg

lemma measurableEmbedding_energyExpMap {a : ℝ} (ha : 0 ≤ a) :
    MeasurableEmbedding (energyExpMap ha) := by
  have hm : MeasurableEmbedding (fun E : Ioi a => Real.exp (-(E : ℝ))) :=
    ContinuousOn.measurableEmbedding measurableSet_Ioi
      (Real.continuous_exp.comp continuous_neg).continuousOn
      (fun x _ y _ h => neg_injective (Real.exp_injective h))
  refine ⟨injective_energyExpMap ha, (continuous_energyExpMap ha).measurable, ?_⟩
  intro s hs
  convert measurable_subtype_coe (hm.measurableSet_image.mpr hs) using 1
  ext t
  constructor
  · rintro ⟨E, hE, rfl⟩
    exact ⟨E, hE, rfl⟩
  · rintro ⟨E, hE, hEt⟩
    exact ⟨E, hE, Subtype.ext hEt⟩

noncomputable def energyCompactification {a : ℝ} (ha : 0 ≤ a) (f : Ioi a → ℂ) :
    Icc (0 : ℝ) 1 → ℂ :=
  Function.extend (energyExpMap ha) f (fun _ => 0)

lemma energyCompactification_energyExpMap {a : ℝ} (ha : 0 ≤ a) (f : Ioi a → ℂ) (E : Ioi a) :
    energyCompactification ha f (energyExpMap ha E) = f E :=
  (injective_energyExpMap ha).extend_apply f (fun _ => 0) E

lemma energyCompactification_comp_energyExpMap {a : ℝ} (ha : 0 ≤ a) (f : Ioi a → ℂ) :
    energyCompactification ha f ∘ energyExpMap ha = f :=
  Function.extend_comp (injective_energyExpMap ha) f (fun _ => 0)

lemma memLp_energyCompactification {a : ℝ} (ha : 0 ≤ a) {μ : Measure (Ioi a)}
    {p : ℝ≥0∞} {f : Ioi a → ℂ} (hf : MemLp f p μ) :
    MemLp (energyCompactification ha f) p (Measure.map (energyExpMap ha) μ) := by
  apply (measurableEmbedding_energyExpMap ha).memLp_map_measure_iff.mpr
  simpa only [energyCompactification_comp_energyExpMap] using hf

lemma eLpNorm_energyCompactification_error {a : ℝ} (ha : 0 ≤ a) {μ : Measure (Ioi a)}
    {p : ℝ≥0∞} (f : Ioi a → ℂ) (g : Icc (0 : ℝ) 1 → ℂ) :
    eLpNorm (fun E => f E - g (energyExpMap ha E)) p μ =
      eLpNorm (energyCompactification ha f - g) p (Measure.map (energyExpMap ha) μ) := by
  rw [(measurableEmbedding_energyExpMap ha).eLpNorm_map_measure]
  congr 1
  ext E
  simp only [Function.comp_apply, Pi.sub_apply, energyCompactification_energyExpMap]

lemma memLp_energyExpMap {a : ℝ} (ha : 0 ≤ a) {μ : Measure (Ioi a)}
    {p : ℝ≥0∞} {g : Icc (0 : ℝ) 1 → ℂ}
    (hg : MemLp g p (Measure.map (energyExpMap ha) μ)) :
    MemLp (g ∘ energyExpMap ha) p μ :=
  (measurableEmbedding_energyExpMap ha).memLp_map_measure_iff.mp hg

/-- Combine real and imaginary coefficient polynomials into one complex polynomial. -/
noncomputable def polynomialOfRealImag (p q : ℝ[X]) : ℂ[X] :=
  p.map Complex.ofRealHom + C Complex.I * q.map Complex.ofRealHom

@[simp] theorem eval_polynomialOfRealImag (p q : ℝ[X]) (t : ℝ) :
    (polynomialOfRealImag p q).eval (t : ℂ) =
      ((p.eval t : ℝ) : ℂ) + Complex.I * ((q.eval t : ℝ) : ℂ) := by
  simp only [polynomialOfRealImag, eval_add, eval_mul, eval_C]
  exact congrArg₂ (fun x y : ℂ => x + Complex.I * y)
    (Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := p) t)
    (Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := q) t)

/-- Actual complex polynomials in `exp (-E)` are dense in L² for every finite
Borel measure on the energy half-line. Both the target and approximant belong
to L²; no polynomial approximation or representing measure is assumed. -/
theorem exists_laplacePolynomial_eLpNorm_sub_lt {a : ℝ} (ha : 0 ≤ a)
    (μ : Measure (Ioi a)) [IsFiniteMeasure μ]
    {f : Ioi a → ℂ} (hf : MemLp f 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X],
      MemLp (fun E : Ioi a => p.eval (Real.exp (-(E : ℝ)) : ℂ)) 2 μ ∧
      eLpNorm (fun E : Ioi a => f E - p.eval (Real.exp (-(E : ℝ)) : ℂ)) 2 μ <
        ENNReal.ofReal ε := by
  let ν := Measure.map (energyExpMap ha) μ
  obtain ⟨p, q, happrox⟩ := exists_polynomial_eLpNorm_sub_lt ν
    (memLp_energyCompactification ha hf) hε
  refine ⟨polynomialOfRealImag p q, ?_, ?_⟩
  · have hp := memLp_energyExpMap ha
      (ContinuousMap.memLp ν ℂ (complexPolynomialOn p q) (p := 2))
    change MemLp (fun E : Ioi a => ((p.eval (Real.exp (-(E : ℝ))) : ℝ) : ℂ) +
      Complex.I * (((q.eval (Real.exp (-(E : ℝ))) : ℝ) : ℂ))) 2 μ at hp
    simpa only [eval_polynomialOfRealImag] using hp
  · have herr := eLpNorm_energyCompactification_error (μ := μ) (p := 2)
      ha f (complexPolynomialOn p q)
    rw [← herr] at happrox
    simpa only [complexPolynomialOn, ContinuousMap.coe_mk, energyExpMap,
      eval_polynomialOfRealImag] using happrox

lemma map_comap_subtype_eq_of_ae_support {α : Type*} [MeasurableSpace α]
    {s : Set α} (hs : MeasurableSet s) {μ : Measure α}
    (hsupport : ∀ᵐ x ∂μ, x ∈ s) :
    (μ.comap (Subtype.val : s → α)).map Subtype.val = μ := by
  rw [map_comap_subtype_coe hs,
    Measure.restrict_eq_self_of_ae_mem hsupport]

lemma memLp_subtype_iff_of_ae_support {α : Type*} [MeasurableSpace α]
    {s : Set α} (hs : MeasurableSet s) {μ : Measure α}
    (hsupport : ∀ᵐ x ∂μ, x ∈ s) {p : ℝ≥0∞} {f : α → ℂ} :
    MemLp (fun x : s => f x) p (μ.comap Subtype.val) ↔ MemLp f p μ := by
  have h := (MeasurableEmbedding.subtype_coe hs).memLp_map_measure_iff
    (g := f) (p := p) (μ := μ.comap Subtype.val)
  rw [map_comap_subtype_eq_of_ae_support hs hsupport] at h
  exact h.symm

lemma eLpNorm_subtype_eq_of_ae_support {α : Type*} [MeasurableSpace α]
    {s : Set α} (hs : MeasurableSet s) {μ : Measure α}
    (hsupport : ∀ᵐ x ∂μ, x ∈ s) {p : ℝ≥0∞} (f : α → ℂ) :
    eLpNorm (fun x : s => f x) p (μ.comap Subtype.val) = eLpNorm f p μ := by
  have h := (MeasurableEmbedding.subtype_coe hs).eLpNorm_map_measure
    (g := f) (p := p) (μ := μ.comap Subtype.val)
  rw [map_comap_subtype_eq_of_ae_support hs hsupport] at h
  exact h.symm

/-- The same density theorem for a measure on the ambient real line which is
concentrated on the physical open half-line. The subtype transfer preserves
both L² membership and the exact approximation error. -/
theorem exists_laplacePolynomial_eLpNorm_sub_lt_of_ae_above {a : ℝ} (ha : 0 ≤ a)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hsupport : ∀ᵐ E ∂μ, a < E)
    {f : ℝ → ℂ} (hf : MemLp f 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], MemLp (fun E => p.eval (Real.exp (-E) : ℂ)) 2 μ ∧
      eLpNorm (fun E => f E - p.eval (Real.exp (-E) : ℂ)) 2 μ < ENNReal.ofReal ε := by
  have hf' := (memLp_subtype_iff_of_ae_support measurableSet_Ioi hsupport).mpr hf
  obtain ⟨p, hp, herr⟩ := exists_laplacePolynomial_eLpNorm_sub_lt ha
    (μ.comap (Subtype.val : Ioi a → ℝ)) hf' hε
  refine ⟨p, (memLp_subtype_iff_of_ae_support measurableSet_Ioi hsupport).mp hp, ?_⟩
  rwa [eLpNorm_subtype_eq_of_ae_support measurableSet_Ioi hsupport
    (fun E => f E - p.eval (Real.exp (-E) : ℂ))] at herr

/-- Polynomial density for the proved finite measure
`ψ(E)^2 * (1+E)^4 dω_j` in every physical spin, including the scalar channel. -/
theorem exists_laplacePolynomial_reference_eLpNorm_sub_lt (j : ℤ)
    {f : ℝ → ℂ} (hf : MemLp f 2 (laplaceReferenceMeasure j))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X],
      MemLp (fun E => p.eval (Real.exp (-E) : ℂ)) 2 (laplaceReferenceMeasure j) ∧
      eLpNorm (fun E => f E - p.eval (Real.exp (-E) : ℂ)) 2
        (laplaceReferenceMeasure j) < ENNReal.ofReal ε :=
  exists_laplacePolynomial_eLpNorm_sub_lt_of_ae_above (abs_nonneg (j : ℝ))
    (laplaceReferenceMeasure j) (laplaceReferenceMeasure_ae_above_edge j) hf hε

end GapFamily.Analytic
