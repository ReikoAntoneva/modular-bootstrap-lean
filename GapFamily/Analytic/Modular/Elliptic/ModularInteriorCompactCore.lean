import GapFamily.Analytic.Modular.ModularResolvent
import Mathlib.Topology.Sequences

/-!
# Smooth graph-core approximation in the actual modular form domain

The completed form domain is the graph of the actual closed modular gradient.
Its defining graph-closure theorem gives smooth automorphic approximants in
the mass-plus-energy norm. No abstract core-density hypothesis is used.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set Filter Dirichlet
open scoped Topology

/-- A genuine smooth automorphic function viewed in the completed form domain. -/
def coreForm : smoothCore →ₗ[ℂ] FormDomain where
  toFun F := formLift
    ⟨value F, gradient_le_closedGradient.1 (LinearMap.mem_range_self value F)⟩
  map_add' F G := by
    apply formEmbedding_injective
    change value (F + G) = value F + value G
    exact value.map_add F G
  map_smul' c F := by
    apply formEmbedding_injective
    change value (c • F) = c • value F
    exact value.map_smul c F

@[simp] theorem formEmbedding_coreForm (F : smoothCore) :
    formEmbedding (coreForm F) = value F := rfl

@[simp] theorem formGradient_coreForm (F : smoothCore) :
    formGradient (coreForm F) = coreGradient F :=
  closedGradient_apply_value F

theorem coreForm_norm_sq (F : smoothCore) :
    ‖coreForm F‖ ^ 2 = ‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2 := by
  simpa only [formEmbedding_coreForm, formGradient_coreForm] using
    formDomain_norm_sq (coreForm F)

theorem value_norm_le_coreForm (F : smoothCore) : ‖value F‖ ≤ ‖coreForm F‖ :=
  gradientEmbedding_norm_le closedGradient (coreForm F)

theorem coreGradient_norm_le_coreForm (F : smoothCore) :
    ‖coreGradient F‖ ≤ ‖coreForm F‖ := by
  simpa only [formGradient_coreForm] using
    gradientValue_norm_le closedGradient (coreForm F)

theorem gradient_graph_eq_core_range :
    (gradient.graph : Set (ModularHilbert × GradientSpace)) =
      Set.range (fun F : smoothCore => (value F, coreGradient F)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨u, rfl⟩ := gradient.mem_graph_iff'.mp hp
    rcases u with ⟨u, hu⟩
    change u ∈ value.range at hu
    obtain ⟨F, rfl⟩ := hu
    exact ⟨F, Prod.ext rfl (gradient_apply_value F).symm⟩
  · rintro ⟨F, rfl⟩
    change (value F, coreGradient F) ∈ gradient.graph
    simpa only [gradient_apply_value] using
      gradient.mem_graph ⟨value F, LinearMap.mem_range_self value F⟩

/-- Graph closure gives actual smooth approximants in the complete form norm. -/
theorem exists_coreForm_tendsto (u : FormDomain) :
    ∃ F : ℕ → smoothCore, Tendsto (fun n => coreForm (F n)) atTop (𝓝 u) := by
  have hu : (formEmbedding u, formGradient u) ∈
      closure (gradient.graph : Set (ModularHilbert × GradientSpace)) := by
    have hu := u.property
    change WithLp.ofLp u.val ∈ closedGradient.graph at hu
    rw [closedGradient_graph] at hu
    exact hu
  rw [gradient_graph_eq_core_range] at hu
  obtain ⟨p, hp, ht⟩ := mem_closure_iff_seq_limit.mp hu
  choose F hF using hp
  refine ⟨F, tendsto_subtype_rng.mpr ?_⟩
  have hc := (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert GradientSpace).symm.continuous
  have ht' := hc.continuousAt.tendsto.comp ht
  have hval (n : ℕ) : (coreForm (F n)).val =
      (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert GradientSpace).symm (p n) := by
    rw [← hF n]
    change WithLp.toLp 2 (value (F n),
      closedGradient ⟨value (F n), _⟩) = WithLp.toLp 2 (value (F n), coreGradient (F n))
    rw [closedGradient_apply_value]
  have huval :
      (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert GradientSpace).symm
        (formEmbedding u, formGradient u) = u.val := by
    change WithLp.toLp 2 (WithLp.ofLp u.val) = u.val
    rfl
  simpa only [Function.comp_def, hval, huval] using ht'

/-- The range of the actual smooth core is dense for the mass-plus-energy norm. -/
theorem coreForm_denseRange : DenseRange coreForm := by
  intro u
  obtain ⟨F, hF⟩ := exists_coreForm_tendsto u
  exact mem_closure_of_tendsto hF (Eventually.of_forall fun n => ⟨F n, rfl⟩)

/-- Approximation with a uniform bound independent of the approximation index. -/
theorem exists_coreForm_tendsto_bounded (u : FormDomain) :
    ∃ F : ℕ → smoothCore,
      Tendsto (fun n => coreForm (F n)) atTop (𝓝 u) ∧
      ∀ n, ‖coreForm (F n)‖ ≤ ‖u‖ + 1 := by
  obtain ⟨F, hF⟩ := exists_coreForm_tendsto u
  have he : ∀ᶠ n in atTop, coreForm (F n) ∈ Metric.ball u 1 :=
    hF.eventually (Metric.ball_mem_nhds u zero_lt_one)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hs : Tendsto (fun n : ℕ => n + N) atTop atTop := by
    refine tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨b, ?_⟩)
    intro n hn
    omega
  refine ⟨fun n => F (n + N), hF.comp hs, ?_⟩
  intro n
  have hd := hN (n + N) (by omega)
  rw [Metric.mem_ball, dist_eq_norm] at hd
  have ht := norm_add_le (coreForm (F (n + N)) - u) u
  rw [sub_add_cancel] at ht
  linarith

/-- The bounded graph approximants converge in both actual modular `L²` coordinates. -/
theorem exists_smoothCore_graph_approximation (u : FormDomain) :
    ∃ F : ℕ → smoothCore,
      Tendsto (fun n => value (F n)) atTop (𝓝 (formEmbedding u)) ∧
      Tendsto (fun n => coreGradient (F n)) atTop (𝓝 (formGradient u)) ∧
      (∀ n, ‖value (F n)‖ ^ 2 + ‖coreGradient (F n)‖ ^ 2 ≤ (‖u‖ + 1) ^ 2) := by
  obtain ⟨F, hF, hb⟩ := exists_coreForm_tendsto_bounded u
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, formEmbedding_coreForm] using
      formEmbedding.continuous.continuousAt.tendsto.comp hF
  · simpa only [Function.comp_def, formGradient_coreForm] using
      formGradient.continuous.continuousAt.tendsto.comp hF
  · intro n
    rw [← coreForm_norm_sq]
    nlinarith [hb n, norm_nonneg (coreForm (F n)), norm_nonneg u]

end GapFamily.Analytic.ModularGradient
