import GapFamily.Layer
import GapFamily.Convergence

/-! Actual finite prefixes of the permanent unit-node spectrum and transfer
of modularity from complete corrections whose residuals vanish. -/
noncomputable section
namespace GapFamily.Construction
open Filter
open scoped Topology UpperHalfPlane

variable {initialCount : ℕ} {layerCount : ℕ → ℕ}

/-- The literal marker, initial block, and first `n` complete finite layers.
Repeated coordinates remain distinct unit nodes at this stage. -/
def permanentNodePrefix {A : Type*} [AddCommMonoid A]
    (term : Layer.Node initialCount layerCount → A) (n : ℕ) : A :=
  term (Layer.marker initialCount layerCount) +
    ∑ i : Fin initialCount, term (Sum.inr (Sum.inl i)) +
      ∑ m ∈ Finset.range n, ∑ i : Fin (layerCount m), term (Sum.inr (Sum.inr ⟨m, i⟩))

@[simp] theorem permanentNodePrefix_zero {A : Type*} [AddCommMonoid A]
    (term : Layer.Node initialCount layerCount → A) :
    permanentNodePrefix term 0 = term (Layer.marker initialCount layerCount) +
      ∑ i : Fin initialCount, term (Sum.inr (Sum.inl i)) := by
  simp [permanentNodePrefix]

theorem permanentNodePrefix_succ {A : Type*} [AddCommMonoid A]
    (term : Layer.Node initialCount layerCount → A) (n : ℕ) :
    permanentNodePrefix term (n + 1) = permanentNodePrefix term n +
      ∑ i : Fin (layerCount n), term (Sum.inr (Sum.inr ⟨n, i⟩)) := by
  simp only [permanentNodePrefix, Finset.sum_range_succ, add_assoc]

section Banach
variable {A : Type*} [NormedAddCommGroup A] [CompleteSpace A]

/-- The actual layer totals are summable once the full unit-node family is. -/
theorem summable_permanentLayer
    (term : Layer.Node initialCount layerCount → A) (hsum : Summable term) :
    Summable (fun m => ∑ i : Fin (layerCount m), term (Sum.inr (Sum.inr ⟨m, i⟩))) := by
  have htail : Summable (fun p : Σ m, Fin (layerCount m) => term (Sum.inr (Sum.inr p))) :=
    (hsum.comp_injective Sum.inr_injective).comp_injective Sum.inr_injective
  simpa only [tsum_fintype] using htail.sigma

/-- Absolute convergence justifies the exact marker/initial/layer regrouping
of the same permanent unit-node series. -/
theorem tsum_permanentNode_eq
    (term : Layer.Node initialCount layerCount → A) (hsum : Summable term) :
    (∑' i, term i) = term (Layer.marker initialCount layerCount) +
      ∑ i : Fin initialCount, term (Sum.inr (Sum.inl i)) +
        ∑' m, ∑ i : Fin (layerCount m), term (Sum.inr (Sum.inr ⟨m, i⟩)) := by
  have hright : Summable
      (fun i : Fin initialCount ⊕ (Σ m, Fin (layerCount m)) => term (Sum.inr i)) :=
    hsum.comp_injective Sum.inr_injective
  have htail : Summable (fun p : Σ m, Fin (layerCount m) => term (Sum.inr (Sum.inr p))) :=
    hright.comp_injective Sum.inr_injective
  rw [Summable.tsum_sum (f := term) (Summable.of_finite) hright,
    Summable.tsum_sum (f := fun i => term (Sum.inr i)) (Summable.of_finite) htail,
    htail.tsum_sigma]
  simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton, Layer.marker, add_assoc]

/-- The finite construction stages converge to the genuine full node series.
The summability hypothesis is the actual absolute norm sum, not a formal tsum. -/
theorem tendsto_permanentNodePrefix
    (term : Layer.Node initialCount layerCount → A)
    (hsum : Summable (fun i => ‖term i‖)) :
    Tendsto (permanentNodePrefix term) atTop (𝓝 (∑' i, term i)) := by
  have hlayer := summable_permanentLayer term hsum.of_norm
  have hlimit := (tendsto_const_nhds (x := term (Layer.marker initialCount layerCount) +
    ∑ i : Fin initialCount, term (Sum.inr (Sum.inl i)))).add hlayer.hasSum.tendsto_sum_nat
  rw [tsum_permanentNode_eq term hsum.of_norm]
  exact hlimit

/-- The omitted permanent-node tail itself tends to zero. -/
theorem tendsto_permanentNode_tail
    (term : Layer.Node initialCount layerCount → A)
    (hsum : Summable (fun i => ‖term i‖)) :
    Tendsto (fun n => (∑' i, term i) - permanentNodePrefix term n) atTop (𝓝 0) := by
  simpa only [sub_self] using
    (tendsto_const_nhds (x := ∑' i, term i)).sub (tendsto_permanentNodePrefix term hsum)

end Banach

/-- Complete corrections approach the same permanent-node sum whenever their
residual after subtracting its actual finite prefix tends to zero. -/
theorem tendsto_nodeSeries_of_remainder
    (term : Layer.Node initialCount layerCount → ℍ → ℂ) (base : ℍ → ℂ)
    (F : ℕ → ℍ → ℂ)
    (hsum : ∀ τ, Summable (fun i => ‖term i τ‖))
    (hremainder : ∀ τ, Tendsto
      (fun n => F n τ - (base τ + permanentNodePrefix (fun i => term i τ) n))
      atTop (𝓝 0)) :
    ∀ τ, Tendsto (fun n => F n τ) atTop (𝓝 (base τ + ∑' i, term i τ)) := by
  intro τ
  simpa only [sub_add_cancel, zero_add] using
    (hremainder τ).add
      ((tendsto_const_nhds (x := base τ)).add
        (tendsto_permanentNodePrefix (fun i => term i τ) (hsum τ)))

/-- Only the complete correction functions are required to be invariant.
No finite primary-node prefix is assumed modular. -/
theorem nodeSeries_invariant_of_remainder
    (transform : ℍ → ℍ) (term : Layer.Node initialCount layerCount → ℍ → ℂ)
    (base : ℍ → ℂ) (F : ℕ → ℍ → ℂ)
    (hsum : ∀ τ, Summable (fun i => ‖term i τ‖))
    (hinvariant : ∀ n τ, F n (transform τ) = F n τ)
    (hremainder : ∀ τ, Tendsto
      (fun n => F n τ - (base τ + permanentNodePrefix (fun i => term i τ) n))
      atTop (𝓝 0)) :
    ∀ τ, base (transform τ) + (∑' i, term i (transform τ)) =
      base τ + ∑' i, term i τ :=
  invariant_of_pointwise_tendsto transform F _ hinvariant
    (tendsto_nodeSeries_of_remainder term base F hsum hremainder)

/-- The same complete correction sequence transfers both modular generators
to the actual permanent-node limit. -/
theorem nodeSeries_modular_of_remainder
    (term : Layer.Node initialCount layerCount → ℍ → ℂ) (base : ℍ → ℂ)
    (F : ℕ → ℍ → ℂ)
    (hsum : ∀ τ, Summable (fun i => ‖term i τ‖))
    (hS : ∀ n τ, F n (ModularGroup.S • τ) = F n τ)
    (hT : ∀ n τ, F n (ModularGroup.T • τ) = F n τ)
    (hremainder : ∀ τ, Tendsto
      (fun n => F n τ - (base τ + permanentNodePrefix (fun i => term i τ) n))
      atTop (𝓝 0)) :
    (∀ τ, base (ModularGroup.S • τ) + (∑' i, term i (ModularGroup.S • τ)) =
      base τ + ∑' i, term i τ) ∧
    (∀ τ, base (ModularGroup.T • τ) + (∑' i, term i (ModularGroup.T • τ)) =
      base τ + ∑' i, term i τ) :=
  ⟨nodeSeries_invariant_of_remainder _ term base F hsum hS hremainder,
    nodeSeries_invariant_of_remainder _ term base F hsum hT hremainder⟩

end GapFamily.Construction
