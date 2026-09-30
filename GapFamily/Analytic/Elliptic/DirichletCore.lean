import GapFamily.Analytic.Elliptic.DirichletGradient

/-!
# The nonnegative operator of a closable gradient core

A genuinely closable densely defined core is first closed as a graph. Its
closed-gradient form then constructs a nonnegative self-adjoint operator.
The original domain remains a graph core. A dense formal divergence domain
is enough to prove closability, so a future modular instantiation can supply
integration by parts instead of assuming a Laplacian.
-/

namespace GapFamily.Analytic.Dirichlet

noncomputable section

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace H] in
/-- A densely defined formal divergence supplies a closed adjoint extension
of the gradient, hence proves that the gradient core is closable. -/
theorem gradient_isClosable_of_formalAdjoint (D : H →ₗ.[ℂ] G) (S : G →ₗ.[ℂ] H)
    (hs : Dense (S.domain : Set G)) (hDS : D.IsFormalAdjoint S) : D.IsClosable :=
  (LinearPMap.adjoint_isClosed hs).isClosable.leIsClosable (hDS.symm.le_adjoint hs)

omit [CompleteSpace H] [CompleteSpace G] in
theorem gradientClosure_dense_domain (D : H →ₗ.[ℂ] G)
    (hd : Dense (D.domain : Set H)) : Dense (D.closure.domain : Set H) :=
  hd.mono D.le_closure.1

/-- The actual operator formed from the closure of a densely defined
closable gradient. Closability excludes the library closure's junk branch. -/
abbrev closableGradientOperator (D : H →ₗ.[ℂ] G) (hD : D.IsClosable)
    (hd : Dense (D.domain : Set H)) : H →ₗ.[ℂ] H :=
  closedGradientOperator D.closure hD.closure_isClosed (gradientClosure_dense_domain D hd)

variable (D : H →ₗ.[ℂ] G) (hD : D.IsClosable) (hd : Dense (D.domain : Set H))

omit [CompleteSpace H] [CompleteSpace G] in
/-- Under genuine closability, the operator closure is exactly the topological
closure of the initial graph; this does not use the fallback closure branch. -/
theorem gradientClosure_graph (hD : D.IsClosable) :
    D.graph.topologicalClosure = D.closure.graph :=
  hD.graph_closure_eq_closure_graph

theorem closableGradientOperator_isSelfAdjoint :
    IsSelfAdjoint (closableGradientOperator D hD hd) :=
  closedGradientOperator_isSelfAdjoint _ _ _

theorem closableGradientOperator_isClosed : (closableGradientOperator D hD hd).IsClosed :=
  (closableGradientOperator_isSelfAdjoint D hD hd).isClosed

theorem closableGradientOperator_dense_domain :
    Dense ((closableGradientOperator D hD hd).domain : Set H) :=
  (closableGradientOperator_isSelfAdjoint D hD hd).dense_domain

theorem closableGradientOperator_nonnegative
    (u : (closableGradientOperator D hD hd).domain) :
    0 ≤ (inner ℂ (closableGradientOperator D hD hd u) (u : H)).re :=
  closedGradientOperator_nonnegative _ _ _ u

/-- The zero mode of the realized operator is exactly the kernel of the
closed gradient; identifying that gradient kernel is an application task. -/
theorem closableGradientOperator_kernel :
    (closableGradientOperator D hD hd).ker = D.closure.ker :=
  closedGradientOperator_kernel _ _ _

omit [CompleteSpace H] [CompleteSpace G] in
/-- This is a graph-core assertion for the closed gradient, not an assertion
that every initial core vector belongs to the second-order operator domain. -/
theorem gradientClosure_hasCore : D.closure.HasCore D.domain := D.closureHasCore

theorem closableGradientOperator_domain_le :
    (closableGradientOperator D hD hd).domain ≤ D.closure.domain :=
  closedGradientOperator_domain_le _ _ _

theorem closableGradientOperator_domain_iff (u : D.closure.domain) :
    (u : H) ∈ (closableGradientOperator D hD hd).domain ↔
      D.closure u ∈ D.closure.adjoint.domain :=
  closedGradientOperator_domain_iff _ _ _ u

theorem closableGradientOperator_value (u : D.closure.domain)
    (hu : D.closure u ∈ D.closure.adjoint.domain) :
    closableGradientOperator D hD hd
      ⟨u, (closableGradientOperator_domain_iff D hD hd u).mpr hu⟩ =
        D.closure.adjoint ⟨D.closure u, hu⟩ :=
  closedGradientOperator_value _ _ _ u hu

omit [CompleteSpace H] [CompleteSpace G] in
/-- On the original core, the closed gradient has exactly the initial value. -/
theorem gradientClosure_apply_core (u : D.domain) :
    D.closure ⟨u, D.le_closure.1 u.property⟩ = D u :=
  (D.le_closure.2 rfl).symm

/-- Membership of an initial core vector in the second-order operator domain
is the genuine adjoint-domain condition on its initial gradient. -/
theorem closableGradientOperator_core_domain_iff (u : D.domain) :
    (u : H) ∈ (closableGradientOperator D hD hd).domain ↔
      D u ∈ D.closure.adjoint.domain := by
  rw [closableGradientOperator_domain_iff D hD hd ⟨u, D.le_closure.1 u.property⟩,
    gradientClosure_apply_core]

end

end GapFamily.Analytic.Dirichlet
