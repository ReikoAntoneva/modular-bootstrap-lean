# Interior weak-Hessian proof

139 adapted modules from [CoarseGraining](https://github.com/scottnarmstrong/CoarseGraining/tree/28ca42c02fd286c8f63a45be3344f6f82d026db3), commit `28ca42c02fd286c8f63a45be3344f6f82d026db3`, under its Apache-2.0 license, plus one shared lemma module. The source and already-applied [compatibility patch](compatibility.patch) are included.

The included source uses this project's pinned Lean/mathlib. The helper `Homogenization.tendsto_eLpNorm_zero_of_ae_norm_le_mul_norm` takes per-term `AEStronglyMeasurable` witnesses supplied by its caller's L² data. The descendant-layer definition uses explicit `Nat.rec`. The weak-Hessian target and the descendant-layer defining equations are preserved.

Shared weak-derivative restriction and smooth-function lemmas are defined in [WeakDerivativeLemmas.lean](Homogenization/Sobolev/WeakDerivativeLemmas.lean), imported by both `H1/BasicLemmas.lean` and `W1p/BasicLemmas.lean`.

The theorem derives interior L² weak Hessians from first weak derivatives, a weak Poisson equation and L² forcing. Its local applications are [GapFamily/Analytic/Elliptic/LocalWeakHessianApproximation.lean](../../GapFamily/Analytic/Elliptic/LocalWeakHessianApproximation.lean) and [GapFamily/Analytic/Poincare/PoincareHighCuspHessian.lean](../../GapFamily/Analytic/Poincare/PoincareHighCuspHessian.lean). These sources build with the normal Lake project.
