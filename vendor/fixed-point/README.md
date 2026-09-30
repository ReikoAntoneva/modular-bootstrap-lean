# Fixed-point proof

Five modules from [harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838), commit `770940ddf9878cf61952ed53d910b92bca841838`, with the [MIT license](LICENSE).

The included source is adapted to this project's pinned Lean/mathlib. [compatibility.patch](compatibility.patch) records proof-elaboration and noncomputable-annotation changes; the statement of `brouwer_fixed_point` is unchanged. The patch is already applied.

[GapFamily/Quadrature/FixedPoint.lean](../../GapFamily/Quadrature/FixedPoint.lean) supplies the centre-attainment application. [GapFamily/Quadrature/UnitNodes.lean](../../GapFamily/Quadrature/UnitNodes.lean) applies it to obtain exactly the prescribed number of unit nodes. These sources build with the normal Lake project.
