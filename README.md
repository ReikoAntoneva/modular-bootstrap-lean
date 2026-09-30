# Modular Bootstrap: Lean formalization

[中文](README.zh-CN.md)

This repository formalizes the gap-family existence theorem (Theorem 2.2) and the all-orders smoothed BTZ entropy expansion (Proposition 2.3) of the accompanying Modular Bootstrap paper.

**Paper:** [arXiv:2609.39930](https://arxiv.org/abs/2609.39930).

## Result

* **Theorem 2.2: proportional and fixed primary-gap families**

    * Declaration: `GapFamily.gap_families`
    * Proof: [GapFamily/GapFamily.lean](GapFamily/GapFamily.lean)
    * Definition: [GapFamily/Contract.lean](GapFamily/Contract.lean), [GapFamily/GapFamilyContract.lean](GapFamily/GapFamilyContract.lean)
    * Remark: The formalization proves this theorem and additionally ensures that the lowest primary in the constructed spectrum families is unique, scalar, and of multiplicity one.

* **Proposition 2.3: all-orders smoothed entropy for a fixed-gap family**

    * Declaration: `BTZEntropy.smoothBTZEntropy_fixedGap`
    * Proof: [BTZEntropy/SmoothEntropy.lean](BTZEntropy/SmoothEntropy.lean)
    * Definition: [BTZEntropy/Contract.lean](BTZEntropy/Contract.lean), [BTZEntropy/Observable.lean](BTZEntropy/Observable.lean), [BTZEntropy/Coefficient.lean](BTZEntropy/Coefficient.lean)

## Layout

* `GapFamily/`: spectrum definitions, construction, and Theorem 2.2.
* `BTZEntropy/`: the observable, coefficients, analytic estimates, and Proposition 2.3.
* `Audit/`: axiom inspection entry point.
* `vendor/`: required third-party proof source with provenance and licensing information.
* `script/`: reproducible verification command.

The Lean source comprises approximately 158k lines, rising to 217k with vendored third-party source and 2,560k with the complete mathlib library.

## Verification

The following commands fetch the dependency cache, build the project, and audit axiom dependencies.

```sh
git clone https://github.com/ReikoAntoneva/modular-bootstrap-lean.git
cd modular-bootstrap-lean
lake exe cache get
./script/verify.sh
```

* Install Lean and Lake through [elan](https://github.com/leanprover/elan).
* The toolchain is pinned to `leanprover/lean4:v4.35.0-rc3`; mathlib is pinned in `lakefile.toml` and `lake-manifest.json`.
* `verify.sh` permits only `propext`, `Classical.choice`, and `Quot.sound`.

## License

The original code is distributed under [Apache-2.0](LICENSE). Third-party source retains its own license and attribution; see the notices and license files under `vendor/`.
