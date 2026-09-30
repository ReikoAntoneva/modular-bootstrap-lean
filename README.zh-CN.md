# Modular Bootstrap：Lean 形式化

[English](README.md)

本仓库形式化证明配套 Modular Bootstrap 论文中的间隙谱族存在性定理（Theorem 2.2）与全阶平滑 BTZ 熵展开（Proposition 2.3）。

**论文：** [arXiv:2609.39930](https://arxiv.org/abs/2609.39930)。

## 结果

* **Theorem 2.2：正比例与固定 primary 间隙谱族**

    * 声明：`GapFamily.gap_families`
    * 证明：[GapFamily/GapFamily.lean](GapFamily/GapFamily.lean)
    * 定义：[GapFamily/Contract.lean](GapFamily/Contract.lean)、[GapFamily/GapFamilyContract.lean](GapFamily/GapFamilyContract.lean)
    * 补充：形式化证明覆盖该定理，并额外保证所构造谱族的最低 primary 唯一、为标量且重数一。

* **Proposition 2.3：固定间隙谱族的全阶平滑熵展开**

    * 声明：`BTZEntropy.smoothBTZEntropy_fixedGap`
    * 证明：[BTZEntropy/SmoothEntropy.lean](BTZEntropy/SmoothEntropy.lean)
    * 定义：[BTZEntropy/Contract.lean](BTZEntropy/Contract.lean)、[BTZEntropy/Observable.lean](BTZEntropy/Observable.lean)、[BTZEntropy/Coefficient.lean](BTZEntropy/Coefficient.lean)

## 目录

* `GapFamily/`：谱定义、构造及 Theorem 2.2。
* `BTZEntropy/`：观测量、系数、分析估计及 Proposition 2.3。
* `Audit/`：公理检查入口。
* `vendor/`：必要第三方证明源码及其来源、许可说明。
* `script/`：可复现的核验命令。

Lean 源码约 158k 行，计入随附第三方源码约 217k 行，计入完整 mathlib 约 2,560k 行。

## 核验

以下命令负责获取依赖缓存、构建项目并运行公理审计。

```sh
git clone https://github.com/ReikoAntoneva/modular-bootstrap-lean.git
cd modular-bootstrap-lean
lake exe cache get
./script/verify.sh
```

* 通过 [elan](https://github.com/leanprover/elan) 安装 Lean 与 Lake。
* 工具链固定为 `leanprover/lean4:v4.35.0-rc3`；mathlib 在 `lakefile.toml` 和 `lake-manifest.json` 中固定版本。
* `verify.sh` 仅允许 `propext`、`Classical.choice` 和 `Quot.sound` 三项公理。

## 许可

原创代码采用 [Apache-2.0](LICENSE)。第三方源码保留原许可证与署名，详见 `vendor/` 下的说明和许可证文件。
