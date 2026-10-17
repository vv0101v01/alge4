# `verify/` — Why3 形式化霍爾邏輯契約與算術定理機器證明模組（Formal Verification & Hoare Logic Contracts）

本資料夾包含附帶形式化前置條件（`requires`）、後置條件（`ensures`）與迴圈不變量（`invariant` / `variant`）的算術與數論演算法，配合根目錄的 `prove.sh` 與 `prelude/moonbit_builtin_prelude.mlw` 可直接產生 Why3 驗證條件（Verification Conditions, VCs）。

---

## 檔案清單與所含定理／演算法／公理

### 1. `arith.mbt` & `arith.mbtp`
| 函數／契約證明目標 | 形式化霍爾邏輯定理（Hoare Triple $\{P\}\;c\;\{Q\}$） | 說明 |
| :--- | :--- | :--- |
| `verified_gcd(a, b)` | **歐幾里得演算法終止性與公因數不變量定理** | 前置條件：$a \ge 0 \land b \ge 0$；<br>迴圈不變量：$\gcd(x, y) = \gcd(a, b) \land x \ge 0 \land y \ge 0$；<br>嚴格遞減變量（Variant）：$y$；<br>後置條件：返回值 $r \ge 0$ 且整除 $a$ 與 $b$。 |
| `verified_mod_add` / `verified_pow` | **模算術範圍安全定理與非負冪次歸納不變量** | 形式化證明模加法結果嚴格落在 $[0, m)$ 內，以及指數累乘在每步迭代中保持 $acc \cdot base^{rem} = base_0^{exp_0}$。 |
