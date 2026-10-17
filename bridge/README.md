# `bridge/` — `algo` 與 `alge3` 六大跨庫數學橋接層（Cross-Package Mathematical Bridge Layer）

本資料夾提供連接 `algo`（抽象代數、Gröbner 基、有限環、模論、仿射概形、HoTT）與 `alge3`（64-bit 位並行線性代數、單純同調、$A_\infty$-代數、奇點導出形變、立方體單價）的六座雙向結構轉換橋樑。

---

## 檔案清單與所含定理／演算法／公理

### 1. `bridge.mbt`
| 橋接編號与函數 | 連接的兩端套件 | 所實現的跨庫定理與演算法 |
| :--- | :--- | :--- |
| **橋 1**：`matrix_to_boolmat`, `boolmat_to_matrix`, `matrix_det` | `@linalg.Matrix` $\Longleftrightarrow$ `@core.BoolMat` / `@core.fp_det` | **位並行加速與行列式判準定理**：將特徵 $p=2$ 的矩陣無損轉為 64-bit `BoolMat` 執行位並行高斯消去與核空間計算，並為任意 $\mathbb{F}_p$ 方陣補上行列式 $\det(A) \ne 0 \iff \mathrm{rank}(A) = n$。 |
| **橋 2**：`equiv_to_iso`, `iso_to_equiv`, `crt_cubical_iso` | `@hott.Equiv` $\Longleftrightarrow$ `@cubical.Iso` $\longrightarrow$ `@cubical.ua` | **中國剩餘定理單價路徑提升定理**：將 `@hott` 的有限型別等價與中國剩餘定理同構 $\mathbb{Z}/n\mathbb{Z} \simeq \prod \mathbb{Z}/p_i^{k_i}\mathbb{Z}$ 具體化為 `@cubical.Iso`，直接送入 `@cubical.ua` 構造宇宙中的單價路徑並執行 Kan 搬運。 |
| **橋 3**：`poly_to_derived`, `derived_to_poly`, `groebner_milnor_number`, `groebner_tjurina_number` | `@poly.Poly` / `groebner_basis` $\Longleftrightarrow$ `@derived.PolyTerm` | **Gröbner 商代數維數＝奇點局部截斷 Milnor/Tjurina 數對偶定理**：用 Buchberger 演算法與 `@finite.FinAlg::zero_dim_quotient` 直接計算奇點 Jacobi 商環維數，與 `@derived` 的分次截斷矩陣法交叉驗證。 |
| **橋 4**：`finalg_mul_monoid`, `finalg_unit_group_monoid`, `finalg_unit_bar_betti` | `@finite.FinAlg` $\longrightarrow$ `@homotopy.Monoid` | **有限交換代數分類空間神經與群同調橋接**：將有限環的乘法么半群 $(R, \cdot, 1)$ 與單位群 $R^\times$ 轉為 `@homotopy.Monoid`，直接計算分類空間 $B(R^\times)$ 的正規化 Bar 同調 Betti 數 $H_*(R^\times; \mathbb{F}_2)$。 |
| **橋 5**：`finalg_to_ainf` | `@finite.FinAlg` ($p=2$) $\longrightarrow$ `@algebra.AInf` | **交換結合代數作為退化 $A_\infty$-代數定理**：將特徵 $2$ 的有限商環（$m_1=0, m_2=\text{mul}, m_3=0$）嵌入 `@algebra.AInf`，以 Stasheff 恆等式自動檢驗環乘法結合律。 |
| **橋 6**：`spec_opens_to_bits`, `variety_points_count`, `free_module_rank_check` | `@scheme.Spec` / `@geometry` / `@modules` $\longrightarrow$ `@core.Bits` | **Zariski 開集格的位並行外延嵌入**：將 $\mathrm{Spec}(R)$ 的全體開集編碼為 `@core.Bits` 位元向量並驗證格交並同構。 |

### 2. `bridge_wbtest.mbt`
- **白盒測試**：逐一驗證上述六座跨庫橋樑的同構性、數值一致性與同調不變量。
