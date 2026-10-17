# `geometry/` — 有限域仿射代數幾何與 Hilbert 零點定理模組（Affine Algebraic Geometry over $\mathbb{F}_p$）

本資料夾實現有限域 $\mathbb{F}_p$ 上的經典仿射代數幾何，建立多項式理想 $I \subseteq \mathbb{F}_p[x_1, \dots, x_n]$ 與仿射簇 $V(I) \subseteq \mathbb{A}^n(\mathbb{F}_p)$ 之間的伽羅瓦伴隨（Zariski 閉包對應）與座標環求值同態。

---

## 檔案清單與所含定理／演算法／公理

### 1. `geometry.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `affine_space(p, n)` | **有限仿射空間 $\mathbb{A}^n(\mathbb{F}_p) = \mathbb{F}_p^n$ 枚舉** | 枚舉 $p^n$ 個有理點並支援字典序正規化。 |
| `vanishing_locus(p, n, gens)` | **零點集算子 $V(I) = \{a \in \mathbb{F}_p^n \mid \forall f \in I,\, f(a) = 0\}$** | 對多項式生成元族計算其在 $\mathbb{A}^n(\mathbb{F}_p)$ 上的共同零點代數簇。 |
| `vanishing_ideal_generators(p, n, pts)` | **消失理想算子 $I(S) = \{f \in \mathbb{F}_p[x_1, \dots, x_n] \mid \forall a \in S,\, f(a) = 0\}$ 與有限域強零點定理** | 利用拉格朗日插值特徵函數與有限域關係式 $x_i^p - x_i = 0$，構造點集 $S$ 的消失理想生成元。 |
| `zariski_closure(p, n, pts)` | **Zariski 拓撲閉包定理 $\overline{S} = V(I(S))$** | 在有限空間 $\mathbb{A}^n(\mathbb{F}_p)$ 中，任意子集皆為代數閉集：$V(I(S)) = S$，且 $(V, I)$ 構成反變伽羅瓦連接（Antitone Galois Connection）：$S \subseteq V(J) \iff J \subseteq I(S)$。 |
| `variety_union` / `variety_intersect` | **Zariski 閉集拓撲公理 $V(I) \cap V(J) = V(I + J)$、$V(I) \cup V(J) = V(I \cdot J)$** | 驗證理想和對應代數簇交、理想積（或交）對應代數簇並。 |
| `eval_algebra_dimension(p, n, gens)` | **有限域 Hilbert 零點定理與座標環維數定理** | 對含域方程 $x_i^p - x_i$ 的根理想，座標環 $\mathbb{F}_p[x_1, \dots, x_n]/I(V)$ 同構於函數環 $\mathrm{Map}(V, \mathbb{F}_p) \cong \mathbb{F}_p^{|V|}$，故其 $\mathbb{F}_p$-維數恆等於有理點個數 $|V|$。 |

### 2. `geometry_tests_wbtest.mbt`
- **白盒測試**：驗證伽羅瓦伴隨恆等式 $V(I(V(J))) = V(J)$、Zariski 拓撲交並定律與座標環求值同構維數定理。
