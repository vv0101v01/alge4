# `linalg/` — 有限域線性代數與算子不變子空間格模組（Linear Algebra & Subspace Lattices over $\mathbb{F}_p$）

本資料夾實現素域 $\mathbb{F}_p$ 上的矩陣高斯—約當消去法、核空間與像空間求解，以及向量子空間的格運算（交、和、算子不變閉包與張量積維數定理）。

---

## 檔案清單與所含定理／演算法／公理

### 1. `matrix.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `Matrix` | **$\mathbb{F}_p$-線性映射表示公理** | 以 $m \times n$ 二維陣列表示線性映射 $T : \mathbb{F}_p^n \to \mathbb{F}_p^m$，支援矩陣加法 `add`、純量乘法 `scale`、矩陣乘法 `mul` 與轉置 `transpose`。 |
| `rref(self)` | **高斯—約當列簡化階梯形演算法（Gauss–Jordan Elimination to RREF）** | 在 $\mathbb{F}_p$ 上使用 `inv_mod` 消去主元，輸出唯一簡化列階梯矩陣（Reduced Row Echelon Form）與主元欄索引（Pivot Columns）。 |
| `rank(self)` | **矩陣秩定理（Row Rank = Column Rank Theorem）** | 由 RREF 的非零列數（主元個數）決定線性映射像空間維數 $\dim \mathrm{im}(A)$。 |
| `kernel_basis(self)` | **秩—零化度定理與零空間基底演算法（Rank–Nullity Theorem & Nullspace Basis）** | 對自由變數逐一賦標準基向量並回代主元變數，構造 $\ker(A) = \{v \in \mathbb{F}_p^n \mid Av = 0\}$ 的線性獨立基底，滿足 $\dim \ker(A) + \mathrm{rank}(A) = n$。 |
| `column_space_basis(self)` / `row_space_basis(self)` | **像空間與列空間基底萃取演算法** | 由主元欄／RREF 非零列提取 $\mathrm{im}(A)$ 與 $\mathrm{row}(A)$ 的正規基底。 |
| `solve(self, b)` | **Rouché–Capelli 線性方程組可解性定理** | 藉由增廣矩陣 $[A \mid b]$ 的 RREF 判定 $Ax = b$ 是否有解（當且僅當最後一欄非主元欄），並給出特解。 |
| `inverse(self)` | **方陣可逆性與高斯—約當求逆演算法** | 對 $[A \mid I_n]$ 做 RREF，當 $\mathrm{rank}(A) = n$ 時輸出 $A^{-1} \in \mathrm{GL}_n(\mathbb{F}_p)$。 |

### 2. `subspace.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `Subspace` | **Grassmann 子空間格正規表示定理** | 每個子空間 $U \subseteq \mathbb{F}_p^n$ 由其唯一的 RREF 非零列基底正規表示，故兩個子空間相等 $U = V \iff$ 其 RREF 基底矩陣完全一致。 |
| `subspace_sum(u, v)` | **子空間格並（Join $U + V$）演算法** | 疊加 $U$ 與 $V$ 的基底列並執行 RREF，得到生成子空間 $U + V = \mathrm{span}(U \cup V)$。 |
| `subspace_intersect(u, v)` | **Zassenhaus / 對偶零化子交演算法與 Grassmann 維數公式** | 利用雙重正交補性質 $U \cap V = (U^\perp + V^\perp)^\perp = \ker \begin{bmatrix} \ker(U^\top)^\top \\ \ker(V^\top)^\top \end{bmatrix}$ 求交集，嚴格滿足模格維數定理 $\dim(U + V) + \dim(U \cap V) = \dim U + \dim V$。 |
| `invariant_closure(seed, ops)` | **Knuth–Bendix / 自適應高維算子不變閉包演算法** | 求包含種子向量且在線性算子族 $\{T_k\} \subseteq \mathrm{End}_{\mathbb{F}_p}(\mathbb{F}_p^n)$ 下不變的最小子空間 $\mathrm{cl}(S) = \sum_{w} w(T)(S)$；對低基數載體枚舉全體元素，對高基數載體自動以 RREF 基底佇列避免指數爆炸。 |
| `kronecker_product(a, b)` | **張量積 Kronecker 矩陣積與秩乘性定理** | 構造 $A \otimes B$，滿足 $\mathrm{rank}(A \otimes B) = \mathrm{rank}(A) \cdot \mathrm{rank}(B)$。 |

### 3. `linalg_test.mbt`
- **白盒測試**：驗證 RREF 唯一性、秩—零化度定理 $\dim \ker(A) + \mathrm{rank}(A) = n$、子空間模格律（Modular Law）與 Grassmann 維數恆等式。
