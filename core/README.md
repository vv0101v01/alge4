# `core/` — 64-bit 位並行 $\mathbb{F}_2$ 線性代數、$\mathbb{F}_p$ 高斯消去、鏈複形同調與持久同調模組（Bit-Parallel Linear Algebra, Homology & Persistent Homology）

本資料夾是 `alge3` 的高性能計算核心，利用 64-bit 機器字（`UInt64`）的位元並行 XOR 運算，將 $\mathbb{F}_2$ 上的高斯消去、零空間求取、鏈複形同調群 $H_n(C_*; \mathbb{F}_2)$ 以及濾過持久同調（Persistent Homology）壓縮至極致的硬體吞吐率。

---

## 檔案清單與所含定理／演算法／公理

### 1. `bitset.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `Bits` (`words : Array[UInt64]`) | **布林環／$\mathbb{F}_2$-向量空間的 64-bit 字並行表示公理** | 將長 $n$ 的 $\mathbb{F}_2$ 向量壓縮進 $\lceil n/64 \rceil$ 個 `UInt64` 字中；一次 `xor_inplace` 同步完成 64 個有限域分量的加法。 |
| `popcount64` / `trailing_zeros64` / `first_set` / `weight` | **Brian Kernighan 漢明權重演算法與尾隨零位掃描（CTZ）** | 快速求取位元集基數 $|S|$ 與最小非零元素索引（主元搜尋）。 |

### 2. `f2.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `BoolMat` / `mul` | **位並行矩陣乘法演算法** | 若第 $(i, k)$ 元為 $1$，以整列 `Bits::xor_inplace` 累加第 $k$ 列，在 $O(mn\lceil p/64\rceil)$ 時間內完成 $\mathbb{F}_2$ 矩陣乘法。 |
| `rref_with_pivots(self)` / `rank(self)` | **64-bit 位並行高斯—約當消去演算法（Bit-Parallel Gauss–Jordan Elimination）** | 在 $\mathbb{F}_2$ 上搜尋主元並以整列 XOR 消去上下所有非零元，比標量實作快一個數量級以上。 |
| `kernel(self)` | **$\mathbb{F}_2$ 秩—零化度定理與零空間基底構造** | 由自由欄直接讀出 $\ker(A)$ 的基底位元向量，嚴格滿足 $\dim \ker(A) + \mathrm{rank}(A) = \mathrm{ncols}$。 |

### 3. `fp.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `fp_rref` / `fp_rank` / `fp_kernel` | **素域 $\mathbb{F}_p$ 標量高斯消去與費馬小定理模逆元 `fp_inv`** | 利用費馬小定理 $a^{-1} \equiv a^{p-2} \pmod p$ 求主元逆元，提供任意奇素數特徵下的秩與核空間計算。 |
| `fp_det(mat, p)` | **高斯上三角化行列式演算法（Gaussian Elimination Determinant over $\mathbb{F}_p$）** | 追蹤列交換次數 $(-1)^s$ 與主元乘積，計算 $\det(A) \in \mathbb{F}_p$，滿足 $\det(A) \ne 0 \iff \mathrm{rank}(A) = n$。 |

### 4. `chain.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `ChainComplex` / `is_valid` | **鏈複形基本公理 $\partial_{k} \circ \partial_{k+1} = 0$（$\mathrm{im}\,\partial_{k+1} \subseteq \ker\partial_k$）** | 透過位並行矩陣乘法驗證相鄰邊界算子合成為零矩陣。 |
| `betti(self, k)` / `all_betti` | **同調群維數公式（Homology Betti Number Theorem）** | 定理：$\beta_k = \dim_{\mathbb{F}_2} H_k(C_*) = \dim \ker(\partial_k) - \dim \mathrm{im}(\partial_{k+1}) = (\dim C_k - \mathrm{rank}\,\partial_k) - \mathrm{rank}\,\partial_{k+1}$。 |
| `euler_characteristic(self)` | **Euler–Poincaré 公式（Euler–Poincaré Characteristic Theorem）** | 定理：鏈複形的交錯維數和恆等於同調 Betti 數的交錯和：$\chi(C_*) = \sum_k (-1)^k \dim C_k = \sum_k (-1)^k \beta_k$。 |

### 5. `persist.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `FilteredComplex` / `compute_persistence` | **Edelsbrunner–Letscher–Zomorodian 持久同調歸約演算法（Standard Boundary Matrix Reduction）** | 將濾過單純複形依進入時間排序，對全維度邊界矩陣由左至右以 XOR 消去最低非零列指標 `low(j)` 的衝突，提取拓撲特徵的誕生—死亡配對 `(birth, death)` 與無窮存活條碼（Persistence Barcode）。 |

### 6. `core_wbtest.mbt`
- **白盒測試**：驗證位元集運算、$\mathbb{F}_2$/$\mathbb{F}_p$ 秩—零化度定理、行列式乘性、鏈複形 Euler–Poincaré 定理與圓周濾過的持久同調條碼。
