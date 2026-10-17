# `algebra/` — 高階同倫代數（$A_\infty$、$E_\infty$ Steenrod 平方）、自由 Monad 與頂點算子代數（VOA）模組

本資料夾實現現代高階代數與數學物理中的四大結構：Stasheff $A_\infty$-代數、對稱上鏈 $E_\infty$-代數（含杯積 $\smile_i$ 與 Steenrod 平方 $Sq^k$）、帶分配律的自由有根樹 Monad 以及海森堡頂點算子代數（Heisenberg Vertex Operator Algebra）與正規序展開。

---

## 檔案清單與所含定理／演算法／公理

### 1. `ainf.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `AInf` / `stasheff_lhs` / `check_stasheff(n)` | **Stasheff $A_\infty$-代數高階結合公理（Stasheff Associahedron Identities over $\mathbb{F}_2$）** | 對多重線性運算族 $\{m_k : V^{\otimes k} \to V\}_{k=1,2,3}$，全稱檢驗第 $n$ 階 Stasheff 恆等式 $\sum_{r+s+t=n} m_{r+1+t}(\mathrm{id}^{\otimes r} \otimes m_s \otimes \mathrm{id}^{\otimes t}) = 0 \pmod 2$：當 $n=1$ 為 $m_1^2 = 0$（微分）、$n=2$ 為 Leibniz 律、$n=3$ 為 $m_2$ 結合律模去同倫 $m_3$。 |
| `from_dg_alg` / `massey_triple` | **微分分次代數（DGA）嵌入與 Massey 三重積（Massey Triple Product $\langle [x], [y], [z] \rangle$）** | 當 $m_2(x, y) = m_1(a)$ 且 $m_2(y, z) = m_1(b)$ 時，構造高階上同調阻塞類 $m_2(a, z) + m_2(x, b) + m_3(x, y, z)$。 |

### 2. `einfty.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `cup_i(k, i, a, b)` | **Steenrod 高階杯積公式（Higher $\smile_i$ Cochain Products）** | 在標準單純形 $\Delta^k$ 的上鏈空間上，由頂點重疊交錯分割（Alexander–Whitney 推廣公式）顯式構造高階同倫交換算子 $\smile_i$。 |
| `verify_steenrod_homotopy` / `steenrod_sq` | **Steenrod $\smile_i$ 上鏈同倫餘邊界恆等式與 Steenrod 平方 $Sq^k$** | 驗證餘邊界公式 $\delta(a \smile_i b) + \delta a \smile_i b + a \smile_i \delta b = a \smile_{i-1} b + b \smile_{i-1} a \pmod 2$，證明當 $a, b$ 為上閉鏈時杯積在同調層級交換，並定義上同調冪運算 $Sq^{|a|-i}(a) = a \smile_i a$。 |

### 3. `monad.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `Tree[A]` / `pure` / `join` / `bind` | **自由二元樹 Monad 公理（Left/Right Unit & Associativity $\mu \circ T\mu = \mu \circ \mu_T$）** | 以葉節點替換展開實現 Monad 乘法 $\mu = \mathrm{join}$，滿足範疇論 Monad 三大定律與自然性。 |
| `distribute` / `verify_beck_laws` | **Beck 分配律定理（Beck's Distributive Law $\lambda : T \circ L \Rightarrow L \circ T$）** | 實現樹 Monad $T$ 與列表 Monad $L$ 之間的分配變換，並驗證四條 Beck 相容公理，使複合函子 $L \circ T$ 自動繼承 Monad 結構。 |

### 4. `voa.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `WeylPoly` / `weyl_mul` | **海森堡—Weyl 代數對易關係 $[a_m, a_n] = m \cdot \delta_{m+n, 0} \cdot K$ 與 Poincaré–Birkhoff–Witt（PBW）正規序演算法** | 將玻色子模算子多項式透過氣泡交換與對易項收縮，化為創生算子 $a_{-m}$ ($m>0$) 在左、湮滅算子 $a_n$ ($n \ge 0$) 在右的唯一 PBW 正規序（Normal Ordering $:AB:$），滿足結合律。 |
| `fock_action` / `borcherds_commutator` | **真空 Fock 模作用與 Borcherds 留數局部對易公式** | 驗證湮滅算子作用於真空 $|0\rangle$ 為零，以及頂點算子場 $a(z) = \sum_n a_n z^{-n-1}$ 的二階極點中心荷留數公式。 |

### 5. `algebra_wbtest.mbt`, `monad_wbtest.mbt` & `voa_wbtest.mbt`
- **白盒測試**：驗證 Stasheff $n=1,2,3,4$ 恆等式、Steenrod $\smile_i$ 餘邊界律、Monad 與 Beck 分配律、以及海森堡代數 PBW 正規序結合律。
