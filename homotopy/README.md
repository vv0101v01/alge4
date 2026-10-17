# `homotopy/` — 單純複形、分類空間神經（Nerve）與群／么半群 Bar 同調模組（Simplicial Homotopy, Classifying Spaces & Bar Homology）

本資料夾建立單純同倫與代數拓撲計算層，將抽象單純複形、有限么半群／群的分類空間神經 $B M = N_\bullet(M)$ 以及幾何對偶跨越（Span / Correspondence）轉化為 `core/` 的位並行鏈複形並計算其同調群。

---

## 檔案清單與所含定理／演算法／公理

### 1. `simplicial.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `SimplicialComplex` / `from_facets` | **抽象單純複形向下閉包公理（Downward Closure of Faces）** | 由最高維生成單純形（Facets）自動枚舉所有維度的子單純形並按字典序正規化，保證對任意 $\sigma \in K$ 及 $\tau \subseteq \sigma$ 必有 $\tau \in K$。 |
| `boundary_matrix(self, d)` / `to_chain_complex` | **單純邊界算子與單純恆等式 $\partial_{d-1} \circ \partial_d = 0$** | 定義 $\partial_d [v_0, \dots, v_d] = \sum_{i=0}^d (-1)^i [v_0, \dots, \hat{v}_i, \dots, v_d] \pmod 2$，因每個餘維 2 的面恰由兩種刪除順序消除，故在 $\mathbb{F}_2$ 上嚴格滿足 $\partial^2 = 0$。 |
| `betti(self)` / `euler(self)` | **單純同調群 $H_*(K; \mathbb{F}_2)$ 與 Euler–Poincaré 定理** | 直接給出球面 $S^n$、環面 $T^2$、實射影平面 $\mathbb{R}P^2$、Klein 瓶等空間的 $\mathbb{F}_2$-Betti 數與歐拉示性數。 |

### 2. `nerve.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `Monoid` (`cyclic_group`, `klein_four`) | **有限么半群與群公理（Associativity & Identity）** | 以乘法表表示有限么半群 $(M, \cdot, e)$，並提供全稱結合律與單位元檢驗 `is_valid`。 |
| `bar_boundary(self, deg)` / `bar_betti` | **Eilenberg–MacLane 分類空間神經 $BM$ 與正規化 Bar 複形同調 $H_*(BM; \mathbb{F}_2)$** | 以非單位元組成的 $k$-元組 $(g_1 \mid \dots \mid g_k) \in (M \setminus \{e\})^k$ 為正規化 $k$-單純形，實現 Hochschild/Bar 邊界算子 $d_0 + \sum_{i=1}^{k-1} d_i + d_k$（其中 $d_i$ 將相鄰元相乘 $g_i g_{i+1}$，若積為單位元 $e$ 則退化消去）；計算群上同調／同調 $H_k(G; \mathbb{F}_2)$（如 $B\mathbb{Z}/2\mathbb{Z} \simeq \mathbb{R}P^\infty$ 各階 Betti 數恆為 $1$）。 |

### 3. `correspondence.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `Span` / `compose` / `pullback_Transform` | **範疇跨距（Span / Correspondence）纖維積合成與推拉變換（Pull-Push / Fourier–Mukai Transform on $\mathbb{F}_2$）** | 對跨距 $X \xleftarrow{p} Z \xrightarrow{q} Y$，以纖維積 $Z_1 \times_Y Z_2$ 實現跨距合成，並定義函數空間上的拉回—推前積分算子 $q_* \circ p^* : \mathbb{F}_2^X \to \mathbb{F}_2^Y$，驗證函子性 $(S_2 \circ S_1)_* = (S_2)_* \circ (S_1)_*$。 |

### 4. `simplicial_wbtest.mbt` & `homotopy_wbtest.mbt`
- **白盒測試**：計算 $S^1, S^2, T^2, \mathbb{R}P^2$ 的單純同調、驗證 $\mathbb{Z}/2\mathbb{Z}$ 與 Klein 四元群 $V_4$ 的分類空間 Bar 同調 $\beta_k(B\mathbb{Z}/2\mathbb{Z}) = 1$、以及跨距推拉函子性。
