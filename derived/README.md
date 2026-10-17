# `derived/` — 奇點形變理論（Milnor / Tjurina 代數）與箭圖表示導出範疇 $\mathrm{Ext}^*$ 模組（Singularity Deformation & Quiver Derived Categories）

本資料夾實現兩個核心導出代數幾何演算法：加權齊次超曲面奇點的局部形變不變量（Milnor 數 $\mu$ 與 Tjurina 數 $\tau$，涵蓋 ADE 單純奇點分類）以及無圈箭圖（Acronyms-free Quiver）路徑代數表示的標準投射分解與 Euler–Ringel 同調雙線性形式。

---

## 檔案清單與所含定理／演算法／公理

### 1. `deform.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `PolyTerm` / `partial_deriv` | **形式偏導數與 Jacobi 理想 $J(f) = \langle \partial f / \partial x_1, \dots, \partial f / \partial x_n \rangle$** | 計算多元多項式在 $\mathbb{F}_p$ 上的偏導數生成元。 |
| `milnor_number` / `tjurina_number` | **奇點 Milnor 代數 $\mathcal{M}_f = k[x]/J(f)$ 與 Tjurina 一階形變代數 $\mathcal{T}_f = k[x]/\langle f, J(f) \rangle$ 維數演算法** | 在分次截斷單項式空間中構造理想倍式矩陣，以 $\mathbb{F}_p$ 高斯消去計算餘維數 $\mu(f) = \dim_k k[x]/J(f)$（消失球面個數）與 $\tau(f) = \dim_k \mathrm{Def}^1(f)$（通用展開基底維數）。 |
| `ade_polynomial` | **Arnold ADE 單純曲面奇點定理（$\mu = \tau$ for Quasi-Homogeneous Singularities）** | 根據 Saito 定理，多項式 $f$ 為加權齊次（Quasi-homogeneous）$\iff f \in J(f) \iff \mu(f) = \tau(f)$；完整內建 $A_n$ ($x^{n+1}+y^2$)、$D_n$ ($x^{n-1}+xy^2$) 與 $E_6, E_7, E_8$ 奇點並驗證 $\mu = \tau = n$。 |

### 2. `quiver.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `Quiver` / `QuiverRep` | **箭圖路徑代數 $kQ$ 與其模範疇 $\mathrm{Rep}_k(Q) \simeq kQ\text{-Mod}$ 等價** | 以頂點向量空間維數向量 $\underline{\dim} M = (d_i)$ 與箭頭矩陣表示有限維箭圖表示。 |
| `hom_dim(m, n)` / `ext1_dim(m, n)` | **標準雙項投射分解與遺傳代數定理（Hereditary Algebra Standard Resolution）** | 定理：無圈箭圖路徑代數 $kQ$ 為遺傳代數（$\mathrm{gl.dim}\,kQ \le 1$，故 $\mathrm{Ext}^k = 0$ 對所有 $k \ge 2$）；透過單一線性映射 $d_{M,N} : \bigoplus_{i \in Q_0} \mathrm{Hom}_k(M_i, N_i) \to \bigoplus_{\alpha : i \to j} \mathrm{Hom}_k(M_i, N_j)$，$\varphi \mapsto (\varphi_j \circ M_\alpha - N_\alpha \circ \varphi_i)$，同時算出 $\dim \mathrm{Hom}_{kQ}(M, N) = \dim \ker(d_{M,N})$ 與一階擴張群 $\dim \mathrm{Ext}^1_{kQ}(M, N) = \dim \mathrm{coker}(d_{M,N})$。 |
| `euler_ringel_form(m, n)` | **Euler–Ringel 同調雙線性形式定理 $\langle \underline{\dim} M, \underline{\dim} N \rangle = \dim \mathrm{Hom}(M, N) - \dim \mathrm{Ext}^1(M, N)$** | 驗證同調交錯和僅依賴維數向量：$\sum_{i \in Q_0} d_i(M) d_i(N) - \sum_{\alpha : i \to j} d_i(M) d_j(N) = \dim \mathrm{Hom}(M,N) - \dim \mathrm{Ext}^1(M,N)$，以及 Gabriel 定理中的剛性不可分解根表示（$\mathrm{Hom}(M,M)=1, \mathrm{Ext}^1(M,M)=0 \implies q(\underline{\dim} M)=1$）。 |

### 3. `deform_wbtest.mbt` & `quiver_wbtest.mbt`
- **白盒測試**：驗證 $A_1 \dots A_5, D_4, D_5, E_6, E_7, E_8$ 奇點的 $\mu = \tau$ 定理、非加權齊次奇點的 $\tau < \mu$ 現象，以及 Dynkin 箭圖上的 Euler–Ringel 公式與 Auslander–Reiten 不可分解根表示。
