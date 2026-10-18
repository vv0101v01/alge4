# `alge4` (`moon-unified`) — 抽象代數、代數幾何、範疇論、位並行同調代數、立方體單價與 QCKS-H 七階段合成大一統庫

本倉庫（`moon-unified`）整合了 **`algo`（`moon-algebra`）** 與 **`alge3`（`arena/moonmath` 3.1）** 的全部模組、連接兩者的跨庫橋接層 **`bridge/`**，以及橫跨 **`alge`、`alge1`、`alge2`、`alge3`、`algo` 五大專案**從**代數幾何、範疇論、同倫代數與格論**提煉出的七階段大一統合成演算法 **`synthesis/`（QCKS-H Engine）**。

倉庫內的**根目錄與全部 20 個子資料夾**均附有獨立的 `README.md`，詳細列出每個檔案中包含的**數學定理、演算法與公理**。

---

## 一、根目錄檔案（`@poly` 套件）之定理、演算法與公理

根目錄實現多變數多項式環 $\mathbb{F}_p[x_1, \dots, x_n]$、單項式序、Buchberger Gröbner 基演算法、多項式理想成員判定與商環算術：

| 根目錄檔案 | 所含定理／演算法／公理 | 說明 |
| :--- | :--- | :--- |
| **`ring.mbt`** | **交換環 $\mathbb{Z}/n\mathbb{Z}$ 單位群、零因子、冪等元與中國剩餘定理分解 `zn_crt_components`** | 實現有限模環 $\mathbb{Z}/n\mathbb{Z}$ 的算術基本定理質冪分解 $n = \prod p_i^{k_i}$、正交冪等元分解、單位群 $(\mathbb{Z}/n\mathbb{Z})^\times$ 與零因子判定。 |
| **`poly.mbt`** | **多變數稀疏多項式環 $\mathbb{F}_p[x_1, \dots, x_n]$ 公理與 Dickson 單項式良序公理（Lex / GrLex / GRevLex）** | 以按單項式序（字典序 `Lex`、分次字典序 `GrLex`、分次反字典序 `GRevLex`）嚴格遞減排列的稀疏項陣列表示多項式，實現多項式加法、乘法、領導項 $\mathrm{LT}(f)$、領導係數 $\mathrm{LC}(f)$、領導單項式 $\mathrm{LM}(f)$ 與求值同態。 |
| **`groebner.mbt`** | **多變數帶餘除法、`s_polynomial` 與 Buchberger 約化 Gröbner 基演算法（Reduced Gröbner Basis & Buchberger's Criterion）** | 構造 S-多項式 $S(f, g) = \frac{\mathrm{lcm}(\mathrm{LM}(f), \mathrm{LM}(g))}{\mathrm{LT}(f)} f - \frac{\mathrm{lcm}(\mathrm{LM}(f), \mathrm{LM}(g))}{\mathrm{LT}(g)} g$；依據 **Buchberger 定理**（$G$ 為 Gröbner 基 $\iff \forall f, g \in G,\, \overline{S(f, g)}^G = 0$）迭代消去所有 S-多項式餘式，並經首一化與互約化輸出**唯一約化 Gröbner 基**。 |
| **`ideal.mbt`** | **多項式理想成員問題判定演算法（Ideal Membership $f \in I \iff \overline{f}^G = 0$）、消去理想與商環正規形算術** | 利用約化 Gröbner 基判定理想相等 $I = J$（當且僅當兩者約化 Gröbner 基完全一致）、計算理想和 $I + J$、理想積 $I \cdot J$、消去理想 $I \cap \mathbb{F}_p[x_{k+1},\dots,x_n]$ 以及零維商環的正規形加法與乘法。 |
| **`moon-algebra.mbt`** | **頂層統一導出介面** | 匯總根套件公開的多項式與 Gröbner 基高階入口。 |
| **`algebra_tests_wbtest.mbt`** | **根套件白盒與 QuickCheck 屬性測試** | 驗證多項式環公理、Buchberger 準則、約化 Gröbner 基唯一性與理想成員定理。 |

---

## 二、全倉庫 20 個子資料夾導覽（每個資料夾均附有詳細 `README.md`）

| 子資料夾 | 來源／定位 | 核心內容與重點定理／演算法／公理摘要 |
| :--- | :--- | :--- |
| **[`num/`](./num/README.md)** | `algo` | 歐幾里得輾轉相除法、擴展歐幾里得與裴蜀恆等式、模逆元、二進制快速冪、費馬小定理、歐拉 $\varphi$ 函數與中國剩餘定理。 |
| **[`linalg/`](./linalg/README.md)** | `algo` | $\mathbb{F}_p$ 高斯—約當 RREF 消去、秩—零化度定理、Rouché–Capelli 線性求解、Zassenhaus 對偶子空間交、算子不變子空間閉包與 Kronecker 張量積。 |
| **[`finite/`](./finite/README.md)** | `algo` | 零維商代數 `FinAlg`（Macaulay 標準單項式基底）、阿廷環理想格 BFS 枚舉、質理想＝極大理想定理、冪零根＝Jacobson 根、導體 $(I:J)$、零化子、Socle、乘性局部化 $S^{-1}R$ 與 Wedderburn–Artin 本原冪等元分解。 |
| **[`modules/`](./modules/README.md)** | `algo` | 有限 $R$-模與子模模格、模同態第一同構定理、正合序列判準、Maschke 半單有補子模定理、Kaplansky 局部環投射模自由定理、Matlis 線性對偶與 Gorenstein 自內射環判準、擬凝聚層 $\widetilde{M}$ 與逆極限 $\varprojlim M_t$。 |
| **[`geometry/`](./geometry/README.md)** | `algo` | 有限域仿射空間 $\mathbb{A}^n(\mathbb{F}_p)$、零點簇 $V(I)$ 與消失理想 $I(S)$ 的反變伽羅瓦伴隨、Zariski 閉包與有限域 Hilbert 零點定理座標環維數。 |
| **[`scheme/`](./scheme/README.md)** | `algo` | Grothendieck 仿射概形 $\mathrm{Spec}(R)$、主開集乘法基 $D(f) \cap D(g) = D(fg)$、不可約分支＝極小質理想、局部環莖 $\mathcal{O}_{X,\mathfrak{p}} = R_{\mathfrak{p}}$、預層限制同態與結構層二元開覆蓋唯一黏合公理 `sheaf_gluing_bijective`。 |
| **[`hott/`](./hott/README.md)** | `algo` | 同倫類型論擬逆等價 `Equiv` 與半伴隨等價、高階歸納型別圓 $\pi_1(S^1) \simeq \mathbb{Z}$ 繞數編解碼、集合商消去原則、自由—遺忘伴隨函子 $F \dashv U$、CRT 環等價與 Newman 引理重寫匯合性。 |
| **[`core/`](./core/README.md)** | `alge3` | 多字組 64-bit 位並行集合 `Bits`、位並行 $\mathbb{F}_2$ 矩陣 `BoolMat` 高斯消去與核空間、$\mathbb{F}_p$ 行列式 `fp_det`、鏈複形同調 Betti 數、Euler–Poincaré 定理與持久同調（Persistent Homology）歸約演算法。 |
| **[`homotopy/`](./homotopy/README.md)** | `alge3` | 抽象單純複形向下閉包與單純同調 $H_*(K; \mathbb{F}_2)$、有限么半群／群分類空間神經 $BM$ 的正規化 Bar 同調 $H_*(BM; \mathbb{F}_2)$、範疇跨距（Span）纖維積合成與拉回—推前變換。 |
| **[`algebra/`](./algebra/README.md)** | `alge3` | Stasheff $A_\infty$-代數高階結合恆等式與 Massey 三重積、Steenrod $\smile_i$ 高階杯積餘邊界定理與 Steenrod 平方 $Sq^k$、自由樹 Monad 與 Beck 分配律、海森堡頂點算子代數（VOA）PBW 正規序展開。 |
| **[`derived/`](./derived/README.md)** | `alge3` | 超曲面奇點 Milnor 代數 $\mu(f)$ 與 Tjurina 形變代數 $\tau(f)$、Saito 加權齊次奇點 $\mu = \tau$ 定理（Arnold ADE 分類）、無圈箭圖標準雙項投射分解求 $\mathrm{Hom}/\mathrm{Ext}^1$ 與 Euler–Ringel 同調雙線性形式。 |
| **[`cubical/`](./cubical/README.md)** | `alge3` | 自由 De Morgan 區間代數 $\mathbb{I}$、餘纖維外延分配格 `Cof::extent`、立方體預層 `CubeTy`、依賴路徑 `PathP`、Kan 開放盒子填補 `comp`、宇宙黏合 `Glue` 與 Voevodsky 單價公理演算法化定理 $\mathrm{transport}(\mathrm{ua}(e), a) = e(a)$。 |
| **[`bridge/`](./bridge/README.md)** | 跨庫橋接 | 連接 `algo` 與 `alge3` 的六大雙向橋樑：矩陣 $\leftrightarrow$ 位並行 `BoolMat`/行列式、`@hott.Equiv` $\leftrightarrow$ `@cubical.Iso`/`ua`（CRT 單價路徑）、Gröbner 商代數 $\leftrightarrow$ 奇點 Milnor/Tjurina 數、`FinAlg` 單位群 $\to$ Bar 同調、`FinAlg` $\to A_\infty$、Zariski 開集格 $\to$ `Bits`。 |
| **[`synthesis/`](./synthesis/README.md)** | **五庫七階段新合成演算法** | **QCKS-H 大一統演算法（橫跨 `alge` + `alge1` + `alge2` + `alge3` + `algo`）**：<br>• **階段 I & II（`quantale_lattice.mbt`）**：位並行閉包量化格 `ClosureQuantale`、伽羅瓦伴隨殘差、Topos Lawvere–Tierney 模態 $\bigcirc_{\neg\neg}$、餘切嵌入維數 $\mathrm{edim}$、Alexandrov Beat 同倫核、莫比烏斯反演與 Folkman–Quillen 階複形同調；<br>• **階段 III & IV（`kan_sheaf.mbt`）**：廣義偏序景 `kan_sheaf_solve` 三合一求解器與 `glue_presheaf` 代數結構單價搬運（SIP）；<br>• **階段 V（`newton_hensel_tensor.mbt`）**：零成本結構張量 `ZeroCostTensorAlg`、冪零／$t$-進 Newton 精度倍增求逆與平方根、以及代數幾何點求值態雙射 $\mathrm{Hom}_{k\text{-Alg}}(A, k) \cong V_k(I)$ 與拉格朗日正交冪等元；<br>• **階段 VI（`categorical_adjunction.mbt`）**：餘米田路徑纖維融合 `CoyonedaStream`、自由么半群泛同態倍增、單價骨架對角化（座標環骨架快速冪與 FWHT 捲積鏈）、張量—Hom 柯里化 Kronecker 作用、Beck–Chevalley 跨距縮並與 Chu / Danos–Regnier 證明網判準；<br>• **階段 VII（`homotopy_derived_groupoid.mbt`）**：位並行強形變收縮 `BitParallelSDR`、同調微擾引理 HPL、Kadeishvili $A_\infty$ 轉移至 `@algebra.AInf`、Koszul–Milnor–Tjurina 導出奇點剖析、以及非交換 1-群胚／2-群交叉模／2D & 3D 立方體 Kan 全純性與 Licata–Shulman 迴路編碼；<br>• **階段 VIII（`bijection_combinations.mbt`）**：五大核心態雙射 $\mathcal{B}_1,\dots,\mathcal{B}_5$ 之 **1對1 兩兩組合（$\binom{5}{2}=10$）**、**3個1組三元組合（$\binom{5}{3}=10$）**、**4個1組四元組合（$\binom{5}{4}=5$）** 與 **5個1組五元終極大一統演算法（$\binom{5}{5}=1$）**（共 26 個多階態雙射合成演算法）。 |
| **[`bench/`](./bench/README.md)** | `alge3` | 串聯全庫五大同調、代數、奇點與單價模組的可執行展示與基準測試程式。 |
| **[`docs/`](./docs/README.md)** | `alge3` | 兩篇完整數學原理與演算法論文（`paper.md`/`html` 與 `cubical.md`/`html`）。 |
| **[`port/`](./port/README.md)** | `algo` | 代數腳本與識別符自動遷移重寫管線。 |
| **[`prelude/`](./prelude/README.md)** | `algo` | Why3 自動定理證明器之 MoonBit 整數與陣列底層公理庫（`.mlw`）。 |
| **[`testutil/`](./testutil/README.md)** | `algo` | 交換環八大公理全稱檢驗器與標準測試代數構造器。 |
| **[`verify/`](./verify/README.md)** | `algo` | 附帶霍爾邏輯前置／後置條件與迴圈不變量的形式化驗證算術演算法。 |

---

## 三、建置與測試

```bash
moon check
moon test
moon test --target native
```

- **`moon check`**：0 Warnings, 0 Errors
- **`moon test`（Wasm & Native 雙後端）**：**158 / 158 測試全數通過**
