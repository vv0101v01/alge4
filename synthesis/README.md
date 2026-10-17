# `synthesis/` — QCKS-H 七階段合成大一統演算法（跨 `alge`、`alge1`、`alge2`、`alge3`、`algo` 五庫合成）

本資料夾從**代數幾何（Algebraic Geometry）**、**範疇論（Category Theory）**、**同倫代數（Homotopical Algebra）**與**格論／無點拓撲（Lattice & Quantale Theory）**四大視角，提煉五個專案（`alge`、`alge1`、`alge2`、`alge3`、`algo`）中具備 **3 個以上共通因子／強大態雙射（Morphism-Bijection / Hom-Bijection）共通因子／特性共通** 的演算法群組，合成為**單一七階段統一演算法管線（QCKS-H Engine）**。

---

## 五大共通因子群（每個均橫跨 $\ge 3$ 至 $5$ 個專案）

| 共通因子群 | 維度視角 | 橫跨的來源專案與模組 | 核心態雙射（Hom-Bijection）／共通代數特性 |
| :--- | :--- | :--- | :--- |
| **共通因子群 A**<br>（階段 I & II） | 格論 $+$ 代數幾何 $+$ Topos | `algo/finite`, `algo/modules`, `algo/scheme`, `alge/quot`, `alge1/topos`, `alge2/vect_top_topos`, `alge3/core`, `alge3/homotopy`, `alge3/cubical` | **交換殘差量化格伽羅瓦伴隨雙射**：<br>$\mathrm{Hom}_{\mathcal{L}}(C \cdot B, A) \cong \mathrm{Hom}_{\mathcal{L}}(C, (A : B))$<br>統一導體 $(I:J)$、零化子 $\mathrm{Ann}(J)$、底座 $\mathrm{Soc}(R)$、Topos Heyting 蘊涵、Lawvere–Tierney 雙重否定模態 $\bigcirc_{\neg\neg}$、餘切嵌入維數 $\mathrm{edim} = \dim_k(\mathfrak{m}/\mathfrak{m}^2)$、Alexandrov Beat 同倫核收縮與 Folkman–Quillen 階複形同調。 |
| **共通因子群 B**<br>（階段 III & IV） | 範疇論 $+$ 代數幾何 $+$ 同倫類型論 | `algo/scheme`, `algo/modules`, `algo/hott`, `alge1/topos`, `alge1/hott_univalence`, `alge2/hott_foundations`, `alge3/cubical` | **有界交半格景預層極限與單價 Glue 雙射**：<br>$\mathrm{Hom}_{\mathsf{PSh}}(1, F) \cong \varprojlim_{u \in \mathcal{P}} F(u)$<br>以單一算子 `kan_sheaf_solve` 統一立方體 Kan 填補 `comp`、Zariski 結構層二元覆蓋唯一黏合、連續模逆極限線程與代數結構單價搬運（SIP）。 |
| **共通因子群 C**<br>（階段 V） | 代數幾何 | `alge/quot`, `alge/ga`, `alge/val`, `algo/finite`, `algo/geometry` | **Hilbert 點求值態雙射與冪零 Newton 倍增提升**：<br>$\mathrm{Hom}_{\mathbb{F}_p\text{-Alg}}(\mathbb{F}_p[x]/I, \mathbb{F}_p) \xrightarrow{\sim} V_{\mathbb{F}_p}(I)$<br>將截斷賦值環 $\mathbb{F}_p[[t]]/(t^d)$ 與零維座標環統一為扁平張量代數 `ZeroCostTensorAlg`，以同一個二次收斂算子 $b_{k+1} = b_k(2 - ab_k)$ 在 $\lceil \log_2 d \rceil$ 步內求逆與平方根，並由求值矩陣逆直接對偶出拉格朗日正交本原冪等元基。 |
| **共通因子群 D**<br>（階段 VI） | 範疇論 | `algo/hott`, `algo/linalg`, `algo/modules`, `alge/ga`, `alge1/functor`, `alge1/linear`, `alge2/functors`, `alge2/vect_top_topos`, `alge2/linear_logic`, `alge3/homotopy` | **三大範疇伴隨態雙射與單價骨架對角化**：<br>1. 自由—遺忘伴隨 $\mathrm{Hom}_{\mathsf{Mon}}(F(\Sigma), M) \cong \mathrm{Hom}_{\mathsf{Set}}(\Sigma, U(M))$ 與米田雙射 $\mathrm{Nat}(\mathrm{Hom}(X,-), G) \cong G(X)$（Coyoneda 零分配融合流 $+$ $\Phi(w^K) = \Phi(w)^K$）；<br>2. 單價骨架對角化 $F : (C, \star) \xrightarrow{\sim} (\mathrm{Sk}(D), \odot)$（統一 FWHT 捲積與座標環求值快速冪）；<br>3. 張量—Hom 柯里化雙射 $\mathrm{Hom}(U \otimes V, W) \cong \mathrm{Hom}(U, \mathrm{Hom}(V, W))$、Beck–Chevalley 拉回縮並與 *-自治 Chu 對偶證明網。 |
| **共通因子群 E**<br>（階段 VII） | 同倫代數 $+$ 導出代數幾何 $+$ 高維群胚 | `alge1/homotopy`, `alge1/groupoid`, `alge2/homotopy_dag`, `alge2/higher_groupoid`, `alge2/hott_foundations`, `alge3/core`, `alge3/algebra`, `alge3/derived`, `alge3/cubical`, `algo/hott` | **同倫收縮轉移、導出相交與高維群胚全純性**：<br>1. 位並行強形變收縮（`BitParallelSDR`）$+$ 同調微擾引理（HPL）$+$ Kadeishvili $A_\infty$ 轉移至 `@algebra.AInf`；<br>2. Koszul 導出相交 $\chi(\mathrm{Tor}_*^R(A,B))$、餘切複形虛擬維度 $\mathrm{vdim}(\mathbb{L}_{X/k})$ 與 Milnor/Tjurina 奇點形變 $(\mu, \tau)$ Saito 判準；<br>3. 非交換二面體 1-群胚路徑壓縮、2-群交叉模交換律、2D/3D 立方體 Kan 填補與 Licata–Shulman `encode`/`decode`。 |

---

## 檔案清單與所含定理／演算法／公理

### 1. `quantale_lattice.mbt`（階段 I & 階段 II）
- `bit_closure`、`ClosureQuantale::synthesize`、`from_finalg`、`from_finmodule`、`from_zariski_spec`、`from_cubical_cofs`；
- 格原子、餘原子、量化質元、根核 `radical_of`、導體 `conductor`、零化子 `annihilator_of`、底座 `socle_id`、有補格半單性、布林中心原子 `boolean_center_atoms`、Krull 維數；
- Topos 內部邏輯 `heyting_implication`、`heyting_negation`、`lawvere_tierney_dense`（$\bigcirc_{\neg\neg}$）、`kripke_joyal_forces`；
- 局部環餘切嵌入維數 `embedding_dimension`（$\dim_k \mathfrak{m}/\mathfrak{m}^2$）與正則局部環判準 `is_regular_local`；
- Stong–Quillen 位並行可縮纖維收縮 `alexandrov_homotopy_core_mask`、Rota–Leinster 莫比烏斯歐拉示性數 `mobius_euler_characteristic` 與 Folkman–Quillen 階複形同調 `order_complex` / `order_homology_betti`。

### 2. `kan_sheaf.mbt`（階段 III & 階段 IV）
- `PosetSite`（`from_quantale`、`from_cube`、`from_chain`）與 `PosetPresheaf`（`from_cubety`、`from_zariski_cover`、`from_inv_system`）；
- 三合一求解器 `PosetPresheaf::kan_sheaf_solve`、`verify_binary_sheaf_gluing`、`extract_limit_threads`；
- 廣義偏序景黏合 `glue_presheaf` 與代數結構單價搬運 `algebraic_univalence_transport_op` / `algebraic_univalence_from_hott_equiv`。

### 3. `newton_hensel_tensor.mbt`（階段 V — 代數幾何）
- `ZeroCostTensorAlg`（`from_finalg`、`from_truncated_dvr`）與張量環公理全稱檢驗 `verify_tensor_ring_axioms`；
- `t`-進賦值 `t_adic_valuation`、統一冪零／`t`-進 Newton 精度倍增求逆 `newton_inv` 與平方根 `newton_sqrt`；
- 代數特徵標枚舉 `algebra_characters`、點求值態雙射驗證 `verify_character_point_hom_bijection`（$\mathrm{Hom}_{k\text{-Alg}}(A, k) \cong V_k(I)$）與拉格朗日正交本原冪等元基合成 `lagrange_primitive_idempotents`。

### 4. `categorical_adjunction.mbt`（階段 VI — 範疇論）
- 餘米田路徑纖維融合流 `CoyonedaStream`（`lift`、`map`、`lower`、`fold_hom`）與自由—遺忘伴隨泛同態倍增 `free_monoid_affine_hom_power`；
- 單價座標環骨架快速冪 `tensor_alg_univalent_skeleton_power` 與 Walsh–Hadamard 單價骨架 XOR 捲積鏈 `fwht_univalent_convolution_chain`；
- 張量—Hom 柯里化逐軸 Kronecker 作用 `kronecker_curried_apply_matrices`、Beck–Chevalley 跨距拉回縮並 `beck_chevalley_span_contraction` 與 *-自治 Chu / Danos–Regnier 乘性線性邏輯證明網樹性判準 `verify_chu_mll_proof_net`。

### 5. `homotopy_derived_groupoid.mbt`（階段 VII — 同倫代數、導出幾何與高維群胚）
- `BitParallelSDR`（`verify_axioms`）、位並行同調微擾引理轉移 `perturb_via_hpl` 與 Kadeishvili 極小模型 $A_\infty$ 轉移 `kadeishvili_transfer_to_ainf`（直接輸出 `@algebra.AInf` 並通過 Stasheff 恆等式檢驗）；
- 綜合導出奇點剖析器 `analyze_derived_singularity`（結合 Milnor $\mu$、Tjurina $\tau$、Saito 判準、餘切複形虛擬維度與 Serre 導出相交歐拉示性數 $\chi(\mathrm{Tor}_*^R(A,B))$）；
- 非交換二面體規範群 `DihedralGauge`、帶權路徑壓縮基本群胚 `PathCompressedGroupoid`、2-群交叉模 `CrossedModule2Cell` 交換律檢驗 `verify_2group_exchange_law`、2D/3D 立方體 Kan 盒子填補 `cubical_hcomp_2d_gauge` / `verify_cubical_kan_fill_3d_gauge` 與 Licata–Shulman 迴路編碼 `hit_bg_encode_word`。

### 6. `synthesis_wbtest.mbt`
- 涵蓋全部七個階段的白盒斷言測試與伽羅瓦伴隨律 QuickCheck 屬性測試。
