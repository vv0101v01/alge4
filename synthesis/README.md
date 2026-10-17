# `synthesis/` — QCKS 合成新演算法：位並行閉包量化格與廣義偏序景 Kan–Sheaf 單價搬運引擎（Quantale-Closure & Kan–Sheaf Univalence Engine）

本資料夾是從**抽象代數（Abstract Algebra）**與**格論／無點拓撲／預層 Topos 理論（Lattice Theory, Quantale Theory & Presheaf Topos Theory）**視角，提煉 `algo` 與 `alge3` 兩大演算法群組的強共通因子所合成出的**全新四階段統一演算法（QCKS）**。

---

## 檔案清單與所含定理／演算法／公理

### 1. `quantale_lattice.mbt`（階段 I & 階段 II）
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `bit_closure` | **位並行算子最小不動點閉包定理（Tarski Fixed-Point Theorem on Bitsets）** | 在 `@core.Bits` 上同時對零元 `zero_idx`、算子族 `act_tables` 與加法表 `add_table` 求最小閉集 $\mathrm{cl}(S)$。 |
| `ClosureQuantale::synthesize` | **交換殘差量化格（Commutative Residuated Quantale）與伽羅瓦伴隨合成演算法** | 將生成元對有限交集閉包形成乘法基，以 BFS 枚舉全體不動點 $\mathcal{L} = \mathrm{Fix}(\mathrm{cl})$，建立位元偏序矩陣 `le_mat`（`@core.BoolMat`）、格交 `meet_table`、格並 `join_table`、量化積 `prod_table`，並由單一伽羅瓦伴隨公式 $(c_i : c_j) = \bigvee \{c_k \in \mathcal{L} \mid c_k \cdot c_j \preceq c_i\}$ 預計算右殘差表 `resid_table`。 |
| `from_finalg`, `from_finmodule`, `from_zariski_spec`, `from_cubical_cofs` | **四合一閉包格領域統一構造定理** | 將有限環理想格 $\mathrm{Idl}(R)$、有限模子模格 $\mathrm{Sub}_R(M)$、仿射概形 Zariski 開集 Frame $\mathcal{O}(\mathrm{Spec}\,R)$ 與立方體餘纖維外延 Frame 全部收斂為 `ClosureQuantale`。 |
| `residual`, `conductor`, `annihilator_of`, `socle_id` | **殘差統一導體、零化子、底座與 Heyting 蘊涵定理** | 在同一個 `resid_table` 中同時給出理想商 $(I:J)$、零化子 $\mathrm{Ann}(J) = (\bot : J)$、底座 $\mathrm{Soc}(R) = \bigvee \mathrm{Atoms}(\mathcal{L}) = (\bot : J(R))$ 與拓撲／餘纖維的 Heyting 蘊涵 $(B \Rightarrow A)$。 |
| `quantale_primes`, `minimal_primes`, `radical_of`, `nilradical_id`, `jacobson_id` | **量化質元與根核（Radical Nucleus）分解定理** | 以量化質公理 $x \cdot y \preceq p \implies x \preceq p \lor y \preceq p$ 與根核 $\mathrm{rad}(a) = \bigvee \{x \mid x^k \preceq a\}$ 統一質理想、不可約分支、冪零根與 Jacobson 根。 |
| `is_complemented_lattice`, `boolean_center_atoms`, `krull_dimension` | **有補格半單性定理與布林中心原子（Wedderburn–Artin 塊分解）** | 以格有補性同時判定環與模的半單性，並由具有唯一補元的冪等元極小非零元直接抽出 Wedderburn 單塊。 |
| `order_complex`, `order_homology_betti` | **【跨庫湧現定理】Folkman–Quillen 代數格階複形同調定理 $H_*(\Delta(\overline{\mathcal{L}}); \mathbb{F}_2)$** | 將閉包格真部 $\overline{\mathcal{L}} = \mathcal{L} \setminus \{\bot, \top\}$ 的嚴格全序鏈轉為 `@homotopy.SimplicialComplex`，直接算出布林理想格的球面同調（$\overline{B_3} \simeq S^1 \Rightarrow \beta=[1,1]$，$\overline{B_4} \simeq S^2 \Rightarrow \beta=[1,0,1]$）與局部環理想格的星形錐可縮同調（$\beta=[1,0]$）。 |

### 2. `kan_sheaf.mbt`（階段 III & 階段 IV）
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `PosetSite` (`from_quantale`, `from_cube`, `from_chain`) | **有界交半格景（Meet-Semilattice Poset Site）統一公理** | 將閉包量化格、立方體面偏序集 $\{0,1,*\}^n$ 與全序鏈統一表示為帶交運算的偏序景。 |
| `PosetPresheaf` (`from_cubety`, `from_zariski_cover`, `from_inv_system`) | **偏序景有限集合預層反變函子公理** | 統一立方體預層、仿射概形二元開覆蓋結構層與連續模逆系統，並提供結合律驗證 `validate()`。 |
| `PosetPresheaf::kan_sheaf_solve` | **三合一 Kan–Sheaf 相容擴延求解定理** | 對局部相容截面族 `sys = {(s_k, v_k)}`（滿足交集相容 `check_coherent`），搜尋頂層截面 `all_fillers` 並投影至目標階段 `lid_stage`：<br>1. 在立方體景上完全重現 `alge3/cubical::comp` 與單價 `transport`；<br>2. 在 Zariski 覆蓋景上由 `verify_binary_sheaf_gluing`（`filler_count == 1`）完全重現 `algo/scheme::sheaf_gluing_bijective`；<br>3. 在全序鏈景上由 `extract_limit_threads` 完全重現 `algo/modules::InvSystem::limit_threads`。 |
| `glue_presheaf`, `algebraic_univalence_transport_op`, `algebraic_univalence_from_hott_equiv` | **廣義偏序景 `Glue` 構造器與結構同一性原理（SIP：代數結構單價搬運定理）** | 將 `glue_ty` 推廣至任意偏序景，並把 `@hott.Equiv`（如 CRT 環同構 $\mathbb{Z}/6\mathbb{Z} \simeq \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/3\mathbb{Z}$）升格為單價路徑預層 $\mathrm{ua}(e)$，透過雙向 `kan_sheaf_solve` 自動將源代數的二元運算表沿單價路徑 Kan 共軛搬運至同構目標，嚴格滿足環同構律 $\mathrm{op}_B(e(x), e(y)) = e(\mathrm{op}_A(x, y))$。 |

### 3. `synthesis_wbtest.mbt`
- **白盒與屬性測試**：對全部四階段演算法、Folkman–Quillen 球面／局部環錐同調定理、三合一 Kan–Sheaf 求解器、CRT 乘法表單價搬運與伽羅瓦伴隨律進行完整驗證。
