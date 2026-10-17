# `cubical/` — CCHM 立方體類型論、Kan 填補算子與演算法化單價公理模組（Cubical Type Theory & Algorithmic Univalence）

本資料夾以有限集合立方體預層模型（Presheaves on the De Morgan Cube Category $\square$）完整實現 Cohen–Coquand–Huber–Mörtberg (CCHM) 立方體類型論的核心計算機制：在這個模型中，**Voevodsky 單價公理（Univalence Axiom）不再是阻塞正規化的外部公理，而是由 `Glue` 型別與 `comp` Kan 盒子填補算子組成的可執行演算法**。

---

## 檔案清單與所含定理／演算法／公理

### 1. `interval.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `IExpr` / `eval_iexpr` | **自由 De Morgan 代數區間 $\mathbb{I}$ 公理** | 實現區間端點 $0, 1$、方向變數 $i_k$、交 $r \wedge s$（連接 Connection）、並 $r \vee s$ 與對合反轉 $1 - r$（滿足 De Morgan 律 $1 - (r \wedge s) = (1-r) \vee (1-s)$，但不滿足排中律 $i \wedge (1-i) \ne 0$）。 |
| `CubeMap` / `Cof` / `extent` | **立方體範疇態射 $\square(m, n)$ 與餘纖維（Cofibration）分配格分類定理** | 藉由將區間項求值於全體二元賦值點 $\{0, 1\}^m$，把餘纖維公式 $\varphi$（面 $(i=0), (i=1)$、對角線 $(i=j)$ 及其交並）正規化為 64-bit 外延位元集 `Bits`，判定兩個餘纖維邏輯等價當且僅當其外延位元集相同。 |

### 2. `cubety.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `CubeTy` / `validate` | **三進制子立方體面分解與立方體集合預層公理** | 將 $n$ 維立方體的 $3^n$ 個子立方體面編碼為三進制索引 $\{0, 1, *\}^n$，在每個面上配置有限纖維 `card[s]` 與限制映射 `res[big -> face]`，並驗證反變函子結合律。 |
| `PathP` / `lam_path` / `app_path` / `refl_path` | **依賴路徑型別 $\mathrm{PathP}(i.\,A, a_0, a_1)$ 作為區間函數抽象定理** | 將恆等型別實現為 $1$ 維立方體截面，其端點限制直接由面映射給出，天然具備函數外延性（`funext` 為逐座標路徑抽象）。 |

### 3. `comp.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `PartialElem` / `check_partial` | **餘纖維管壁局部截面相容性判準** | 檢驗局部給定的各面截面在所有兩兩交集子立方體面上限制是否一致。 |
| `comp` / `hcomp` / `transp_line` | **Kan 開放盒子填補算子（Kan Composition & Transport Operational Semantics）** | 給定管壁局部截面 `tube` 與底蓋 $(i=\text{src})$ 上的 `cap`，搜尋頂部立方體截面 $x \in A(*^n)$ 使其同時延伸 `tube` 與 `cap`，並投影至頂蓋 $(i=1-\text{src})$ 輸出 `(lid, filler)`；由此衍生路徑連接方塊 `connection_and`、`connection_or`、路徑逆 `path_symm` 與路徑合成 `path_concat`。 |

### 4. `univalence.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `Iso` / `glue_ty` | **CCHM 宇宙黏合型別構造器 $\mathrm{Glue}[\varphi \mapsto (T, e)]\,B$** | 對任意餘纖維外延 $\varphi$，在 $\varphi$ 成立的面上將纖維替換為 $T$，而當限制映射從 $\neg\varphi$ 的大立方體跨越至 $\varphi$ 的邊界面時，以等價逆映射扭轉 $\mathrm{res}^{\mathrm{Glue}}_{\text{big}\to\text{face}} = e_{\text{face}}^{-1} \circ \mathrm{res}^B_{\text{big}\to\text{face}}$，且嚴格保持預層結合律！ |
| `ua(e)` / `ua_beta` | **Voevodsky 單價公理演算法化定理 $\mathrm{transport}(\mathrm{ua}(e), a) \equiv e(a)$** | 在區間 $i \in \mathbb{I}$ 的端點餘纖維 $\varphi = (i=0) \vee (i=1)$ 上構造 $\mathrm{ua}(e) = \mathrm{Glue}[(i=0) \mapsto (A, e),\; (i=1) \mapsto (B, \mathrm{id}_B)]\,B$；定理：對 $\mathrm{ua}(e)$ 執行 Kan 搬運 `transp_line` 時，唯一合法填補為 $e(a) \in B$，故頂蓋輸出精確等於 $e(a)$（計算性單價 $\beta$-歸約）！ |

### 5. `interval_wbtest.mbt`, `comp_wbtest.mbt` & `univalence_wbtest.mbt`
- **白盒測試**：驗證 De Morgan 代數定律、Kan 盒子填補與路徑群胚律、對稱群 $S_4$ 全部 $24$ 個排列等價的單價計算律 $\mathrm{ua}_\beta$ 以及函子性 $\mathrm{ua}(e_2 \circ e_1) \sim \mathrm{ua}(e_1) \cdot \mathrm{ua}(e_2)$。
