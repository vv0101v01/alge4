# `hott/` — 同倫類型論、高階歸納型別（HIT）、範疇伴隨與 Knuth–Bendix 重寫模組（Homotopy Type Theory, Adjunctions & Rewriting）

本資料夾以「定理即程序（Propositions as Types / Proofs as Programs）」為核心，實現同倫類型論中的擬逆等價（Quasi-inverse Equivalence）、半伴隨等價、高階歸納型別（圓 $S^1$ 基本群 $\pi_1(S^1) \cong \mathbb{Z}$ 與集合商）、有限範疇與伴隨函子（自由模 $\dashv$ 遺忘函子、中國剩餘定理等價）以及字串重寫匯合性檢查。

---

## 檔案清單與所含定理／演算法／公理

### 1. `hott.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `Equiv[A, B]` / `HalfAdj[A, B]` | **擬逆等價（qinv）與半伴隨等價（Half-Adjoint Equivalence）定義** | 以互逆函子對 `(fwd, bwd)` 表達型別等價 $A \simeq B$，並提供段律 `sect_ok` ($g(f(a)) = a$)、回縮律 `retr_ok` ($f(g(b)) = b$) 與有限全域等價檢驗 `is_equiv_finite`。 |
| `equiv_refl`, `equiv_symm`, `equiv_trans` | **型別等價構成群胚等價關係定理** | 構造恆等、逆轉與合成等價，驗證 $\simeq$ 的自反、對稱與傳遞性。 |
| `transport_along_equiv` / `ap_preserves_eq` | **萊布尼茲不可區分性與單價搬運投影（Leibniz / Transport Axiom）** | 實現函數作用保等價 `ap` 以及謂詞沿等價 $e : A \simeq B$ 的反變／協變搬運。 |
| `contrapositive_holds`, `impl_trans_holds`, `de_morgan_holds`, `dne_holds` | **構造性與可判定布林命題演算定理** | 在可判定有限型別上逐點驗證逆否命題律、蘊涵傳遞律、De Morgan 定律與雙重否定消去。 |

### 2. `hit.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `s1_loop`, `s1_concat`, `s1_inv`, `pi1_s1_equiv` | **高階歸納型別圓 $S^1$ 與基本群定理 $\pi_1(S^1) \simeq \mathbb{Z}$** | 以繞數（Winding Number）作為覆蓋空間編碼／解碼（Encode–Decode Method）的計算內核，給出迴路空間 $\Omega(S^1, \mathrm{base})$ 與整數加法群 $\mathbb{Z}$ 的顯式等價。 |
| `quotient_well_defined` | **集合商高階歸納型別消去原則（Set-Quotient Elimination Principle）** | 檢驗函數 $h : R \to C$ 在模理想關係 $a - b \in I$ 下是否良定義（即尊重路徑構造子 $\mathrm{glue}(a, b)$），從而誘導商映射 $\bar{h} : R/I \to C$。 |
| `is_prop_finite` / `uip_witness` | **同倫截斷層級公理（Truncation Levels: $-1$-Type `isProp` & $0$-Type `isSet` / UIP）** | 驗證命題截斷（任意兩元相等）與集合層級的恆等路徑唯一性（Uniqueness of Identity Proofs）。 |

### 3. `category.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `FinCat` / `check_category_laws` | **有限範疇公理（Category Axioms: Identity & Associativity）** | 以態射合成表表示有限範疇，窮舉檢驗左右單位律 $1_B \circ f = f = f \circ 1_A$ 與結合律 $(h \circ g) \circ f = h \circ (g \circ f)$。 |
| `free_forgetful_hom_bijection` | **自由—遺忘伴隨函子定理 $F \dashv U : \mathrm{Hom}_R(R^k, M) \cong \mathrm{Map}(\{1,\dots,k\}, U(M))$** | 驗證自由 $R$-模的泛性質：$R^k \to M$ 的模同態數恆等於 $|M|^k$，且由基元像唯一決定。 |
| `crt_forward` / `crt_ring_equiv_holds` | **中國剩餘定理作為環範疇自然等價 $\mathbb{Z}/\prod m_i\mathbb{Z} \simeq \prod \mathbb{Z}/m_i\mathbb{Z}$** | 驗證當模數兩兩互質時，餘數投影映射為保持加法與乘法的雙射等價。 |

### 4. `rewrite.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `RewriteRule` / `normalize_word` / `is_locally_confluent` | **Newman 引理與字串重寫匯合性演算法（Termination + Local Confluence $\implies$ Confluence）** | 在良基（Well-founded）終止重寫系統中，檢驗臨界對（Critical Pairs）的局部匯合性以保證正規形（Normal Form）唯一，作為有限呈現么半群字問題的判定演算法。 |

### 5. `hott_test.mbt`
- **白盒測試**：驗證 qinv 等價群胚律、$\pi_1(S^1) \simeq \mathbb{Z}$ 繞數同構、自由模伴隨雙射、CRT 等價與重寫系統正規形唯一性。
