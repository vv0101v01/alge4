# `scheme/` — Grothendieck 仿射概形、Zariski 拓撲與結構層黏合模組（Affine Schemes $\mathrm{Spec}(R)$ & Structure Sheaf Gluing）

本資料夾將 `finite/` 的有限交換環提升為 Grothendieck 仿射概形 $(X, \mathcal{O}_X) = \mathrm{Spec}(R)$，實現質理想譜、主開集基 $D(f)$、Zariski 開集格（Frame）、局部環莖 $\mathcal{O}_{X, \mathfrak{p}} = R_{\mathfrak{p}}$、截面限制同態與層黏合雙射公理。

---

## 檔案清單與所含定理／演算法／公理

### 1. `scheme.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `Spec` / `spec(r)` | **Grothendieck 質理想譜構造 $\mathrm{Spec}(R)$** | 提取環 $R$ 的全體質理想作為拓撲空間底點，並預計算全體 Zariski 開集。 |
| `basic_open(sp, f)` | **主開集基定理 $D(f) = \{\mathfrak{p} \in \mathrm{Spec}(R) \mid f \notin \mathfrak{p}\}$** | 實現主開集映射，滿足乘法基恆等式 $D(f) \cap D(g) = D(fg)$、$D(0) = \emptyset$、$D(1) = \mathrm{Spec}(R)$，以及 $D(f) = \emptyset \iff f \in \mathrm{Nil}(R)$。 |
| `vanishing_closed(sp, idl)` | **Zariski 閉集 $V(I) = \{\mathfrak{p} \in \mathrm{Spec}(R) \mid I \subseteq \mathfrak{p}\}$** | 驗證 $V(I) = V(\sqrt{I})$、$V(I + J) = V(I) \cap V(J)$ 與 $V(I \cdot J) = V(I) \cup V(J)$。 |
| `irreducible_components(sp)` | **不可約分支＝極小質理想閉包定理** | $\mathrm{Spec}(R)$ 的不可約分支一對一對應於 $R$ 的極小質理想 $\{V(\mathfrak{p}_{\min})\}$。 |
| `stalk_at(sp, p_idx)` | **結構層莖定理 $\mathcal{O}_{X, \mathfrak{p}} \cong R_{\mathfrak{p}}$** | 在質理想點 $\mathfrak{p}$ 處對 $S = R \setminus \mathfrak{p}$ 局部化，得到唯一極大理想為 $\mathfrak{p}R_{\mathfrak{p}}$ 的局部環。 |
| `sections_over_basic(r, f)` / `restriction(r, f, g)` | **結構層截面 $\mathcal{O}_X(D(f)) = R_f$ 與反變限制同態** | 當 $D(f g) \subseteq D(f)$ 時，構造自然局部化同態 $\mathrm{res}_{D(f) \to D(fg)} : R_f \to R_{fg}$，滿足預層函子律 $\mathrm{res}_{U \to U} = \mathrm{id}$ 與 $\mathrm{res}_{V \to W} \circ \mathrm{res}_{U \to V} = \mathrm{res}_{U \to W}$。 |
| `sheaf_gluing_bijective(r, h, f, g)` | **結構層黏合公理定理（Sheaf Gluing Axiom on Principal Opens）** | 定理：當 $D(h) = D(hf) \cup D(hg)$ 時，序列 $0 \to \mathcal{O}_X(D(h)) \to \mathcal{O}_X(D(hf)) \times \mathcal{O}_X(D(hg)) \rightrightarrows \mathcal{O}_X(D(hfg))$ 為集合正合（即均衡子 Equalizer）：每對在交集 $D(hfg)$ 上限制相等的局部截面 $(u, v)$，恰存在唯一全局截面 $s \in R_h$。 |

### 2. `scheme_tests_wbtest.mbt`
- **白盒測試**：驗證主開集乘法基定律、冪零元在 $\mathrm{Spec}(R)$ 上處處消失、預層限制函子結合律與二元開覆蓋上的結構層唯一黏合定理。
