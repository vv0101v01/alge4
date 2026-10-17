# `modules/` — 有限模論、投射／內射模、Matlis 對偶、擬凝聚層與連續逆極限模組（Module Theory, Duality & Sheaves of Modules）

本資料夾在有限交換環 $R$（`FinAlg`）上建構完整的模論體系，包含子模格與模同態、Maschke 半單補子模定理、投射模與自由模、Matlis/Pontryagin 線性對偶 $M^\vee$、仿射概形上的擬凝聚層 $\widetilde{M}$ 以及完備化逆系統 $\varprojlim M_n$。

---

## 檔案清單與所含定理／演算法／公理

### 1. `module.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `FinModule` / `FinSubmodule` | **$R$-模作用公理與子模閉包表示** | 將有限 $R$-模 $M$ 表示為底層 $\mathbb{F}_p$-向量空間加上滿足環同態律 $r \cdot (s \cdot m) = (rs) \cdot m$ 的純量乘法矩陣族。 |
| `enumerate_submodules(m)` | **子模完備模格（Modular Lattice of Submodules）枚舉演算法** | 以算子不變閉包枚舉 $M$ 的全體 $R$-子模，滿足 Dedekind 模律（Modular Law）：若 $A \subseteq C$，則 $A + (B \cap C) = (A + B) \cap C$。 |
| `ModHom` / `hom_kernel` / `hom_image` | **模同態第一同構定理（First Isomorphism Theorem for Modules）** | 檢驗 $R$-線性性 $f(r \cdot m) = r \cdot f(m)$，計算 $\ker(f)$ 與 $\mathrm{im}(f)$，驗證 $M/\ker(f) \cong \mathrm{im}(f)$。 |
| `is_exact_at(f, g)` | **正合序列判準（Exactness Criterion $\mathrm{im}(f) = \ker(g)$）** | 給定 $M_1 \xrightarrow{f} M_2 \xrightarrow{g} M_3$，檢驗 $g \circ f = 0$ 且 $\dim \mathrm{im}(f) = \dim \ker(g)$。 |

### 2. `projective.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `complement_exists(m, sub)` / `is_semisimple_module(m)` | **Maschke / 半單模有補子模格定理** | 模 $M$ 為半單模 $\iff$ 其子模格 $\mathrm{Sub}_R(M)$ 為**有補格（Complemented Lattice）**，即每個子模 $N \subseteq M$ 均存在直和補 $N'$ 使 $N \oplus N' = M$。 |
| `splitting_map(pi)` | **投射模滿同態分裂定理（Projective Splitting Criterion）** | 檢驗滿同態 $\pi : M \twoheadrightarrow P$ 是否存在 $R$-模截面 $s : P \to M$ 滿足 $\pi \circ s = \mathrm{id}_P$。 |
| `kaplansky_local_projective_is_free` | **Kaplansky 定理（局部環上的投射模必為自由模）** | 驗證在有限局部阿廷環 $(R, \mathfrak{m})$ 上，任何有限生成投射模皆同構於自由模 $R^n$。 |

### 3. `dual.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `dual_module(m)` / `double_dual_iso(m)` | **有限维 Matlis / $\mathbb{F}_p$-線性對偶反變自等價定理** | 定義對偶模 $M^\vee = \mathrm{Hom}_{\mathbb{F}_p}(M, \mathbb{F}_p)$ 並賦予右乘誘導的 $R$-模結構 $(r \cdot \varphi)(m) = \varphi(r \cdot m)$；驗證雙對偶自然同構 $M \xrightarrow{\sim} M^{\vee\vee}$ 與子模格反序對偶 $\mathrm{Sub}_R(M)^{\mathrm{op}} \cong \mathrm{Sub}_R(M^\vee)$。 |
| `is_gorenstein_ring(r)` | **零維 Gorenstein 環＝自內射環判準（Bass–Matlis Theorem）** | 有限交換局部環 $(R, \mathfrak{m})$ 為 Gorenstein（即自內射 $R \cong R^\vee$）$\iff$ 其底座 $\mathrm{Soc}(R)$ 為 $1$ 維單純模（唯一極小非零理想）。 |

### 4. `sheaf.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `localize_module_at_elem(m, f)` / `ModuleSheaf` | **Serre–Grothendieck 仿射擬凝聚層定理 $\widetilde{M}(D(f)) = M_f$** | 對任意有限 $R$-模 $M$，構造基本開集 $D(f) \subseteq \mathrm{Spec}(R)$ 上的局部化模截面 $M_f = S_f^{-1}M$、限制同態與全局截面自然同構 $\Gamma(\mathrm{Spec}\,R, \widetilde{M}) \cong M$。 |

### 5. `continuous.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `InvSystem` / `limit_threads` | **$\mathfrak{a}$-進拓撲與逆極限構造（$\mathfrak{a}$-adic Completion & Inverse Limit $\varprojlim M_t$）** | 給定逆系統 $\dots \to M_2 \xrightarrow{b_1} M_1 \xrightarrow{b_0} M_0$，計算全體相容線程 $\{(x_{n-1}, \dots, x_0) \in \prod M_t \mid b_t(x_{t+1}) = x_t\}$，並驗證有限阿廷環在冪零根濾過下的完備化自然同構 $M \xrightarrow{\sim} \varprojlim M/\mathfrak{m}^k M$。 |

### 6. `modules_tests_wbtest.mbt`
- **白盒測試**：驗證模同態第一同構定理、半單模補子模格、Gorenstein 對偶性（對偶數環 vs 尖點環）、擬凝聚層黏合與逆極限線程。
