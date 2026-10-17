# `finite/` — 有限維交換代數、阿廷環理想格與結構分解模組（Finite Commutative Algebras & Artinian Ring Theory）

本資料夾實現有限域 $\mathbb{F}_p$ 上的零維商代數 $R = \mathbb{F}_p[x_1, \dots, x_n]/I$，涵蓋理想枚舉、質理想與極大理想、冪零根與 Jacobson 根、乘性局部化 $S^{-1}R$、Socle、本原冪等元與 Wedderburn–Artin 結構分解。

---

## 檔案清單與所含定理／演算法／公理

### 1. `alg.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `FinAlg` | **有限零維交換 $\mathbb{F}_p$-代數結構常數表示** | 將維數為 $d$ 的商代數 $R \cong \mathbb{F}_p^d$ 表示為基元乘法表與 $|R| = p^d$ 個全體元素載體。 |
| `FinAlg::univariate_quotient(p, mod_coeffs)` | **單變數商代數構造定理 $\mathbb{F}_p[x]/(f(x))$** | 以長除法餘式建立伴隨矩陣與結構常數，當 $f$ 不可約時構造有限域 $\mathbb{F}_{p^d}$（Galois Field）。 |
| `FinAlg::zero_dim_quotient(p, gens)` | **Gröbner 基商代數標準單項式基底定理（Macaulay Basis Theorem）** | 先求理想 $I = \langle \text{gens} \rangle$ 的約化 Gröbner 基 $G$，枚舉不被 $\mathrm{LT}(G)$ 整除的標準單項式（Standard Monomials）作為 $\mathbb{F}_p$-基底，並由正規形 `poly_reduce` 構造乘法表。 |
| `units(self)` / `zero_divisors(self)` | **有限阿廷環正則元＝可逆元定理** | 在有限交換環中，每個元素非單位（可逆元）即零因子：$R = R^\times \sqcup Z(R)$。 |

### 2. `ideals.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `FinIdeal` / `ideal_generated_by` | **理想作為左乘算子不變子空間定理** | 將理想 $I \triangleleft R$ 視為在全體左乘矩陣 $\{L_a\}_{a \in R}$ 下不變的 $\mathbb{F}_p$-線性子空間，以 RREF 基底正規化。 |
| `enumerate_ideals(r)` | **理想完備模格 BFS 閉包枚舉演算法** | 從零理想 $(0)$ 出發，逐一加入主理想 $(x)$ 求和閉包，枚舉有限環的全體理想格 $\mathrm{Idl}(R)$。 |
| `prime_ideals(r)` / `maximal_ideals(r)` | **有限阿廷環質理想＝極大理想定理（Artinian Prime = Maximal Theorem）** | 有限整環必為體（Wedderburn 小定理），故在有限交換環中 $P \in \mathrm{Spec}(R) \iff R/P$ 為有限域 $\iff P \in \mathrm{Max}(R)$。 |
| `simple_ideals(r)` | **極小非零理想（原子 Atoms）枚舉** | 找出理想格中覆蓋 $(0)$ 的極小非零理想。 |
| `ideal_product(r, i, j)` / `ideal_quotient(r, i, j)` / `annihilator_ideal(r, j)` | **理想量化積 $I \cdot J$、導體 $(I : J)$ 與零化子 $\mathrm{Ann}_R(J)$** | 實現交換代數中理想乘法與殘差商運算 $(I : J) = \{x \in R \mid xJ \subseteq I\}$。 |
| `krull_dim(r)` / `longest_ideal_chain(r)` | **Krull 維數與 Jordan–Hölder 合成列長度定理** | 有限環為阿廷環，其 Krull 維數恆為 $0$，而最長理想鏈長度等於阿廷合成列長度加 $1$。 |

### 3. `radical.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `radical(r, i)` / `nilradical(r)` | **理想根與 Krull 冪零根定理 $\sqrt{I} = \bigcap_{\mathfrak{p} \supseteq I} \mathfrak{p}$** | 計算 $\sqrt{I} = \{x \in R \mid \exists k \ge 1,\, x^k \in I\}$，並驗證 $\mathrm{Nil}(R) = \sqrt{(0)} = \bigcap_{\mathfrak{p} \in \mathrm{Spec}(R)} \mathfrak{p}$。 |
| `jacobson_radical(r)` | **阿廷環 Jacobson 根＝冪零根定理 $J(R) = \mathrm{Nil}(R)$** | 計算 $J(R) = \bigcap_{\mathfrak{m} \in \mathrm{Max}(R)} \mathfrak{m}$，在有限交換環上恆等於 $\mathrm{Nil}(R)$。 |
| `socle(r)` | **環的底座定理 $\mathrm{Soc}(R) = \sum \text{極小理想} = \mathrm{Ann}_R(J(R))$** | 構造所有極小非零理想之和，等價於被 Jacobson 根零化的全體元素。 |
| `is_reduced_ring(r)` / `is_semisimple_ring(r)` | **約化環與半單環（Wedderburn–Artin）判準** | 在有限交換環中，$R$ 半單 $\iff J(R) = 0 \iff \mathrm{Nil}(R) = 0 \iff R$ 為有限域的直積。 |

### 4. `localize.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `MultiplicativeSet` / `localize(r, s)` | **乘性局部化 $S^{-1}R$ 泛性質與分式等價類構造演算法** | 對乘性閉集 $S \subseteq R$，以等價關係 $(a, s) \sim (b, t) \iff \exists u \in S,\, u(at - bs) = 0$ 構造商環 $S^{-1}R$ 與自然同態 $\iota : R \to S^{-1}R$。 |
| `localize_at_elem(r, f)` / `localize_at_prime(r, p)` | **基本開集局部化 $R_f$ 與局部環莖 $R_{\mathfrak{p}}$** | 分別對 $S_f = \{1, f, f^2, \dots\}$ 與 $S_{\mathfrak{p}} = R \setminus \mathfrak{p}$ 進行局部化，作為仿射概形結構層 $\mathcal{O}_{\mathrm{Spec}\,R}$ 的代數核心。 |

### 5. `structure.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `idempotents(r)` / `primitive_idempotents(r)` | **正交本原冪等元分解定理（Orthogonal Primitive Idempotents）** | 找出滿足 $e^2 = e$ 的全體冪等元及其極小非零元 $e_1, \dots, e_k$，滿足 $e_i e_j = \delta_{ij} e_i$ 且 $\sum e_i = 1$。 |
| `wedderburn_fields(r)` / `artin_local_factors(r)` | **交換阿廷環結構定理（Structure Theorem for Artinian Rings）** | 定理：任意有限交換阿廷環唯一分解為有限個局部阿廷環的直積 $R \cong \prod_{i=1}^k R e_i$；若 $R$ 半單則每個因子 $R e_i$ 皆為有限域（Wedderburn–Artin 定理）。 |

### 6. `finite_tests_wbtest.mbt`
- **白盒與屬性測試**：在 $\mathbb{F}_4$、$\mathbb{F}_2[x]/(x^2)$、$\mathbb{F}_3 \times \mathbb{F}_3$ 及尖點局部環 $\mathbb{F}_5[x,y]/(x^2,xy,y^2)$ 上驗證全套阿廷環定理。
