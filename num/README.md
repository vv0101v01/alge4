# `num/` — 數論與有限域底層算術模組（Number Theory & Finite Field Arithmetic）

本資料夾提供整數環 $\mathbb{Z}$、模環 $\mathbb{Z}/m\mathbb{Z}$ 與素域 $\mathbb{F}_p$ 的底層算術演算法與數論定理實現，作為整個 `moon-unified` 代數、幾何與同調計算的基石。

---

## 檔案清單與所含定理／演算法／公理

### 1. `num.mbt`
| 函數／結構 | 數學演算法／定理／公理 | 說明 |
| :--- | :--- | :--- |
| `gcd(a, b)` | **歐幾里得輾轉相除法（Euclidean Algorithm）** | 計算最大公因數 $\gcd(a, b) \ge 0$，滿足主理想整環性質 $(a, b) = (\gcd(a, b))$。 |
| `ext_gcd(a, b)` | **擴展歐幾里得演算法與裴蜀定理（Bézout's Identity）** | 求 $(g, x, y)$ 使得 $ax + by = g = \gcd(a, b)$；此為模逆元、主理想生成元與中國剩餘定理構造的核心演算法。 |
| `mod_pos(a, m)` | **歐幾里得帶餘除法正規化（Canonical Remainder Axiom）** | 將任意整數 $a$ 映射至正規剩餘類代表元 $r \in \{0, 1, \dots, m-1\}$，滿足 $a \equiv r \pmod m$。 |
| `add_mod`, `sub_mod`, `mul_mod`, `neg_mod` | **交換環 $\mathbb{Z}/m\mathbb{Z}$ 公理（Commutative Ring Axioms mod $m$）** | 實現模 $m$ 加法阿貝爾群、乘法結合律與分配律。 |
| `pow_mod(base, exp, m)` | **二進制反覆平方法（Binary Exponentiation / Square-and-Multiply）** | 在 $O(\log \text{exp})$ 步內計算 $a^e \bmod m$；驗證費馬小定理 $a^{p-1} \equiv 1 \pmod p$ 與歐拉定理。 |
| `inv_mod(a, m)` | **模可逆元定理（Modular Invertibility Criterion）** | 定理：$\bar{a} \in (\mathbb{Z}/m\mathbb{Z})^\times \iff \gcd(a, m) = 1$；當互質時由裴蜀係數返回唯一逆元 $a^{-1} \bmod m$，當 $m = p$ 為質數時賦予 $\mathbb{F}_p$ 體（Field）公理。 |
| `is_prime(n)` | **試除質數判定法（Primality Test up to $\sqrt{n}$）** | 依據算術基本定理，檢驗 $n \ge 2$ 是否無 $\le \lfloor\sqrt{n}\rfloor$ 的真因子，判定 $\mathbb{Z}/n\mathbb{Z}$ 是否為整環／有限域。 |
| `euler_totient(n)` | **歐拉 $\varphi$ 函數積性公式（Euler's Totient Multiplicative Formula）** | 利用質因數分解計算單位群階數 $\varphi(n) = |(\mathbb{Z}/n\mathbb{Z})^\times| = n \prod_{p \mid n} (1 - 1/p)$。 |
| `crt_pair(r1, m1, r2, m2)` / `crt_many` | **中國剩餘定理構造演算法（Chinese Remainder Theorem, CRT）** | 當 $\gcd(m_i, m_j) = 1$ 時，顯式構造環同構 $\mathbb{Z}/(\prod m_i)\mathbb{Z} \xrightarrow{\sim} \prod \mathbb{Z}/m_i\mathbb{Z}$ 的逆映射。 |

### 2. `num_test.mbt`
- **白盒與屬性測試**：驗證裴蜀恆等式 $ax + by = \gcd(a, b)$、有限域逆元律 $a \cdot a^{-1} \equiv 1 \pmod p$、費馬小定理、歐拉定理 $a^{\varphi(n)} \equiv 1 \pmod n$ 與中國剩餘定理同構唯一性。
