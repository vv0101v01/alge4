# `testutil/` — 代數公理通用檢驗器與測試輔助生成器模組（Algebraic Axiom Checkers & Test Generators）

本資料夾提供給全工作區白盒測試與 QuickCheck 屬性測試共用的小規模有限環、多項式、矩陣確定性構造器與環／群公理斷言輔助函數。

---

## 檔案清單與所含定理／演算法／公理

### 1. `testutil.mbt`
| 函數／結構 | 數學公理檢驗／輔助構造 | 說明 |
| :--- | :--- | :--- |
| `sample_rings` / `sample_polys` | **標準測試代數族構造器（Canonical Test Algebras）** | 生成涵蓋體（$\mathbb{F}_p, \mathbb{F}_{p^2}$）、局部冪零環（$\mathbb{F}_p[x]/(x^k)$）、半單乘積環（$\mathbb{F}_p \times \mathbb{F}_p$）與非主理想尖點環的代表性樣本集。 |
| `assert_ring_axioms` | **交換環八大公理全稱檢驗器（Commutative Ring Axiom Verifier）** | 在有限載體上窮舉檢驗加法阿貝爾群（結合律、交換律、零元、負元）、乘法交換么半群（結合律、交換律、單位元 $1$）以及左右分配律 $a(b+c) = ab + ac$。 |
