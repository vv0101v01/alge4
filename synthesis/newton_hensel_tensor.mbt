// =============================================================================
// 合成新演算法（階段 V — 代數幾何）：零成本結構張量座標環、點求值態雙射與
// 冪零／t-進 Newton–Hensel 精度倍增引擎
// (Zero-Cost Structure Tensor Coordinate Ring, Character–Point Hom-Bijection &
//  Nilpotent / t-adic Newton–Hensel Precision-Doubling Engine)
//
// 跨五庫（alge + algo + alge1 + alge2 + alge3）代數幾何共通因子提煉：
//   1. `alge/algebra-ct/quot` + `alge/algebra/ga`：零成本結構張量 T[i,j,t]、張量環公理判準、
//      拉格朗日原始冪等元與有理點求值矩陣；
//   2. `alge/algebra-ct/val`：截斷離散賦值環 K[[t]]/(t^d)、t-進賦值與 Newton 精度倍增求逆／平方根；
//   3. `algo/finite` + `algo/geometry`：零維商代數 FinAlg、Hilbert 零點定理與代數簇有理點集 V(I)。
//
// 核心統一原理：
//   • 截斷冪級數環 K[[t]]/(t^d)、局部阿廷商環 K[x]/I 與半單座標環全部統一為同一個
//     扁平結構張量代數 `ZeroCostTensorAlg`（乘法僅需 O(d²) 查表累加，無執行期 Gröbner 約化）；
//   • 在任意 `ZeroCostTensorAlg` 上，只要初始近似 b_0 滿足 1 - a·b_0 ∈ Nil(A)，
//     統一的 **Newton 二次收斂倍增算子** `b_{k+1} = b_k · (2·1 - a·b_k)` 必在 ⌈log₂ d⌉ 步內
//     將誤差平方消滅 `(1 - a·b_0)^{2^k} = 0`，同時涵蓋 t-進級數求逆與局部環單位求逆！
//   • 實現完美代數幾何態雙射（Morphism Bijection）：
//       Hom_{K-Alg}(A, K)  ≃  V_K(I)
//     每個 K-代數特徵同態 χ : A -> K 一對一對應仿射簇的有理點，並對偶出正交拉格朗日冪等元基。
// =============================================================================

///|
/// 零成本扁平結構張量代數（Zero-Cost Flat Structure Tensor Algebra）：
/// - `p`：基域素數特徵 `𝔽_p`；
/// - `d`：向量空間維數 `dim_{𝔽_p} A`（基底 `e_0 = 1, e_1, ..., e_{d-1}`）；
/// - `nvar`：環境多項式環變數個數；
/// - `basis_exps`：長 `d * nvar` 的標準單項式指數表；
/// - `mul_tensor`：長 `d * d * d` 的結構常數張量，`mul_tensor[(i * d + j) * d + t]`
///                 為 `e_i · e_j` 在 `e_t` 上的座標。
pub(all) struct ZeroCostTensorAlg {
  p : Int32
  d : Int32
  nvar : Int32
  basis_exps : Array[Int32]
  mul_tensor : Array[Int32]
}

///|
/// 由 `algo/finite::FinAlg`（單變數生成元 `1, x, ..., x^{d-1}`）直接萃取扁平結構張量 `ZeroCostTensorAlg`。
pub fn ZeroCostTensorAlg::from_finalg(alg : @finite.FinAlg) -> ZeroCostTensorAlg {
  let p = alg.p
  let d = alg.dim
  let basis_exps : Array[Int32] = []
  for i in 0..<d {
    basis_exps.push(i)
  }
  let mul_tensor = Array::make(d * d * d, 0)
  for i in 0..<d {
    for j in 0..<d {
      let base_off = (i * d + j) * d
      for t in 0..<d {
        mul_tensor[base_off + t] = @num.mod_pos(alg.mult[i].data[t][j], p)
      }
    }
  }
  ZeroCostTensorAlg::{ p, d, nvar: 1, basis_exps, mul_tensor }
}

///|
/// 由截斷離散賦值環（落特環 / Truncated DVR `𝔽_p[[t]] / (t^d)`，整合 `alge/val`）
/// 直接構造結構張量代數：`e_i = t^i`，當 `i + j < d` 時 `e_i · e_j = e_{i+j}`，否則為 `0`。
pub fn ZeroCostTensorAlg::from_truncated_dvr(
  p : Int32,
  d : Int32,
) -> ZeroCostTensorAlg {
  let basis_exps : Array[Int32] = []
  for i in 0..<d {
    basis_exps.push(i)
  }
  let mul_tensor = Array::make(d * d * d, 0)
  for i in 0..<d {
    for j in 0..<d {
      if i + j < d {
        mul_tensor[(i * d + j) * d + (i + j)] = 1
      }
    }
  }
  ZeroCostTensorAlg::{ p, d, nvar: 1, basis_exps, mul_tensor }
}

///|
/// 單位元向量 `1_A = [1, 0, ..., 0]`。
pub fn ZeroCostTensorAlg::one(self : ZeroCostTensorAlg) -> Array[Int32] {
  let out = Array::make(self.d, 0)
  if self.d > 0 {
    out[0] = 1
  }
  out
}

///|
/// 零元向量 `0_A = [0, ..., 0]`。
pub fn ZeroCostTensorAlg::zero(self : ZeroCostTensorAlg) -> Array[Int32] {
  Array::make(self.d, 0)
}

///|
/// 向量加法 `a + b (mod p)`。
pub fn ZeroCostTensorAlg::add(
  self : ZeroCostTensorAlg,
  a : Array[Int32],
  b : Array[Int32],
) -> Array[Int32] {
  let out = Array::make(self.d, 0)
  for i in 0..<self.d {
    out[i] = @num.mod_pos(a[i] + b[i], self.p)
  }
  out
}

///|
/// 向量減法 `a - b (mod p)`。
pub fn ZeroCostTensorAlg::sub(
  self : ZeroCostTensorAlg,
  a : Array[Int32],
  b : Array[Int32],
) -> Array[Int32] {
  let out = Array::make(self.d, 0)
  for i in 0..<self.d {
    out[i] = @num.mod_pos(a[i] - b[i], self.p)
  }
  out
}

///|
/// 純量乘法 `c · a (mod p)`。
pub fn ZeroCostTensorAlg::scale(
  self : ZeroCostTensorAlg,
  c : Int32,
  a : Array[Int32],
) -> Array[Int32] {
  let out = Array::make(self.d, 0)
  let cn = @num.mod_pos(c, self.p)
  for i in 0..<self.d {
    out[i] = @num.mod_pos(cn * a[i], self.p)
  }
  out
}

///|
/// 零成本張量查表乘法 `a · b`（整合 `alge/ga::Tables::mul`，複雜度 `O(|supp(a)|·|supp(b)|·d)`）。
pub fn ZeroCostTensorAlg::mul(
  self : ZeroCostTensorAlg,
  a : Array[Int32],
  b : Array[Int32],
) -> Array[Int32] {
  let d = self.d
  let p = self.p
  let out = Array::make(d, 0)
  for i in 0..<d {
    let ai = @num.mod_pos(a[i], p)
    if ai == 0 {
      continue
    }
    for j in 0..<d {
      let bj = @num.mod_pos(b[j], p)
      if bj == 0 {
        continue
      }
      let coef = @num.mod_pos(ai * bj, p)
      let cell = (i * d + j) * d
      for t in 0..<d {
        let v = self.mul_tensor[cell + t]
        if v != 0 {
          out[t] = @num.mod_pos(out[t] + coef * v, p)
        }
      }
    }
  }
  out
}

///|
/// 驗證結構張量是否滿足交換環公理（`alge` 定理 2.3：左/右單位律、交換律、結合律）。
pub fn ZeroCostTensorAlg::verify_tensor_ring_axioms(
  self : ZeroCostTensorAlg,
) -> Bool {
  let d = self.d
  let p = self.p
  for i in 0..<d {
    for t in 0..<d {
      let delta = if i == t { 1 } else { 0 }
      if self.mul_tensor[(i * d + 0) * d + t] != delta ||
        self.mul_tensor[(0 * d + i) * d + t] != delta {
        return false
      }
    }
  }
  for i in 0..<d {
    for j in 0..<d {
      for t in 0..<d {
        if self.mul_tensor[(i * d + j) * d + t] !=
          self.mul_tensor[(j * d + i) * d + t] {
          return false
        }
      }
    }
  }
  for i in 0..<d {
    for j in 0..<d {
      for k in 0..<d {
        for t in 0..<d {
          let mut lhs = 0
          let mut rhs = 0
          for s in 0..<d {
            lhs = @num.mod_pos(
              lhs +
              self.mul_tensor[(i * d + j) * d + s] *
              self.mul_tensor[(s * d + k) * d + t],
              p,
            )
            rhs = @num.mod_pos(
              rhs +
              self.mul_tensor[(j * d + k) * d + s] *
              self.mul_tensor[(i * d + s) * d + t],
              p,
            )
          }
          if lhs != rhs {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// `t`-進賦值（`t`-adic Valuation，整合 `alge/val::valuation`）：
/// 返回最小非零基底指標 `i`（零元返回 `-1`），滿足 `v(f·g) = v(f) + v(g)`（未截斷溢位時）。
pub fn ZeroCostTensorAlg::t_adic_valuation(
  self : ZeroCostTensorAlg,
  a : Array[Int32],
) -> Int32 {
  for i in 0..<self.d {
    if @num.mod_pos(a[i], self.p) != 0 {
      return i
    }
  }
  -1
}

///|
/// 統一冪零／`t`-進 Newton 精度倍增求逆算子（Unified Nilpotent / `t`-adic Newton Inversion）：
/// 設 `a = a_0·1 + n`（其中 `a_0 = a[0] != 0 mod p` 且 `n` 冪零，`n^d = 0`）。
/// 演算法：
///   1. 取初始近似 `b = a_0^{-1} · 1_A`，此時誤差 `r_0 = 1 - a·b ∈ (n)`；
///   2. 執行二次收斂迭代 `b <- b · (2·1_A - a·b)`：
///      每步將誤差平方 `1 - a·b' = (1 - a·b)²`，故僅需 `⌈log₂ d⌉` 步即精確收斂至 `a^{-1}`！
pub fn ZeroCostTensorAlg::newton_inv(
  self : ZeroCostTensorAlg,
  a : Array[Int32],
) -> Array[Int32]? {
  if self.d == 0 {
    return None
  }
  let a0 = @num.mod_pos(a[0], self.p)
  if a0 == 0 {
    return None
  }
  let inv0 = match @num.invmod(a0, self.p) {
    Some(v) => v
    None => return None
  }
  let mut b = self.scale(inv0, self.one())
  let two_one = self.scale(2, self.one())
  let mut prec = 1
  while prec < self.d {
    let ab = self.mul(a, b)
    let factor = self.sub(two_one, ab)
    b = self.mul(b, factor)
    prec = prec * 2
  }
  if self.mul(a, b) == self.one() {
    Some(b)
  } else {
    None
  }
}

///|
/// 統一冪零／`t`-進 Newton 精度倍增平方根算子（Unified Newton Square-Root，要求奇素數特徵 `p > 2`）：
/// 設 `a[0]` 在 `𝔽_p` 中有平方根 `s_0`（`s_0² ≡ a[0] mod p`）。
/// 以 `s <- 2^{-1} · (s + a · s^{-1})` 執行 `⌈log₂ d⌉` 步精度倍增，返回滿足 `s² == a` 的平方根 `s`。
pub fn ZeroCostTensorAlg::newton_sqrt(
  self : ZeroCostTensorAlg,
  a : Array[Int32],
) -> Array[Int32]? {
  if self.d == 0 || self.p <= 2 {
    return None
  }
  let a0 = @num.mod_pos(a[0], self.p)
  if a0 == 0 {
    return None
  }
  let mut s0 = -1
  for c in 1..<self.p {
    if @num.mod_pos(c * c, self.p) == a0 {
      s0 = c
      break
    }
  }
  if s0 < 0 {
    return None
  }
  let inv2 = match @num.invmod(2, self.p) {
    Some(v) => v
    None => return None
  }
  let mut s = self.scale(s0, self.one())
  let mut prec = 1
  while prec < self.d {
    match self.newton_inv(s) {
      None => return None
      Some(s_inv) => {
        let q = self.mul(a, s_inv)
        s = self.scale(inv2, self.add(s, q))
      }
    }
    prec = prec * 2
  }
  if self.mul(s, s) == a {
    Some(s)
  } else {
    None
  }
}

///|
/// 在仿射點 `pt ∈ 𝔽_p^nvar` 處對座標向量 `c ∈ A` 求值 `χ_pt(c)`（整合 `alge/quot::eval_coords`）。
pub fn ZeroCostTensorAlg::eval_at_point(
  self : ZeroCostTensorAlg,
  c : Array[Int32],
  pt : Array[Int32],
) -> Int32 {
  let mut acc = 0
  for i in 0..<self.d {
    let ci = @num.mod_pos(c[i], self.p)
    if ci == 0 {
      continue
    }
    let mut mono_val = 1
    for v in 0..<self.nvar {
      let exp = self.basis_exps[i * self.nvar + v]
      if exp > 0 {
        mono_val = @num.mod_pos(
          mono_val * @num.powmod(pt[v], exp, self.p),
          self.p,
        )
      }
    }
    acc = @num.mod_pos(acc + ci * mono_val, self.p)
  }
  acc
}

///|
/// 判定線性泛函 `chi : A -> 𝔽_p`（由基底像 `chi_basis[i] = χ(e_i)` 給定）是否為
/// `𝔽_p`-代數同態（即滿足 `χ(1) = 1` 且 `∀i, j, χ(e_i · e_j) = χ(e_i) χ(e_j)`）。
pub fn ZeroCostTensorAlg::is_algebra_character(
  self : ZeroCostTensorAlg,
  chi_basis : Array[Int32],
) -> Bool {
  if chi_basis.length() != self.d || self.d == 0 {
    return false
  }
  if @num.mod_pos(chi_basis[0], self.p) != 1 {
    return false
  }
  for i in 0..<self.d {
    for j in 0..<self.d {
      let mut lhs = 0
      let cell = (i * self.d + j) * self.d
      for t in 0..<self.d {
        lhs = @num.mod_pos(
          lhs + self.mul_tensor[cell + t] * chi_basis[t],
          self.p,
        )
      }
      let rhs = @num.mod_pos(chi_basis[i] * chi_basis[j], self.p)
      if lhs != rhs {
        return false
      }
    }
  }
  true
}

///|
/// 枚舉 `A` 的全體 `𝔽_p`-代數同態（特徵標集合 `Hom_{𝔽_p-Alg}(A, 𝔽_p)`）：
/// 定理（代數幾何核心態雙射 Hom-Bijection，整合 `alge` 定理 2.10 與 `algo/geometry`）：
///   `Hom_{𝔽_p-Alg}(K[x]/I, 𝔽_p)  ≃  V_{𝔽_p}(I)`
/// 每個代數同態 `χ` 唯一對應代數簇 `V(I)` 的一個 `𝔽_p`-有理點！
pub fn ZeroCostTensorAlg::algebra_characters(
  self : ZeroCostTensorAlg,
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let d = self.d
  let p = self.p
  let mut total = 1
  for _ in 0..<(d - 1) {
    total = total * p
  }
  for code in 0..<total {
    let chi = Array::make(d, 0)
    chi[0] = 1
    let mut tmp = code
    for i in 1..<d {
      chi[i] = tmp % p
      tmp = tmp / p
    }
    if self.is_algebra_character(chi) {
      out.push(chi)
    }
  }
  out
}

///|
/// 驗證有理點集 `points ⊆ V(I)` 與特徵標集 `Hom_{𝔽_p-Alg}(A, 𝔽_p)` 之間的**完美態雙射（Hom-Bijection）**：
/// 對每個點 `pt ∈ points`，求值泛函 `e_i ↦ e_i(pt)` 必為合法代數同態，且互不相同、數目與 `algebra_characters()` 完全相等！
pub fn ZeroCostTensorAlg::verify_character_point_hom_bijection(
  self : ZeroCostTensorAlg,
  points : Array[Array[Int32]],
) -> Bool {
  let chars = self.algebra_characters()
  if chars.length() != points.length() {
    return false
  }
  let eval_chars : Array[Array[Int32]] = []
  for pt in points {
    let chi = Array::make(self.d, 0)
    for i in 0..<self.d {
      let ei = Array::make(self.d, 0)
      ei[i] = 1
      chi[i] = self.eval_at_point(ei, pt)
    }
    if !self.is_algebra_character(chi) {
      return false
    }
    for prev in eval_chars {
      if prev == chi {
        return false
      }
    }
    eval_chars.push(chi)
  }
  true
}

///|
/// 由有理點求值矩陣透過 `@linalg.Matrix::inverse` 對偶合成拉格朗日正交本原冪等元基
/// （整合 `alge/ga::primitive_idempotents` 與 `algo/finite::primitive_idempotents`）：
/// 當 `|points| == d`（半單エタール座標環）時，求值矩陣 `E[r, j] = e_j(P_r)` 的逆矩陣第 `r` 欄
/// 即第 `r` 個本原冪等元 `e^{(r)} ∈ A`，滿足 `e^{(r)}(P_s) = δ_{r,s}`、`e^{(r)}·e^{(s)} = δ_{r,s} e^{(r)}` 且 `∑ e^{(r)} = 1_A`！
pub fn ZeroCostTensorAlg::lagrange_primitive_idempotents(
  self : ZeroCostTensorAlg,
  points : Array[Array[Int32]],
) -> Array[Array[Int32]]? {
  let d = self.d
  if points.length() != d {
    return None
  }
  let eval_mat = @linalg.Matrix::zero(self.p, d, d)
  for r in 0..<d {
    for j in 0..<d {
      let ej = Array::make(d, 0)
      ej[j] = 1
      eval_mat.data[r][j] = self.eval_at_point(ej, points[r])
    }
  }
  let idems : Array[Array[Int32]] = []
  for r in 0..<d {
    let rhs = Array::make(d, 0)
    rhs[r] = 1
    match eval_mat.solve(rhs) {
      None => return None
      Some(er) => idems.push(er)
    }
  }
  Some(idems)
}
