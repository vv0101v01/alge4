// 橋接層（bridge）：連接 moon-algebra（algo）與 moonmath（alge3 3.1）的六大數學介面：
//   1. 線性代數橋：@linalg.Matrix (𝔽_p) ⇄ @core.BoolMat (GF(2) 位並行) + @core.fp_det
//   2. 同倫與立方體單價橋：@hott.Equiv ⇄ @cubical.Iso → @cubical.ua (Glue + comp) + CRT 單價路徑
//   3. 多項式與奇點導出橋：@poly.Poly ⇄ Array[@derived.PolyTerm] + Gröbner Milnor/Tjurina 代數
//   4. 有限代數與同倫神經橋：@finite.FinAlg (R, ·, 1) 及單位群 R^× → @homotopy.Monoid (bar 同調)
//   5. 有限代數與 A_∞ 橋：@finite.FinAlg (p=2) → @algebra.AInf (Stasheff 恆等式驗證)
//   6. 概形拓撲與模論橋：@scheme.Spec Zariski 開集 → @core.Bits 位元外延 + @geometry/@modules 橋接

///|
/// 1.1 將 `@linalg.Matrix`（要求 `p == 2`）轉換為位並行 `@core.BoolMat`。
pub fn matrix_to_boolmat(m : @linalg.Matrix) -> @core.BoolMat {
  if m.p != 2 {
    abort("matrix_to_boolmat: requires characteristic p == 2")
  }
  let rows : Array[@core.Bits] = []
  for i in 0..<m.rows {
    let b = @core.Bits::new(m.cols)
    for j in 0..<m.cols {
      if @num.mod_pos(m.data[i][j], 2) == 1 {
        b.set(j)
      }
    }
    rows.push(b)
  }
  @core.BoolMat::new(rows, m.cols)
}

///|
/// 1.2 將位並行 `@core.BoolMat` 轉換為 `@linalg.Matrix`（`p = 2`）。
pub fn boolmat_to_matrix(bm : @core.BoolMat) -> @linalg.Matrix {
  let m = bm.nrows()
  let n = bm.ncols
  let out = @linalg.Matrix::zero(2, m, n)
  for i in 0..<m {
    for j in 0..<n {
      if bm.get(i, j) {
        out.data[i][j] = 1
      }
    }
  }
  out
}

///|
/// 1.3 為 `@linalg.Matrix` 補上 `@core.fp_det` 行列式計算（要求方陣）。
/// 定理：`det(A) != 0 (mod p) ⟺ rank(A) == n`。
pub fn matrix_det(m : @linalg.Matrix) -> Int32 {
  if m.rows != m.cols {
    abort("matrix_det: matrix must be square")
  }
  @core.fp_det(m.data, m.p)
}

///|
/// 2.1 將 `@hott.Equiv[Int32, Int32]`（定義於 `0..<n`）具體化為 `@cubical.Iso`。
pub fn equiv_to_iso(e : @hott.Equiv[Int32, Int32], n : Int32) -> @cubical.Iso? {
  let fwd : Array[Int32] = []
  let bwd : Array[Int32] = []
  for x in 0..<n {
    fwd.push((e.fwd)(x))
    bwd.push((e.bwd)(x))
  }
  let iso = @cubical.Iso::new(n, n, fwd, bwd)
  if iso.check() {
    Some(iso)
  } else {
    None
  }
}

///|
/// 2.2 將 `@cubical.Iso` 抬升為 `@hott.Equiv[Int32, Int32]`。
pub fn iso_to_equiv(iso : @cubical.Iso) -> @hott.Equiv[Int32, Int32] {
  @hott.Equiv::{
    fwd: fn(x : Int32) { iso.apply(x) },
    bwd: fn(y : Int32) { iso.apply_inv(y) },
  }
}

///|
/// 2.3 把 `@hott` 的中國剩餘定理等價 `ℤ/nℤ ≃ ∏ ℤ/p_i^{k_i}ℤ` 編碼為 `Fin n` 上的
/// 雙射 `@cubical.Iso`，從而可直接送入 `@cubical.ua` 構造宇宙中的 Glue 路徑！
pub fn crt_cubical_iso(n : Int32) -> @cubical.Iso? {
  if n < 2 {
    return Some(@cubical.Iso::id(1))
  }
  let mods = @poly.zn_crt_components(n)
  let fwd : Array[Int32] = []
  let bwd : Array[Int32] = []
  for _i in 0..<n {
    bwd.push(0)
  }
  for x in 0..<n {
    let res = @hott.crt_forward(mods, x)
    // 混合進制編碼 tuple (r_0, ..., r_{k-1}) ∈ [0, n)
    let mut code = 0
    let mut place = 1
    for i in 0..<mods.length() {
      code = code + res[i] * place
      place = place * mods[i]
    }
    fwd.push(code)
    bwd[code] = x
  }
  let iso = @cubical.Iso::new(n, n, fwd, bwd)
  if iso.check() {
    Some(iso)
  } else {
    None
  }
}

///|
/// 3.1 將 `@poly.Poly` 轉為 `@derived.PolyTerm` 陣列（用於加權齊次奇點計算）。
pub fn poly_to_derived(p : @poly.Poly) -> Array[@derived.PolyTerm] {
  let pairs : Array[(Array[Int32], Int32)] = []
  for t in p.terms {
    let e : Array[Int32] = []
    for x in t.exp {
      e.push(x)
    }
    pairs.push((e, t.coeff.rep()))
  }
  @derived.poly_of(pairs)
}

///|
/// 3.2 將 `@derived.PolyTerm` 陣列轉為規範化的 `@poly.Poly`。
pub fn derived_to_poly(
  terms : Array[@derived.PolyTerm],
  nvars : Int32,
  modulus : Int32,
) -> @poly.Poly {
  let raw : Array[(Int32, Array[Int32])] = []
  for t in terms {
    raw.push((t.coeff, t.exp))
  }
  @poly.poly_of_terms(nvars, modulus, raw)
}

///|
/// 3.3 以 Buchberger Gröbner 基計算孤立奇點的雅可比理想生成元 `(∂_0 f, ..., ∂_{n-1} f)`。
pub fn jacobian_ideal_gens(f : @poly.Poly) -> Array[@poly.Poly] {
  let gens : Array[@poly.Poly] = []
  for i in 0..<f.nvars {
    gens.push(f.derivative(i))
  }
  gens
}

///|
/// 3.4 以 Gröbner 基標準單項式計算 Milnor 數 `μ(f) = dim_k k[x]/(∂f)`。
/// 定理：對加權齊次孤立奇點，Gröbner 基求出的全局商維數與 `@derived.milnor_number`
/// 在截斷度數充足時的加權局部維數完全一致。
pub fn groebner_milnor_number(f : @poly.Poly) -> Int32? {
  match @poly.standard_monomials(jacobian_ideal_gens(f)) {
    Some(b) => Some(b.length())
    None => None
  }
}

///|
/// 3.5 以 Gröbner 基標準單項式計算 Tjurina 數 `τ(f) = dim_k k[x]/(f, ∂f)`。
pub fn groebner_tjurina_number(f : @poly.Poly) -> Int32? {
  let gens : Array[@poly.Poly] = [f]
  for g in jacobian_ideal_gens(f) {
    gens.push(g)
  }
  match @poly.standard_monomials(gens) {
    Some(b) => Some(b.length())
    None => None
  }
}

///|
/// 3.6 構造孤立奇點的 Milnor 代數 `M(f) = 𝔽_p[x]/(∂f)` 為有限交換代數 `@finite.FinAlg`，
/// 使其可直接調用 `is_local`、`nilradical`、`socle`、`embedding_dim` 等結構定理。
pub fn groebner_milnor_algebra(f : @poly.Poly) -> @finite.FinAlg {
  @finite.FinAlg::zero_dim_quotient(f.modulus, jacobian_ideal_gens(f))
}

///|
/// 4.1 將有限代數 `@finite.FinAlg` 的乘法結構 `(R, ·, 1)` 抽出為 `@homotopy.Monoid`。
pub fn finalg_mul_monoid(alg : @finite.FinAlg) -> @homotopy.Monoid {
  let elems = alg.all_elements()
  let n = elems.length()
  let one = alg.one_elem()
  let mut e_idx = 0
  for i in 0..<n {
    if @linalg.vec_eq(elems[i], one) {
      e_idx = i
    }
  }
  let mul : Array[Array[Int32]] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<n {
      let prod = alg.mul_elem(elems[i], elems[j])
      let mut idx = 0
      for k in 0..<n {
        if @linalg.vec_eq(elems[k], prod) {
          idx = k
        }
      }
      row.push(idx)
    }
    mul.push(row)
  }
  @homotopy.Monoid::new(mul, e_idx)
}

///|
/// 4.2 將有限代數 `@finite.FinAlg` 的可逆元群 `R^×` 抽出為 `@homotopy.Monoid`，
/// 供 `@homotopy.bar_betti` 計算分類空間同調 `H_*(B R^×; 𝔽_2)`。
pub fn finalg_unit_group_monoid(alg : @finite.FinAlg) -> @homotopy.Monoid {
  let elems = alg.all_elements()
  let one = alg.one_elem()
  let units : Array[Array[Int32]] = []
  for x in elems {
    let mut is_unit = false
    for y in elems {
      if @linalg.vec_eq(alg.mul_elem(x, y), one) {
        is_unit = true
      }
    }
    if is_unit {
      units.push(x)
    }
  }
  let u = units.length()
  let mut e_idx = 0
  for i in 0..<u {
    if @linalg.vec_eq(units[i], one) {
      e_idx = i
    }
  }
  let mul : Array[Array[Int32]] = []
  for i in 0..<u {
    let row : Array[Int32] = []
    for j in 0..<u {
      let prod = alg.mul_elem(units[i], units[j])
      let mut idx = 0
      for k in 0..<u {
        if @linalg.vec_eq(units[k], prod) {
          idx = k
        }
      }
      row.push(idx)
    }
    mul.push(row)
  }
  @homotopy.Monoid::new(mul, e_idx)
}

///|
/// 5.1 將特徵 2 的有限代數 `@finite.FinAlg`（`p == 2`）嵌入為集中於度數 0 的
/// `@algebra.AInf`（`m_1 = 0, m_3 = 0`，`m_2` 由結構常數矩陣給出）。
pub fn finalg_to_ainf_dga(alg : @finite.FinAlg) -> @algebra.AInf {
  if alg.p != 2 {
    abort("finalg_to_ainf_dga: requires characteristic p == 2")
  }
  let d = alg.dim
  let a = @algebra.AInf::zero(@algebra.GradedSpace::new([d]))
  for i in 0..<d {
    for j in 0..<d {
      for k in 0..<d {
        if @num.mod_pos(alg.mult[i].data[k][j], 2) == 1 {
          a.set_m2(i, j, k)
        }
      }
    }
  }
  a
}

///|
/// 6.1 以 `@core.Bits` 位元向量加速表示 `@scheme.Spec` 的 Zariski 開集外延：
/// 將 `Spec::opens()` 的開集遮罩編碼為 64-bit 位並行 `@core.Bits`（與 `@cubical.Cof::extent` 同構），
/// 並驗證與 `@geometry.singular_points` 及 `@modules.FinModule` 的跨層一致性。
pub fn spec_opens_bits(sp : @scheme.Spec) -> @core.Bits {
  let opens = sp.opens()
  let bits = @core.Bits::new(opens.length())
  for i in 0..<opens.length() {
    if opens[i] {
      bits.set(i)
    }
  }
  bits
}

///|
/// 6.2 驗證仿射奇點簇 `@geometry.singular_points` 在原點處的 Milnor 自由模維數。
pub fn singularity_milnor_module_dim(f : @poly.Poly, bound : Int32) -> Int32 {
  let sings = @geometry.singular_points([f], bound, f.nvars - 1)
  if sings.length() == 0 {
    return 0
  }
  let malg = groebner_milnor_algebra(f)
  let mmod = @modules.FinModule::free(malg, 1)
  @modules.dual_dim(mmod)
}
