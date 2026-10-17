// =============================================================================
// 合成新演算法（階段 VI — 範疇論）：萬有伴隨態雙射（Hom-Bijection）、餘米田融合、
// 單價骨架對角化與張量—Hom 縮並引擎
// (Universal Adjunction Hom-Bijection, Coyoneda Fusion, Univalent Skeleton
//  Diagonalization & Tensor–Hom / Beck–Chevalley Contraction Engine)
//
// 跨五庫（alge + alge1 + alge2 + alge3 + algo）範疇論共通因子提煉：
//   1. 萬有伴隨態雙射 `Hom_D(L X, Y) ≃ Hom_C(X, R Y)` 與米田引理 `Nat(Hom(X, -), F) ≃ F(X)`
//      （統一 `algo/hott::free_forgetful_hom_bijection`、`alge1/functor::Free`、
//       `alge2/functors::Coyoneda` 與 `free_monoid_hom_power`）；
//   2. 單價骨架對角化 `F : (C, ⋆) ≃ (Sk(D), ⊙)` 與路徑消去律 `ua(F)^{-1} · ua(F) = refl`
//      （統一 `alge2/functors::fwht_inplace` XOR 捲積對角化、`alge/ga` 有理點求值對角化
//       與 `algo/hott` + `alge3/cubical` CRT 單價傳輸）；
//   3. 張量—Hom 柯里化伴隨 `Hom(U ⊗ V, W) ≃ Hom(U, Hom(V, W))`、Beck–Chevalley 同倫拉回縮並
//      與 *-自治 Chu 對偶 / Danos–Regnier 證明網切換準則
//      （統一 `alge2/vect_top_topos::kronecker_bifunctor_apply`、`algo/linalg::kronecker_product`、
//       `alge2/functors::flat_kan_chain_contraction`、`alge3/homotopy::Span` 與 `alge2/linear_logic`）。
// =============================================================================

///|
/// 餘米田路徑纖維融合流（Coyoneda Path-Fiber Stream，整合 `alge1/functor::Free` 與 `alge2/functors::Coyoneda`）：
/// 基於米田自然雙射 `Nat(Hom(X, -), F) ≃ F(X)`，將任意多次 `map` 合成融合為單一閉包 `X -> A`，
/// 實現零中間陣列分配的函子管線與一步么半群歸約。
pub(all) struct CoyonedaStream[X, A] {
  source : Array[X]
  morphism : (X) -> A
}

///|
pub fn[X] CoyonedaStream::lift(source : Array[X]) -> CoyonedaStream[X, X] {
  CoyonedaStream::{ source, morphism: fn(x : X) { x } }
}

///|
pub fn[X, A, B] CoyonedaStream::map(
  self : CoyonedaStream[X, A],
  f : (A) -> B,
) -> CoyonedaStream[X, B] {
  let prev = self.morphism
  CoyonedaStream::{ source: self.source, morphism: fn(x : X) { f(prev(x)) } }
}

///|
pub fn[X, A] CoyonedaStream::lower(self : CoyonedaStream[X, A]) -> Array[A] {
  let out : Array[A] = []
  let f = self.morphism
  for x in self.source {
    out.push(f(x))
  }
  out
}

///|
pub fn[X, A, M] CoyonedaStream::fold_hom(
  self : CoyonedaStream[X, A],
  unit : M,
  mul : (M, A) -> M,
) -> M {
  let mut acc = unit
  let f = self.morphism
  for x in self.source {
    acc = mul(acc, f(x))
  }
  acc
}

///|
/// 自由—遺忘伴隨泛同態倍增算子（Universal Free–Forgetful Monoid Homomorphism Doubling）：
/// 由伴隨態雙射 `Hom_Mon(Free(Σ), M) ≃ Hom_Set(Σ, U(M))`，字 `w ∈ Free(Σ)` 重複 `repeat_k` 次
/// 在目標么半群 `M`（如模 `modulus` 的仿射自同態 `x ↦ a·x + b`）上的同態像滿足
///   `Φ(w^K) = (Φ(w))^K`，
/// 故只需 1 次 Coyoneda 折疊求 `Φ(w)` 加 `O(log K)` 次二進制倍增（整合 `alge2/functors::free_monoid_hom_power`）。
pub fn free_monoid_affine_hom_power(
  word : Array[Int32],
  gen_a : Array[Int64],
  gen_b : Array[Int64],
  repeat_k : Int64,
  modulus : Int64,
) -> (Int64, Int64) {
  let compose = fn(f1 : (Int64, Int64), f2 : (Int64, Int64)) -> (Int64, Int64) {
    let (a1, b1) = f1
    let (a2, b2) = f2
    (a1 * a2 % modulus, (a1 * b2 + b1) % modulus)
  }
  let stream = CoyonedaStream::lift(word).map(fn(g : Int32) -> (Int64, Int64) {
    (gen_a[g], gen_b[g])
  })
  // 注意右起作用合成順序：先作用前綴再作用後繼
  let mut base = stream.fold_hom((1L, 0L), fn(acc, step) { compose(step, acc) })
  let mut res = (1L, 0L)
  let mut exp = repeat_k
  while exp > 0L {
    if (exp & 1L) == 1L {
      res = compose(base, res)
    }
    base = compose(base, base)
    exp = exp >> 1
  }
  res
}

///|
/// 驗證自由—遺忘伴隨態雙射與單價骨架對角化（Univalent Coordinate-Ring Skeleton Power）：
/// 對半單零成本張量代數 `alg : ZeroCostTensorAlg` 及有理點集 `points`（`|points| == d`）：
///   1. 正向等價 `F = eval` 將代數元 `a ∈ A` 映射至點態對角骨架 `[a(P_0), ..., a(P_{d-1})] ∈ 𝔽_p^d`；
///   2. 在骨架中以 `O(d log exp)` 逐點快速冪計算 `[a(P_r)^exp]`（中間 `exp - 1` 次逆變換由 `ua(F)^{-1}·ua(F) = refl` 消去）；
///   3. 逆向等價 `F^{-1}` 透過拉格朗日正交本原冪等元基 `e^{(r)}` 重組回 `A` 中元素 `∑ a(P_r)^exp · e^{(r)}`；
/// 定理：骨架快速冪結果嚴格等於在 `A` 中直接做 `exp` 次張量乘法 `a^exp`！
pub fn tensor_alg_univalent_skeleton_power(
  alg : ZeroCostTensorAlg,
  points : Array[Array[Int32]],
  a : Array[Int32],
  exp : Int32,
) -> Array[Int32]? {
  match alg.lagrange_primitive_idempotents(points) {
    None => None
    Some(idems) => {
      let d = alg.d
      let mut out = alg.zero()
      for r in 0..<d {
        let val_r = alg.eval_at_point(a, points[r])
        let pow_r = @num.powmod(val_r, exp, alg.p)
        out = alg.add(out, alg.scale(pow_r, idems[r]))
      }
      Some(out)
    }
  }
}

///|
/// Walsh–Hadamard 單價骨架 XOR 捲積鏈（整合 `alge2/functors::fwht_inplace` 與 `lift_to_skeleton`）：
/// 將一組長 `n = 2^k` 的向量透過原地 FWHT 提升至對角譜骨架 `Sk(D)`，
/// 在骨架中執行逐點乘積後僅執行唯一一次逆 FWHT 還原，時間複雜度 `O(m·n log n)` 取代 `O(m·n²)`。
pub fn fwht_univalent_convolution_chain(
  vectors : Array[Array[Int64]],
) -> Array[Int64] {
  if vectors.length() == 0 {
    return []
  }
  let n = vectors[0].length()
  if n == 0 || (n & (n - 1)) != 0 {
    return []
  }
  let fwht = fn(buf : Array[Int64], invert : Bool) -> Unit {
    let mut len = 1
    while len < n {
      let step = len << 1
      let mut i = 0
      while i < n {
        for j in 0..<len {
          let u = buf[i + j]
          let v = buf[i + j + len]
          buf[i + j] = u + v
          buf[i + j + len] = u - v
        }
        i = i + step
      }
      len = step
    }
    if invert {
      let n64 = n.to_int64()
      for i in 0..<n {
        buf[i] = buf[i] / n64
      }
    }
  }
  let acc = vectors[0].copy()
  fwht(acc, false)
  for idx in 1..<vectors.length() {
    let cur = vectors[idx].copy()
    fwht(cur, false)
    for i in 0..<n {
      acc[i] = acc[i] * cur[i]
    }
  }
  fwht(acc, true)
  acc
}

///|
/// 張量—Hom 柯里化伴隨的逐軸 Kronecker 作用算子（Curried Tensor–Hom Kronecker Action）：
/// 基於範疇伴隨態雙射
///   `Hom_{𝔽_p}(V_0 ⊗ V_1 ⊗ ... ⊗ V_{k-1}, W)  ≃  Hom_{𝔽_p}(V_0, Hom(V_1, ..., W))`
/// 對一系列 `@linalg.Matrix` 因子 `[A_0, A_1, ..., A_{k-1}]` 與狀態向量 `state ∈ 𝔽_p^{∏ n_i}`，
/// 不實化龐大的 `∏ n_i × ∏ n_i` Kronecker 矩陣（`algo/linalg::kronecker_product`），
/// 而是逐軸沿張量纖維切片應用 `A_idx`，將複雜度由 `O(N²)` 降至 `O(∑ n_i · N)`
/// （整合 `algo/linalg::kronecker_product` 與 `alge2/vect_top_topos::kronecker_bifunctor_apply`）！
pub fn kronecker_curried_apply_matrices(
  factors : Array[@linalg.Matrix],
  state : Array[Int32],
) -> Array[Int32] {
  if factors.length() == 0 {
    return state.copy()
  }
  let p = factors[0].p
  let total_len = state.length()
  let mut cur = state.copy()
  let mut next = Array::make(total_len, 0)
  let mut stride = 1
  let mut idx = factors.length() - 1
  while idx >= 0 {
    let mat = factors[idx]
    let n = mat.rows
    let block = stride * n
    let mut base = 0
    while base < total_len {
      for offset in 0..<stride {
        for r in 0..<n {
          let mut sum = 0
          for c in 0..<n {
            sum = @num.mod_pos(
              sum + mat.data[r][c] * cur[base + c * stride + offset],
              p,
            )
          }
          next[base + r * stride + offset] = sum
        }
      }
      base = base + block
    }
    let tmp = cur
    cur = next
    next = tmp
    stride = block
    idx = idx - 1
  }
  cur
}

///|
/// 實化兩個 `@linalg.Matrix` 的 Kronecker 張量積矩陣 `A ⊗ B`（供驗證張量—Hom 柯里化分解定理）。
pub fn kronecker_product_matrix(
  a : @linalg.Matrix,
  b : @linalg.Matrix,
) -> @linalg.Matrix {
  let p = a.p
  let r1 = a.rows
  let c1 = a.cols
  let r2 = b.rows
  let c2 = b.cols
  let out = @linalg.Matrix::zero(p, r1 * r2, c1 * c2)
  for i1 in 0..<r1 {
    for j1 in 0..<c1 {
      let aij = a.data[i1][j1]
      for i2 in 0..<r2 {
        for j2 in 0..<c2 {
          out.data[i1 * r2 + i2][j1 * c2 + j2] = @num.mul_mod(
            aij,
            b.data[i2][j2],
            p,
          )
        }
      }
    }
  }
  out
}

///|
/// Beck–Chevalley 同倫拉回與跨距（Span）線性時間縮並算子
/// （整合 `alge2/functors::flat_kan_chain_contraction` 與 `alge3/homotopy::Span`）：
/// 給定三個帶權二元態射族 `R_1, R_2, R_3`（元素為 `(src, dst, weight)`）與頂點上界 `key_bound`，
/// 利用 `Σ–Π` 伴隨分配律先在中間纖維 `b` 與 `c` 上預聚合邊權，在 `O(|R_1| + |R_2| + |R_3| + key_bound)`
/// 線性時間內精確算出三重拉回跡 `∑ w_1(a,b) · w_2(b,c) · w_3(c,d)`！
pub fn beck_chevalley_span_contraction(
  r1 : Array[(Int32, Int32, Int64)],
  r2 : Array[(Int32, Int32, Int64)],
  r3 : Array[(Int32, Int32, Int64)],
  key_bound : Int32,
) -> Int64 {
  let fiber_b = Array::make(key_bound, 0L)
  for e in r1 {
    let (_, dst, w) = e
    fiber_b[dst] = fiber_b[dst] + w
  }
  let fiber_c = Array::make(key_bound, 0L)
  for e in r3 {
    let (src, _, w) = e
    fiber_c[src] = fiber_c[src] + w
  }
  let mut total = 0L
  for e in r2 {
    let (src, dst, w) = e
    total = total + fiber_b[src] * w * fiber_c[dst]
  }
  total
}

///|
/// *-自治 Chu 空間對偶配對與 Danos–Regnier 乘性線性邏輯（MLL）證明網切換樹性判準
/// （整合 `algo/modules/dual.mbt`、`alge1/linear.mbt` 與 `alge2/linear_logic::verify_mll_proof_net`）：
/// 檢驗對所有 `2^{|par_switches|}` 個 `⅋`（Par）開關選擇，由固定邊 `fixed_edges` 與選中前提邊
/// 構成的誘導圖是否恆為無環且連通的生成樹（`|E| == |V| - 1` 且無圈）。
pub fn verify_chu_mll_proof_net(
  num_vertices : Int32,
  fixed_edges : Array[(Int32, Int32)],
  par_switches : Array[(Int32, Int32, Int32)],
) -> Bool {
  let num_pars = par_switches.length()
  if num_vertices <= 0 || fixed_edges.length() + num_pars != num_vertices - 1 {
    return false
  }
  let total_switchings = 1 << num_pars
  let parent = Array::make(num_vertices, 0)
  let find_root = fn(x : Int32) -> Int32 {
    let mut cur = x
    while parent[cur] != cur {
      parent[cur] = parent[parent[cur]]
      cur = parent[cur]
    }
    cur
  }
  for mask in 0..<total_switchings {
    for v in 0..<num_vertices {
      parent[v] = v
    }
    for e in fixed_edges {
      let (u, v) = e
      let ru = find_root(u)
      let rv = find_root(v)
      if ru == rv {
        return false
      }
      parent[ru] = rv
    }
    for p in 0..<num_pars {
      let (concl, l_prem, r_prem) = par_switches[p]
      let target = if ((mask >> p) & 1) == 0 { l_prem } else { r_prem }
      let ru = find_root(concl)
      let rv = find_root(target)
      if ru == rv {
        return false
      }
      parent[ru] = rv
    }
  }
  true
}
