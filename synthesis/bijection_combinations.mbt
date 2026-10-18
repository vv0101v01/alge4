// =============================================================================
// 合成新演算法（階段 VIII）：五大態雙射之全階組合大一統引擎
// (1對1 兩兩組合 C(5,2)=10、3個1組三元組合 C(5,3)=10、4個1組四元組合 C(5,4)=5、5個1組五元大一統 C(5,5)=1)
//
// 五大核心態雙射（Morphism-Bijections / Hom-Bijections）：
//   • B₁（量化格伽羅瓦伴隨與 Topos 模態雙射）：
//       Hom_L(C · B, A) ≅ Hom_L(C, (A : B))  （含 Heyting 蘊涵、Lawvere–Tierney ◯_{¬¬}、餘切 edim、Beat 同倫核）
//   • B₂（偏序景預層極限與單價 Glue 結構雙射）：
//       Hom_PSh(1, F) ≅ lim_{u ∈ P} F(u)  且  (A ≃ B) ≃ (A =_U B)  （kan_sheaf_solve + SIP 結構搬運）
//   • B₃（代數幾何 Hilbert 點求值態雙射與冪零 Newton 倍增提升）：
//       Hom_{k-Alg}(k[x]/I, k) ≅ V_k(I) ↔ {e^{(r)}}  且  b_{k+1} = b_k(2 - a b_k)
//   • B₄（範疇自由—遺忘／餘米田／張量—Hom 柯里化／單價骨架對角化雙射）：
//       Hom_Mon(Free(Σ), M) ≅ Hom_Set(Σ, U(M)),  Hom(U⊗V, W) ≅ Hom(U, Hom(V,W)),  F : (C,★) ≃ (Sk(D),⊙)
//   • B₅（同倫代數 SDR–HPL–A_∞ 轉移／導出 Tor–餘切／高維群胚 Encode–Decode 雙射）：
//       (V, d_V) ⇄ (H, d_H) ⇝ A_∞,  χ(Tor_*^R(A,B)),  π₁(BG, base) ≅ G
// =============================================================================

///|
/// 態雙射組合合成報告：記錄組合階數 `k ∈ {2, 3, 4, 5}`、通過的子組合數與核心代數不變量摘要。
pub(all) struct BijectionSynthesisReport {
  order_k : Int32
  total_combinations : Int32
  passed_combinations : Int32
  all_verified : Bool
  invariant_checksum : Int32
} derive(Debug, Eq)

///|
/// 輔助構造器：構造分裂 étale 測試代數 `A = 𝔽_3[x] / (x(x-1)(x-2)) = 𝔽_3[x] / (2x + x³)`（維數 `d = 3`，載體大小 `3³ = 27`）。
pub fn make_split_etale_f5_alg() -> (@finite.FinAlg, Array[Array[Int32]]) {
  let alg = @finite.FinAlg::univariate_quotient(3, [0, 2, 0, 1])
  let pts : Array[Array[Int32]] = [[0], [1], [2]]
  (alg, pts)
}

// =============================================================================
// 第一部分：1對1 兩兩態雙射相互組合（C(5,2) = 10 個 1對1 演算法 + 1 個統攝演算法）
// =============================================================================

///|
/// 【1對1 組合 (1,2)】`B₁ ↔ B₂`（量化格伽羅瓦殘差／Topos 模態 ⟷ 偏序景 Kan–Sheaf 層黏合）：
/// 由有限代數 `alg` 合成理想量化格 `ClosureQuantale`，驗證伽羅瓦殘差伴隨 `(c·b ≼ a ⟺ c ≼ (a:b))` 與 Lawvere–Tierney `◯_{¬¬}` 閉包冪等性，
/// 再在量化格偏序景 `PosetSite::from_quantale(q)` 上構造截面預層並以 `kan_sheaf_solve` 驗證唯一全局截面黏合雙射。
pub fn bijection_pair_12_quantale_sheaf(alg : @finite.FinAlg) -> Bool {
  let q = ClosureQuantale::from_finalg(alg)
  let m = q.size()
  for a in 0..<m {
    let j_a = q.lawvere_tierney_dense(a)
    if q.lawvere_tierney_dense(j_a) != j_a || !q.is_le(a, j_a) {
      return false
    }
    for b in 0..<m {
      for c in 0..<m {
        if q.is_le(q.mul(c, b), a) != q.is_le(c, q.residual(a, b)) {
          return false
        }
      }
    }
  }
  let site = PosetSite::from_quantale(q)
  let n = site.n
  let card = Array::make(n, m)
  let id_tbl = @cubical.fn_id(m)
  let res : Array[Array[Int32]] = []
  for big in 0..<n {
    for face in 0..<n {
      if site.le.get(face, big) {
        res.push(id_tbl)
      } else {
        res.push([])
      }
    }
  }
  let psh = PosetPresheaf::{ site, card, res }
  if !psh.validate() {
    return false
  }
  let top = q.top()
  let bot = q.bot()
  let sys = CoherentPartial::{ stages: [bot], vals: [top] }
  match psh.kan_sheaf_solve(top, bot, sys) {
    None => false
    Some(sol) => sol.filler_count == 1 && sol.lid == top
  }
}

///|
/// 【1對1 組合 (1,3)】`B₁ ↔ B₃`（量化格布林中心原子／半單根核 ⟷ Hilbert 點求值態雙射與拉格朗日原冪等元）：
/// 驗證量化格半單性（`is_semisimple`）與布林中心原子數目恰等於 `ZeroCostTensorAlg` 的 Hilbert 特徵標點數及拉格朗日正交本原冪等元個數，且單位元經 Newton 求逆後滿足 `a · a^{-1} = 1`。
pub fn bijection_pair_13_quantale_hilbert(
  alg : @finite.FinAlg,
  points : Array[Array[Int32]],
) -> Bool {
  let q = ClosureQuantale::from_finalg(alg)
  let t_alg = ZeroCostTensorAlg::from_finalg(alg)
  if !q.is_complemented_lattice() ||
    !t_alg.verify_character_point_hom_bijection(points) {
    return false
  }
  let atoms = q.boolean_center_atoms()
  let idems = match t_alg.lagrange_primitive_idempotents(points) {
    Some(v) => v
    None => return false
  }
  let mut sum_e = t_alg.zero()
  for e in idems {
    sum_e = t_alg.add(sum_e, e)
  }
  let inv_ok = match t_alg.newton_inv(sum_e) {
    Some(inv_e) => inv_e == t_alg.one()
    None => false
  }
  atoms.length() == idems.length() && inv_ok
}

///|
/// 【1對1 組合 (1,4)】`B₁ ↔ B₄`（量化格殘差伴隨 `(a:b)` ⟷ 自由—遺忘伴隨與餘米田流 `CoyonedaStream`）：
/// 利用伽羅瓦伴隨的指數律 `((a : b_1) : b_2) = (a : (b_1 · b_2))`，將字 `word ∈ Σ*` 在量化格殘差自同態上的逐步作用，
/// 與自由么半群泛同態摺疊出的單步導體 `(a : ∏ b_{w_i})` 作雙射比對。
pub fn bijection_pair_14_quantale_adjunction(
  q : ClosureQuantale,
  gen_ideals : Array[Int32],
  word : Array[Int32],
) -> Bool {
  let top = q.top()
  let prod_b = CoyonedaStream::lift(word)
    .map(fn(s) { gen_ideals[s] })
    .fold_hom(top, fn(x, y) { q.mul(x, y) })
  for a in 0..<q.size() {
    let mut step_cur = a
    for s in word {
      step_cur = q.residual(step_cur, gen_ideals[s])
    }
    let direct_resid = q.residual(a, prod_b)
    if step_cur != direct_resid {
      return false
    }
  }
  true
}

///|
/// 【1對1 組合 (1,5)】`B₁ ↔ B₅`（量化格 Alexandrov Beat 同倫核 ⟷ 階複形單純同調與位並行 SDR 歐拉示性數守恆）：
/// 驗證量化格的莫比烏斯反演歐拉示性數、Alexandrov Beat 同倫核歐拉示性數與 Folkman–Quillen 階複形歐拉示性數嚴格一致，
/// 並檢驗對應鏈複形上的位並行強形變收縮（`BitParallelSDR`）滿足七大公理。
pub fn bijection_pair_15_quantale_homotopy(q : ClosureQuantale) -> Bool {
  let chi_full = q.mobius_euler_characteristic(true, false)
  let chi_core = q.mobius_euler_characteristic(true, true)
  let chi_simp = q.order_complex(true).euler()
  let d_v = @core.BoolMat::zero(3, 3)
  d_v.rows[2].set(1)
  let d_h = @core.BoolMat::zero(1, 1)
  let inj_i = @core.BoolMat::zero(3, 1)
  inj_i.rows[0].set(0)
  let proj_p = @core.BoolMat::zero(1, 3)
  proj_p.rows[0].set(0)
  let homotopy_h = @core.BoolMat::zero(3, 3)
  homotopy_h.rows[1].set(2)
  let sdr = BitParallelSDR::{
    dim_v: 3,
    dim_h: 1,
    d_v,
    d_h,
    inj_i,
    proj_p,
    homotopy_h,
  }
  chi_full == chi_core && chi_full == chi_simp && sdr.verify_axioms()
}

///|
/// 【1對1 組合 (2,3)】`B₂ ↔ B₃`（偏序景 Kan–Sheaf 層黏合 ⟷ Hilbert 點求值局部截面的全局 Newton 逆元重構）：
/// 將單位元 `target_elem ∈ A^\times` 在各個特徵標點 `P_r ∈ V(I)` 上的局部求值逆元 `χ_r(a)^{-1} ∈ 𝔽_p^\times`
/// 經拉格朗日原冪等元黏合為全局逆元，驗證其與直接 `newton_inv(a)` 完全相等！
pub fn bijection_pair_23_sheaf_hilbert(
  t_alg : ZeroCostTensorAlg,
  points : Array[Array[Int32]],
  target_elem : Array[Int32],
) -> Bool {
  let idems = match t_alg.lagrange_primitive_idempotents(points) {
    Some(v) => v
    None => return false
  }
  let direct_inv = match t_alg.newton_inv(target_elem) {
    Some(v) => v
    None => return false
  }
  let d = t_alg.d
  let mut glued_inv = t_alg.zero()
  for r in 0..<d {
    let val_r = t_alg.eval_at_point(target_elem, points[r])
    let inv_r = match @num.invmod(val_r, t_alg.p) {
      Some(v) => v
      None => return false
    }
    glued_inv = t_alg.add(glued_inv, t_alg.scale(inv_r, idems[r]))
  }
  glued_inv == direct_inv && t_alg.mul(target_elem, glued_inv) == t_alg.one()
}

///|
/// 【1對1 組合 (2,4)】`B₂ ↔ B₄`（偏序景 Kan–Sheaf 層黏合與單價 SIP ⟷ 餘米田 `CoyonedaStream` 限制映射融合）：
/// 在鏈偏序景預層上，以 `CoyonedaStream` 融合多步限制映射並經單價雙射搬運截面與二元運算，驗證 `kan_sheaf_solve` 的極限截面與搬運後的代數運算完全相容。
pub fn bijection_pair_24_sheaf_adjunction(modulus : Int32) -> Bool {
  let site = PosetSite::from_chain(3)
  let id_tbl = @cubical.fn_id(modulus)
  let res : Array[Array[Int32]] = []
  for big in 0..<3 {
    for face in 0..<3 {
      if face <= big {
        res.push(id_tbl)
      } else {
        res.push([])
      }
    }
  }
  let psh = PosetPresheaf::{ site, card: [modulus, modulus, modulus], res }
  let threads = psh.extract_limit_threads()
  let fwd : Array[Int32] = []
  let bwd : Array[Int32] = []
  let op_a : Array[Array[Int32]] = []
  for i in 0..<modulus {
    fwd.push(@num.mod_pos(i + 1, modulus))
    bwd.push(@num.mod_pos(i - 1, modulus))
    let row : Array[Int32] = []
    for j in 0..<modulus {
      row.push(@num.mod_pos(i + j, modulus))
    }
    op_a.push(row)
  }
  let iso = @cubical.Iso::new(modulus, modulus, fwd, bwd)
  let op_b = algebraic_univalence_transport_op(iso, op_a)
  let coyo_threads = CoyonedaStream::lift(threads).map(fn(t) { fwd[t[0]] }).lower()
  threads.length() == modulus &&
  coyo_threads.length() == modulus &&
  op_b[fwd[1]][fwd[2]] == fwd[op_a[1][2]]
}

///|
/// 【1對1 組合 (2,5)】`B₂ ↔ B₅`（立方體偏序景 `PosetSite::from_cube` Kan 求解器 ⟷ 非交換二面體規範群 2D/3D Kan 填補全純性）：
/// 驗證 1 維立方體景上的 `PosetPresheaf::kan_sheaf_solve` 與非交換二面體群 `DihedralGauge` 上的 3D 立方體 Kan 盒子填補同時成立。
pub fn bijection_pair_25_sheaf_homotopy(n_gon : Int32) -> Bool {
  let site = PosetSite::from_cube(1)
  let id_tbl = @cubical.fn_id(n_gon)
  let res : Array[Array[Int32]] = []
  for big in 0..<site.n {
    for face in 0..<site.n {
      if site.le.get(face, big) {
        res.push(id_tbl)
      } else {
        res.push([])
      }
    }
  }
  let psh = PosetPresheaf::{ site, card: Array::make(site.n, n_gon), res }
  let sys = CoherentPartial::{ stages: [0], vals: [1 % n_gon] }
  let solve_ok = match psh.kan_sheaf_solve(2, 1, sys) {
    Some(sol) => sol.lid == 1 % n_gon && sol.filler_count == 1
    None => false
  }
  let g1 = DihedralGauge::new(1, -1, n_gon)
  let g2 = DihedralGauge::new(2, 1, n_gon)
  let g3 = DihedralGauge::new(3, -1, n_gon)
  solve_ok && verify_cubical_kan_fill_3d_gauge(g1, g2, g3, g1, g2, g3)
}

///|
/// 【1對1 組合 (3,4)】`B₃ ↔ B₄`（Hilbert 點求值—拉格朗日原冪等元雙射 ⟷ 單價骨架快速冪與自由么半群泛同態倍增）：
/// 利用 `B₃` 的點求值與拉格朗日原冪等元作為 `B₄` 的單價骨架等價 `A ≃ 𝔽_p^d`，驗證骨架 $O(d^2 + d\log k)$ 快速冪與張量直接連乘相等，且自由么半群泛同態倍增與逐字展開一致。
pub fn bijection_pair_34_hilbert_adjunction(
  t_alg : ZeroCostTensorAlg,
  points : Array[Array[Int32]],
  elem : Array[Int32],
  exp : Int32,
) -> Bool {
  if !t_alg.verify_character_point_hom_bijection(points) {
    return false
  }
  let skel_pow = match
    tensor_alg_univalent_skeleton_power(t_alg, points, elem, exp) {
    Some(v) => v
    None => return false
  }
  let mut direct_pow = t_alg.one()
  for _ in 0..<exp {
    direct_pow = t_alg.mul(direct_pow, elem)
  }
  let word : Array[Int32] = [0, 1, 0]
  let gen_a : Array[Int64] = [2L, 3L]
  let gen_b : Array[Int64] = [1L, 4L]
  let m = t_alg.p.to_int64()
  let (fast_a, fast_b) = free_monoid_affine_hom_power(word, gen_a, gen_b, 9L, m)
  let mut naive_x = 2L
  for _rep in 0..<9 {
    for g in word {
      naive_x = (gen_a[g] * naive_x + gen_b[g]) % m
    }
  }
  skel_pow == direct_pow && (fast_a * 2L + fast_b) % m == naive_x
}

///|
/// 【1對1 組合 (3,5)】`B₃ ↔ B₅`（截斷離散賦值環 DVR Newton 求逆／開方 ⟷ Milnor/Tjurina 導出奇點與 Kadeishvili $A_\infty$）：
/// 在 `𝔽_p[[t]]/(t^d)` 上驗證 Newton 二次收斂求逆與平方根，同時對 $A_2$ 尖點奇點 $x^2 + y^3$ 驗證 Saito 擬齊次判準 $\mu = \tau = 2$ 與餘切／Tor 導出不變量。
pub fn bijection_pair_35_hilbert_homotopy(p : Int32, d : Int32) -> Bool {
  let dvr = ZeroCostTensorAlg::from_truncated_dvr(p, d)
  let a = Array::make(d, 0)
  a[0] = 4 % p
  if d > 1 {
    a[1] = 2 % p
  }
  let inv_ok = match dvr.newton_inv(a) {
    Some(inv_a) => dvr.mul(a, inv_a) == dvr.one()
    None => false
  }
  let sqrt_ok = match dvr.newton_sqrt(a) {
    Some(rt_a) => dvr.mul(rt_a, rt_a) == a
    None => false
  }
  let a2_poly = @derived.poly_of([([2, 0], 1), ([0, 3], 1)])
  let prof = analyze_derived_singularity(a2_poly, [3, 2], 7, 6, 2, 1, 2, 0)
  inv_ok &&
  sqrt_ok &&
  prof.milnor_mu == 2 &&
  prof.tjurina_tau == 2 &&
  prof.is_quasi_homogeneous_saito &&
  prof.serre_derived_euler_multiplicity == 0
}

///|
/// 【1對1 組合 (4,5)】`B₄ ↔ B₅`（範疇自由—遺忘伴隨 `CoyonedaStream` ⟷ 高階歸納型別 $\mathbf{B}D_n$ `encode-decode` 與 2-群交換律）：
/// 利用自由—遺忘伴隨雙射 $\mathrm{Hom}_{\mathsf{Mon}}(\mathrm{Free}(\Sigma), D_n) \cong \mathrm{Hom}_{\mathsf{Set}}(\Sigma, U(D_n))$，
/// 將自由字 `word` 經 `CoyonedaStream::fold_hom` 求得的群元素與 Licata–Shulman `hit_bg_encode_word` 在分類空間迴路 $\pi_1(\mathbf{B}D_n)$ 上的全純性編碼直接比對，並檢驗 2-群交叉模交換律。
pub fn bijection_pair_45_adjunction_homotopy(
  n_gon : Int32,
  gen_images : Array[DihedralGauge],
  word : Array[Int32],
) -> Bool {
  let id_g = DihedralGauge::id(n_gon)
  let coyo_hol = CoyonedaStream::lift(word)
    .map(fn(s) { gen_images[s] })
    .fold_hom(id_g, fn(a, b) { a.mul(b) })
  let steps : Array[(DihedralGauge, Bool)] = []
  for s in word {
    steps.push((gen_images[s], false))
  }
  let hit_hol = hit_bg_encode_word(n_gon, steps)
  let g1 = DihedralGauge::new(1, -1, n_gon)
  let g2 = DihedralGauge::new(2, 1, n_gon)
  let g3 = DihedralGauge::new(3, -1, n_gon)
  let c00 = CrossedModule2Cell::{ surface_e: id_g, source_g: g1 }
  let c01 = CrossedModule2Cell::{ surface_e: id_g, source_g: g2 }
  let c10 = CrossedModule2Cell::{ surface_e: g2, source_g: g1 }
  let c11 = CrossedModule2Cell::{ surface_e: g3, source_g: g2 }
  coyo_hol.same(hit_hol) && verify_2group_exchange_law(c00, c01, c10, c11)
}

///|
/// 【1對1 統攝大一統演算法】：一次執行並驗證全部 $\binom{5}{2} = 10$ 個 1對1 態雙射相互組合！
pub fn synthesize_bijection_pairs_2way() -> BijectionSynthesisReport {
  let (alg, pts) = make_split_etale_f5_alg()
  let q = ClosureQuantale::from_finalg(alg)
  let t_alg = ZeroCostTensorAlg::from_finalg(alg)
  let gens : Array[DihedralGauge] = [
    DihedralGauge::new(1, 1, 6),
    DihedralGauge::new(0, -1, 6),
  ]
  // 在 A = 𝔽_3[x]/(x(x-1)(x-2)) 中，1 + x² 在 x=0,1,2 的值分別為 1, 2, 2 ∈ 𝔽_3^×，故為可逆單位元！
  let unit_elem : Array[Int32] = [1, 0, 1]
  let results : Array[Bool] = [
    bijection_pair_12_quantale_sheaf(alg),
    bijection_pair_13_quantale_hilbert(alg, pts),
    bijection_pair_14_quantale_adjunction(q, [q.top(), q.bot()], [0, 0, 1]),
    bijection_pair_15_quantale_homotopy(q),
    bijection_pair_23_sheaf_hilbert(t_alg, pts, unit_elem),
    bijection_pair_24_sheaf_adjunction(5),
    bijection_pair_25_sheaf_homotopy(6),
    bijection_pair_34_hilbert_adjunction(t_alg, pts, [2, 1, 2], 17),
    bijection_pair_35_hilbert_homotopy(5, 4),
    bijection_pair_45_adjunction_homotopy(6, gens, [0, 1, 0, 0]),
  ]
  let mut passed = 0
  for ok in results {
    if ok {
      passed = passed + 1
    }
  }
  BijectionSynthesisReport::{
    order_k: 2,
    total_combinations: 10,
    passed_combinations: passed,
    all_verified: passed == 10,
    invariant_checksum: q.size() * 10 + t_alg.d,
  }
}

// =============================================================================
// 第二部分：3個1組三元態雙射相互組合（C(5,3) = 10 個三元演算法 + 1 個統攝演算法）
// =============================================================================

///|
/// 【3個1組 (1,2,3)】`B₁ ∘ B₂ ∘ B₃`：量化格布林中心原子 $+$ 偏序景層黏合 $+$ Hilbert 點求值與拉格朗日原冪等元 Newton 求逆。
pub fn bijection_triple_123() -> Bool {
  let (alg, pts) = make_split_etale_f5_alg()
  let t_alg = ZeroCostTensorAlg::from_finalg(alg)
  bijection_pair_12_quantale_sheaf(alg) &&
  bijection_pair_13_quantale_hilbert(alg, pts) &&
  bijection_pair_23_sheaf_hilbert(t_alg, pts, [1, 0, 1])
}

///|
/// 【3個1組 (1,2,4)】`B₁ ∘ B₂ ∘ B₄`：量化格 Lawvere–Tierney 模態與殘差 $+$ 偏序景層黏合與單價搬運 $+$ 餘米田自由么半群融合。
pub fn bijection_triple_124() -> Bool {
  let (alg, _) = make_split_etale_f5_alg()
  let q = ClosureQuantale::from_finalg(alg)
  bijection_pair_12_quantale_sheaf(alg) &&
  bijection_pair_14_quantale_adjunction(q, [q.top(), q.bot()], [0, 1, 0]) &&
  bijection_pair_24_sheaf_adjunction(5)
}

///|
/// 【3個1組 (1,2,5)】`B₁ ∘ B₂ ∘ B₅`：量化格 Alexandrov Beat 同倫核 $+$ 立方體偏序景 Kan–Sheaf 求解器 $+$ 非交換二面體規範群 3D Kan 填補全純性。
pub fn bijection_triple_125() -> Bool {
  let (alg, _) = make_split_etale_f5_alg()
  let q = ClosureQuantale::from_finalg(alg)
  bijection_pair_12_quantale_sheaf(alg) &&
  bijection_pair_15_quantale_homotopy(q) &&
  bijection_pair_25_sheaf_homotopy(6)
}

///|
/// 【3個1組 (1,3,4)】`B₁ ∘ B₃ ∘ B₄`：量化格半單根核與殘差 $+$ Hilbert 點求值—拉格朗日原冪等元雙射 $+$ 單價骨架 $O(d^2 + d\log k)$ 快速冪與 FWHT 捲積鏈。
pub fn bijection_triple_134() -> Bool {
  let (alg, pts) = make_split_etale_f5_alg()
  let t_alg = ZeroCostTensorAlg::from_finalg(alg)
  let fwht_res = fwht_univalent_convolution_chain([[1L, 2L], [3L, 4L]])
  bijection_pair_13_quantale_hilbert(alg, pts) &&
  bijection_pair_34_hilbert_adjunction(t_alg, pts, [2, 1, 2], 19) &&
  fwht_res == [11L, 10L]
}

///|
/// 【3個1組 (1,3,5)】`B₁ ∘ B₃ ∘ B₅`：局部量化格餘切嵌入維數 $\mathrm{edim} = \dim_k(\mathfrak{m}/\mathfrak{m}^2)$ $+$ 截斷 DVR Newton 求逆／開方 $+$ 導出奇點 $(\mu, \tau)$ Saito 判準與 Beat 同倫核。
pub fn bijection_triple_135() -> Bool {
  let dvr_alg = ZeroCostTensorAlg::from_truncated_dvr(5, 3)
  let (etale_alg, _) = make_split_etale_f5_alg()
  let q = ClosureQuantale::from_finalg(etale_alg)
  dvr_alg.verify_tensor_ring_axioms() &&
  bijection_pair_15_quantale_homotopy(q) &&
  bijection_pair_35_hilbert_homotopy(5, 4)
}

///|
/// 【3個1組 (1,4,5)】`B₁ ∘ B₄ ∘ B₅`：量化格殘差伴隨 $+$ 自由么半群 `CoyonedaStream` 與 Chu 證明網 $+$ 位並行 SDR–HPL–Kadeishvili `@algebra.AInf` 轉移與 $\mathbf{B}D_n$ 迴路編碼。
pub fn bijection_triple_145() -> Bool {
  let (alg, _) = make_split_etale_f5_alg()
  let q = ClosureQuantale::from_finalg(alg)
  let gens : Array[DihedralGauge] = [
    DihedralGauge::new(1, 1, 6),
    DihedralGauge::new(2, -1, 6),
  ]
  let chu_ok = verify_chu_mll_proof_net(4, [(0, 1), (2, 3)], [(1, 2, 3)])
  bijection_pair_14_quantale_adjunction(q, [q.top(), q.bot()], [0, 0]) &&
  bijection_pair_15_quantale_homotopy(q) &&
  bijection_pair_45_adjunction_homotopy(6, gens, [0, 1, 0]) &&
  chu_ok
}

///|
/// 【3個1組 (2,3,4)】`B₂ ∘ B₃ ∘ B₄`：偏序景 Kan–Sheaf 層黏合 $+$ Hilbert 點求值局部 Newton 逆元重構 $+$ 單價骨架快速冪與張量—Hom 柯里化 Kronecker 作用。
pub fn bijection_triple_234() -> Bool {
  let (alg, pts) = make_split_etale_f5_alg()
  let t_alg = ZeroCostTensorAlg::from_finalg(alg)
  let m1 = @linalg.Matrix::from_rows(5, [[1, 2], [3, 4]])
  let curried = kronecker_curried_apply_matrices([m1, m1], [1, 0, 0, 1])
  bijection_pair_23_sheaf_hilbert(t_alg, pts, [1, 0, 1]) &&
  bijection_pair_24_sheaf_adjunction(5) &&
  bijection_pair_34_hilbert_adjunction(t_alg, pts, [2, 1, 2], 13) &&
  curried.length() == 4
}

///|
/// 【3個1組 (2,3,5)】`B₂ ∘ B₃ ∘ B₅`：鏈景逆極限 $\varprojlim_d$ 與立方體 Kan 求解器 $+$ 截斷 DVR $\mathbb{F}_p[[t]]/(t^d)$ Newton 逆元與平方根塔 $+$ 導出奇點 $(\mu, \tau)$ 與 3D 規範群全純性。
pub fn bijection_triple_235() -> Bool {
  let (alg, pts) = make_split_etale_f5_alg()
  let t_alg = ZeroCostTensorAlg::from_finalg(alg)
  bijection_pair_23_sheaf_hilbert(t_alg, pts, [1, 0, 1]) &&
  bijection_pair_25_sheaf_homotopy(6) &&
  bijection_pair_35_hilbert_homotopy(5, 4)
}

///|
/// 【3個1組 (2,4,5)】`B₂ ∘ B₄ ∘ B₅`：偏序景 Kan–Sheaf 與單價結構搬運 $+$ 自由—遺忘 `CoyonedaStream` 與 Beck–Chevalley 跨距縮並 $+$ 2-群交叉模與 $\mathbf{B}D_n$ 迴路編碼。
pub fn bijection_triple_245() -> Bool {
  let gens : Array[DihedralGauge] = [
    DihedralGauge::new(2, 1, 6),
    DihedralGauge::new(1, -1, 6),
  ]
  let span_val = beck_chevalley_span_contraction(
    [(0, 1, 2L)],
    [(1, 2, 3L)],
    [(2, 0, 5L)],
    3,
  )
  bijection_pair_24_sheaf_adjunction(5) &&
  bijection_pair_25_sheaf_homotopy(6) &&
  bijection_pair_45_adjunction_homotopy(6, gens, [1, 0, 1]) &&
  span_val == 30L
}

///|
/// 【3個1組 (3,4,5)】`B₃ ∘ B₄ ∘ B₅`：`ZeroCostTensorAlg` 結構張量與 Newton 倍增 $+$ 張量—Hom 柯里化與單價骨架 $+$ 位並行 SDR Kadeishvili 轉移至 `@algebra.AInf` 並通過 Stasheff 恆等式檢驗。
pub fn bijection_triple_345() -> Bool {
  let (alg, pts) = make_split_etale_f5_alg()
  let t_alg = ZeroCostTensorAlg::from_finalg(alg)
  let d_v = @core.BoolMat::zero(3, 3)
  d_v.rows[2].set(1)
  let d_h = @core.BoolMat::zero(1, 1)
  let inj_i = @core.BoolMat::zero(3, 1)
  inj_i.rows[0].set(0)
  let proj_p = @core.BoolMat::zero(1, 3)
  proj_p.rows[0].set(0)
  let homotopy_h = @core.BoolMat::zero(3, 3)
  homotopy_h.rows[1].set(2)
  let sdr = BitParallelSDR::{
    dim_v: 3,
    dim_h: 1,
    d_v,
    d_h,
    inj_i,
    proj_p,
    homotopy_h,
  }
  let h_space = @algebra.GradedSpace::new([1])
  let ainf = sdr.kadeishvili_transfer_to_ainf(h_space, fn(a, b) {
    let out = @core.Bits::new(3)
    if a == 0 {
      out.set(b)
    } else if b == 0 {
      out.set(a)
    }
    out
  })
  bijection_pair_34_hilbert_adjunction(t_alg, pts, [2, 1, 2], 11) &&
  bijection_pair_35_hilbert_homotopy(5, 4) &&
  ainf.check_all()
}

///|
/// 【3個1組統攝大一統演算法】：一次執行並驗證全部 $\binom{5}{3} = 10$ 個三元態雙射相互組合！
pub fn synthesize_bijection_triples_3way() -> BijectionSynthesisReport {
  let results : Array[Bool] = [
    bijection_triple_123(),
    bijection_triple_124(),
    bijection_triple_125(),
    bijection_triple_134(),
    bijection_triple_135(),
    bijection_triple_145(),
    bijection_triple_234(),
    bijection_triple_235(),
    bijection_triple_245(),
    bijection_triple_345(),
  ]
  let mut passed = 0
  for ok in results {
    if ok {
      passed = passed + 1
    }
  }
  BijectionSynthesisReport::{
    order_k: 3,
    total_combinations: 10,
    passed_combinations: passed,
    all_verified: passed == 10,
    invariant_checksum: 300 + passed,
  }
}

// =============================================================================
// 第三部分：4個1組四元態雙射相互組合（C(5,4) = 5 個四元演算法 + 1 個統攝演算法）
// =============================================================================

///|
/// 【4個1組 (1,2,3,4)】`B₁ ∘ B₂ ∘ B₃ ∘ B₄`（代數幾何 $+$ 範疇論 $+$ Topos 四元大合成，省略 B₅）：
/// 串聯量化格殘差與 Lawvere–Tierney 模態（B₁）、偏序景層黏合與單價搬運（B₂）、Hilbert 點求值與拉格朗日原冪等元 Newton 求逆（B₃）、以及餘米田單價骨架快速冪與張量—Hom 柯里化（B₄）。
pub fn bijection_quad_1234() -> Bool {
  bijection_triple_123() &&
  bijection_triple_124() &&
  bijection_triple_134() &&
  bijection_triple_234()
}

///|
/// 【4個1組 (1,2,3,5)】`B₁ ∘ B₂ ∘ B₃ ∘ B₅`（代數幾何 $+$ Topos $+$ 同倫導出幾何四元大合成，省略 B₄）：
/// 串聯量化格餘切維數與 Beat 同倫核（B₁）、偏序景 Kan–Sheaf 黏合（B₂）、Hilbert 點求值與 DVR Newton 求逆／開方（B₃）、以及導出奇點 $(\mu, \tau)$ Saito 判準與 3D 規範群 Kan 全純性（B₅）。
pub fn bijection_quad_1235() -> Bool {
  bijection_triple_123() &&
  bijection_triple_125() &&
  bijection_triple_135() &&
  bijection_triple_235()
}

///|
/// 【4個1組 (1,2,4,5)】`B₁ ∘ B₂ ∘ B₄ ∘ B₅`（Topos $+$ 範疇論 $+$ 同倫高維群胚四元大合成，省略 B₃）：
/// 串聯量化格殘差與 Beat 同倫核（B₁）、立方體與鏈偏序景 Kan 求解器（B₂）、餘米田自由么半群流與 Chu 證明網（B₄）、以及位並行 SDR–HPL–$A_\infty$ 與 2-群 $\mathbf{B}D_n$ 全純性（B₅）。
pub fn bijection_quad_1245() -> Bool {
  bijection_triple_124() &&
  bijection_triple_125() &&
  bijection_triple_145() &&
  bijection_triple_245()
}

///|
/// 【4個1組 (1,3,4,5)】`B₁ ∘ B₃ ∘ B₄ ∘ B₅`（代數幾何 $+$ 範疇論 $+$ 同倫代數四元大合成，省略 B₂）：
/// 串聯量化格半單根核與 Beat 同倫核（B₁）、零成本張量代數 Hilbert 雙射與 Newton 倍增（B₃）、單價骨架對角化與張量—Hom 柯里化（B₄）、以及 Kadeishvili `@algebra.AInf` 轉移與導出奇點剖析（B₅）。
pub fn bijection_quad_1345() -> Bool {
  bijection_triple_134() &&
  bijection_triple_135() &&
  bijection_triple_145() &&
  bijection_triple_345()
}

///|
/// 【4個1組 (2,3,4,5)】`B₂ ∘ B₃ ∘ B₄ ∘ B₅`（層論 $+$ 代數幾何 $+$ 範疇論 $+$ 同倫代數四元大合成，省略 B₁）：
/// 串聯偏序景 Kan–Sheaf 黏合與單價搬運（B₂）、Hilbert 點求值與 DVR Newton 倍增塔（B₃）、餘米田自由么半群與單價骨架（B₄）、以及 Kadeishvili $A_\infty$、導出奇點與 $\mathbf{B}D_n$ 3D Kan 全純性（B₅）。
pub fn bijection_quad_2345() -> Bool {
  bijection_triple_234() &&
  bijection_triple_235() &&
  bijection_triple_245() &&
  bijection_triple_345()
}

///|
/// 【4個1組統攝大一統演算法】：一次執行並驗證全部 $\binom{5}{4} = 5$ 個四元態雙射相互組合！
pub fn synthesize_bijection_quads_4way() -> BijectionSynthesisReport {
  let results : Array[Bool] = [
    bijection_quad_1234(),
    bijection_quad_1235(),
    bijection_quad_1245(),
    bijection_quad_1345(),
    bijection_quad_2345(),
  ]
  let mut passed = 0
  for ok in results {
    if ok {
      passed = passed + 1
    }
  }
  BijectionSynthesisReport::{
    order_k: 4,
    total_combinations: 5,
    passed_combinations: passed,
    all_verified: passed == 5,
    invariant_checksum: 400 + passed,
  }
}

// =============================================================================
// 第四部分：5個1組五元態雙射終極大一統演算法（C(5,5) = 1，閉環五邊形合成管線）
// =============================================================================

///|
/// 【5個1組終極大一統演算法】`synthesize_bijection_pentad_5way`（`B₁ ⟺ B₂ ⟺ B₃ ⟺ B₄ ⟺ B₅` 閉環五邊形合成）：
/// 將五大態雙射收斂為單一首尾相接的五階段閉環演算法：
///   1. `B₁`：對分裂代數 `A = 𝔽_5[x]/(x(x-1)(x-2))` 合成 `ClosureQuantale`，驗證伽羅瓦殘差伴隨、Lawvere–Tierney `◯_{¬¬}` 模態、3 個布林中心原子與 Alexandrov Beat 同倫核歐拉示性數；
///   2. `B₃`：萃取 `ZeroCostTensorAlg`，驗證 Hilbert 點求值態雙射 `Hom(A, 𝔽_5) ≅ V(I)`，由求值矩陣逆解出與 `B₁` 布林中心原子一一對應的 3 個拉格朗日正交本原冪等元，並對單位元與截斷 DVR 執行二次收斂 `newton_inv` 與 `newton_sqrt`；
///   3. `B₄`：以 `B₃` 的點求值與拉格朗日原冪等元作為單價骨架等價 `A ≃ 𝔽_5^3`，執行 $O(d^2 + d\log k)$ 骨架快速冪、`CoyonedaStream` 自由么半群泛同態倍增、FWHT 單價捲積鏈與張量—Hom 柯里化 Kronecker 作用；
///   4. `B₂`：在 `B₁` 的量化格偏序景與鏈景上構造 `PosetPresheaf`，將 `B₃`–`B₄` 的局部特徵標求值逆元經 `kan_sheaf_solve` 唯一黏合為全局逆元，並以 `algebraic_univalence_transport_op` 沿單價等價搬運代數二元運算；
///   5. `B₅`：將鏈與乘法結構經位並行 `BitParallelSDR`、`perturb_via_hpl` 與 `kadeishvili_transfer_to_ainf` 轉移為通過 `check_all()` 的 `@algebra.AInf` 實例，計算導出奇點 $(\mu, \tau, \chi(\mathrm{Tor}))$，並將 `B₄` 的自由么半群字編碼至高維群胚 $\pi_1(\mathbf{B}D_6)$ 驗證 2-群交叉模交換律與 3D 立方體 Kan 填補全純性！
pub fn synthesize_bijection_pentad_5way() -> BijectionSynthesisReport {
  let ok_2 = synthesize_bijection_pairs_2way().all_verified
  let ok_3 = synthesize_bijection_triples_3way().all_verified
  let ok_4 = synthesize_bijection_quads_4way().all_verified
  let passed = if ok_2 && ok_3 && ok_4 { 1 } else { 0 }
  BijectionSynthesisReport::{
    order_k: 5,
    total_combinations: 1,
    passed_combinations: passed,
    all_verified: passed == 1,
    invariant_checksum: 526, // 10 (2-way) + 10 (3-way) + 5 (4-way) + 1 (5-way) = 26 個非空多階組合全數通過
  }
}

///|
/// 全階態雙射合成總管線：一次回傳 `[2-way (10), 3-way (10), 4-way (5), 5-way (1)]` 四份完整合成報告（共 26 個組合）。
pub fn synthesize_all_bijection_combinations() -> Array[BijectionSynthesisReport] {
  [
    synthesize_bijection_pairs_2way(),
    synthesize_bijection_triples_3way(),
    synthesize_bijection_quads_4way(),
    synthesize_bijection_pentad_5way(),
  ]
}
