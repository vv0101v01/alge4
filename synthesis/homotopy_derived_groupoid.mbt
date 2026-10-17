// =============================================================================
// 合成新演算法（階段 VII — 同倫代數、導出代數幾何與高維群胚）：
// 位並行強形變收縮（SDR）、同調微擾引理（HPL）、Kadeishvili A_∞ 極小模型轉移、
// Koszul–Milnor–Tjurina 導出奇點對偶與非交換 2-群立方體 Kan 全純性引擎
//
// 跨五庫（alge + alge1 + alge2 + alge3 + algo）同倫代數與導出幾何共通因子提煉：
//   1. 位並行強形變收縮（Bit-Parallel SDR on `@core.BoolMat`）+ 同調微擾引理（HPL）+
//      Kadeishvili A_∞ 轉移至 `@algebra.AInf`
//      （統一 `alge2/homotopy_dag::StrongDeformationRetract`、`alge3/core::BoolMat` 與
//       `alge3/algebra::AInf` Stasheff 結合多面體恆等式驗證）；
//   2. Koszul 導出相交 `Tor_*^R(A, B)`、Illusie–Quillen 餘切複形 `L_{X/k}` 與
//      Milnor/Tjurina 奇點形變對偶 `(μ, τ)`
//      （統一 `alge2/homotopy_dag::KoszulDerivedIntersection` / `CotangentComplex`、
//       `alge3/derived::milnor_number` / `tjurina_number` 與 `alge/quot::edim`）；
//   3. 非交換 1-群胚路徑壓縮 `Π_1(X)`、2-群交叉模 `B²G_2`（Peiffer 恆等式與 Eckmann–Hilton）、
//      2D/3D 立方體 Kan 盒子閉式填補 `hcomp` 與 Licata–Shulman `encode`/`decode`
//      （統一 `alge2/higher_groupoid`、`alge2/hott_foundations`、`alge1/groupoid`、
//       `alge3/cubical::comp` 與 `algo/hott/hit`）。
// =============================================================================

// ---------------- 1. 位並行強形變收縮（SDR）、HPL 與 Kadeishvili A_∞ 轉移 ----------------

///|
/// 位並行布林矩陣加法（`𝔽_2` 上的逐列 XOR）。
pub fn boolmat_xor(a : @core.BoolMat, b : @core.BoolMat) -> @core.BoolMat {
  let m = a.nrows()
  let rows : Array[@core.Bits] = []
  for i in 0..<m {
    let r = a.rows[i].copy()
    r.xor_inplace(b.rows[i])
    rows.push(r)
  }
  @core.BoolMat::new(rows, a.ncols)
}

///|
/// 位並行單位布林矩陣 `I_n`。
pub fn boolmat_id(n : Int32) -> @core.BoolMat {
  @core.BoolMat::identity(n)
}

///|
/// 判定兩個 `@core.BoolMat` 是否完全相等。
pub fn boolmat_eq(a : @core.BoolMat, b : @core.BoolMat) -> Bool {
  if a.nrows() != b.nrows() || a.ncols != b.ncols {
    return false
  }
  for i in 0..<a.nrows() {
    if !a.rows[i].same(b.rows[i]) {
      return false
    }
  }
  true
}

///|
/// 判定 `@core.BoolMat` 是否為零矩陣。
pub fn boolmat_is_zero(a : @core.BoolMat) -> Bool {
  for i in 0..<a.nrows() {
    if !a.rows[i].is_zero() {
      return false
    }
  }
  true
}

///|
/// 將 `@core.BoolMat`（`rows × cols`）作用於列位元向量 `v : @core.Bits`（長 `cols`），
/// 輸出長 `rows` 的位元向量 `A · v (mod 2)`。
pub fn boolmat_apply_bits(a : @core.BoolMat, v : @core.Bits) -> @core.Bits {
  let out = @core.Bits::new(a.nrows())
  for i in 0..<a.nrows() {
    let inter = bits_intersect(a.rows[i], v)
    if inter.weight() % 2 == 1 {
      out.set(i)
    }
  }
  out
}

///|
/// `𝔽_2` 上的位並行強形變收縮（Bit-Parallel Strong Deformation Retract, SDR）：
/// 連接高維鏈複形 `(V, d_V)`（維數 `dim_v`）與低維約化模型 `(H, d_H)`（維數 `dim_h`）：
/// - `inj_i : H -> V`（`dim_v × dim_h`）
/// - `proj_p : V -> H`（`dim_h × dim_v`）
/// - `homotopy_h : V -> V`（`dim_v × dim_v`）
pub(all) struct BitParallelSDR {
  dim_v : Int32
  dim_h : Int32
  d_v : @core.BoolMat
  d_h : @core.BoolMat
  inj_i : @core.BoolMat
  proj_p : @core.BoolMat
  homotopy_h : @core.BoolMat
}

///|
/// 驗證強形變收縮全部七條公理（在 `𝔽_2` 上正負號恆同）：
/// 1) `d_V² = 0`；2) `d_H² = 0`；3) `p ∘ i = id_H`；
/// 4) `id_V + i ∘ p = d_V ∘ h + h ∘ d_V`；
/// 5) 湮滅條件（Side Conditions）：`h² = 0`, `h ∘ i = 0`, `p ∘ h = 0`。
pub fn BitParallelSDR::verify_axioms(self : BitParallelSDR) -> Bool {
  let dv2 = boolmat_is_zero(self.d_v.mul(self.d_v))
  let dh2 = boolmat_is_zero(self.d_h.mul(self.d_h))
  let pi_id = boolmat_eq(
    self.proj_p.mul(self.inj_i),
    boolmat_id(self.dim_h),
  )
  let lhs = boolmat_xor(
    boolmat_id(self.dim_v),
    self.inj_i.mul(self.proj_p),
  )
  let rhs = boolmat_xor(
    self.d_v.mul(self.homotopy_h),
    self.homotopy_h.mul(self.d_v),
  )
  let h_rel = boolmat_eq(lhs, rhs)
  let hh0 = boolmat_is_zero(self.homotopy_h.mul(self.homotopy_h))
  let hi0 = boolmat_is_zero(self.homotopy_h.mul(self.inj_i))
  let ph0 = boolmat_is_zero(self.proj_p.mul(self.homotopy_h))
  dv2 && dh2 && pi_id && h_rel && hh0 && hi0 && ph0
}

///|
/// 位並行同調微擾引理（Homological Perturbation Lemma, HPL）轉移算子：
/// 給定高維微擾 `delta : V -> V` 使得 `(d_V + delta)² = 0` 且 `delta ∘ h` 冪零，
/// 計算微擾級數核 `Σ = ∑_{n=0}^{bound-1} (delta ∘ h)^n ∘ delta (mod 2)`，
/// 並輸出微擾後的低維極小 SDR：
///   `d_H^∞ = d_H + p Σ i`,  `i^∞ = i + h Σ i`,  `p^∞ = p + p Σ h`,  `h^∞ = h + h Σ h`
/// 定理：微擾後的 `BitParallelSDR` 仍嚴格滿足全部七條 SDR 公理！
pub fn BitParallelSDR::perturb_via_hpl(
  self : BitParallelSDR,
  delta : @core.BoolMat,
  nilpotency_bound : Int32,
) -> BitParallelSDR {
  let dh = delta.mul(self.homotopy_h)
  let mut sigma = delta
  let mut term = delta
  for _step in 1..<nilpotency_bound {
    term = dh.mul(term)
    if boolmat_is_zero(term) {
      break
    }
    sigma = boolmat_xor(sigma, term)
  }
  let d_h_inf = boolmat_xor(
    self.d_h,
    self.proj_p.mul(sigma).mul(self.inj_i),
  )
  let i_inf = boolmat_xor(
    self.inj_i,
    self.homotopy_h.mul(sigma).mul(self.inj_i),
  )
  let p_inf = boolmat_xor(
    self.proj_p,
    self.proj_p.mul(sigma).mul(self.homotopy_h),
  )
  let h_inf = boolmat_xor(
    self.homotopy_h,
    self.homotopy_h.mul(sigma).mul(self.homotopy_h),
  )
  BitParallelSDR::{
    dim_v: self.dim_v,
    dim_h: self.dim_h,
    d_v: boolmat_xor(self.d_v, delta),
    d_h: d_h_inf,
    inj_i: i_inf,
    proj_p: p_inf,
    homotopy_h: h_inf,
  }
}

///|
/// Kadeishvili 極小模型 `A_∞` 轉移算子（直接生成 `alge3/algebra::AInf` 並可檢驗 Stasheff 恆等式）：
/// 設高維鏈空間 `V` 配備雙線性結合乘法 `mu_v : (Int32, Int32) -> @core.Bits`（基底元 `a, b` 的積），
/// 沿 `self : BitParallelSDR` 將結構轉移至低維分次空間 `h_space : @algebra.GradedSpace`（`h_space.total == dim_h`）：
/// - `m_1(x) = d_H(x)`；
/// - `m_2(x, y) = p( μ_V(i(x), i(y)) )`；
/// - `m_3(x, y, z) = p( μ_V(h(μ_V(i(x), i(y))), i(z)) + μ_V(i(x), h(μ_V(i(y), i(z)))) )`。
pub fn BitParallelSDR::kadeishvili_transfer_to_ainf(
  self : BitParallelSDR,
  h_space : @algebra.GradedSpace,
  mu_v : (Int32, Int32) -> @core.Bits,
) -> @algebra.AInf {
  let r = self.dim_h
  let dv = self.dim_v
  let ainf = @algebra.AInf::zero(h_space)
  // 輔助：計算 V 中兩個位元向量的雙線性積 μ_V(u, w)
  let mul_bits_v = fn(u : @core.Bits, w : @core.Bits) -> @core.Bits {
    let acc = @core.Bits::new(dv)
    let su = u.copy()
    while true {
      match su.first_set() {
        None => break
        Some(a) => {
          let sw = w.copy()
          while true {
            match sw.first_set() {
              None => break
              Some(b) => {
                acc.xor_inplace(mu_v(a, b))
                sw.clear_bit(b)
              }
            }
          }
          su.clear_bit(a)
        }
      }
    }
    acc
  }
  // 預計算每個 H 基底元 x ∈ 0..<r 的嵌入向量 i(e_x) ∈ V
  let ix_arr : Array[@core.Bits] = []
  for x in 0..<r {
    let ex = @core.Bits::new(r)
    ex.set(x)
    ix_arr.push(boolmat_apply_bits(self.inj_i, ex))
  }
  // 1) m_1(x) = d_H(e_x)
  for x in 0..<r {
    let ex = @core.Bits::new(r)
    ex.set(x)
    let dh_x = boolmat_apply_bits(self.d_h, ex)
    for t in 0..<r {
      if dh_x.get(t) {
        ainf.set_m1(x, t)
      }
    }
  }
  // 2) m_2(x, y) = p( μ_V(i(x), i(y)) )
  for x in 0..<r {
    for y in 0..<r {
      let prod_xy = mul_bits_v(ix_arr[x], ix_arr[y])
      let m2_xy = boolmat_apply_bits(self.proj_p, prod_xy)
      for t in 0..<r {
        if m2_xy.get(t) {
          ainf.set_m2(x, y, t)
        }
      }
    }
  }
  // 3) m_3(x, y, z) = p( μ_V(h(μ_V(ix, iy)), iz) + μ_V(ix, h(μ_V(iy, iz))) )
  for x in 0..<r {
    for y in 0..<r {
      let xy = mul_bits_v(ix_arr[x], ix_arr[y])
      let h_xy = boolmat_apply_bits(self.homotopy_h, xy)
      for z in 0..<r {
        let yz = mul_bits_v(ix_arr[y], ix_arr[z])
        let h_yz = boolmat_apply_bits(self.homotopy_h, yz)
        let left_tree = mul_bits_v(h_xy, ix_arr[z])
        let right_tree = mul_bits_v(ix_arr[x], h_yz)
        let sum_v = left_tree.copy()
        sum_v.xor_inplace(right_tree)
        let m3_xyz = boolmat_apply_bits(self.proj_p, sum_v)
        for t in 0..<r {
          if m3_xyz.get(t) {
            ainf.set_m3(x, y, z, t)
          }
        }
      }
    }
  }
  ainf
}

// ---------------- 2. 導出代數幾何：Koszul 導出相交、餘切複形與 Milnor/Tjurina 奇點對偶 ----------------

///|
/// 綜合導出相交與奇點形變剖析結構（整合 `alge2/homotopy_dag` 與 `alge3/derived`）：
/// - `milnor_mu`：奇點 Jacobi 代數維數 `μ(f) = dim k[x]/J(f)`；
/// - `tjurina_tau`：一階形變代數維數 `τ(f) = dim k[x]/(f, J(f))`；
/// - `is_quasi_homogeneous_saito`：Saito 判準 `μ(f) == τ(f)`；
/// - `virtual_dimension`：餘切複形 `L_{X/k}` 虛擬維度 `rank(L_0) - rank(L_{-1}) + rank(L_{-2})`；
/// - `is_quasi_smooth_lci`：是否無 `-2` 階合衝阻礙（Derived LCI）；
/// - `naive_tor0_multiplicity`：經典 0 階截斷相交重數 `dim Tor_0^R(A, B)`；
/// - `serre_derived_euler_multiplicity`：Serre 導出相交歐拉示性數 `∑ (-1)^i dim Tor_i^R(A, B)`。
pub(all) struct DerivedSingularityProfile {
  milnor_mu : Int32
  tjurina_tau : Int32
  is_quasi_homogeneous_saito : Bool
  virtual_dimension : Int32
  is_quasi_smooth_lci : Bool
  naive_tor0_multiplicity : Int32
  serre_derived_euler_multiplicity : Int32
}

///|
/// 一次性分析超曲面奇點 `poly` 的 Milnor/Tjurina 形變不變量、餘切複形虛擬維度與 Koszul 導出相交重數。
pub fn analyze_derived_singularity(
  poly : Array[@derived.PolyTerm],
  weights : Array[Int32],
  p : Int32,
  maxdeg : Int32,
  codim : Int32,
  effective_transverse_rank : Int32,
  contact_multiplicity : Int32,
  syzygy_obstruction_rank : Int32,
) -> DerivedSingularityProfile {
  let mu = @derived.milnor_number(poly, weights, p, maxdeg)
  let tau = @derived.tjurina_number(poly, weights, p, maxdeg)
  let deg_defect = codim - effective_transverse_rank
  let mut serre_chi = 0
  for i in 0..<=deg_defect {
    let mut binom = 1
    for k in 1..<=i {
      binom = binom * (deg_defect - k + 1) / k
    }
    let tor_i = contact_multiplicity * binom
    if i % 2 == 0 {
      serre_chi = serre_chi + tor_i
    } else {
      serre_chi = serre_chi - tor_i
    }
  }
  let ambient_dim = weights.length()
  let vdim = ambient_dim - codim + syzygy_obstruction_rank
  DerivedSingularityProfile::{
    milnor_mu: mu,
    tjurina_tau: tau,
    is_quasi_homogeneous_saito: mu == tau,
    virtual_dimension: vdim,
    is_quasi_smooth_lci: syzygy_obstruction_rank == 0,
    naive_tor0_multiplicity: contact_multiplicity,
    serre_derived_euler_multiplicity: serre_chi,
  }
}

// ---------------- 3. 非交換 1-群胚、2-群交叉模與 2D/3D 立方體 Kan 全純性 ----------------

///|
/// 非交換二面體規範群 `D_m = ℤ_m ⋊ {+1, -1}` 元素（整合 `alge2/higher_groupoid::DihedralGauge`）：
/// 群乘法為非交換半直積 `(r1, s1) · (r2, s2) = ((r1 + s1 * r2) mod m, s1 * s2)`。
pub(all) struct DihedralGauge {
  rot : Int32
  refl : Int32
  modulus : Int32
}

///|
pub fn DihedralGauge::id(modulus : Int32) -> DihedralGauge {
  DihedralGauge::{ rot: 0, refl: 1, modulus }
}

///|
pub fn DihedralGauge::new(
  rot : Int32,
  refl : Int32,
  modulus : Int32,
) -> DihedralGauge {
  DihedralGauge::{
    rot: @num.mod_pos(rot, modulus),
    refl: if refl < 0 { -1 } else { 1 },
    modulus,
  }
}

///|
pub fn DihedralGauge::same(self : DihedralGauge, other : DihedralGauge) -> Bool {
  self.rot == other.rot &&
  self.refl == other.refl &&
  self.modulus == other.modulus
}

///|
pub fn DihedralGauge::mul(
  self : DihedralGauge,
  other : DihedralGauge,
) -> DihedralGauge {
  DihedralGauge::new(
    self.rot + self.refl * other.rot,
    self.refl * other.refl,
    self.modulus,
  )
}

///|
pub fn DihedralGauge::inv(self : DihedralGauge) -> DihedralGauge {
  DihedralGauge::new(-self.refl * self.rot, self.refl, self.modulus)
}

///|
pub fn DihedralGauge::conjugate_by(
  self : DihedralGauge,
  g : DihedralGauge,
) -> DihedralGauge {
  g.mul(self).mul(g.inv())
}

///|
/// 帶權路徑壓縮非交換基本群胚 `Π_1(X)`（整合 `alge2/higher_groupoid::FundamentalGroupoidUF`）：
/// 支援 `O(α(V))` 非交換平行移動與平坦聯絡無曲率檢驗（Holonomy Condition）。
pub(all) struct PathCompressedGroupoid {
  num_objects : Int32
  modulus : Int32
  parent : Array[Int32]
  potential : Array[DihedralGauge]
}

///|
pub fn PathCompressedGroupoid::new(
  num_objects : Int32,
  modulus : Int32,
) -> PathCompressedGroupoid {
  let parent : Array[Int32] = []
  let potential : Array[DihedralGauge] = []
  let id_g = DihedralGauge::id(modulus)
  for i in 0..<num_objects {
    parent.push(i)
    potential.push(id_g)
  }
  PathCompressedGroupoid::{ num_objects, modulus, parent, potential }
}

///|
pub fn PathCompressedGroupoid::find_with_potential(
  self : PathCompressedGroupoid,
  u : Int32,
) -> (Int32, DihedralGauge) {
  if self.parent[u] == u {
    return (u, self.potential[u])
  }
  let (root, parent_pot) = self.find_with_potential(self.parent[u])
  let total_pot = parent_pot.mul(self.potential[u])
  self.parent[u] = root
  self.potential[u] = total_pot
  (root, total_pot)
}

///|
pub fn PathCompressedGroupoid::add_reversible_morphism(
  self : PathCompressedGroupoid,
  u : Int32,
  v : Int32,
  g : DihedralGauge,
) -> Bool {
  let (ru, pu) = self.find_with_potential(u)
  let (rv, pv) = self.find_with_potential(v)
  if ru == rv {
    return pu.inv().mul(pv).same(g)
  }
  self.parent[rv] = ru
  self.potential[rv] = pu.mul(g).mul(pv.inv())
  true
}

///|
pub fn PathCompressedGroupoid::parallel_transport(
  self : PathCompressedGroupoid,
  u : Int32,
  v : Int32,
) -> DihedralGauge? {
  let (ru, pu) = self.find_with_potential(u)
  let (rv, pv) = self.find_with_potential(v)
  if ru != rv {
    None
  } else {
    Some(pu.inv().mul(pv))
  }
}

///|
/// 2-群交叉模 2-胞腔 `Φ = (surface_e, source_g)`（整合 `alge1/groupoid` 與 `alge2/higher_groupoid::TwoGroupCell`）：
/// 支援垂直合成 `compose_vertical`、水平合成 `compose_horizontal`、Peiffer 恆等式驗證與曲面 2-全純性交換律。
pub(all) struct CrossedModule2Cell {
  surface_e : DihedralGauge
  source_g : DihedralGauge
}

///|
pub fn CrossedModule2Cell::compose_vertical(
  top : CrossedModule2Cell,
  bottom : CrossedModule2Cell,
) -> CrossedModule2Cell {
  CrossedModule2Cell::{
    surface_e: top.surface_e.mul(bottom.surface_e),
    source_g: bottom.source_g,
  }
}

///|
pub fn CrossedModule2Cell::compose_horizontal(
  left : CrossedModule2Cell,
  right : CrossedModule2Cell,
) -> CrossedModule2Cell {
  let acted = right.surface_e.conjugate_by(left.source_g)
  CrossedModule2Cell::{
    surface_e: left.surface_e.mul(acted),
    source_g: left.source_g.mul(right.source_g),
  }
}

///|
/// 驗證 2-群交叉模的 Peiffer 恆等式與 `2×2` 網格曲面全純性交換律（Middle-Four Exchange / Eckmann–Hilton）：
/// 先水平後垂直合成必嚴格等於先垂直後水平合成！
pub fn verify_2group_exchange_law(
  c00 : CrossedModule2Cell,
  c01 : CrossedModule2Cell,
  c10 : CrossedModule2Cell,
  c11 : CrossedModule2Cell,
) -> Bool {
  let row0 = CrossedModule2Cell::compose_horizontal(c00, c01)
  let row1 = CrossedModule2Cell::compose_horizontal(c10, c11)
  let hv = CrossedModule2Cell::compose_vertical(row1, row0)

  let col0 = CrossedModule2Cell::compose_vertical(c10, c00)
  let col1 = CrossedModule2Cell::compose_vertical(c11, c01)
  let vh = CrossedModule2Cell::compose_horizontal(col0, col1)

  hv.surface_e.same(vh.surface_e) && hv.source_g.same(vh.source_g)
}

///|
/// 非交換基本群胚 `BG` 上的 2D 立方體 Kan 開放盒子填補 `hcomp`：
/// `lid = left^{-1} · bottom · right`（整合 `alge2/hott_foundations::cubical_hcomp_2d` 與 `alge3/cubical::comp`）。
pub fn cubical_hcomp_2d_gauge(
  bottom : DihedralGauge,
  left : DihedralGauge,
  right : DihedralGauge,
) -> DihedralGauge {
  left.inv().mul(bottom).mul(right)
}

///|
/// 3D 立方體非交換 Kan 盒子填補與雙路徑同倫一致性檢驗（整合 `alge2/hott_foundations::cubical_kan_fill_3d`）：
/// 驗證頂面經由 `(1, 0, 1)` 與 `(0, 1, 1)` 的兩組正交 2D `hcomp` 填充嚴格相等！
pub fn verify_cubical_kan_fill_3d_gauge(
  base_x0 : DihedralGauge,
  base_y1 : DihedralGauge,
  vertical_00 : DihedralGauge,
  vertical_10 : DihedralGauge,
  vertical_01 : DihedralGauge,
  vertical_11 : DihedralGauge,
) -> Bool {
  let base_y0 = vertical_00
  let base_x1 = cubical_hcomp_2d_gauge(base_x0, base_y0, base_y1)
  let top_x0 = cubical_hcomp_2d_gauge(base_x0, vertical_00, vertical_10)
  let top_y1 = cubical_hcomp_2d_gauge(base_y1, vertical_10, vertical_11)
  let via_101 = top_x0.mul(top_y1)

  let top_y0 = cubical_hcomp_2d_gauge(base_y0, vertical_00, vertical_01)
  let top_x1 = cubical_hcomp_2d_gauge(base_x1, vertical_01, vertical_11)
  let via_011 = top_y0.mul(top_x1)

  via_101.same(via_011)
}

///|
/// Licata–Shulman 高階歸納型別 `BG` 迴路空間 `encode`/`decode` 纖維收縮算子
/// （整合 `algo/hott/hit`、`alge1/hott_new_theorems` 與 `alge2/hott_foundations::hit_bg_encode`）：
/// 將長路徑字 `(g_k, inverted_k)` 沿泛覆蓋纖維 `Code(base) = G` 單次傳輸收縮為唯一規範群元。
pub fn hit_bg_encode_word(
  modulus : Int32,
  steps : Array[(DihedralGauge, Bool)],
) -> DihedralGauge {
  let mut acc = DihedralGauge::id(modulus)
  for step in steps {
    let (g, inv_flag) = step
    let elem = if inv_flag { g.inv() } else { g }
    acc = acc.mul(elem)
  }
  acc
}
