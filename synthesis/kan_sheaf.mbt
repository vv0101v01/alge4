// =============================================================================
// 合成新演算法（階段 III & IV）：有限偏序格預層上的 Kan–層填充與 Glue 單價引擎
// (Unified Poset Presheaf, Kan–Sheaf Gluing & Algebraic Univalence Engine)
//
// 抽象代數與格論共通因子提煉：
//   將以下三組看似位於不同領域的演算法收斂為同一個偏序集預層 Kan 求解器：
//     1. algo/scheme/scheme.mbt：Zariski 開集覆蓋上的結構層限制與 Stacks Project 黏合雙射公理
//     2. algo/modules/continuous.mbt：逆向系統 InvSystem 的相容線程極限 limit_threads
//     3. alge3/cubical/{cubety,comp,univalence}.mbt：立方體預層 CubeTy、PartialElem、
//        Glue 扭轉類型、Kan 填補合成 comp/transp_line 與單價定理 ua/idtoeqv
// =============================================================================

///|
/// 有限偏序集／格景（Finite Poset / Lattice Site）`P = {0, ..., n-1}`：
/// - `le`：`le.get(tau, sigma)` 為真當且僅當 `tau ≼ sigma`（`tau` 是 `sigma` 的子階段／子開集／子面）；
/// - `meet`：`meet[a][b]` 為 `a ∧ b` 在 `P` 中的索引；若不交則為 `-1`。
pub(all) struct PosetSite {
  n : Int32
  le : @core.BoolMat
  meet : Array[Array[Int32]]
}

///|
/// 景構造器 1：由 `ClosureQuantale` 格直接生成 `PosetSite`（每個元素即格中一個閉集／開集／理想）。
pub fn PosetSite::from_quantale(q : ClosureQuantale) -> PosetSite {
  PosetSite::{ n: q.size(), le: q.le_mat, meet: q.meet_table }
}

///|
/// 景構造器 2：由 `alge3/cubical` 的 `dim`-維立方體面偏序集 `{0,1,*}^dim` 生成 `PosetSite`（共 `3^dim` 個階段）。
pub fn PosetSite::from_cube(dim : Int32) -> PosetSite {
  let total = @cubical.pow3(dim)
  let le_rows : Array[@core.Bits] = []
  let meet : Array[Array[Int32]] = []
  for a in 0..<total {
    let r = @core.Bits::new(total)
    let mrow : Array[Int32] = []
    for b in 0..<total {
      if @cubical.is_subface(a, b, dim) {
        r.set(b)
      }
      mrow.push(@cubical.meet_cube(a, b, dim))
    }
    le_rows.push(r)
    meet.push(mrow)
  }
  PosetSite::{ n: total, le: @core.BoolMat::new(le_rows, total), meet }
}

///|
/// 景構造器 3：由線性鏈 `0 ≺ 1 ≺ ... ≺ len-1` 生成 `PosetSite`（對應 `algo/modules` 的 `InvSystem`）。
pub fn PosetSite::from_chain(len : Int32) -> PosetSite {
  let le_rows : Array[@core.Bits] = []
  let meet : Array[Array[Int32]] = []
  for i in 0..<len {
    let r = @core.Bits::new(len)
    let mrow : Array[Int32] = []
    for j in 0..<len {
      if i <= j {
        r.set(j)
      }
      mrow.push(if i < j { i } else { j })
    }
    le_rows.push(r)
    meet.push(mrow)
  }
  PosetSite::{ n: len, le: @core.BoolMat::new(le_rows, len), meet }
}

///|
/// 偏序景 `P` 上的有限集預層（Finite Set Presheaf）`F : P^op -> FinSet`：
/// - `card[sigma]`：階段 `sigma` 上的截面集合大小 `|F(sigma)|`（元素編碼為 `0 ..< card[sigma]`）；
/// - `res[sigma * n + tau]`：當 `tau ≼ sigma` 時的限制映射表 `F(sigma) -> F(tau)`。
pub(all) struct PosetPresheaf {
  site : PosetSite
  card : Array[Int32]
  res : Array[Array[Int32]]
}

///|
/// 讀取限制映射表 `res_{big -> face}`。
pub fn PosetPresheaf::res_fn(
  self : PosetPresheaf,
  big : Int32,
  face : Int32,
) -> Array[Int32] {
  self.res[big * self.site.n + face]
}

///|
/// 將階段 `big` 上的截面 `x` 限制到子階段 `face ≼ big`。
pub fn PosetPresheaf::restrict(
  self : PosetPresheaf,
  big : Int32,
  face : Int32,
  x : Int32,
) -> Int32 {
  self.res_fn(big, face)[x]
}

///|
/// 預層公理驗證器（Identity + Functoriality）：
/// 對所有 `s` 檢查 `res_{s->s} = id`，對所有 `face ≼ mid ≼ big` 檢查
/// `res_{mid->face}(res_{big->mid}(x)) == res_{big->face}(x)`。
pub fn PosetPresheaf::validate(self : PosetPresheaf) -> Bool {
  let n = self.site.n
  for s in 0..<n {
    if self.card[s] < 0 ||
      !@cubical.fn_eq(self.res_fn(s, s), @cubical.fn_id(self.card[s])) {
      return false
    }
  }
  for big in 0..<n {
    for mid in 0..<n {
      if self.site.le.get(mid, big) {
        for face in 0..<n {
          if self.site.le.get(face, mid) {
            for x in 0..<self.card[big] {
              let y = self.restrict(big, mid, x)
              if y < 0 || y >= self.card[mid] {
                return false
              }
              if self.restrict(mid, face, y) != self.restrict(big, face, x) {
                return false
              }
            }
          }
        }
      }
    }
  }
  true
}

///|
/// 預層轉換器 1：將 `alge3/cubical` 的 `CubeTy` 無損轉為通用 `PosetPresheaf`。
pub fn PosetPresheaf::from_cubety(ct : @cubical.CubeTy) -> PosetPresheaf {
  let site = PosetSite::from_cube(ct.n)
  let total = site.n
  let card : Array[Int32] = []
  let res : Array[Array[Int32]] = []
  for s in 0..<total {
    card.push(ct.card[s])
  }
  for big in 0..<total {
    for face in 0..<total {
      if site.le.get(face, big) {
        res.push(ct.res_fn(big, face))
      } else {
        res.push([])
      }
    }
  }
  PosetPresheaf::{ site, card, res }
}

///|
/// 將立方體景上的 `PosetPresheaf` 轉回 `@cubical.CubeTy`。
pub fn PosetPresheaf::to_cubety(
  self : PosetPresheaf,
  dim : Int32,
) -> @cubical.CubeTy {
  let card : Array[Int32] = []
  let res : Array[Array[Int32]] = []
  for x in self.card {
    card.push(x)
  }
  for r in self.res {
    res.push(r)
  }
  @cubical.CubeTy::new(dim, card, res)
}

///|
/// 預層轉換器 2：將 `algo/modules` 的逆向系統 `InvSystem` 轉為鏈景上的 `PosetPresheaf`。
/// 對 `i <= j`，限制映射 `res_{j -> i}` 由鍵映射 `bonds[i] ∘ ... ∘ bonds[j-1]` 複合而成。
pub fn PosetPresheaf::from_inv_system(inv : @modules.InvSystem) -> PosetPresheaf {
  if !inv.validate() {
    abort("PosetPresheaf::from_inv_system: invalid InvSystem")
  }
  let n = inv.sizes.length()
  let site = PosetSite::from_chain(n)
  let card : Array[Int32] = []
  for s in inv.sizes {
    card.push(s)
  }
  let res : Array[Array[Int32]] = []
  for big in 0..<n {
    for face in 0..<n {
      if face <= big {
        let mut cur_fn = @cubical.fn_id(card[big])
        let mut step = big - 1
        while step >= face {
          cur_fn = @cubical.fn_comp(cur_fn, inv.bonds[step])
          step = step - 1
        }
        res.push(cur_fn)
      } else {
        res.push([])
      }
    }
  }
  PosetPresheaf::{ site, card, res }
}

///|
/// 預層轉換器 3：將 `algo/scheme` 在二元開覆蓋 `D(h) = D(hf) ∪ D(hg)` 上的局部化結構層
/// 轉為 4 元菱形格景 `{0: D(h²fg), 1: D(hf), 2: D(hg), 3: D(h)}` 上的 `PosetPresheaf`。
pub fn PosetPresheaf::from_zariski_cover(
  alg : @finite.FinAlg,
  h : Array[Int32],
  f : Array[Int32],
  g : Array[Int32],
) -> PosetPresheaf? {
  if !@scheme.covers_basic(alg, h, f, g) {
    return None
  }
  let hf = alg.mul_elem(h, f)
  let hg = alg.mul_elem(h, g)
  let hfg = alg.mul_elem(alg.mul_elem(hf, g), h) // h²fg
  let res_3_1 = match @scheme.restriction(alg, h, hf) {
    Some(t) => t
    None => return None
  }
  let res_3_2 = match @scheme.restriction(alg, h, hg) {
    Some(t) => t
    None => return None
  }
  let res_1_0 = match @scheme.restriction(alg, hf, hfg) {
    Some(t) => t
    None => return None
  }
  let res_2_0 = match @scheme.restriction(alg, hg, hfg) {
    Some(t) => t
    None => return None
  }
  let res_3_0 = @cubical.fn_comp(res_3_1, res_1_0)
  let loc_0 = alg.localize_at_element(hfg).size()
  let loc_1 = alg.localize_at_element(hf).size()
  let loc_2 = alg.localize_at_element(hg).size()
  let loc_3 = alg.localize_at_element(h).size()
  let card : Array[Int32] = [loc_0, loc_1, loc_2, loc_3]
  // 菱形偏序：0 ≼ 1, 2 ≼ 3
  let r0 = @core.Bits::new(4)
  r0.set(0)
  r0.set(1)
  r0.set(2)
  r0.set(3)
  let r1 = @core.Bits::new(4)
  r1.set(1)
  r1.set(3)
  let r2 = @core.Bits::new(4)
  r2.set(2)
  r2.set(3)
  let r3 = @core.Bits::new(4)
  r3.set(3)
  let le = @core.BoolMat::new([r0, r1, r2, r3], 4)
  let meet : Array[Array[Int32]] = [
    [0, 0, 0, 0],
    [0, 1, 0, 1],
    [0, 0, 2, 2],
    [0, 1, 2, 3],
  ]
  let site = PosetSite::{ n: 4, le, meet }
  let res : Array[Array[Int32]] = [
    // big = 0
    @cubical.fn_id(loc_0),
    [],
    [],
    [],
    // big = 1
    res_1_0,
    @cubical.fn_id(loc_1),
    [],
    [],
    // big = 2
    res_2_0,
    [],
    @cubical.fn_id(loc_2),
    [],
    // big = 3
    res_3_0,
    res_3_1,
    res_3_2,
    @cubical.fn_id(loc_3),
  ]
  Some(PosetPresheaf::{ site, card, res })
}

// ---------------- 核心算子 3：統一 Kan–層相容填充與黏合演算法 ----------------

///|
/// 偏序景上的部分截面系統（Partial Section / Open Box / Cover Family）：
/// 在階段 `stages[k]` 上指定截面值 `vals[k] ∈ [0, card[stages[k]])`。
pub(all) struct CoherentPartial {
  stages : Array[Int32]
  vals : Array[Int32]
}

///|
/// 相容性判定（Sheaf Overlap Agreement ≡ Cubical Tube Compatibility）：
/// 對所有 `(i, j)`，若兩階段在偏序景中存在交 `m = meet[stages[i]][stages[j]] >= 0`，
/// 則兩截面限制到 `m` 的值必須相等：`res_{s_i -> m}(v_i) == res_{s_j -> m}(v_j)`。
pub fn PosetPresheaf::check_coherent(
  self : PosetPresheaf,
  sys : CoherentPartial,
) -> Bool {
  if sys.stages.length() != sys.vals.length() {
    return false
  }
  let k = sys.stages.length()
  for i in 0..<k {
    let s = sys.stages[i]
    if s < 0 || s >= self.site.n || sys.vals[i] < 0 || sys.vals[i] >= self.card[s] {
      return false
    }
  }
  for i in 0..<k {
    for j in (i + 1)..<k {
      let m = self.site.meet[sys.stages[i]][sys.stages[j]]
      if m >= 0 {
        if self.restrict(sys.stages[i], m, sys.vals[i]) !=
          self.restrict(sys.stages[j], m, sys.vals[j]) {
          return false
        }
      }
    }
  }
  true
}

///|
/// 統一 Kan–層求解結果：
/// - `lid`：首個填補截面在目標面 `lid_stage` 上的投影值（即 `comp` 或 `transp` 的輸出）；
/// - `filler`：首個全局填補截面 `x ∈ F(top_stage)`；
/// - `filler_count`：符合全部邊界／覆蓋條件的全局截面總數（層黏合公理要求恆為 `1`）；
/// - `unique_lid`：所有填補截面投影到 `lid_stage` 的值是否唯一；
/// - `all_fillers`：全體符合條件的全局截面列表。
pub(all) struct KanSheafResult {
  lid : Int32
  filler : Int32
  filler_count : Int32
  unique_lid : Bool
  all_fillers : Array[Int32]
}

///|
/// 核心合成演算法：`kan_sheaf_solve`。
/// 給定目標階段 `top_stage`、輸出讀取階段 `lid_stage ≼ top_stage` 與部分截面系統 `sys`：
///   1. 驗證所有 `sys.stages[k] ≼ top_stage` 且 `sys` 滿足交集相容性 `check_coherent`；
///   2. 掃描 `cand ∈ 0 ..< card[top_stage]`，篩選滿足 `∀k, res_{top -> s_k}(cand) == v_k` 的全體全局截面；
///   3. 將每個全局截面投影至 `lid_stage` 並記錄唯一性。
///
/// 三合一特化定理：
///   - 當 `self = from_cubety(X)`、`top_stage = generic_cube(n)`、`lid_stage = face_cube(n, dir, 1)`、
///     `sys = tube ∪ {(face_cube(n, dir, 0), cap)}` 時，此函數即 `alge3/cubical::comp`！
///   - 當 `self = from_zariski_cover(R, h, f, g)`、`top_stage = lid_stage = 3`、`sys = {1: u, 2: v}` 時，
///     `filler_count == 1` 對所有相容對 `(u, v)` 成立即 `algo/scheme::sheaf_gluing_bijective`！
///   - 當 `self = from_inv_system(inv)`、`top_stage = n-1`、`sys = ∅` 時，每個 `cand ∈ all_fillers`
///     向各階段 `t` 的限制 `[res_{n-1 -> n-1}(cand), ..., res_{n-1 -> 0}(cand)]` 即 `InvSystem::limit_threads`！
pub fn PosetPresheaf::kan_sheaf_solve(
  self : PosetPresheaf,
  top_stage : Int32,
  lid_stage : Int32,
  sys : CoherentPartial,
) -> KanSheafResult? {
  if !self.site.le.get(lid_stage, top_stage) {
    return None
  }
  for s in sys.stages {
    if !self.site.le.get(s, top_stage) {
      return None
    }
  }
  if !self.check_coherent(sys) {
    return None
  }
  let all_fillers : Array[Int32] = []
  let mut chosen_filler = -1
  let mut lid0 = -1
  let mut unique_lid = true
  for cand in 0..<self.card[top_stage] {
    let mut ok = true
    for k in 0..<sys.stages.length() {
      if self.restrict(top_stage, sys.stages[k], cand) != sys.vals[k] {
        ok = false
        break
      }
    }
    if ok {
      all_fillers.push(cand)
      let lid_val = self.restrict(top_stage, lid_stage, cand)
      if chosen_filler < 0 {
        chosen_filler = cand
        lid0 = lid_val
      } else if lid_val != lid0 {
        unique_lid = false
      }
    }
  }
  if chosen_filler < 0 {
    None
  } else {
    Some(KanSheafResult::{
      lid: lid0,
      filler: chosen_filler,
      filler_count: all_fillers.length(),
      unique_lid,
      all_fillers,
    })
  }
}

///|
/// 以 `kan_sheaf_solve` 判定二元覆蓋 `{c1, c2}` 對 `top_stage` 是否滿足層黏合公理（Sheaf Gluing Axiom）：
/// 對每一對在交集 `meet[c1][c2]` 上相容的局部截面 `(u, v)`，恰存在唯一全局截面 `x ∈ F(top_stage)`。
pub fn PosetPresheaf::verify_binary_sheaf_gluing(
  self : PosetPresheaf,
  top_stage : Int32,
  c1 : Int32,
  c2 : Int32,
) -> Bool {
  let mut coherent_pairs = 0
  for u in 0..<self.card[c1] {
    for v in 0..<self.card[c2] {
      let sys = CoherentPartial::{ stages: [c1, c2], vals: [u, v] }
      if self.check_coherent(sys) {
        coherent_pairs = coherent_pairs + 1
        match self.kan_sheaf_solve(top_stage, top_stage, sys) {
          Some(res) =>
            if res.filler_count != 1 {
              return false
            }
          None => return false
        }
      }
    }
  }
  coherent_pairs == self.card[top_stage]
}

///|
/// 以 `kan_sheaf_solve` 抽出鏈景預層的全部相容逆極限線程（統一 `InvSystem::limit_threads`）。
pub fn PosetPresheaf::extract_limit_threads(
  self : PosetPresheaf,
) -> Array[Array[Int32]] {
  let top = self.site.n - 1
  let empty = CoherentPartial::{ stages: [], vals: [] }
  match self.kan_sheaf_solve(top, top, empty) {
    None => []
    Some(res) => {
      let out : Array[Array[Int32]] = []
      for x in res.all_fillers {
        let thread : Array[Int32] = []
        let mut t = top
        while t >= 0 {
          thread.push(self.restrict(top, t, x))
          t = t - 1
        }
        out.push(thread)
      }
      out
    }
  }
}

// ---------------- 核心算子 4：廣義偏序景 Glue 構造器與代數結構單價搬運 ----------------

///|
/// 廣義偏序景 `Glue` 構造器：
/// 給定基礎預層 `base`、偏序景上的下閉位元外延 `ext : @core.Bits`、局部預層 `t_diag`
/// 以及在每個 `sigma ∈ ext` 上的雙射 `isos[sigma] : T(sigma) ≃ Base(sigma)`：
///   - 在 `sigma ∈ ext` 上，黏合預層的纖維嚴格取 `T(sigma)`；
///   - 在 `sigma ∉ ext` 上，纖維取 `Base(sigma)`；
///   - 當限制映射跨越邊界（`big ∉ ext` 而 `face ∈ ext`）時，以逆雙射扭轉：
///     `res^{Glue}_{big -> face} = (isos[face].bwd) ∘ res^{Base}_{big -> face}`。
pub fn glue_presheaf(
  base : PosetPresheaf,
  ext : @core.Bits,
  t_diag : PosetPresheaf,
  isos : Array[@cubical.Iso],
) -> PosetPresheaf {
  let n = base.site.n
  let card : Array[Int32] = []
  for s in 0..<n {
    if ext.get(s) {
      card.push(t_diag.card[s])
    } else {
      card.push(base.card[s])
    }
  }
  let res : Array[Array[Int32]] = []
  for big in 0..<n {
    for face in 0..<n {
      if !base.site.le.get(face, big) {
        res.push([])
      } else if ext.get(big) {
        res.push(t_diag.res_fn(big, face))
      } else if !ext.get(face) {
        res.push(base.res_fn(big, face))
      } else {
        res.push(@cubical.fn_comp(base.res_fn(big, face), isos[face].bwd))
      }
    }
  }
  PosetPresheaf::{ site: base.site, card, res }
}

///|
/// 代數結構沿單價路徑 `ua(iso)` 的自動 Kan 搬運（Algebraic Structure Univalence Transport）：
/// 給定兩個大小為 `n` 的有限代數載體之間的雙射 `iso : A ≃ B`（例如由 CRT、Wedderburn–Artin
/// 冪等元分解或坐標環求值同構給出）及 `A` 上的二元運算表 `op_a`：
///   1. 用廣義 `glue_presheaf` 在 1-維立方體景 `{0, 1, *}` 上構造單價路徑預層 `U_line = ua(iso)`；
///   2. 沿 `U_line` 的限制映射對二元運算表執行 Kan 共軛填補搬運，輸出 `B` 上的二元運算表 `op_b`；
///   3. 定理（結構同一性原理 SIP）：搬運後的 `op_b` 嚴格滿足同態律
///      `op_b[iso(x)][iso(y)] == iso(op_a[x][y])`！
pub fn algebraic_univalence_transport_op(
  iso : @cubical.Iso,
  op_a : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let n = iso.dom
  // 在 1-維立方體景 {0: i=0, 1: i=1, 2: i=*} 上以 glue_presheaf 構造 ua(iso)
  let site1 = PosetSite::from_cube(1)
  let base = PosetPresheaf::from_cubety(@cubical.const_ty(1, iso.cod))
  let t_card : Array[Int32] = [iso.dom, iso.cod, iso.dom]
  let t_res : Array[Array[Int32]] = [
    @cubical.fn_id(iso.dom),
    [],
    [],
    [],
    @cubical.fn_id(iso.cod),
    [],
    @cubical.fn_id(iso.dom),
    iso.fwd,
    @cubical.fn_id(iso.dom),
  ]
  let t_diag = PosetPresheaf::{ site: site1, card: t_card, res: t_res }
  let ext = @core.Bits::new(3)
  ext.set(0)
  ext.set(1)
  let isos : Array[@cubical.Iso] = [
    iso,
    @cubical.Iso::id(iso.cod),
    @cubical.Iso::id(iso.dom),
  ]
  let ua_diag = glue_presheaf(base, ext, t_diag, isos)
  // 用 kan_sheaf_solve 在 ua_diag 上執行雙向點搬運：
  //   fwd_transport(x) = kan_sheaf_solve(top=2, lid=1, {0: x}).lid
  //   bwd_transport(y) = kan_sheaf_solve(top=2, lid=0, {1: y}).lid
  let bwd_map : Array[Int32] = []
  for y in 0..<n {
    let sys_bwd = CoherentPartial::{ stages: [1], vals: [y] }
    match ua_diag.kan_sheaf_solve(2, 0, sys_bwd) {
      Some(r) => bwd_map.push(r.lid)
      None => abort("algebraic_univalence_transport_op: backward Kan fill failed")
    }
  }
  let op_b : Array[Array[Int32]] = []
  for y1 in 0..<n {
    let row : Array[Int32] = []
    let x1 = bwd_map[y1]
    for y2 in 0..<n {
      let x2 = bwd_map[y2]
      let res_a = op_a[x1][x2]
      let sys_fwd = CoherentPartial::{ stages: [0], vals: [res_a] }
      match ua_diag.kan_sheaf_solve(2, 1, sys_fwd) {
        Some(r) => row.push(r.lid)
        None =>
          abort("algebraic_univalence_transport_op: forward Kan fill failed")
      }
    }
    op_b.push(row)
  }
  op_b
}

///|
/// 直接將 `algo/hott` 的型別等價 `@hott.Equiv[Int32, Int32]`（定義於 `0..<n`）
/// 升格為廣義偏序景單價路徑，並搬運二元代數運算表。
pub fn algebraic_univalence_from_hott_equiv(
  e : @hott.Equiv[Int32, Int32],
  n : Int32,
  op_a : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let fwd : Array[Int32] = []
  let bwd : Array[Int32] = []
  for x in 0..<n {
    fwd.push((e.fwd)(x))
    bwd.push((e.bwd)(x))
  }
  let iso = @cubical.Iso::new(n, n, fwd, bwd)
  algebraic_univalence_transport_op(iso, op_a)
}

