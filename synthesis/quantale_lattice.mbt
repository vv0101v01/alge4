// =============================================================================
// 合成新演算法（階段 I & II）：位並行量化閉包格與根核／同調分解引擎
// (Bit-Parallel Quantale Closure Lattice & Radical/Homology Synthesis Engine)
//
// 抽象代數與格論共通因子提煉：
//   將 algo 的「理想格 / 子模格 / Zariski 開集格 / 算子閉包枚舉 / 根理想 / 導體 / 零化子 /
//   Socle / Wedderburn–Artin 冪等元分解」與 alge3 的「64-bit Bits 位元並行運算 /
//   立方體餘纖維外延格 Cof::extent / 單純複形與鏈複形同調 SimplicialComplex」
//   統一收斂為單一結構：`ClosureQuantale`（有限交換量化格 / 殘差閉包格）。
// =============================================================================

///|
/// 位元集合包含判定：`a ⊆ b` ⟺ `∀i, a[i] ⟹ b[i]`。
pub fn bits_subset(a : @core.Bits, b : @core.Bits) -> Bool {
  let n = a.length()
  let x = a.copy()
  while true {
    match x.first_set() {
      None => break
      Some(i) => {
        if i < n && !b.get(i) {
          return false
        }
        x.clear_bit(i)
      }
    }
  }
  true
}

///|
/// 位元集合交集：`a ∩ b`。
pub fn bits_intersect(a : @core.Bits, b : @core.Bits) -> @core.Bits {
  let n = a.length()
  let out = @core.Bits::new(n)
  let x = a.copy()
  while true {
    match x.first_set() {
      None => break
      Some(i) => {
        if i < n && b.get(i) {
          out.set(i)
        }
        x.clear_bit(i)
      }
    }
  }
  out
}

///|
/// 位元集合聯集：`a ∪ b`。
pub fn bits_union(a : @core.Bits, b : @core.Bits) -> @core.Bits {
  let out = a.copy()
  out.or_inplace(b)
  out
}

///|
/// 位元集合字典序比較（先比權重/基數，基數相同時按最低相異位比較），
/// 保證格中 `0` 號元素恆為 `⊥`，最後一個元素恆為 `⊤`，且嚴格包含必保序。
fn bits_cmp(a : @core.Bits, b : @core.Bits) -> Int32 {
  let wa = a.weight()
  let wb = b.weight()
  if wa != wb {
    return wa.compare(wb)
  }
  let n = a.length()
  for i in 0..<n {
    let ai = a.get(i)
    let bi = b.get(i)
    if ai != bi {
      return if ai { 1 } else { -1 }
    }
  }
  0
}

///|
/// 有限載體 `X = {0, ..., N-1}` 上的位並行閉包量化格（Complete Residuated Closure Lattice / Quantale）：
/// - `closed`：全體閉子集 `L = Fix(cl)`，每個元素為 `@core.Bits`；
/// - `le_mat`：偏序關係 `c_i ≼ c_j ⟺ c_i ⊆ c_j`；
/// - `meet_table`：格交 `c_i ∧ c_j = c_i ∩ c_j`；
/// - `join_table`：格並 `c_i ∨ c_j = cl(c_i ∪ c_j)`；
/// - `prod_table`：量化乘法 `c_i · c_j = cl({x · y | x ∈ c_i, y ∈ c_j})`
///                 （在理想格中為理想積 `I·J`；在子模格／開集格／面格中取交 `c_i ∧ c_j` 即 Frame）；
/// - `resid_table`：右殘差／導體／Heyting 蘊涵 `(c_i : c_j) = ⋁ { c_k ∈ L | c_k · c_j ≼ c_i }`。
pub(all) struct ClosureQuantale {
  carrier_size : Int32
  zero_idx : Int32
  add_table : Array[Array[Int32]]
  act_tables : Array[Array[Int32]]
  mul_table : Array[Array[Int32]]
  closed : Array[@core.Bits]
  le_mat : @core.BoolMat
  meet_table : Array[Array[Int32]]
  join_table : Array[Array[Int32]]
  prod_table : Array[Array[Int32]]
  resid_table : Array[Array[Int32]]
}

///|
/// 核心算子 1：位並行算子閉包 `cl(seed)`。
/// 給定載體上的任意種子位元集 `seed`，在位元層面同時對：
///   (1) 零元 `zero_idx`（若存在 `>= 0`）、
///   (2) 加法表 `add_table`（子群／子空間閉包）、
///   (3) 算子表 `act_tables`（環作用／模作用／拓撲基生成）
/// 求最小不動點 `cl(seed)`。
pub fn bit_closure(
  carrier_size : Int32,
  zero_idx : Int32,
  add_table : Array[Array[Int32]],
  act_tables : Array[Array[Int32]],
  seed : @core.Bits,
) -> @core.Bits {
  let cur = seed.copy()
  if zero_idx >= 0 && zero_idx < carrier_size {
    cur.set(zero_idx)
  }
  let mut changed = true
  while changed {
    changed = false
    // 1. 算子不變閉包（每個算子 op 將 x 映至 act_tables[op][x]）
    for op in act_tables {
      let scan = cur.copy()
      while true {
        match scan.first_set() {
          None => break
          Some(x) => {
            let y = op[x]
            if y >= 0 && y < carrier_size && !cur.get(y) {
              cur.set(y)
              changed = true
            }
            scan.clear_bit(x)
          }
        }
      }
    }
    // 2. 加法閉包（若提供加法表）
    if add_table.length() == carrier_size {
      let s1 = cur.copy()
      while true {
        match s1.first_set() {
          None => break
          Some(x) => {
            let s2 = cur.copy()
            while true {
              match s2.first_set() {
                None => break
                Some(y) => {
                  let z = add_table[x][y]
                  if z >= 0 && z < carrier_size && !cur.get(z) {
                    cur.set(z)
                    changed = true
                  }
                  s2.clear_bit(y)
                }
              }
            }
            s1.clear_bit(x)
          }
        }
      }
    }
  }
  cur
}

///|
/// 在已排序的閉集陣列 `closed` 中查找位元集 `target` 的索引。
pub fn find_closed_index(closed : Array[@core.Bits], target : @core.Bits) -> Int32 {
  for i in 0..<closed.length() {
    if closed[i].same(target) {
      return i
    }
  }
  -1
}

///|
/// 核心算子 2：由閉包系統與量化乘法表一次性合成完整的 `ClosureQuantale`。
/// 算法：
///   1. 以位並行 BFS 從最小閉集 `⊥ = cl(∅)` 出發枚舉全體不動點 `L = Fix(cl)`；
///   2. 按基數與字典序正規化排序，使 `0 = ⊥`、`L.length()-1 = ⊤`；
///   3. 建立位元偏序矩陣 `le_mat`、格交 `meet_table`、格並 `join_table`、量化積 `prod_table`；
///   4. 透過伽羅瓦伴隨公式 `(c_i : c_j) = ⋁ { c_k | c_k · c_j ≼ c_i }` 預計算殘差表 `resid_table`。
pub fn ClosureQuantale::synthesize(
  carrier_size : Int32,
  zero_idx : Int32,
  add_table : Array[Array[Int32]],
  act_tables : Array[Array[Int32]],
  mul_table : Array[Array[Int32]],
  generators : Array[@core.Bits],
) -> ClosureQuantale {
  let bot_bits = bit_closure(
    carrier_size,
    zero_idx,
    add_table,
    act_tables,
    @core.Bits::new(carrier_size),
  )
  let queue : Array[@core.Bits] = [bot_bits]
  // 若未額外限制生成元，預設以載體所有單元素為生成元；否則以給定生成元擴張
  let gens : Array[@core.Bits] = []
  if generators.length() == 0 {
    for x in 0..<carrier_size {
      let b = @core.Bits::new(carrier_size)
      b.set(x)
      gens.push(bit_closure(carrier_size, zero_idx, add_table, act_tables, b))
    }
  } else {
    for g in generators {
      let cg = bit_closure(carrier_size, zero_idx, add_table, act_tables, g)
      if find_closed_index(gens, cg) == -1 {
        gens.push(cg)
      }
    }
    // 將給定生成元對有限交集閉包，使其構成拓撲基（Multiplicative Basis）
    let mut gi = 0
    while gi < gens.length() {
      let a = gens[gi]
      gi = gi + 1
      let cur_len = gens.length()
      for gj in 0..<cur_len {
        let inter = bit_closure(
          carrier_size,
          zero_idx,
          add_table,
          act_tables,
          bits_intersect(a, gens[gj]),
        )
        if find_closed_index(gens, inter) == -1 {
          gens.push(inter)
        }
      }
    }
  }
  let mut qi = 0
  while qi < queue.length() {
    let cur = queue[qi]
    qi = qi + 1
    for g in gens {
      if bits_subset(g, cur) {
        continue
      }
      let cand = bit_closure(
        carrier_size,
        zero_idx,
        add_table,
        act_tables,
        bits_union(cur, g),
      )
      if find_closed_index(queue, cand) == -1 {
        queue.push(cand)
      }
    }
  }
  queue.sort_by(bits_cmp)
  let m = queue.length()
  // 偏序矩陣 le_mat
  let le_rows : Array[@core.Bits] = []
  for i in 0..<m {
    let r = @core.Bits::new(m)
    for j in 0..<m {
      if bits_subset(queue[i], queue[j]) {
        r.set(j)
      }
    }
    le_rows.push(r)
  }
  let le_mat = @core.BoolMat::new(le_rows, m)
  // meet_table 與 join_table
  let meet_table : Array[Array[Int32]] = []
  let join_table : Array[Array[Int32]] = []
  for i in 0..<m {
    let mrow : Array[Int32] = []
    let jrow : Array[Int32] = []
    for j in 0..<m {
      let inter = bits_intersect(queue[i], queue[j])
      let midx = find_closed_index(queue, inter)
      mrow.push(midx)
      let uni = bit_closure(
        carrier_size,
        zero_idx,
        add_table,
        act_tables,
        bits_union(queue[i], queue[j]),
      )
      let jidx = find_closed_index(queue, uni)
      jrow.push(jidx)
    }
    meet_table.push(mrow)
    join_table.push(jrow)
  }
  // prod_table：若提供 mul_table 則計算閉包積 cl(c_i · c_j)，否則退化為 Frame 的 meet
  let prod_table : Array[Array[Int32]] = []
  if mul_table.length() == carrier_size {
    for i in 0..<m {
      let prow : Array[Int32] = []
      for j in 0..<m {
        let seed = @core.Bits::new(carrier_size)
        let s1 = queue[i].copy()
        while true {
          match s1.first_set() {
            None => break
            Some(a) => {
              let s2 = queue[j].copy()
              while true {
                match s2.first_set() {
                  None => break
                  Some(b) => {
                    let ab = mul_table[a][b]
                    if ab >= 0 && ab < carrier_size {
                      seed.set(ab)
                    }
                    s2.clear_bit(b)
                  }
                }
              }
              s1.clear_bit(a)
            }
          }
        }
        let closed_prod = bit_closure(
          carrier_size, zero_idx, add_table, act_tables, seed,
        )
        prow.push(find_closed_index(queue, closed_prod))
      }
      prod_table.push(prow)
    }
  } else {
    for i in 0..<m {
      let prow : Array[Int32] = []
      for j in 0..<m {
        prow.push(meet_table[i][j])
      }
      prod_table.push(prow)
    }
  }
  // resid_table: (c_i : c_j) = ⋁ { c_k | c_k · c_j ≼ c_i }
  let resid_table : Array[Array[Int32]] = []
  for i in 0..<m {
    let rrow : Array[Int32] = []
    for j in 0..<m {
      let mut acc = 0 // ⊥
      for k in 0..<m {
        let kj = prod_table[k][j]
        if kj >= 0 && le_mat.get(kj, i) {
          acc = join_table[acc][k]
        }
      }
      rrow.push(acc)
    }
    resid_table.push(rrow)
  }
  ClosureQuantale::{
    carrier_size,
    zero_idx,
    add_table,
    act_tables,
    mul_table,
    closed: queue,
    le_mat,
    meet_table,
    join_table,
    prod_table,
    resid_table,
  }
}

///|
/// 實例化 1：由 `algo/finite` 的有限交換代數 `FinAlg` 構造其理想量化格 `Idl(R)`。
pub fn ClosureQuantale::from_finalg(alg : @finite.FinAlg) -> ClosureQuantale {
  let elems = alg.all_elements()
  let n = elems.length()
  let p = alg.p
  let d = alg.dim
  fn code_of(v : Array[Int32], p : Int32, d : Int32) -> Int32 {
    let mut c = 0
    let mut place = 1
    for k in 0..<d {
      c = c + @num.mod_pos(v[k], p) * place
      place = place * p
    }
    c
  }
  let add_table : Array[Array[Int32]] = []
  let mul_table : Array[Array[Int32]] = []
  for i in 0..<n {
    let arow : Array[Int32] = []
    let mrow : Array[Int32] = []
    for j in 0..<n {
      arow.push(code_of(alg.add_elem(elems[i], elems[j]), p, d))
      mrow.push(code_of(alg.mul_elem(elems[i], elems[j]), p, d))
    }
    add_table.push(arow)
    mul_table.push(mrow)
  }
  // 算子作用：乘以每個基向量 e_0, ..., e_{d-1}
  let act_tables : Array[Array[Int32]] = []
  for b in 0..<d {
    let op : Array[Int32] = []
    for x in 0..<n {
      let y = alg.mult[b].apply(elems[x])
      op.push(code_of(y, p, d))
    }
    act_tables.push(op)
  }
  ClosureQuantale::synthesize(n, 0, add_table, act_tables, mul_table, [])
}

///|
/// 實例化 2：由 `algo/modules` 的有限模 `FinModule` 構造其子模完備模格 `Sub(M)`。
pub fn ClosureQuantale::from_finmodule(m : @modules.FinModule) -> ClosureQuantale {
  let p = m.alg.p
  let d = m.dim
  let elems = @linalg.enumerate_vectors(p, d)
  let n = elems.length()
  fn code_of(v : Array[Int32], p : Int32, d : Int32) -> Int32 {
    let mut c = 0
    let mut place = 1
    for k in 0..<d {
      c = c + @num.mod_pos(v[k], p) * place
      place = place * p
    }
    c
  }
  let add_table : Array[Array[Int32]] = []
  for i in 0..<n {
    let arow : Array[Int32] = []
    for j in 0..<n {
      arow.push(code_of(@linalg.vec_add(p, elems[i], elems[j]), p, d))
    }
    add_table.push(arow)
  }
  let act_tables : Array[Array[Int32]] = []
  for b in 0..<m.action.length() {
    let op : Array[Int32] = []
    for x in 0..<n {
      op.push(code_of(m.action[b].apply(elems[x]), p, d))
    }
    act_tables.push(op)
  }
  ClosureQuantale::synthesize(n, 0, add_table, act_tables, [], [])
}

///|
/// 實例化 3：由 `algo/scheme` 的素理想譜 `Spec R` 構造 Zariski 開集 Frame（無點拓撲分配格）。
/// 每個開集為 `Spec R` 的位元子集，由基本開集 `D(f)` 經有限並生成；
/// 乘法為交集 `U ∩ V`，殘差 `(U : V)` 即開集 Heyting 蘊涵 `int((Spec \ V) ∪ U)`！
pub fn ClosureQuantale::from_zariski_spec(sp : @scheme.Spec) -> ClosureQuantale {
  let nprimes = sp.primes.length()
  let gens : Array[@core.Bits] = []
  for f in sp.alg.all_elements() {
    let b = @core.Bits::new(nprimes)
    for idx in sp.basic_open(f) {
      b.set(idx)
    }
    gens.push(b)
  }
  ClosureQuantale::synthesize(nprimes, -1, [], [], [], gens)
}

///|
/// 實例化 4：由 `alge3/cubical` 的餘纖維集合構造 `n`-維立方體面格（Cofibration Extent Frame）。
/// 載體為 `3^n` 個子立方體，每個餘纖維 `φ` 對應向下封閉位元外延 `φ.extent(n)`。
pub fn ClosureQuantale::from_cubical_cofs(
  n : Int32,
  cofs : Array[@cubical.Cof],
) -> ClosureQuantale {
  let total = @cubical.pow3(n)
  // 下閉包算子：每個方向 d ∈ 0..<n、端點 eps ∈ {0,1} 將自由面映向子面
  let act_tables : Array[Array[Int32]] = []
  for d in 0..<n {
    for eps in 0..<2 {
      let op : Array[Int32] = []
      for code in 0..<total {
        op.push(@cubical.subcube_set_digit(code, d, eps))
      }
      act_tables.push(op)
    }
  }
  let gens : Array[@core.Bits] = []
  for phi in cofs {
    gens.push(phi.extent(n))
  }
  ClosureQuantale::synthesize(total, -1, [], act_tables, [], gens)
}

// ---------------- 階段 II：統一格論與抽象代數不變量演算法 ----------------

///|
/// 格元素個數 `|L|`。
pub fn ClosureQuantale::size(self : ClosureQuantale) -> Int32 {
  self.closed.length()
}

///|
/// 最小元 `⊥ = 0`。
pub fn ClosureQuantale::bot(self : ClosureQuantale) -> Int32 {
  ignore(self)
  0
}

///|
/// 最大元 `⊤ = |L| - 1`。
pub fn ClosureQuantale::top(self : ClosureQuantale) -> Int32 {
  self.closed.length() - 1
}

///|
/// 偏序判定 `a ≼ b`。
pub fn ClosureQuantale::is_le(
  self : ClosureQuantale,
  a : Int32,
  b : Int32,
) -> Bool {
  self.le_mat.get(a, b)
}

///|
/// 格交 `a ∧ b`。
pub fn ClosureQuantale::meet(
  self : ClosureQuantale,
  a : Int32,
  b : Int32,
) -> Int32 {
  self.meet_table[a][b]
}

///|
/// 格並 `a ∨ b`。
pub fn ClosureQuantale::join(
  self : ClosureQuantale,
  a : Int32,
  b : Int32,
) -> Int32 {
  self.join_table[a][b]
}

///|
/// 量化積 `a · b`（理想乘積或 Frame 交）。
pub fn ClosureQuantale::mul(
  self : ClosureQuantale,
  a : Int32,
  b : Int32,
) -> Int32 {
  self.prod_table[a][b]
}

///|
/// 右殘差／導體／Heyting 蘊涵 `(a : b) = ⋁ { x ∈ L | x · b ≼ a }`。
pub fn ClosureQuantale::residual(
  self : ClosureQuantale,
  a : Int32,
  b : Int32,
) -> Int32 {
  self.resid_table[a][b]
}

///|
/// 零化子／Heyting 偽補元 `Ann(a) = (⊥ : a)`。
pub fn ClosureQuantale::annihilator_of(
  self : ClosureQuantale,
  a : Int32,
) -> Int32 {
  self.resid_table[self.bot()][a]
}

///|
/// 格的原子（Atoms）：極小非底元 `a ≻ ⊥`。
/// 在理想格中即單純理想 `simple_ideals`；在子模格中即單純子模。
pub fn ClosureQuantale::atoms(self : ClosureQuantale) -> Array[Int32] {
  let m = self.size()
  let bot = self.bot()
  let out : Array[Int32] = []
  for a in 0..<m {
    if a == bot {
      continue
    }
    let mut minimal = true
    for b in 0..<m {
      if b != bot && b != a && self.is_le(b, a) {
        minimal = false
      }
    }
    if minimal {
      out.push(a)
    }
  }
  out
}

///|
/// 格的餘原子（Coatoms）：極大真元 `c ≺ ⊤`。
/// 在理想格中即極大理想 `maximal_ideals`。
pub fn ClosureQuantale::coatoms(self : ClosureQuantale) -> Array[Int32] {
  let m = self.size()
  let top = self.top()
  let out : Array[Int32] = []
  for a in 0..<m {
    if a == top {
      continue
    }
    let mut maximal = true
    for b in 0..<m {
      if b != top && b != a && self.is_le(a, b) {
        maximal = false
      }
    }
    if maximal {
      out.push(a)
    }
  }
  out
}

///|
/// 量化格的素元譜 `Spec(L) = { p ≺ ⊤ | ∀a,b ∈ L: a·b ≼ p ⟹ a ≼ p ∨ b ≼ p }`。
/// 定理（理想層面）：交換環理想格上的量化素元與環論素理想一一對應！
pub fn ClosureQuantale::quantale_primes(
  self : ClosureQuantale,
) -> Array[Int32] {
  let m = self.size()
  let top = self.top()
  let out : Array[Int32] = []
  for p in 0..<m {
    if p == top {
      continue
    }
    let mut is_p = true
    for a in 0..<m {
      for b in 0..<m {
        if self.is_le(self.mul(a, b), p) &&
          !self.is_le(a, p) &&
          !self.is_le(b, p) {
          is_p = false
        }
      }
    }
    if is_p {
      out.push(p)
    }
  }
  out
}

///|
/// 極小素元 `MinSpec(L)`（概形的不可約分支 `irreducible_components`）。
pub fn ClosureQuantale::minimal_primes(
  self : ClosureQuantale,
) -> Array[Int32] {
  let ps = self.quantale_primes()
  let out : Array[Int32] = []
  for p in ps {
    let mut minimal = true
    for q in ps {
      if q != p && self.is_le(q, p) {
        minimal = false
      }
    }
    if minimal {
      out.push(p)
    }
  }
  out
}

///|
/// 根核算子（Radical Nucleus）：`rad(a) = ⋀ { p ∈ Spec(L) | a ≼ p }`。
/// 定理（Krull / 量化格根定理）：在有限交換環理想格中，`rad(I) = √I` 恆等於包含 `I` 的所有素理想之交。
pub fn ClosureQuantale::radical_of(
  self : ClosureQuantale,
  a : Int32,
) -> Int32 {
  let mut acc = self.top()
  for p in self.quantale_primes() {
    if self.is_le(a, p) {
      acc = self.meet(acc, p)
    }
  }
  acc
}

///|
/// 冪零根 `Nil(L) = rad(⊥)`。
pub fn ClosureQuantale::nilradical_id(self : ClosureQuantale) -> Int32 {
  self.radical_of(self.bot())
}

///|
/// Jacobson 根 `J(L) = ⋀ Coatoms(L)`。
pub fn ClosureQuantale::jacobson_id(self : ClosureQuantale) -> Int32 {
  let mut acc = self.top()
  for c in self.coatoms() {
    acc = self.meet(acc, c)
  }
  acc
}

///|
/// 格的芯 `Socle(L) = (⊥ : J(L)) = Ann(J(L))`。
pub fn ClosureQuantale::socle_id(self : ClosureQuantale) -> Int32 {
  self.annihilator_of(self.jacobson_id())
}

///|
/// 半素元（Radical element）判定：`rad(a) == a`。
pub fn ClosureQuantale::is_semiprime_id(
  self : ClosureQuantale,
  a : Int32,
) -> Bool {
  self.radical_of(a) == a
}

///|
/// 格元素 `a` 是否存在格補元 `b`（`a ∧ b = ⊥ ∧ a ∨ b = ⊤`）。
/// 在子模格中對應 `FinModule::complement_exists`（分裂短正合列）。
pub fn ClosureQuantale::has_complement(
  self : ClosureQuantale,
  a : Int32,
) -> Bool {
  let m = self.size()
  let bot = self.bot()
  let top = self.top()
  for b in 0..<m {
    if self.meet(a, b) == bot && self.join(a, b) == top {
      return true
    }
  }
  false
}

///|
/// 整座格是否為有補格（Complemented Lattice）：`∀a ∈ L, has_complement(a)`。
/// 定理（模格半單判準）：模 M 的子模格為有補格 ⟺ M 為半單模（Semisimple）！
pub fn ClosureQuantale::is_complemented_lattice(
  self : ClosureQuantale,
) -> Bool {
  for a in 0..<self.size() {
    if !self.has_complement(a) {
      return false
    }
  }
  true
}

///|
/// 量化格的布林中心原子（Boolean Center Atoms / Primitive Idempotent Blocks）：
/// 尋找所有非底元 `e ≻ ⊥`，使得存在 `f` 滿足 `e ∨ f = ⊤` 且 `e · f = ⊥`（故 `e · e = e`），
/// 且 `e` 在此類直積分裂元中極小。
/// 定理（格論版 Wedderburn–Artin / Krull–Schmidt）：理想格的布林中心原子與環的本原冪等元角塊 `eR` 一一對應！
pub fn ClosureQuantale::boolean_center_atoms(
  self : ClosureQuantale,
) -> Array[Int32] {
  let m = self.size()
  let bot = self.bot()
  let top = self.top()
  let center : Array[Int32] = []
  for e in 0..<m {
    let mut is_central_idem = false
    for f in 0..<m {
      if self.join(e, f) == top &&
        self.mul(e, f) == bot &&
        self.meet(e, f) == bot {
        is_central_idem = true
      }
    }
    if is_central_idem && e != bot {
      center.push(e)
    }
  }
  let atoms : Array[Int32] = []
  for e in center {
    let mut minimal = true
    for c in center {
      if c != e && self.is_le(c, e) {
        minimal = false
      }
    }
    if minimal {
      atoms.push(e)
    }
  }
  atoms
}

///|
/// 格的最大嚴格鏈節點數（DCC / 合成列長度 + 1）：因 `closed` 已按基數拓撲排序，
/// 直接以一次前向 O(|L|²) DAG 動態規劃求出。
pub fn ClosureQuantale::longest_chain_len(self : ClosureQuantale) -> Int32 {
  let m = self.size()
  if m == 0 {
    return 0
  }
  let dp = Array::make(m, 1)
  let mut best = 1
  for i in 0..<m {
    for j in 0..<i {
      if self.is_le(j, i) && dp[j] + 1 > dp[i] {
        dp[i] = dp[j] + 1
      }
    }
    if dp[i] > best {
      best = dp[i]
    }
  }
  best
}

///|
/// 量化素譜的 Krull 維數：`Spec(L)` 中嚴格鏈的最大邊數（空譜回傳 `-1`）。
pub fn ClosureQuantale::krull_dimension(self : ClosureQuantale) -> Int32 {
  let ps = self.quantale_primes()
  let n = ps.length()
  if n == 0 {
    return -1
  }
  let dp = Array::make(n, 1)
  let mut best = 1
  for i in 0..<n {
    for j in 0..<i {
      if self.is_le(ps[j], ps[i]) && dp[j] + 1 > dp[i] {
        dp[i] = dp[j] + 1
      }
    }
    if dp[i] > best {
      best = dp[i]
    }
  }
  best - 1
}

///|
/// 跨庫湧現算子：構造格 `L`（或真部 `L \ {⊥, ⊤}`）的 **階複形（Order Complex / Poset Nerve）**
/// `Δ(L)` 為 `@homotopy.SimplicialComplex`（要求節點數 `<= 62`）。
/// `k`-單形即嚴格鏈 `x_0 ≺ x_1 ≺ ... ≺ x_k`，由極大鏈以 `UInt64` 位元遮罩生成。
pub fn ClosureQuantale::order_complex(
  self : ClosureQuantale,
  proper_only : Bool,
) -> @homotopy.SimplicialComplex {
  let m = self.size()
  let nodes : Array[Int32] = []
  for i in 0..<m {
    if proper_only && (i == self.bot() || i == self.top()) {
      continue
    }
    nodes.push(i)
  }
  let k = nodes.length()
  if k == 0 || k > 60 {
    return @homotopy.SimplicialComplex::from_maximal([])
  }
  // DFS 枚舉偏序集中的所有極大嚴格鏈，編碼為 0..<k 上的 UInt64 遮罩
  let maximal : Array[UInt64] = []
  fn dfs(
    q : ClosureQuantale,
    nodes : Array[Int32],
    last_idx : Int32,
    mask : UInt64,
    maximal : Array[UInt64],
  ) -> Unit {
    let mut extended = false
    let start = last_idx + 1
    for nxt in start..<nodes.length() {
      if q.is_le(nodes[last_idx], nodes[nxt]) {
        extended = true
        dfs(q, nodes, nxt, mask | (1UL << nxt), maximal)
      }
    }
    if !extended {
      maximal.push(mask)
    }
  }
  for i in 0..<k {
    let mut has_pred = false
    for j in 0..<i {
      if self.is_le(nodes[j], nodes[i]) {
        has_pred = true
      }
    }
    if !has_pred {
      dfs(self, nodes, i, 1UL << i, maximal)
    }
  }
  @homotopy.SimplicialComplex::from_maximal(maximal)
}

///|
/// 計算格階複形 `Δ(L)` 在 `𝔽_2` 上的 Folkman–Quillen 同調 Betti 數。
pub fn ClosureQuantale::order_homology_betti(
  self : ClosureQuantale,
  proper_only : Bool,
) -> Array[Int32] {
  self.order_complex(proper_only).betti()
}

// ---------------- 跨庫擴展（整合 alge / alge1 / alge2）：Topos 模態、餘切嵌入維數與 Alexandrov 同倫核 ----------------

///|
/// Topos 內部 Heyting 蘊涵 `(b ⇒ a)`：在殘差量化格中即右殘差 `residual(a, b) = (a : b)`
/// （整合 `alge1/topos::omega_implies` 與 `alge2/vect_top_topos::heyting_implies`）。
pub fn ClosureQuantale::heyting_implication(
  self : ClosureQuantale,
  b : Int32,
  a : Int32,
) -> Int32 {
  self.residual(a, b)
}

///|
/// Topos 內部偽補否定 `¬a = (a ⇒ ⊥) = (⊥ : a)`（在理想格中即零化子 `Ann(a)`）。
pub fn ClosureQuantale::heyting_negation(
  self : ClosureQuantale,
  a : Int32,
) -> Int32 {
  self.residual(self.bot(), a)
}

///|
/// Lawvere–Tierney 左精確雙重否定稠密模態 `○_{¬¬}(a) = ¬¬a = (⊥ : (⊥ : a))`
/// （整合 `alge1/topos::sheafify` 與 `alge2/vect_top_topos::lawvere_tierney_dense`）。
pub fn ClosureQuantale::lawvere_tierney_dense(
  self : ClosureQuantale,
  a : Int32,
) -> Int32 {
  self.heyting_negation(self.heyting_negation(a))
}

///|
/// Kripke–Joyal 語義強制判定 `stage_p ⊩ formula_a` ⟺ `stage_p ≼ formula_a`
/// （整合 `alge1/topos::mitchell_benabou_eval` 與 `alge2/vect_top_topos::kripke_joyal_forces`）。
pub fn ClosureQuantale::kripke_joyal_forces(
  self : ClosureQuantale,
  stage_p : Int32,
  formula_a : Int32,
) -> Bool {
  self.is_le(stage_p, formula_a)
}

///|
/// 判定量化格是否為局部格（具唯一餘原子／唯一極大理想 `m`，整合 `alge/quot::is_local`）。
pub fn ClosureQuantale::is_local_quantale(self : ClosureQuantale) -> Bool {
  self.coatoms().length() == 1
}

///|
/// 計算局部阿廷環理想格在素數特徵 `p` 下的 Zariski 餘切空間嵌入維數
/// `edim(R) = dim_{𝔽_p}(m / m²) = log_p(|m| / |m²|)`（整合 `alge/quot::edim` 與 `alge/ga::Tables::edim`）。
pub fn ClosureQuantale::embedding_dimension(
  self : ClosureQuantale,
  p : Int32,
) -> Int32 {
  let cs = self.coatoms()
  if cs.length() != 1 || p <= 1 {
    return 0
  }
  let m = cs[0]
  let m2 = self.mul(m, m)
  let wm = self.closed[m].weight()
  let wm2 = self.closed[m2].weight()
  if wm2 <= 0 || wm <= wm2 {
    return 0
  }
  let mut ratio = wm / wm2
  let mut edim = 0
  while ratio > 1 {
    ratio = ratio / p
    edim = edim + 1
  }
  edim
}

///|
/// 正則局部環判準（Auslander–Buchsbaum–Serre / `alge/quot` 定理 T4）：
/// 局部環 `R` 為正則局部環 ⟺ `edim(R) == krull_dimension(R)`（對零維局部阿廷環即 `edim == 0`，亦即 `R` 為體）。
pub fn ClosureQuantale::is_regular_local(
  self : ClosureQuantale,
  p : Int32,
) -> Bool {
  self.is_local_quantale() &&
  self.embedding_dimension(p) == self.krull_dimension()
}

///|
/// 輔助函數：檢查嚴格錐遮罩 `strict_cone` 在偏序集是否存在唯一錐頂點（Beat Apex）。
fn quantale_has_cone_apex(
  k : Int32,
  strict_cone : UInt64,
  cones : Array[UInt64],
) -> Bool {
  if strict_cone == 0UL {
    return false
  }
  for y in 0..<k {
    let y_bit = 1UL << y
    if (strict_cone & y_bit) != 0UL && (strict_cone & cones[y]) == strict_cone {
      return true
    }
  }
  false
}

///|
/// Stong–Quillen Alexandrov 偏序集可縮纖維（Up-Beat / Down-Beat Points）位並行強形變收縮
/// （整合 `alge1/topos::contractible_reduction` 與 `alge2/vect_top_topos::AlexandrovSpace::homotopy_core_mask`）：
/// 對格 `L`（或真部 `L \ {⊥, ⊤}`）迭代消去所有具唯一上錐頂或唯一下錐頂的可縮節點，
/// 返回同倫極小核（Homotopy Core）的 64-bit 存活位元遮罩。
pub fn ClosureQuantale::alexandrov_homotopy_core_mask(
  self : ClosureQuantale,
  proper_only : Bool,
) -> UInt64 {
  let m = self.size()
  let nodes : Array[Int32] = []
  for i in 0..<m {
    if proper_only && (i == self.bot() || i == self.top()) {
      continue
    }
    nodes.push(i)
  }
  let k = nodes.length()
  if k <= 0 || k > 62 {
    return 0UL
  }
  let upset = Array::make(k, 0UL)
  let downset = Array::make(k, 0UL)
  for u in 0..<k {
    for v in 0..<k {
      if self.is_le(nodes[u], nodes[v]) {
        upset[u] = upset[u] | (1UL << v)
        downset[v] = downset[v] | (1UL << u)
      }
    }
  }
  let mut active = (1UL << k) - 1UL
  let mut changed = true
  while changed {
    changed = false
    for x in 0..<k {
      let x_bit = 1UL << x
      if (active & x_bit) != 0UL {
        let not_x = x_bit.lnot()
        let strict_up = upset[x] & active & not_x
        let strict_down = downset[x] & active & not_x
        let is_beat = quantale_has_cone_apex(k, strict_up, upset) ||
          quantale_has_cone_apex(k, strict_down, downset)
        if is_beat {
          active = active & not_x
          changed = true
        }
      }
    }
  }
  active
}

///|
/// Rota–Leinster 偏序集莫比烏斯反演歐拉示性數 `χ_Möbius = ∑_{x ≼ y} μ(x, y)`
/// （整合 `alge2/vect_top_topos::euler_characteristic_on_mask`）：
/// 定理（Rota–Quillen）：對任意有限偏序集（及其 Beat 收縮同倫核），莫比烏斯反演歐拉示性數
/// 恆等於其 Folkman–Quillen 階複形單純同調的歐拉示性數 `order_complex(proper_only).euler()`！
pub fn ClosureQuantale::mobius_euler_characteristic(
  self : ClosureQuantale,
  proper_only : Bool,
  use_homotopy_core : Bool,
) -> Int32 {
  let m = self.size()
  let nodes : Array[Int32] = []
  for i in 0..<m {
    if proper_only && (i == self.bot() || i == self.top()) {
      continue
    }
    nodes.push(i)
  }
  let k = nodes.length()
  if k <= 0 || k > 62 {
    return 0
  }
  let mask = if use_homotopy_core {
    self.alexandrov_homotopy_core_mask(proper_only)
  } else {
    (1UL << k) - 1UL
  }
  let mu = Array::make(k * k, 0)
  for i in 0..<k {
    if (mask & (1UL << i)) != 0UL {
      mu[i * k + i] = 1
    }
  }
  for x in 0..<k {
    if (mask & (1UL << x)) == 0UL {
      continue
    }
    for y in (x + 1)..<k {
      if (mask & (1UL << y)) != 0UL && self.is_le(nodes[x], nodes[y]) {
        let mut s = 0
        for z in x..<y {
          if (mask & (1UL << z)) != 0UL &&
            self.is_le(nodes[x], nodes[z]) &&
            self.is_le(nodes[z], nodes[y]) {
            s = s + mu[x * k + z]
          }
        }
        mu[x * k + y] = -s
      }
    }
  }
  let mut chi = 0
  for x in 0..<k {
    if (mask & (1UL << x)) != 0UL {
      for y in x..<k {
        if (mask & (1UL << y)) != 0UL && self.is_le(nodes[x], nodes[y]) {
          chi = chi + mu[x * k + y]
        }
      }
    }
  }
  chi
}
