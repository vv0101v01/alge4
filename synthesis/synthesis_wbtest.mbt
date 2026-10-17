// =============================================================================
// 合成新演算法白盒驗證套件（Assertion + QuickCheck Property Tests）
// 驗證 ClosureQuantale + PosetPresheaf + kan_sheaf_solve + glue_presheaf 四階段演算法
// =============================================================================

///|
test "Stage I & II: ClosureQuantale unifies ideal lattices, radicals, conductors, socle & Wedderburn blocks" {
  // 1) 四元域 𝔽_4 = 𝔽_2[x]/(x²+x+1)
  let f4 = @finite.FinAlg::univariate_quotient(2, [1, 1, 1])
  let q_f4 = ClosureQuantale::from_finalg(f4)
  assert_eq(q_f4.size(), @finite.enumerate_ideals(f4).length())
  assert_eq(q_f4.atoms().length(), @finite.simple_ideals(f4).length())
  assert_eq(q_f4.coatoms().length(), @finite.maximal_ideals(f4).length())
  assert_eq(q_f4.quantale_primes().length(), @finite.prime_ideals(f4).length())
  assert_true(q_f4.is_complemented_lattice())
  assert_eq(q_f4.krull_dimension(), @finite.krull_dim(f4))

  // 2) 對偶數局部環 𝔽_2[x]/(x²)
  let x2 = @finite.FinAlg::univariate_quotient(2, [0, 0, 1])
  let q_x2 = ClosureQuantale::from_finalg(x2)
  assert_eq(q_x2.size(), 3)
  assert_eq(q_x2.longest_chain_len(), @finite.longest_ideal_chain(x2))
  assert_eq(q_x2.nilradical_id(), q_x2.jacobson_id())
  assert_eq(q_x2.closed[q_x2.nilradical_id()].weight(), 2)
  assert_eq(q_x2.closed[q_x2.socle_id()].weight(), @finite.socle(x2).members.length())
  assert_false(q_x2.is_complemented_lattice())
  assert_false(q_x2.is_semiprime_id(q_x2.bot()))
  assert_true(q_x2.is_semiprime_id(q_x2.nilradical_id()))

  // 3) 半單直積環 𝔽_3 × 𝔽_3
  let f3x3 = @finite.FinAlg::univariate_quotient(3, [2, 0, 1])
  let q_f3x3 = ClosureQuantale::from_finalg(f3x3)
  assert_eq(q_f3x3.size(), 4)
  assert_true(q_f3x3.is_complemented_lattice())
  assert_eq(q_f3x3.boolean_center_atoms().length(), @finite.primitive_idempotents(f3x3).length())
  assert_eq(q_f3x3.minimal_primes().length(), @scheme.spec(f3x3).irreducible_components().length())

  // 4) 尖點非正則局部環 𝔽_5[x,y]/(x², xy, y²)
  let cusp = @finite.FinAlg::zero_dim_quotient(5, [
    @poly.poly_of_terms(2, 5, [(1, [2, 0])]),
    @poly.poly_of_terms(2, 5, [(1, [1, 1])]),
    @poly.poly_of_terms(2, 5, [(1, [0, 2])]),
  ])
  let q_cusp = ClosureQuantale::from_finalg(cusp)
  assert_eq(q_cusp.size(), 9)
  assert_eq(q_cusp.atoms().length(), 6) // 6 條極小單純理想線
  assert_eq(q_cusp.coatoms().length(), 1) // 唯一極大理想 m = (x, y)
  assert_eq(q_cusp.longest_chain_len(), 4)
  let m_id = q_cusp.coatoms()[0]
  assert_eq(q_cusp.nilradical_id(), m_id)
  assert_eq(q_cusp.jacobson_id(), m_id)
  // 在尖點環中 m² = 0 ⇒ (0 : m) = socle = m，且對任意兩條不同單純理想線 L_1, L_2 有 (L_1 : L_2) = m
  assert_eq(q_cusp.socle_id(), m_id)
  let l1 = q_cusp.atoms()[0]
  let l2 = q_cusp.atoms()[1]
  assert_eq(q_cusp.residual(l1, l2), m_id)
  assert_eq(q_cusp.annihilator_of(l1), m_id)
}

///|
test "Stage I & II: Submodule lattices, Zariski open Frames & Cubical cofibration Heyting adjunction" {
  // 1) 子模格：半單環 𝔽_3×𝔽_3 上的自由模子模格有補；對偶數環 𝔽_2[x]/(x²) 上的自由模子模格無補
  let f3x3 = @finite.FinAlg::univariate_quotient(3, [2, 0, 1])
  let mod_ss = @modules.FinModule::free(f3x3, 1)
  let q_mod_ss = ClosureQuantale::from_finmodule(mod_ss)
  assert_eq(q_mod_ss.size(), @modules.enumerate_submodules(mod_ss).length())
  assert_true(q_mod_ss.is_complemented_lattice())

  let x2 = @finite.FinAlg::univariate_quotient(2, [0, 0, 1])
  let mod_loc = @modules.FinModule::free(x2, 1)
  let q_mod_loc = ClosureQuantale::from_finmodule(mod_loc)
  assert_eq(q_mod_loc.size(), @modules.enumerate_submodules(mod_loc).length())
  assert_false(q_mod_loc.is_complemented_lattice())

  // 2) Zariski 開集 Frame：驗證殘差即 Heyting 蘊涵 c ∧ b ≼ a ⟺ c ≼ (a : b)
  let sp = @scheme.spec(f3x3)
  let q_zar = ClosureQuantale::from_zariski_spec(sp)
  assert_eq(q_zar.size(), sp.open_count())
  for a in 0..<q_zar.size() {
    for b in 0..<q_zar.size() {
      for c in 0..<q_zar.size() {
        assert_eq(
          q_zar.is_le(q_zar.meet(c, b), a),
          q_zar.is_le(c, q_zar.residual(a, b)),
        )
      }
    }
  }

  // 3) 立方體餘纖維外延 Frame（2 維立方體的面格生成元）
  let cofs : Array[@cubical.Cof] = [
    @cubical.face_cof(0, 0),
    @cubical.face_cof(0, 1),
    @cubical.face_cof(1, 0),
    @cubical.face_cof(1, 1),
  ]
  let q_cub = ClosureQuantale::from_cubical_cofs(2, cofs)
  for a in 0..<q_cub.size() {
    for b in 0..<q_cub.size() {
      for c in 0..<q_cub.size() {
        assert_eq(
          q_cub.is_le(q_cub.meet(c, b), a),
          q_cub.is_le(c, q_cub.residual(a, b)),
        )
      }
    }
  }
}

///|
test "Stage II (Emergent Theorem): Folkman–Quillen Order Complex Homology of Algebraic Lattices" {
  // 定理（Folkman–Quillen）：n 元布林代數 B_n = Idl(𝔽_2^n) 的真部 L \ {⊥, ⊤}
  // 是 (n-2)-維球面 S^{n-2} 的重心細分（barycentric subdivision of ∂Δ^{n-1}）！
  // 1) B_3 = Idl(𝔽_2³)：真部同倫於圓 S¹ ⇒ Betti 數 = [1, 1]，Euler 特徵數 = 0
  let b3_alg = @finite.FinAlg::product(2, [1, 1, 1])
  let q_b3 = ClosureQuantale::from_finalg(b3_alg)
  assert_eq(q_b3.size(), 8)
  let cx_b3 = q_b3.order_complex(true)
  assert_eq(cx_b3.count(0), 6) // 3 個原子 + 3 個餘原子
  assert_eq(cx_b3.count(1), 6) // 6 條嚴格包含邊，構成六邊形 S¹
  assert_eq(cx_b3.betti(), [1, 1])
  assert_eq(cx_b3.euler(), 0)

  // 2) B_4 = Idl(𝔽_2⁴)：真部同倫於二維球面 S² ⇒ Betti 數 = [1, 0, 1]，Euler 特徵數 = 2
  let b4_alg = @finite.FinAlg::product(2, [1, 1, 1, 1])
  let q_b4 = ClosureQuantale::from_finalg(b4_alg)
  assert_eq(q_b4.size(), 16)
  let cx_b4 = q_b4.order_complex(true)
  assert_eq(cx_b4.count(0), 14) // 14 個真非空子集
  assert_eq(cx_b4.count(1), 36) // 36 條二元嚴格鏈
  assert_eq(cx_b4.count(2), 24) // 24 條三元嚴格鏈（對應 S_4 的 24 個排列！）
  assert_eq(cx_b4.betti(), [1, 0, 1])
  assert_eq(cx_b4.euler(), 2)

  // 3) 局部環理想格具唯一極大理想 m（錐頂點）⇒ 真部階複形可縮（Contractible）！
  //    尖點環 𝔽_3[x,y]/(x²,xy,y²)：4 條單純理想線匯聚於錐頂 m ⇒ Betti = [1, 0]，χ = 1
  let cusp3 = @finite.FinAlg::zero_dim_quotient(3, [
    @poly.poly_of_terms(2, 3, [(1, [2, 0])]),
    @poly.poly_of_terms(2, 3, [(1, [1, 1])]),
    @poly.poly_of_terms(2, 3, [(1, [0, 2])]),
  ])
  let q_cusp3 = ClosureQuantale::from_finalg(cusp3)
  let cx_cusp3 = q_cusp3.order_complex(true)
  assert_eq(cx_cusp3.betti(), [1, 0])
  assert_eq(cx_cusp3.euler(), 1)
}

///|
test "Stage III: kan_sheaf_solve unifies Cubical comp, Zariski sheaf gluing & InvSystem limit threads" {
  // 1) Cubical 單價：Fin 4 全部 24 個等價的 ua(e) 轉為 PosetPresheaf 後，
  //    kan_sheaf_solve(top=2, lid=1, {0: a}) 逐點重現 transport (ua e) a == e(a)
  for perm in @cubical.all_permutations(4) {
    match @cubical.perm_iso(perm) {
      Some(e) => {
        let ua_ct = @cubical.ua(e)
        let diag = PosetPresheaf::from_cubety(ua_ct)
        assert_true(diag.validate())
        for a in 0..<4 {
          let sys = CoherentPartial::{ stages: [0], vals: [a] }
          match diag.kan_sheaf_solve(2, 1, sys) {
            Some(r) => {
              assert_eq(r.lid, e.apply(a))
              assert_eq(r.filler_count, 1)
              assert_true(r.unique_lid)
            }
            None => abort("expected Kan filler on ua(e)")
          }
        }
      }
      None => abort("expected valid permutation Iso")
    }
  }

  // 2) Zariski 結構層黏合：𝔽_3 × 𝔽_3 在正交冪等元覆蓋 D(1) = D(e_1) ∪ D(e_2) 上
  //    verify_binary_sheaf_gluing 與 @scheme.sheaf_gluing_bijective 完全一致
  let r = @finite.FinAlg::univariate_quotient(3, [2, 0, 1])
  let prims = @finite.primitive_idempotents(r)
  let h = r.one_elem()
  let f = prims[0]
  let g = prims[1]
  assert_true(@scheme.sheaf_gluing_bijective(r, h, f, g))
  match PosetPresheaf::from_zariski_cover(r, h, f, g) {
    Some(z_diag) => {
      assert_true(z_diag.validate())
      assert_true(z_diag.verify_binary_sheaf_gluing(3, 1, 2))
    }
    None => abort("expected valid Zariski cover PosetPresheaf")
  }

  // 3) 連續模逆極限線程：InvSystem 轉為鏈景 PosetPresheaf 後，
  //    extract_limit_threads() 與 inv.limit_threads() 完全一致
  let inv = @modules.InvSystem::{
    sizes: [2, 4, 8],
    bonds: [[0, 1, 0, 1], [0, 1, 2, 3, 0, 1, 2, 3]],
  }
  let p_inv = PosetPresheaf::from_inv_system(inv)
  assert_true(p_inv.validate())
  let threads_kan = p_inv.extract_limit_threads()
  let threads_orig = inv.limit_threads()
  assert_eq(threads_kan.length(), threads_orig.length())
  for i in 0..<threads_kan.length() {
    assert_eq(threads_kan[i], threads_orig[i])
  }
}

///|
test "Stage IV: Algebraic Univalence Transport carries ring multiplication across CRT & Wedderburn isomorphisms" {
  // 將 ℤ/6ℤ 的模 6 乘法表沿中國剩餘定理單價路徑 ua(crt_iso : ℤ/6ℤ ≃ ℤ/2ℤ × ℤ/3ℤ)
  // 用 glue_presheaf + kan_sheaf_solve 自動搬運，驗證所得二元運算表精確等於
  // ℤ/2ℤ × ℤ/3ℤ 的逐分量乘法表！
  let n = 6
  let mul_z6 : Array[Array[Int32]] = []
  for a in 0..<n {
    let row : Array[Int32] = []
    for b in 0..<n {
      row.push(@num.mul_mod(a, b, n))
    }
    mul_z6.push(row)
  }
  let mods : Array[Int32] = [2, 3]
  let bwd = Array::make(n, 0)
  for x in 0..<n {
    let r = @hott.crt_forward(mods, x)
    bwd[r[0] + 2 * r[1]] = x
  }
  let crt_equiv : @hott.Equiv[Int32, Int32] = @hott.Equiv::{
    fwd: fn(x : Int32) {
      let r = @hott.crt_forward(mods, x)
      r[0] + 2 * r[1]
    },
    bwd: fn(code : Int32) { bwd[code] },
  }
  let transported_mul = algebraic_univalence_from_hott_equiv(
    crt_equiv, n, mul_z6,
  )
  for c1 in 0..<n {
    let r1_2 = c1 % 2
    let r1_3 = c1 / 2
    for c2 in 0..<n {
      let r2_2 = c2 % 2
      let r2_3 = c2 / 2
      let expected_code = r1_2 * r2_2 % 2 + 2 * (r1_3 * r2_3 % 3)
      assert_eq(transported_mul[c1][c2], expected_code)
    }
  }
}

///|
test "property: ClosureQuantale satisfies residuated Galois adjunction (a · b ≼ c ⟺ a ≼ (c : b))" {
  @quickcheck.check((seed : Int32) => {
    let s = @num.mod_pos(seed, 10000)
    let ps : Array[Int32] = [2, 3]
    let p = ps[@num.mod_pos(s, 2)]
    let c0 = @num.mod_pos(s / 2, p)
    let c1 = @num.mod_pos(s / 7, p)
    let alg = @finite.FinAlg::univariate_quotient(p, [c0, c1, 1])
    let q = ClosureQuantale::from_finalg(alg)
    let m = q.size()
    let mut ok = true
    for a in 0..<m {
      for b in 0..<m {
        for c in 0..<m {
          let lhs = q.is_le(q.mul(a, b), c)
          let rhs = q.is_le(a, q.residual(c, b))
          if lhs != rhs {
            ok = false
          }
        }
      }
    }
    ok
  })
}
