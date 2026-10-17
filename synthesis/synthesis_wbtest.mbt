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
test "Stage I & II (Upgraded across alge/alge1/alge2): Topos modalities, cotangent edim & Alexandrov–Möbius–Quillen Euler identity" {
  // 1) 餘切嵌入維數 edim = dim_k(m/m²) 與正則局部環判準（整合 alge/quot & alge/ga）
  let f4 = @finite.FinAlg::univariate_quotient(2, [1, 1, 1])
  let q_f4 = ClosureQuantale::from_finalg(f4)
  assert_true(q_f4.is_local_quantale())
  assert_eq(q_f4.embedding_dimension(2), 0)
  assert_true(q_f4.is_regular_local(2))

  let x2 = @finite.FinAlg::univariate_quotient(2, [0, 0, 1])
  let q_x2 = ClosureQuantale::from_finalg(x2)
  assert_true(q_x2.is_local_quantale())
  assert_eq(q_x2.embedding_dimension(2), 1)
  assert_false(q_x2.is_regular_local(2))

  let cusp = @finite.FinAlg::zero_dim_quotient(5, [
    @poly.poly_of_terms(2, 5, [(1, [2, 0])]),
    @poly.poly_of_terms(2, 5, [(1, [1, 1])]),
    @poly.poly_of_terms(2, 5, [(1, [0, 2])]),
  ])
  let q_cusp = ClosureQuantale::from_finalg(cusp)
  assert_true(q_cusp.is_local_quantale())
  assert_eq(q_cusp.embedding_dimension(5), 2) // dim_{𝔽_5}(m/m²) = 2（胖點尖點環）
  assert_false(q_cusp.is_regular_local(5))

  // 2) Topos 雙重否定 Lawvere–Tierney 模態 ○_{¬¬} 與 Kripke–Joyal 強制（整合 alge1/topos & alge2/vect_top_topos）
  let b3_alg = @finite.FinAlg::product(2, [1, 1, 1])
  let q_b3 = ClosureQuantale::from_finalg(b3_alg)
  for a in 0..<q_b3.size() {
    // 在布林格上雙重否定模態恆等於自身：¬¬a == a
    assert_eq(q_b3.lawvere_tierney_dense(a), a)
    let impl_aa = q_b3.heyting_implication(a, a)
    assert_eq(impl_aa, q_b3.top())
    assert_true(q_b3.kripke_joyal_forces(a, impl_aa))
  }

  // 3) Stong–Quillen Alexandrov Beat 收縮同倫核與 Rota–Leinster 莫比烏斯反演歐拉示性數恆等式：
  //    χ_Möbius(L \ {⊥,⊤}) == χ_Simplicial(Δ(L \ {⊥,⊤}))
  assert_eq(
    q_b3.mobius_euler_characteristic(true, false),
    q_b3.order_complex(true).euler(),
  )
  assert_eq(
    q_b3.mobius_euler_characteristic(true, true),
    q_b3.order_complex(true).euler(),
  )
  let b4_alg = @finite.FinAlg::product(2, [1, 1, 1, 1])
  let q_b4 = ClosureQuantale::from_finalg(b4_alg)
  assert_eq(
    q_b4.mobius_euler_characteristic(true, false),
    q_b4.order_complex(true).euler(),
  )
  // 局部環真部具唯一錐頂 m ⇒ Alexandrov Beat 收縮將整個真部收縮為單一頂點（popcnt == 1，χ == 1）！
  let core_cusp = q_cusp.alexandrov_homotopy_core_mask(true)
  assert_eq(core_cusp.popcnt(), 1)
  assert_eq(q_cusp.mobius_euler_characteristic(true, true), 1)
}

///|
test "Stage V (Algebraic Geometry): ZeroCostTensorAlg, Newton precision-doubling & Character–Point Hom-Bijection" {
  // 1) 截斷離散賦值環（落特環）𝔽_5[[t]]/(t⁴)：驗證張量環公理、Newton 倍增求逆與平方根（整合 alge/val）
  let dvr = ZeroCostTensorAlg::from_truncated_dvr(5, 4)
  assert_true(dvr.verify_tensor_ring_axioms())
  // a = 4 + 2t + t² + 3t³ ∈ (𝔽_5[[t]]/(t⁴))^×
  let a : Array[Int32] = [4, 2, 1, 3]
  assert_eq(dvr.t_adic_valuation(a), 0)
  match dvr.newton_inv(a) {
    Some(inv_a) => assert_eq(dvr.mul(a, inv_a), dvr.one())
    None => abort("expected Newton inverse in truncated DVR")
  }
  match dvr.newton_sqrt(a) {
    Some(sqrt_a) => assert_eq(dvr.mul(sqrt_a, sqrt_a), a)
    None => abort("expected Newton square root in truncated DVR")
  }

  // 2) 半單エタール座標環 A = 𝔽_5[x]/(x(x-1)(x-2)) = 𝔽_5[x]/(2x - 3x² + x³)
  //    驗證代數幾何核心態雙射 Hom_{𝔽_5-Alg}(A, 𝔽_5) ≃ V(I) = {0, 1, 2} 與拉格朗日正交冪等元（整合 alge/quot & alge/ga）
  let cubic_alg = @finite.FinAlg::univariate_quotient(5, [0, 2, 2, 1])
  let t_cubic = ZeroCostTensorAlg::from_finalg(cubic_alg)
  assert_true(t_cubic.verify_tensor_ring_axioms())
  let pts : Array[Array[Int32]] = [[0], [1], [2]]
  assert_true(t_cubic.verify_character_point_hom_bijection(pts))
  match t_cubic.lagrange_primitive_idempotents(pts) {
    Some(idems) => {
      assert_eq(idems.length(), 3)
      let mut sum_idem = t_cubic.zero()
      for r in 0..<3 {
        sum_idem = t_cubic.add(sum_idem, idems[r])
        // 冪等性 e_r² == e_r
        assert_eq(t_cubic.mul(idems[r], idems[r]), idems[r])
        for s in 0..<3 {
          let expected = if r == s { 1 } else { 0 }
          assert_eq(t_cubic.eval_at_point(idems[r], pts[s]), expected)
          if r != s {
            assert_eq(t_cubic.mul(idems[r], idems[s]), t_cubic.zero())
          }
        }
      }
      assert_eq(sum_idem, t_cubic.one())
    }
    None => abort("expected Lagrange primitive idempotents")
  }
}

///|
test "Stage VI (Category Theory): Coyoneda Hom-Bijection, Univalent Skeleton, Curried Kronecker & Chu MLL Proof Net" {
  // 1) 自由—遺忘伴隨泛同態倍增與餘米田融合流（整合 alge1/functor & alge2/functors）
  let word : Array[Int32] = [0, 1, 0, 2]
  let gen_a : Array[Int64] = [3L, 5L, 7L]
  let gen_b : Array[Int64] = [2L, 1L, 4L]
  let m = 998244353L
  let (fast_a, fast_b) = free_monoid_affine_hom_power(word, gen_a, gen_b, 25L, m)
  let mut naive_x = 42L
  for _rep in 0..<25 {
    for g in word {
      naive_x = (gen_a[g] * naive_x + gen_b[g]) % m
    }
  }
  assert_eq((fast_a * 42L + fast_b) % m, naive_x)

  // 2) 單價座標環骨架快速冪 vs 張量直接連乘（驗證 ua(eval)^{-1}·ua(eval) = refl 消除中間逆變換）
  let cubic_alg = @finite.FinAlg::univariate_quotient(5, [0, 2, 2, 1])
  let t_cubic = ZeroCostTensorAlg::from_finalg(cubic_alg)
  let pts : Array[Array[Int32]] = [[0], [1], [2]]
  let elem : Array[Int32] = [1, 2, 3]
  match tensor_alg_univalent_skeleton_power(t_cubic, pts, elem, 11) {
    Some(sk_pow) => {
      let mut direct = t_cubic.one()
      for _ in 0..<11 {
        direct = t_cubic.mul(direct, elem)
      }
      assert_eq(sk_pow, direct)
    }
    None => abort("expected skeleton power")
  }

  // 3) Walsh–Hadamard 單價骨架 XOR 捲積鏈
  let v1 : Array[Int64] = [1L, 2L, 3L, 4L]
  let v2 : Array[Int64] = [4L, 3L, 2L, 1L]
  let conv = fwht_univalent_convolution_chain([v1, v2])
  let expected_xor = Array::make(4, 0L)
  for i in 0..<4 {
    for j in 0..<4 {
      expected_xor[i ^ j] = expected_xor[i ^ j] + v1[i] * v2[j]
    }
  }
  assert_eq(conv, expected_xor)

  // 4) 張量—Hom 柯里化 Kronecker 作用 vs @linalg.kronecker_product 實化矩陣作用
  let m1 = @linalg.Matrix::from_rows(5, [[1, 2], [3, 4]])
  let m2 = @linalg.Matrix::from_rows(5, [[2, 0], [1, 3]])
  let state : Array[Int32] = [1, 2, 3, 4]
  let curried_res = kronecker_curried_apply_matrices([m1, m2], state)
  let full_kron = kronecker_product_matrix(m1, m2)
  let direct_res : Array[Int32] = []
  for r in 0..<4 {
    let mut s = 0
    for c in 0..<4 {
      s = @num.mod_pos(s + full_kron.data[r][c] * state[c], 5)
    }
    direct_res.push(s)
  }
  assert_eq(curried_res, direct_res)

  // 5) Beck–Chevalley 同倫拉回跨距縮並 & Danos–Regnier Chu MLL 證明網檢驗
  let r1 : Array[(Int32, Int32, Int64)] = [(0, 1, 2L), (1, 1, 3L)]
  let r2 : Array[(Int32, Int32, Int64)] = [(1, 2, 4L)]
  let r3 : Array[(Int32, Int32, Int64)] = [(2, 0, 5L), (2, 3, 1L)]
  assert_eq(beck_chevalley_span_contraction(r1, r2, r3, 4), (2L + 3L) * 4L * (5L + 1L))
  assert_true(
    verify_chu_mll_proof_net(4, [(0, 1), (2, 3)], [(1, 2, 3)]),
  )
}

///|
test "Stage VII (Homotopical Algebra, Derived Geometry & 2-Groups): BitParallelSDR + HPL + Kadeishvili A_∞, ADE Singularity & 3D Kan Holonomy" {
  // 1) 位並行強形變收縮（SDR）、同調微擾引理（HPL）與 Kadeishvili A_∞ 轉移至 @algebra.AInf
  //    構造 3 維鏈複形 V = span{e_0, e_1, e_2}（其中 d_V(e_1) = e_2，H = span{e_0} 為 1 維同調核）
  let d_v = @core.BoolMat::zero(3, 3)
  d_v.rows[2].set(1) // d_V(e_1) = e_2
  let d_h = @core.BoolMat::zero(1, 1)
  let inj_i = @core.BoolMat::zero(3, 1)
  inj_i.rows[0].set(0) // i(h_0) = e_0
  let proj_p = @core.BoolMat::zero(1, 3)
  proj_p.rows[0].set(0) // p(e_0) = h_0
  let homotopy_h = @core.BoolMat::zero(3, 3)
  homotopy_h.rows[1].set(2) // h(e_2) = e_1 ⇒ d_V h + h d_V 在 span{e_1, e_2} 上為恆等！
  let sdr = BitParallelSDR::{
    dim_v: 3,
    dim_h: 1,
    d_v,
    d_h,
    inj_i,
    proj_p,
    homotopy_h,
  }
  assert_true(sdr.verify_axioms())
  // 微擾 HPL 檢驗（取零微擾或冪零微擾仍保持 SDR 七大公理）
  let delta = @core.BoolMat::zero(3, 3)
  let sdr_pert = sdr.perturb_via_hpl(delta, 4)
  assert_true(sdr_pert.verify_axioms())
  // Kadeishvili A_∞ 轉移：在 V 上定義單位元乘法 e_0 · e_k = e_k，轉移至 H 上生成 @algebra.AInf 並驗證全部 Stasheff 恆等式！
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
  assert_true(ainf.check_all())

  // 2) 導出代數幾何：Arnold E_6 奇點 f = x³ + y⁴（權重 w = (4, 3), maxdeg = 12）
  //    驗證 Saito 定理 μ = τ = 6 與 Serre 導出相交歐拉示性數
  let e6_poly = @derived.poly_of([([3, 0], 1), ([0, 4], 1)])
  let prof = analyze_derived_singularity(e6_poly, [4, 3], 101, 12, 2, 1, 3, 0)
  assert_eq(prof.milnor_mu, 6)
  assert_eq(prof.tjurina_tau, 6)
  assert_true(prof.is_quasi_homogeneous_saito)
  assert_true(prof.is_quasi_smooth_lci)
  assert_eq(prof.naive_tor0_multiplicity, 3)
  assert_eq(prof.serre_derived_euler_multiplicity, 0) // 退化相交 Tor_0 - Tor_1 = 3 - 3 = 0

  // 3) 非交換 1-群胚平行移動、2-群交叉模交換律與 3D 立方體 Kan 盒子填補全純性
  let g1 = DihedralGauge::new(1, -1, 6)
  let g2 = DihedralGauge::new(2, 1, 6)
  let g3 = DihedralGauge::new(3, -1, 6)
  let gpoid = PathCompressedGroupoid::new(4, 6)
  assert_true(gpoid.add_reversible_morphism(0, 1, g1))
  assert_true(gpoid.add_reversible_morphism(1, 2, g2))
  match gpoid.parallel_transport(0, 2) {
    Some(t02) => assert_true(t02.same(g1.mul(g2)))
    None => abort("expected parallel transport in groupoid")
  }
  let id6 = DihedralGauge::id(6)
  let c00 = CrossedModule2Cell::{ surface_e: id6, source_g: g1 }
  let c01 = CrossedModule2Cell::{ surface_e: id6, source_g: g2 }
  let c10 = CrossedModule2Cell::{ surface_e: g2, source_g: g1 }
  let c11 = CrossedModule2Cell::{ surface_e: g3, source_g: g2 }
  assert_true(verify_2group_exchange_law(c00, c01, c10, c11))
  assert_true(verify_cubical_kan_fill_3d_gauge(g1, g2, g3, g1, g2, g3))
  let loop_code = hit_bg_encode_word(6, [(g1, false), (g2, false), (g2, true)])
  assert_true(loop_code.same(g1))
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
