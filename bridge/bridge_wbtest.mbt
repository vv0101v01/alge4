// 跨庫整合白盒測試：驗證 algo (moon-algebra) 與 alge3 (moonmath 3.1) 五大橋接定理。

///|
test "Bridge 1: @linalg.Matrix (𝔽_2) ⇄ @core.BoolMat rank, matmul & fp_det agreement" {
  let rows1 : Array[Array[Int32]] = [
    [1, 0, 1, 1],
    [0, 1, 1, 0],
    [1, 1, 0, 1],
    [1, 0, 1, 0],
  ]
  let rows2 : Array[Array[Int32]] = [
    [1, 1, 0, 0],
    [0, 1, 1, 1],
    [1, 0, 1, 0],
    [0, 1, 0, 1],
  ]
  let m1 = @linalg.Matrix::from_rows(2, rows1)
  let m2 = @linalg.Matrix::from_rows(2, rows2)
  let bm1 = matrix_to_boolmat(m1)
  let bm2 = matrix_to_boolmat(m2)
  // 位並行 rank 與 RREF rank 完全一致
  assert_eq(m1.rank(), @core.rank_mat(bm1))
  assert_eq(m2.rank(), @core.rank_mat(bm2))
  // 位並行乘法與 F_2 矩陣乘法完全一致
  let prod_linalg = m1.mul(m2)
  let prod_bool = boolmat_to_matrix(bm1.mul(bm2))
  for i in 0..<4 {
    for j in 0..<4 {
      assert_eq(prod_linalg.get(i, j), prod_bool.get(i, j))
    }
  }
  // 行列式與滿秩判準在 𝔽_7 上一致
  let m7 = @linalg.Matrix::from_rows(7, [[1, 2, 3], [0, 4, 5], [0, 0, 6]])
  assert_eq(matrix_det(m7), @num.mod_pos(24, 7))
  assert_eq(m7.rank(), 3)
}

///|
test "Bridge 2: @hott.Equiv & CRT isomorphism → @cubical.ua (Glue + comp univalence)" {
  // 1) 將 @hott 的等價送入 @cubical.ua 並驗證 ua-beta 與 ua-eta
  let e_rot : @hott.Equiv[Int32, Int32] = @hott.Equiv::{
    fwd: fn(x : Int32) { @num.mod_pos(x + 1, 4) },
    bwd: fn(y : Int32) { @num.mod_pos(y - 1, 4) },
  }
  assert_true(
    e_rot.is_equiv_finite((a, b) => a == b, (a, b) => a == b, [0, 1, 2, 3], [
      0, 1, 2, 3,
    ]),
  )
  match equiv_to_iso(e_rot, 4) {
    Some(iso) => {
      assert_true(@cubical.check_ua_beta(iso))
      let line = @cubical.ua(iso)
      assert_true(@cubical.check_ua_eta(line))
      let back = iso_to_equiv(iso)
      for x in 0..<4 {
        assert_eq((back.fwd)(x), (e_rot.fwd)(x))
      }
    }
    None => abort("expected valid Iso from Equiv")
  }
  // 2) 中國剩餘定理 ℤ/6ℤ ≃ ℤ/2ℤ × ℤ/3ℤ 誘導的立方體單價路徑 ua(crt_iso)
  assert_true(@hott.crt_equiv_holds(6))
  match crt_cubical_iso(6) {
    Some(crt6) => {
      assert_true(@cubical.check_ua_beta(crt6))
      let ua_crt = @cubical.ua(crt6)
      assert_true(@cubical.check_ua_eta(ua_crt))
      // 沿 CRT 單價線 transport 每個殘基 x ∈ ℤ/6ℤ 嚴格等於混合進制 CRT 座標
      for x in 0..<6 {
        assert_eq(@cubical.transport_path(ua_crt, x), Some(crt6.apply(x)))
      }
    }
    None => abort("expected valid CRT Iso for n=6")
  }
}

///|
test "Bridge 3: Gröbner basis Milnor/Tjurina algebra ⇄ @derived weighted singularity invariants" {
  // ADE 奇點於 𝔽_5：A_2 (x³ + y²), A_3 (x⁴ + y²), D_4 (x³ + xy²)
  // 1) A_2: f = x^3 + y^2 over 𝔽_5 → μ = τ = 2
  let a2_poly = @poly.poly_of_terms(2, 5, [(1, [3, 0]), (1, [0, 2])])
  let a2_der = poly_to_derived(a2_poly)
  let mu_derived_a2 = @derived.milnor_number(a2_der, [2, 3], 5, 12)
  let tau_derived_a2 = @derived.tjurina_number(a2_der, [2, 3], 5, 12)
  assert_eq(groebner_milnor_number(a2_poly), Some(mu_derived_a2))
  assert_eq(groebner_tjurina_number(a2_poly), Some(tau_derived_a2))
  assert_eq(mu_derived_a2, 2)
  // 構造 A_2 的 Milnor 代數 M(f) = 𝔽_5[x,y]/(3x², 2y) ≅ 𝔽_5[x]/(x²)，驗證其為局部 Artin 環
  let m_a2 = groebner_milnor_algebra(a2_poly)
  assert_true(m_a2.validate())
  assert_eq(m_a2.dim, 2)
  assert_true(@finite.is_local(m_a2))
  assert_false(@finite.is_reduced(m_a2))
  assert_eq(@finite.socle(m_a2).members.length(), 5)
  // 2) D_4: f = x^3 + x*y^2 over 𝔽_7 → μ = τ = 4
  let d4_poly = @poly.poly_of_terms(2, 7, [(1, [3, 0]), (1, [1, 2])])
  let d4_der = poly_to_derived(d4_poly)
  let mu_derived_d4 = @derived.milnor_number(d4_der, [2, 2], 7, 12)
  assert_eq(groebner_milnor_number(d4_poly), Some(mu_derived_d4))
  assert_eq(mu_derived_d4, 4)
  // 往返轉換保持多項式規範形
  assert_eq(derived_to_poly(d4_der, 2, 7), d4_poly)
}

///|
test "Bridge 4: @finite.FinAlg unit group & monoid → @homotopy.Monoid nerve & bar homology" {
  // 1) 對偶數環 R = 𝔽_2[x]/(x²) 的可逆元群 R^× = {1, 1+x} ≅ ℤ/2ℤ
  //    其分類空間 B(R^×) = B(ℤ/2ℤ) 在 𝔽_2 係數下各度 Betti 數恆為 1
  let dual = @finite.FinAlg::univariate_quotient(2, [0, 0, 1])
  let m_mul = finalg_mul_monoid(dual)
  assert_true(m_mul.is_associative())
  assert_true(m_mul.is_unital())
  let u_dual = finalg_unit_group_monoid(dual)
  assert_eq(u_dual.n, 2)
  assert_true(u_dual.is_associative())
  assert_true(u_dual.is_unital())
  assert_eq(@homotopy.bar_betti(u_dual, 4), [1, 1, 1, 1, 1])
  // 2) 四元域 𝔽_4 = 𝔽_2[x]/(x²+x+1) 的可逆元群 𝔽_4^× ≅ ℤ/3ℤ
  //    3 在 𝔽_2 可逆 ⇒ 正度同調全為 0
  let f4 = @finite.FinAlg::univariate_quotient(2, [1, 1, 1])
  let u_f4 = finalg_unit_group_monoid(f4)
  assert_eq(u_f4.n, 3)
  assert_eq(@homotopy.bar_betti(u_f4, 4), [1, 0, 0, 0, 0])
}

///|
test "Bridge 5: @finite.FinAlg (p=2) → @algebra.AInf Stasheff identities & Spec/Geometry/Module bridge" {
  // 𝔽_2[x]/(x³) 既可由 @finite.FinAlg 構造，也可嵌入為 @algebra.AInf 並通過全部 Stasheff 檢驗
  let r_x3 = @finite.FinAlg::univariate_quotient(2, [0, 0, 0, 1])
  let ainf = finalg_to_ainf_dga(r_x3)
  assert_true(ainf.check_all())
  let f4 = @finite.FinAlg::univariate_quotient(2, [1, 1, 1])
  let ainf_f4 = finalg_to_ainf_dga(f4)
  assert_true(ainf_f4.check_all())
  // Spec Zariski 開集位元外延重量 == open_count()
  let prod = @finite.FinAlg::product(3, [1, 1])
  let sp = @scheme.spec(prod)
  assert_eq(spec_opens_bits(sp).weight(), sp.open_count())
  // 尖點曲線 y² − x³ 於 𝔽_5 原點奇異，其 Milnor 代數自由模自對偶維數 = μ = 2
  let cusp = @poly.poly_of_terms(2, 5, [(1, [0, 2]), (4, [3, 0])])
  assert_eq(singularity_milnor_module_dim(cusp, 100), 2)
}
