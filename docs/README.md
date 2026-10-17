# `docs/` — 數學原理論文與立方體單價理論技術文件（Mathematical Papers & Technical Documentation）

本資料夾收錄 `alge3` 體系的兩篇完整數學與演算法設計文檔（提供 Markdown 原稿與排版後 HTML 版本），詳述各模組的公理、定理證明與複雜度分析。

---

## 檔案清單與所含定理／演算法／公理

### 1. `paper.md` / `paper.html`
- **《Bit-Parallel Homological Algebra, Higher Operadic Structures, and Derived Deformation Theory in MoonBit》**：
  1. **位並行同調代數**：64-bit 字並行高斯—約當消去、秩—零化度定理、鏈複形 Euler–Poincaré 公式與 Edelsbrunner–Letscher–Zomorodian 持久同調歸約演算法；
  2. **單純神經與跨距推拉**：抽象單純複形、么半群分類空間 $BM$ 的正規化 Bar 解消與有限跨距（Span）的拉回—推前積分函子性；
  3. **高階同倫代數**：Stasheff $A_\infty$ 結合多面體恆等式、Steenrod $\smile_i$ 高階杯積餘邊界定理、Beck 分配律與海森堡頂點算子代數 PBW 正規序；
  4. **導出形變與箭圖表示**：Saito 加權齊次奇點 $\mu = \tau$ 定理（ADE 分類）與遺傳箭圖代數的標準雙項投射分解及 Euler–Ringel 同調雙線性形式。

### 2. `cubical.md` / `cubical.html`
- **《Algorithmic Univalence via Finite Cubical Presheaves》**：
  1. **De Morgan 區間代數 $\mathbb{I}$ 與餘纖維分類格**：連接運算 $\wedge, \vee$、對合 $1-i$ 與餘纖維外延布林向量判定；
  2. **立方體集合預層與依賴路徑 `PathP`**：三進制面索引分解、反變函子公理與函數外延性；
  3. **Kan 開放盒子填補 `comp` 與宇宙黏合 `Glue`**：證明當在端點餘纖維 $(i=0) \vee (i=1)$ 上構造 $\mathrm{ua}(e)$ 時，沿區間的 Kan 搬運 $\mathrm{transp\_line}(\mathrm{ua}(e), a)$ 必由逆雙射扭轉唯一收斂至 $e(a)$（計算性單價定理）。
