# `bench/` — 多領域同調、代數與立方體單價基準測試與展示入口（Benchmark & Executable Showcase）

本資料夾為 `alge3` / `moon-unified` 的可執行主程式入口，串聯位並行 $\mathbb{F}_2$ 線性代數、單純複形同調、持久同調、么半群分類空間 Bar 同調、$A_\infty$/$E_\infty$/VOA、ADE 奇點 Milnor/Tjurina 數、箭圖 $\mathrm{Ext}^1$ 與立方體單價計算進行端到端基準驗證與輸出展示。

---

## 檔案清單與所含定理／演算法／公理

### 1. `main.mbt`
| 區塊 | 所呼叫與展示的演算法／定理 | 說明 |
| :--- | :--- | :--- |
| **Part 1 (`core`)** | 64-bit 位並行 $\mathbb{F}_2$ 高斯消去與持久同調條碼 | 計算隨機與結構化布林矩陣的秩、核空間維數及濾過複形的誕生—死亡配對。 |
| **Part 2 (`homotopy`)** | 環面 $T^2$、實射影平面 $\mathbb{R}P^2$ 單純同調與循環群 Bar 同調 | 輸出 $\beta(T^2) = [1, 2, 1]$、$\beta(\mathbb{R}P^2) = [1, 1, 0]$（特徵 2）與 $H_*(B\mathbb{Z}/2\mathbb{Z}; \mathbb{F}_2)$。 |
| **Part 3 (`algebra`)** | Stasheff $A_\infty$ 恆等式、Steenrod $\smile_i$ 平方、自由樹 Monad 與海森堡 VOA 正規序 | 執行高階同倫結合律與 PBW 正規序基準檢查。 |
| **Part 4 (`derived`)** | Arnold ADE 奇點（$A_k, D_k, E_6, E_7, E_8$）之 $\mu = \tau$ 定理與 Dynkin 箭圖 Euler–Ringel 形式 | 輸出各奇點的 Milnor/Tjurina 維數與箭圖表示的 $\dim \mathrm{Hom} - \dim \mathrm{Ext}^1$。 |
| **Part 5 (`cubical`)** | CCHM 立方體 Kan 盒子填補 `comp` 與對稱群 $S_n$ 單價路徑計算律 $\mathrm{ua}_\beta$ | 對排列雙射構造 `ua(e)` 並以 `transp_line` 驗證計算性單價歸約。 |
