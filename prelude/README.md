# `prelude/` — Why3 形式化驗證器之 MoonBit 內建型別公理前導庫（Why3 Formal Verification Prelude for MoonBit Builtins）

本資料夾提供將 MoonBit 程式透過 `prove.sh` 送入 **Why3 / Alt-Ergo / Z3** 自動定理證明器進行形式化驗證時所需的 WhyML（`.mlw`）底層公理定義。

---

## 檔案清單與所含定理／演算法／公理

### 1. `moonbit_builtin_prelude.mlw`
| 模組／公理區塊 | 形式化邏輯公理（WhyML Axioms & Theories） | 說明 |
| :--- | :--- | :--- |
| `Moonbit_Int32` / `Moonbit_Int64` | **機器整數算術與歐幾里得整除公理（Machine Integer & Euclidean Division Axioms）** | 載入整數環 $(\mathbb{Z}, +, -, \times)$ 與帶餘除法 `div`, `mod` 公理，供證明器推導迴圈不變量（Loop Invariants）與模算術後置條件。 |
| `Moonbit_Array` | **一階陣列外延與讀寫公理（McCarthy Select–Store Array Axioms）** | 定義陣列長度非負公理 `length a >= 0` 與讀寫公理 `get (set a i v) j = if i = j then v else get a j`，支撐矩陣與多項式演算法的邊界安全與正確性證明。 |
