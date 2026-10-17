# `port/` — 跨語言代數代碼自動遷移與 AST 重寫映射模組（Algebraic Code Porting & AST Pattern Translation）

本資料夾實現從舊版或外部命令式代數偽代碼／腳本向正規化 MoonBit 代數 API 的自動語法轉換、識別符正規化與規則重寫管線。

---

## 檔案清單與所含定理／演算法／公理

### 1. `port.mbt`
| 函數／結構 | 演算法／形式化規則 | 說明 |
| :--- | :--- | :--- |
| `PortRule` / `apply_port_rules` | **決定性優先序樣式重寫演算法（Deterministic Term/String Rewriting）** | 依規則表將外部代數算子與關鍵字映射為 `moon-algebra` 標準 API 呼叫，保證單步與多步轉換的確定性與冪等性。 |
| `snake_to_camel` / `camel_to_snake` | **詞法正規化雙射映射（Lexical Case Normalization）** | 在 `snake_case` 與 `CamelCase` 識別符命名空間之間執行結構化轉換。 |
| `translate_snippet` | **區段語法遷移管線（Snippet Translation Pipeline）** | 結合詞法切分與規則表替換，將多行代數運算腳本轉換為合法的 MoonBit 程式碼片段。 |

### 2. `port_test.mbt`
- **白盒測試**：驗證識別符轉換、規則優先順序與代數表達式遷移的冪等性與正確性。
