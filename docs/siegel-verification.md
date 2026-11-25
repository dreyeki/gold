# 獨立驗證：`L-goldbach-frontier-no-siegel-zero`

平台上這條已標記 ACCEPTED。命題內容是「存在絕對常數 c > 0，使所有實 Dirichlet 特徵的 L 函數在 (1 − c/log(q+2), 1) 內沒有零點」，也就是 Landau–Siegel 零點不存在。

- 證明來源：`CGandGameEngineLearner/goldbach-proofs` 的 PR #2493。
  - 檔案 `lean/PEqualNP/Outside/L_goldbach_frontier_no_siegel_zero.lean`，共 8963 行。
  - sha256 `d8197eeaa9c08990302c4acd27bdc8f56a581b2655c8221df65f7d9ffa92aa69`，與平台驗證紀錄一致。
- 檔案自述改編自 OpenAI 的 `openai/math` 倉庫，以及 `jmreilly1113/siegel-zeros-audit`。
- 數學背景：OpenAI 2026-10-01 的預印本《Uniform exclusion of Landau–Siegel zeros》，以及 Banks、Kerr 等人的後續預印本。這些都尚未經同行審查。

## 驗證結果（2026-11-25）

驗證環境為 Lean v4.36.0，Mathlib commit `fc4f59e5…`（與平台相同）。

```
lake env lean NoSiegel.lean      # 檔尾加上 #print axioms
→ 0 errors，耗時 56 秒
'PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

另外用 grep 檢查過：檔案中沒有 `sorry`、`axiom`、`native_decide`、`implemented_by`、`macro`、`elab`、`#eval`。

結論：在固定版本的 Lean 核心與 Mathlib 下，這個形式命題的證明是完整的，只依賴標準公理。至於形式命題是否忠實表達了 Landau–Siegel 猜想，我人工讀過命題，認為忠實。
