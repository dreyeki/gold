# `L-twin-primes-energy-bridge` 的陳述無法通過驗證器

## 結論

平台目前記錄的兩條陳述，任何證明都不可能被接受：

- `L-twin-primes-energy-bridge`
- `L-twin-primes-prescribed-energy`

原因不在數學，而在陳述的寫法。`L-twin-primes-endpoint` 依賴前者，所以這條路線也一起卡住。

## 原因

兩條陳述都在定義 `energy` 時寫了：

```lean
letI : NeZero (N X) := ⟨by dsimp [N]; omega⟩
```

驗證器 `lean/CheckLemma.lean` 會先自己把記錄的陳述 elaborate 一次。`by ... omega` 這段策略證明會被 Lean 抽成輔助宣告 `PEqualNPChecker.recorded._proof_1`。

驗證器要求陳述只依賴固定版本的 Mathlib 與 `PEqualNP.Defs`，所以在檢查證明之前就退回：

```
REJECTED (statement): the recorded statement rests on declarations that are not in the
pinned library or the definitions root as the kernel accepted them:
[PEqualNPChecker.recorded._proof_1]. Write it as one term that needs no auxiliary declaration
```

本地驗證器與上游 `main` 的 `lean/CheckLemma.lean`、`tools/check-lean.mjs` 逐字相同。

## 其他開放題沒有同樣問題

我把四個題庫裡全部 47 條開放陳述，照驗證器的寫法逐條 elaborate（環境：固定版本的 Mathlib 加 `PEqualNP.Defs`，`autoImplicit false`），再列出每條陳述用到、但不在函式庫裡的常數：

- 47 條都能 elaborate，沒有錯誤。
- 只有 `energy-bridge` 與 `prescribed-energy` 產生輔助宣告。

## 修正方式

把策略證明換成一個項即可：

```lean
letI : NeZero (N X) := ⟨Nat.succ_ne_zero _⟩
```

`N X = 2*X+5` 會與 `?n + 1` 統一，不需要輔助宣告。數學內容完全不變。

但已發布的陳述不能就地修改：

- `research/build_catalogue.py --write` 會回報 `ValueError: Frozen statement changed: L-twin-primes-energy-bridge; create a new ID`。catalogue CI 跑的就是這支。
- 領題記錄綁定陳述位元組的 SHA-256，所以修正已發布的命題要開新 ID。

因此要由維護者處理：

- 撤下 `L-twin-primes-energy-bridge` 與 `L-twin-primes-prescribed-energy`。
- 以新 ID（例如加上 `-v2`）發布修正後的陳述，並在路線裡註明替代關係。
- 把 `L-twin-primes-endpoint` 的 `depends_on` 改成新 ID。

## 已備好的證明

[`submissions/L_twin_primes_energy_bridge.lean`](../submissions/L_twin_primes_energy_bridge.lean) 是 `energy-bridge` 的完整證明（136 行，只 `import Mathlib`）。

1. 對 `ZMod M` 上的實值函數 `g`，證明 `∑ₖ Re ψ(2k)·‖dft g k‖² = M·∑ⱼ g(j+2)·g(j)`：展開 `‖F‖² = F·conj F`，再用加法特徵的正交性。
2. 能量為正時，必有 `j` 使 `g(j)` 與 `g(j+2)` 都不為零。
3. `f` 只在窗口 `(X, 1.02X)` 內的素數上非零，而 `M = 2X+5`，所以 `j.val + 2` 不會繞回。因此 `j.val` 與 `j.val + 2` 都是大於 `X` 的素數。

驗證結果：

| 陳述 | 平台驗證器 |
|---|---|
| 平台原文 | `REJECTED (statement)`，與證明無關 |
| 換成 `⟨Nat.succ_ne_zero _⟩` | `ACCEPTED`，公理只有 `propext`、`Classical.choice`、`Quot.sound` |

`prescribed-energy` 本身等價於孪生素數猜想，修正陳述只是讓它日後有機會被驗證。
