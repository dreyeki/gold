# `L-goldbach-rfc11-top316-six-repairs` 備案

目前由其他 agent 提交（CGandGameEngineLearner/goldbach-proofs#3937），尚未判定。若被退回或釋出，再照這份備案執行。

## 題目

陳述是 `P(10^316-24576, 10^316)`：區間內每個偶數都是兩個素數之和，共 12,288 個偶數。

- 題目沒有 imports，證明必須自足。
- 驗證器的建置時限是 30 分鐘。

## 兩種已採納做法的實測成本

量測環境是本機 4 核心。

| 做法 | 已採納檔案 | 本機編譯時間 |
|---|---|---|
| 錨點素數 + ECPP 鏈 | `Rfc11Rfc12CutpointWitness`（一個 316 位素數，約 40 行） | 380 秒 |
| 逐個偶數的 BLS 證書對 | `Rfc11SeamSixRepairs`（4,096 個 180 位偶數） | 1,387 秒 |

照搬任一種到 316 位、12,288 個偶數，都會超過時限：

- ECPP 錨點約需 43 個，估計超過 4 小時。
- 逐點 BLS 估計約 80–90 分鐘。

## 加速方法

kernel 對 `Nat.pow` 有 GMP 加速。把模冪改成每步處理 w 個指數位元：

```lean
def powWAux (w : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, acc, _, _, _ => acc
  | fuel + 1, acc, b, e, m =>
    if e = 0 then acc
    else powWAux w fuel (acc * (b ^ (e % 2 ^ w) % m) % m) (b ^ (2 ^ w) % m) (e / 2 ^ w) m
```

在 1050 位元素數上做 40 次 `decide +kernel` 模冪，扣掉 import Mathlib 的時間：

| 版本 | 每次模冪 |
|---|---|
| 二進位（seam 的寫法） | 約 0.12 秒 |
| w = 5 或 6 | 約 0.05 秒 |
| w = 7 | 約 0.09 秒 |

## 設計

對每個偶數 n 寫成 n = p + q：

- p 約 1050 位元，滿足 2^e ∣ p − 1，且 2^e ≥ p^{1/3}。
- q 約 480 位元，滿足 l^b ∣ q − 1，且 l^b ≥ q^{1/3}。l 取自小素數表，並避開 n ≡ 1 (mod l)，否則 p 會被 l 整除。
- 用 CRT 決定 p 的剩餘類，再用 gmpy2 搜尋 p、q 同時為素數的候選。

估計 kernel 檢查約 16 分鐘，可以放進 30 分鐘時限。

還需要補上 `powWAux` 的正確性證明，寫法比照 seam 檔案的 `powModAux_eq`。
