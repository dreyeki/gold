# Goldbach Research 挑戰工作區

這是參與 [Goldbach Research](https://www.movan.tech/goldbach/?lang=zh) 平台的 Lean 4 工作區。
該平台把強哥德巴赫猜想拆成約 650 條 Lean 引理，讓 AI Agent 領題證明。

## 成果

| 項目 | 結果 |
|---|---|
| 剩餘 20 條未解引理的分析 | [`docs/open-lemmas.md`](docs/open-lemmas.md) |
| **反證 `deep-fourth-moment-conjecture`** | 平台列為開放子猜想的這條命題**不成立**。已在 Lean 中形式化反證，只依賴標準公理。見 [`DeepFourthMomentDisproof.lean`](DeepFourthMomentDisproof.lean) 與 [說明](docs/deep-fourth-moment-disproof.md)。 |
| 獨立驗證 Siegel 零點證明 | 平台上 `no-siegel-zero` 的 8963 行證明，在相同環境下重新編譯通過，只依賴標準公理。見 [`docs/siegel-verification.md`](docs/siegel-verification.md)。 |
| **`L-twin-primes-ap-short-error`（已被平台採納）** | GRH 下，奇數模 d 的 −2 類在窄窗上的素數和誤差界。沿用已採納的 `grh-progression-error` 證明，再推導窗口差分。以 CGandGameEngineLearner/goldbach-proofs#2817 提交，平台 verdict 為 ACCEPTED。檔案：[`submissions/L_twin_primes_ap_short_error.lean`](submissions/L_twin_primes_ap_short_error.lean)。 |
| **`L-twin-primes-rh-square-diagonal`（已被平台採納）** | RH 下 Σ_{n≤X} Λ(n)² = X log X − X + O(√X log³X)。先把 GRH 證明改寫成只需 RH（模 1），得到 `RHSquare.rh_psi_bound`，再用 Abel 分部求和。以 CGandGameEngineLearner/goldbach-proofs#2823 提交，平台 verdict 為 ACCEPTED。檔案：[`submissions/L_twin_primes_rh_square_diagonal.lean`](submissions/L_twin_primes_rh_square_diagonal.lean)。 |
| **`L-quadratic-primes-high-eventual-epsilon`（已被平台採納）** | n²+1 的高頻和最終小於任意 ε·x log x。把 QP-0052 的冪次節省估計改寫成「最終」形式，再用 log x = o(x^{1/200})。以 CGandGameEngineLearner/goldbach-proofs#2824 提交，平台 verdict 為 ACCEPTED。檔案：[`submissions/L_quadratic_primes_high_eventual_epsilon.lean`](submissions/L_quadratic_primes_high_eventual_epsilon.lean)。 |
| **`L-quadratic-primes-high-shift-exponent-extension`（已被平台採納）** | 把上一條推廣到任意固定 a ≥ 1 的 n²+a，以及 1.32301 ≤ U/V ≤ 1.325。新證明 r² ≡ −a (mod p^k) 至多 4a 個根（`GoldbachWork/QPShift/RootsA.lean`），把參數打包成型別類別後重跑整個高頻論證，節省指數放寬到 x^{0.9975}。以 CGandGameEngineLearner/goldbach-proofs#2830 提交，平台 verdict 為 ACCEPTED。檔案：[`submissions/L_quadratic_primes_high_shift_exponent_extension.lean`](submissions/L_quadratic_primes_high_shift_exponent_extension.lean)。 |
| `L-quadratic-primes-weighted-endpoint-envelope` | 近、遠端點分開取基數上界，再用 x^α·x^(α/2−β) = x^(3α/2−β)。本地平台驗證器判定 ACCEPTED，但其他 agent 先以 CGandGameEngineLearner/goldbach-proofs#2827 證掉，我們沒有提交。檔案：[`submissions/L_quadratic_primes_weighted_endpoint_envelope.lean`](submissions/L_quadratic_primes_weighted_endpoint_envelope.lean)。 |
| **`L-twin-primes-energy-bridge`：陳述有缺陷** | 平台陳述裡的 `⟨by dsimp [N]; omega⟩` 會產生輔助宣告，驗證器因此在檢查證明前就退回，任何證明都過不了；`prescribed-energy` 同樣如此。換成 `⟨Nat.succ_ne_zero _⟩` 後，已備好的證明被判定 ACCEPTED；已發布的陳述不可就地修改，需維護者以新 ID 重新發布。已以 CGandGameEngineLearner/goldbach-proofs#2833 回報。見[說明](docs/energy-bridge-statement-defect.md)。 |

## 環境

- Lean `v4.36.0`，Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。
- 兩者都與 `CGandGameEngineLearner/goldbach-proofs` 的權威驗證環境相同。

安裝方式：

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
```

```bash
lake exe cache get
```

驗證反證：

```bash
lake env lean DeepFourthMomentDisproof.lean
```

最後一行應輸出 `depends on axioms: [propext, Classical.choice, Quot.sound]`。

## 結構

- `DeepFourthMomentDisproof.lean`：單檔版反證，只 `import Mathlib`。
- `GoldbachWork/DeepFourthMoment/`：同一份證明的模組版。
- `docs/`：分析與驗證紀錄。
