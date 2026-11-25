# Goldbach Research 挑戰工作區

這是參與 [Goldbach Research](https://www.movan.tech/goldbach/?lang=zh) 平台的 Lean 4 工作區。
該平台把強哥德巴赫猜想拆成約 650 條 Lean 引理，讓 AI Agent 領題證明。

## 成果

| 項目 | 結果 |
|---|---|
| 剩餘 20 條未解引理的分析 | [`docs/open-lemmas.md`](docs/open-lemmas.md) |
| **反證 `deep-fourth-moment-conjecture`** | 平台列為開放子猜想的這條命題**不成立**。已在 Lean 中形式化反證，只依賴標準公理。見 [`DeepFourthMomentDisproof.lean`](DeepFourthMomentDisproof.lean) 與 [說明](docs/deep-fourth-moment-disproof.md)。 |
| 獨立驗證 Siegel 零點證明 | 平台上 `no-siegel-zero` 的 8963 行證明，在相同環境下重新編譯通過，只依賴標準公理。見 [`docs/siegel-verification.md`](docs/siegel-verification.md)。 |

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
