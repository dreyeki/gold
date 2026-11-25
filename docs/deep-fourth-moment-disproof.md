# 反證：`L-goldbach-frontier-deep-fourth-moment-conjecture`

## 平台命題

令 `w(k) = log k`（k 為素數）、否則為 0，`S_n(t) = Σ_{k≤n} w(k) e(kt)`。
`wideArcs n` 是所有 q ≤ ⌊n^{1/3}⌋、半徑 H/(qn) 的弧，其中 `H = 256·⌊n^{1/3}⌋·(log₂(n+2))²`。
平台聲稱：

> ∀ η > 0，∃ N，∀ n ≥ N：∫₀¹ 1_{(wideArcs n)ᶜ}(t) |S_n(t)|⁴ dt ≤ n^{2+η}

平台把它當成待攻克的「開放子猜想」。命題簡介寫的是：要把平凡上界 n^{8/3+η} 壓到平方根消去的門檻 n^{2+η}。

## 為什麼不成立

深次弧只排除了 q ≤ n^{1/3} 的寬弧。對分母 q 略大於 n^{1/3} 的既約分數 a/q，主弧近似 `S(a/q+β) ≈ μ(q)/φ(q)·v(β)` 依然成立，所以在寬度約 1/n 的範圍內 |S| ≈ n/q。把這些尖峰的四階矩加總：

  Σ_{q > n^{1/3}} φ(q) · (n/φ(q))⁴ · (1/n) ≈ n³ / n^{2/3} = n^{7/3}

這遠大於 n^{2+η}（η < 1/3 時）。

## 嚴格證明的思路（已在 Lean 中完成）

取 `n = 2^{12s}`（s ≥ 20），令 `𝒬` 為所有素數 p ∈ (2^{4s}, 2^{5s}]，`d = 1/(16n)`。

1. 弧 `I_{p,a} = [a/p − d, a/p + d]`（1 ≤ a < p）互不相交、落在 (0,1] 內，且不與任何寬弧相交。這只用到 `|a/p − a'/q| ≥ 1/(pq)` 與參數大小的比較。
2. 定義 `J_{p,a} = ∫_{I_{p,a}} S`。展開得 `J = Σ_k w(k) e(ka/p) ρ_k`，其中 `ρ_k = ∫_{−d}^{d} e(ku) du`，且 `Re ρ_k ≥ 1.8d`。
3. 用素數模的 Ramanujan 和 `Σ_{1≤a<p} e(ka/p) = −1`（p ∤ k），得到 `Re(−Σ_a J_{p,a}) ≥ d((9/5)θ(n) − 2p log p) ≥ dn/2`。這一步用到 Mathlib 的 `Chebyshev.theta_ge`。
4. 單弧 Jensen 給出 `∫_I |S|⁴ ≥ |J|⁴/(2d)³`。冪平均給出 `Σ|J|⁴ ≥ (Σ|J|)⁴/#X³`。
5. 用 Mathlib 的 `Chebyshev.pi_ge_of_four_le` 得 `K = #𝒬 ≥ 2^{5s}/(10s)`。合起來：

   ∫_deep |S|⁴ ≥ K·n³/(2048·2^{15s}) ≥ 2^{26s}/(20480 s) > 2^{25s} = n^{2+1/12}

## Lean 檔案

- `DeepFourthMomentDisproof.lean`：單檔版，只 `import Mathlib`。
  - 最終定理 `L_goldbach_frontier_deep_fourth_moment_conjecture_is_false` 的型別，是平台命題字串的**逐字否定**。
  - 這個定理放在所有 `open` 的作用域之外。
- `GoldbachWork/DeepFourthMoment/`：同一份證明拆成的模組（Basic、Arcs、Measure、Params、Main、Final）。

驗證環境：Lean v4.36.0，Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`（與平台的權威驗證環境相同）。

```
'L_goldbach_frontier_deep_fourth_moment_conjecture_is_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 對平台的建議

可能的修正方向（維護者決定）：

- 把上界改成 n^{7/3+η}。這可能才是正確的量級，但需要另外證明。
- 或者把積分範圍改成排除分母到 √n 的弧（例如 `sqrtArcs` 的補集）。
