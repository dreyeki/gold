# Goldbach Research 剩餘 20 條未解引理

資料來源：`https://www.movan.tech/goldbach/api/status`，抓取時間 2026-11-25。
當時共發布 649 條，已通過 629 條，未解 20 條，累計嘗試 819 次。

所有命題都使用同一套記號：

- `w(k)`：k 是素數時取 `log k`，否則取 0。
- `r(n) = Σ_{p+q=n} w(p)w(q)`：n 的「加權哥德巴赫表示數」。`r(n) > 0` 等價於 n 可寫成兩素數之和。
- `S(t) = Σ_{k≤n} w(k) e(kt)`，其中 `e(x) = exp(2πix)`。由 `r(n) = ∫₀¹ S(t)² e(−nt) dt` 出發，用圓法把 [0,1] 切成「主弧」與「次弧」。
- `Q = (log₂ n)²`。主弧（arcs）指 q ≤ Q、半徑 Q/(qn) 的小弧。
- `Q₁ ≈ n^{1/3}`，`H = 256·Q₁·Q`。寬弧（wideArcs）指 q ≤ Q₁、半徑 H/(qn) 的弧，寬弧的補集稱為「深次弧」。

平台上已經通過、且和下面這些題目相關的結果：

- 主弧下界 `arc-major-floor`：主弧貢獻 ≥ cn。
- 歸約 `arc-budget-transfer`：主弧下界加上次弧下界，可以推出充分大偶數的哥德巴赫。
- 不存在 Siegel 零點 `frontier-no-siegel-zero`：改編自 OpenAI 2026-10 的預印本。

所以剩下的題目，基本上都落在「次弧」與「奇偶性障礙」上。

---

## A. 終點與等價題（3 條）

| ID | 內容 | 判斷 |
|---|---|---|
| `binary-pointwise-positivity` | 每個偶數 n ≥ 4 都有 r(n) > 0 | **就是強哥德巴赫猜想本身**。平台的終點題。 |
| `dyadic-correlation-floor` | ∃ c > 0, N：所有偶數 n ≥ N 都有 r(n) ≥ cn | 比「充分大偶數的哥德巴赫」還強，是定量版。開放。 |
| `dyadic-central-prime-mass` | n = 2^k 時，只計 p ∈ [n/3, 2n/3] 的加權表示數 ≥ cn | 把哥德巴赫限制在 2 的冪上，仍然開放。 |

## B. 次弧的單側下界（3 條）

| ID | 內容 | 判斷 |
|---|---|---|
| `arc-minor-saving` | ∀ε，充分大偶數 n 的次弧貢獻實部 ≥ −εn | 加上已通過的主弧下界和歸約，可直接推出充分大偶數的哥德巴赫。**這是整個證明的核心缺口。** |
| `bulk-signed-floor` | 只取兩個素數都大於 n^{1/3} 的「高×高」部分，其次弧積分 ≥ −εn | 依賴 `minor-shift-window-budget`。本質上和上一條一樣難。 |
| `frontier-antispike-shift-transfer` | 深次弧貢獻不會比 [n, 2n] 上某個非負局部加權平均小太多。權重的 L² 範數 ≤ (ε/2)² n^{−2/3−η} | 我的分析：在這個權重限制下，用 Bessel 不等式和已知的 5/6 冪估計，加權平均項至多只貢獻 o(n)。所以這條實質上仍是「深次弧 ≥ −εn」，開放。 |

## C. 中間弧帶與「裙邊」（4 條）

| ID | 內容 | 判斷 |
|---|---|---|
| `frontier-skirt-polylog-moduli` | q ≤ (log₂n)² 的主弧，從半徑 Q/(qn) 外擴到 H/(qn)，這段環帶的貢獻 ≥ −εn | **20 條裡最可能用已知技術證出來的一條**，詳見下方說明。形式化工程量很大。 |
| `frontier-skirt-medium-moduli` | 寬弧扣掉中弧和低模裙邊後的剩餘環帶 ≥ −εn | 模數達到 n^{1/3}，超出 Siegel–Walfisz 的範圍，而且弧與弧之間會重疊。開放。 |
| `frontier-sqrt-modulus-arc-band` | n^{1/3} < q ≤ √n/(log n)⁴ 的擴展弧帶 ≥ −εn | 需要對單一 n 成立、超過 Bombieri–Vinogradov 的等分佈估計。開放。 |
| `frontier-spatial-diag-series-margin` | 高模 Ramanujan–sinc 相關項加上截斷奇異級數，減去對角項，≤ εn | 次弧問題在「空間側」的改寫，難度相同。開放。 |

**`skirt-polylog-moduli` 的初步分析**（只是我的推演，尚未嚴格驗證）：

- 在 q ≤ (log n)² 的弧上，可以把 S 拆成模型項 μ(q)/φ(q)·v(β) 加誤差。
- 模型項的平方乘上 e(−nβ)，恰好是 Fejér 型核 sin²(π(n+1)β)/sin²(πβ)，非負。對 a 求和後得到 Ramanujan 和 c_q(n)。
- 環帶上的模型總貢獻約為 `(n/(π²Q))·Σ_{q≤Q} μ²(q)·q·c_q(n)/φ(q)²`。
- 用分部求和改寫後，正負由「奇異級數部分和 A(t) 與 A(Q) 的差」決定。我初步估算它 ≥ −o(Q)，也就是模型項 ≥ −o(n)。
- 誤差項可以用 Gallagher 引理，化為「短區間（長度約 n^{2/3}）內算術級數素數定理的均方估計」。這只需要經典的零點密度估計（Carlson 或 Ingham 等級即可），再配合 Siegel–Walfisz。
- 問題在於，零點密度估計和短區間均方估計 Mathlib 都沒有。全部寫進一個只能 `import Mathlib` 的檔案，估計要上萬行。

## D. Type-II 雙線性矩陣（深次弧，6 條）

這一組用 Vaughan 恆等式把 Λ 拆成幾段。τᵢ 是因子 a 落在第 i 個區間的部分：

- 區間 1：(n^{1/16}, n^{1/4}]
- 區間 2：(n^{1/4}, n^{1/3}]
- 區間 3：(n^{1/3}, n^{2/3}]
- 區間 4：(n^{2/3}, n/U]

每一格要求 `∫_{深次弧} S_{τᵢ}(t) S_{τⱼ}(t) e(−nt) dt = o(n)`。(3,3) 格只要求單側下界 ≥ −εn。

| ID | 格點 | 判斷 |
|---|---|---|
| `frontier-type2-b1-b1` | (1,1) | 開放 |
| `frontier-type2-b1-b2` | (1,2) | 開放（目前有人領題中） |
| `frontier-type2-b2-b2` | (2,2) | 開放（目前有人領題中） |
| `frontier-type2-b1-b3` | (1,3) | 開放 |
| `frontier-type2-b2-b3` | (2,3) | 開放 |
| `frontier-type2-b3-b3-parity` | (3,3) | **篩法奇偶性障礙的本源**。開放。 |

為什麼 (1,4)、(2,4)、(3,4)、(4,4) 已經通過，(1,1) 反而沒過？這不是命題寫錯：

- 第 4 帶的因子 a > n^{2/3}，互補因子 m/a < n^{1/3}。
- 因此 τ₄ 其實是「小模數、長光滑變數」的 Type-I 序列，可以用格點計數直接算出主項，誤差為 o(n)。
- 前三帶的 Λ 落在長變數上。每一格的二元相關 Σ_{m₁+m₂=n} τᵢ(m₁)τⱼ(m₂)，都等同一族二元哥德巴赫型問題。
- 對單一 n，標準手段（sup 估計乘上 L¹ 或 L² 範數）只能給出約 n^{4/3} 的上界，離 o(n) 還很遠。

## E. 矩估計與逐點估計（2 條）

| ID | 內容 | 判斷 |
|---|---|---|
| `frontier-deep-fourth-moment-conjecture` | ∫_{深次弧} \|S\|⁴ ≤ n^{2+η} | **命題不成立，已在 Lean 中反證**，見 `DeepFourthMomentDisproof.lean`。深次弧裡仍有分母 q 略大於 n^{1/3} 的有理點 a/q，那裡 \|S\| ≈ n/q。這些尖峰讓四階矩至少達到約 n^{7/3}/polylog n，遠大於 n^{2+η}。 |
| `frontier-deep-three-quarters-saving` | 深次弧上 \|S(t)\| ≤ n^{3/4+η} | 已知最好的無條件結果是 5/6 冪（Vinogradov–Vaughan，在 q ≈ n^{1/3} 處）。即使假設 GRH，在 q ≈ n^{2/3} 附近也無法一致達到 3/4。開放。 |

## F. 分佈水平（1 條）

| ID | 內容 | 判斷 |
|---|---|---|
| `frontier-bv-three-fifths-level` | Bombieri–Vinogradov 推到模數 q ≤ X^{3/5}：每個 q 的誤差要對所有剩餘類一致取上界，總和 ≤ C·X/(log X)^A | 經典 BV 定理只到 1/2。Zhang、Polymath、Maynard 突破 1/2 時，都只針對光滑或可良好分解的權重，而且固定剩餘類 a。這裡要求對全部模數取絕對值、對 a 取最大值，是著名的開放問題。 |

## G. 有限範圍顯式估計（1 條）

| ID | 內容 | 判斷 |
|---|---|---|
| `finite-fixed-progression-unit-error` | 對 q ≤ 105、gcd(a,q) = 1、10¹⁶ ≤ n < e^{e^{3.8}} ≈ 2.6×10¹⁹，有 \|ψ(n;q,a) − n/φ(q)\| ≤ n/100 | 見下方說明。 |

這是 20 條裡**唯一確定為真**的一條：已發表的顯式算術級數素數定理（例如 arXiv 2003.01925 一類的結果）就涵蓋了它。難處在於形式化：

- q = 1、2 時，等於要求 1% 精度的顯式素數定理。
- 初等的 Chebyshev 型方法達不到 1%。
- 我粗估過，只用 de la Vallée Poussin 型零點自由區，在 10¹⁶ 處的誤差常數約差三個數量級。
- 因此還需要 L 函數零點的大規模數值驗證，而 Mathlib 完全沒有這類工具。
- 平台紀錄：被領題 3 次，2 次以 `missing_lemma` 退回，2 次逾時。目前有人領題中。

---

## 其他題庫的未解題（共 9 條）

- **no-three-in-line**（1 條）：`density-gain` 要求在無窮多個 n×n 格子上放 ≥ (3/2+δ)n 個點，任三點不共線。目前已知的構造是 Hall 等人 1975 年的 (3/2−ε)n，突破 3/2 是開放問題。
- **quadratic-primes**（8 條）：都在找 n²+1 的大素因子 P(n²+1)。
  - 據我所知，已發表的最好結果是 Merikoski 的 n^{1.279}。
  - 平台把 1.323 當作基線，但這個數字來自維護者自己尚未審稿的倉庫 `landau-fourth-problem-1.323`。
  - `lpf-endpoint` 要求素因子 > n²，等價於「n²+1 有無窮多個素數」，即朗道第四問題。
- **square-packing、hash-collision-lab、log-rank**：全部已解。

## 總結

- 20 條裡有 3 條就是哥德巴赫本身或比它更強。
- 13 條是次弧、Type-II、分佈水平上的開放子猜想。這些正是哥德巴赫幾十年來卡住的地方。
- 四階矩猜想（`deep-fourth-moment-conjecture`）**命題本身是錯的**，已用 Lean 形式化反證（只依賴標準公理）。
- 3/4 冪逐點估計比現有技術更強，但與已知的尖峰結構（約 n^{2/3}）不矛盾，仍屬開放。
- 1 條（`skirt-polylog-moduli`）大概可以用經典技術證出來，但形式化工程量極大。
- 1 條（`finite-fixed-progression-unit-error`）確定為真，但需要 Mathlib 沒有的顯式數值工具。
