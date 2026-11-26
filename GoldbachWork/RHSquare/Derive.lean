import Mathlib

/-!
# 由 `|ψ(X) - X| ≤ C √X log²(2X)` 推出 `Σ_{n≤X} Λ(n)² = X log X - X + O(√X log³ X)`

1. `ΣΛ(n)²` 與 `ΣΛ(n) log n` 只差非素數項，至多 `log X · (ψ - θ)(X) ≤ 2√X log² X`。
2. Abel 分部求和：`ΣΛ(n) log n = ψ(X) log X - Σ_{m<X} ψ(m) (log(m+1) - log m)`。
3. 主項 `Σ m (log(m+1) - log m)` 與 `X` 相差至多 `2 + log X`。
4. 誤差項用 `Σ 1/√m ≤ 2√X` 控制。
-/

open Real Finset

namespace RHSquare

/-- Abel 分部求和（離散形式）。 -/
lemma abel_sum (a b : ℕ → ℝ) (X : ℕ) :
    ∑ n ∈ range (X + 1), a n * b n =
      (∑ k ∈ range (X + 1), a k) * b X -
        ∑ m ∈ range X, (∑ k ∈ range (m + 1), a k) * (b (m + 1) - b m) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun m => (∑ k ∈ range (m + 1), a k) *
      (b (m + 1) - b m)), sum_range_succ a (X + 1)]
    ring

/-- `Σ_{m ≤ X, m ≥ 1} 1/√m ≤ 2√X`。 -/
lemma sum_inv_sqrt_le (X : ℕ) :
    ∑ m ∈ range (X + 1), (if m = 0 then (0 : ℝ) else 1 / √(m : ℝ)) ≤ 2 * √(X : ℝ) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [sum_range_succ, if_neg (Nat.succ_ne_zero X)]
    have ha : 0 < √((X + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hb : 0 ≤ √(X : ℝ) := Real.sqrt_nonneg _
    have ha2 : √((X + 1 : ℕ) : ℝ) ^ 2 = (X : ℝ) + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have hb2 : √(X : ℝ) ^ 2 = (X : ℝ) := Real.sq_sqrt (by positivity)
    have hab : √(X : ℝ) ≤ √((X + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by push_cast; linarith)
    have key : 1 / √((X + 1 : ℕ) : ℝ) ≤ 2 * √((X + 1 : ℕ) : ℝ) - 2 * √(X : ℝ) := by
      rw [div_le_iff₀ ha]
      nlinarith [sq_nonneg (√((X + 1 : ℕ) : ℝ) - √(X : ℝ))]
    linarith

lemma log_succ_sub_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← Real.log_div (by positivity) hmR.ne']
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / m by positivity)
  have e : ((m + 1 : ℕ) : ℝ) / m - 1 = 1 / m := by push_cast; field_simp; ring
  linarith

lemma log_succ_sub_nonneg (m : ℕ) :
    0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hm) (by push_cast; linarith)
    linarith

lemma mul_log_succ_sub_ge (m : ℕ) (hm : 1 ≤ m) :
    1 - 1 / ((m : ℝ) + 1) ≤ (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← Real.log_div (by positivity) hmR.ne']
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / m by positivity)
  have e : 1 - (((m + 1 : ℕ) : ℝ) / m)⁻¹ = 1 / ((m : ℝ) + 1) := by push_cast; field_simp; ring
  rw [e] at h
  have e2 : 1 - 1 / ((m : ℝ) + 1) = (m : ℝ) * (1 / ((m : ℝ) + 1)) := by field_simp; ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left h hmR.le

lemma mul_log_succ_sub_ge' (m : ℕ) :
    1 - 1 / ((m : ℝ) + 1) ≤ (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact mul_log_succ_sub_ge m hm

lemma mul_log_succ_sub_le_one (m : ℕ) :
    (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h := log_succ_sub_le m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    calc (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤ (m : ℝ) * (1 / m) :=
          mul_le_mul_of_nonneg_left h hmR.le
      _ = 1 := by field_simp

lemma sum_inv_succ_eq_harmonic (X : ℕ) :
    ∑ m ∈ range X, 1 / ((m : ℝ) + 1) = (harmonic X : ℝ) := by
  unfold harmonic
  push_cast
  simp [one_div]

/-- 主項：`X - Σ_{m<X} m (log(m+1) - log m)` 落在 `[0, 1 + log X]`。 -/
lemma main_term_bound (X : ℕ) :
    |(X : ℝ) - ∑ m ∈ range X, (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ))| ≤
      1 + Real.log X := by
  have hup : ∑ m ∈ range X, (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤ X := by
    calc ∑ m ∈ range X, (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ))
        ≤ ∑ m ∈ range X, (1 : ℝ) := Finset.sum_le_sum fun m _ => mul_log_succ_sub_le_one m
      _ = X := by simp
  have hlow : ∑ m ∈ range X, (1 - 1 / ((m : ℝ) + 1)) ≤
      ∑ m ∈ range X, (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) :=
    Finset.sum_le_sum fun m _ => mul_log_succ_sub_ge' m
  rw [Finset.sum_sub_distrib, sum_inv_succ_eq_harmonic] at hlow
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hlow
  have hH : (harmonic X : ℝ) ≤ 1 + Real.log X := harmonic_le_one_add_log X
  rw [abs_le]
  constructor <;> linarith

/-- `Σ_{n≤X, n 非素數} Λ(n) ≤ 2√X log X`。 -/
lemma sum_not_prime_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ n ∈ (range (X + 1)).filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt n ≤
      2 * √(X : ℝ) * Real.log X := by
  calc ∑ n ∈ (range (X + 1)).filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt n
      = Chebyshev.psi X - Chebyshev.theta X := by
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
        symm
        apply Finset.sum_subset
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hk ⊢
          exact ⟨by omega, hk.2⟩
        · intro k hk hk'
          have hk0 : k = 0 := by
            by_contra h
            apply hk'
            simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hk ⊢
            exact ⟨⟨by omega, by omega⟩, hk.2⟩
          subst hk0
          simp
    _ ≤ 2 * √(X : ℝ) * Real.log X := Chebyshev.psi_sub_theta_le (by exact_mod_cast hX)

set_option maxHeartbeats 2000000 in
theorem derive
    (hψ : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
      |(∑ k ∈ range (X + 1), ArithmeticFunction.vonMangoldt k) - X| ≤
        C * √(X : ℝ) * Real.log (2 * (X : ℝ)) ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℕ, 2 ≤ X →
      |(∑ n ∈ range (X + 1), ArithmeticFunction.vonMangoldt n ^ 2) - ((X : ℝ) * Real.log X - X)| ≤
        K * √(X : ℝ) * Real.log (2 + (X : ℝ)) ^ 3 := by
  obtain ⟨C, hC, hE⟩ := hψ
  refine ⟨12 * C + 6, by positivity, ?_⟩
  intro X hX
  set Lam := ArithmeticFunction.vonMangoldt with hLam
  set ψN : ℕ → ℝ := fun m => ∑ k ∈ range (m + 1), Lam k with hψN
  set Δ : ℕ → ℝ := fun m => Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) with hΔ
  set S1 := ∑ n ∈ range (X + 1), Lam n * Real.log (n : ℝ) with hS1
  set C0 := ∑ n ∈ range (X + 1), Lam n ^ 2 with hC0
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX1 : 1 ≤ X := by omega
  -- 第一步：S1 - C0
  have hdiff : 0 ≤ S1 - C0 ∧ S1 - C0 ≤ Real.log X * (2 * √(X : ℝ) * Real.log X) := by
    have heq : S1 - C0 = ∑ n ∈ range (X + 1), Lam n * (Real.log (n : ℝ) - Lam n) := by
      rw [hS1, hC0, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [heq]
    have hterm : ∀ n ∈ range (X + 1), 0 ≤ Lam n * (Real.log (n : ℝ) - Lam n) ∧
        Lam n * (Real.log (n : ℝ) - Lam n) ≤
          (if n.Prime then 0 else Lam n * Real.log X) := by
      intro n hn
      have hnX : n ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hLam0 : 0 ≤ Lam n := ArithmeticFunction.vonMangoldt_nonneg
      have hLamle : Lam n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      by_cases hp : n.Prime
      · rw [if_pos hp, hLam, ArithmeticFunction.vonMangoldt_apply_prime hp]
        simp
      · rw [if_neg hp]
        refine ⟨mul_nonneg hLam0 (by linarith), ?_⟩
        have hlogn : Real.log (n : ℝ) ≤ Real.log X := by
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · simp; exact Real.log_nonneg (by linarith)
          · exact Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnX)
        nlinarith
    constructor
    · exact Finset.sum_nonneg fun n hn => (hterm n hn).1
    · calc ∑ n ∈ range (X + 1), Lam n * (Real.log (n : ℝ) - Lam n)
          ≤ ∑ n ∈ range (X + 1), (if n.Prime then 0 else Lam n * Real.log X) :=
            Finset.sum_le_sum fun n hn => (hterm n hn).2
        _ = Real.log X * ∑ n ∈ (range (X + 1)).filter (fun n => ¬ n.Prime), Lam n := by
            rw [Finset.mul_sum, Finset.sum_filter]
            refine Finset.sum_congr rfl fun n _ => ?_
            split_ifs <;> ring
        _ ≤ Real.log X * (2 * √(X : ℝ) * Real.log X) :=
            mul_le_mul_of_nonneg_left (sum_not_prime_le X hX1)
              (Real.log_nonneg (by linarith))
  -- 第二步：Abel 分部求和
  have habel : S1 = ψN X * Real.log X - ∑ m ∈ range X, ψN m * Δ m := by
    rw [hS1, abel_sum Lam (fun n => Real.log (n : ℝ)) X]
  have hsplit : S1 - ((X : ℝ) * Real.log X - X) =
      (ψN X - X) * Real.log X +
        ((X : ℝ) - ∑ m ∈ range X, (m : ℝ) * Δ m) -
        ∑ m ∈ range X, (ψN m - m) * Δ m := by
    rw [habel]
    have : ∑ m ∈ range X, ψN m * Δ m =
        ∑ m ∈ range X, (m : ℝ) * Δ m + ∑ m ∈ range X, (ψN m - m) * Δ m := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => by ring
    rw [this]
    ring
  -- 第三步：各項估計
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  set l2 := Real.log (2 * (X : ℝ)) with hl2
  have hl20 : 0 ≤ l2 := Real.log_nonneg (by linarith)
  have hsq1 : 1 ≤ √(X : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have t1 : |(ψN X - X) * Real.log X| ≤ C * √(X : ℝ) * l2 ^ 2 * Real.log X := by
    rw [abs_mul, abs_of_nonneg hlogX0]
    exact mul_le_mul_of_nonneg_right (hE X hX) hlogX0
  have t2 : |(X : ℝ) - ∑ m ∈ range X, (m : ℝ) * Δ m| ≤ 1 + Real.log X := main_term_bound X
  -- 誤差和
  set g : ℕ → ℝ := fun m => if m = 0 then 0 else 1 / √(m : ℝ) with hg
  have hterm3 : ∀ m ∈ range X, |(ψN m - m) * Δ m| ≤
      (if m = 1 then (1 : ℝ) else 0) + C * l2 ^ 2 * g m := by
    intro m hm
    have hmX : m < X := Finset.mem_range.mp hm
    have hΔ0 : 0 ≤ Δ m := log_succ_sub_nonneg m
    have hgm : 0 ≤ g m := by
      simp only [hg]; split_ifs <;> positivity
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · simp [hΔ, hψN]
        positivity
      · have hψ1 : ψN 1 = 0 := by simp [hψN, Finset.sum_range_succ, hLam]
        have hΔ1 : Δ 1 = Real.log 2 := by simp [hΔ]; norm_num
        rw [hψ1, hΔ1, if_pos rfl]
        have hlog2 : Real.log 2 ≤ 1 := by
          have := Real.log_two_lt_d9; linarith
        have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        rw [abs_of_nonpos (by push_cast; nlinarith)]
        push_cast
        nlinarith [mul_nonneg (mul_nonneg hC.le (sq_nonneg l2)) hgm]
    · rw [if_neg (by omega)]
      have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      have hEm := hE m hm2
      have hlogm : Real.log (2 * (m : ℝ)) ≤ l2 := by
        rw [hl2]; apply Real.log_le_log (by linarith)
        have : (m : ℝ) ≤ X := by exact_mod_cast hmX.le
        linarith
      have hlogm0 : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by linarith)
      have hΔle : Δ m ≤ 1 / (m : ℝ) := log_succ_sub_le m (by omega)
      have hsqm : 0 < √(m : ℝ) := Real.sqrt_pos.mpr (by linarith)
      have hgm' : g m = 1 / √(m : ℝ) := by simp only [hg]; rw [if_neg (by omega)]
      rw [hgm', zero_add, abs_mul, abs_of_nonneg hΔ0]
      have hsq : √(m : ℝ) * (1 / (m : ℝ)) = 1 / √(m : ℝ) := by
        have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ m by linarith)
        calc √(m : ℝ) * (1 / (m : ℝ)) = √(m : ℝ) / (√(m : ℝ) * √(m : ℝ)) := by rw [h]; ring
          _ = 1 / √(m : ℝ) := by field_simp
      calc |ψN m - (m : ℝ)| * Δ m
          ≤ (C * √(m : ℝ) * Real.log (2 * (m : ℝ)) ^ 2) * (1 / (m : ℝ)) :=
            mul_le_mul hEm hΔle hΔ0 (by positivity)
        _ ≤ (C * √(m : ℝ) * l2 ^ 2) * (1 / (m : ℝ)) := by
            gcongr
        _ = C * l2 ^ 2 * (√(m : ℝ) * (1 / (m : ℝ))) := by ring
        _ = C * l2 ^ 2 * (1 / √(m : ℝ)) := by rw [hsq]
  have t3 : |∑ m ∈ range X, (ψN m - m) * Δ m| ≤ 1 + C * l2 ^ 2 * (2 * √(X : ℝ)) := by
    calc |∑ m ∈ range X, (ψN m - m) * Δ m|
        ≤ ∑ m ∈ range X, |(ψN m - m) * Δ m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ range X, ((if m = 1 then (1 : ℝ) else 0) + C * l2 ^ 2 * g m) :=
          Finset.sum_le_sum hterm3
      _ = (∑ m ∈ range X, (if m = 1 then (1 : ℝ) else 0)) + C * l2 ^ 2 * ∑ m ∈ range X, g m := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 1 + C * l2 ^ 2 * (2 * √(X : ℝ)) := by
          have h1 : (∑ m ∈ range X, (if m = 1 then (1 : ℝ) else 0)) ≤ 1 := by
            rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
          have hg0 : ∀ m, 0 ≤ g m := fun m => by simp only [hg]; split_ifs <;> positivity
          have h2 : ∑ m ∈ range X, g m ≤ 2 * √(X : ℝ) :=
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
              (fun m _ _ => hg0 m)).trans (sum_inv_sqrt_le X)
          have hCl : 0 ≤ C * l2 ^ 2 := by positivity
          nlinarith
  -- 第四步：組合
  set L := Real.log (2 + (X : ℝ)) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    have : Real.exp 1 ≤ 2 + (X : ℝ) := by have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  have hlogXL : Real.log X ≤ L := by
    rw [hL]; exact Real.log_le_log (by linarith) (by linarith)
  have hl2L : l2 ≤ 2 * L := by
    rw [hl2, hL, ← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show ((2 : ℝ) + X) ^ (2 : ℝ) = (2 + X) ^ 2 by norm_cast]
    nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hsX0 : 0 ≤ √(X : ℝ) := Real.sqrt_nonneg _
  have key : |C0 - ((X : ℝ) * Real.log X - X)| ≤
      C * √(X : ℝ) * l2 ^ 2 * Real.log X + (1 + Real.log X) + (1 + C * l2 ^ 2 * (2 * √(X : ℝ)))
        + Real.log X * (2 * √(X : ℝ) * Real.log X) := by
    have e : C0 - ((X : ℝ) * Real.log X - X) =
        (S1 - ((X : ℝ) * Real.log X - X)) - (S1 - C0) := by ring
    rw [e, hsplit]
    have a1 := abs_sub ((ψN X - X) * Real.log X + ((X : ℝ) - ∑ m ∈ range X, (m : ℝ) * Δ m) -
        ∑ m ∈ range X, (ψN m - m) * Δ m) (S1 - C0)
    have a2 := abs_sub ((ψN X - X) * Real.log X + ((X : ℝ) - ∑ m ∈ range X, (m : ℝ) * Δ m))
        (∑ m ∈ range X, (ψN m - m) * Δ m)
    have a3 := abs_add_le ((ψN X - X) * Real.log X) ((X : ℝ) - ∑ m ∈ range X, (m : ℝ) * Δ m)
    rw [abs_of_nonneg hdiff.1] at a1
    linarith [hdiff.2]
  -- 換成 L 的冪
  have hl2sq : l2 ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have b1 : C * √(X : ℝ) * l2 ^ 2 * Real.log X ≤ 4 * C * √(X : ℝ) * L ^ 3 := by
    have : l2 ^ 2 * Real.log X ≤ 4 * L ^ 2 * L := mul_le_mul hl2sq hlogXL hlogX0 (by positivity)
    calc C * √(X : ℝ) * l2 ^ 2 * Real.log X = C * √(X : ℝ) * (l2 ^ 2 * Real.log X) := by ring
      _ ≤ C * √(X : ℝ) * (4 * L ^ 2 * L) := by gcongr
      _ = 4 * C * √(X : ℝ) * L ^ 3 := by ring
  have b2 : (1 + Real.log X) + 1 ≤ 3 * √(X : ℝ) * L ^ 3 := by
    have hL3 : L ≤ L ^ 3 := by nlinarith
    have : 2 + L ≤ 3 * L ^ 3 := by nlinarith
    nlinarith
  have b3 : C * l2 ^ 2 * (2 * √(X : ℝ)) ≤ 8 * C * √(X : ℝ) * L ^ 3 := by
    have hL23 : L ^ 2 ≤ L ^ 3 := by nlinarith
    calc C * l2 ^ 2 * (2 * √(X : ℝ)) ≤ C * (4 * L ^ 2) * (2 * √(X : ℝ)) := by gcongr
      _ ≤ C * (4 * L ^ 3) * (2 * √(X : ℝ)) := by gcongr
      _ = 8 * C * √(X : ℝ) * L ^ 3 := by ring
  have b4 : Real.log X * (2 * √(X : ℝ) * Real.log X) ≤ 3 * √(X : ℝ) * L ^ 3 := by
    have hlx2 : Real.log X * Real.log X ≤ L ^ 2 := by nlinarith
    have hL23 : L ^ 2 ≤ L ^ 3 := by nlinarith
    nlinarith
  calc |C0 - ((X : ℝ) * Real.log X - X)| ≤ _ := key
    _ ≤ (12 * C + 6) * √(X : ℝ) * L ^ 3 := by nlinarith

end RHSquare
