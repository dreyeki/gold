import Mathlib

/-!
# 由一致的 GRH 算術級數誤差界推出 `L-twin-primes-ap-short-error`

假設 `|ψ(X;q,a) - X/φ(q)| ≤ C₀ √X log²(2qX)`（對所有 `q`、與 `q` 互質的 `a`、`X ≥ 2`）。

- 對奇數 `d`，`d ∣ p+2` 等價於 `p ≡ 2d-2 (mod d)`，而 `2d-2` 與 `d` 互質。
- 窄窗 `(X, (51X-1)/50]` 上的素數和等於兩端 `θ(·; d, 2d-2)` 之差。
- `ψ - θ` 只來自素數冪，用 Mathlib 的 `Chebyshev.psi_sub_theta_le` 控制。
-/

open Real Finset

namespace TwinAPShort

noncomputable def psiR (q a Y : ℕ) : ℝ :=
  Finset.sum ((Finset.range (Y + 1)).filter (fun k => k % q = a % q))
    (fun k => ArithmeticFunction.vonMangoldt k)

noncomputable def thetaR (q a Y : ℕ) : ℝ :=
  Finset.sum ((Finset.range (Y + 1)).filter (fun k => k % q = a % q ∧ k.Prime))
    (fun k => Real.log k)

lemma psiR_sub_thetaR_eq (q a Y : ℕ) :
    psiR q a Y - thetaR q a Y =
      Finset.sum ((Finset.range (Y + 1)).filter (fun k => k % q = a % q ∧ ¬ k.Prime))
        (fun k => ArithmeticFunction.vonMangoldt k) := by
  unfold psiR thetaR
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.range (Y + 1)).filter (fun k => k % q = a % q)) (fun k => k.Prime)]
  rw [Finset.filter_filter, Finset.filter_filter]
  have : Finset.sum ((Finset.range (Y + 1)).filter (fun k => k % q = a % q ∧ k.Prime))
      (fun k => ArithmeticFunction.vonMangoldt k) =
      Finset.sum ((Finset.range (Y + 1)).filter (fun k => k % q = a % q ∧ k.Prime))
        (fun k => Real.log k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    exact ArithmeticFunction.vonMangoldt_apply_prime hk.2.2
  rw [this]
  ring

lemma psiR_sub_thetaR_nonneg (q a Y : ℕ) : 0 ≤ psiR q a Y - thetaR q a Y := by
  rw [psiR_sub_thetaR_eq]
  exact Finset.sum_nonneg fun k _ => ArithmeticFunction.vonMangoldt_nonneg

lemma psiR_sub_thetaR_le (q a Y : ℕ) (hY : 1 ≤ Y) :
    psiR q a Y - thetaR q a Y ≤ 2 * √(Y : ℝ) * Real.log Y := by
  rw [psiR_sub_thetaR_eq]
  calc Finset.sum ((Finset.range (Y + 1)).filter (fun k => k % q = a % q ∧ ¬ k.Prime))
        (fun k => ArithmeticFunction.vonMangoldt k)
      ≤ Finset.sum ((Finset.range (Y + 1)).filter (fun k => ¬ k.Prime))
          (fun k => ArithmeticFunction.vonMangoldt k) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          simp only [Finset.mem_filter] at hk ⊢
          exact ⟨hk.1, hk.2.2⟩
        · intro k _ _
          exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Chebyshev.psi Y - Chebyshev.theta Y := by
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
    _ ≤ 2 * √(Y : ℝ) * Real.log Y := Chebyshev.psi_sub_theta_le (by exact_mod_cast hY)

lemma dvd_add_two_iff {d n : ℕ} (hd : 1 ≤ d) : d ∣ n + 2 ↔ n % d = (2 * d - 2) % d := by
  have h2 : 2 * d - 2 + 2 = 2 * d := by omega
  have h0 : 2 * d ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left d 2)
  constructor
  · intro h
    have h1 : n + 2 ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr h
    have h3 : n + 2 ≡ 2 * d - 2 + 2 [MOD d] := by
      rw [h2]; exact h1.trans h0.symm
    exact Nat.ModEq.add_right_cancel' 2 h3
  · intro h
    have h3 : n + 2 ≡ 2 * d - 2 + 2 [MOD d] := Nat.ModEq.add_right 2 h
    rw [h2] at h3
    exact Nat.modEq_zero_iff_dvd.mp (h3.trans h0)

lemma coprime_two_mul_sub {d : ℕ} (hd : Odd d) : Nat.Coprime (2 * d - 2) d := by
  have hd1 : 1 ≤ d := hd.pos
  have hmod : d % 2 = 1 := Nat.odd_iff.mp hd
  set g := Nat.gcd (2 * d - 2) d with hg
  have h1 : g ∣ d := Nat.gcd_dvd_right _ _
  have h2 : g ∣ 2 * d - 2 := Nat.gcd_dvd_left _ _
  have h3 : g ∣ 2 * d := dvd_mul_of_dvd_right h1 2
  have h4 : g ∣ 2 := by
    have := Nat.dvd_sub h3 h2
    rwa [show 2 * d - (2 * d - 2) = 2 by omega] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h | h
  · exact h
  · exfalso
    rw [h] at h1
    omega

lemma window_eq {X d : ℕ} (hX : 1 ≤ X) (hd : 1 ≤ d) :
    ((Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)).filter
        (fun p => p.Prime ∧ d ∣ p + 2) =
      ((Finset.range ((51 * X - 1) / 50 + 1)).filter
          (fun k => k % d = (2 * d - 2) % d ∧ k.Prime)) \
        ((Finset.range (X + 1)).filter (fun k => k % d = (2 * d - 2) % d ∧ k.Prime)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff, not_and]
  rw [dvd_add_two_iff hd]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨⟨by omega, h5, h4⟩, fun h _ _ => by omega⟩
  · rintro ⟨⟨h1, h5, h4⟩, h6⟩
    have h7 : ¬ n < X + 1 := fun h => h6 h h5 h4
    exact ⟨⟨by omega, by omega, by omega⟩, h4, h5⟩

set_option maxHeartbeats 1000000 in
theorem derive
    (hB : ∃ C : ℝ, 0 < C ∧ ∀ q a X : ℕ, 0 < q → Nat.Coprime a q → 2 ≤ X →
      |(Finset.sum ((Finset.range (X + 1)).filter (fun k => k % q = a % q))
        (fun k => ArithmeticFunction.vonMangoldt k)) - (X : ℝ) / (Nat.totient q : ℝ)| ≤
        C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2) :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
    ∃ C : ℝ, 0 < C ∧ ∀ (X d : ℕ), 2 ≤ X → d ≤ X → Odd d →
      |((w X).filter (fun p => p.Prime ∧ d ∣ p+2)).sum (fun p => Real.log p) -
        (X:ℝ)/(50*Nat.totient d)| ≤ C*Real.sqrt X*(Real.log (2*(d:ℝ)*X))^2 := by
  intro w
  obtain ⟨C₀, hC₀, hbound⟩ := hB
  refine ⟨9 * C₀ + 8, by positivity, ?_⟩
  intro X d hX hdX hd
  have hd1 : 1 ≤ d := hd.pos
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = 2 * d - 2 := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℕ, U = (51 * X - 1) / 50 := ⟨_, rfl⟩
  have hU1 : 50 * U ≤ 51 * X - 1 := by omega
  have hU2 : 51 * X - 1 < 50 * U + 50 := by omega
  have hXU : X ≤ U := by omega
  have hU2X : U ≤ 2 * X := by omega
  have hcop : Nat.Coprime a d := by rw [ha]; exact coprime_two_mul_sub hd
  -- 窗口和 = θ(U) - θ(X)
  have hwin : ((w X).filter (fun p => p.Prime ∧ d ∣ p+2)).sum (fun p => Real.log p) =
      thetaR d a U - thetaR d a X := by
    simp only [w]
    rw [window_eq (by omega) hd1, ← ha, ← hU]
    unfold thetaR
    rw [Finset.sum_sdiff_eq_sub]
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨by omega, hk.2⟩
  rw [hwin]
  -- 各項估計
  have hEU : |psiR d a U - (U : ℝ) / (Nat.totient d : ℝ)| ≤
      C₀ * Real.sqrt (U : ℝ) * (Real.log (2 * (d : ℝ) * (U : ℝ))) ^ 2 :=
    hbound d a U hd1 hcop (by omega)
  have hEX : |psiR d a X - (X : ℝ) / (Nat.totient d : ℝ)| ≤
      C₀ * Real.sqrt (X : ℝ) * (Real.log (2 * (d : ℝ) * (X : ℝ))) ^ 2 :=
    hbound d a X hd1 hcop hX
  have hPU0 := psiR_sub_thetaR_nonneg d a U
  have hPU := psiR_sub_thetaR_le d a U (by omega)
  have hPX0 := psiR_sub_thetaR_nonneg d a X
  have hPX := psiR_sub_thetaR_le d a X (by omega)
  -- 實數化
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hURle : (U : ℝ) ≤ 2 * X := by exact_mod_cast hU2X
  have hXURle : (X : ℝ) ≤ U := by exact_mod_cast hXU
  have hU1R : 50 * (U : ℝ) ≤ 51 * X - 1 := by
    have : ((50 * U : ℕ) : ℝ) ≤ ((51 * X - 1 : ℕ) : ℝ) := by exact_mod_cast hU1
    push_cast [show 1 ≤ 51 * X by omega] at this
    linarith
  have hU2R : 51 * (X : ℝ) - 1 < 50 * U + 50 := by
    have : ((51 * X - 1 : ℕ) : ℝ) < ((50 * U + 50 : ℕ) : ℝ) := by exact_mod_cast hU2
    push_cast [show 1 ≤ 51 * X by omega] at this
    linarith
  have hφ : (1 : ℝ) ≤ (Nat.totient d : ℝ) := by
    have := Nat.totient_pos.mpr hd1
    exact_mod_cast this
  have hφpos : (0 : ℝ) < (Nat.totient d : ℝ) := by linarith
  -- 對數與平方根
  set LX := Real.log (2 * (d : ℝ) * X) with hLX
  have h2dX : (4 : ℝ) ≤ 2 * (d : ℝ) * X := by nlinarith
  have hLX1 : 1 ≤ LX := by
    rw [hLX]
    have : Real.exp 1 ≤ 2 * (d : ℝ) * X := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  have hLXsq : LX ≤ LX ^ 2 := by nlinarith
  have hlog2 : Real.log 2 ≤ LX := by
    rw [hLX]; exact Real.log_le_log (by norm_num) (by linarith)
  have hLU : Real.log (2 * (d : ℝ) * U) ≤ 2 * LX := by
    have hpos : (0 : ℝ) < 2 * (d : ℝ) * U := by
      have : (2 : ℝ) ≤ U := le_trans hXR hXURle
      positivity
    calc Real.log (2 * (d : ℝ) * U) ≤ Real.log (2 * (2 * (d : ℝ) * X)) := by
          apply Real.log_le_log hpos
          nlinarith
      _ = Real.log 2 + LX := by
          rw [hLX, Real.log_mul (by norm_num) (by positivity)]
      _ ≤ 2 * LX := by linarith
  have hLU0 : 0 ≤ Real.log (2 * (d : ℝ) * U) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ U := le_trans hXR hXURle
    nlinarith
  have hLU2 : Real.log (2 * (d : ℝ) * U) ^ 2 ≤ 4 * LX ^ 2 := by
    have := pow_le_pow_left₀ hLU0 hLU 2
    nlinarith
  have hsqU : √(U : ℝ) ≤ 2 * √(X : ℝ) := by
    have h4 : √(4 * (X : ℝ)) = 2 * √(X : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← h4]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqX1 : 1 ≤ √(X : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqX0 : 0 ≤ √(X : ℝ) := Real.sqrt_nonneg _
  have hlogU : Real.log U ≤ LX := by
    rw [hLX]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hlogX : Real.log X ≤ LX := by
    rw [hLX]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hlogU0 : 0 ≤ Real.log (U : ℝ) := Real.log_nonneg (by linarith)
  have hlogX0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by linarith)
  set B := √(X : ℝ) * LX ^ 2 with hB
  have hB1 : 1 ≤ B := by
    rw [hB]; nlinarith
  -- 誤差各項 ≤ 常數 · B
  have t1 : |psiR d a U - (U : ℝ) / (Nat.totient d : ℝ)| ≤ 8 * C₀ * B := by
    refine hEU.trans ?_
    rw [hB]
    calc C₀ * √(U : ℝ) * Real.log (2 * (d : ℝ) * U) ^ 2
        ≤ C₀ * (2 * √(X : ℝ)) * (4 * LX ^ 2) := by gcongr
      _ = 8 * C₀ * (√(X : ℝ) * LX ^ 2) := by ring
  have t2 : |psiR d a X - (X : ℝ) / (Nat.totient d : ℝ)| ≤ C₀ * B := by
    refine hEX.trans (le_of_eq ?_)
    rw [hB, hLX]
    ring
  have t3 : psiR d a U - thetaR d a U ≤ 4 * B := by
    refine hPU.trans ?_
    rw [hB]
    calc 2 * √(U : ℝ) * Real.log U ≤ 2 * (2 * √(X : ℝ)) * LX := by gcongr
      _ ≤ 2 * (2 * √(X : ℝ)) * LX ^ 2 := by gcongr
      _ = 4 * (√(X : ℝ) * LX ^ 2) := by ring
  have t4 : psiR d a X - thetaR d a X ≤ 2 * B := by
    refine hPX.trans ?_
    rw [hB]
    calc 2 * √(X : ℝ) * Real.log X ≤ 2 * √(X : ℝ) * LX := by gcongr
      _ ≤ 2 * √(X : ℝ) * LX ^ 2 := by gcongr
      _ = 2 * (√(X : ℝ) * LX ^ 2) := by ring
  have t5 : |((U : ℝ) - X - X / 50) / (Nat.totient d : ℝ)| ≤ 2 * B := by
    rw [abs_div, abs_of_pos hφpos]
    have habs : |(U : ℝ) - X - X / 50| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    calc |(U : ℝ) - X - X / 50| / (Nat.totient d : ℝ) ≤ 2 / 1 := by
          apply div_le_div₀ (by norm_num) habs (by norm_num) hφ
      _ = 2 := by norm_num
      _ ≤ 2 * B := by linarith
  -- 組合
  have hdecomp : thetaR d a U - thetaR d a X - (X : ℝ) / (50 * (Nat.totient d : ℝ)) =
      (psiR d a U - (U : ℝ) / (Nat.totient d : ℝ)) - (psiR d a X - (X : ℝ) / (Nat.totient d : ℝ))
        - (psiR d a U - thetaR d a U) + (psiR d a X - thetaR d a X)
        + ((U : ℝ) - X - X / 50) / (Nat.totient d : ℝ) := by
    field_simp
    ring
  have hgoal : |thetaR d a U - thetaR d a X - (X : ℝ) / (50 * (Nat.totient d : ℝ))| ≤
      (9 * C₀ + 8) * B := by
    rw [hdecomp]
    have e1 := abs_add_le
      ((psiR d a U - (U : ℝ) / (Nat.totient d : ℝ)) - (psiR d a X - (X : ℝ) / (Nat.totient d : ℝ))
        - (psiR d a U - thetaR d a U) + (psiR d a X - thetaR d a X))
      (((U : ℝ) - X - X / 50) / (Nat.totient d : ℝ))
    have e2 := abs_add_le
      ((psiR d a U - (U : ℝ) / (Nat.totient d : ℝ)) - (psiR d a X - (X : ℝ) / (Nat.totient d : ℝ))
        - (psiR d a U - thetaR d a U)) (psiR d a X - thetaR d a X)
    have e3 := abs_sub
      ((psiR d a U - (U : ℝ) / (Nat.totient d : ℝ)) - (psiR d a X - (X : ℝ) / (Nat.totient d : ℝ)))
      (psiR d a U - thetaR d a U)
    have e4 := abs_sub (psiR d a U - (U : ℝ) / (Nat.totient d : ℝ))
      (psiR d a X - (X : ℝ) / (Nat.totient d : ℝ))
    rw [abs_of_nonneg hPU0] at e3
    rw [abs_of_nonneg hPX0] at e2
    linarith
  calc |thetaR d a U - thetaR d a X - (X : ℝ) / (50 * (Nat.totient d : ℝ))|
      ≤ (9 * C₀ + 8) * B := hgoal
    _ = (9 * C₀ + 8) * √(X : ℝ) * (Real.log (2 * (d : ℝ) * X)) ^ 2 := by
        rw [hB, hLX]; ring

end TwinAPShort
