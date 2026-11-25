import GoldbachWork.DeepFourthMoment.Main

/-!
# 總組裝與最終定理
-/

open Real Complex MeasureTheory Finset

noncomputable section

namespace DeepFourthMoment

/-- 核心估計：對 `s ≥ 20`，`I4(2^(12s)) > 2^(25s)`。 -/
theorem I4_lower (s : ℕ) (hs : 20 ≤ s) : ((2 : ℝ) ^ s) ^ 25 < I4 (2 ^ (12 * s)) := by
  set n := 2 ^ (12 * s) with hn_def
  set d : ℝ := 1 / (16 * (n : ℝ)) with hd_def
  obtain ⟨hz20, hzs⟩ := z_facts s hs
  set z := (2 : ℝ) ^ s with hz
  have hz1 : 1 ≤ z := le_trans (by norm_num) hz20
  have hzpos : 0 < z := by positivity
  have hnR : (n : ℝ) = z ^ 12 := cast_n s
  have hnpos : 0 < n := by positivity
  have hd : 0 < d := by rw [hd_def]; positivity
  have hdn : d * (n : ℝ) = 1 / 16 := by
    rw [hd_def]; field_simp
  have hs0 : (0 : ℝ) < s := by
    have : (20 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  -- 第一步：深次弧積分 ≥ 小弧積分之和
  have h1 := sum_arcs_le_I4 n (Xs s) ctr hd (fun x hx => arc_subset hs hx)
    (fun x hx t ht => arc_not_mem_wideArcs hs hx ht) (arcs_disjoint s hs)
  set J : (Σ _ : ℕ, ℕ) → ℂ := fun x => ∫ t in (ctr x - d)..(ctr x + d), S n t with hJ
  -- 第二步：單弧 Jensen
  have h2 : ∑ x ∈ Xs s, ‖J x‖ ^ 4 ≤
      (2 * d) ^ 3 * ∑ x ∈ Xs s, ∫ t in (ctr x - d)..(ctr x + d), ‖S n t‖ ^ 4 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => norm_J_pow_four_le n (ctr x) hd
  -- 第三步：冪平均
  have h3 := pow_sum_div_card_le_sum_pow (s := Xs s) (f := fun x => ‖J x‖)
    (fun x _ => norm_nonneg _) 3
  -- 第四步：Σ‖J‖ ≥ K·d·n/2
  set K : ℝ := ((Qs s).card : ℝ) with hK
  have h4 : K * (d * n / 2) ≤ ∑ x ∈ Xs s, ‖J x‖ := by
    calc K * (d * n / 2) = ∑ p ∈ Qs s, d * n / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ Qs s, (-(∑ a ∈ Finset.Ico 1 p, J ⟨p, a⟩)).re := by
          apply Finset.sum_le_sum
          intro p hp
          have hpQ := Finset.mem_filter.mp hp
          have hpY := (Finset.mem_Ioc.mp hpQ.1).2
          have hpn : p ≤ n := le_trans hpY (Nat.pow_le_pow_right (by norm_num) (by omega))
          have hJp := sum_J_prime hpQ.2 hpn hnpos
          have ht := theta_part_ge s hs hpQ.2 hpY
          calc d * n / 2 = d * ((n : ℝ) / 2) := by ring
            _ ≤ d * ((9 / 5) * (∑ k ∈ Finset.range (n + 1), wP k) - 2 * (p : ℝ) * Real.log p) :=
                mul_le_mul_of_nonneg_left ht hd.le
            _ ≤ _ := hJp
      _ = ∑ x ∈ Xs s, (-(J x)).re := by
          rw [Xs, Finset.sum_sigma]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_neg_distrib, Complex.re_sum]
      _ ≤ ∑ x ∈ Xs s, ‖J x‖ := Finset.sum_le_sum fun x _ => by
          have := Complex.re_le_norm (-(J x))
          rwa [norm_neg] at this
  -- 第五步：#X ≤ K·z^5
  have h5 : ((Xs s).card : ℝ) ≤ K * z ^ 5 := by
    rw [Xs, Finset.card_sigma]
    push_cast
    calc ∑ p ∈ Qs s, ((Finset.Ico 1 p).card : ℝ) ≤ ∑ p ∈ Qs s, z ^ 5 := by
          apply Finset.sum_le_sum
          intro p hp
          have hpY := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
          have hc : (Finset.Ico 1 p).card ≤ 2 ^ (5 * s) := by
            rw [Nat.card_Ico]; omega
          have : (((Finset.Ico 1 p).card : ℕ) : ℝ) ≤ ((2 ^ (5 * s) : ℕ) : ℝ) := by
            exact_mod_cast hc
          rw [show ((2 ^ (5 * s) : ℕ) : ℝ) = z ^ 5 by push_cast; rw [hz, two_pow_mul_eq]]
            at this
          exact this
      _ = K * z ^ 5 := by rw [Finset.sum_const, nsmul_eq_mul]
  -- K 的下界與正性
  have hKge := card_Qs_ge s hs
  rw [← hK] at hKge
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hKge
  -- 組合
  set A := ∑ x ∈ Xs s, ‖J x‖ with hA
  set C : ℝ := ((Xs s).card : ℝ) with hC
  have hA0 : 0 < K * (d * n / 2) := by positivity
  have hApos : 0 < A := lt_of_lt_of_le hA0 h4
  have hCpos : 0 < C := by
    rcases (Nat.eq_zero_or_pos (Xs s).card) with h0 | h0
    · exfalso
      have hempty : Xs s = ∅ := Finset.card_eq_zero.mp h0
      have : A = 0 := by rw [hA, hempty, Finset.sum_empty]
      linarith
    · rw [hC]; exact_mod_cast h0
  have hchain : A ^ 4 / C ^ 3 ≤ (2 * d) ^ 3 * I4 n := by
    have := h3.trans (h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity)))
    simpa [hA, hC] using this
  have hlow : (K * (d * n / 2)) ^ 4 / (K * z ^ 5) ^ 3 ≤ A ^ 4 / C ^ 3 := by
    apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hA0.le h4 4) (by positivity)
      (pow_le_pow_left₀ hCpos.le h5 3)
  have hmain : (K * (d * n / 2)) ^ 4 / (K * z ^ 5) ^ 3 ≤ (2 * d) ^ 3 * I4 n :=
    hlow.trans hchain
  -- 化簡：(K/32)^4/(K z^5)^3 ≤ (1/(8 z^12))^3 · I4
  have hdn2 : d * (n : ℝ) / 2 = 1 / 32 := by rw [hdn]; norm_num
  have h2d : 2 * d = 1 / (8 * z ^ 12) := by
    rw [hd_def, hnR]; field_simp; ring
  rw [hdn2, h2d] at hmain
  have hsimp : (K * (1 / 32)) ^ 4 / (K * z ^ 5) ^ 3 = K / (1048576 * z ^ 15) := by
    field_simp; ring
  rw [hsimp] at hmain
  have hI : K * z ^ 21 / 2048 ≤ I4 n := by
    have h512 : (1 / (8 * z ^ 12)) ^ 3 = 1 / (512 * z ^ 36) := by field_simp; ring
    rw [h512] at hmain
    have hz36 : 0 < 512 * z ^ 36 := by positivity
    have := mul_le_mul_of_nonneg_left hmain hz36.le
    have e1 : 512 * z ^ 36 * (K / (1048576 * z ^ 15)) = K * z ^ 21 / 2048 := by
      field_simp; ring
    have e2 : 512 * z ^ 36 * (1 / (512 * z ^ 36) * I4 n) = I4 n := by
      field_simp
    rw [e1, e2] at this
    exact this
  -- 最後的數值比較
  have hK2 : z ^ 26 / (10 * s * 2048) ≤ K * z ^ 21 / 2048 := by
    have := mul_le_mul_of_nonneg_right hKge (by positivity : (0 : ℝ) ≤ z ^ 21 / 2048)
    calc z ^ 26 / (10 * s * 2048) = z ^ 5 / (10 * s) * (z ^ 21 / 2048) := by
          field_simp
      _ ≤ K * (z ^ 21 / 2048) := this
      _ = K * z ^ 21 / 2048 := by ring
  have hfin : z ^ 25 < z ^ 26 / (10 * s * 2048) := by
    rw [lt_div_iff₀ (by positivity)]
    have : z ^ 26 = z ^ 25 * z := by ring
    rw [this]
    have h25 : 0 < z ^ 25 := by positivity
    have : 10 * (s : ℝ) * 2048 < z := by linarith
    nlinarith
  linarith

theorem not_deep_fourth_moment :
    ¬ (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → I4 n ≤ (n : ℝ) ^ (2 + η)) := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 12) (by norm_num)
  set s := max N 20 with hs_def
  have hs : 20 ≤ s := le_max_right _ _
  have hNs : N ≤ 2 ^ (12 * s) := by
    have h1 : N ≤ s := le_max_left _ _
    have h2 : s < 2 ^ s := Nat.lt_two_pow_self
    have h3 : 2 ^ s ≤ 2 ^ (12 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 := hN _ hNs
  have h2 := I4_lower s hs
  have h3 : (((2 ^ (12 * s) : ℕ) : ℝ)) ^ ((2 : ℝ) + 1 / 12) = ((2 : ℝ) ^ s) ^ 25 := by
    rw [cast_n, ← Real.rpow_natCast ((2 : ℝ) ^ s) 12, ← Real.rpow_mul (by positivity)]
    rw [show ((12 : ℕ) : ℝ) * (2 + 1 / 12) = ((25 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3] at h1
  linarith

end DeepFourthMoment

/-- 平台命題 `L-goldbach-frontier-deep-fourth-moment-conjecture` 的逐字否定。 -/
theorem L_goldbach_frontier_deep_fourth_moment_conjecture_is_false :
    ¬ (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => ‖S n w u‖ ^ 4) t) (0 : ℝ) 1 MeasureTheory.volume ≤ (n : ℝ) ^ (2 + η)) := by
  intro h
  exact DeepFourthMoment.not_deep_fourth_moment h

#print axioms L_goldbach_frontier_deep_fourth_moment_conjecture_is_false
