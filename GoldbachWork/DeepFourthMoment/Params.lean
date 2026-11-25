import GoldbachWork.DeepFourthMoment.Measure

/-!
# 參數：`n = 2^(12s)`、分母 `p ∈ (2^(4s), 2^(5s)]`（素數）、半徑 `d = 1/(16n)`
-/

open Real Complex MeasureTheory Finset

noncomputable section

namespace DeepFourthMoment

lemma two_pow_ge (s : ℕ) (hs : 20 ≤ s) : 40960 * s ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

lemma Q₁_pow (s : ℕ) : Q₁ (2 ^ (12 * s)) = 2 ^ (4 * s) := by
  unfold Q₁
  have h : ((2 ^ (12 * s) : ℕ) : ℝ) = (((2 ^ (4 * s) : ℕ) : ℝ)) ^ (3 : ℕ) := by
    push_cast
    rw [← pow_mul]
    ring_nf
  rw [h]
  have h3 : (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [h3, Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  exact Nat.floor_natCast _

lemma Q_pow (s : ℕ) (hs : 1 ≤ s) : Q (2 ^ (12 * s)) = (12 * s) ^ 2 := by
  unfold Q
  congr 1
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · have h2 : 2 < 2 ^ (12 * s) := by
      calc 2 < 2 ^ 12 := by norm_num
        _ ≤ 2 ^ (12 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]
    omega

lemma H_pow (s : ℕ) (hs : 1 ≤ s) : H (2 ^ (12 * s)) = 256 * 2 ^ (4 * s) * (12 * s) ^ 2 := by
  unfold H
  rw [Q₁_pow, Q_pow s hs]

/-- 兩個不同的既約分數 `a/p`、`a'/q`（`p` 素數、`p ∤ a`、`p ∤ q`）之差至少 `1/(pq)`。 -/
lemma abs_sub_frac_ge {p q a a' : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hne : a * q ≠ a' * p) :
    1 / ((p : ℝ) * q) ≤ |(a : ℝ) / p - (a' : ℝ) / q| := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hint : ((a * q : ℕ) : ℤ) - ((a' * p : ℕ) : ℤ) ≠ 0 := by
    intro h
    apply hne
    exact_mod_cast sub_eq_zero.mp h
  have h1 : (1 : ℤ) ≤ |((a * q : ℕ) : ℤ) - ((a' * p : ℕ) : ℤ)| := Int.one_le_abs hint
  have h1R : (1 : ℝ) ≤ |(a : ℝ) * q - (a' : ℝ) * p| := by
    have := h1
    have hc : (((|((a * q : ℕ) : ℤ) - ((a' * p : ℕ) : ℤ)|) : ℤ) : ℝ) =
        |(a : ℝ) * q - (a' : ℝ) * p| := by
      push_cast
      rfl
    rw [← hc]
    exact_mod_cast this
  have heq : (a : ℝ) / p - (a' : ℝ) / q = ((a : ℝ) * q - (a' : ℝ) * p) / ((p : ℝ) * q) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) * q)]
  exact div_le_div_of_nonneg_right h1R (by positivity)

end DeepFourthMoment
