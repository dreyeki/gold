import Mathlib

/-!
# 反證 `L-goldbach-frontier-deep-fourth-moment-conjecture`：基本定義與指數和

本檔定義與平台命題逐字相同的物件（`E`、`S`、`wideArcs` 等），並證明
素數模的 Ramanujan 和公式。
-/

open Real Complex MeasureTheory Finset

noncomputable section

namespace DeepFourthMoment

/-- 素數的對數權，非素數權為零。 -/
def wP (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

/-- `E x = exp(2πix)`，寫法與平台命題相同。 -/
def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- `S_n(t) = Σ_{k≤n} w(k) e(kt)`。 -/
def S (n : ℕ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (wP k : ℂ) * E ((k : ℝ) * t))

def Q (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def Q₁ (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊

def H (n : ℕ) : ℕ := 256 * Q₁ n * Q n

def wideArcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))}

/-- 深次弧上的四階矩。 -/
def I4 (n : ℕ) : ℝ :=
  intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => ‖S n u‖ ^ 4) t) (0 : ℝ) 1
    MeasureTheory.volume

lemma wP_nonneg (k : ℕ) : 0 ≤ wP k := by
  unfold wP
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_rfl

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_E (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  exact Complex.norm_exp_ofReal_mul_I _

lemma E_re (x : ℝ) : (E x).re = Real.cos (2 * Real.pi * x) := by
  unfold E
  rw [Complex.exp_ofReal_mul_I_re]

lemma continuous_E : Continuous E := by
  unfold E
  fun_prop

lemma E_nat_mul (m : ℕ) (x : ℝ) : E ((m : ℝ) * x) = E x ^ m := by
  unfold E
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma E_intCast (m : ℤ) : E (m : ℝ) = 1 := by
  unfold E
  rw [Complex.exp_eq_one_iff]
  exact ⟨m, by push_cast; ring⟩

lemma E_eq_one_iff (x : ℝ) : E x = 1 ↔ ∃ m : ℤ, x = m := by
  constructor
  · intro h
    unfold E at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    refine ⟨m, ?_⟩
    have h2 : ((2 * Real.pi * x : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi) := by
      have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
      have := hm
      calc ((2 * Real.pi * x : ℝ) : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I / Complex.I := by
            field_simp
        _ = (m : ℂ) * (2 * Real.pi * Complex.I) / Complex.I := by rw [this]
        _ = (m : ℂ) * (2 * Real.pi) := by field_simp
    have h3 : (2 * Real.pi * x : ℝ) = (m : ℝ) * (2 * Real.pi) := by exact_mod_cast h2
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : x = m := by
      have := h3
      field_simp at this
      linarith
    exact this
  · rintro ⟨m, rfl⟩
    exact E_intCast m

lemma continuous_S (n : ℕ) : Continuous (S n) := by
  unfold S
  refine continuous_finsetSum _ fun k _ => ?_
  exact continuous_const.mul (continuous_E.comp (continuous_const.mul continuous_id))

/-- 素數模的 Ramanujan 和：`Σ_{1≤a<p} e(ka/p)` 在 `p ∤ k` 時為 `-1`，在 `p ∣ k` 時為 `p-1`。 -/
lemma sum_E_prime {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ a ∈ Finset.Ico 1 p, E ((k : ℝ) * ((a : ℝ) / (p : ℝ))) =
      if p ∣ k then ((p : ℂ) - 1) else -1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set ζ := E ((k : ℝ) / (p : ℝ)) with hζ
  have hterm : ∀ a : ℕ, E ((k : ℝ) * ((a : ℝ) / (p : ℝ))) = ζ ^ a := by
    intro a
    rw [hζ, ← E_nat_mul]
    congr 1
    ring
  have hfull : ∑ a ∈ Finset.range p, ζ ^ a = 1 + ∑ a ∈ Finset.Ico 1 p, ζ ^ a := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.pos]
    simp
  simp_rw [hterm]
  have hζp : ζ ^ p = 1 := by
    rw [hζ, ← E_nat_mul]
    have : (p : ℝ) * ((k : ℝ) / (p : ℝ)) = ((k : ℤ) : ℝ) := by
      field_simp
      simp
    rw [this, E_intCast]
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    have hζ1 : ζ = 1 := by
      rw [hζ]
      have : ((p * m : ℕ) : ℝ) / (p : ℝ) = ((m : ℤ) : ℝ) := by
        push_cast
        field_simp
      rw [this, E_intCast]
    rw [hζ1]
    simp only [one_pow, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub hp.one_lt.le]
    simp
  · have hζ1 : ζ ≠ 1 := by
      intro h1
      rw [hζ, E_eq_one_iff] at h1
      obtain ⟨m, hm⟩ := h1
      apply hdvd
      have hk : (k : ℝ) = (p : ℝ) * m := by
        field_simp at hm
        linarith
      have hk' : (k : ℤ) = (p : ℤ) * m := by exact_mod_cast hk
      have : (p : ℤ) ∣ (k : ℤ) := ⟨m, hk'⟩
      exact_mod_cast this
    have hgeom : ∑ a ∈ Finset.range p, ζ ^ a = 0 := by
      rw [geom_sum_eq hζ1, hζp]
      simp
    have := hfull
    rw [hgeom] at this
    linear_combination -this

end DeepFourthMoment
