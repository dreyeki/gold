import GoldbachWork.DeepFourthMoment.Params

/-!
# 主定理：深次弧四階矩猜想不成立

取 `n = 2^(12s)`，以及所有素數 `p ∈ (2^(4s), 2^(5s)]`、`1 ≤ a < p`。
半徑 `d = 1/(16n)` 的小弧 `[a/p - d, a/p + d]` 落在深次弧內且互不相交。
單弧 Jensen 不等式、冪平均不等式、Ramanujan 和與 Chebyshev 下界合起來給出

  `I4 n ≥ K·n³/(2048·Y³) ≥ 2^(26s)/(20480 s) > 2^(25s) = n^(2+1/12)`。

因此對 `η = 1/12`，命題 `∀ η>0, ∃N, ∀ n≥N, I4 n ≤ n^(2+η)` 不成立。
-/

open Real Complex MeasureTheory Finset

noncomputable section

namespace DeepFourthMoment

/-- 素數分母集合 `{p 素數 : 2^(4s) < p ≤ 2^(5s)}`。 -/
def Qs (s : ℕ) : Finset ℕ := (Finset.Ioc (2 ^ (4 * s)) (2 ^ (5 * s))).filter Nat.Prime

/-- 弧的指標 `(p, a)`，`p ∈ Qs s`、`1 ≤ a < p`。 -/
def Xs (s : ℕ) : Finset (Σ _ : ℕ, ℕ) := (Qs s).sigma fun p => Finset.Ico 1 p

/-- 弧心 `a/p`。 -/
def ctr (x : Σ _ : ℕ, ℕ) : ℝ := (x.2 : ℝ) / (x.1 : ℝ)

lemma mem_Xs {s : ℕ} {x : Σ _ : ℕ, ℕ} (hx : x ∈ Xs s) :
    x.1.Prime ∧ 2 ^ (4 * s) < x.1 ∧ x.1 ≤ 2 ^ (5 * s) ∧ 1 ≤ x.2 ∧ x.2 < x.1 := by
  simp only [Xs, Qs, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico] at hx
  exact ⟨hx.1.2, hx.1.1.1, hx.1.1.2, hx.2.1, hx.2.2⟩

lemma two_pow_mul_eq (k s : ℕ) : (2 : ℝ) ^ (k * s) = ((2 : ℝ) ^ s) ^ k := by
  rw [← pow_mul, mul_comm]

/-- 以 `z = 2^s` 表示的基本數值事實。 -/
lemma z_facts (s : ℕ) (hs : 20 ≤ s) :
    (2 : ℝ) ^ 20 ≤ (2 : ℝ) ^ s ∧ 40960 * (s : ℝ) ≤ (2 : ℝ) ^ s := by
  refine ⟨pow_le_pow_right₀ (by norm_num) hs, ?_⟩
  have := two_pow_ge s hs
  exact_mod_cast this

lemma cast_n (s : ℕ) : ((2 ^ (12 * s) : ℕ) : ℝ) = ((2 : ℝ) ^ s) ^ 12 := by
  push_cast; exact two_pow_mul_eq 12 s

lemma ctr_bounds {s : ℕ} {x : Σ _ : ℕ, ℕ} (hx : x ∈ Xs s) :
    1 / ((2 : ℝ) ^ s) ^ 5 ≤ ctr x ∧ ctr x ≤ 1 - 1 / ((2 : ℝ) ^ s) ^ 5 := by
  obtain ⟨hp, hp1, hp2, ha1, ha2⟩ := mem_Xs hx
  have hpR : (0 : ℝ) < x.1 := by exact_mod_cast hp.pos
  have hpz : (x.1 : ℝ) ≤ ((2 : ℝ) ^ s) ^ 5 := by
    rw [← two_pow_mul_eq]; exact_mod_cast hp2
  have ha1R : (1 : ℝ) ≤ x.2 := by exact_mod_cast ha1
  have ha2R : (x.2 : ℝ) ≤ x.1 - 1 := by
    have : x.2 + 1 ≤ x.1 := ha2
    have : ((x.2 + 1 : ℕ) : ℝ) ≤ x.1 := by exact_mod_cast this
    push_cast at this; linarith
  have hz5 : (0 : ℝ) < ((2 : ℝ) ^ s) ^ 5 := by positivity
  unfold ctr
  constructor
  · calc 1 / ((2 : ℝ) ^ s) ^ 5 ≤ 1 / (x.1 : ℝ) := one_div_le_one_div_of_le hpR hpz
      _ ≤ (x.2 : ℝ) / x.1 := div_le_div_of_nonneg_right ha1R hpR.le
  · have h1 : (x.2 : ℝ) / x.1 ≤ 1 - 1 / (x.1 : ℝ) := by
      rw [le_sub_iff_add_le, ← add_div, div_le_one hpR]; linarith
    have h2 : 1 / ((2 : ℝ) ^ s) ^ 5 ≤ 1 / (x.1 : ℝ) := one_div_le_one_div_of_le hpR hpz
    linarith

/-- 小弧落在 `(0, 1]` 內。 -/
lemma arc_subset {s : ℕ} (hs : 20 ≤ s) {x : Σ _ : ℕ, ℕ} (hx : x ∈ Xs s) :
    Set.Icc (ctr x - 1 / (16 * ((2 ^ (12 * s) : ℕ) : ℝ)))
      (ctr x + 1 / (16 * ((2 ^ (12 * s) : ℕ) : ℝ))) ⊆ Set.Ioc 0 1 := by
  obtain ⟨hc1, hc2⟩ := ctr_bounds hx
  obtain ⟨hz20, -⟩ := z_facts s hs
  set z := (2 : ℝ) ^ s
  have hz1 : 1 ≤ z := le_trans (by norm_num) hz20
  have hd : 1 / (16 * ((2 ^ (12 * s) : ℕ) : ℝ)) < 1 / z ^ 5 := by
    rw [cast_n]
    apply one_div_lt_one_div_of_lt (by positivity)
    have : z ^ 5 ≤ z ^ 12 := pow_le_pow_right₀ hz1 (by norm_num)
    have : 0 < z ^ 12 := by positivity
    linarith
  intro t ⟨ht1, ht2⟩
  constructor <;> linarith

/-- 小弧落在深次弧內（不與任何寬弧相交）。 -/
lemma arc_not_mem_wideArcs {s : ℕ} (hs : 20 ≤ s) {x : Σ _ : ℕ, ℕ} (hx : x ∈ Xs s) {t : ℝ}
    (ht : t ∈ Set.Icc (ctr x - 1 / (16 * ((2 ^ (12 * s) : ℕ) : ℝ)))
      (ctr x + 1 / (16 * ((2 ^ (12 * s) : ℕ) : ℝ)))) :
    t ∉ wideArcs (2 ^ (12 * s)) := by
  obtain ⟨hp, hp1, hp2, ha1, ha2⟩ := mem_Xs hx
  rintro ⟨q, a', hq1, hqQ, ha'q, -, hdist⟩
  rw [Q₁_pow] at hqQ
  rw [H_pow s (by omega)] at hdist
  have hne : x.2 * q ≠ a' * x.1 := by
    intro h
    have hdvd : x.1 ∣ x.2 * q := ⟨a', by rw [h, mul_comm]⟩
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
    · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
    · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
  have hsep := abs_sub_frac_ge (p := x.1) (q := q) (a := x.2) (a' := a') hp.pos (by omega) hne
  obtain ⟨hz20, hzs⟩ := z_facts s hs
  set z := (2 : ℝ) ^ s with hz
  set d := 1 / (16 * ((2 ^ (12 * s) : ℕ) : ℝ)) with hd_def
  have hnR := cast_n s
  have hz1 : 1 ≤ z := le_trans (by norm_num) hz20
  have hzpos : 0 < z := by positivity
  have hpR : (0 : ℝ) < x.1 := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
  have hpz : (x.1 : ℝ) ≤ z ^ 5 := by rw [hz, ← two_pow_mul_eq]; exact_mod_cast hp2
  have hqz : (q : ℝ) ≤ z ^ 4 := by rw [hz, ← two_pow_mul_eq]; exact_mod_cast hqQ
  have htc : |t - ctr x| ≤ d := abs_sub_le_iff.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  -- 三角不等式
  have htri : |(x.2 : ℝ) / x.1 - (a' : ℝ) / q| ≤
      d + ((256 * 2 ^ (4 * s) * (12 * s) ^ 2 : ℕ) : ℝ) / ((q : ℝ) * ((2 ^ (12 * s) : ℕ) : ℝ)) := by
    have := abs_sub_le ((x.2 : ℝ) / x.1) t ((a' : ℝ) / q)
    have h1 : |(x.2 : ℝ) / x.1 - t| = |t - ctr x| := by rw [abs_sub_comm]; rfl
    linarith
  have hineq := hsep.trans htri
  set Hn : ℝ := ((256 * 2 ^ (4 * s) * (12 * s) ^ 2 : ℕ) : ℝ) with hHn
  have hHz : Hn = 256 * z ^ 4 * (12 * (s : ℝ)) ^ 2 := by
    rw [hHn, hz, ← two_pow_mul_eq]; push_cast; ring
  set nR : ℝ := ((2 ^ (12 * s) : ℕ) : ℝ) with hnR_def
  have hnpos : 0 < nR := by rw [hnR]; positivity
  have hdn : d * nR = 1 / 16 := by rw [hd_def]; field_simp
  -- 乘以 p q n
  have hmul : nR ≤ (x.1 : ℝ) * q / 16 + Hn * x.1 := by
    have hpqn : 0 ≤ (x.1 : ℝ) * q * nR := by positivity
    have := mul_le_mul_of_nonneg_right hineq hpqn
    have e1 : 1 / ((x.1 : ℝ) * q) * ((x.1 : ℝ) * q * nR) = nR := by field_simp
    have e2 : (d + Hn / ((q : ℝ) * nR)) * ((x.1 : ℝ) * q * nR) =
        (x.1 : ℝ) * q * (d * nR) + Hn * x.1 := by field_simp
    rw [e1, e2, hdn] at this
    linarith
  -- 數值矛盾
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hpq : (x.1 : ℝ) * q ≤ z ^ 9 := by
    calc (x.1 : ℝ) * q ≤ z ^ 5 * z ^ 4 := mul_le_mul hpz hqz hqR.le (by positivity)
      _ = z ^ 9 := by ring
  have hHp : Hn * x.1 ≤ 36864 * (s : ℝ) ^ 2 * z ^ 9 := by
    rw [hHz]
    calc 256 * z ^ 4 * (12 * (s : ℝ)) ^ 2 * x.1 ≤ 256 * z ^ 4 * (12 * (s : ℝ)) ^ 2 * z ^ 5 := by
          gcongr
      _ = 36864 * (s : ℝ) ^ 2 * z ^ 9 := by ring
  have hz12 : nR = z ^ 9 * z ^ 3 := by rw [hnR]; ring
  have hkey : z ^ 9 * z ^ 3 ≤ z ^ 9 * (1 / 16 + 36864 * (s : ℝ) ^ 2) := by
    rw [← hz12]; nlinarith
  have hz3 : z ^ 3 ≤ 1 / 16 + 36864 * (s : ℝ) ^ 2 :=
    le_of_mul_le_mul_left hkey (by positivity)
  have hs2 : (s : ℝ) ^ 2 ≤ (z / 40960) ^ 2 := by
    apply pow_le_pow_left₀ hs0; linarith
  have hz2 : 2 ^ 20 * z ^ 2 ≤ z ^ 3 := by
    have : z ^ 3 = z * z ^ 2 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hz20 (by positivity)
  have hz2' : 1 ≤ z ^ 2 := one_le_pow₀ hz1
  nlinarith

/-- 不同的小弧互不相交。 -/
lemma arcs_disjoint (s : ℕ) (hs : 20 ≤ s) :
    Set.Pairwise (Xs s : Set (Σ _ : ℕ, ℕ))
      (Function.onFun Disjoint fun x => Set.Icc (ctr x - 1 / (16 * ((2 ^ (12 * s) : ℕ) : ℝ)))
        (ctr x + 1 / (16 * ((2 ^ (12 * s) : ℕ) : ℝ)))) := by
  intro x hx y hy hxy
  obtain ⟨hp, hp1, hp2, ha1, ha2⟩ := mem_Xs hx
  obtain ⟨hq, hq1, hq2, hb1, hb2⟩ := mem_Xs hy
  rw [Function.onFun, Set.disjoint_left]
  intro t ht1 ht2
  have hne : x.2 * y.1 ≠ y.2 * x.1 := by
    intro h
    have hdvd : x.1 ∣ x.2 * y.1 := ⟨y.2, by rw [h, mul_comm]⟩
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
    · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
    · have hpq : x.1 = y.1 := (Nat.prime_dvd_prime_iff_eq hp hq).mp h1
      have hab : x.2 = y.2 := by
        rw [hpq] at h
        exact Nat.eq_of_mul_eq_mul_right hq.pos h
      exact hxy (Sigma.ext hpq (heq_of_eq hab))
  have hsep := abs_sub_frac_ge (p := x.1) (q := y.1) (a := x.2) (a' := y.2) hp.pos hq.pos hne
  obtain ⟨hz20, -⟩ := z_facts s hs
  set z := (2 : ℝ) ^ s with hz
  have hz1 : 1 ≤ z := le_trans (by norm_num) hz20
  have hpz : (x.1 : ℝ) ≤ z ^ 5 := by rw [hz, ← two_pow_mul_eq]; exact_mod_cast hp2
  have hqz : (y.1 : ℝ) ≤ z ^ 5 := by rw [hz, ← two_pow_mul_eq]; exact_mod_cast hq2
  have hpR : (0 : ℝ) < x.1 := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < y.1 := by exact_mod_cast hq.pos
  have hsep' : 1 / z ^ 10 ≤ |ctr x - ctr y| := by
    refine le_trans ?_ hsep
    apply one_div_le_one_div_of_le (by positivity)
    calc (x.1 : ℝ) * y.1 ≤ z ^ 5 * z ^ 5 := mul_le_mul hpz hqz hqR.le (by positivity)
      _ = z ^ 10 := by ring
  have hclose : |ctr x - ctr y| ≤ 2 * (1 / (16 * ((2 ^ (12 * s) : ℕ) : ℝ))) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [ht1.1, ht1.2, ht2.1, ht2.2]
  rw [cast_n, ← hz] at hclose
  have hlt : 2 * (1 / (16 * z ^ 12)) < 1 / z ^ 10 := by
    have h10 : 0 < z ^ 10 := by positivity
    have : z ^ 12 = z ^ 10 * z ^ 2 := by ring
    rw [this]
    have hz2 : 1 ≤ z ^ 2 := one_le_pow₀ hz1
    rw [show 2 * (1 / (16 * (z ^ 10 * z ^ 2))) = 1 / (8 * z ^ 2 * z ^ 10) by
      field_simp; ring]
    apply one_div_lt_one_div_of_lt h10
    nlinarith
  linarith

lemma sum_wP_eq_theta (n : ℕ) : ∑ k ∈ Finset.range (n + 1), wP k = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  unfold wP
  rw [← Finset.sum_filter]
  rfl

/-- θ 的下界：對 `p ≤ 2^(5s)`，`(9/5)θ(n) - 2 p log p ≥ n/2`。 -/
lemma theta_part_ge (s : ℕ) (hs : 20 ≤ s) {p : ℕ} (hp : p.Prime) (hpY : p ≤ 2 ^ (5 * s)) :
    ((2 ^ (12 * s) : ℕ) : ℝ) / 2 ≤
      (9 / 5) * (∑ k ∈ Finset.range (2 ^ (12 * s) + 1), wP k) - 2 * (p : ℝ) * Real.log p := by
  rw [sum_wP_eq_theta]
  have hth := Chebyshev.theta_ge (2 ^ (12 * s))
  obtain ⟨hz20, hzs⟩ := z_facts s hs
  set z := (2 : ℝ) ^ s with hz
  have hz1 : 1 ≤ z := le_trans (by norm_num) hz20
  have hnR := cast_n s
  rw [hnR] at hth ⊢
  have hL := Real.log_two_gt_d9
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log (z ^ 12) = 12 * s * Real.log 2 := by
    rw [hz, ← pow_mul, Real.log_pow]; push_cast; ring
  have hsqrt : √(z ^ 12) = z ^ 6 := by
    rw [show z ^ 12 = (z ^ 6) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hlogn1 : Real.log (z ^ 12 + 1) ≤ Real.log 2 + 12 * s * Real.log 2 := by
    rw [← hlogn, ← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    have : 1 ≤ z ^ 12 := one_le_pow₀ hz1
    linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpz : (p : ℝ) ≤ z ^ 5 := by rw [hz, ← two_pow_mul_eq]; exact_mod_cast hpY
  have hlogp : Real.log p ≤ 5 * s * Real.log 2 := by
    calc Real.log p ≤ Real.log (z ^ 5) := Real.log_le_log hpR hpz
      _ = 5 * s * Real.log 2 := by rw [hz, ← pow_mul, Real.log_pow]; push_cast; ring
  have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  rw [hsqrt, hlogn] at hth
  -- θ ≥ log2 · (z^12 - 1 - 12s - 24 s z^6)
  have hθ : Real.log 2 * (z ^ 12 - 1 - 12 * s - 24 * s * z ^ 6) ≤ Chebyshev.theta (z ^ 12) := by
    nlinarith
  have hplogp : (p : ℝ) * Real.log p ≤ z ^ 5 * (5 * s * Real.log 2) :=
    mul_le_mul hpz hlogp hlogp0 (by positivity)
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hsz : (s : ℝ) ≤ z := by linarith
  have hz7 : 1 ≤ z ^ 7 := one_le_pow₀ hz1
  have h1 : (s : ℝ) * z ^ 6 ≤ z ^ 7 := by
    calc (s : ℝ) * z ^ 6 ≤ z * z ^ 6 := by gcongr
      _ = z ^ 7 := by ring
  have h2 : (s : ℝ) * z ^ 5 ≤ z ^ 7 := by
    calc (s : ℝ) * z ^ 5 ≤ z * z ^ 6 := by
          apply mul_le_mul hsz (pow_le_pow_right₀ hz1 (by norm_num)) (by positivity) (by positivity)
      _ = z ^ 7 := by ring
  have h3 : (s : ℝ) ≤ z ^ 7 := hsz.trans (le_self_pow₀ hz1 (by norm_num))
  have h4 : 100 * z ^ 7 ≤ z ^ 12 := by
    have : z ^ 12 = z ^ 5 * z ^ 7 := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : (2 : ℝ) ^ 20 ≤ z ^ 5 := le_trans hz20 (le_self_pow₀ hz1 (by norm_num))
    linarith
  -- 括號 ≥ z^12
  have hbr : z ^ 12 ≤ (9 / 5) * (z ^ 12 - 1 - 12 * s - 24 * s * z ^ 6) - 10 * s * z ^ 5 := by
    nlinarith
  have hfinal : z ^ 12 / 2 ≤ Real.log 2 * ((9 / 5) * (z ^ 12 - 1 - 12 * s - 24 * s * z ^ 6)
      - 10 * s * z ^ 5) := by
    have : 0 ≤ z ^ 12 := by positivity
    nlinarith
  nlinarith

/-- 素數分母個數的下界：`#Qs ≥ 2^(5s)/(10 s)`。 -/
lemma card_Qs_ge (s : ℕ) (hs : 20 ≤ s) :
    ((2 : ℝ) ^ s) ^ 5 / (10 * s) ≤ ((Qs s).card : ℝ) := by
  have hpi := Chebyshev.pi_ge_of_four_le (n := 2 ^ (5 * s)) (by
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (5 * s) := Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨hz20, hzs⟩ := z_facts s hs
  set z := (2 : ℝ) ^ s with hz
  have hz1 : 1 ≤ z := le_trans (by norm_num) hz20
  have hs0 : (0 : ℝ) < s := by have : (20 : ℝ) ≤ s := by exact_mod_cast hs
                               linarith
  have hY : ((2 ^ (5 * s) : ℕ) : ℝ) = z ^ 5 := by push_cast; rw [hz, two_pow_mul_eq]
  rw [hY] at hpi
  have hlog : Real.log (z ^ 5) = 5 * s * Real.log 2 := by
    rw [hz, ← pow_mul, Real.log_pow]; push_cast; ring
  rw [hlog] at hpi
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi' : z ^ 5 / (5 * s) ≤ (Nat.primeCounting (2 ^ (5 * s)) : ℝ) := by
    have : z ^ 5 * Real.log 2 / (5 * s * Real.log 2) = z ^ 5 / (5 * s) := by
      field_simp
    rw [← this]; exact hpi
  -- π(Y) ≤ #Qs + 2^(4s) + 1
  have hsub : Nat.primesLE (2 ^ (5 * s)) ⊆ Qs s ∪ Finset.range (2 ^ (4 * s) + 1) := by
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp
    simp only [Qs, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    by_cases h : p ≤ 2 ^ (4 * s)
    · right; omega
    · left; exact ⟨⟨by omega, by omega⟩, hp.2⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Nat.primesLE_card_eq_primeCounting, Finset.card_range] at hcard
  have hcardR : (Nat.primeCounting (2 ^ (5 * s)) : ℝ) ≤ ((Qs s).card : ℝ) + (z ^ 4 + 1) := by
    have : ((Nat.primeCounting (2 ^ (5 * s)) : ℕ) : ℝ) ≤
        (((Qs s).card + (2 ^ (4 * s) + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at this
    rw [hz, ← two_pow_mul_eq]; linarith
  -- z^5/(10s) ≤ z^5/(5s) - z^4 - 1
  have hz4 : 1 ≤ z ^ 4 := one_le_pow₀ hz1
  have hkey : z ^ 5 / (10 * s) + (z ^ 4 + 1) ≤ z ^ 5 / (5 * s) := by
    have h20 : 20 * (s : ℝ) ≤ z := by linarith
    have hA1 : z ^ 4 + 1 ≤ 2 * z ^ 4 := by linarith
    have hA2 : 10 * (s : ℝ) * (z ^ 4 + 1) ≤ 10 * s * (2 * z ^ 4) :=
      mul_le_mul_of_nonneg_left hA1 (by positivity)
    have hA3 : 20 * (s : ℝ) * z ^ 4 ≤ z * z ^ 4 := mul_le_mul_of_nonneg_right h20 (by positivity)
    have hA : 10 * (s : ℝ) * (z ^ 4 + 1) ≤ z ^ 5 := by nlinarith
    have e : z ^ 5 / (5 * s) - z ^ 5 / (10 * s) = z ^ 5 / (10 * s) := by
      field_simp; ring
    have hB : z ^ 4 + 1 ≤ z ^ 5 / (10 * s) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  linarith

end DeepFourthMoment
