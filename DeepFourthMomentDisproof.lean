import Mathlib

/-!
# `L-goldbach-frontier-deep-fourth-moment-conjecture` 不成立（單檔版）

平台命題聲稱：對每個 η > 0，充分大的 n 都有
`∫_{(wideArcs n)ᶜ ∩ [0,1]} |S_n(w,t)|⁴ dt ≤ n^(2+η)`。

本檔證明其否定。取 η = 1/12、n = 2^(12s)（s ≥ 20），以及所有素數 p ∈ (2^(4s), 2^(5s)]、1 ≤ a < p。
以 a/p 為中心、半徑 1/(16n) 的小弧都落在深次弧內，且互不相交。
由 Ramanujan 和與 Chebyshev 下界，每個分母 p 的弧上積分總和約為 n/(16n)·n。
再用單弧 Jensen 與冪平均不等式，得到
`∫_deep |S|⁴ ≥ K·n³/(2048·Y³) > n^(2+1/12)`。
真實量級約為 n^(7/3)，來自分母略大於 n^(1/3) 的有理點附近、高度約 n/q 的尖峰。
-/

section Proof

open Real Complex MeasureTheory Finset

noncomputable section

-- ===== Basic =====

/-!
# 反證 `L-goldbach-frontier-deep-fourth-moment-conjecture`：基本定義與指數和

本檔定義與平台命題逐字相同的物件（`E`、`S`、`wideArcs` 等），並證明
素數模的 Ramanujan 和公式。
-/



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

-- ===== Arcs =====

/-!
# 弧上積分：`J` 的展開、`ρ` 的界、單一素數分母的總和下界
-/



namespace DeepFourthMoment

/-- `ρ_k(d) = ∫_{-d}^{d} e(ku) du`。 -/
def rho (d : ℝ) (k : ℕ) : ℂ := ∫ u in (-d)..d, E ((k : ℝ) * u)

lemma continuous_E_mul (k : ℝ) : Continuous fun u : ℝ => E (k * u) :=
  continuous_E.comp (continuous_const.mul continuous_id)

lemma integral_E_shift (k : ℕ) (x d : ℝ) :
    ∫ t in (x - d)..(x + d), E ((k : ℝ) * t) = E ((k : ℝ) * x) * rho d k := by
  have h := intervalIntegral.integral_comp_add_right (fun t => E ((k : ℝ) * t)) (a := -d)
    (b := d) x
  rw [show x - d = -d + x by ring, show x + d = d + x by ring, ← h]
  unfold rho
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  ext u
  rw [show (k : ℝ) * (u + x) = (k : ℝ) * x + (k : ℝ) * u by ring, E_add]

lemma J_eq (n : ℕ) (x d : ℝ) :
    ∫ t in (x - d)..(x + d), S n t =
      ∑ k ∈ Finset.range (n + 1), (wP k : ℂ) * (E ((k : ℝ) * x) * rho d k) := by
  unfold S
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_E_shift]
  · intro k _
    exact (continuous_const.mul (continuous_E_mul _)).intervalIntegrable _ _

lemma norm_rho_le {d : ℝ} (hd : 0 ≤ d) (k : ℕ) : ‖rho d k‖ ≤ 2 * d := by
  unfold rho
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -d) (b := d) (C := 1)
    (f := fun u => E ((k : ℝ) * u)) (fun u _ => (norm_E _).le)
  have habs : |d - -d| = 2 * d := by
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [habs, one_mul] at this
  exact this

lemma re_rho_ge {n k : ℕ} (hk : k ≤ n) (hn : 0 < n) :
    (9 / 5 : ℝ) * (1 / (16 * (n : ℝ))) ≤ (rho (1 / (16 * (n : ℝ))) k).re := by
  set d : ℝ := 1 / (16 * (n : ℝ)) with hd_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < d := by rw [hd_def]; positivity
  have hnd : (n : ℝ) * d = 1 / 16 := by rw [hd_def]; field_simp
  unfold rho
  have hint : IntervalIntegrable (fun u : ℝ => E ((k : ℝ) * u)) volume (-d) d :=
    (continuous_E_mul _).intervalIntegrable _ _
  have hre := intervalIntegral.intervalIntegral_re hint
  have hre' : (∫ u in (-d)..d, E ((k : ℝ) * u)).re =
      ∫ u in (-d)..d, Real.cos (2 * Real.pi * ((k : ℝ) * u)) := by
    rw [← RCLike.re_to_complex, ← hre]
    congr 1
    ext u
    rw [RCLike.re_to_complex, E_re]
  rw [hre']
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hcos : ∀ u ∈ Set.Icc (-d) d, (9 / 10 : ℝ) ≤ Real.cos (2 * Real.pi * ((k : ℝ) * u)) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hu2' : u ^ 2 ≤ d ^ 2 := sq_le_sq' hu1 hu2
    have hk2 : (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hk0 hkR 2
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have hx2 : (2 * Real.pi * ((k : ℝ) * u)) ^ 2 ≤ Real.pi ^ 2 / 64 := by
      have e1 : (2 * Real.pi * ((k : ℝ) * u)) ^ 2 = 4 * Real.pi ^ 2 * ((k : ℝ) ^ 2 * u ^ 2) := by
        ring
      have e2 : (k : ℝ) ^ 2 * u ^ 2 ≤ (n : ℝ) ^ 2 * d ^ 2 :=
        mul_le_mul hk2 hu2' (sq_nonneg _) (sq_nonneg _)
      have e3 : (n : ℝ) ^ 2 * d ^ 2 = 1 / 256 := by
        rw [show (n : ℝ) ^ 2 * d ^ 2 = ((n : ℝ) * d) ^ 2 by ring, hnd]
        norm_num
      rw [e1]
      calc 4 * Real.pi ^ 2 * ((k : ℝ) ^ 2 * u ^ 2) ≤ 4 * Real.pi ^ 2 * (1 / 256) := by
            rw [← e3]; gcongr
        _ = Real.pi ^ 2 / 64 := by ring
    have hcosb := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * ((k : ℝ) * u))
    nlinarith
  have hcint : IntervalIntegrable (fun u : ℝ => Real.cos (2 * Real.pi * ((k : ℝ) * u)))
      volume (-d) d := by
    apply Continuous.intervalIntegrable; fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := -d) (b := d)
    (by linarith) (intervalIntegrable_const (c := (9 / 10 : ℝ))) hcint hcos
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have : (d - -d) * (9 / 10 : ℝ) = (9 / 5) * d := by ring
  linarith

/-- 對單一素數分母 `p`，所有 `a/p` 弧上積分之和的實部下界。 -/
lemma sum_J_prime {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) (hn : 0 < n) :
    (1 / (16 * (n : ℝ))) * ((9 / 5) * (∑ k ∈ Finset.range (n + 1), wP k)
        - 2 * (p : ℝ) * Real.log p) ≤
      (-(∑ a ∈ Finset.Ico 1 p,
        ∫ t in ((a : ℝ) / p - 1 / (16 * (n : ℝ)))..((a : ℝ) / p + 1 / (16 * (n : ℝ))),
          S n t)).re := by
  set d : ℝ := 1 / (16 * (n : ℝ)) with hd_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < d := by rw [hd_def]; positivity
  -- 展開成對 k 的和
  set g : ℕ → ℝ := fun k => if p ∣ k then -((p : ℝ) - 1) else 1 with hg
  have hexp : -(∑ a ∈ Finset.Ico 1 p,
      ∫ t in ((a : ℝ) / p - d)..((a : ℝ) / p + d), S n t) =
      ∑ k ∈ Finset.range (n + 1), (((wP k * g k : ℝ)) : ℂ) * rho d k := by
    simp_rw [J_eq]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ∑ a ∈ Finset.Ico 1 p, (wP k : ℂ) * (E ((k : ℝ) * ((a : ℝ) / p)) * rho d k) =
        (wP k : ℂ) * rho d k * ∑ a ∈ Finset.Ico 1 p, E ((k : ℝ) * ((a : ℝ) / p)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [this, sum_E_prime hp k]
    simp only [hg]
    split_ifs <;> push_cast <;> ring
  rw [hexp, Complex.re_sum]
  simp_rw [Complex.re_ofReal_mul]
  -- 逐項下界
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (9 / 5) * d * wP k - (if k = p then 2 * (p : ℝ) * Real.log p * d else 0) ≤
        wP k * g k * (rho d k).re := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hre := re_rho_ge hkn hn
    rw [← hd_def] at hre
    have hnorm := norm_rho_le hd.le k
    have hre_le : (rho d k).re ≤ 2 * d := (Complex.re_le_norm _).trans hnorm
    by_cases hkp : k = p
    · subst hkp
      have hw : wP k = Real.log k := by simp [wP, hp]
      have hgk : g k = -((k : ℝ) - 1) := by simp [hg]
      rw [hw, hgk, if_pos rfl]
      have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hp.one_lt.le
      nlinarith [mul_nonneg hlog (sub_nonneg.mpr hk1), mul_nonneg hlog hd.le]
    · rw [if_neg hkp, sub_zero]
      by_cases hkprime : k.Prime
      · have hndvd : ¬ p ∣ k := by
          intro hdvd
          exact hkp ((Nat.prime_dvd_prime_iff_eq hp hkprime).mp hdvd).symm
        have hgk : g k = 1 := by simp [hg, hndvd]
        rw [hgk, mul_one]
        have hw0 := wP_nonneg k
        nlinarith
      · have hw : wP k = 0 := by simp [wP, hkprime]
        rw [hw]
        simp
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hpmem : p ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hpn)
  rw [Finset.sum_ite_eq' (Finset.range (n + 1)) p, if_pos hpmem] at hsum
  linarith

end DeepFourthMoment

-- ===== Measure =====

/-!
# 測度論部分：`wideArcs` 可測、深次弧積分不小於小弧積分之和、單弧 Jensen 不等式
-/



namespace DeepFourthMoment

lemma measurableSet_wideArcs (n : ℕ) : MeasurableSet (wideArcs n) := by
  have : wideArcs n = ⋃ q : ℕ, ⋃ a : ℕ,
      {t : ℝ | (1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q) ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
    ext t
    simp only [wideArcs, Set.mem_setOf_eq, Set.mem_iUnion, and_assoc]
  rw [this]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  exact (MeasurableSet.const _).inter
    (measurableSet_le (f := fun t : ℝ => |t - (a : ℝ) / (q : ℝ)|) (by fun_prop) measurable_const)

/-- 單弧 Jensen：`(∫_a^b f)^4 ≤ (b-a)^3 ∫_a^b f^4`。 -/
lemma integral_pow_four_ge {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) {a b : ℝ}
    (hab : a < b) :
    (∫ x in a..b, f x) ^ 4 ≤ (b - a) ^ 3 * ∫ x in a..b, f x ^ 4 := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ 4) := convexOn_pow 4
  have hJ := hconv.map_set_average_le (μ := volume) (t := Set.Ioc a b) (f := f)
    (continuous_pow 4).continuousOn isClosed_Ici
    (by simp [Real.volume_Ioc, hab]) (by simp [Real.volume_Ioc])
    (Filter.Eventually.of_forall fun x => hf0 x) hf.integrableOn_Ioc
    ((continuous_pow 4).comp hf).integrableOn_Ioc
  rw [setAverage_eq, setAverage_eq] at hJ
  simp only [Real.volume_real_Ioc_of_le hab.le, smul_eq_mul] at hJ
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le]
  set X := ∫ x in Set.Ioc a b, f x
  set Y := ∫ x in Set.Ioc a b, f x ^ 4
  have hJ' : (b - a)⁻¹ ^ 4 * X ^ 4 ≤ (b - a)⁻¹ * Y := by
    rw [← mul_pow]; exact hJ
  have hpos : 0 < (b - a) ^ 4 := by positivity
  calc X ^ 4 = (b - a) ^ 4 * ((b - a)⁻¹ ^ 4 * X ^ 4) := by
        field_simp
    _ ≤ (b - a) ^ 4 * ((b - a)⁻¹ * Y) := by gcongr
    _ = (b - a) ^ 3 * Y := by field_simp

/-- 單弧下界：`‖∫ S‖^4 ≤ (2d)^3 ∫ ‖S‖^4`。 -/
lemma norm_J_pow_four_le (n : ℕ) (c : ℝ) {d : ℝ} (hd : 0 < d) :
    ‖∫ t in (c - d)..(c + d), S n t‖ ^ 4 ≤
      (2 * d) ^ 3 * ∫ t in (c - d)..(c + d), ‖S n t‖ ^ 4 := by
  have hab : c - d < c + d := by linarith
  have h1 : ‖∫ t in (c - d)..(c + d), S n t‖ ≤ ∫ t in (c - d)..(c + d), ‖S n t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab.le
  have h2 := integral_pow_four_ge (f := fun t => ‖S n t‖) (continuous_S n).norm
    (fun _ => norm_nonneg _) hab
  have hlen : c + d - (c - d) = 2 * d := by ring
  rw [hlen] at h2
  calc ‖∫ t in (c - d)..(c + d), S n t‖ ^ 4 ≤ (∫ t in (c - d)..(c + d), ‖S n t‖) ^ 4 := by
        gcongr
    _ ≤ _ := h2

/-- 深次弧四階矩不小於互不相交、落在深次弧內的小弧上的積分之和。 -/
lemma sum_arcs_le_I4 {ι : Type*} (n : ℕ) (X : Finset ι) (c : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsub : ∀ i ∈ X, Set.Icc (c i - d) (c i + d) ⊆ Set.Ioc 0 1)
    (hout : ∀ i ∈ X, ∀ t ∈ Set.Icc (c i - d) (c i + d), t ∉ wideArcs n)
    (hdisj : Set.Pairwise (X : Set ι) (Function.onFun Disjoint fun i => Set.Icc (c i - d) (c i + d))) :
    ∑ i ∈ X, ∫ t in (c i - d)..(c i + d), ‖S n t‖ ^ 4 ≤ I4 n := by
  set f : ℝ → ℝ := fun u => ‖S n u‖ ^ 4 with hf
  have hfc : Continuous f := (continuous_S n).norm.pow 4
  have hf0 : ∀ u, 0 ≤ f u := fun u => by positivity
  have hW := (measurableSet_wideArcs n).compl
  unfold I4
  rw [intervalIntegral.integral_of_le zero_le_one]
  set A := ⋃ i ∈ X, Set.Icc (c i - d) (c i + d) with hA_def
  have hA : MeasurableSet A := Finset.measurableSet_biUnion X fun i _ => measurableSet_Icc
  have hAsub : A ⊆ Set.Ioc 0 1 := Set.iUnion₂_subset fun i hi => hsub i hi
  have hgint : IntegrableOn ((wideArcs n)ᶜ.indicator f) (Set.Ioc 0 1) :=
    (hfc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator hW
  have h1 : ∫ t in A, (wideArcs n)ᶜ.indicator f t ≤
      ∫ t in Set.Ioc 0 1, (wideArcs n)ᶜ.indicator f t :=
    setIntegral_mono_set hgint
      (Filter.Eventually.of_forall fun t => Set.indicator_nonneg (fun u _ => hf0 u) t)
      (Filter.Eventually.of_forall hAsub)
  have h2 : ∫ t in A, (wideArcs n)ᶜ.indicator f t = ∫ t in A, f t := by
    apply setIntegral_congr_fun hA
    intro t ht
    simp only [hA_def, Set.mem_iUnion] at ht
    obtain ⟨i, hi, hti⟩ := ht
    exact Set.indicator_of_mem (hout i hi t hti) f
  have h3 : ∫ t in A, f t = ∑ i ∈ X, ∫ t in Set.Icc (c i - d) (c i + d), f t :=
    integral_biUnion_finset X (fun i _ => measurableSet_Icc) hdisj
      (fun i _ => hfc.integrableOn_Icc)
  have h4 : ∀ i ∈ X, ∫ t in Set.Icc (c i - d) (c i + d), f t =
      ∫ t in (c i - d)..(c i + d), f t := by
    intro i _
    rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  rw [← Finset.sum_congr rfl h4, ← h3, ← h2]
  exact h1

end DeepFourthMoment

-- ===== Params =====

/-!
# 參數：`n = 2^(12s)`、分母 `p ∈ (2^(4s), 2^(5s)]`（素數）、半徑 `d = 1/(16n)`
-/



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

-- ===== Main =====

/-!
# 主定理：深次弧四階矩猜想不成立

取 `n = 2^(12s)`，以及所有素數 `p ∈ (2^(4s), 2^(5s)]`、`1 ≤ a < p`。
半徑 `d = 1/(16n)` 的小弧 `[a/p - d, a/p + d]` 落在深次弧內且互不相交。
單弧 Jensen 不等式、冪平均不等式、Ramanujan 和與 Chebyshev 下界合起來給出

  `I4 n ≥ K·n³/(2048·Y³) ≥ 2^(26s)/(20480 s) > 2^(25s) = n^(2+1/12)`。

因此對 `η = 1/12`，命題 `∀ η>0, ∃N, ∀ n≥N, I4 n ≤ n^(2+η)` 不成立。
-/



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

-- ===== Final =====
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

end -- noncomputable section

end Proof

/-- 平台命題 `L-goldbach-frontier-deep-fourth-moment-conjecture` 的逐字否定。 -/
theorem L_goldbach_frontier_deep_fourth_moment_conjecture_is_false :
    ¬ (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => ‖S n w u‖ ^ 4) t) (0 : ℝ) 1 MeasureTheory.volume ≤ (n : ℝ) ^ (2 + η)) := by
  intro h
  exact DeepFourthMoment.not_deep_fourth_moment h

#print axioms L_goldbach_frontier_deep_fourth_moment_conjecture_is_false
