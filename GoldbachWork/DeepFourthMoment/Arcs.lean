import GoldbachWork.DeepFourthMoment.Basic

/-!
# 弧上積分：`J` 的展開、`ρ` 的界、單一素數分母的總和下界
-/

open Real Complex MeasureTheory Finset

noncomputable section

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
