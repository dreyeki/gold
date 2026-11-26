import Mathlib

/-!
# 由正的「平移 2」能量抽出孪生素數

對 `ZMod M` 上的實值函數 `g`，令 `F = dft g`。用 `‖F k‖² = F k · conj (F k)` 展開，
再用加法特徵的正交性 `∑ₖ ψ(k b) = M·[b = 0]`，得到

  `∑ₖ Re ψ(2k) · ‖F k‖² = M · ∑ⱼ g(j+2) g(j)`。

右邊為正時，必有某個 `j` 使 `g(j)` 與 `g(j+2)` 都不為零。
平台的 `f` 只在窗口 `(X, 1.02X)` 內的素數上非零，而 `M = 2X+5`，
所以 `j.val + 2` 不會繞回，`j.val` 與 `j.val + 2` 都是大於 `X` 的素數。
-/

open ZMod Finset ComplexConjugate

namespace TwinEnergyBridge

theorem energy_eq (M : ℕ) [NeZero M] (g : ZMod M → ℝ) :
    ∑ k : ZMod M, (stdAddChar (N := M) (2 * k)).re *
        ‖dft (fun j : ZMod M => ((g j : ℝ) : ℂ)) k‖ ^ 2
      = M * ∑ j : ZMod M, g (j + 2) * g j := by
  classical
  set Φ : ZMod M → ℂ := fun j => ((g j : ℝ) : ℂ) with hΦ
  have hconj : ∀ a : ZMod M, conj (stdAddChar (N := M) (-a)) = stdAddChar (N := M) a := by
    intro a
    have := AddChar.map_neg_eq_conj (stdAddChar (N := M)) (-a)
    rw [neg_neg] at this
    exact this.symm
  have hnorm : ∀ k, ((‖dft Φ k‖ ^ 2 : ℝ) : ℂ) = dft Φ k * conj (dft Φ k) := by
    intro k
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have horth : ∀ b : ZMod M, ∑ k : ZMod M, stdAddChar (N := M) (k * b) = if b = 0 then (M : ℂ) else 0 := by
    intro b
    rw [AddChar.sum_mulShift b (isPrimitive_stdAddChar M), ZMod.card]
    split_ifs <;> simp
  have key : ∑ k : ZMod M, stdAddChar (N := M) (2 * k) * ((‖dft Φ k‖ ^ 2 : ℝ) : ℂ)
      = (M : ℂ) * ∑ j : ZMod M, Φ (j + 2) * Φ j := by
    have hexp : ∀ k, stdAddChar (N := M) (2 * k) * ((‖dft Φ k‖ ^ 2 : ℝ) : ℂ)
        = ∑ j : ZMod M, ∑ j' : ZMod M, Φ j * Φ j' * stdAddChar (N := M) (k * (2 - j + j')) := by
      intro k
      rw [hnorm, dft_apply]
      simp only [smul_eq_mul]
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      have hΦr : conj (Φ j') = Φ j' := by simp [hΦ]
      rw [map_mul (starRingEnd ℂ) (stdAddChar (N := M) (-(j' * k))) (Φ j'), hconj, hΦr]
      have : stdAddChar (N := M) (k * (2 - j + j')) = stdAddChar (N := M) (2 * k) * stdAddChar (N := M) (-(j * k)) * stdAddChar (N := M) (j' * k) := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 1; ring
      rw [this]; ring
    have hinner : ∀ j j' : ZMod M,
        ∑ k : ZMod M, Φ j * Φ j' * stdAddChar (N := M) (k * (2 - j + j'))
          = if j = j' + 2 then (M : ℂ) * Φ j * Φ j' else 0 := by
      intro j j'
      rw [← Finset.mul_sum, horth]
      by_cases h : j = j' + 2
      · have : (2 : ZMod M) - j + j' = 0 := by rw [h]; ring
        rw [if_pos this, if_pos h]; ring
      · have : (2 : ZMod M) - j + j' ≠ 0 := by
          intro h0; apply h; linear_combination -h0
        rw [if_neg this, if_neg h, mul_zero]
    calc ∑ k : ZMod M, stdAddChar (N := M) (2 * k) * ((‖dft Φ k‖ ^ 2 : ℝ) : ℂ)
        = ∑ k : ZMod M, ∑ j : ZMod M, ∑ j' : ZMod M, Φ j * Φ j' * stdAddChar (N := M) (k * (2 - j + j')) :=
          Finset.sum_congr rfl fun k _ => hexp k
      _ = ∑ j : ZMod M, ∑ j' : ZMod M, ∑ k : ZMod M, Φ j * Φ j' * stdAddChar (N := M) (k * (2 - j + j')) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ j : ZMod M, ∑ j' : ZMod M, (if j = j' + 2 then (M : ℂ) * Φ j * Φ j' else 0) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => hinner j j'
      _ = (M : ℂ) * ∑ j : ZMod M, Φ (j + 2) * Φ j := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [Finset.sum_ite_eq' Finset.univ (j' + 2) (fun j => (M : ℂ) * Φ j * Φ j'),
            if_pos (Finset.mem_univ _)]
          ring
  have hre := congrArg Complex.re key
  have lhs : (∑ k : ZMod M, stdAddChar (N := M) (2 * k) * ((‖dft Φ k‖ ^ 2 : ℝ) : ℂ)).re
      = ∑ k : ZMod M, (stdAddChar (N := M) (2 * k)).re * ‖dft Φ k‖ ^ 2 := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_mul_ofReal]
  have rhs : ((M : ℂ) * ∑ j : ZMod M, Φ (j + 2) * Φ j).re
      = M * ∑ j : ZMod M, g (j + 2) * g j := by
    have : (M : ℂ) * ∑ j : ZMod M, Φ (j + 2) * Φ j
        = ((M * ∑ j : ZMod M, g (j + 2) * g j : ℝ) : ℂ) := by
      push_cast [hΦ]; rfl
    rw [this, Complex.ofReal_re]
  rw [lhs, rhs] at hre
  exact hre

end TwinEnergyBridge

theorem PEqualNP.Outside.L_twin_primes_energy_bridge :
  (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let N := fun (X : ℕ) => 2*X+5; let f := fun (X n : ℕ) => if n ∈ w X ∧ n.Prime then Real.log n else 0; let energy := fun (X : ℕ) => letI : NeZero (N X) := ⟨Nat.succ_ne_zero _⟩; ∑ k : ZMod (N X), (ZMod.stdAddChar (N:=N X) (2*k)).re * ‖ZMod.dft (fun j : ZMod (N X) => ((f X j.val:ℝ):ℂ)) k‖^2; ∀ B : ℕ, ∃ X : ℕ, B<X ∧ 0<energy X) → (∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ (p+2).Prime) := by
  intro hE B
  obtain ⟨X, hBX, hpos⟩ := hE B
  dsimp only at hpos
  rw [TwinEnergyBridge.energy_eq] at hpos
  set g : ZMod (2 * X + 5) → ℝ := fun j =>
    if j.val ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X) ∧ j.val.Prime
    then Real.log j.val else 0 with hg
  have hM : (0 : ℝ) < ((2 * X + 5 : ℕ) : ℝ) := by positivity
  have hsum : 0 < ∑ j : ZMod (2 * X + 5), g (j + 2) * g j := by
    by_contra h
    push Not at h
    have := mul_nonpos_of_nonneg_of_nonpos hM.le h
    linarith
  obtain ⟨j, -, hj⟩ : ∃ j ∈ (Finset.univ : Finset (ZMod (2 * X + 5))), 0 < g (j + 2) * g j := by
    by_contra h
    push Not at h
    have := Finset.sum_nonpos h
    linarith
  have hgj : g j ≠ 0 := fun h0 => by rw [h0, mul_zero] at hj; exact lt_irrefl _ hj
  have hgj2 : g (j + 2) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hj; exact lt_irrefl _ hj
  have hcond : ∀ i : ZMod (2 * X + 5), g i ≠ 0 →
      (X < i.val ∧ 50 * i.val < 51 * X) ∧ i.val.Prime := by
    intro i hi
    by_contra hc
    apply hi
    simp only [hg, Finset.mem_filter, Finset.mem_range]
    rw [ite_eq_right_iff]
    tauto
  obtain ⟨⟨hX1, hX2⟩, hp⟩ := hcond j hgj
  obtain ⟨-, hp2⟩ := hcond (j + 2) hgj2
  have hlt : j.val + 2 < 2 * X + 5 := by omega
  have h2v : (2 : ZMod (2 * X + 5)).val = 2 := by
    have : ((2 : ℕ) : ZMod (2 * X + 5)).val = 2 := ZMod.val_natCast_of_lt (by omega)
    simpa using this
  have hval : (j + 2).val = j.val + 2 := by
    rw [ZMod.val_add_of_lt (by rw [h2v]; exact hlt), h2v]
  refine ⟨j.val, by omega, hp, ?_⟩
  rw [← hval]; exact hp2
