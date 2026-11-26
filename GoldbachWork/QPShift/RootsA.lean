import Mathlib

/-!
# `r² ≡ -a (mod p^k)` 的根數上界：至多 `4a` 個

設 `p` 為素數、`a ≥ 1`。

- 若 `p^k ≤ 4a`，根數不超過 `p^k`，直接成立。
- 否則固定一個根 `r₀`，令 `j = min(v_p(2r₀), k)`、`g = p^j`、`q = p^(k-j)`。
  - 任一根 `s` 都滿足 `q ∣ |r₀ - s|` 或 `q ∣ r₀ + s`，因為 `p^k ∣ (r₀-s)(r₀+s)`，而兩因子的公共 `p` 冪整除 `2r₀`。
  - `g² ≤ 4a`：若 `2j ≤ k`，則 `g² ∣ 4(r₀²+a) - (2r₀)² = 4a`；若 `2j > k`，則 `p^k ∣ 4a`，與 `p^k > 4a` 矛盾。
  - 所以根落在模 `q` 的兩個剩餘類中，每類至多 `g` 個，合計至多 `2g ≤ 4a` 個。
-/

namespace QPShift

def rootsA (a m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun n => m ∣ n ^ 2 + a)

/-- 一個剩餘類在 `[0, q·g)` 中至多 `g` 個元素。 -/
lemma card_residue_le (q g c : ℕ) (hq : 0 < q) :
    ((Finset.range (q * g)).filter (fun s => s % q = c)).card ≤ g := by
  calc ((Finset.range (q * g)).filter (fun s => s % q = c)).card
      ≤ (Finset.range g).card := by
        apply Finset.card_le_card_of_injOn (fun s => s / q)
        · intro s hs
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hs
          rw [Finset.mem_coe, Finset.mem_range]
          exact (Nat.div_lt_iff_lt_mul hq).mpr (by rw [mul_comm]; exact hs.1)
        · intro s hs t ht hst
          rw [Finset.mem_coe, Finset.mem_filter] at hs ht
          have h1 := Nat.div_add_mod s q
          have h2 := Nat.div_add_mod t q
          simp only at hst
          rw [hst, hs.2] at h1
          rw [ht.2] at h2
          omega
    _ = g := Finset.card_range g

/-- 兩因子的公共 `p` 冪：若 `p^m ∣ D` 且 `p^m ∣ B`，則 `p^m ∣ 2r₀`。 -/
lemma common_dvd_two_mul {r s D B P : ℕ} (hD : D = max r s - min r s) (hB : B = r + s)
    (h1 : P ∣ D) (h2 : P ∣ B) : P ∣ 2 * r := by
  rcases le_total s r with h | h
  · have hD' : D = r - s := by rw [hD, max_eq_left h, min_eq_right h]
    have : D + B = 2 * r := by omega
    rw [← this]; exact dvd_add h1 h2
  · have hD' : D = s - r := by rw [hD, max_eq_right h, min_eq_left h]
    have : B - D = 2 * r := by omega
    rw [← this]; exact Nat.dvd_sub h2 h1

theorem rootsA_prime_power_le {a p k : ℕ} (ha : 1 ≤ a) (hp : p.Prime) (hk : 0 < k) :
    (rootsA a (p ^ k)).card ≤ 4 * a := by
  classical
  have hpk0 : 0 < p ^ k := pow_pos hp.pos k
  by_cases hsmall : p ^ k ≤ 4 * a
  · calc (rootsA a (p ^ k)).card ≤ (Finset.range (p ^ k)).card := Finset.card_filter_le _ _
      _ = p ^ k := Finset.card_range _
      _ ≤ 4 * a := hsmall
  push_neg at hsmall
  rcases (rootsA a (p ^ k)).eq_empty_or_nonempty with hE | ⟨r0, hr0⟩
  · simp [hE]
  have hr0' := Finset.mem_filter.mp hr0
  have hr0lt : r0 < p ^ k := Finset.mem_range.mp hr0'.1
  have hr0d : p ^ k ∣ r0 ^ 2 + a := hr0'.2
  have := Fact.mk hp
  -- r0 > 0：否則 p^k ∣ a
  have hr0pos : 0 < r0 := by
    rcases Nat.eq_zero_or_pos r0 with h | h
    · subst h
      have : p ^ k ∣ a := by simpa using hr0d
      have := Nat.le_of_dvd (by omega) this
      omega
    · exact h
  set j := min (multiplicity p (2 * r0)) k with hj
  set g := p ^ j with hg
  set q := p ^ (k - j) with hq
  have hjk : j ≤ k := min_le_right _ _
  have hqg : q * g = p ^ k := by rw [hq, hg, ← pow_add]; congr 1; omega
  have hq0 : 0 < q := pow_pos hp.pos _
  have hg2r : g ∣ 2 * r0 := by
    rw [hg]
    exact (pow_dvd_pow p (min_le_left _ _)).trans (pow_multiplicity_dvd _ _)
  -- g² ≤ 4a
  have hg4a : g ^ 2 ≤ 4 * a := by
    by_cases h2j : 2 * j ≤ k
    · have hgsq : g ^ 2 ∣ p ^ k := by
        rw [hg, ← pow_mul]; exact pow_dvd_pow p (by omega)
      have h4 : g ^ 2 ∣ 4 * (r0 ^ 2 + a) := (hgsq.trans hr0d).mul_left 4
      have h4r : g ^ 2 ∣ (2 * r0) ^ 2 := pow_dvd_pow_of_dvd hg2r 2
      have h4a : g ^ 2 ∣ 4 * a := by
        have := Nat.dvd_sub h4 h4r
        rwa [show 4 * (r0 ^ 2 + a) - (2 * r0) ^ 2 = 4 * a by ring_nf; omega] at this
      exact Nat.le_of_dvd (by omega) h4a
    · exfalso
      have hpkg : p ^ k ∣ g ^ 2 := by
        rw [hg, ← pow_mul]; exact pow_dvd_pow p (by omega)
      have h4r : p ^ k ∣ (2 * r0) ^ 2 := hpkg.trans (pow_dvd_pow_of_dvd hg2r 2)
      have h4 : p ^ k ∣ 4 * (r0 ^ 2 + a) := hr0d.mul_left 4
      have h4a : p ^ k ∣ 4 * a := by
        have := Nat.dvd_sub h4 h4r
        rwa [show 4 * (r0 ^ 2 + a) - (2 * r0) ^ 2 = 4 * a by ring_nf; omega] at this
      have := Nat.le_of_dvd (by omega) h4a
      omega
  have hg2a : g ≤ 2 * a := by nlinarith
  -- 每個根落在兩個剩餘類之一
  have hclass : ∀ s ∈ rootsA a (p ^ k),
      s % q = r0 % q ∨ s % q = (q - r0 % q) % q := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    have hsd : p ^ k ∣ s ^ 2 + a := hs'.2
    set D := max r0 s - min r0 s with hD
    set B := r0 + s with hB
    have hBpos : 0 < B := by omega
    have hprod : p ^ k ∣ D * B := by
      rcases le_total s r0 with h | h
      · have hD' : D = r0 - s := by rw [hD, max_eq_left h, min_eq_right h]
        have e : D * B = (r0 ^ 2 + a) - (s ^ 2 + a) := by
          rw [hD', hB]
          have : s ^ 2 ≤ r0 ^ 2 := Nat.pow_le_pow_left h 2
          zify [h, this, (show s ^ 2 + a ≤ r0 ^ 2 + a by omega)]; ring
        rw [e]; exact Nat.dvd_sub hr0d hsd
      · have hD' : D = s - r0 := by rw [hD, max_eq_right h, min_eq_left h]
        have e : D * B = (s ^ 2 + a) - (r0 ^ 2 + a) := by
          rw [hD', hB]
          have : r0 ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left h 2
          zify [h, this, (show r0 ^ 2 + a ≤ s ^ 2 + a by omega)]; ring
        rw [e]; exact Nat.dvd_sub hsd hr0d
    -- q ∣ D 或 q ∣ B
    have hqDB : q ∣ D ∨ q ∣ B := by
      by_cases hD0 : D = 0
      · left; rw [hD0]; exact dvd_zero q
      by_cases hqD : q ∣ D
      · exact Or.inl hqD
      right
      have hvD : multiplicity p D < k - j := by
        by_contra hc
        push_neg at hc
        exact hqD ((pow_dvd_pow p hc).trans (pow_multiplicity_dvd _ _))
      have hvsum : k ≤ multiplicity p D + multiplicity p B := by
        rw [← Nat.multiplicity_mul hD0 hBpos.ne']
        exact (Nat.pow_dvd_iff_le_multiplicity hp.ne_one (by positivity)).mp hprod
      -- 公共冪
      have hmin : min (multiplicity p D) (multiplicity p B) ≤ multiplicity p (2 * r0) := by
        apply (Nat.pow_dvd_iff_le_multiplicity hp.ne_one (by omega)).mp
        apply common_dvd_two_mul hD hB
        · exact (pow_dvd_pow p (min_le_left _ _)).trans (pow_multiplicity_dvd _ _)
        · exact (pow_dvd_pow p (min_le_right _ _)).trans (pow_multiplicity_dvd _ _)
      have hvB : k - j ≤ multiplicity p B := by
        by_cases hjeq : j = k
        · omega
        have hj' : j = multiplicity p (2 * r0) := by
          rw [hj]; exact min_eq_left (by omega)
        rcases le_total (multiplicity p D) (multiplicity p B) with h | h
        · rw [min_eq_left h] at hmin
          omega
        · rw [min_eq_right h] at hmin
          omega
      exact (pow_dvd_pow p hvB).trans (pow_multiplicity_dvd _ _)
    rcases hqDB with h | h
    · left
      rcases le_total s r0 with hsr | hsr
      · have hD' : D = r0 - s := by rw [hD, max_eq_left hsr, min_eq_right hsr]
        rw [hD'] at h
        exact ((Nat.modEq_iff_dvd' hsr).mpr h)
      · have hD' : D = s - r0 := by rw [hD, max_eq_right hsr, min_eq_left hsr]
        rw [hD'] at h
        exact ((Nat.modEq_iff_dvd' hsr).mpr h).symm
    · right
      have h1 : (r0 % q + s % q) % q = 0 := by
        rw [← Nat.add_mod]; exact Nat.mod_eq_zero_of_dvd h
      obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h1
      have hr := Nat.mod_lt r0 hq0
      have hs := Nat.mod_lt s hq0
      have hc2 : c < 2 := by
        by_contra hc2
        push_neg at hc2
        have : q * 2 ≤ q * c := Nat.mul_le_mul_left q hc2
        omega
      interval_cases c
      · have hr0' : r0 % q = 0 := by omega
        have hs0 : s % q = 0 := by omega
        rw [hr0', hs0, Nat.sub_zero, Nat.mod_self]
      · rw [Nat.mod_eq_of_lt (by omega : q - r0 % q < q)]
        omega
  -- 計數
  have hsub : rootsA a (p ^ k) ⊆
      ((Finset.range (q * g)).filter (fun s => s % q = r0 % q)) ∪
        ((Finset.range (q * g)).filter (fun s => s % q = (q - r0 % q) % q)) := by
    intro s hs
    have hslt : s < p ^ k := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_range, hqg]
    rcases hclass s hs with h | h
    · exact Or.inl ⟨hslt, h⟩
    · exact Or.inr ⟨hslt, h⟩
  calc (rootsA a (p ^ k)).card
      ≤ (((Finset.range (q * g)).filter (fun s => s % q = r0 % q)) ∪
        ((Finset.range (q * g)).filter (fun s => s % q = (q - r0 % q) % q))).card :=
        Finset.card_le_card hsub
    _ ≤ g + g := (Finset.card_union_le _ _).trans
        (add_le_add (card_residue_le q g _ hq0) (card_residue_le q g _ hq0))
    _ ≤ 4 * a := by omega

end QPShift
