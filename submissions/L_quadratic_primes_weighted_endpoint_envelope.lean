import Mathlib

/-!
# 近、遠端點的加權包絡

把 `rows` 拆成 `near` 與 `rows \ near`。
- 近端：每項至多 `D (log x)^2`，項數至多 `C x^γ`。
- 遠端：每項至多 `D x^(α/2-β) (log x)^2`，項數至多 `|rows| ≤ C x^α`，
  而 `x^α · x^(α/2-β) = x^(3α/2-β)`。
-/

theorem PEqualNP.Outside.L_quadratic_primes_weighted_endpoint_envelope :
  ∀ (ι : Type) [DecidableEq ι] (rows near : Finset ι) (f : ι → ℝ) (x C D α β γ : ℝ), 1 ≤ x → 0 ≤ C → 0 ≤ D → near ⊆ rows → (rows.card : ℝ) ≤ C * x ^ α → (near.card : ℝ) ≤ C * x ^ γ → (∀ i ∈ near, f i ≤ D * (Real.log x)^2) → (∀ i ∈ rows \ near, f i ≤ D * x ^ (α / 2 - β) * (Real.log x)^2) → (∑ i ∈ rows, f i) ≤ C * D * (x ^ γ + x ^ (3 * α / 2 - β)) * (Real.log x)^2 := by
  intro ι _ rows near f x C D α β γ hx hC hD hsub hrows hnear hfn hff
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hL : 0 ≤ (Real.log x) ^ 2 := sq_nonneg _
  have hDL : 0 ≤ D * (Real.log x) ^ 2 := mul_nonneg hD hL
  have hfar0 : 0 ≤ D * x ^ (α / 2 - β) * (Real.log x) ^ 2 :=
    mul_nonneg (mul_nonneg hD (Real.rpow_nonneg hx0.le _)) hL
  rw [← Finset.sum_sdiff hsub]
  have h1 : ∑ i ∈ rows \ near, f i ≤ C * D * x ^ (3 * α / 2 - β) * (Real.log x) ^ 2 := by
    calc ∑ i ∈ rows \ near, f i
        ≤ ∑ _i ∈ rows \ near, D * x ^ (α / 2 - β) * (Real.log x) ^ 2 :=
          Finset.sum_le_sum hff
      _ = ((rows \ near).card : ℝ) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (rows.card : ℝ) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) := by
          gcongr
          exact Finset.sdiff_subset
      _ ≤ (C * x ^ α) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) :=
          mul_le_mul_of_nonneg_right hrows hfar0
      _ = C * D * (x ^ α * x ^ (α / 2 - β)) * (Real.log x) ^ 2 := by ring
      _ = C * D * x ^ (3 * α / 2 - β) * (Real.log x) ^ 2 := by
          rw [← Real.rpow_add hx0]; congr 3; ring
  have h2 : ∑ i ∈ near, f i ≤ C * D * x ^ γ * (Real.log x) ^ 2 := by
    calc ∑ i ∈ near, f i ≤ ∑ _i ∈ near, D * (Real.log x) ^ 2 := Finset.sum_le_sum hfn
      _ = (near.card : ℝ) * (D * (Real.log x) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C * x ^ γ) * (D * (Real.log x) ^ 2) := mul_le_mul_of_nonneg_right hnear hDL
      _ = C * D * x ^ γ * (Real.log x) ^ 2 := by ring
  calc ∑ i ∈ rows \ near, f i + ∑ i ∈ near, f i
      ≤ C * D * x ^ (3 * α / 2 - β) * (Real.log x) ^ 2 + C * D * x ^ γ * (Real.log x) ^ 2 :=
        add_le_add h1 h2
    _ = C * D * (x ^ γ + x ^ (3 * α / 2 - β)) * (Real.log x) ^ 2 := by ring
