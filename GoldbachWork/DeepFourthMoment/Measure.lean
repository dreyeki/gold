import GoldbachWork.DeepFourthMoment.Arcs

/-!
# 測度論部分：`wideArcs` 可測、深次弧積分不小於小弧積分之和、單弧 Jensen 不等式
-/

open Real Complex MeasureTheory Finset

noncomputable section

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
