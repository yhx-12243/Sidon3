module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Normed.Module.Normalize
public import Sidon3.SquareCoeffBound

@[expose] public section

open scoped ComplexConjugate Rat
open Complex (I)

private lemma exists_unit_norm_add_eq (a b : ℂ) : ∃ z, ‖z‖ = 1 ∧ ‖z * a + b‖ = ‖a‖ + ‖b‖ := by
  by_cases h : b / a = 0
  · simp only [div_eq_zero_iff] at h
    rcases h with (rfl | rfl) <;> (use 1; simp)
  · have h₁ := NormedSpace.norm_normalize h
    refine ⟨NormedSpace.normalize (b / a), h₁, ?_⟩
    calc
      _ = ‖NormedSpace.normalize (b / a) * a‖ + ‖b‖ := by
        rw [norm_add_eq_iff_real]
        simp only [h₁, Complex.norm_mul, one_mul]
        simp only [NormedSpace.normalize, Complex.norm_div, inv_div]
        simp only [div_eq_zero_iff, not_or] at h
        rcases h with ⟨a₀, b₀⟩
        change ‖b‖ * ((‖a‖ / ‖b‖ : ℝ) * (b / a) * a) = ‖a‖ * b
        field_simp
        norm_cast
        exact mul_div_cancel₀ _ (by simpa)
      _ = _ := by simp [h₁]

set_option linter.style.whitespace false in
private lemma binary_cauchy {r₁ r₂ f₁ f₂ g₁ g₂ : ℝ} (hr₁ : r₁^2 = f₁ * g₁) (hr₂ : r₂^2 = f₂ * g₂)
    (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂) :
    (r₁ + r₂)^2 ≤ (f₁ + f₂) * (g₁ + g₂) := by
  let r c := bif c then r₁ else r₂
  let f c := bif c then f₁ else f₂
  let g c := bif c then g₁ else g₂
  convert Finset.univ.sum_sq_le_sum_mul_sum_of_sq_eq_mul (r := r) (f := f) (g := g) ?_ ?_ ?_
  · simp [r]
  · simp [f]
  · simp [g]
  · simp [f, hf₁, hf₂]
  · simp [g, hg₁, hg₂]
  · simp [r, f, g, hr₁, hr₂]

set_option linter.style.whitespace false in
theorem Sidon3 {a₀ a₁ a₂ a₃ : ℂ} (h : ∀ z, ‖z‖ ≤ 1 → ‖a₀ + a₁ * z + a₂ * z^2 + a₃ * z^3‖ ≤ 1) :
    ‖a₀‖ + ‖a₁‖ + ‖a₂‖ + ‖a₃‖ ≤ 5 / 3 := by
  wlog a₁₂ : ‖a₂‖ • a₁ = ‖a₁‖ • a₂ with hg
  · have a₁₀ : a₁ ≠ 0 := by contrapose a₁₂; simp [a₁₂]
    have a₂₀ : a₂ ≠ 0 := by contrapose a₁₂; simp [a₁₂]
    have a₁₂₀ : a₁ / a₂ ≠ 0 := by simp [a₁₀, a₂₀]
    let μ := NormedSpace.normalize (a₁ / a₂)
    have μ₁ : ‖μ‖ = 1 := NormedSpace.norm_normalize a₁₂₀
    have t := @hg a₀ (μ * a₁) (μ^2 * a₂) (μ^3 * a₃) (fun z z₁ ↦ ?_) ?_
    · simpa [μ₁] using t
    · have : ‖μ * z‖ ≤ 1 := by simpa [μ₁]
      convert h _ this using 2
      ring
    · simp only [μ₁, Complex.norm_mul, norm_pow, one_pow, one_mul, Complex.real_smul]
      rw [mul_left_comm _ _ a₁, mul_left_comm _ _ a₂, sq, mul_assoc μ]
      congr 1
      simp only [μ, NormedSpace.normalize, Complex.norm_div, inv_div]
      change _ = (‖a₂‖ / ‖a₁‖ : ℝ) * (a₁ / a₂) * _
      field_simp
      norm_cast
      refine (div_mul_cancel₀ _ (by simpa)).symm
  rw [add_assoc ‖a₀‖, ← norm_add_eq_iff_real.2 a₁₂, add_comm ‖a₀‖, add_assoc]
  rcases exists_unit_norm_add_eq a₀ a₃ with ⟨ξ, ξ₁, a₀₃⟩
  rw [← a₀₃]
  refine le_of_sq_le_sq ?_ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have h' z (z₁ : ‖z‖ ≤ 1) : ‖a₃ * z^3 + a₂ * z^2 + a₁ * z + a₀‖ ≤ 1 := by
    convert h z z₁ using 2
    ring
  calc
    _ ≤ (6⁻¹ + 9⁻¹) * (6 * ‖a₁ + a₂‖^2 + 9 * ‖ξ * a₀ + a₃‖^2) := by apply binary_cauchy <;> simp
    _ ≤ _ := by linarith [SquareCoeffBound.CubicCoeffBoundsCore ξ₁ h']
