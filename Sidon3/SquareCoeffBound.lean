module

public import Sidon3.KeySystem

@[expose] public section

open scoped ComplexConjugate Polynomial
open Polynomial (C X)

private lemma complex_down {a : ℝ} {b : ℂ} (h : a = b) : a = b.re := by simp [← h]

namespace SquareCoeffBound

variable {a₀ a₁ a₂ a₃ : ℂ} {ξ : ℂ} (ξ₁ : ‖ξ‖ = 1)

lemma normSq_eval {z : ℂ} (z₁ : ‖z‖ = 1) : (a₃ * z^3 + a₂ * z^2 + a₁ * z + a₀).normSq =
    ((a₀ * conj a₀ + a₁ * conj a₁ + a₂ * conj a₂ + a₃ * conj a₃) +
    2 * (a₁ * conj a₀ + a₂ * conj a₁ + a₃ * conj a₂) * z +
    2 * (a₂ * conj a₀ + a₃ * conj a₁) * z^2 +
    2 * (a₃ * conj a₀) * z^3).re := by
  have z₁' : z.normSq = 1 := by rwa [← Real.sqrt_eq_one, ← Complex.norm_def]
  have h₁ w n : (w * z^n).normSq = (w * conj w).re := by
    simp [Complex.normSq_mul, z₁']
    rfl
  have h₂ := h₁ a₁ 1
  simp only [pow_one] at h₂
  have h₃ := h₁ a₀ 0
  simp only [pow_zero, mul_one] at h₃
  simp only [Complex.normSq_add, h₁, h₂, h₃, ← Complex.add_re, ← Complex.re_ofReal_mul]
  congr 1
  simp [← Complex.inv_eq_conj z₁]
  field

include ξ₁

set_option linter.style.whitespace false in
lemma CubicCoeffBoundsCore_aux {μ₁ μ₂ μ₃ : ℝ} {z₁ z₂ z₃ : ℂ}
    (z₁s : ‖z₁‖ = 1) (z₂s : ‖z₂‖ = 1) (z₃s : ‖z₃‖ = 1)
    (Λ₀ : μ₁ + μ₂ + μ₃ = 10)
    (Λ₁ : μ₁ * z₁ + μ₂ * z₂ + μ₃ * z₃ = 2)
    (Λ₂ : μ₁ * z₁^2 + μ₂ * z₂^2 + μ₃ * z₃^2 = -2)
    (Λ₃ : μ₁ * z₁^3 + μ₂ * z₂^3 + μ₃ * z₃^3 = -1 + 9 * conj ξ) :
    μ₁ * (a₃ * z₁^3 + a₂ * z₁^2 + a₁ * z₁ + a₀).normSq +
    μ₂ * (a₃ * z₂^3 + a₂ * z₂^2 + a₁ * z₂ + a₀).normSq +
    μ₃ * (a₃ * z₃^3 + a₂ * z₃^2 + a₁ * z₃ + a₀).normSq =
    (a₀ + 2 * a₁ - 2 * a₂ - a₃).normSq +
    6 * (a₁ + a₂).normSq +
    9 * (ξ * a₀ + a₃).normSq := by
  rw [
    normSq_eval z₁s, normSq_eval z₂s, normSq_eval z₃s,
    ← Complex.re_ofReal_mul, ← Complex.re_ofReal_mul, ← Complex.re_ofReal_mul,
    ← Complex.add_re, ← Complex.add_re,
  ]
  set δ₀ := a₀ * conj a₀ + a₁ * conj a₁ + a₂ * conj a₂ + a₃ * conj a₃
  set δ₁ := a₁ * conj a₀ + a₂ * conj a₁ + a₃ * conj a₂
  set δ₂ := a₂ * conj a₀ + a₃ * conj a₁
  set δ₃ := a₃ * conj a₀
  set lhs :=
    μ₁ * (δ₀ + 2 * δ₁ * z₁ + 2 * δ₂ * z₁^2 + 2 * δ₃ * z₁^3) +
    μ₂ * (δ₀ + 2 * δ₁ * z₂ + 2 * δ₂ * z₂^2 + 2 * δ₃ * z₂^3) +
    μ₃ * (δ₀ + 2 * δ₁ * z₃ + 2 * δ₂ * z₃^2 + 2 * δ₃ * z₃^3)
  have lhs_tr : lhs = (μ₁ + μ₂ + μ₃ : ℝ) * δ₀ + 2 * (
      (μ₁ * z₁ + μ₂ * z₂ + μ₃ * z₃) * δ₁ +
      (μ₁ * z₁^2 + μ₂ * z₂^2 + μ₃ * z₃^2) * δ₂ +
      (μ₁ * z₁^3 + μ₂ * z₂^3 + μ₃ * z₃^3) * δ₃) := by
    simp only [Complex.ofReal_add]
    ring
  rw [lhs_tr, Λ₀, Λ₁, Λ₂, Λ₃]
  have ξ₁' : ξ.normSq = 1 := by rwa [← Real.sqrt_eq_one, ← Complex.norm_def]
  calc
    _ = 10 * (a₀.normSq + a₁.normSq + a₂.normSq + a₃.normSq) + 2 * (
        (a₃ * conj (2 * a₂)).re +
        ((a₃ + 2 * a₂) * conj (-2 * a₁)).re +
        ((a₃ + 2 * a₂ + -2 * a₁) * conj (-a₀)).re +
        (6 * (a₂ * conj a₁).re) +
        (9 * (a₃ * conj (ξ * a₀)).re)) := by
      rw [Complex.add_re]
      congr
      · simp [δ₀]
        rfl
      simp only [← Complex.add_re, ← Complex.re_ofReal_mul]
      congr 1
      simp [δ₁, δ₂, δ₃, Complex.conj_ofNat]
      ring
    _ = (a₃ + 2 * a₂ + (-2) * a₁ + (-a₀)).normSq + 6 * (a₂ + a₁).normSq +
        9 * (a₃ + ξ * a₀).normSq := by
      simp only [Complex.normSq_add, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_ofNat,
        ξ₁', one_mul]
      linarith
    _ = _ := by
      congr 2
      · rw [← Complex.normSq_neg]
        congr
        ring
      · rw [add_comm]
      · rw [add_comm]

set_option linter.style.whitespace false in
theorem CubicCoeffBoundsCore (h : ∀ z, ‖z‖ ≤ 1 → ‖a₃ * z^3 + a₂ * z^2 + a₁ * z + a₀‖ ≤ 1) :
    6 * ‖a₁ + a₂‖^2 + 9 * ‖ξ * a₀ + a₃‖^2 ≤ 10 := by
  have ξ₁' : ‖conj ξ‖ = 1 := by simpa only [RCLike.norm_conj]
  rcases KeySystem.main ξ₁' with ⟨μ₁, μ₂, μ₃, z₁, z₂, z₃, μ₁₀, μ₂₀, μ₃₀, z₁s, z₂s, z₃s,
    Λ₀, Λ₁, Λ₂, Λ₃⟩
  have A₁ := h z₁ z₁s.le
  have A₂ := h z₂ z₂s.le
  have A₃ := h z₃ z₃s.le
  simp only [Complex.norm_def, Real.sqrt_le_one] at A₁ A₂ A₃
  have B₁ := mul_le_mul_of_nonneg_left A₁ μ₁₀
  have B₂ := mul_le_mul_of_nonneg_left A₂ μ₂₀
  have B₃ := mul_le_mul_of_nonneg_left A₃ μ₃₀
  have := add_le_add (add_le_add B₁ B₂) B₃
  simp only [mul_one, Λ₀, CubicCoeffBoundsCore_aux ξ₁ z₁s z₂s z₃s Λ₀ Λ₁ Λ₂ Λ₃] at this
  simp only [← Complex.normSq_eq_norm_sq]
  refine this.trans' ?_
  simp [Complex.normSq_nonneg]

end SquareCoeffBound
