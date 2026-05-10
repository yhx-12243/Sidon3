module

public import Mathlib.Algebra.Polynomial.Mirror
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Star.Basic

@[expose] public section

namespace Polynomial

lemma roots_star {R : Type u} [CommRing R] [StarRing R] [IsDomain R] {p : R[X]} :
    p.roots.map star = (p.map (starRingEnd R)).roots := by
  refine le_antisymm ?_ ?_
  · exact p.map_roots_le_of_injective star_injective
  · rw [← Multiset.map_le_map_iff star_injective, Multiset.map_map]
    simp only [Function.comp_apply, star_star]
    convert (p.map (starRingEnd R)).map_roots_le_of_injective (f := starRingEnd R) star_injective
    simp [map_map]

@[simp]
theorem leadingCoeff_pow'' {R : Type u} [Semiring R] [IsReduced R] {p : R[X]} {n : ℕ} :
    (p ^ n).leadingCoeff = p.leadingCoeff ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    by_cases p₀ : p = 0
    · simp [p₀]
    · apply leadingCoeff_pow'
      simpa

@[simp]
theorem reverse_pow {R : Type u} [Semiring R] [IsReduced R] {p : R[X]} {n : ℕ} :
    (p ^ n).reverse = p.reverse ^ n := by
  induction n with
  | zero => simp [reverse]
  | succ n h =>
    by_cases p₀ : p = 0
    · simp [p₀]
    · rw [pow_succ, pow_succ, reverse_mul, h]
      rw [leadingCoeff_pow'', ← pow_succ]
      simpa

private lemma roots_reverse_aux₁ {R : Type u} [Field R] {p : R[X]} (p₀ : p.constantCoeff ≠ 0)
    {r : R} (r₀ : r ≠ 0) : p.rootMultiplicity r⁻¹ ≤ p.reverse.rootMultiplicity r := by
  rw [le_rootMultiplicity_iff]
  swap
  · contrapose p₀
    simp at p₀
    simp [p₀]
  set n := p.rootMultiplicity r⁻¹
  obtain ⟨q, h₁⟩ : (X - C r⁻¹)^n ∣ p := p.pow_rootMultiplicity_dvd r⁻¹
  have h₂ := congrArg reverse h₁
  simp only [reverse_mul_of_domain, reverse_pow] at h₂
  have h₃ : (X - C r⁻¹).reverse = (X - C r) * C (-r⁻¹) := by simp [reverse, sub_mul, ← map_mul, r₀]
  rw [h₃, mul_pow, mul_assoc] at h₂
  exact ⟨_, h₂⟩

private lemma roots_reverse_aux₂ {R : Type u} [Field R] {p : R[X]} (p₀ : p.constantCoeff ≠ 0)
    {r : R} (r₀ : r ≠ 0) : p.rootMultiplicity r⁻¹ = p.reverse.rootMultiplicity r := by
  refine le_antisymm (roots_reverse_aux₁ p₀ r₀) ?_
  have p₀' : p.reverse.constantCoeff ≠ 0 := by
    contrapose p₀
    simp at p₀
    simp [p₀]
  have r₀' : r⁻¹ ≠ 0 := by simpa
  convert roots_reverse_aux₁ p₀' r₀'
  · simp
  change p = (p.reflect p.natDegree).reflect p.reverse.natDegree
  have h₁ : p.reverse.natDegree = p.natDegree := by
    simp only [p.natDegree_eq_reverse_natDegree_add_natTrailingDegree, Nat.left_eq_add,
      natTrailingDegree_eq_zero]
    exact Or.inr p₀
  rw [h₁]
  exact reflect_reflect.symm

lemma roots_mirror {R : Type u} [Field R] {p : R[X]} : p.roots.map Inv.inv = p.mirror.roots := by
  by_cases p₀ : p = 0
  · simp [p₀]
  haveI := Classical.typeDecidableEq R
  ext r
  conv_lhs => rw [← inv_inv r, p.roots.count_map_eq_count' Inv.inv inv_injective]
  simp only [count_roots]
  by_cases r₀ : r = 0
  · simp [r₀, rootMultiplicity_eq_natTrailingDegree', mirror_natTrailingDegree]
  · simp only [mirror]
    set n := p.natTrailingDegree
    have n_spec : rootMultiplicity 0 p = n := rootMultiplicity_eq_natTrailingDegree'
    rcases p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p₀ 0 with ⟨q, pq, q₀⟩
    simp only [n_spec, map_zero, sub_zero] at pq
    simp only [X_dvd_iff, map_zero, sub_zero] at q₀
    conv_lhs => rw [pq]
    rw [rootMultiplicity_mul (by simpa [← pq]), rootMultiplicity_mul (by simpa)]
    have h₁ : (X ^ n).rootMultiplicity r = 0 := by simp [r₀]
    have h₂ : (X ^ n).rootMultiplicity r⁻¹ = 0 := by simp [r₀]
    simp only [h₁, h₂, zero_add, add_zero]
    convert roots_reverse_aux₂ q₀ r₀ using 2
    rw [pq, reverse_X_pow_mul]

end Polynomial
