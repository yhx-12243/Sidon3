module

public import Sidon3.Polynomial.Cohn

@[expose] public section

open scoped ComplexConjugate Finset Polynomial
open Polynomial (C X)

noncomputable section

namespace KeySystem

variable {ξ : ℂ} (ξ₁ : ‖ξ‖ = 1)

def ψ := (ξ + 1) / 4

include ξ₁ in
theorem ψξ : (@ψ ξ) = conj (@ψ ξ) * ξ := by
  simp only [ψ, Complex.conj_ofNat, map_div₀, map_add, map_one]
  rw [← mul_div_right_comm, add_one_mul, Complex.conj_mul', ξ₁, add_comm ξ,
    Complex.ofReal_one, one_pow]

def P : ℂ[X] := X^3 - C (@ψ ξ) * X^2 + C (@ψ ξ) * X - C ξ

theorem dP : (@P ξ).natDegree = 3 := by
  unfold P
  compute_degree!

theorem Pmonic : (@P ξ).Monic := by
  change P.coeff P.natDegree = 1
  rw [dP]
  simp [P]

theorem Pc : (@P ξ).coeff 0 = -ξ := by simp [P]

set_option linter.flexible false in
include ξ₁ in
theorem Pi : (@P ξ).SelfInversive := by
  simp only [Polynomial.SelfInversive, dP, show P.leadingCoeff = 1 from Pmonic, Pc,
    star_one, one_mul, Pi.star_apply, RCLike.star_def, Polynomial.constantCoeff_apply, mul_neg]
  intro i i₃
  interval_cases i <;> simp [P]
  · exact ψξ ξ₁
  · exact ψξ ξ₁
  · rw [Complex.conj_mul', ξ₁, Complex.ofReal_one, one_pow]

def Q : ℂ[X] := 3 * X^2 - 2 * C (@ψ ξ) * X + C (@ψ ξ)

theorem dQ : (@Q ξ).natDegree = 2 := by
  unfold Q
  compute_degree!

theorem Pderiv : (@P ξ).derivative = (@Q ξ) := by
  simp only [P, Q, Polynomial.derivative_sub, Polynomial.derivative_X_pow_succ, Nat.cast_ofNat,
    map_add, map_one, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, Nat.cast_one,
    pow_one, zero_add, Polynomial.derivative_X, mul_one, sub_zero, add_left_inj]
  congr 1
  · congr
    convert (map_add C (2 : ℂ) 1).symm
    norm_cast
  · rw [one_add_one_eq_two, ← mul_assoc, mul_comm 2]

include ξ₁ in
theorem Qr : ((@Q ξ).roots.toFinset : Set ℂ) ⊆ Metric.ball 0 1 := by
  intro r rr
  simp only [SetLike.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq,
    Polynomial.IsRoot.def] at rr
  replace rr := rr.2
  simp only [Q, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at rr
  simp only [mem_ball_zero_iff]
  have h₁ : (2 * r - 1) * (@ψ ξ) = 3 * r^2 := by grind
  have h₂ := congrArg norm h₁
  have h₃ : ‖@ψ ξ‖ ≤ 2⁻¹ := by
    simp only [ψ, Complex.norm_div, Complex.norm_ofNat]
    grw [norm_add_le, ξ₁]
    simp
    linarith
  simp only [Complex.norm_mul, Complex.norm_ofNat, norm_pow] at h₂
  have h₄ : 3 * ‖r‖^2 ≤ ‖r‖ + 2⁻¹ := by
    calc
      _ = ‖2 * r - 1‖ * ‖ψ‖ := h₂.symm
      _ ≤ ‖2 * r - 1‖ * 2⁻¹ := by grw [h₃]
      _ ≤ (2 * ‖r‖ + 1) * 2⁻¹ := by
        gcongr
        grw [norm_sub_le]
        simp
      _ = _ := by field
  nlinarith

include ξ₁ in
theorem Pr : ((@P ξ).roots.toFinset : Set ℂ) ⊆ Metric.sphere 0 1 := by
  rw [(Pi ξ₁).roots_sphere_iff, Pderiv]
  exact (Qr ξ₁).trans Metric.ball_subset_closedBall

include ξ₁ in
theorem Ps : (@P ξ).Separable := by
  rw [P.separable_def, Pderiv, Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  intro r
  rw [← not_and_or]
  intro ⟨r₁, r₂⟩
  simp only [Polynomial.coe_aeval_eq_eval] at r₁ r₂
  have r₁' : r ∈ (@P ξ).roots.toFinset := by
    simp only [r₁, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def,
      and_true]
    intro P₀
    have := @dP ξ
    simp [P₀] at this
  have r₂' : r ∈ (@Q ξ).roots.toFinset := by
    simp only [r₂, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def,
      and_true]
    intro Q₀
    have := @dQ ξ
    simp [Q₀] at this
  have r₃ := Pr ξ₁ r₁'
  have r₄ := Qr ξ₁ r₂'
  simp only [mem_sphere_zero_iff_norm] at r₃
  simp only [mem_ball_zero_iff] at r₄
  exact r₃.not_lt r₄

structure KRS (ξ) where
  z₁ : ℂ
  z₂ : ℂ
  z₃ : ℂ
  σ₁ : z₁ + z₂ + z₃ = @ψ ξ
  σ₂ : z₁ * z₂ + z₁ * z₃ + z₂ * z₃ = @ψ ξ
  σ₃ : z₁ * z₂ * z₃ = ξ
  z₁₂ : z₁ ≠ z₂
  z₁₃ : z₁ ≠ z₃
  z₂₃ : z₂ ≠ z₃
  z₁s : ‖z₁‖ = 1
  z₂s : ‖z₂‖ = 1
  z₃s : ‖z₃‖ = 1
  z₁r : z₁^3 - @ψ ξ * z₁^2 + @ψ ξ * z₁ - ξ = 0
  z₂r : z₂^3 - @ψ ξ * z₂^2 + @ψ ξ * z₂ - ξ = 0
  z₃r : z₃^3 - @ψ ξ * z₃^2 + @ψ ξ * z₃ - ξ = 0

def KRS.rotate (κ : KRS ξ) : KRS ξ := {
  z₁ := κ.z₂
  z₂ := κ.z₃
  z₃ := κ.z₁
  σ₁ := by rw [← κ.σ₁]; ring
  σ₂ := by rw [← κ.σ₂]; ring
  σ₃ := by conv_rhs => { rw [← κ.σ₃] }; ring
  z₁₂ := κ.z₂₃
  z₁₃ := κ.z₁₂.symm
  z₂₃ := κ.z₁₃.symm
  z₁s := κ.z₂s
  z₂s := κ.z₃s
  z₃s := κ.z₁s
  z₁r := κ.z₂r
  z₂r := κ.z₃r
  z₃r := κ.z₁r
}

include ξ₁ in
instance : Nonempty (KRS ξ) := by
  have ps := IsAlgClosed.splits (@P ξ)
  have h₁ := Polynomial.nodup_roots (Ps ξ₁)
  have h₂ := ps.natDegree_eq_card_roots.symm
  rw [dP] at h₂
  let 𝒲 : Finset ℂ := ⟨(@P ξ).roots, h₁⟩
  have h₃ : #𝒲 = 3 := h₂
  rw [Finset.card_eq_three] at h₃
  rcases h₃ with ⟨z₁, z₂, z₃, z₁₂, z₁₃, z₂₃, 𝒲spec⟩
  have h₃ : P.roots = (Multiset.ndinsert z₂ {z₃}).ndinsert z₁ := congrArg Finset.val 𝒲spec
  rw [
    Multiset.ndinsert_of_notMem (a := z₂) (by simpa),
    Multiset.ndinsert_of_notMem (by simp [z₁₂, z₁₃]),
  ] at h₃
  change P.roots = {z₁, z₂, z₃} at h₃
  have σ₁ : z₁ + z₂ + z₃ = @ψ ξ := by
    have := ps.nextCoeff_eq_neg_sum_roots_of_monic Pmonic
    simp only [h₃] at this
    rw [Polynomial.nextCoeff_of_natDegree_pos, dP] at this
    · simp [P] at this
      grind
    simp [dP]
  have σ₂ : z₁ * z₂ + z₁ * z₃ + z₂ * z₃ = @ψ ξ := by
    have := ps.eq_prod_roots_of_monic Pmonic
    simp only [h₃, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton] at this
    have μ₁ := congr(($this).coeff 1)
    simp [P, sub_mul] at μ₁
    simp [μ₁]
    ring
  have σ₃ : z₁ * z₂ * z₃ = ξ := by
    have := ps.coeff_zero_eq_prod_roots_of_monic Pmonic
    simp [h₃, dP, show Odd 3 from ⟨1, rfl⟩] at this
    simp [P] at this
    simp [this, mul_assoc]
  have := Pr ξ₁
  simp only [h₃, Set.insert_subset_iff, Multiset.insert_eq_cons, Multiset.toFinset_cons,
    Multiset.toFinset_singleton, Finset.coe_insert, Finset.coe_singleton, mem_sphere_zero_iff_norm,
    Set.singleton_subset_iff] at this
  rcases this with ⟨z₁s, z₂s, z₃s⟩
  have h₄ := Multiset.Subset.refl (@P ξ).roots
  conv_lhs at h₄ => rw [h₃]
  simp only [← and_and_left, Multiset.insert_eq_cons, Multiset.cons_subset, Polynomial.mem_roots',
    ne_eq, Polynomial.IsRoot.def, Multiset.singleton_subset] at h₄
  rcases h₄ with ⟨-, z₁r, z₂r, z₃r⟩
  simp only [P, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] at z₁r z₂r z₃r
  exact ⟨{z₁, z₂, z₃, σ₁, σ₂, σ₃, z₁₂, z₁₃, z₂₃, z₁s, z₂s, z₃s, z₁r, z₂r, z₃r}⟩

def Λ (z₁ z₂ z₃ : ℂ) := 2 * (5 * z₂ * z₃ - z₂ - z₃ - 1) / ((z₁ - z₂) * (z₁ - z₃))

theorem Λ₀ (κ : KRS ξ) : Λ κ.z₁ κ.z₂ κ.z₃ + Λ κ.z₂ κ.z₃ κ.z₁ + Λ κ.z₃ κ.z₁ κ.z₂ = 10 := by
  have z₁₂ := κ.z₁₂
  have z₁₃ := κ.z₁₃
  have z₂₃ := κ.z₂₃
  unfold Λ
  field (disch := grind)

theorem Λ₁ (κ : KRS ξ) :
    Λ κ.z₁ κ.z₂ κ.z₃ * κ.z₁ +
    Λ κ.z₂ κ.z₃ κ.z₁ * κ.z₂ +
    Λ κ.z₃ κ.z₁ κ.z₂ * κ.z₃ = 2 := by
  have z₁₂ := κ.z₁₂
  have z₁₃ := κ.z₁₃
  have z₂₃ := κ.z₂₃
  unfold Λ
  field (disch := grind)

theorem Λ₂ (κ : KRS ξ) :
    Λ κ.z₁ κ.z₂ κ.z₃ * κ.z₁^2 +
    Λ κ.z₂ κ.z₃ κ.z₁ * κ.z₂^2 +
    Λ κ.z₃ κ.z₁ κ.z₂ * κ.z₃^2 = -2 := by
  have z₁₂ := κ.z₁₂
  have z₁₃ := κ.z₁₃
  have z₂₃ := κ.z₂₃
  unfold Λ
  field (disch := grind)

theorem Λ₃ (κ : KRS ξ) :
    Λ κ.z₁ κ.z₂ κ.z₃ * κ.z₁^3 +
    Λ κ.z₂ κ.z₃ κ.z₁ * κ.z₂^3 +
    Λ κ.z₃ κ.z₁ κ.z₂ * κ.z₃^3 = -1 + 9 * ξ := by
  have z₁₂ := κ.z₁₂
  have z₁₃ := κ.z₁₃
  have z₂₃ := κ.z₂₃
  calc
    _ = -2 * (κ.z₁ + κ.z₂ + κ.z₃) - 2 * (κ.z₁ * κ.z₂ + κ.z₁ * κ.z₃ + κ.z₂ * κ.z₃)
        + 10 * (κ.z₁ * κ.z₂ * κ.z₃) := by
      unfold Λ
      field (disch := grind)
    _ = _ := by
      simp [κ.σ₁, κ.σ₂, κ.σ₃, ψ]
      ring

def Λ' (z : ℂ) : ℂ := 36 * z^2 / (1 - 2 * z + 12 * z^2 - 2 * z^3 + z^4)

theorem Λ'spec (κ : KRS ξ) : Λ κ.z₁ κ.z₂ κ.z₃ = Λ' κ.z₁ := by
  have h₁ := κ.z₁r
  set z := κ.z₁
  have h₂ : ξ = 4 * @ψ ξ - 1 := by
    simp [ψ]
    field
  nth_rw 3 [h₂] at h₁
  have h₃ : @ψ ξ * (z^2 - z + 4) = z^3 + 1 := by grind
  have h₄ : z ^ 2 - z + 4 ≠ 0 := by grind
  have h₅ : @ψ ξ = (z^3 + 1) / (z^2 - z + 4) := eq_div_of_mul_eq h₄ h₃
  have h₆ : z + _ + _ = _ := κ.σ₁
  rw [
    add_assoc, ← eq_sub_iff_add_eq', h₅, div_sub' h₄,
    show z^3 + 1 - (z^2 - z + 4) * z = z^2 - 4 * z + 1 by ring,
  ] at h₆
  have h₇ : z * _ + z * _ + _ = _ := κ.σ₂
  rw [
    ← mul_add, h₆, ← eq_sub_iff_add_eq', h₅, ← mul_div_assoc, ← sub_div,
    show z^3 + 1 - z * (z^2 - 4 * z + 1) = 4 * z^2 - z + 1 by ring,
  ] at h₇
  have h₈ : 1 - 2 * z + 12 * z ^ 2 - 2 * z ^ 3 + z ^ 4 ≠ 0 := by
    intro e
    replace e : 12 * z^2 = -z^4 + 2 * z^3 + 2 * z - 1 := by grind
    apply_fun norm at e
    have z₁ : ‖z‖ = 1 := κ.z₁s
    simp only [z₁, Complex.norm_mul, Complex.norm_ofNat, norm_pow, one_pow, mul_one] at e
    have : (12 : ℝ) ≤ 6 := by
      calc
        12 = _ := e
        _ ≤ 6 := by
          grw [norm_sub_le, norm_add_le, norm_add_le]
          simp [z₁]
          norm_num
    norm_num at this
  unfold Λ Λ'
  rw [div_eq_div_iff _ h₈]
  swap
  · simp only [mul_ne_zero_iff, sub_ne_zero]
    exact ⟨κ.z₁₂, κ.z₁₃⟩
  rw [
    sub_sub _ κ.z₂, mul_sub (z - κ.z₂), sub_mul, sub_mul, ← sub_add,
    sub_sub (z * z), mul_comm κ.z₂, ← mul_add, mul_assoc 5,
    h₆, h₇
  ]
  field (disch := grind)

def Λᵣ (z : ℂ) : ℝ := 18 / (6 - 2 * z.re + (z^2).re)

theorem Λᵣspec {z : ℂ} (z₁ : ‖z‖ = 1) : Λ' z = Λᵣ z := by
  calc
    _ = 36 / ((z⁻¹)^2 - 2 * z⁻¹ + 12 - 2 * z + z^2) := by
      have h₁ : z^2 ≠ 0 := by
        rw [pow_ne_zero_iff two_ne_zero]
        rintro rfl
        simp at z₁
      rw [← mul_div_mul_right _ _ h₁]
      unfold Λ'
      congr
      simp at h₁
      field_simp
    _ = 36 / ((conj z)^2 - 2 * conj z + 12 - 2 * z + z^2) := by rw [Complex.inv_eq_conj z₁]
    _ = 36 / (12 - 2 * (2 * z.re : ℝ) + (2 * (z^2).re : ℝ) : ℂ) := by
      congr 1
      rw [← Complex.add_conj, ← Complex.add_conj, map_pow]
      ring
    _ = _ := by
      unfold Λᵣ
      norm_cast
      conv_rhs => rw [← mul_div_mul_right _ _ two_ne_zero]
      ring

theorem Λᵣpos {z : ℂ} (z₁ : ‖z‖ = 1) : 0 < Λᵣ z := by
  refine div_pos (by simp) ?_
  have a : z.re ≤ 1 := z.re_le_norm.trans_eq z₁
  have b : -1 ≤ (z^2).re := neg_le_of_abs_le <| (z^2).abs_re_le_norm.trans (by simp [z₁])
  linarith

include ξ₁ in
theorem main : ∃ (μ₁ μ₂ μ₃ : ℝ) (z₁ z₂ z₃ : ℂ),
    0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧ 0 ≤ μ₃ ∧
    ‖z₁‖ = 1 ∧ ‖z₂‖ = 1 ∧ ‖z₃‖ = 1 ∧
    μ₁ + μ₂ + μ₃ = 10 ∧
    μ₁ * z₁ + μ₂ * z₂ + μ₃ * z₃ = 2 ∧
    μ₁ * z₁^2 + μ₂ * z₂^2 + μ₃ * z₃^2 = -2 ∧
    μ₁ * z₁^3 + μ₂ * z₂^3 + μ₃ * z₃^3 = -1 + 9 * ξ := by
  rcases instNonemptyKRS ξ₁ with ⟨κ⟩
  let μ₁ := Λᵣ κ.z₁
  let μ₂ := Λᵣ κ.z₂
  let μ₃ := Λᵣ κ.z₃
  let μ₁' := Λ κ.z₁ κ.z₂ κ.z₃
  let μ₂' := Λ κ.z₂ κ.z₃ κ.z₁
  let μ₃' := Λ κ.z₃ κ.z₁ κ.z₂
  have μ₁spec : μ₁' = μ₁ := (Λ'spec κ).trans (Λᵣspec κ.z₁s)
  have μ₂spec : μ₂' = μ₂ := (Λ'spec κ.rotate).trans (Λᵣspec κ.z₂s)
  have μ₃spec : μ₃' = μ₃ := (Λ'spec κ.rotate.rotate).trans (Λᵣspec κ.z₃s)
  refine ⟨
    μ₁, μ₂, μ₃, κ.z₁, κ.z₂, κ.z₃,
    (Λᵣpos κ.z₁s).le, (Λᵣpos κ.z₂s).le, (Λᵣpos κ.z₃s).le,
    κ.z₁s, κ.z₂s, κ.z₃s, ?_, ?_, ?_, ?_
  ⟩
  · have : μ₁' + μ₂' + μ₃' = 10 := Λ₀ κ
    simp [μ₁spec, μ₂spec, μ₃spec] at this
    norm_cast at this
  · have : μ₁' * κ.z₁ + μ₂' * κ.z₂ + μ₃' * κ.z₃ = 2 := Λ₁ κ
    simpa [μ₁spec, μ₂spec, μ₃spec] using this
  · have : μ₁' * κ.z₁^2 + μ₂' * κ.z₂^2 + μ₃' * κ.z₃^2 = -2 := Λ₂ κ
    simpa [μ₁spec, μ₂spec, μ₃spec] using this
  · have : μ₁' * κ.z₁^3 + μ₂' * κ.z₂^3 + μ₃' * κ.z₃^3 = -1 + 9 * ξ := Λ₃ κ
    simpa [μ₁spec, μ₂spec, μ₃spec] using this

end KeySystem
