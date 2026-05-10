module

public import Mathlib.Analysis.Complex.Polynomial.GaussLucas
public import Sidon3.Polynomial.SelfInversive

@[expose] public section

open scoped ComplexConjugate

namespace Polynomial.SelfInversive

@[simp]
theorem _root_.Polynomial.reverse_prod_of_domain {R : Type u} [CommSemiring R] [NoZeroDivisors R]
    (m : Multiset R[X]) : m.prod.reverse = (m.map reverse).prod := by
  let φ : R[X] →* R[X] := {
    toFun := reverse
    map_one' := reverse_C 1
    map_mul' := reverse_mul_of_domain
  }
  exact map_multiset_prod φ m

@[simp]
theorem _root_.Multiset.norm_prod {α : Type u} [SeminormedCommRing α] [NormOneClass α]
    [NormMulClass α] (m : Multiset α) : ‖m.prod‖ = (m.map norm).prod :=
  map_multiset_prod normHom m

private lemma Blaschke_product {p : ℂ[X]} (hp : (p.roots.toFinset : Set ℂ) ⊆ Metric.closedBall 0 1)
    {r : ℂ} (r₁ : 1 ≤ ‖r‖) : ‖(p.reverse.map conj).eval r‖ ≤ ‖p.eval r‖ := by
  have h₁ := (IsAlgClosed.splits p).eq_prod_roots
  have h₂ := congrArg reverse h₁
  have h₃ (x : ℂ) : (X - C x).reverse = 1 - C x * X := by simp [reverse]
  simp only [reverse_mul_of_domain, reverse_C, reverse_prod_of_domain] at h₂
  simp only [Multiset.map_map, Function.comp_apply, h₃] at h₂
  have h₄ : p.reverse.map conj = C (conj p.leadingCoeff) *
      (p.roots.map (fun x ↦ 1 - C (conj x) * X)).prod := by
    rw [h₂, Polynomial.map_mul, map_C]
    congr
    change (p.roots.map (fun x ↦ 1 - C x * X)).prod.mapRingHom conj = _
    simp [map_multiset_prod]
  conv =>
    congr
    · rw [h₄]
    · rw [h₁]
  simp only [eval_mul, eval_C, Complex.norm_mul, Complex.norm_conj, eval_multiset_prod]
  gcongr
  simp only [Multiset.map_map, Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C,
    eval_X, Multiset.norm_prod]
  refine Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ norm_nonneg _) (fun s sr ↦ ?_)
  have s₁ : ‖s‖ ≤ 1 := mem_closedBall_zero_iff.1 (hp (by simp [sr]))
  rw [norm_sub_rev r s]
  simp only [Complex.norm_def]
  refine Real.sqrt_le_sqrt ?_
  simp only [Complex.normSq_sub, Complex.normSq_conj, Complex.conj_conj,
    map_one, map_mul, one_mul]
  gcongr 1
  have s₁' : s.normSq ≤ 1 := by
    simp only [Complex.norm_def] at s₁
    exact Real.sqrt_le_one.1 s₁
  have r₁' : 1 ≤ r.normSq := by
    simp only [Complex.norm_def] at r₁
    exact Real.one_le_sqrt.1 r₁
  nlinarith

theorem roots_sphere_iff {p : ℂ[X]} (hp : p.SelfInversive) :
    (p.roots.toFinset : Set ℂ) ⊆ Metric.sphere (0 : ℂ) 1 ↔
    (p.derivative.roots.toFinset : Set ℂ) ⊆ Metric.closedBall (0 : ℂ) 1 := by
  rcases p.natDegree.eq_zero_or_pos with (p₀ | p₀)
  · rw [natDegree_eq_zero] at p₀
    rcases p₀ with ⟨c, rfl⟩
    simp
  rw [← hp.disk_iff_sphere]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := rootSet_derivative_subset_convexHull_rootSet (natDegree_pos_iff_degree_pos.1 p₀)
    simp only [rootSet, aroots, Algebra.algebraMap_self, map_id] at this
    grw [this, h]
    apply subset_of_eq
    rw [convexHull_eq_self]
    exact convex_closedBall 0 1
  · set q := p.derivative
    set n := p.natDegree
    let α := p.leadingCoeff
    let β := p.constantCoeff
    have α₀ : α ≠ 0 := by
      simp only [α, leadingCoeff_ne_zero]
      intro p₀'
      simp [n, p₀'] at p₀
    have dq : q.natDegree = n - 1 := by
      unfold natDegree
      rw [p.degree_derivative_eq p₀]
      rfl
    have q₀ : q ≠ 0 := by
      intro q₀
      have n₀ : n = 0 := natDegree_eq_zero_of_derivative_eq_zero q₀
      exact n₀.not_gt p₀
    have αβ : ‖α‖ = ‖β‖ := hp.norm_head_tail
    have deg₁ : (conj α • (X * q) + β • q.reverse.map conj).natDegree ≤ n := by
      refine natDegree_add_le_of_degree_le ?_ ?_ <;> grw [natDegree_smul_le]
      · rw [natDegree_X_mul q₀, dq, Nat.sub_one_add_one_eq_of_pos p₀]
      · simp only [natDegree_map, reverse_natDegree, dq]
        omega
    have deg₂ : ((n • conj α) • p).natDegree ≤ n := p.natDegree_smul_le _
    have id₁ : conj α • (X * q) + β • q.reverse.map conj = (n • conj α) • p := by
      rw [ext_iff_natDegree_le deg₁ deg₂]
      intro i ih
      simp only [coeff_reverse, dq, coeff_add, coeff_smul, smul_eq_mul, coeff_map, nsmul_eq_mul]
      have h₁ : conj α * p.coeff i = conj (p.coeff (n - i)) * β := hp i ih
      apply Nat.eq_or_lt_of_le at ih
      rcases ih with (rfl | ih)
      · have := n.sub_one_lt p₀.ne'
        rw [
          revAt_eq_self_of_lt this,
          coeff_eq_zero_of_natDegree_lt (p := q) (by rw [dq]; exact this),
          map_zero, mul_zero, add_zero,
        ]
        rcases n.exists_eq_add_one_of_ne_zero p₀.ne' with ⟨m, mspec⟩
        rw [mspec, coeff_X_mul, coeff_derivative]
        simp
        ring
      · rw [
          revAt_le (Nat.le_sub_one_of_lt ih), coeff_derivative, ← Nat.cast_add_one,
          show n - 1 - i + 1 = n - i by omega,
          map_mul, map_natCast, ← mul_assoc, mul_comm β, ← h₁,
          mul_assoc, ← mul_add, mul_assoc (n : ℂ), mul_comm (n : ℂ), mul_assoc,
        ]
        congr
        cases i with
        | zero => simp
        | succ j =>
          rw [coeff_X_mul, coeff_derivative, ← mul_add]
          congr
          norm_cast
          exact Nat.add_sub_cancel' ih.le
    intro r rr
    simp at rr
    have h₁ := congrArg (eval r) id₁
    simp only [rr.2, eval_add, eval_smul, eval_mul, eval_X,
      smul_eq_mul, nsmul_eq_mul, mul_zero] at h₁
    have h₂ := congrArg norm (neg_eq_of_add_eq_zero_right h₁)
    simp only [← αβ, α₀, norm_neg, Complex.norm_mul, Complex.norm_conj,
      mul_eq_mul_left_iff, norm_eq_zero, or_false] at h₂
    simp only [mem_closedBall_zero_iff]
    by_contra! r₁
    have := Blaschke_product h r₁.le
    rw [← h₂, mul_le_iff_le_one_left] at this
    · exact this.not_gt r₁
    simp only [norm_pos_iff]
    intro rq
    have := h (a := r) (by simp [q₀, rq])
    simp only [mem_closedBall_zero_iff] at this
    exact this.not_gt r₁

end Polynomial.SelfInversive
