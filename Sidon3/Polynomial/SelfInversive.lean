module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Sidon3.Polynomial.RootsUtil

@[expose] public section

variable {R : Type u}

namespace Polynomial

def SelfInversive [Semiring R] [Star R] (p : R[X]) : Prop :=
  ∀ i ≤ p.natDegree, star p.leadingCoeff * p.coeff i =
    star p.coeff (p.natDegree - i) * p.constantCoeff

namespace SelfInversive

theorem head_tail [Semiring R] [Star R] {p : R[X]} (hp : p.SelfInversive) :
    star p.leadingCoeff * p.leadingCoeff = star p.constantCoeff * p.constantCoeff := by
  convert hp p.natDegree (Nat.le_refl _)
  simp only [Nat.sub_self]
  rfl

theorem norm_head_tail [NormedRing R] [StarRing R] [CStarRing R]
    {p : R[X]} (hp : p.SelfInversive) : ‖p.leadingCoeff‖ = ‖p.constantCoeff‖ := by
  have := congrArg norm hp.head_tail
  simp only [CStarRing.norm_star_mul_self, ← sq] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

@[simp]
theorem constantCoeff_zero [NormedRing R] [StarRing R] [CStarRing R]
    {p : R[X]} (hp : p.SelfInversive) : p.constantCoeff = 0 ↔ p = 0 := by
  constructor
  · intro p₀
    simpa [p₀] using hp.norm_head_tail
  · rintro rfl
    simp

@[simp]
theorem natTrailingDegree_eq_zero [NormedRing R] [StarRing R] [CStarRing R]
    {p : R[X]} (hp : p.SelfInversive) : p.natTrailingDegree = 0 := by
  simp only [← constantCoeff_apply, hp, Polynomial.natTrailingDegree_eq_zero,
    constantCoeff_zero, ne_eq]
  exact eq_or_ne p 0

theorem norm_symmetric [NormedRing R] [StarRing R] [CStarRing R] [NormMulClass R]
    {p : R[X]} (hp : p.SelfInversive) {i : ℕ} (hi : i ≤ p.natDegree) :
    ‖p.coeff i‖ = ‖p.coeff (p.natDegree - i)‖ := by
  have := congrArg norm (hp i hi)
  simp only [norm_mul, norm_star, ← hp.norm_head_tail, mul_comm ‖p.leadingCoeff‖] at this
  by_cases h : ‖p.leadingCoeff‖ = 0
  · simp at h
    simp [h]
  · simpa only [mul_left_inj' h, Pi.star_apply, norm_star] using this

theorem _root_.Polynomial.SelfInversive_iff [CommSemiring R] [StarRing R] {p : R[X]} :
    p.SelfInversive ↔
      star p.leadingCoeff • p = p.constantCoeff • p.reverse.map (starRingEnd R) := by
  have deg₁ : (star p.leadingCoeff • p).natDegree ≤ p.natDegree := p.natDegree_smul_le _
  have deg₂ : (p.constantCoeff • p.reverse.map (starRingEnd R)).natDegree ≤ p.natDegree := by
    grw [natDegree_smul_le, natDegree_map_le, reverse_natDegree_le]
  rw [ext_iff_natDegree_le deg₁ deg₂]
  refine forall₂_congr fun i ih ↦ ?_
  simp [mul_comm (p.coeff 0), coeff_reverse, ih]
  rfl

theorem roots_map [NormedField R] [StarRing R] [CStarRing R] {p : R[X]} (hp : p.SelfInversive) :
    p.roots = p.roots.map (fun x ↦ star x⁻¹) := by
  by_cases p₀ : p = 0
  · simp [p₀]
  have h₁ := congrArg roots (SelfInversive_iff.1 hp)
  rw [roots_smul_nonzero, roots_smul_nonzero, ← roots_star] at h₁
  rotate_left
  · simpa only [ne_eq, constantCoeff_zero, hp]
  · simpa
  calc
    _ = p.reverse.roots.map star := h₁
    _ = (p.roots.map Inv.inv).map star := by
      congr
      rw [roots_mirror]
      congr
      simp [mirror, hp]
    _ = _ := by
      rw [Multiset.map_map]
      rfl

theorem root_multiplicity [NormedField R] [StarRing R] [CStarRing R] {p : R[X]}
    (hp : p.SelfInversive) (r : R) : p.rootMultiplicity r = p.rootMultiplicity (star r⁻¹) := by
  haveI := Classical.typeDecidableEq R
  simp only [← count_roots]
  have hf : Function.Injective (fun (x : R) ↦ star x⁻¹) := by
    intro _ _ h
    simpa using h
  conv_rhs => rw [hp.roots_map, p.roots.count_map_eq_count' (fun x ↦ star x⁻¹) hf]

theorem disk_iff_sphere [NormedField R] [DecidableEq R] [StarRing R] [CStarRing R] {p : R[X]}
    (hp : p.SelfInversive) : (p.roots.toFinset : Set R) ⊆
      Metric.closedBall (0 : R) 1 ↔ (p.roots.toFinset : Set R) ⊆ Metric.sphere (0 : R) 1 := by
  refine ⟨fun h r rr ↦ ?_, fun h ↦ h.trans Metric.sphere_subset_closedBall⟩
  have r₁ := h rr
  simp only [mem_closedBall_zero_iff] at r₁
  simp only [mem_sphere_zero_iff_norm]
  rw [
    SetLike.mem_coe, Multiset.mem_toFinset, mem_roots', ← rootMultiplicity_pos',
    hp.root_multiplicity r, rootMultiplicity_pos', ← mem_roots', ← Multiset.mem_toFinset,
  ] at rr
  have r₂ := h rr
  simp only [mem_closedBall_zero_iff, star_inv₀, norm_inv, norm_star] at r₂
  by_cases r₀ : r = 0
  · simp [r₀, ← coeff_zero_eq_eval_zero, ← constantCoeff_apply, hp] at rr
  · rw [inv_le_one₀ (by simpa)] at r₂
    exact le_antisymm r₁ r₂

end Polynomial.SelfInversive
