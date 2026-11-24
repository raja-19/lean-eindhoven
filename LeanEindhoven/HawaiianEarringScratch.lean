module

import Mathlib

open Metric Set Relation Complex Bornology

/-- Subspace definition of Hawaiian Earring -/
noncomputable def p (n : ℕ) : ℂ := ⟨1 / n, 0⟩
noncomputable def r (n : ℕ) : ℝ := 1 / n
noncomputable def H1 : Set ℂ := ⋃ n, sphere (p n) (r n)

noncomputable def Ear (m : ℕ) : Set ℂ :=
  (⋃ n : Fin (m + 1), sphere (p n) (r n)) ∪ closedBall (p (m + 2)) (r (m + 2))

lemma isClosed_Ear (m : ℕ) : IsClosed (Ear m) := by
  refine IsClosed.union ?_ ?_
  · apply isClosed_iUnion_of_finite 
    intro k
    exact isClosed_sphere
  · exact isClosed_closedBall

lemma isBounded_Ear (m : ℕ) : IsBounded (Ear m) := by
  refine IsBounded.union ?_ ?_
  · rw [isBounded_iUnion]
    intro k
    exact isBounded_sphere
  · exact isBounded_closedBall

lemma isCompact_Ear (m : ℕ) : CompactSpace (Ear m) := by
  rw [← isCompact_iff_compactSpace]
  exact isCompact_of_isClosed_isBounded (isClosed_Ear m) (isBounded_Ear m)


lemma Ear_union_H1_closedBall (m : ℕ) : Ear (m : ℕ) = H1 ∪ closedBall (p (m + 2)) (r (m + 2)) := by
  sorry

lemma H1_inter_Ear : H1 = ⋂ n, Ear n := by
    simp only [Ear_union_H1_closedBall]
    rw [← union_iInter]
    have h1 : ⋂ i, closedBall (p (i + 2)) (r (i + 2)) = {⟨0,0⟩} := by
      ext x
      refine ⟨fun f ↦ ?_, fun f ↦ ?_⟩
      <;> rw [mem_singleton_iff] at *
      · have h (n : ℕ) : ∀ x ∈ closedBall (p n) (r n), ‖x‖ ≤ 2 / n := by
          intro y hy
          have h1 := norm_le_of_mem_closedBall hy
          simp [p, r] at h1
          nth_rewrite 2 [Complex.norm_def] at h1
          simp at h1
          grw [h1]
          grind
        by_cases h1 : ‖x‖ > 0
        · have ⟨m, hm⟩ := exists_nat_gt (2 / ‖x‖)
          exfalso
          specialize h (m + 2)
          have h2 := h x (mem_iInter.mp f m)
          have h3 : (m : ℝ) < (m + 2 : ℝ) := by simp
          have h4 := lt_trans hm h3
          field_simp at h2 h4
          simp at h2
          linarith
        · simp at h1
          trivial
      · rw [mem_iInter]
        intro i
        simp [p, r, f]
        rw [Real.sqrt_sq (by linarith)]
    rw [h1]
    symm
    apply union_eq_self_of_subset_right
    apply subset_iUnion_of_subset 0
    simp [p, r]

lemma H1isClosed : IsClosed H1 := by
  rw [H1_inter_Ear]
  apply isClosed_iInter
  intro m
  exact isClosed_Ear m

lemma H1isBounded : IsBounded H1 := by
  rw [H1_inter_Ear]
  exact Bornology.IsBounded.subset (isBounded_Ear 0) (iInter_subset Ear 0)

lemma H1isCompact : CompactSpace H1 := by
  rw [← isCompact_iff_compactSpace]
  exact isCompact_of_isClosed_isBounded H1isClosed H1isBounded
