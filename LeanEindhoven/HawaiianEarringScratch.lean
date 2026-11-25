module

import Mathlib

open Metric Set Relation Complex Bornology Real

/-- Subspace definition of Hawaiian Earring -/
noncomputable def p (n : ℕ) : ℂ := ⟨1 / n, 0⟩
noncomputable def r (n : ℕ) : ℝ := 1 / n
noncomputable def S (n : ℕ) : Set ℂ := sphere (p n) (r n)
noncomputable def CB (n : ℕ) : Set ℂ := closedBall (p n) (r n)
noncomputable def H1 : Set ℂ := ⋃ n, S n

noncomputable def Ear (m : ℕ) : Set ℂ :=
  (⋃ n : Fin (m + 1), S n) ∪ CB (m + 1)

lemma isClosed_Ear (m : ℕ) : IsClosed (Ear m) :=
  IsClosed.union (isClosed_iUnion_of_finite (fun _ ↦ isClosed_sphere)) isClosed_closedBall

lemma isBounded_Ear (m : ℕ) : IsBounded (Ear m) :=
  IsBounded.union (isBounded_iUnion.mpr (fun _ ↦ isBounded_sphere)) isBounded_closedBall

lemma isCompact_Ear (m : ℕ) : CompactSpace (Ear m) := by
  rw [← isCompact_iff_compactSpace]
  exact isCompact_of_isClosed_isBounded (isClosed_Ear m) (isBounded_Ear m)


lemma Ear_union_H1_closedBall (m : ℕ) : Ear m = H1 ∪ CB (m + 1) := by
  unfold H1
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases h with
    | inl h1 =>
      obtain ⟨n, hn⟩ := mem_iUnion.mp h1
      left
      rw [Set.mem_iUnion]
      use n
    | inr h1 => exact Or.inr h1
  · cases h with
    | inl h1 =>
      obtain ⟨n, hn⟩ := mem_iUnion.mp h1
      by_cases! h : (n ≥ m + 1)
      · right
        have h2 : r n + dist (p n) (p (m + 1)) ≤ r (m + 1) := by
          simp [r, p]
          rw [sub_sq_comm, sqrt_sq]
          · linarith
          · rw [sub_nonneg]
            exact inv_anti₀ (by linarith) (by exact_mod_cast h)
        apply closedBall_subset_closedBall' h2
        exact sphere_subset_closedBall hn
      · left
        rw [Set.mem_iUnion]
        use Fin.mk n h
    | inr h1 => exact Or.inr h1

lemma H1_inter_Ear : H1 = ⋂ n, Ear n := by
    simp only [Ear_union_H1_closedBall]
    rw [← union_iInter]
    have h1 : ⋂ i, CB (i + 1) = {⟨0,0⟩} := by
      ext x
      refine ⟨fun f ↦ ?_, fun f ↦ ?_⟩
      <;> rw [mem_singleton_iff] at *
      · have h (n : ℕ) : ∀ x ∈ CB n, ‖x‖ ≤ 2 / n := by
          intro y hy
          have h1 := norm_le_of_mem_closedBall hy
          simp only [p, r, one_div] at h1
          nth_rewrite 2 [Complex.norm_def] at h1
          simp at h1
          grw [h1]
          grind
        by_cases h1 : ‖x‖ > 0
        · have ⟨m, hm⟩ := exists_nat_gt (2 / ‖x‖)
          exfalso
          specialize h (m + 1)
          have h2 := h x (mem_iInter.mp f m)
          have h3 : (m : ℝ) < (m + 1 : ℝ) := by simp
          have h4 := lt_trans hm h3
          field_simp at h2 h4
          simp at h2
          linarith
        · simp at h1
          trivial
      · rw [mem_iInter]
        intro i
        simp [CB, p, r, f]
        rw [sqrt_sq (by linarith)]
    rw [h1]
    symm
    apply union_eq_self_of_subset_right
    apply subset_iUnion_of_subset 0
    simp [S, p, r]

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

-- Generalize IsPathConnected.union to infinite number of sets. Then this follows directly.

lemma IsPathConnected.iUnion {ι α : Type*} [hι : Nonempty ι] [TopologicalSpace α] (f : ι → Set α)
    (hpc : ∀ i, IsPathConnected (f i)) (hne : Nonempty (⋂ i, f i)) :
    IsPathConnected (⋃ i, f i) := by
  obtain ⟨x, hx⟩ := hne
  use x
  constructor
  · rw [Set.mem_iUnion]
    obtain ⟨i⟩ := hι
    use i
    rw [Set.mem_iInter] at hx
    exact hx i
  · intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, hi⟩ := hy
    refine JoinedIn.mono ?_ (subset_iUnion f i)
    rw [Set.mem_iInter] at hx
    refine (hpc i).joinedIn x (hx i) y hi

-- H1 is PathConnected
lemma H1isPathConnected : IsPathConnected H1 := by
  apply IsPathConnected.iUnion
  · intro i
    apply isPathConnected_sphere
    <;> simp [r]
  · use 0
    rw [Set.mem_iInter]
    intro i
    rw [S, p, r, mem_sphere_iff_norm, ← Complex.ofReal]
    simp
