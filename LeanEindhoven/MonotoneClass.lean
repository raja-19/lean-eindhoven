import Mathlib

open MeasureTheory
open MeasurableSpace

variable {α : Type*}

structure IsMonotoneClass (F : Set (Set α)) : Prop where
  iUnion_mem : ∀ (s : ℕ → Set α), (∀ i, s i ∈ F) → Monotone s → (⋃ i, s i) ∈ F
  iInter_mem : ∀ (s : ℕ → Set α), (∀ i, s i ∈ F) → Antitone s → (⋂ i, s i) ∈ F

inductive GenerateMonotoneClass (G : Set (Set α)) : Set α → Prop
  | base (s : Set α) (s_mem : s ∈ G) : (GenerateMonotoneClass G) s
  | iUnion (s : ℕ → Set α) (hs : ∀ i, GenerateMonotoneClass G (s i)) (hn : Monotone s) :
    GenerateMonotoneClass G (⋃ i, s i)
  | iInter (s : ℕ → Set α) (hs : ∀ i, GenerateMonotoneClass G (s i)) (hn : Antitone s) :
    GenerateMonotoneClass G (⋂ i, s i)

@[simp]
def generateMonotoneClass (G : Set (Set α)) : Set (Set α) := {s | GenerateMonotoneClass G s}

theorem IsMonotoneClass_generateMonotoneClass (G : Set (Set α)) :
    IsMonotoneClass (generateMonotoneClass G) where
  iUnion_mem := .iUnion
  iInter_mem := .iInter

theorem generateMonotoneClass_subset {G M : Set (Set α)}
    (hGM : G ⊆ M) (hM : IsMonotoneClass M) : (generateMonotoneClass G) ⊆ M := by
  intro s hs
  induction hs with
  | base t ht => exact hGM ht
  | iUnion t _ hm hn => exact hM.iUnion_mem t hn hm
  | iInter t _ hm hn => exact hM.iInter_mem t hn hm

theorem IsMonotoneClass.biUnion_mem
  {M : Set (Set α)} (hM : IsMonotoneClass M)
  {f : ℕ → Set α}
  (n : ℕ) (h1 : ∀ b, f b ∈ M) (hf : Monotone f)
  : (⋃ b ≤ n, f b) ∈ M := by
    set g := fun i ↦ if i ≤ n then f i else f n with hg
    have t : ⋃ i, g i = ⋃ b ≤ n, f b := by 
      ext x
      constructor 
      · intro hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨i, hi⟩ := hx
        unfold g at hi
        by_cases hle : i ≤ n
        · simp [hle] at hi
          rw [Set.mem_iUnion]
          use i
          simp [hle, hi]
        · simp [hle] at hi
          refine Set.mem_iUnion.mpr ⟨n, ?_⟩
          simp only [Std.le_refl, Set.iUnion_true, hi] 
      · intro hx   
        rw [Set.mem_iUnion] at hx 
        obtain ⟨i, hi⟩ := hx
        simp only [Set.mem_iUnion, exists_prop] at hi 
        rcases hi with ⟨hi,hx⟩
        rw [Set.mem_iUnion]
        use i
        simp only [g, hi]
        exact hx 
    rw [← t]
    refine hM.iUnion_mem g ?_ ?_
    · intro i
      rw [hg]
      simp only
      split_ifs
      · exact h1 i
      · exact h1 n
    · intros i j h_ij
      rw [hg]
      simp only
      split_ifs with ha hb
      · exact hf h_ij
      · exact hf ha
      · lia
      · exact Set.Subset.rfl


@[simp]
def generateSigmaAlgebra (G : Set (Set α)) : Set α → Prop :=
  GenerateMeasurable G

lemma Set.biUnion_le_mono (f : ℕ -> Set α) (i j : ℕ) (h_ij : i ≤ j) :
    ⋃ k ≤ i, f k ⊆ ⋃ k ≤ j, f k := by
  refine biUnion_subset_biUnion_left ?_
  intro l hl
  exact le_trans hl h_ij


def measurableSpace_of_monotoneClass {G : Set (Set α)} (h : IsSetAlgebra G)
  : MeasurableSpace α where
      MeasurableSet' := GenerateMonotoneClass G
      measurableSet_empty := .base ∅ h.empty_mem
      measurableSet_iUnion f hf := by
        set M := generateMonotoneClass G
        suffices ∀ n, (⋃ i ≤ n, f i) ∈ M by
          let g := fun i ↦ ⋃ j ≤ i, f j
          rw [← Set.biUnion_le_eq_iUnion]
          refine .iUnion g this (Set.biUnion_le_mono f)
        suffices ∀ A ∈ M, ∀ B ∈ M, A ∪ B ∈ M by
          intro n
          induction n with
            | zero =>
                simp only [nonpos_iff_eq_zero, Set.iUnion_iUnion_eq_left]
                exact hf 0
            | succ m ih =>
                rw [Set.biUnion_le_succ]
                exact this (⋃ i ≤ m, f i) ih (f (m + 1)) (hf (m + 1))
        intro A hA
        let M_A := {B ∈ M | A ∪ B ∈ M}
        have : M_A = M := by
          apply Set.Subset.antisymm
          · exact Set.sep_subset M fun x ↦ A ∪ x ∈ M
          · apply generateMonotoneClass_subset
            · intro g hg
              simp only [M_A]
              constructor
              · exact .base g hg
              · induction hA with
                  | base s hs =>
                      apply GenerateMonotoneClass.base
                      exact h.union_mem hs hg
                  | iUnion f hf hf_mono ih =>
                      rw [Set.iUnion_union]
                      apply GenerateMonotoneClass.iUnion
                      · exact ih
                      · exact Monotone.union hf_mono monotone_const
                  | iInter f hf hf_antitone ih =>
                      rw [Set.iInter_union]
                      apply GenerateMonotoneClass.iInter
                      · exact ih
                      · exact Antitone.union hf_antitone antitone_const
            · refine ⟨?_, ?_⟩
              · intro s hs hs_mono
                simp only [M_A]
                constructor
                · have : ∀ (i : ℕ), s i ∈ M := by
                    intro i
                    exact Set.mem_of_mem_inter_left (hs i)
                  exact GenerateMonotoneClass.iUnion s this hs_mono
                · let g := fun i ↦ A ∪ s i
                  rw [Set.union_iUnion]
                  refine GenerateMonotoneClass.iUnion g ?_ ?_
                  · exact fun i ↦ (hs i).right
                  · intro a b h_ab
                    exact Set.union_subset_union_right A (hs_mono h_ab)
              · intro s hs hs_antitone
                simp only [M_A]
                constructor
                · have : ∀ (i : ℕ), s i ∈ M := by
                    intro i
                    exact Set.mem_of_mem_inter_left (hs i)
                  exact GenerateMonotoneClass.iInter s this hs_antitone
                · let g := fun i ↦ A ∪ s i
                  rw [Set.union_iInter]
                  refine GenerateMonotoneClass.iInter g ?_ ?_
                  · exact fun i ↦ (hs i).right
                  · intro a b h_ab
                    exact Set.union_subset_union_right A (hs_antitone h_ab)
        intro B hB
        rw [← this] at hB
        simp [M_A] at hB
        exact hB.right
      measurableSet_compl := by sorry

theorem MeasurableSpace.GenerateMeasurable_eq_GenerateMonotoneClass
  (G : Set (Set α)) (h : IsSetAlgebra G) :
    measurableSpace_of_monotoneClass h = generateFrom G := by
      apply le_antisymm
      · intro s hs
        induction hs with
          | base t t_mem => exact .basic t t_mem
          | iUnion t ht hn ih => exact GenerateMeasurable.iUnion t ih
          | iInter t ht hn ih =>
              rw [Set.iInter_eq_compl_iUnion_compl]
              refine GenerateMeasurable.compl (⋃ i, (t i)ᶜ) ?_
              refine GenerateMeasurable.iUnion (fun i ↦  (t i)ᶜ) ?_
              intro i
              exact .compl (t i) (ih i)
      · apply MeasurableSpace.generateFrom_le
        intro t ht
        unfold MeasurableSet
        simp only [measurableSpace_of_monotoneClass]
        exact .base t ht
