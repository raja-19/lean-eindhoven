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

theorem generateMonotoneClass_subset (G M : Set (Set α))
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
    let g := fun i ↦ if i ≤ n then f i else f n
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
    · sorry
    · sorry 


@[simp]
def generateSigmaAlgebra (G : Set (Set α)) : Set α → Prop :=
  GenerateMeasurable G

lemma Set.biUnion_le_mono (f : ℕ -> Set α) (i j : ℕ) (h_ij : i ≤ j) :
  ⋃ k ≤ i, f k ⊆ ⋃ k ≤ j, f k := by
    refine biUnion_subset_biUnion_left ?_
    intro l hl
    exact le_trans hl h_ij

theorem MeasurableSpace.GenerateMeasurable_eq_GenerateMonotoneClass (G : Set (Set α)) (h : IsSetAlgebra G) :
  generateMonotoneClass G = generateSigmaAlgebra G := by
    apply Set.Subset.antisymm
    · intro s hs
      simp only [generateSigmaAlgebra]
      induction hs with
        | base t t_mem => exact .basic t t_mem
        | iUnion t ht hn ih => exact .iUnion t ih
        | iInter t ht hn ih =>
            rw [Set.iInter_eq_compl_iUnion_compl]
            refine .compl (⋃ i, (t i)ᶜ) ?_
            refine .iUnion (fun i ↦  (t i)ᶜ) ?_
            intro i
            exact .compl (t i) (ih i)
    · intro s hs
      induction hs with
        | empty => exact .base ∅ h.empty_mem
        | basic u hu => exact .base u hu
        | iUnion f hf ih =>
            rw [← Set.biUnion_le_eq_iUnion]
            refine .iUnion (fun i ↦  ⋃ j ≤ i, f j) ?_ ?_
            · intro i
              apply GenerateMonotoneClass.iUnion
              · intro j
                exact ih j
              · sorry
            · intro i j h_ij
              simp only
              exact Set.biUnion_le_mono f i j h_ij
        | compl t ht ih => sorry
