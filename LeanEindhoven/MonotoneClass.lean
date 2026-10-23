import Mathlib
open MeasureTheory
namespace MonotoneClass

variable {α : Type*}

structure IsMonotoneClass (F : Set (Set α)) : Prop where
  iUnion_mem : ∀ (s : ℕ → Set α), (∀ i, s i ∈ F) → Monotone s → (⋃ i, s i) ∈ F
  iInter_mem : ∀ (s : ℕ → Set α), (∀ i, s i ∈ F) → Antitone s → (⋂ i, s i) ∈ F

inductive GenerateMonotoneClass (G : Set (Set α)) : Set α → Prop
  | base (s : Set α) (s_mem : s ∈ G) : (GenerateMonotoneClass G) s
  | iUnion (s : ℕ → Set α) (hs : ∀ i, GenerateMonotoneClass G (s i)) 
    (hn : Monotone s) : GenerateMonotoneClass G (⋃ i, s i)
  | iInter (s : ℕ → Set α) (hs : ∀ i, GenerateMonotoneClass G (s i)) 
    (hn : Antitone s) : GenerateMonotoneClass G (⋂ i, s i)

@[simp]
def generateMonotoneClass (G : Set (Set α)) : Set (Set α) := {s | GenerateMonotoneClass G s}

theorem IsMonotoneClass_generateMonotoneClass (G : Set (Set α)) : 
    IsMonotoneClass (generateMonotoneClass G) where
  iUnion_mem := .iUnion 
  iInter_mem := .iInter

theorem generateMonotoneClass_subset (G M : Set (Set α)) 
    (hGM : G ⊆ M) (hM : IsMonotoneClass M) : (generateMonotoneClass G) ⊆ M := by
  rw [Set.subset_def]
  intro s hs
  rw [generateMonotoneClass] at hs
  rw [Set.ofPred] at hs
  induction hs with 
  | base t ht=> 
    exact hGM ht  
  | iUnion t ht hm hn => 
    exact hM.iUnion_mem t hn hm 
  | iInter t ht hm hn => 
    exact hM.iInter_mem t hn hm 

theorem MeasurableSpace.GenerateMeasurable_eq_GenerateMonotoneClass (G : Set (Set α)) : 
    MeasurableSpace.GenerateMeasurable G = GenerateMonotoneClass G := by
      funext s
      rw [← iff_eq_eq]
      constructor
      · sorry
      · sorry










