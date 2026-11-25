module

import Mathlib

open Metric Set Relation Complex

noncomputable def S (p : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  { (r * Real.cos (2*Real.pi*t) + p.1, r * Real.sin (2*Real.pi*t) + p.2) | t ∈ [0,1] }

noncomputable def H11 : Set (ℝ × ℝ) := ⋃ n ≥ 1, (S (n⁻¹, 0) n⁻¹)

noncomputable def H12 : Set (ℝ × ℝ) := ⋃ n ≥ 1, sphere (1 / n, 0) (1 / n)

noncomputable def H13 : Set ℂ := ⋃ n, sphere (⟨1 / n, 0⟩ : ℂ) (1 / n)

--- Subspace definition of Hawaiian Earring

noncomputable def p (n : ℕ) : ℂ := ⟨1 / n, 0⟩
noncomputable def r (n : ℕ) : ℝ := 1 / n

noncomputable def H1 : Set ℂ := ⋃ n, sphere (p n) (r n)

---

--- Suspension definition of Hawaiian Earring

noncomputable def X : Set ℝ := { 1 / n | n : ℕ }
@[reducible]
def Y := X × (Icc (0 : ℝ) 1)


-- Relation with collapsing a set into one point. Could be added to mathlib
def RelOnSet {X : Type} (D : Set X) : X → X → Prop := ReflGen (fun x y ↦ (x ∈ D ∧ y ∈ D))

lemma equivalence_relOnSet {X : Type} (D : Set X) : Equivalence (RelOnSet D) := by
  unfold RelOnSet
  constructor <;> grind

-- We can also add suspension in mathlib

def D : Set Y := { y : Y | y.1 = (0 : ℝ) ∨ y.2 = 0 ∨ y.2 = 1 }

def RelY (x y : Y) : Prop := (x ∈ D ∧ y ∈ D) ∨ (x = y)
-- Alternative way to define the equivalence relation we want, by taking reflexive closure
def RelY2 := ReflGen (fun x y ↦ (x ∈ D ∧ y ∈ D))

#check RelY2

lemma RelY.equivalence : Equivalence RelY where
  refl := by
    unfold RelY
    simp
  symm := by
    unfold RelY
    grind
  trans := by
    unfold RelY
    grind

lemma RelY2.equivalence : Equivalence RelY2 where
  refl := by
    unfold RelY2
    exact fun x ↦ ReflGen.refl
  symm := by
    sorry
  trans := by
    sorry

instance setoidY : Setoid Y where
  r := RelY
  iseqv := RelY.equivalence

@[reducible]
def SY := Quotient setoidY

---

example : TopologicalSpace SY := inferInstance

example : T2Space (ℝ × ℝ) := inferInstance
#synth T2Space (ℝ × ℝ)

-- H1 is Hausdorff 
lemma H1isHausdorff : T2Space H1 := inferInstance
