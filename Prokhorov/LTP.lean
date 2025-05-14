import Mathlib.MeasureTheory.Measure.NullMeasurable

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- `IsPartition` is a Prop that checks if a collection of sets
    partitions the space (pairwise disjoint and union is the whole space).-/
def IsPartition (B : ℕ → Set Ω) : Prop :=
  (∀ i j, i ≠ j → (Disjoint (B i) (B j))) ∧ (⋃ i, B i = ⊤)

/-! The law of total probability states that if `A` is a measurable set
and `B` is a partition of the Space, the measure of A is the sum of the
measure of A ∩ B i-/
theorem Law_Of_Total_Probability (A : Set Ω) (ha : MeasurableSet A) (B : ℕ → Set Ω)
  (hm: ∀ i, MeasurableSet <| B i) (hb : IsPartition B) : μ A = ∑' i : ℕ, μ (A ∩ B i) := by
  have A_union : A = ⋃ i, (A ∩ B i) := by
    rw [←Set.inter_iUnion,hb.right, Set.top_eq_univ, Set.inter_univ]
  nth_rewrite 1 [A_union]
  rw [measure_iUnion]
  · obtain ⟨hdisjoint,huniv⟩ := hb
    refine (pairwise_disjoint_on fun i ↦ A ∩ B i).mpr ?_
    intro m n hmn
    specialize hdisjoint m n (Nat.ne_of_lt hmn)
    refine Disjoint.inter_left' A ?_
    exact Disjoint.inter_right' A hdisjoint
  · exact fun i ↦ MeasurableSet.inter ha (hm i)
