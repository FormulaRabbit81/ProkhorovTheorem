import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.IntervalIntegral -- Assuming relevant modules are available


open MeasureTheory Filter Finset Asymptotics
open scoped Topology BigOperators MeasureTheory ProbabilityTheory ENNReal NNReal
namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def is_partition (B : ℕ → Set Ω) : Prop :=
  (∀ i j, i ≠ j → (Disjoint (B i) (B j))) ∧ (⋃ i, B i = ⊤)

omit [IsProbabilityMeasure μ] in
theorem ltp (A : Set Ω) (ha : MeasurableSet A) (B : ℕ → Set Ω) (hm: ∀ i, MeasurableSet $ B i)(hb : is_partition B) : μ A = ∑' i : ℕ, μ (A ∩ B i) := by
  -- ℙ A = ∑ i, ℙ (A ∩ B i) :=
  have A_union : A = ⋃ i, (A ∩ B i) := by
    --refine Set.ext ?h
    rw [←Set.inter_iUnion]
    rw [hb.right]
    rw [Set.top_eq_univ, Set.inter_univ]
  --conv_lhs => rw [A_union]
  nth_rewrite 1 [A_union]
  rw [measure_iUnion]
  intro i j h
  rw [Function.onFun]
  have := hb.left i j h
  --rw [Disjoint]
  --rw [Set.disjoint_iff_inter_eq_empty] at this ⊢
  rw [Disjoint]
  intro x hx hx'
  apply this
  apply le_trans hx
  simp only [Set.le_eq_subset, Set.inter_subset_right]
  apply le_trans hx'
  simp only [Set.le_eq_subset, Set.inter_subset_right]
  intro i
  specialize hm i
  apply MeasurableSet.inter ha hm
