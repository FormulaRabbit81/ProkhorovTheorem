import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

open Topology Metric Filter Set ENNReal NNReal ProbabilityMeasure TopologicalSpace

namespace MeasureTheory


variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [SeparableSpace Ω]
[OpensMeasurableSpace Ω]
variable {μ : ℕ → Set Ω → ℝ}


variable (S : Set (ProbabilityMeasure Ω))


lemma claim5point2 (U : ℕ → Set Ω) (O : ∀ i, IsOpen (U i))
    (hcomp: IsCompact (closure S)) (ε : ℝ≥0) :
    ∃ (k : ℕ), ∀ μ ∈ S, μ (⋃ (i ≤ k), U i) > 1 - ε := by
  by_contra! nh
  choose μ hμ hμε using nh

  obtain ⟨μnew, hμtwo, sub, tub, bub⟩ := hcomp.isSeqCompact (fun n =>  subset_closure <| hμ n)
  have thing n := calc
    μnew (⋃ (i ≤ n), U i)
    _ ≤ liminf (fun k => μ (sub k) (⋃ (i ≤ n), U i)) atTop := by
      sorry
    _ ≤ liminf (fun k => μ (sub k) (⋃ (i ≤ k), U i)) atTop := by
      sorry
    _ ≤ 1 - ε := by
      apply Filter.liminf_le_of_le
      · sorry
      · simp only [eventually_atTop, ge_iff_le, forall_exists_index]
        intros b c h
        apply?
  sorry
