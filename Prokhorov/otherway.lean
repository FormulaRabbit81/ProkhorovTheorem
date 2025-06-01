import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

set_option diagnostics true

set_option autoImplicit false

open TopologicalSpace MeasureTheory.ProbabilityMeasure Module--Analysis

variable {G : Type*} [PseudoMetricSpace G] [CompactSpace G] [SeparableSpace G]
  [MeasurableSpace G] [OpensMeasurableSpace G]

namespace MeasureTheory
noncomputable section
instance psm : PseudoMetricSpace (LevyProkhorov <| ProbabilityMeasure G) :=
  levyProkhorovDist_pseudoMetricSpace_probabilityMeasure

#synth PseudoMetrizableSpace <| ProbabilityMeasure G

instance levyProkhorovCompact : CompactSpace (LevyProkhorov (ProbabilityMeasure G)) := by
  have hSeparability : SeparableSpace G := by infer_instance
  let C := Dual G

--   refine { isCompact_univ := ?_ }
--   --have C
--   instance : NormedAddCommGroup C(X, ℝ) := by
--     refine AddGroupNorm.toNormedAddCommGroup ?_
--     use fun x ↦ sSup (Set.range (fun x ↦ ‖x‖)) --fun s ↦ ‖s‖


instance : NormedSpace ℝ C(G, ℝ) :=
  have E : CompleteSpace C(X, ℝ) ∧ NormedSpace ℝ C(X, ℝ) :=
  have hbanach : BanachSpace (ProbabilityMeasure X) := by


lemma fivepoint3 {MeasurableSpace X} (MetricSpace X)  (h : IsCompact X) : IsCompact (PseudoMetricSpace (LevyProkhorov (ProbabilityMeasure X))) (ha : inferInstance TopologicalSpace (LevyProkhorov (ProbabilityMeasure X))) := by
  sorry
