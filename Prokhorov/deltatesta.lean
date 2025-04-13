import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
set_option maxHeartbeats 40000
set_option linter.style.longLine false
open Topology Metric Filter Set ENNReal NNReal MeasureTheory.ProbabilityMeasure TopologicalSpace

namespace MeasureTheory

open scoped Topology ENNReal NNReal BoundedContinuousFunction


variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
[OpensMeasurableSpace X] [SeparableSpace X]

end MeasureTheory

    -- have ignore : IsProbabilityMeasure (μ.toMeasure) := by
    --   exact instIsProbabilityMeasureToMeasure μ
    -- have ignoretoo : MeasurableSet (⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (1 / (↑m + 1)))) := by
    --   -- refine Finite.measurableSet_biUnion ?_ ?_
    --   -- · simp
    --   --   refine finite_def.mpr ?_
    --   --   refine exists_true_iff_nonempty.mp ?_
    --   sorry
