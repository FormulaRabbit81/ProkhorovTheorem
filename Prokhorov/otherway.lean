--import Mathlib
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
--import Mathlib.Topology.MetricSpace.Embedding
--import Mathlib.Topology.MetricSpace.HilbertCube


set_option diagnostics true

set_option autoImplicit false

open TopologicalSpace MeasureTheory.ProbabilityMeasure Module--Analysis

variable {G : Type*} [PseudoMetricSpace G] [CompactSpace G] [SeparableSpace G]
  [MeasurableSpace G] [OpensMeasurableSpace G]

namespace MeasureTheory
noncomputable section
instance psm : PseudoMetricSpace (LevyProkhorov <| ProbabilityMeasure G) :=
  levyProkhorovDist_pseudoMetricSpace_probabilityMeasure


instance levyProkhorovCompact : CompactSpace (LevyProkhorov (ProbabilityMeasure G)) := by
  have hSeparability : SeparableSpace G := by infer_instance
  --let C := Dual G
  -- instance : NormedSpace ℝ C(G, ℝ) :=
  --   have E : CompleteSpace C(X, ℝ) ∧ NormedSpace ℝ C(X, ℝ) :=
  --   have hbanach : BanachSpace (ProbabilityMeasure X) := by
  sorry


--open scoped Interval MeasureTheory

open Topology Metric Filter Set ENNReal NNReal MeasureTheory.ProbabilityMeasure TopologicalSpace

def IsTightMeasureSet (S : Set (Measure G)) : Prop :=
  Tendsto (⨆ μ ∈ S, μ) (cocompact G).smallSets (𝓝 0)

variable (S : Set <| Measure G)
--Useful version
lemma IsTightMeasureSet_iff_exists_isCompact_measure_compl_le :
    IsTightMeasureSet S ↔ ∀ ε, 0 < ε → ∃ K : Set G, IsCompact K ∧ ∀ μ ∈ S, μ (Kᶜ) ≤ ε := by sorry

def TightProb (S : Set (ProbabilityMeasure G)) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set G, IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ ε

lemma Tightprob_iff_Tight {S : Set (ProbabilityMeasure G)} :
  TightProb S ↔ IsTightMeasureSet {((μ : ProbabilityMeasure G) : Measure G) | μ ∈ S} := by
  sorry
namespace MeasureTheory

open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {E : Type*} (μ : Measure ℕ := Measure.sum (fun i => (2⁻¹  : NNReal)^i • Measure.dirac i))
  {X : Type*} [MetricSpace X] [SeparableSpace X]




--def Y' : Set (ℕ → ℝ) := {f | ∀ n, f n ∈ Icc (0 : ℝ) 1}
def Y : Set ↥(Lp ℝ 1 μ) :=  (fun x => ⇑x)⁻¹' {f | ∀ n, f n ∈ Icc (0 : ℝ) 1} --Y'

lemma Compacty : CompactSpace Y := sorry


theorem homeo_to_compact_space {X : Type*} [MetricSpace X] [SeparableSpace X] :
    ∃ (T : X → Y), IsEmbedding T := by--Maybe build T explicitly first?
    -- obtain ⟨D, fD⟩ := TopologicalSpace.exists_countable_dense X
      sorry


lemma Tight_closure_if_tight (S : Set (ProbabilityMeasure G)):
  IsTightMeasureSet {((μ : ProbabilityMeasure G) : Measure G) | μ ∈ S} →
  TightProb (closure S) := by
  intro ht
  simp [TightProb]; intro ε hε
  rw [← Tightprob_iff_Tight, TightProb] at ht
  specialize ht ε hε
  obtain ⟨K,hc, htight⟩ := ht; use K
  constructor
  · simpa
  intro μ hμ


lemma Compact_if_tight {S : Set (ProbabilityMeasure G)}
(ht : IsTightMeasureSet {((μ : ProbabilityMeasure G) : Measure G) | μ ∈ S}) :
  IsCompact (closure S) := by
  by_cases hempty : IsEmpty (closure S)
  · simp_all only [isEmpty_coe_sort, isClosed_empty, IsClosed.closure_eq,
    finite_empty, Finite.isCompact]
  rw [not_isEmpty_iff] at hempty
  --rw [←Tightprob_iff_Tight, TightProb] at ht
  rw [@IsTightMeasureSet_iff_exists_isCompact_measure_compl_le] at ht
  --simp [IsCompact]
  obtain ⟨μ , hμ⟩ := hempty
  --choose! ε using ht
  have tightness (ε : ENNReal) (hε : ε > 0):
    ∃ (K : Set G), IsCompact K ∧ μ K ≥ 1 - ε := by
    specialize ht ε hε
    simp at ht




  --obtain ⟨D⟩ := ht
    sorry
