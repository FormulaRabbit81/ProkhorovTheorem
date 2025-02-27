import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.IntervalIntegral -- Assuming relevant modules are available
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.MeasureTheory.Measure.Portmanteau
--set_option diagnostics true

open Topology Metric Filter Set ENNReal NNReal ProbabilityMeasure TopologicalSpace

namespace MeasureTheory

open scoped Topology ENNReal NNReal BoundedContinuousFunction


variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] -- consider changing this to EMetric later
[OpensMeasurableSpace Ω] [SeparableSpace Ω] --[∀ i, μ i : Measure Ω] {P : MeasurableSpace Ω}
variable {μ : ℕ → Set Ω → ℝ}




noncomputable section

--def compactsetofmeasures := {X : Set (ProbabilityMeasure Ω) // IsCompact X}




-- Levy Prok α is syn
-- α is Foo, ofSyn is .equiv


variable (S : Set (ProbabilityMeasure Ω)) --(S : Set (LevyProkhorov (ProbabilityMeasure Ω))) --

abbrev P := LevyProkhorov.equiv (ProbabilityMeasure Ω)

abbrev T := P⁻¹' S


variable [OpensMeasurableSpace Ω] in

theorem tendsto_iff_forall_integral_tendsto_prok {γ : Type*} {F : Filter γ}
    {μs : γ → LevyProkhorov (ProbabilityMeasure Ω)} {μ : LevyProkhorov (ProbabilityMeasure Ω)} {μnorm : ProbabilityMeasure Ω}:
    Tendsto μs F (𝓝 μ) ↔ Tendsto (fun n => P (μs n)) F (𝓝 (P μ)) := by sorry
  --     ∀ f : Ω →ᵇ ℝ,
  --       Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  -- rw [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  -- rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  -- rfl

lemma claim5point2 (U : ℕ → Set Ω) (O : ∀ i, IsOpen (U i)) --(T : Set (LevyProkhorov (ProbabilityMeasure Ω)))
    (hcomp: IsCompact (closure S)) (ε : ℝ≥0) (Cov : univ = ⋃ i, U i):
    ∃ (k : ℕ), ∀ μ ∈ S, μ (⋃ (i ≤ k), U i) > 1 - ε := by
  by_contra! nh
  choose μ hμ hμε using nh

  --exact hcomp.mem_of_is_closed (IsClosed.closure hcomp.is_closed)
  obtain ⟨μnew, hμ, sub, tub, bub⟩ := hcomp.isSeqCompact (fun n =>  subset_closure <| hμ n)
  have thing n := calc
    P μnew (⋃ (i ≤ n), U i)
    _ = liminf (fun k => (μ (sub k)) (⋃ (i ≤ n), U i)) atTop := by
      rw [Tendsto.liminf_eq]
      --rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at bub
      sorry
      --levyProkhorov_eq_convergenceInDistribution --homeomorph_probabilityMeasure_levyProkhorov
    _ ≤ liminf (fun k => P (μ (sub k)) (⋃ (i ≤ k), U i)) atTop := by sorry
    _ ≤ 1 - ε := sorry

  have cdiction : Tendsto (fun n => P μnew (⋃ i ≤ n, U i)) atTop (𝓝 1) := by sorry
    --(∀ n, P μnew (⋃ (i ≤ n), U i)) ≤ liminf (fun k => P (μ (sub k)) (⋃ (i ≤ n), U i)) atTop := by exact P.liminf_le_liminf hμ
      -- have conv :
  --simp at nh --gt_iff_lt, not_exists, not_forall, Classical.not_imp, not_lt] at nh
  --have h : ∃ μ ∈ (closure S), ∃ (m : ℕ → LevyProkhorov (ProbabilityMeasure Ω)), (∀ i : ℕ, m i ∈ closure S) ∧ Tendsto m atTop (𝓝 μ) := by
  --exact IsCompact.isSeqCompact c
  sorry





lemma fivepoint3 (MetricSpace X) (h : IsCompact X) (A : ProbabilityMeasure X) (B := LevyProkhorov.equiv (ProbabilityMeasure X)) : IsCompact B := by
  sorry


-- Definition taken from Rémy's PR number #21955
def IsTightFamily (S : Set (Measure Ω)) : Prop :=
  ∀ ε, 0 < ε → ∃ (K_ε : Set Ω), ∀ μ ∈ S, μ K_εᶜ < ε ∧ IsCompact K_ε


def IsRelativelyCompact (S : Set (Measure Ω)) [PseudoMetricSpace (Measure Ω)] : Prop :=
  IsCompact (closure S)

theorem Prokhorov (G : Set (Measure Ω)) [PseudoMetricSpace (Measure Ω)]:
   (IsTightFamily G) ↔ (IsRelativelyCompact G) := by
   sorry

end section
-- Change Omega to X
