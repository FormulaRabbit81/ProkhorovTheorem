import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integrable
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ENNReal.Basic

noncomputable section

open MeasureTheory Filter Finset Asymptotics

open Set (indicator)

open scoped Topology MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} [mΩ: MeasurableSpace Ω] {μ : Measure Ω}
  {X : ℕ → Ω → ℝ} {Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y)
  --(hXY : IndepFun X Y P)

-- variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [mℕ : MeasurableSpace ℕ]{u : ℝ≥0 → Ω → ℕ}

-- theorem central_limit_theorem {μ : Measure Ω} {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X X μ) (h_ident_dist : ∀ i j, IdentDistrib (X i) (X j) μ μ)
--   (h_zero_mean : ∀ i, μ[ X i ] = 0)
--   (h_pos_finite_var : ∀ i, variance (X i) μ > 0) :
-- ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (NNReal.sqrt n) * (((∑ i ∈ range n, X i ω) / n) - (μ [X 0]))) atTop (𝓝 (gaussianPDFReal 0 (evariance (X 0) μ).toNNReal (X 0 ω))) :=
-- sorry

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {u : ℝ≥0 → Ω → ℕ} [MeasurableSpace ℝ]--[mℕ : MeasurableSpace ℕ]

theorem central_limit_theorem2 {μ : Measure Ω} {X : ℕ → Ω → ℝ} (h_indep : iIndepFun (fun _ => ℝ) u μ) (h_ident_dist : ∀ i j, IdentDistrib (X i) (X j) μ μ)
  (h_zero_mean : ∀ i, μ[ X i ] = 0)
  (h_pos_finite_var : ∀ i, variance (X i) μ > 0) :
∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (NNReal.sqrt n) * (((∑ i ∈ range n, X i ω) / n) - (μ [X 0]))) atTop (𝓝 (gaussianPDFReal 0 (evariance (X 0) μ).toNNReal (X 0 ω))) :=
sorry
