-- This module serves as the root of the `MyProject` library.
-- Import modules here that should be built as part of the library.
import «MyProject».Basic
import Mathlib.Probability.Variance
import Mathlib.Data.Complex.Exponential

open MeasureTheory Filter Finset Real Complex

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory
section CharacteristicFunction

variable {t : ℝ}
variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {p : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable section

/-- Moment generating function of a real random variable `X`: `fun t => μ[exp(t*X)]`. -/
def mgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  μ[fun ω => rexp (t * X ω)]

/-- Cumulant generating function of a real random variable `X`: `fun t => log μ[exp(t*X)]`. -/
def cgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  log (mgf X μ t)

--change from complex number to function
def charfunc (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℂ :=
  μ[fun ω => cexp (Complex.I * t * ↑(X ω))]

-- theorem mgf_zero_fun : mgf 0 μ t = (μ Set.univ).toReal := by
--   simp only [mgf, Pi.zero_apply, mul_zero, Complex.exp_zero, integral_const, smul_eq_mul, mul_one]

lemma char_zero : charfunc X μ 0 = 1:= by
  simp [charfunc,Pi.zero_apply]

lemma bound : Complex.abs (charfunc X μ t) ≤ 1 := by
  -- refine toNNReal_le_one
  --use [abs_le_abs_re_add_abs_im]
  simp [charfunc]
  refine SimpleFunc.restrict_lintegral_eq_lintegral_restrict

theorem continuous_charfunc : Continuous (φ : charfunc X μ t) := by
sorry

theorem levy : (Isinstance S : Set charfunc) (n : ℕ → S):




theorem indepchar  (X Y : Ω → ℝ) : φ (X + Y) :=
  φ x φ y
