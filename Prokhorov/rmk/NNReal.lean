/-
Copyright (c) 2025 Yoh Tanimioto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/

import Mathlib

/-!
#  Riesz–Markov–Kakutani representation theorem for `ℝ≥0`

This file proves the Riesz-Markov-Kakutani representation theorem on a locally compact
T2 space `X` for `ℝ≥0`-linear functionals `Λ`.

## Implementation notes

The proof depends on the version of the theorem for `ℝ`-linear functional Λ because in a standard
proof one has to prove the inequalities by `le_antisymm`, yet for `C_c(X, ℝ≥0)` there is no `Neg`.
Here we prove the result by writing `ℝ≥0`-linear `Λ` in terms of `ℝ`-linear `toRealLinear Λ` and by
reducing the statement to the `ℝ`-version of the theorem.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

section Aux
variable {X : Type*} [TopologicalSpace X]
/-- A variation of Urysohn's lemma. In a Hausdorff locally compact space, for a compact set `K`
contained in an open set `V`, there exists a compactly supported continuous function `f` such that
`0 ≤ f ≤ 1`, `f = 1` on K and the support of `f` is contained in `V`. -/
lemma exists_continuous_one_of_compact_subset_open [T2Space X] [LocallyCompactSpace X]
    {K V : Set X} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ f : C(X, ℝ), Set.EqOn (⇑f) 1 K ∧ IsCompact (tsupport ⇑f)
    ∧ tsupport ⇑f ⊆ V ∧ ∀ (x : X), f x ∈ Set.Icc 0 1 := by
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_tsupport_one_of_isOpen_isClosed hU1 hU4 hK.isClosed hU2
  have : tsupport f ⊆ closure U := hf1.trans subset_closure
  exact ⟨f, hf2, hU4.of_isClosed_subset isClosed_closure this, this.trans hU3, hf3⟩

open Set Filter ENNReal NNReal TopologicalSpace
open scoped symmDiff Topology

namespace MeasureTheory

namespace Measure

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p q : Set α → Prop} {U : Set α}
  {ε : ℝ≥0∞}

namespace InnerRegularWRT

theorem eq_on_q_of_eq_on_p {ν : Measure α} (hμ : μ.InnerRegularWRT p q) (hν : ν.InnerRegularWRT p q)
    (hμν : ∀ U, p U → μ U = ν U) (U : Set α) (hU : q U) : μ U = ν U := by
  rw [hμ.measure_eq_iSup hU, hν.measure_eq_iSup hU]
  congr! 4 with t _ ht2
  exact hμν t ht2

end InnerRegularWRT

variable [TopologicalSpace α]
namespace OuterRegular
/-- Outer regular measures are determined by values on open sets. -/
theorem eq_of_eq_on_isOpen {ν : Measure α} [OuterRegular μ] [OuterRegular ν]
    (hμν : ∀ U, IsOpen U → μ U = ν U) : μ = ν := by
  ext s ms
  rw [Set.measure_eq_iInf_isOpen, Set.measure_eq_iInf_isOpen]
  congr! 4 with t _ ht2
  exact hμν t ht2

end OuterRegular

end Measure
end MeasureTheory

end Aux

section Realss

open scoped ENNReal
open CompactlySupported CompactlySupportedContinuousMap Filter Function Set Topology
  TopologicalSpace MeasureTheory

/-- Compactly supported continuous functions are integrable. -/
lemma CompactlySupportedContinuousMap.integrable {X E : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [NormedAddCommGroup E] (f : C_c(X, E))
    {μ : Measure X} [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ] :
    Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

namespace RealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
variable (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)

/-- The Riesz measure induced by a positive linear functional on `C_c(X, ℝ)` is regular. -/
instance rieszMeasure_regular : (rieszMeasure Λ).Regular :=
  (rieszContent _).regular

section integralPositiveLinearMap

/-! We show that `RealRMK.rieszMeasure` is a bijection between positive linear functionals on
`C_c(X, ℝ)` and regular measures with inverse `RealRMK.integralPositiveLinearMap`. -/

-- Note: the assumption `IsFiniteMeasureOnCompacts μ` cannot be removed. For example, if
-- `μ` is infinite on any nonempty set and `ν = 0`, then the hypothese are satisfied.
lemma compare_measure_of_compact_sets {μ ν : Measure X} [ν.OuterRegular]
    [IsFiniteMeasureOnCompacts ν] [IsFiniteMeasureOnCompacts μ]
    (hμν : ∀ (f : C_c(X, ℝ)), ∫ (x : X), f x ∂μ ≤ ∫ (x : X), f x ∂ν)
    ⦃K : Set X⦄ (hK : IsCompact K) : μ K ≤ ν K := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hν ↦ ?_
  have hνK : ν K ≠ ⊤ := hν.ne
  have hμK : μ K ≠ ⊤ := hK.measure_lt_top.ne
  obtain ⟨V, pV1, pV2, pV3⟩ : ∃ V ⊇ K, IsOpen V ∧ ν V ≤ ν K + ε := by
    exact Set.exists_isOpen_le_add K ν (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
  suffices  (μ K).toReal ≤ (ν K).toReal + ε by
    rw [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
    all_goals finiteness
  have VltTop : ν V < ⊤ := pV3.trans_lt <| by finiteness
  obtain ⟨f, pf1, pf2, pf3⟩ :
      ∃ f : C_c(X, ℝ), Set.EqOn (⇑f) 1 K ∧ tsupport ⇑f ⊆ V ∧ ∀ (x : X), f x ∈ Set.Icc 0 1 := by
    obtain ⟨f, hf1, hf2, hf3⟩ := exists_continuous_one_of_compact_subset_open hK pV2 pV1
    exact ⟨⟨f, hasCompactSupport_def.mpr hf2⟩, hf1, hf3⟩
  have hfV (x : X) : f x ≤ V.indicator 1 x := by
    by_cases hx : x ∈ tsupport f
    · simp [(pf2 hx), (pf3 x).2]
    · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
  have hfK (x : X) : K.indicator 1 x ≤ f x := by
    by_cases hx : x ∈ K
    · simp [hx, pf1 hx]
    · simp [hx, (pf3 x).1]
  calc
    (μ K).toReal = ∫ (x : X), K.indicator 1 x ∂μ := by
      rw [integral_indicator_one hK.measurableSet, measureReal_def]
    _ ≤ ∫ (x : X), (f x : ℝ) ∂μ := by
      refine integral_mono ?_ f.integrable hfK
      exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
    _ ≤ ∫ (x : X), (f x : ℝ) ∂ν := hμν f
    _ ≤ ∫ (x : X), V.indicator 1 x ∂ν := by
      refine integral_mono f.integrable ?_ hfV
      exact IntegrableOn.integrable_indicator integrableOn_const pV2.measurableSet
    _ ≤ (ν K).toReal + ↑ε := by
      rwa [integral_indicator_one pV2.measurableSet, measureReal_def,
        ← ENNReal.coe_toReal, ← ENNReal.toReal_add, ENNReal.toReal_le_toReal]
      all_goals finiteness

/-- If two regular measures give the same integral for every function in `C_c(X, ℝ)`,
then they are equal. -/
theorem _root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported {μ ν : Measure X}
    [μ.Regular] [ν.Regular] (hμν : ∀ (f : C_c(X, ℝ)), ∫ (x : X), f x ∂μ = ∫ (x : X), f x ∂ν) :
    μ = ν := by
  apply Measure.OuterRegular.eq_of_eq_on_isOpen
  apply Measure.InnerRegularWRT.eq_on_q_of_eq_on_p Measure.Regular.innerRegular
    Measure.Regular.innerRegular
  intro K hK
  apply le_antisymm
  · exact compare_measure_of_compact_sets (fun f ↦ (hμν f).le) hK
  · exact compare_measure_of_compact_sets (fun f ↦ (hμν f).ge) hK

/-- Integral as a positive linear functional on `C_c(X, ℝ)`. -/
@[simps!]
noncomputable def integralPositiveLinearMap (μ : Measure X) [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts μ] : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun f := ∫ (x : X), f x ∂μ,
      map_add' f g := integral_add' f.integrable g.integrable
      map_smul' c f := integral_smul c f }
    fun _ ↦ integral_nonneg

/-- Two regular measures are equal iff they induce the same positive linear functional
on `C_c(X, ℝ)`. -/
theorem integralPositiveLinearMap_inj {μ ν : Measure X} [μ.Regular] [ν.Regular] :
    integralPositiveLinearMap μ = integralPositiveLinearMap ν ↔ μ = ν :=
  ⟨fun hμν ↦ Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ congr($hμν f),
    fun _ ↦ by congr⟩

/-- Every regular measure is induced by a positive linear functional on `C_c(X, ℝ)`.
That is, `RealRMK.rieszMeasure` is a surjective function onto regular measures. -/
@[simp]
theorem rieszMeasure_integralPositiveLinearMap {μ : Measure X} [μ.Regular] :
    rieszMeasure (integralPositiveLinearMap μ) = μ :=
  Measure.ext_of_integral_eq_on_compactlySupported (by simp [integral_rieszMeasure])

@[simp]
theorem integralPositiveLinearMap_rieszMeasure :
    integralPositiveLinearMap (rieszMeasure Λ) = Λ := by ext; simp [integral_rieszMeasure]

end integralPositiveLinearMap

end RealRMK
end Realss

open scoped NNReal

open CompactlySupported CompactlySupportedContinuousMap MeasureTheory

namespace NNRealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
variable (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)
-- /-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
-- the (Bochner) integral of `f` (as a `ℝ`-valued function) with respect to the `rieszMeasure`
-- associated to `Λ` is equal to `Λ f`. -/
-- @[simp]
-- theorem integral_rieszMeasure (f : C_c(X, ℝ≥0)) :
    --∫ (x : X), (f x : ℝ) ∂(rieszMeasure Λ) = Λ f := by
--   rw [← eq_toRealPositiveLinear_toReal Λ f,
--       ← RealRMK.integral_rieszMeasure (toRealPositiveLinear Λ) f.toReal]
--   simp [RealRMK.rieszMeasure, NNRealRMK.rieszMeasure]

-- /-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
-- the (lower) Lebesgue integral of `f` with respect to the `rieszMeasure` associated to `Λ` is
    --equal
-- to `Λ f`. -/
-- @[simp]
-- theorem lintegral_rieszMeasure (f : C_c(X, ℝ≥0)) : ∫⁻ (x : X), f x ∂(rieszMeasure Λ) = Λ f := by
--   rw [lintegral_coe_eq_integral, ← ENNReal.ofNNReal_toNNReal]
--   · rw [ENNReal.coe_inj, Real.toNNReal_of_nonneg (MeasureTheory.integ
--ral_nonneg (by intro a; simp)),
--        NNReal.eq_iff, NNReal.coe_mk]
--     exact integral_rieszMeasure Λ f
--   rw [rieszMeasure]
--   exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
--     (HasCompactSupport.comp_left f.hasCompactSupport rfl)

/-- The Riesz measure induced by a linear functional on `C_c(X, ℝ≥0)` is regular. -/
instance rieszMeasure_regular (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) : (rieszMeasure Λ).Regular :=
  (rieszContent Λ).regular

section integralLinearMap

/-! We show that `NNRealRMK.rieszMeasure` is a bijection between linear functionals on `C_c(X, ℝ≥0)`
and regular measures with inverse `NNRealRMK.integralLinearMap`. -/

/-- If two regular measures give the same integral for every function in `C_c(X, ℝ≥0)`, then they
are equal. -/
theorem _root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_nnreal
    {μ ν : Measure X} [μ.Regular] [ν.Regular]
    (hμν : ∀ (f : C_c(X, ℝ≥0)), ∫ (x : X), (f x : ℝ) ∂μ = ∫ (x : X), (f x : ℝ) ∂ν) : μ = ν := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    repeat rw [integral_eq_integral_pos_part_sub_integral_neg_part f.integrable]
    erw [hμν f.nnrealPart, hμν (-f).nnrealPart]
    rfl

/-- Integration as a positive linear functional on `C_c(X, ℝ≥0)`. -/
-- Note: the default generated `simps` lemma uses `Subtype.val` instead of `NNReal.toReal`.
@[simps! apply]
noncomputable def integralLinearMap (μ : Measure X) [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts μ] :
    C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 :=
    CompactlySupportedContinuousMap.toNNRealLinear (RealRMK.integralPositiveLinearMap μ)

/-- If two regular measures induce the same linear functional on `C_c(X, ℝ≥0)`, then they are
equal. -/
@[simp]
theorem integralLinearMap_inj {μ ν : Measure X} [μ.Regular] [ν.Regular] :
    integralLinearMap μ = integralLinearMap ν ↔ μ = ν :=
  ⟨fun hμν ↦ Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f ↦
      by simpa using congr(($hμν f).toReal), fun _ ↦ by congr⟩

/-- Every regular measure is induced by a positive linear functional on `C_c(X, ℝ≥0)`.
That is, `NNRealRMK.rieszMeasure` is a surjective function onto regular measures. -/
@[simp]
theorem rieszMeasure_integralLinearMap {μ : Measure X} [μ.Regular] :
    rieszMeasure (integralLinearMap μ) = μ :=
  Measure.ext_of_integral_eq_on_compactlySupported_nnreal (by simp [integral_rieszMeasure])

@[simp]
theorem integralLinearMap_rieszMeasure :
    integralLinearMap (rieszMeasure Λ) = Λ := by ext; simp [integral_rieszMeasure]

end integralLinearMap

end NNRealRMK

open MeasureTheory NormedSpace WeakDual CompactlySupported CompactlySupportedContinuousMap
  Filter

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [CompactSpace X] [BorelSpace X]

noncomputable section

instance : PseudoMetricSpace (LevyProkhorov (ProbabilityMeasure X)) :=
  levyProkhorovDist_pseudoMetricSpace_probabilityMeasure

/-
S ⊆ P(X) is relatively compact iff tight.
Let X be a compact metric space. P(X) is a compact metric space.
-/

instance : CompactSpace (LevyProkhorov (ProbabilityMeasure X)) := by
  let Φ := { φ : WeakDual ℝ C(X, ℝ) | ‖toStrongDual φ‖ ≤ 1
    ∧ φ ⟨fun x ↦ 1, continuous_const⟩ = 1 ∧ ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ φ f }
  have hΦ1 : CompactSpace Φ := by
    let A := { φ : WeakDual ℝ C(X, ℝ) | ‖toStrongDual φ‖ ≤ 1 }
    have hA1 : IsCompact A := by
      have : A = ⇑toStrongDual ⁻¹' Metric.closedBall 0 1 := by
        ext x
        simp [A]
        sorry --Note simp fully proves this given #28601
      simp only [this]; exact isCompact_closedBall ℝ 0 1
    let B := { φ : WeakDual ℝ C(X, ℝ) | φ ⟨(fun x => 1), continuous_const⟩ = 1 }
    let C := { φ : WeakDual ℝ C(X, ℝ) | ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ φ f}
    have : Φ = A ∩ B ∩ C := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Φ, A, B, C]; tauto
    rw [this]
    apply isCompact_iff_compactSpace.mp
    refine IsCompact.of_isClosed_subset hA1 ?_ ?_
    · refine IsClosed.inter ?_ ?_
      · refine IsClosed.inter (IsCompact.isClosed hA1) ?_
        · let eval1 := fun φ : WeakDual ℝ C(X, ℝ) ↦ φ ⟨(fun x => 1), continuous_const⟩
          have : B = eval1 ⁻¹' {1} := by ext x; simp [B, eval1]
          simp only [this]
          refine (IsClosed.preimage ?_ isClosed_singleton)
          · apply WeakDual.eval_continuous
      · /-Maybe we can generalize this lemma to positive linear maps/order homomorphisms.-/
        have : C = ⋂ (f : { g : C_c(X, ℝ) | 0 ≤ g }), { φ : WeakDual ℝ C(X, ℝ) | 0 ≤ φ f } := by
          ext x; simp [C]
        simp only [this]; apply isClosed_iInter; intro f
        let evalf := fun φ : WeakDual ℝ C(X, ℝ) ↦ φ f
        have : {φ | 0 ≤ φ ↑f} = evalf ⁻¹' Set.Ici 0 := by ext x; simp [evalf]
        simp only [this]; exact (IsClosed.preimage (eval_continuous f.val.toContinuousMap) isClosed_Ici)
    · intro x hx; exact hx.1.1
  apply UniformSpace.compactSpace_iff_seqCompactSpace.mpr
  constructor
  let T : Φ → LevyProkhorov (ProbabilityMeasure X) := by
    intro φ; simp only [Φ] at φ
    let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun    := fun f => φ.1 f.1
      map_add' := by intro f g; rw [← φ.1.map_add]; rfl
      map_smul' := by intro c f; rw [← φ.1.map_smul]; rfl
      monotone' := by
        intro f g hfb; simp;
        obtain ⟨φ,φ2,φ3,φ4⟩ := φ
        push_cast;
        have hφ_nonneg : 0 ≤ φ ↑(g - f) := φ4 (g - f) <| sub_nonneg.2 hfb
        have cont_map_dist : φ ↑(g - f) = φ (g.toContinuousMap - f.toContinuousMap) := rfl
        have : 0 ≤ φ g.toContinuousMap - φ f.toContinuousMap := by
          rw [← ContinuousLinearMap.map_sub, ← cont_map_dist]; exact hφ_nonneg
        simpa using (le_of_sub_nonneg this) }
    have hΛ : ∀ (f : CompactlySupportedContinuousMap X ℝ), 0 ≤ f → 0 ≤ Λ f := φ.2.2.2
    let μ := RealRMK.rieszMeasure Λ; use μ
    constructor
    apply (ENNReal.toReal_eq_one_iff (μ Set.univ)).mp
    let c1 := CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported
      ⟨(fun (x : X) => (1 : ℝ)), continuous_const⟩
    calc
      (μ Set.univ).toReal = μ.real Set.univ := by simp [MeasureTheory.Measure.real_def]
      _ = μ.real Set.univ • 1 := by simp [smul_eq_mul, mul_one]
      _ = ∫ (x : X), 1 ∂μ := (integral_const (μ := μ) 1).symm
      _ = Λ c1 := by exact (RealRMK.integral_rieszMeasure Λ c1)
      _ = φ.1 ⟨fun x ↦ 1, continuous_const⟩ := by rfl
      _ = 1 := φ.2.2.1
  have : Set.univ = Set.range T := by
    ext μ; simp only [Set.mem_univ, Set.mem_range, true_iff, Φ]

    sorry /-Riesz Representation-/
  simp only [this]
  have wat : IsCompact ↑Φ := by exact isCompact_iff_compactSpace.mpr hΦ1
  --have SeparableSpace X := by (expose_names; exact X_1)
  have hΦ2 : SeqCompactSpace Φ := by --need janettes code here
    sorry
  --→SL[σ₁₂]
  sorry

  -- apply IsSeqCompact.range
  -- intro s L hs
  -- sorry

#check MeasureTheory.FiniteMeasure.ext_of_forall_lintegral_eq
