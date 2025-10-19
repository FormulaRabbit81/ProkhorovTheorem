/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Josha Dekker
-/
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.RegularityCompacts


/-!
# Tight sets of measures

A set of measures is tight if for all `0 < ε`, there exists a compact set `K` such that for all
measures in the set, the complement of `K` has measure at most `ε`.

## Main definitions

* `MeasureTheory.IsTightMeasureSet`: A set of measures `S` is tight if for all `0 < ε`, there exists
  a compact set `K` such that for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
  The definition uses an equivalent formulation with filters: `⨆ μ ∈ S, μ` tends to `0` along the
  filter of cocompact sets.
  `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` establishes equivalence between
  the two definitions.

## Main statements

* `isTightMeasureSet_singleton_of_innerRegularWRT`: every finite, inner-regular measure is tight.
* `IsTight_of_isRelativelyCompact`: every relatively compact set of measures is tight.

-/

open Filter Set

open scoped ENNReal NNReal Topology

--This section has been PRed to mathlib:

-- namespace ENNReal

-- protected lemma inv_zpow (x : ℝ≥0∞) (n : ℤ) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
--   simp [← rpow_intCast, inv_rpow]


-- lemma zero_zpow_def (n : ℤ) : (0 : ℝ≥0∞) ^ n = if 0 < n then 0 else if n = 0 then 1 else ⊤ := by
--   have : (0 : ENNReal) ≠ ⊤ := zero_ne_top
--   rcases lt_trichotomy (0 : ℤ) n with (H | rfl | H)
--   swap; · simp
--   · split_ifs with ha
--     swap; · linarith
--     lift n to ℕ using Int.le_of_lt H
--     rw [zpow_natCast]
--     simp only [pow_eq_zero_iff', ne_eq, true_and]
--     exact Nat.ne_zero_iff_zero_lt.mpr <| Int.ofNat_pos.mp H
--   · split_ifs with ha hb
--     all_goals try linarith
--     induction n
--     all_goals try linarith
--     rw [neg_sub_comm,neg_sub_left,←Int.negSucc_eq, zpow_negSucc]
--     simp

-- lemma top_zpow (n : ℤ) : (⊤ : ℝ≥0∞) ^ n = if 0 < n then ⊤ else if n = 0 then 1
--     else 0 := by
--   rw [← inv_zero, ENNReal.inv_zpow, zero_zpow_def]; split_ifs with h; all_goals simp

-- protected lemma inv_zpow' (x : ℝ≥0∞) (n : ℤ) : x⁻¹ ^ n = x ^ (-n) := by
--   by_cases h0 : x = 0
--   · rw[h0, zero_zpow_def]
--     simp
--     rw [top_zpow]
--     split_ifs with ha hb hc hd he hf
--     all_goals try linarith
--     all_goals try rfl
--     have : n = 0 := (Int.le_antisymm (Int.not_lt.mp ha) (Int.not_lt.mp hf))
--     contradiction
--   by_cases h1 : x = ⊤
--   · rw [h1, inv_top, zero_zpow_def, top_zpow]
--     split_ifs with a b c d e f g h
--     all_goals try simp;
--     all_goals try linarith
--     · rw [neg_eq_zero] at f
--       contradiction
--     · rw [neg_eq_zero] at h
--       contradiction
--     simp only [Int.neg_pos, not_lt] at g a
--     have : n = 0 := Eq.symm (Int.le_antisymm g a)
--     contradiction
--   rw [ENNReal.inv_zpow, ←ENNReal.eq_inv_of_mul_eq_one_left]
--   rw [←ENNReal.zpow_add]
--   · simp
--   · exact h0
--   exact h1

-- lemma zpow_le_one_of_nonpos {n : ℤ} (hn : n ≤ 0) {x : ℝ≥0∞} (hx : 1 ≤ x) : x ^ n ≤ 1 := by
--   obtain ⟨m, rfl⟩ := neg_surjective n
--   lift m to ℕ using by simpa using hn
--   rw [← ENNReal.inv_zpow', ENNReal.inv_zpow, ENNReal.inv_le_one]
--   exact mod_cast one_le_pow₀ hx

-- lemma ENNReal.tsum_two_zpow_neg_add_one :
--     ∑' m : ℕ, 2 ^ (-1 - m  : ℤ) = (1 : ENNReal) := by
--   simp_rw [neg_sub_left, ENNReal.zpow_neg (x:= 2) (by norm_num) (by norm_num),
--    ← Nat.cast_one (R := ℤ), ← Nat.cast_add, zpow_natCast, ENNReal.inv_pow,
--    ENNReal.tsum_geometric_add_one, one_sub_inv_two, inv_inv]
--   exact ENNReal.inv_mul_cancel (by simp) (by simp)

-- end ENNReal
namespace MeasureTheory

open Metric ENNReal NNReal ProbabilityMeasure TopologicalSpace

variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] (S : Set (ProbabilityMeasure X))


lemma lt_geom_series (D : ℕ → X) (ε : ℝ≥0∞) (μ : ProbabilityMeasure X) (hs : μ ∈ S) (km : ℕ → ℕ)
    (hbound : ∀ k : ℕ, ∀ μ ∈ S, μ (⋃ i, ⋃ (_ : i ≤ km k), ball (D i) (1 / (↑k + 1))) >
    1 - ε * 2 ^ (-k : ℤ)) :
  ∑' (m : ℕ), (1 - μ.toMeasure (⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (1 / (↑m + 1))))) ≤
  ∑' (m : ℕ), (ε : ENNReal) * 2 ^ (-((m : ℤ) + 1)) := by
  refine ENNReal.tsum_le_tsum ?_
  intro m
  specialize hbound (m+1) μ hs
  refine tsub_le_iff_tsub_le.mp ?_
  apply le_of_lt at hbound
  simp only [neg_add_rev, Int.reduceNeg, one_div, tsub_le_iff_right]
  simp only [Nat.cast_add, Nat.cast_one, one_div, tsub_le_iff_right] at hbound
  rw [← ENNReal.coe_ofNat,← ENNReal.coe_zpow, ←ennreal_coeFn_eq_coeFn_toMeasure]
  swap; · simp
  apply le_trans hbound
  gcongr
  · refine apply_mono μ <| iUnion₂_mono ?_
    intro i hi
    rw [subset_def]
    intro x hx; rw [EMetric.mem_closure_iff_infEdist_zero]
    refine EMetric.infEdist_zero_of_mem ?_
    rw [mem_ball']; rw [mem_ball'] at hx;
    apply hx.trans; field_simp
    refine (one_div_lt_one_div (by positivity) (by positivity)).mpr (by simp)
  · rw [← Int.neg_add, zpow_neg]; norm_cast
    simp only [zpow_negSucc, Nat.cast_pow, Nat.cast_ofNat, ne_eq, Nat.add_eq_zero, one_ne_zero,
      false_and, not_false_eq_true, pow_eq_zero_iff, OfNat.ofNat_ne_zero, coe_inv,
      ENNReal.coe_pow, coe_ofNat, ENNReal.inv_le_inv]
    rw [Nat.add_comm m 1]

noncomputable section

variable [OpensMeasurableSpace X] [SeparableSpace X]

lemma MeasOpenCoverTendstoMeasUniv (U : ℕ → Set X) (O : ∀ i, IsOpen (U i))
    (hcomp : IsCompact (closure S)) (ε : ℝ≥0∞) (hε : 0 < ε) (hεbound : ε ≤ 1)
    (Cov : ⋃ i, U i = univ) : ∃ (k : ℕ), ∀ μ ∈ S,  1 - ε < μ (⋃ (i ≤ k), U i) := by
  have εfin : ε ≠ ⊤ := by
    intro h
    rw [h] at hεbound
    exact not_top_le_coe hεbound
  lift ε to ℝ≥0 using εfin
  obtain ⟨ε,hε'⟩ := ε
  simp only [ENNReal.coe_pos, ← NNReal.coe_lt_coe, NNReal.coe_zero, NNReal.coe_mk, coe_le_one_iff, ←
    NNReal.coe_le_coe, NNReal.coe_one] at hε hεbound
  by_contra! nh; choose μ hμInS hcontradiction using nh
  obtain ⟨μlim, _, sub, hsubmono, hμconverges⟩ :=
  hcomp.isSeqCompact (fun n ↦ subset_closure <| hμInS n)
  have Measurebound n := calc
    (μlim (⋃ (i ≤ n), U i) : ℝ)
    _ ≤ liminf (fun k ↦ (μ (sub k) (⋃ (i ≤ n), U i) : ℝ)) atTop := by
      have hopen : IsOpen (⋃ i ≤ n, U i) := isOpen_biUnion fun i a ↦ O i
      have := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμconverges hopen
      simp only [Function.comp_apply] at this
      rw [toReal_liminf]; norm_cast
      simp_rw [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
      rw [←ofNNReal_liminf] at this; norm_cast at this
      use 1
      simp only [ge_iff_le, eventually_map, eventually_atTop, forall_exists_index]
      exact fun _ x h ↦ (h x (by simp)).trans <|
        ProbabilityMeasure.apply_le_one (μ (sub x)) (⋃ i ≤ n, U i)
    _ ≤ liminf (fun k ↦ (μ (sub k) (⋃ (i ≤ sub k), U i) : ℝ)) atTop := by
      apply Filter.liminf_le_liminf
      · simp only [NNReal.coe_le_coe, eventually_atTop, ge_iff_le]
        use n + 1
        intro b hypo
        refine (μ (sub b)).apply_mono
        <| Set.biUnion_mono (fun i (hi : i ≤ n) ↦ hi.trans ?_) fun _ _ ↦ le_rfl
        exact le_trans (Nat.le_add_right n 1) (le_trans hypo (StrictMono.le_apply hsubmono))
      · simp only [autoParam, ge_iff_le, isBoundedUnder_ge_toReal]; use 0; simp
      · simp only [autoParam, ge_iff_le, isCoboundedUnder_ge_toReal]
        use 1
        simp only [eventually_map, eventually_atTop, ge_iff_le, forall_exists_index]
        exact fun _ d hyp ↦ (hyp d (by simp)).trans
          <| ProbabilityMeasure.apply_le_one (μ (sub d)) (⋃ i ≤ sub d, U i)
    _ ≤ 1 - ε := by
      apply Filter.liminf_le_of_le
      · use 0; simp
      simp only [eventually_atTop, ge_iff_le, forall_exists_index]
      intro b c h
      apply le_trans (h c le_rfl)
      refine (ofReal_le_ofReal_iff ?_).mp ?_
      · rw [sub_nonneg]
        exact hεbound
      rw [ofReal_coe_nnreal]
      apply le_trans (hcontradiction (sub c))
      norm_cast
  have accumulation : Tendsto (fun n ↦ μlim (⋃ i ≤ n, U i)) atTop (𝓝 (μlim (⋃ i, U i))) := by
    simp_rw [←Set.accumulate_def]
    exact ProbabilityMeasure.tendsto_measure_iUnion_accumulate
  rw [Cov, coeFn_univ, ←NNReal.tendsto_coe] at accumulation
  have exceeds_bound : ∀ᶠ n in atTop, (1 - ε / 2 : ℝ) ≤ μlim (⋃ i ≤ n, U i) := by
    refine Tendsto.eventually_const_le (v := 1) (by simp; positivity) (accumulation)
  suffices ∀ᶠ n : ℕ in atTop, False by exact this.exists.choose_spec
  filter_upwards [exceeds_bound] with n hn
  have lim_measure_lb : (1 - ε / 2 : ℝ) ≤ 1 - ε := hn.trans <| Measurebound n
  linarith [lim_measure_lb]

variable [CompleteSpace X]

theorem IsTight_of_isRelativelyCompact (hcomp : IsCompact (closure S)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} := by
  rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  by_cases hempty : IsEmpty X
  · intro ε εpos
    use ∅
    constructor
    · exact isCompact_empty
    intro μ hμ
    rw [← univ_eq_empty_iff] at hempty
    rw [←hempty]
    simp
  rw [not_isEmpty_iff] at hempty
  intro ε εpos
  obtain ⟨D, hD⟩ := exists_dense_seq X
  have hcov (m : ℕ): ⋃ i, ball (D i) (1 / (m + 1)) = univ := by
    rw [denseRange_iff] at hD
    ext p
    exact ⟨fun a ↦ trivial,fun _ ↦ mem_iUnion.mpr <| hD p (1 / (m + 1)) Nat.one_div_pos_of_nat⟩
  by_cases hεbound : ε > 1
  · use ∅
    constructor;
    · exact isCompact_empty
    intro μ hμ
    simp only [mem_setOf_eq] at hμ
    obtain ⟨μ', hμ', rfl⟩ := hμ
    rw [compl_empty,measure_univ]; exact le_of_lt hεbound
  have byclaim (m : ℕ) : ∃ (k : ℕ), ∀ μ ∈ S, μ (⋃ i ≤ k, ball (D i) (1 / (m + 1))) >
  1 - (ε * 2 ^ (- m : ℤ) : ℝ≥0∞) := by
    refine (MeasOpenCoverTendstoMeasUniv (S := S) (U := fun i ↦ ball (D i) (1 / (m + 1)))
    (ε := (ε * 2 ^ (-m : ℤ))) (hε := ?_) (fun i ↦ isOpen_ball) hcomp) ?_ (hcov m)
    · simp; exact ⟨εpos,(ENNReal.zpow_pos (Ne.symm (NeZero.ne' 2)) (ofNat_ne_top) (-↑m))⟩
    · exact Left.mul_le_one (le_of_not_gt hεbound) <| zpow_le_one_of_nonpos (by linarith) (by simp)
  choose! km hbound using byclaim
  -- This is a set we can construct to show tightness
  let bigK := ⋂ m, ⋃ (i ≤ km (m + 1)), closure (ball (D i) (1 / (m + 1)))
  have bigcalc (μ : ProbabilityMeasure X) (hs : μ ∈ S) := calc
    μ.toMeasure (bigK)ᶜ
    _ = μ.toMeasure (⋃ m,(⋃ (i ≤ km (m + 1)), closure (ball (D i) (1 / (m + 1))))ᶜ) := by
      simp only [bigK, compl_iInter, compl_iUnion]
    _ ≤ ∑' m, μ.toMeasure ((⋃ (i ≤ km (m + 1)), closure (ball (D i) (1 / (m + 1))))ᶜ) := by
      apply measure_iUnion_le
    _ = ∑' m, (1 - μ.toMeasure (⋃ (i ≤ km (m + 1)), closure (ball (D i) (1 / (m + 1))))) := by
      congr! with m; rw [measure_compl (by measurability) (by simp)]; simp
    _ ≤ (∑' (m : ℕ), (ε : ENNReal) * 2 ^ (-(m + 1) : ℤ)) := by
      apply lt_geom_series S D ε μ hs km hbound
    _ = ε := by
      rw [ENNReal.tsum_mul_left]
      nth_rw 2 [←mul_one (a :=ε)]
      congr
      ring_nf
      exact ENNReal.tsum_two_zpow_neg_add_one
  -- Final proof
  use bigK
  constructor
  -- Compactness first
  · refine TotallyBounded.isCompact_of_isClosed ?_ ?_
    --Totally bounded
    · refine Metric.totallyBounded_iff.mpr ?_
      intro δ δpos
      -- t should be image under D of the set of numbers less than km of 1/δ.ceil
      refine ⟨D '' .Iic (km (⌊δ⁻¹⌋₊ + 1)), (Set.finite_Iic _).image _, ?_⟩
      simp only [one_div, mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right, bigK]
      calc
            ⋂ m, ⋃ i ≤ km (m + 1), closure (ball (D i) (m + 1)⁻¹)
        _ ⊆ ⋃ i ≤ km (⌊δ⁻¹⌋₊ + 1), closure (ball (D i) (⌊δ⁻¹⌋₊ + 1)⁻¹) := iInter_subset ..
        _ ⊆ ⋃ i ≤ km (⌊δ⁻¹⌋₊ + 1), ball (D i) δ := by
            gcongr
            exact closure_ball_subset_closedBall.trans <| closedBall_subset_ball <|
              inv_lt_of_inv_lt₀ δpos <| Nat.lt_floor_add_one _
    -- Closedness
    · simp only [one_div, bigK]
      refine isClosed_iInter ?_
      intro n
      refine Finite.isClosed_biUnion ?_ (fun _ _ ↦ isClosed_closure)
      · refine Finite.ofFinset (Finset.Iic (km (n + 1))) fun x ↦ ?_
        simp only [Finset.mem_Iic, Nat.le_eq]; exact Eq.to_iff rfl
  simp only [mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact bigcalc

end

end MeasureTheory
