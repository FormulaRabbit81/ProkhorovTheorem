import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib
--set_option maxHeartbeats 400000
--set_option diagnostics true
set_option linter.style.longLine false
set_option linter.unusedTactic false
set_option linter.flexible true
open Topology Metric Filter Set ENNReal NNReal MeasureTheory.ProbabilityMeasure TopologicalSpace

namespace MeasureTheory

open scoped Topology ENNReal NNReal BoundedContinuousFunction

--   simpa [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.tendsto_coe]
--     using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure)


variable {X : Type*} [MeasurableSpace X]

lemma nnreal_tsum_ge_onion {μ : ProbabilityMeasure X} (f : ℕ → Set X)
  (hf : Summable fun n ↦ μ (f n)) :
    μ (⋃ n, f n) ≤ ∑' n, μ (f n) := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_tsum hf]
  simpa using measure_iUnion_le (μ := μ.toMeasure) f

variable [PseudoMetricSpace X] -- may change this to EMetric later

theorem prob_tendsto_measure_iUnion_accumulate {α ι : Type*}
    [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
    {_ : MeasurableSpace α} {μ : Measure α} {f : ι → Set α} :
    Tendsto (fun i ↦ μ (Accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [measure_iUnion_eq_iSup_accumulate]
  exact tendsto_atTop_iSup fun i j hij ↦ by gcongr

-- Definition taken from Rémy's Repository but modified to use ProbabilityMeasure instead of measure. - Need to change this later
def TightProb (S : Set (ProbabilityMeasure X)) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ ε

lemma tightProb_iff_nnreal {S : Set (ProbabilityMeasure X)} :
    TightProb S ↔ ∀ ε : ℝ≥0, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ ε := by
  simp only [TightProb, forall_ennreal, ENNReal.coe_pos, ENNReal.coe_le_coe, zero_lt_top, le_top,
    implies_true, and_true, forall_const, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨∅, isCompact_empty⟩

variable [OpensMeasurableSpace X]

lemma meas_compl_thang (μ : ProbabilityMeasure X) (km : ℕ → ℕ) (m:ℕ) (D : ℕ → X) :
    μ (⋃ i ≤ km (m + 1), closure (ball (D i) (1 / (↑m + 1)))) +
    μ (⋃ i ≤ km (m + 1), closure (ball (D i) (1 / (↑m + 1))))ᶜ = 1 := by
  suffices MeasurableSet (⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (1 / (↑m + 1)))) by
    have := prob_add_prob_compl (α := X) (μ := μ) this
    simp only [← ennreal_coeFn_eq_coeFn_toMeasure] at this
    exact_mod_cast this
  change MeasurableSet (⋃ i ∈ {i | i ≤ km (m + 1)}, _)
  refine Finite.measurableSet_biUnion ?_ ?_
  · exact finite_le_nat (km (m + 1))
  · intro b
    intro hb
    exact measurableSet_closure

variable [SeparableSpace X]
noncomputable section

variable (S : Set (ProbabilityMeasure X))

abbrev P := LevyProkhorov.equiv (ProbabilityMeasure X)

abbrev T := P⁻¹' S

lemma claim5point2 (U : ℕ → Set X) (O : ∀ i, IsOpen (U i))
    (hcomp: IsCompact (closure S)) (ε : ℝ) (heps : ε > 0) (Cov : ⋃ i, U i = univ):
    ∃ (k : ℕ), ∀ μ ∈ S, μ (⋃ (i ≤ k), U i) > 1 - ε := by
  by_contra! nh
  choose μ hμ hμε using nh
  --exact hcomp.mem_of_is_closed (IsClosed.closure hcomp.is_closed)
  obtain ⟨μnew, hμtwo, sub, tub, bub⟩ := hcomp.isSeqCompact (fun n =>  subset_closure <| hμ n)
  have thing n := calc
    (μnew (⋃ (i ≤ n), U i) : ℝ)
    _ ≤ liminf (fun k => (μ (sub k) (⋃ (i ≤ n), U i) : ℝ)) atTop := by
      have hopen : IsOpen (⋃ i ≤ n, U i) := by
        exact isOpen_biUnion fun i a => O i
      --This is the key lemma
      have := ProbabilityMeasure.le_liminf_measure_open_of_tendsto bub hopen
      simp only [Function.comp_apply, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ennreal_coeFn_eq_coeFn_toMeasure] at this
      rw [toReal_liminf]
      norm_cast
      rw [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
      simp_rw [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
      rw [←ofNNReal_liminf] at this
      norm_cast at this
      use 1
      simp only [ge_iff_le, eventually_map, eventually_atTop, forall_exists_index]
      intro a x h
      specialize h x (by simp)
      apply h.trans
      exact ProbabilityMeasure.apply_le_one (μ (sub x)) (⋃ i ≤ n, U i)
    _ ≤ liminf (fun k => (μ (sub k) (⋃ (i ≤ sub k), U i) : ℝ)) atTop := by
      apply Filter.liminf_le_liminf
      · simp only [NNReal.coe_le_coe, eventually_atTop, ge_iff_le]
        use n + 1
        intro b hypo
        refine (μ (sub b)).apply_mono <| Set.biUnion_mono (fun i (hi : i ≤ n) ↦ hi.trans ?_) fun _ _ ↦ le_rfl
        apply le_trans _ (le_trans hypo _)
        norm_num
        exact StrictMono.le_apply tub
      · simp only [autoParam, ge_iff_le, isBoundedUnder_ge_toReal]
        use 0
        simp
      · simp only [autoParam, ge_iff_le, isCoboundedUnder_ge_toReal]
        use 1
        simp only [eventually_map, eventually_atTop, ge_iff_le, forall_exists_index]
        intro a d hyp
        specialize hyp d (by simp)
        apply hyp.trans
        norm_cast
        exact ProbabilityMeasure.apply_le_one (μ (sub d)) (⋃ i ≤ sub d, U i)
    _ ≤ 1 - ε := by
      apply Filter.liminf_le_of_le
      · use 0
        simp
      · simp only [eventually_atTop, ge_iff_le, forall_exists_index]
        intros b c h
        refine le_trans (h c le_rfl) (hμε _)
  have cdiction : Tendsto (fun n => μnew (⋃ i ≤ n, U i)) atTop (𝓝 1) := by
    have re : Tendsto (fun n => μnew (⋃ i ≤ n, U i)) atTop (𝓝 (μnew (⋃ i, U i))) := by
      -- congr
      simp_rw [←Set.accumulate_def]
      exact ProbabilityMeasure.tendsto_measure_iUnion_accumulate
    rw [Cov] at re
    simpa using re

  have oop : ∀ᶠ n in atTop, μnew (⋃ i ≤ n, U i) ≥ 1 - ε / 2 := by
    apply Tendsto.eventually_const_le (v := 1)
    norm_num
    positivity
    rw [←NNReal.tendsto_coe] at cdiction
    exact cdiction

  suffices ∀ᶠ n : ℕ in atTop, False by exact this.exists.choose_spec
  filter_upwards [oop] with n hn
  have whatever := hn.trans (thing n)
  linarith



lemma geom_series : ∑' (x : ℕ), ((2:ℝ) ^ (x+1))⁻¹ = 1 := by
  simp_rw [← inv_pow, pow_succ, _root_.tsum_mul_right, tsum_geometric_inv_two]
  norm_num

variable [CompleteSpace X]

lemma geomsery (ε : ℝ≥0) : (∑' (m : ℕ), ε * 2 ^ (-(m+1) : ℤ) : NNReal) = ε := by
  rw [NNReal.tsum_mul_left]
  nth_rw 2 [←mul_one (a :=ε)]
  congr
  have form : ∑' (x : ℕ), 2 ^ (-((x:ℤ) + 1)) = ∑' (x : ℕ), ((2:ℝ) ^ (x+1))⁻¹ := by
    congr
  refine NNReal.coe_eq_one.mp ?_
  push_cast
  rw [form]
  exact geom_series

lemma better : ∀ m:ℕ, (2 : NNReal) ^ (-(1:ℤ) + -(m:ℤ)) = 1 / 2 * (1 / 2) ^ m := by
  intro m
  field_simp
  rw [← @Int.neg_add]
  rw [@zpow_neg]--rw [←npow_add (n:=(m:ℕ)) (k:=1) (x:=2)]
  refine (inv_mul_eq_one₀ ?_).mpr ?_
  · refine zpow_ne_zero (1 + m) (by simp)
  · refine zpow_one_add₀ (by simp) m

theorem IsTightFamily_of_isRelativelyCompact (hcomp : IsCompact (closure S)) :
    TightProb S := by
  rw [tightProb_iff_nnreal]
  by_cases hempty : ¬Nonempty X
  · simp only [not_nonempty_iff] at hempty
    intro ε εpos
    use ∅
    constructor
    · exact isCompact_empty
    intro μ hμ
    rw [← @univ_eq_empty_iff] at hempty
    rw [← hempty]
    simp_all only [univ_eq_empty_iff, compl_univ]
    rw [← ENNReal.coe_le_coe]
    simp
  simp only [not_nonempty_iff, not_isEmpty_iff] at hempty

  -- Introduce ε > 0 for which we need to find a compact set K with μ(K) ≥ 1 - ε for all μ ∈ S
  intro ε εpos
  obtain ⟨D, fD⟩ := exists_dense_seq X
  --obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  -- For each m ≥ 1, cover X with balls of radius 1/m around points in the dense subset D
  have hcov : ∀ m : ℕ, ⋃ i, ball (D i) (1 / (m+1)) = univ := by
    rw [denseRange_iff] at fD
    intro m
    ext p
    constructor
    · exact fun a ↦ trivial
    specialize fD p
    specialize fD (1 / (m+1))
    intro hp
    have hmdiv : 1 / ((m : ℝ) + 1) > 0 := by
      exact Nat.one_div_pos_of_nat
    specialize fD hmdiv
    exact mem_iUnion.mpr fD

  -- have byclam : ∀ μ ∈ S, ∀ (m : ℕ), ∃ (k : ℕ), μ (⋃ i ≤ k, ball (D i) (φ m)) > 1 - (ε * 2 ^ (-m : ℤ) : ℝ) := by
  --   intro μ hμ m
  --   -- I am sure there is an easier way to do this - I found it!
  --   let m' := m + 1
  --   let ε' := (ε * 2 ^ (-m : ℤ)).toReal
  --   have fiveee : ∃ (k : ℕ), ∀ μ ∈ S, μ (⋃ (i ≤ k), ball (D i) (φ m)) > 1 - ε' := by
  --     apply claim5point2 (S := S) (U := fun i => ball (D i) (φ m)) (ε := ε') (heps := _)
  --     · exact fun i ↦ isOpen_ball
  --     · exact hcomp
  --     · simp_all only [ge_iff_le, one_div]
  --     · intro O hcomp_1
  --       simp_all only [gt_iff_lt, ε']
  --       simp [εpos]
  --   obtain ⟨w, h⟩ := fiveee
  --   use w
  --   exact h μ hμ
  have byclam : ∀ (m : ℕ), ∃ (k : ℕ),∀ μ ∈ S, μ (⋃ i ≤ k, ball (D i) (1 / (m+1))) > 1 - (ε * 2 ^ (-m : ℤ) : ℝ) := by
    intro m
    let ε' :=  (ε : ℝ) * 2 ^ (-m : ℤ)
    apply claim5point2 (S := S) (U := fun i => ball (D i) (1 / (m+1))) (ε := ε') (heps := _)
    · intro i
      exact isOpen_ball
    · exact hcomp
    · exact hcov m
    · intro h _
      positivity

  choose! km hbound using id byclam
  simp_all only [zpow_neg, zpow_natCast]
  let bigK := ⋂ m, ⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1)))
  --This is proven ahead of our calc block as it will need to be called
  --multiple times inside to satisfy tsum's need to show summability
  -- I had to do it inside the actual proof term because this particular
  -- inequality required all our assumptions to be in scope
  have lt_geom_series : ∀ (μ : ProbabilityMeasure X), μ ∈ S → ∑' (m : ℕ), (1 - μ (⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (1 / (↑m + 1))))) < ∑' (m : ℕ), ε * 2 ^ (-((m:ℤ) + 1)) := by
    intro μ hs
    refine NNReal.tsum_strict_mono ?_ ?_
    · rw [summable_mul_left_iff] --Show it is summable
      · field_simp
        simp_rw [better]
        simp only [one_div, inv_pow]
        rw [summable_mul_left_iff]
        · field_simp
          have ugh : (Summable fun m ↦ ((1 / 2 ^ m) : ℝ≥0)) ↔ (Summable fun m ↦ ((1:ℝ) / 2) ^ m) := by
            simp only [one_div, inv_pow]
            exact summable_mk fun n ↦ Nonneg.inv._proof_1 (2 ^ n)
          rw [ugh]
          exact summable_geometric_two
        · simp
      · exact Ne.symm (ne_of_lt εpos)
    · rw [Pi.lt_def]
      constructor
      · intro m
        specialize hbound (m+1) μ hs
        refine tsub_le_iff_tsub_le.mp ?_
        apply le_of_lt at hbound
        simp only [neg_add_rev, Int.reduceNeg, one_div, tsub_le_iff_right]
        simp only [Nat.cast_add, Nat.cast_one, one_div, tsub_le_iff_right] at hbound
        refine one_le_coe.mp ?_
        apply le_trans hbound
        push_cast
        refine add_le_add ?_ ?_
        · gcongr
          refine apply_mono μ ?_
          refine iUnion₂_mono ?_
          intro i hi
          rw [@subset_def]
          intro x hx
          rw [@mem_ball'] at hx
          rw [@EMetric.mem_closure_iff_infEdist_zero]
          refine EMetric.infEdist_zero_of_mem ?_
          rw [@mem_ball']
          apply hx.trans
          field_simp
          refine (one_div_lt_one_div (by positivity) (by positivity)).mpr (by simp)
        · congr!
          rw [← @Int.neg_add, @zpow_neg]
          congr!
          norm_cast
          simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, pow_right_inj₀]
          exact Nat.add_comm m 1
      · use 0
        specialize hbound 1 μ hs
        simp only [zero_add, CharP.cast_eq_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self,
          Int.reduceNeg, zpow_neg, zpow_one]
        simp only [Nat.cast_one, one_div, pow_one, gt_iff_lt] at hbound
        refine NNReal.coe_lt_coe.mp ?_
        simp only [apply_le_one, NNReal.coe_sub, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_inv,
          NNReal.coe_ofNat]
        rw [@sub_lt_comm]
        apply hbound.trans_le
        norm_cast
        simp only [Nat.reduceAdd, Nat.cast_ofNat]
        refine apply_mono μ ?_
        refine iUnion₂_mono ?_
        intro i hi
        rw [@subset_def]
        intro x hx
        rw [@mem_ball'] at hx
        rw [@EMetric.mem_closure_iff_infEdist_zero]
        refine EMetric.infEdist_zero_of_mem ?_
        rw [@mem_ball']
        apply hx.trans
        linarith
  have tsumMeasureCompl (μ : ProbabilityMeasure X): ∑' (m : ℕ), μ (⋃ i ≤ km (m + 1), closure (ball (D i) (1 / (↑m + 1))))ᶜ =
  ∑' (m : ℕ), (1 - μ (⋃ i ≤ km (m + 1), closure (ball (D i) (1 / (↑m + 1))))) := by
    congr! with m
    refine ENNReal.coe_inj.mp ?_
    rw [@ennreal_coeFn_eq_coeFn_toMeasure, measure_compl ?_ ?_]
    · simp
    · refine Finite.measurableSet_biUnion ?_ ?_
      · simp only [Nat.le_eq]
        refine BddAbove.finite ?_
        refine bddAbove_def.mpr ?_
        use km (m + 1) + 1
        intro y
        rw [@mem_def]
        omega
      · intro b _
        exact measurableSet_closure
    · simp


  have bigcalc (μ : ProbabilityMeasure X) (hs : μ ∈ S) := calc
    μ (bigK)ᶜ
    _ = μ (⋃ m,(⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))ᶜ) := by
      simp only [bigK]
      simp only [compl_iInter, compl_iUnion, bigK]
    _ ≤ ∑' m, μ ((⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))ᶜ) := by
      apply nnreal_tsum_ge_onion
      rw [← @tsum_coe_ne_top_iff_summable]
      -- Can possibly cut this shorter here
      refine lt_top_iff_ne_top.mp ?_
      refine lt_iff_exists_real_btwn.mpr ?_
      use ε
      refine ⟨ ?_, ?_, ?_⟩
      · exact zero_le_coe
      · rw [←geomsery ε]
        simp only [ennreal_coeFn_eq_coeFn_toMeasure, ofReal_coe_nnreal]
        have ljbdfi : ∑' (b : ℕ), μ.toMeasure (⋃ i, ⋃ (_ : i ≤ km (b + 1)), closure (ball (D i) (1 / (↑b + 1))))ᶜ
         = ∑' (m : ℕ), (1 - μ (⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (1 / (↑m + 1))))) := by
          rw [← tsumMeasureCompl]
          have klfb : ↑(∑' (m : ℕ), μ (⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (1 / ((m:ℝ) + 1))))ᶜ) =
            (∑' (m : ℕ), μ.toMeasure (⋃ i ≤ km (m + 1), closure (ball (D i) (1 / ((m:ℝ) + 1))))ᶜ) := by
              --rw [@coeFn_def]
              rw [@tsum_eq_toNNReal_tsum]
              simp only [one_div, compl_iUnion, ennreal_coeFn_eq_coeFn_toMeasure, bigK]
              refine coe_toNNReal ?_
              refine lt_top_iff_ne_top.mp ?_
              refine lt_iff_exists_nnreal_btwn.mpr ?_
              use ε
              constructor
              · sorry
              · exact coe_lt_top
              --rw [ENNReal.tsum_toNNReal_eq]




          exact id (Eq.symm klfb)



        rw [ljbdfi]
        exact coe_lt_coe_of_lt (lt_geom_series μ hs)


        -- have eq : ∑' (b : ℕ), μ.toMeasure (⋂ i, ⋂ (_ : i ≤ km (b+1)), (closure (ball (D i) (b+1)⁻¹))ᶜ) = ∑' m, (1 - μ (⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))) := by
        --   have compl : ∑' m, μ ((⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))ᶜ) = ∑' m, (1 - μ (⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))) := by
        --     congr
        --     ext m
        --     congr
        --     refine Eq.symm (tsub_eq_of_eq_add ?_)
        --     apply Eq.symm
        --     rw [add_comm]
        --     exact meas_compl_thang μ km m D
        --   rw [←compl]
        --   have push_coerce : ↑(∑' (m : ℕ), μ (⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (1 / (↑m + 1))))ᶜ) = ∑' (m : ℕ), μ.toMeasure (⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (1 / (↑m + 1))))ᶜ := by
        --     sorry
        --   rw [push_coerce]
        --   congr
        --   simp

        -- -- have lt_geomser : ∑' m, (1 - μ (⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))) < (∑' (m : ℕ), ε * 2 ^ (-(m+1) : ℤ) : NNReal) := by
        -- --   apply?
        -- rw [eq]
        -- gcongr
        -- rw [← geomsery ε]
        -- exact lt_geom_series μ hs
      · simp only [ofReal_coe_nnreal, coe_lt_top, bigK]
    _ = ∑' m, (1 - μ (⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))) := by
      exact tsumMeasureCompl μ
    _ < (∑' (m : ℕ), ε * 2 ^ (-(m+1) : ℤ) : NNReal) := by
      exact lt_geom_series μ hs
    _ = ε := by exact geomsery ε
  by_cases hsempty : S = ∅
  · use ∅
    constructor
    · exact isCompact_empty
    · intro μ hμ
      subst hsempty
      simp_all only [isClosed_empty, IsClosed.closure_eq, finite_empty, Finite.isCompact, mem_empty_iff_false,
        not_isEmpty_of_nonempty, iUnion_of_empty, gt_iff_lt, IsEmpty.exists_iff, implies_true, IsEmpty.forall_iff,
        iInter_of_empty, compl_univ, bigK]
  -- Final proof
  use bigK
  constructor
  -- Compactness first
  · refine isCompact_of_totallyBounded_isClosed ?_ ?_
    --Totally bounded
    · refine EMetric.totallyBounded_iff.mpr ?_
      intro δ δpos
      by_cases δfin : δ = ⊤
      · obtain ⟨x⟩ := hempty
        use {x}
        constructor
        · exact finite_singleton x
        simp [δfin]
      apply nonempty_iff_ne_empty'.mpr at hsempty
      --specialize hempty Classical.choice
      -- t should be image under D of the set of numbers less than km of 1/δ.ceil
      use Set.image D (Finset.Icc 0 (km (⌈1 / δ.toReal⌉₊ + 1)))
      constructor
      · exact toFinite (D '' ↑(Finset.Icc 0 (km (⌈1 / δ.toReal⌉₊ + 1))))
      · simp only [one_div, Finset.coe_Icc, mem_image, mem_Icc, zero_le, true_and, iUnion_exists,
        biUnion_and', iUnion_iUnion_eq_right, bigK]
        have interthing : ∀ t, ⋂ m, ⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (↑m + 1)⁻¹) ⊆ ⋃ i, ⋃ (_ : i ≤ km (t + 1)), closure (ball (D i) (↑t + 1)⁻¹) := by
          exact fun t ↦ iInter_subset_of_subset t fun ⦃a⦄ a ↦ a
        specialize interthing (⌈δ.toReal⁻¹⌉₊)
        apply interthing.trans
        gcongr with i hi
        intro x hx
        rw [@EMetric.mem_ball']
        rw [@EMetric.mem_closure_iff] at hx
        let B : ℝ≥0∞ := δ - (↑δ⁻¹ + (1 / 2: ℝ≥0∞))⁻¹
        specialize hx B
        have Bpos : 0 < B := by
          simp only [one_div, tsub_pos_iff_lt, B, bigK]; field_simp; refine div_lt_of_lt_mul ?_
          ring_nf; refine ENNReal.lt_add_of_sub_lt_left ?_ ?_
          left; exact one_ne_top
          field_simp; rw [@ENNReal.div_eq_inv_mul]
          rw [ENNReal.inv_mul_cancel (ne_of_gt δpos) δfin]
          simp only [tsub_self, ENNReal.div_pos_iff, ne_eq, ofNat_ne_top, not_false_eq_true,
            and_true, B, bigK]
          exact pos_iff_ne_zero.mp δpos
        specialize hx Bpos
        obtain ⟨y, hy, hyd⟩ := hx
        rw [@mem_ball', ← @edist_lt_ofReal] at hy
        apply lt_of_le_of_lt (edist_triangle _ y _)
        rw [edist_comm] at hyd
        have greivance_dos : (ENNReal.ofReal (↑⌈δ.toReal⁻¹⌉₊ + 1)⁻¹) = ((⌈δ.toReal⁻¹⌉₊ + 1):ℝ≥0∞)⁻¹ := by
            refine (toReal_eq_toReal_iff' (by simp) (by simp)).mp ?_
            rw [toReal_ofReal]
            simp; norm_cast; positivity
          --rw [ofReal_toReal]
        rw [greivance_dos] at hy
        have le_sum : edist (D i) y + edist y x < ((↑⌈δ.toReal⁻¹⌉₊ + 1):ℝ≥0∞)⁻¹ + B := by
          exact ENNReal.add_lt_add hy hyd
        apply le_sum.trans; simp only [one_div, B, bigK]
        refine lt_tsub_iff_left.mp ?_
        refine sub_lt_of_sub_lt ?_ ?_ ?_
        · rw [@inv_le_iff_inv_le]
          simp
        · left; exact δfin
        · field_simp
          have subsub : δ - (δ - 1 / (↑⌈1 / δ.toReal⌉₊ + 1)) = 1 / (↑⌈1 / δ.toReal⌉₊ + 1) := by
            refine ENNReal.sub_sub_cancel δfin ?_
            simp only [one_div, B, bigK]
            rw [@inv_le_iff_inv_le]
            refine le_add_of_le_of_nonneg ?_ ?_
            · refine (toReal_le_toReal ?_ (natCast_ne_top ⌈δ.toReal⁻¹⌉₊)).mp ?_
              · simp only [ne_eq, inv_eq_top, B, bigK]; exact pos_iff_ne_zero.mp δpos
              · simp only [toReal_inv, toReal_natCast, B, bigK]
                have coersion : δ.toReal⁻¹ ≤ ⌈δ.toReal⁻¹⌉₊ := by
                  exact Nat.le_ceil δ.toReal⁻¹
                apply coersion.trans; rfl
            simp
          rw [subsub]
          simp only [one_div, ENNReal.inv_lt_inv, gt_iff_lt, B, bigK]
          refine ENNReal.add_lt_add_of_le_of_lt ?_ ?_ ?_
          · refine inv_ne_top.mpr (Ne.symm (ne_of_lt δpos))
          · refine (toReal_le_toReal ?_ ?_).mp ?_
            · refine inv_ne_top.mpr (Ne.symm (ne_of_lt δpos))
            · simp only [ne_eq, natCast_ne_top, not_false_eq_true, B, bigK]
            have ceil_cancel : (δ.toReal⁻¹) ≤ ⌈δ.toReal⁻¹⌉₊ := by
              exact Nat.le_ceil δ.toReal⁻¹
            apply le_trans _ ceil_cancel
            simp
          simp
    -- Closedness
    · simp only [one_div, bigK]
      refine isClosed_iInter ?_
      intro n
      refine Finite.isClosed_biUnion ?_ ?_
      · refine Finite.ofFinset ?_ fun x ↦ ?_
        · exact (Finset.Iic (km (n+1)))
        · simp only [Finset.mem_Iic, Nat.le_eq, bigK]
          exact Eq.to_iff rfl
      intro i hi
      exact isClosed_closure
  exact fun μ a ↦ le_of_lt (bigcalc μ a)


-- lemma fivepoint3 {MeasurableSpace X} (MetricSpace X)  (h : IsCompact X) : (inferInstance : TopologicalSpace (LevyProkhorov (ProbabilityMeasure X))) := by
--   sorry

theorem Prokhorov (G : Set (ProbabilityMeasure X)) [PseudoMetricSpace (Measure X)]:
   (TightProb G) ↔ (IsCompact (closure G)) := by
  constructor
  · sorry
  · exact fun a ↦ IsTightFamily_of_isRelativelyCompact G a


end section
end
end MeasureTheory
--#min_imports
--#lint
--#lint unusedHavesSuffices
