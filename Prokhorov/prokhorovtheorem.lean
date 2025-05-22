import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Tactic.Rify

--import Mathlib
--set_option maxHeartbeats 400000
--set_option diagnostics true
set_option linter.style.longLine false
set_option linter.unusedTactic false
set_option linter.flexible true
open Topology Metric Filter Set ENNReal NNReal MeasureTheory.ProbabilityMeasure TopologicalSpace
namespace MeasureTheory

open scoped Topology ENNReal NNReal BoundedContinuousFunction


variable {X : Type*} [MeasurableSpace X]

lemma ENNreal_ProbMeasure_toMeasure (μ : ProbabilityMeasure X) (s : Set X) :
    μ.toMeasure s = ((μ s) : ENNReal) := by
    exact Eq.symm (ennreal_coeFn_eq_coeFn_toMeasure μ s)

lemma nnreal_tsum_ge_union {μ : ProbabilityMeasure X} (f : ℕ → Set X)
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
def Tight (G : Set (Measure X)) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∀ μ ∈ G, μ Kᶜ ≤ ε

def TightProb (S : Set (ProbabilityMeasure X)) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ ε

/-- Need to sort this out so I can put this in Remy's repo-/
lemma tight_iff_tightprob (G : Set (Measure X)) {S : Set (ProbabilityMeasure X)} : Tight G ↔ TightProb S := by sorry

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
  · intro b hb
    exact measurableSet_closure

variable [SeparableSpace X]
noncomputable section

variable (S : Set (ProbabilityMeasure X))

abbrev P := LevyProkhorov.equiv (ProbabilityMeasure X)

abbrev T := P⁻¹' S

lemma MeasOpenCoverTendstoMeasUniv (U : ℕ → Set X) (O : ∀ i, IsOpen (U i))
    (hcomp: IsCompact (closure S)) (ε : ℝ) (heps : ε > 0) (Cov : ⋃ i, U i = univ):
    ∃ (k : ℕ), ∀ μ ∈ S, μ (⋃ (i ≤ k), U i) > 1 - ε := by
  by_contra! nh
  choose μ hμInS hcontradiction using nh
  obtain ⟨μlim, _, sub, hsubmono, hμconverges⟩ := hcomp.isSeqCompact (fun n => subset_closure <| hμInS n)
  have Measurebound n := calc
    (μlim (⋃ (i ≤ n), U i) : ℝ)
    _ ≤ liminf (fun k => (μ (sub k) (⋃ (i ≤ n), U i) : ℝ)) atTop := by
      have hopen : IsOpen (⋃ i ≤ n, U i) := by
        exact isOpen_biUnion fun i a => O i
      --This is the key lemma
      have := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμconverges hopen
      simp only [Function.comp_apply, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ennreal_coeFn_eq_coeFn_toMeasure] at this
      rw [toReal_liminf]; norm_cast
      simp_rw [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
      rw [←ofNNReal_liminf] at this; norm_cast at this
      use 1
      simp only [ge_iff_le, eventually_map, eventually_atTop, forall_exists_index]
      intro a x h
      specialize h x (by simp); apply h.trans
      exact ProbabilityMeasure.apply_le_one (μ (sub x)) (⋃ i ≤ n, U i)
    _ ≤ liminf (fun k => (μ (sub k) (⋃ (i ≤ sub k), U i) : ℝ)) atTop := by
      apply Filter.liminf_le_liminf
      · simp only [NNReal.coe_le_coe, eventually_atTop, ge_iff_le]
        use n + 1
        intro b hypo
        refine (μ (sub b)).apply_mono <| Set.biUnion_mono (fun i (hi : i ≤ n) ↦ hi.trans ?_) fun _ _ ↦ le_rfl
        apply le_trans (Nat.le_add_right n 1) (le_trans hypo (StrictMono.le_apply hsubmono))
      · simp only [autoParam, ge_iff_le, isBoundedUnder_ge_toReal]
        use 0; simp
      · simp only [autoParam, ge_iff_le, isCoboundedUnder_ge_toReal]
        use 1; simp only [eventually_map, eventually_atTop, ge_iff_le, forall_exists_index]
        intro a d hyp
        specialize hyp d (by simp)
        apply hyp.trans; norm_cast
        exact ProbabilityMeasure.apply_le_one (μ (sub d)) (⋃ i ≤ sub d, U i)
    _ ≤ 1 - ε := by
      apply Filter.liminf_le_of_le
      · use 0; simp
      · simp only [eventually_atTop, ge_iff_le, forall_exists_index]
        intro b c h
        apply le_trans (h c le_rfl) (hcontradiction _)
  have cdiction : Tendsto (fun n => μlim (⋃ i ≤ n, U i)) atTop (𝓝 1) := by
    have accumulation : Tendsto (fun n => μlim (⋃ i ≤ n, U i)) atTop (𝓝 (μlim (⋃ i, U i))) := by
      simp_rw [←Set.accumulate_def]
      exact ProbabilityMeasure.tendsto_measure_iUnion_accumulate
    rw [Cov] at accumulation
    simpa using accumulation
  have tends_to_univ : ∀ᶠ n in atTop, μlim (⋃ i ≤ n, U i) ≥ 1 - ε / 2 := by
    apply Tendsto.eventually_const_le (v := 1)
    norm_num; positivity
    rw [←NNReal.tendsto_coe] at cdiction
    exact cdiction
  suffices ∀ᶠ n : ℕ in atTop, False by exact this.exists.choose_spec
  filter_upwards [tends_to_univ] with n hn
  have falseity := hn.trans (Measurebound n)
  linarith

--#lint unusedHavesSuffices
lemma geom_series : ∑' (x : ℕ), ((2:ℝ) ^ (x+1))⁻¹ = 1 := by
  simp_rw [← inv_pow, pow_succ, _root_.tsum_mul_right, tsum_geometric_inv_two]
  norm_num

variable [CompleteSpace X]

lemma geomsery (ε : ENNReal) : (∑' (m : ℕ), ε * 2 ^ (-(m+1) : ℤ)) = ε := by
  rw [ENNReal.tsum_mul_left]
  nth_rw 2 [←mul_one (a :=ε)]
  congr
  simp_rw [← Nat.cast_one (R := ℤ), ← Nat.cast_add, ENNReal.zpow_neg (x:= 2) (by norm_num) (by norm_num)]
  simp_rw [zpow_natCast, ENNReal.inv_pow]
  rw [ENNReal.tsum_geometric_add_one]
  norm_num
  rw [ENNReal.inv_mul_cancel]
  all_goals norm_num

lemma better : ∀ m:ℕ, (2 : NNReal) ^ (-(1:ℤ) + -(m:ℤ)) = 1 / 2 * (1 / 2) ^ m := by
  intro m
  field_simp
  rw [← @Int.neg_add, zpow_neg]
  refine (inv_mul_eq_one₀ ?_).mpr ?_
  · refine zpow_ne_zero (1 + m) (by simp)
  · refine zpow_one_add₀ (by simp) m

-- set_option diagnostics true in
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
  have byclam : ∀ (m : ℕ), ∃ (k : ℕ),∀ μ ∈ S, μ (⋃ i ≤ k, ball (D i) (1 / (m+1))) > 1 - (ε * 2 ^ (-m : ℤ) : ℝ) := by
    intro m
    let ε' :=  (ε : ℝ) * 2 ^ (-m : ℤ)
    apply MeasOpenCoverTendstoMeasUniv (S := S) (U := fun i => ball (D i) (1 / (m+1))) (ε := ε') (heps := _)
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
  have lt_geom_series : ∀ (μ : ProbabilityMeasure X), μ ∈ S → ∑' (m : ℕ), (1 - μ.toMeasure (⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (1 / (↑m + 1))))) ≤ ∑' (m : ℕ), (ε: ENNReal) * 2 ^ (-((m:ℤ) + 1)) := by
    intro μ hs
    refine ENNReal.tsum_le_tsum ?_
    intro m
    specialize hbound (m+1) μ hs
    refine tsub_le_iff_tsub_le.mp ?_
    apply le_of_lt at hbound
    simp only [neg_add_rev, Int.reduceNeg, one_div, tsub_le_iff_right]
    simp only [Nat.cast_add, Nat.cast_one, one_div, tsub_le_iff_right] at hbound
    -- refine one_le_coe.mp ?_
    rw [← ENNReal.coe_ofNat,← ENNReal.coe_zpow,← ENNReal.coe_mul,ENNreal_ProbMeasure_toMeasure, ← ENNReal.coe_add,ENNReal.one_le_coe_iff, ← NNReal.coe_le_coe]
    apply le_trans hbound
    push_cast
    gcongr
    · refine apply_mono μ ?_
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
    · simp
  have tsumMeasureCompl (μ : ProbabilityMeasure X) : ∑' (m : ℕ), μ.toMeasure (⋃ i ≤ km (m + 1), closure (ball (D i) (1 / (↑m + 1))))ᶜ =
  ∑' (m : ℕ), (1 - μ.toMeasure (⋃ i ≤ km (m + 1), closure (ball (D i) (1 / (↑m + 1))))) := by
    congr! with m
    rw [measure_compl ?_ ?_]
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
    μ.toMeasure (bigK)ᶜ
    _ = μ.toMeasure (⋃ m,(⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))ᶜ) := by
      simp only [bigK]
      simp only [compl_iInter, compl_iUnion, bigK]
    _ ≤ ∑' m, μ.toMeasure ((⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))ᶜ) := by
      apply measure_iUnion_le
    _ = ∑' m, (1 - μ.toMeasure (⋃ (i ≤ km (m+1)), closure (ball (D i) (1 / (m+1))))) := by
      exact tsumMeasureCompl μ
    _ ≤ (∑' (m : ℕ), (ε : ENNReal) * 2 ^ (-(m+1) : ℤ)) := by
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
          unfold B
          rw [tsub_pos_iff_lt]
          lift δ to ℝ≥0 using δfin
          suffices ↑((δ:NNReal)⁻¹ + ↑((1:NNReal) / (2:NNReal)))⁻¹ < (δ:ENNReal) by -- shoudln't be necessary
            convert this using 1
            push_cast -- cast of inverse equals invers of cast, missing norm_cast/push_cast lemma?
            simp only [one_div, ne_eq, add_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, and_false,
              not_false_eq_true, coe_inv, coe_add, coe_ofNat, inv_inj, bigK]
            refine (ENNReal.add_left_inj <| by simp).mpr ?_
            · refine Eq.symm (coe_inv ?_)
              simp only [gt_iff_lt, ENNReal.coe_pos, bigK] at δpos
              exact Ne.symm (ne_of_lt δpos)
          norm_cast at δpos ⊢
          rw [inv_lt_iff_one_lt_mul₀]
          field_simp
          rw [lt_div_iff₀,← NNReal.coe_lt_coe]
          rify
          have H : 0 < (δ:ℝ) ^2:= by positivity
          linear_combination H
          all_goals positivity
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
  simp_rw [ENNreal_ProbMeasure_toMeasure, ENNReal.coe_le_coe] at bigcalc
  exact bigcalc


-- lemma fivepoint3 {MeasurableSpace X} (MetricSpace X)  (h : IsCompact X) : (inferInstance : TopologicalSpace (LevyProkhorov (ProbabilityMeasure X))) := by
--   sorry

theorem Prokhorov (G : Set (ProbabilityMeasure X)) [PseudoMetricSpace (Measure X)]:
   (TightProb G) ↔ (IsCompact (closure G)) := by
  constructor
  · sorry
  · exact fun a ↦ IsTightFamily_of_isRelativelyCompact G a

-- /--Nonsense from here onwards-/
-- variable {A B : Type*} [TopologicalSpace A] {mA : MeasurableSpace A}
--   {μ ν : Measure A} {G H : Set (Measure A)}
-- /-- A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K` such that
-- for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
-- This is formulated in terms of filters, and proven equivalent to the definition above
-- in `IsTightMeasureSet_iff_exists_isCompact_measure_compl_le`. -/
-- def IsTightMeasureSet (S : Set (Measure X)) : Prop :=
--   Tendsto (⨆ μ ∈ S, μ) (cocompact X).smallSets (𝓝 0)

-- /-- A set of measures `S` is tight if for all `0 < ε`, there exists a compact set `K` such that
-- -- for all `μ ∈ S`, `μ Kᶜ ≤ ε`. -/
-- lemma IsTightMeasureSet_iff_exists_isCompact_measure_compl_le :
--     IsTightMeasureSet G ↔ ∀ ε, 0 < ε → ∃ K : Set A, IsCompact K ∧ ∀ μ ∈ S, μ (Kᶜ) ≤ ε := by
--   simp only [IsTightMeasureSet, ENNReal.tendsto_nhds ENNReal.zero_ne_top, gt_iff_lt, zero_add,
--     iSup_apply, mem_Icc, tsub_le_iff_right, zero_le, iSup_le_iff, true_and, eventually_smallSets,
--     mem_cocompact]
--   refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
--   · obtain ⟨A, ⟨K, h1, h2⟩, hA⟩ := h ε hε
--     exact ⟨K, h1, hA Kᶜ h2⟩
--   · obtain ⟨K, h1, h2⟩ := h ε hε
--     exact ⟨Kᶜ, ⟨K, h1, subset_rfl⟩, fun A hA μ hμS ↦ (μ.mono hA).trans (h2 μ hμS)⟩

-- theorem isTightMeasureSet_iff_isCompact_closure
--   {E : Type*} {mE : MeasurableSpace E} [MetricSpace E] [CompleteSpace E]
--   [SecondCountableTopology E] [BorelSpace E] {S : Set (ProbabilityMeasure E)} :
--     IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}
--       ↔ IsCompact (closure S) := by sorry


end section
end
end MeasureTheory
--#min_imports
--#lint
--#lint unusedHavesSuffices
