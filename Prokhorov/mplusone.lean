import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
--set_option maxHeartbeats 400000
--set_option diagnostics true
set_option linter.style.longLine false

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
  simp [TightProb, ENNReal.forall_ennreal, ←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact fun _ ↦ ⟨∅, isCompact_empty⟩

variable [OpensMeasurableSpace X] [SeparableSpace X]

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
      simp only [Function.comp_apply, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
      simp at this
      rw [toReal_liminf]
      norm_cast
      rw [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
      simp_rw [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
      rw [←ofNNReal_liminf] at this
      norm_cast at this
      use 1
      simp
      intro a x h
      specialize h x (by simp)
      apply h.trans
      exact ProbabilityMeasure.apply_le_one (μ (sub x)) (⋃ i ≤ n, U i)
    _ ≤ liminf (fun k => (μ (sub k) (⋃ (i ≤ sub k), U i) : ℝ)) atTop := by
      apply Filter.liminf_le_liminf
      · simp
        use n + 1
        intro b hypo
        refine (μ (sub b)).apply_mono <| Set.biUnion_mono (fun i (hi : i ≤ n) ↦ hi.trans ?_) fun _ _ ↦ le_rfl
        apply le_trans _ (le_trans hypo _)
        norm_num
        exact StrictMono.le_apply tub
      · simp [autoParam]
        use 0
        simp
      · simp [autoParam]
        use 1
        simp
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
    simp at re
    exact re

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
  have frac : ∑' (x : ℕ), ((2 ^ (x+1)) : ℝ)⁻¹ = ∑' (x : ℕ), (1 / 2) ^ (x+1) := by
    congr
    simp
  rw [frac]
  have gethalf : ∑' (x : ℕ), ((1 : ℝ) / 2) ^ (x + 1) = 1/2 * (∑' (x : ℕ), 1 / 2 ^ x) := by
    have robert : ∑' (x : ℕ), ((1 : ℝ) / 2) ^ (x + 1) = ∑' (x : ℕ), (1/2) * (1 / 2) ^ x := by
      simp
      congr
      field_simp
      congr! with x
      exact pow_succ' 2 x
    rw [robert]
    simp
    simp_all only [one_div, inv_pow]
    exact _root_.tsum_mul_left
  rw [gethalf]
  field_simp
  have sdfdhf : ∑' (x : ℕ), 1 / 2 ^ x = ∑' n : ℕ, ((1 : ℝ) / 2) ^ n := by
    simp_all only [one_div, inv_pow]
  rw [sdfdhf]
  exact tsum_geometric_two

variable [CompleteSpace X]

theorem IsTightFamily_of_isRelativelyCompact (hcomp : IsCompact (closure S)) :
    TightProb S := by
  rw [tightProb_iff_nnreal]
  by_cases hempty : ¬Nonempty X
  · simp at hempty
    intro ε εpos
    use ∅
    constructor
    · exact isCompact_empty
    intro μ hμ
    rw [← @univ_eq_empty_iff] at hempty
    rw [← hempty]
    simp_all
    rw [← ENNReal.coe_le_coe]
    simp
  simp at hempty

  -- Introduce ε > 0 for which we need to find a compact set K with μ(K) ≥ 1 - ε for all μ ∈ S
  intro ε εpos
  obtain ⟨D, fD⟩ := exists_dense_seq X
  obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  -- For each m ≥ 1, cover X with balls of radius 1/m around points in the dense subset D
  have hcov : ∀ m : ℕ, ⋃ i, ball (D i) (φ m) = univ := by
    rw [denseRange_iff] at fD
    intro m
    ext p
    constructor
    · exact fun a ↦ trivial
    specialize fD p
    specialize fD (φ m)
    intro hp
    specialize fD (hφ₂ m)
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
  have byclam : ∀ (m : ℕ), ∃ (k : ℕ),∀ μ ∈ S, μ (⋃ i ≤ k, ball (D i) (φ m)) > 1 - (ε * 2 ^ (-m : ℤ) : ℝ) := by
    intro m
    let ε' :=  (ε : ℝ) * 2 ^ (-m : ℤ)
    apply claim5point2 (S := S) (U := fun i => ball (D i) (φ m)) (ε := ε') (heps := _)
    · intro i
      exact isOpen_ball
    · exact hcomp
    · exact hcov m
    · intro h _
      positivity

  choose! km hbound using id byclam
  simp_all only [zpow_neg, zpow_natCast]
  let bigK := ⋂ m, ⋃ (i ≤ km (m+1)), closure (ball (D i) (φ (m+1)))
  have bigcalc (μ : ProbabilityMeasure X) (hs : μ ∈ S) := calc
    μ (bigK)ᶜ
    _ = μ (⋃ m,(⋃ (i ≤ km (m+1)), closure (ball (D i) (φ (m+1))))ᶜ) := by
      simp only [bigK]
      simp only [compl_iInter, compl_iUnion, bigK]
    _ ≤ ∑' m, μ ((⋃ (i ≤ km (m+1)), closure (ball (D i) (φ (m+1))))ᶜ) := by
      simp
      apply nnreal_tsum_ge_onion
      rw [← @tsum_coe_ne_top_iff_summable]
      refine lt_top_iff_ne_top.mp ?_
      refine lt_iff_exists_real_btwn.mpr ?_
      use ε
      refine ⟨ ?_, ?_, ?_⟩
      · exact zero_le_coe
      · simp

        have eq : ∑' (b : ℕ), μ.toMeasure (⋂ i, ⋂ (_ : i ≤ km (b+1)), (closure (ball (D i) (φ (b+1))))ᶜ) = ∑' m, (1 - μ (⋃ (i ≤ km (m+1)), closure (ball (D i) (φ (m+1))))) := by
          have compl : ∑' m, μ ((⋃ (i ≤ km (m+1)), closure (ball (D i) (φ (m+1))))ᶜ) = ∑' m, (μ univ - μ (⋃ (i ≤ km (m+1)), closure (ball (D i) (φ (m+1))))) := by
            refine tsum_eq_tsum_of_hasSum_iff_hasSum ?_
          -- rw [measure_compl (s := (⋃ i, ⋃ (_ : i ≤ km μ _), closure (ball (D i) (φ _)))) (μ := μ)]
            sorry
          sorry
        have lt_geomser : ∑' m, (1 - μ (⋃ (i ≤ km (m+1)), closure (ball (D i) (φ (m+1))))) < (∑' (m : ℕ), ε * 2 ^ (-(m+1) : ℤ) : NNReal) := by sorry
        have geom_ser : (∑' (m : ℕ), ε * 2 ^ (-(m+1) : ℤ) : NNReal) = ε := by sorry
        rw [eq]
        gcongr
        rw [← geom_ser]
        exact lt_geomser
      · simp only [ofReal_coe_nnreal, coe_lt_top, bigK]
    _ = ∑' m, (1 - μ (⋃ (i ≤ km (m+1)), closure (ball (D i) (φ (m+1))))) := by sorry
    _ < (∑' (m : ℕ), ε * 2 ^ (-(m+1) : ℤ) : NNReal) := by sorry
    _ = ε := by
      rw [NNReal.tsum_mul_left]
      nth_rw 2 [←mul_one (a :=ε)]
      congr
      have form : ∑' (x : ℕ), 2 ^ (-((x:ℤ) + 1)) = ∑' (x : ℕ), ((2:ℝ) ^ (x+1))⁻¹ := by
        congr
      refine NNReal.coe_eq_one.mp ?_
      push_cast
      rw [form]
      exact geom_series

  by_cases hempty : S = ∅
  · use ∅
    constructor
    · exact isCompact_empty
    · intro μ hμ
      subst hempty
      simp_all only [isClosed_empty, IsClosed.closure_eq, finite_empty, Finite.isCompact, mem_empty_iff_false,
        not_isEmpty_of_nonempty, iUnion_of_empty, gt_iff_lt, IsEmpty.exists_iff, implies_true, IsEmpty.forall_iff,
        iInter_of_empty, compl_univ, bigK]
  -- obtain ⟨s⟩ := hempty
  -- Final proof
  use bigK
  constructor
  -- Compactness first
  · refine isCompact_of_totallyBounded_isClosed ?_ ?_
    --Totally bounded
    · refine EMetric.totallyBounded_iff.mpr ?_
      intro δ δpos
      apply nonempty_iff_ne_empty'.mpr at hempty
      --specialize hempty Classical.choice
      -- t should be image under D of the set of numbers less than km of 1/δ.ceil
      use Set.image D (Finset.Icc 0 (km (Nat.ceil (1 /δ.toReal))))
      constructor
      · simp
        exact toFinite (D '' Icc 0 (km ⌈δ.toReal⁻¹⌉₊))
      · simp [bigK]
        have interthing : ∀ t, ⋂ m, ⋃ i, ⋃ (_ : i ≤ km (m + 1)), closure (ball (D i) (φ (m + 1))) ⊆ ⋃ i, ⋃ (_ : i ≤ km (t + 1)), closure (ball (D i) (φ (t + 1))) := by
          exact fun t ↦ iInter_subset_of_subset t fun ⦃a⦄ a ↦ a
        specialize interthing (⌈δ.toReal⁻¹⌉₊ - 1)
        apply interthing.trans
        gcongr with i
        simp
        intro hkm





        -- Want to say intersection over m is subset of particular m = ⌈δ.toReal⁻¹⌉₊
        --refine iInter_subset LE.le (⋂ m, ⋃ i, ⋃ (_ : i ≤ km m), closure (ball (D i) (φ m))) ?_
    -- Closedness
    · simp [bigK]
      refine isClosed_iInter ?_
      intro n
      refine Finite.isClosed_biUnion ?_ ?_
      · refine Finite.ofFinset ?_ fun x ↦ ?_
        · exact (Finset.Iic (km (n+1)))
        · simp
          exact Eq.to_iff rfl
      intro i hi
      exact isClosed_closure
  exact fun μ a ↦ le_of_lt (bigcalc μ a)

-- lemma wat (h : ¬S = ∅): Nonempty S := by
--   exact nonempty_iff_ne_empty'.mpr h

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
