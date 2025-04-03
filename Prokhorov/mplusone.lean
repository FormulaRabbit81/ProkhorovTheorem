import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
set_option linter.style.longLine false

open Topology Metric Filter Set ENNReal NNReal MeasureTheory.ProbabilityMeasure TopologicalSpace

namespace MeasureTheory

open scoped Topology ENNReal NNReal BoundedContinuousFunction



variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] -- may change this to EMetric later
[OpensMeasurableSpace X] [SeparableSpace X]


noncomputable section

variable (S : Set (ProbabilityMeasure X))

abbrev P := LevyProkhorov.equiv (ProbabilityMeasure X)

abbrev T := P⁻¹' S


lemma claim5point2 (U : ℕ → Set X) (O : ∀ i, IsOpen (U i))
    (hcomp: IsCompact (closure S)) (ε : ℝ) (heps : ε > 0) (Cov : ⋃ i, U i = univ):
    ∃ (k : ℕ), ∀ μ ∈ S, μ (⋃ (i ≤ k), U i) > 1 - ε := by
  by_contra! nh
  choose μ hμ hμε using nh
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
      simp_rw [←Set.accumulate_def]
      exact ProbabilityMeasure.tendsto_measure_iUnion_accumulate
    rw [Cov] at re
    simp at re
    exact re

  have oop : ∀ᶠ n in atTop, μnew (⋃ i ≤ n, U i) ≥ 1 - ε / 2 := by
    --rw [tendsto_atTop_nhds] at cdiction
    apply Tendsto.eventually_const_le (v := 1)
    norm_num
    positivity
    rw [←NNReal.tendsto_coe] at cdiction
    exact cdiction

  suffices ∀ᶠ n : ℕ in atTop, False by exact this.exists.choose_spec
  filter_upwards [oop] with n hn
  have whatever := hn.trans (thing n)
  linarith

-- Definition taken from Rémy's Repository but modified to use ProbabilityMeasure instead of measure. - Need to change this later
def TightProb (S : Set (ProbabilityMeasure X)) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ ε

omit [OpensMeasurableSpace X] [SeparableSpace X] in lemma tightProb_iff_nnreal {S : Set (ProbabilityMeasure X)} :
    TightProb S ↔ ∀ ε : ℝ≥0, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ ε := by
  simp [TightProb, ENNReal.forall_ennreal, ←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact fun _ ↦ ⟨∅, isCompact_empty⟩


variable [CompleteSpace X]

-- lemma nnreal_tsum_thing {μ : ProbabilityMeasure X} (f : ℕ → Set X) (hf : Summable fun n ↦ μ (f n)) :
--     μ (⋃ n, f n) ≤ ∑' n, μ (f n) := by
--     let ν : Measure X := μ
--     have h_ineq_ennreal : ν (⋃ n, f n) ≤ ∑' n, ν (f n) := by
--       apply MeasureTheory.measure_iUnion_le f
--     have ν_finite : ∀ (s : Set X), ν s ≠ ∞ := by exact fun s ↦ measure_ne_top ν s
--     have ν_eq_ofNNReal : ∀ (s : Set X), μ s = ENNReal.ofNNReal (μ s) := by
--       intro s
--       rfl
--     rw [← @ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn]



lemma nnreal_tsum_thing {μ : ProbabilityMeasure X} (f : ℕ → Set X) (hf : Summable fun n ↦ μ (f n)) :
    μ (⋃ n, f n) ≤ ∑' n, μ (f n) := by
    let ν : Measure X := ↑μ
    have h_ineq_ennreal : ν (⋃ n, f n) ≤ ∑' n, ν (f n) := by
      exact MeasureTheory.measure_iUnion_le f
    -- have coerce : ENNReal.ofNNReal (μ (⋃ n, f n)) ≤ ∑' n, ENNReal.ofNNReal (μ (f n)) := by
    rw [← @ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn]
    sorry


    -- simp_rw [ProbabilityMeasure.coe_ennreal_eq_ofNNReal μ] at h_ineq_ennreal
    -- rw [← @ProbabilityMeasure.coeFn_comp_toFiniteMeasure_eq_coeFn]

    --choose! coerce using id ν_eq_ofNNReal


    -- simp_rw [ν_eq_ofNNReal] at h_ineq_ennreal
    -- rw [← ν_eq_ofNNReal] at h_ineq_ennreal

    -- have newting : ν (⋃ n, f n) ≤ ∑' (n : ℕ), μ (f n) := by


    -- exact le_of_ofNNReal_le_ofNNReal h_ineq_ennreal


  --refine measure_iUnion_le (ι := ℕ) ?_
  -- refine NNReal.coe_le_coe.mp ?_
  -- refine (Real.le_toNNReal_iff_coe_le ?_).mp ?_
  -- · exact zero_le_coe
  -- · sorry
  -- apply measure_biUnion_le (μ := μ.toMeasure) (s := f)


theorem IsTightFamily_of_isRelativelyCompact [Nonempty X] (hcomp : IsCompact (closure S)) :
    TightProb S := by
  rw [tightProb_iff_nnreal]
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

  have byclam : ∀ μ ∈ S, ∀ (m : ℕ), ∃ (k : ℕ), μ (⋃ i ≤ k, ball (D i) (φ m)) > 1 - (ε * 2 ^ (-m : ℤ) : ℝ) := by
    intro μ hμ m
    -- I am sure there is an easier way to do this
    let m' := m + 1
    let ε' := (ε * 2 ^ (-m : ℤ)).toReal
    have fiveee : ∃ (k : ℕ), ∀ μ ∈ S, μ (⋃ (i ≤ k), ball (D i) (φ m)) > 1 - ε' := by
      apply claim5point2 (S := S) (U := fun i => ball (D i) (φ m)) (ε := ε') (heps := _)
      · exact fun i ↦ isOpen_ball
      · exact hcomp
      · simp_all only [ge_iff_le, one_div]
      · intro O hcomp_1
        simp_all only [gt_iff_lt, ε']
        simp [εpos]
    obtain ⟨w, h⟩ := fiveee
    use w
    exact h μ hμ

  choose! km hbound using id byclam
  simp_all only [zpow_neg, zpow_natCast]
  let bigK μ := ⋂ m, ⋃ (i ≤ km μ m+1), closure (ball (D i) (φ m))
  have bigcalc (μ : ProbabilityMeasure X) (hs : μ ∈ S) := calc
    μ (bigK μ)ᶜ
    _ = μ (⋃ m,(⋃ (i ≤ km μ m+1), closure (ball (D i) (φ m+1)))ᶜ) := by
      simp only [bigK]
      simp --∑' m : ℕ, if m > 1 then (1 / (m ^ 2 : ℝ) else 0
    -- _ = μ (⋃ m, ⋃ (i ≤ km μ m), closure (ball (D i) (φ m))ᶜ) := by
    --   -- congr
    --   refine DFunLike.congr rfl ?_
    --   ext x
    --   constructor
    --   · intro hx

      sorry

    _ ≤ ∑' m, μ ((⋃ (i ≤ km μ m+1), closure (ball (D i) (φ m+1)))ᶜ) := by
      --simp_all only [ge_iff_le, one_div, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, gt_iff_lt, compl_iUnion, bigK]
      simp


      apply nnreal_tsum_thing
      rw [@summable_iff_not_tendsto_nat_atTop]
      refine not_tendsto_iff_exists_frequently_nmem.mpr ?_
      have eq : ∑' m, μ ((⋃ (i ≤ km μ m+1), closure (ball (D i) (φ m+1)))ᶜ) = ∑' m, (1 - μ (⋃ (i ≤ km μ m+1), closure (ball (D i) (φ m+1)))) := by
        have compl : ∑' m, μ ((⋃ (i ≤ km μ m), closure (ball (D i) (φ m)))ᶜ) = ∑' m, (μ univ - μ (⋃ (i ≤ km μ m), closure (ball (D i) (φ m+1)))) := by
          refine tsum_eq_tsum_of_hasSum_iff_hasSum ?_
          -- rw [measure_compl (s := (⋃ i, ⋃ (_ : i ≤ km μ _), closure (ball (D i) (φ _)))) (μ := μ)]
          sorry
        sorry
      sorry

      --convert MeasureTheory.measure_iUnion_le _ (ι := ℕ) (α := X) (μ := μ.toMeasure)

    _ = ∑' m, (1 - μ (⋃ (i ≤ km μ m+1), closure (ball (D i) (φ m+1)))) := by sorry
    _ < (∑' (m : ℕ), ε * 2 ^ (-(1+m) : ℤ) : NNReal) := by sorry
    _ = ε := by
      simp
      rw [NNReal.tsum_mul_left]
      nth_rw 2 [←mul_one (a :=ε)]
      refine (NNReal.mul_eq_mul_left ?_).mpr ?_
      · exact pos_iff_ne_zero.mp εpos
      · have frac : ∑' (x : ℕ), 2 ^ (-(x : ℝ) + -1) = ∑' (x : ℕ), (1 / 2) ^ (x + 1) := by
          rw [HPow]
          sorry
        sorry
        sorry
        -- apply tsum_geometric_of_lt_one
  sorry


-- lemma fivepoint3 {MeasurableSpace X} (MetricSpace X)  (h : IsCompact X) : (inferInstance : TopologicalSpace (LevyProkhorov (ProbabilityMeasure X))) := by
--   sorry


theorem Prokhorov (G : Set (ProbabilityMeasure X)) [PseudoMetricSpace (Measure X)]:
   (TightProb G) ↔ (IsCompact (closure G)) := by
   sorry

end section
end
end MeasureTheory
--#min_imports
