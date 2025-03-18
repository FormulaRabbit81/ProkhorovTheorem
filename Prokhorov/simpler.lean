import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.IntervalIntegral -- Assuming relevant modules are available
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Defs
--set_option maxHeartbeats 400000
--set_option diagnostics true
set_option linter.style.longLine false

open Topology Metric Filter Set ENNReal NNReal ProbabilityMeasure TopologicalSpace

namespace MeasureTheory

open scoped Topology ENNReal NNReal BoundedContinuousFunction

-- This has been proven by Yaël in #22877
variable {X : Type*} [MeasurableSpace X] in
protected lemma ProbabilityMeasure.tendsto_measure_iUnion_accumulate {ι : Type*} [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] {μ : ProbabilityMeasure X} {f : ι → Set X} :
    Tendsto (fun i ↦ μ (Accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.tendsto_coe]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure)

--And this in #22903:
lemma toReal_liminf {ι : Type*} {f : Filter ι} {u : ι → ℝ≥0} :
  liminf (fun i ↦ (u i : ℝ)) f = liminf u f := by
  sorry


variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] -- may change this to EMetric later
[OpensMeasurableSpace X] [SeparableSpace X]


noncomputable section

--def compactsetofmeasures := {X : Set (ProbabilityMeasure X) // IsCompact X}

variable (S : Set (ProbabilityMeasure X))

abbrev P := LevyProkhorov.equiv (ProbabilityMeasure X)

abbrev T := P⁻¹' S

theorem prob_tendsto_measure_iUnion_accumulate {α ι : Type*}
    [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
    {_ : MeasurableSpace α} {μ : Measure α} {f : ι → Set α} :
    Tendsto (fun i ↦ μ (Accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [measure_iUnion_eq_iSup_accumulate]
  exact tendsto_atTop_iSup fun i j hij ↦ by gcongr


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


variable [CompleteSpace X]

theorem IsTightFamily_of_isRelativelyCompact [Nonempty X] (hcomp : IsCompact (closure S)) :
    TightProb S := by
  -- Introduce ε > 0 for which we need to find a compact set K with μ(K) ≥ 1 - ε for all μ ∈ S
  intro ε εpos
  obtain ⟨D, fD⟩ := exists_dense_seq X
  -- For each m ≥ 1, cover X with balls of radius 1/m around points in the dense subset D
  have hcov : ∀ m : ℝ, m ≥ 1 → ⋃ i, ball (D i) (1 / m) = univ := by
    rw [denseRange_iff] at fD
    intro m hm
    ext p
    constructor
    · exact fun a ↦ trivial
    specialize fD p
    specialize fD (1 / m)
    intro hp
    specialize fD (by positivity)
    exact mem_iUnion.mpr fD

  have byclam : ∀ μ ∈ S, ∀ (m : ℤ), m ≥ 1 → ∃ (k : ℕ), μ (⋃ i ≤ k, ball (D i) (1 / m)) > 1 - (ε * 2 ^ (-m)) := by
    intro μ hμ m hm
    let ε' := ε.toReal * 2 ^ (-m)
    have fiveee : ∃ (k : ℕ), ∀ μ ∈ S, μ (⋃ (i ≤ k), ball (D i) (1 / m)) > 1 - ε' := by
      apply claim5point2 (S := S) (U := fun i => ball (D i) (1 / m)) (ε := ε') (heps := _)
      · exact fun i ↦ isOpen_ball
      · exact hcomp
      · simp_all only [ge_iff_le, one_div]
        sorry -- easy by dnsity of D
      · intro O hcomp_1
        simp_all only [ge_iff_le, one_div, gt_iff_lt, ε']
        by_cases h : ε = ⊤
        · sorry
        · sorry
    sorry --have inq : ε.toReal < ε.toReal * 2 ^ (-m) := by
  have := byclam
  choose k hk m using this
  constructor
  swap
  set bigK := ⋂ _ ≥ 1, ⋃ i ≤ l, closure (ball (D i) (1 / (_ : ℝ)))
  let μ :=  ∈ S



      --specialize hcov m
  use bigK
  have kcomp : IsCompact bigK := by
    sorry
      -- apply IsCompact_Inter
      -- · exact fun i ↦ IsCompact_Union fun _ ↦ IsCompact_closure
      -- · exact fun i ↦ IsClosed
  have bigcalc μ := calc
    μ bigKᶜ
    _ = μ (⋃ m, ⋃ (i ≤ k), closure (ball (D i) (1 / m))ᶜ) := by sorry
    _ ≤ ∑ m μ (⋃ (i ≤ k), closure (ball (D i) (1 / m))ᶜ) := by sorry
    _ = ∑ m (1 - μ (⋃ (i ≤ k), closure (ball (D i) (1 / m)))) := by sorry
    _ < ∑ m ε 2 ^ (-m) := by sorry
    _ = ε := by sorry
    exact bigcalc



    have fivpoint : ∀ (m : ℝ), ∀ μ ∈ S, m ≥ 1 → ∃ k, ↑(μ (⋃ i, ⋃ (_ : i ≤ k), ball (D i) (1 / m))) > 1 - ε * 2 ^ (-m) := by
      intro m
      sorry
    intro m μ hμ
    --obtain ⟨k⟩ := claim5point2 _ _ _
    --rw [→claim5point2] at hcov

-- lemma fivepoint3 {MeasurableSpace X} (MetricSpace X)  (h : IsCompact X) : (inferInstance : TopologicalSpace (LevyProkhorov (ProbabilityMeasure X))) := by
--   sorry


theorem Prokhorov (G : Set (ProbabilityMeasure X)) [PseudoMetricSpace (Measure X)]:
   (TightProb G) ↔ (IsCompact (closure G)) := by
   sorry

end section
end
end MeasureTheory
