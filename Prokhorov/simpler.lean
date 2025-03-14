import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.IntervalIntegral -- Assuming relevant modules are available
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Defs
--set_option maxHeartbeats 400000
--set_option diagnostics true

open Topology Metric Filter Set ENNReal NNReal ProbabilityMeasure TopologicalSpace

namespace MeasureTheory

open scoped Topology ENNReal NNReal BoundedContinuousFunction

-- This has been proved by Yaël and will be in Mathlib soon. PR: #22659
lemma eq_of_forall_nnreal_iff {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r ≤ x ↔ ↑r ≤ y) : x = y :=
  le_antisymm (le_of_forall_nnreal_lt fun _r hr ↦ (h _).1 hr.le)
    (le_of_forall_nnreal_lt fun _r hr ↦ (h _).2 hr.le)

lemma ofNNReal_liminf {ι : Type*} {f : Filter ι} {u : ι → ℝ≥0} (hf : f.IsCoboundedUnder (· ≥ ·) u) :
    liminf u f = liminf (fun i ↦ (u i : ℝ≥0∞)) f := by
  sorry

-- This too in #22877
variable {Ω : Type*} [MeasurableSpace Ω] in
protected lemma ProbabilityMeasure.tendsto_measure_iUnion_accumulate {ι : Type*} [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] {μ : ProbabilityMeasure Ω} {f : ι → Set Ω} :
    Tendsto (fun i ↦ μ (Accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.tendsto_coe]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure)

--And this in #22903:
lemma toReal_liminf {ι : Type*} {f : Filter ι} {u : ι → ℝ≥0} :
  liminf (fun i ↦ (u i : ℝ)) f = liminf u f := by
  sorry


variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] -- may change this to EMetric later
[OpensMeasurableSpace Ω] [SeparableSpace Ω] --[∀ i, μ i : Measure Ω] {P : MeasurableSpace Ω}
variable {μ : ℕ → Set Ω → ℝ}



noncomputable section

--def compactsetofmeasures := {X : Set (ProbabilityMeasure Ω) // IsCompact X}

variable (S : Set (ProbabilityMeasure Ω)) --(S : Set (ProbabilityMeasure Ω)) --

abbrev P := LevyProkhorov.equiv (ProbabilityMeasure Ω)

abbrev T := P⁻¹' S

theorem prob_tendsto_measure_iUnion_accumulate {α ι : Type*}
    [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
    {_ : MeasurableSpace α} {μ : Measure α} {f : ι → Set α} :
    Tendsto (fun i ↦ μ (Accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [measure_iUnion_eq_iSup_accumulate]
  exact tendsto_atTop_iSup fun i j hij ↦ by gcongr


lemma claim5point2 (U : ℕ → Set Ω) (O : ∀ i, IsOpen (U i)) --(T : Set (LevyProkhorov (ProbabilityMeasure Ω)))
    (hcomp: IsCompact (closure S)) (ε : ℝ) (heps : ε > 0) (Cov : ⋃ i, U i = univ):
    ∃ (k : ℕ), ∀ μ ∈ S, μ (⋃ (i ≤ k), U i) > 1 - ε := by
  by_contra! nh
  choose μ hμ hμε using nh
  --exact hcomp.mem_of_is_closed (IsClosed.closure hcomp.is_closed)
  obtain ⟨μnew, hμtwo, sub, tub, bub⟩ := hcomp.isSeqCompact (fun n =>  subset_closure <| hμ n)
  have thing n := calc
    (μnew (⋃ (i ≤ n), U i) : ℝ)
    _ ≤ liminf (fun k => (μ (sub k) (⋃ (i ≤ n), U i) : ℝ)) atTop := by
      have hopen : IsOpen (⋃ i, ⋃ (_ : i ≤ n), U i) := by
        exact isOpen_biUnion fun i a => O i
      --This is the key lemma
      have := ProbabilityMeasure.le_liminf_measure_open_of_tendsto bub hopen
      simp only [Function.comp_apply] at this
      simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
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
      exact ProbabilityMeasure.apply_le_one (μ (sub x)) (⋃ i, ⋃ (_ : i ≤ n), U i)
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
        exact ProbabilityMeasure.apply_le_one (μ (sub d)) (⋃ i, ⋃ (_ : i ≤ sub d), U i)
    _ ≤ 1 - ε := by
      apply Filter.liminf_le_of_le
      · use 0
        simp
      · simp only [eventually_atTop, ge_iff_le, forall_exists_index]
        intros b c h
        refine le_trans (h c le_rfl) (hμε _)
  have cdiction : Tendsto (fun n => μnew (⋃ i ≤ n, U i)) atTop (𝓝 1) := by
    have re : Tendsto (fun n => μnew (⋃ i, ⋃ (_ : i ≤ n), U i)) atTop (𝓝 (μnew (⋃ i, U i))) := by
      -- congr
      simp_rw [←Set.accumulate_def]
      exact ProbabilityMeasure.tendsto_measure_iUnion_accumulate
    rw [Cov] at re
    simp at re
    exact re


  have oop : ∀ᶠ n in atTop, μnew (⋃ i, ⋃ (_ : i ≤ n), U i) ≥ 1 - ε / 2 := by
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



-- lemma fivepoint3 {MeasurableSpace X} (MetricSpace X)  (h : IsCompact X) : (inferInstance : TopologicalSpace (LevyProkhorov (ProbabilityMeasure X))) := by
--   sorry


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






      -- Stuff from trying to prove union of i < n tends to union of i
      -- apply Filter.Tendsto.comp ?_ ?_
      -- exact Filter.sInf fun a => S μnew
      -- rw [Cov]
      -- simp only [ProbabilityMeasure.coeFn_univ]


      -- rw [Filter.tendsto_atTop']
      -- rw [Cov]
      -- simp only [ProbabilityMeasure.coeFn_univ]
      -- intro s hs


      --rw [Tendsto]

      -- refine map_le_iff_le_comap.mpr ?one
      -- rw [Cov]
      -- simp only [ProbabilityMeasure.coeFn_univ]

      -- have hm : Monotone (fun n => ⋃ i ≤ n, U i) := by
      --   intro a b h
      --   refine le_iff_subset.mpr ?_
      --   sorry

      --norm_push
      -- refine tendsto_measure_iUnion_atTop ?_


      --intro blob a
      --rw [tendsto_map'_iff]


-- lemma ofReal_liminf {ι : Type*} {l : Filter α} {f : α → ℝ≥0} (hf : l.IsCoboundedUnder (· ≥ ·) f) :
--     liminf f l = liminf (fun i ↦ (f i : ℝ)) l := by
--   sorry
