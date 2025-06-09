--import Mathlib
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
--import Mathlib.Topology.MetricSpace.Embedding
--import Mathlib.Topology.MetricSpace.HilbertCube
import Prokhorov.Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

open TopologicalSpace MeasureTheory.ProbabilityMeasure Module--Analysis

namespace ENNReal

@[simp] lemma nsmul_eq_mul (n : ℕ) (x : ℝ≥0∞) : n • x = n * x := by cases x <;> simp

end ENNReal

variable {G : Type*} [PseudoMetricSpace G] [CompactSpace G] [SeparableSpace G]
  [MeasurableSpace G] [OpensMeasurableSpace G] --[T2Space G]
  --Iterestingly I need the T2 assumption on G to show the closure is also tight

namespace MeasureTheory
noncomputable section
instance psm : PseudoMetricSpace (LevyProkhorov <| ProbabilityMeasure G) :=
  levyProkhorovDist_pseudoMetricSpace_probabilityMeasure


instance levyProkhorovCompact : CompactSpace (LevyProkhorov (ProbabilityMeasure G)) := by
  have hSeparability : SeparableSpace G := by infer_instance
  --let C : G → ℝ := Dual G
  -- instance : NormedSpace ℝ C(G, ℝ) :=
  sorry


--open scoped Interval MeasureTheory

open Topology Metric Filter Set ENNReal NNReal MeasureTheory.ProbabilityMeasure TopologicalSpace

def IsTightMeasureSet (S : Set (Measure G)) : Prop :=
  Tendsto (⨆ μ ∈ S, μ) (cocompact G).smallSets (𝓝 0)

variable (S : Set <| Measure G)
--Useful version
lemma IsTightMeasureSet_iff_exists_isCompact_measure_compl_le :
    IsTightMeasureSet S ↔ ∀ ε, 0 < ε → ∃ K : Set G, IsCompact K ∧ ∀ μ ∈ S, μ (Kᶜ) ≤ ε := by sorry


def TightProb (S : Set (ProbabilityMeasure G)) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set G, IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ ε

lemma Tightprob_iff_Tight {S : Set (ProbabilityMeasure G)} :
  TightProb S ↔ IsTightMeasureSet {((μ : ProbabilityMeasure G) : Measure G) | μ ∈ S} := by
  sorry

open Bornology
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {E : Type*}
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
def μ : Measure ℕ := Measure.sum (fun i => (2⁻¹  : NNReal)^i • Measure.dirac i)

@[simp]
lemma iUnion_pure : (⨆ i, pure i: Filter ℕ) = ⊤ := by
  ext i; constructor
  · intro hi;
    simp_all only [mem_iSup, mem_pure, mem_top]
    ext x
    simp_all only [mem_univ]
  · intro hi; simp_all only [mem_top, univ_mem]

@[simp] lemma ae_μ : ae μ = ⊤ := by
  simp [ae_eq_top]
  intro a
  simp[μ]

def equiv (s : Set (ℕ → ℝ)) (hs : ∃ t : Set ℝ, IsBounded t ∧ s ⊆ Set.univ.pi fun ℕ ↦ t) :
    s ≃ ((⇑) ⁻¹' s : Set (Lp ℝ 1 μ)) where
  toFun f := by
    refine ⟨MemLp.toLp f ?_, ?_⟩
    · simp [MemLp]
      constructor
      · measurability
      simp [eLpNorm, eLpNorm'];
      obtain ⟨bigset, bd, bigsetbound⟩ := hs
      rw [lintegral_countable']
      have (a) : ‖(f : ℕ → ℝ) a‖ₑ < ⊤ := by
        simp
      rw [@isBounded_iff_forall_norm_le] at bd
      obtain ⟨C, hC⟩ := bd
      have sdo : (∀ a, ‖(f : ℕ → ℝ) a‖ₑ ≤ (C.toNNReal)) := by
        intro a
        specialize hC ((f : ℕ → ℝ) a)
        have bob : (f : ℕ → ℝ) a ∈ bigset := by aesop
        specialize hC bob
        rw [Real.norm_eq_abs] at hC
        rw [@enorm_le_coe]
        exact NNReal.le_toNNReal_of_coe_le hC
      have mulrw : ∑' (a : ℕ), ‖(f : ℕ → ℝ) a‖ₑ * μ {a} ≤ ∑' (a : ℕ), C.toNNReal * μ {a} := by
        gcongr with a
        exact sdo a
      apply mulrw.trans_lt
      rw [ENNReal.tsum_mul_left]
      refine mul_lt_top (by simp) ?_
      simp [μ, indicator, ENNReal.smul_def]
      simp_rw [ENNReal.inv_pow, tsum_geometric, one_sub_inv_two, inv_inv, ofNat_lt_top]
    · simp
      convert f.2
      simpa using MemLp.coeFn_toLp (μ := μ) _
  invFun f := ⟨f, f.2⟩
  left_inv f := by ext : 1; simpa using MemLp.coeFn_toLp (μ := μ) _
  right_inv f := by simp

def Y : Set (Lp ℝ 1 μ) :=  (fun x => ⇑x)⁻¹' {f | ∀ n, f n ∈ Icc (0 : ℝ) 1}

lemma Compacty : CompactSpace Y := by
  sorry -- refine compactSpace_iff_isBounded_univ.mpr ?_ ?_

variable (a := Classical.choose (exists_dense_seq X))

-- def T (x : X) : Y := equiv {
--     val n := min 1 (dist x <| Classical.choose (exists_dense_seq X) n)
--     property := sorry
--   }

theorem homeo_to_compact_space {X : Type*} [MetricSpace X] [SeparableSpace X] :
    ∃ (T : X → Y), IsEmbedding T := by--Maybe build T explicitly first?
    -- obtain ⟨D, fD⟩ := TopologicalSpace.exists_countable_dense X
      sorry

omit [PseudoMetricSpace G] [CompactSpace G] [SeparableSpace G] [OpensMeasurableSpace G] in
lemma ENNreal_ProbMeasure_toMeasure (μ : ProbabilityMeasure G) (A : Set G) :
    μ.toMeasure A = ((μ A) : ENNReal) := by
    exact Eq.symm (ennreal_coeFn_eq_coeFn_toMeasure μ A)

/-One direction is trivial-/

variable [T2Space G]

lemma Tight_closure_iff_tight (S : Set (ProbabilityMeasure G)):
  IsTightMeasureSet {((μ : ProbabilityMeasure G) : Measure G) | μ ∈ S} ↔
  TightProb (closure S) := by
  constructor; swap
  · simp [TightProb]; intro hε; rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε εpos; specialize hε ε εpos; obtain ⟨K,hkCompact,hbound⟩ := hε
    use K; constructor
    · exact hkCompact
    intro μ hμ; simp at hμ
    obtain ⟨p,hp,hpμ⟩ := hμ
    specialize hbound p <| subset_closure hp
    rw [←hpμ]; exact hbound
  intro ht
  simp [TightProb]; intro ε hε
  rw [← Tightprob_iff_Tight, TightProb] at ht
  specialize ht ε hε
  obtain ⟨K,hc, htight⟩ := ht; use K
  constructor
  · simpa
  intro μ hμ
  obtain ⟨convseq, hconv_mem, hconv⟩ := mem_closure_iff_seq_limit.mp hμ
  have tightnesscalc := calc
    (μ.toMeasure Kᶜ)
    _ ≤ (liminf (fun k => (convseq k (Kᶜ))) atTop) := by
      rw [ENNreal_ProbMeasure_toMeasure]; norm_cast
      have hopen : IsOpen Kᶜ := by
        simp
        -- Note - I needed to add a Hausdorff assumption for this line
        -- (Maybe there is a way to avoid it)
        -- I only need to prove K is closed to apply the portmanteau theorem
        apply hc.isClosed
      have := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hopen
      simp_rw [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at this
      rw [←ofNNReal_liminf] at this;
      exact ENNReal.coe_le_coe.mp this
      use 1; simp; intro a x hb
      specialize hb x (by rfl)
      apply hb.trans; simp
    _ ≤ ε := by
      rw [ofNNReal_liminf]; apply Filter.liminf_le_of_le
      · use 0; simp
      simp only [eventually_atTop, ge_iff_le, forall_exists_index]
      intro b c h
      apply le_trans (h c le_rfl) <| htight (convseq c) <| hconv_mem c
      use 1; simp; intro a x hb
      specialize hb x (by rfl)
      apply hb.trans; simp
  exact tightnesscalc

lemma Compact_if_tight {S : Set (ProbabilityMeasure G)}
(ht : IsTightMeasureSet {((μ : ProbabilityMeasure G) : Measure G) | μ ∈ S}) :
  IsCompact (closure S) := by
  by_cases hempty : IsEmpty (closure S)
  · simp_all only [isEmpty_coe_sort, isClosed_empty, IsClosed.closure_eq,
    finite_empty, Finite.isCompact]
  rw [not_isEmpty_iff] at hempty
  rw [@IsTightMeasureSet_iff_exists_isCompact_measure_compl_le] at ht
  obtain ⟨μ , hμ⟩ := hempty
  have tightness (ε : ENNReal) (hε : ε > 0):
    ∃ (K : Set G), IsCompact K ∧ μ K ≥ 1 - ε := by
    specialize ht ε hε
    simp at ht
    sorry
  sorry
