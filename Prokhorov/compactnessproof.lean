import Mathlib
-- import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
-- import Prokhorov.Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

--This stuff was in Algebra.InfiniteSum.Basic in a weird folder in my repo?
-- variable {α β : Type*} [TopologicalSpace α] [CommMonoid α]

-- @[to_additive (attr := simp)]
-- theorem tprod_ite_eq' (b : β) [DecidablePred (· = b)] (f : β → α) :
--     ∏' b', (if b' = b then f b' else 1) = f b := by
--   rw [tprod_eq_mulSingle b]
--   · simp
--   · intro b' hb'; simp [hb']
open TopologicalSpace MeasureTheory.ProbabilityMeasure Module

namespace ENNReal

@[simp] lemma nsmul_eq_mul (n : ℕ) (x : ℝ≥0∞) : n • x = n * x := by cases x <;> simp

end ENNReal

variable {G : Type*} [MetricSpace G] --[CompactSpace G] --Relax to PseudoEmetricSpace later?
  [MeasurableSpace G] [BorelSpace G]--[OpensMeasurableSpace G] --[T2Space G]
  --Iterestingly I need the T2 assumption on G to show the closure is also tight

namespace MeasureTheory
noncomputable section
instance psm : PseudoMetricSpace (LevyProkhorov <| ProbabilityMeasure G) :=
  levyProkhorovDist_pseudoMetricSpace_probabilityMeasure


open Topology Metric Filter Set ENNReal NNReal

variable (S : Set <| ProbabilityMeasure G)
--Useful version
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
      simp_all only [μ, inv_pow, ENNReal.smul_def, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
        false_and, not_false_eq_true, coe_inv, ENNReal.coe_pow, coe_ofNat,
        MeasurableSpace.measurableSet_top, Measure.sum_apply, Measure.smul_apply,
        Measure.dirac_apply', indicator, mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero,tsum_ite_eq]
      simp_rw [ENNReal.inv_pow, tsum_geometric, one_sub_inv_two, inv_inv, ofNat_lt_top]
    · simp
      convert f.2
      simpa using MemLp.coeFn_toLp (μ := μ) _
  invFun f := ⟨f, f.2⟩
  left_inv f := by ext : 1; simpa using MemLp.coeFn_toLp (μ := μ) _
  right_inv f := by simp


variable (a := Classical.choose (exists_dense_seq X))


-- theorem homeo_to_compact_space {X : Type*} [PseudoMetricSpace X] [SeparableSpace X] :
--     ∃ (T : X → Y), IsEmbedding T := by--Done
--       sorry

omit [MetricSpace G] [BorelSpace G] in
lemma ENNreal_ProbMeasure_toMeasure (μ : ProbabilityMeasure G) (A : Set G) :
    μ.toMeasure A = ((μ A) : ENNReal) := by
    exact Eq.symm (ennreal_coeFn_eq_coeFn_toMeasure μ A)

variable [MeasurableSpace X]  (μ : ProbabilityMeasure G)


variable [SecondCountableTopology G]
/-One direction is trivial-/
lemma Tight_closure_iff_tight (S : Set (ProbabilityMeasure G)) :
  IsTightMeasureSet {((μ : ProbabilityMeasure G) : Measure G) | μ ∈ S} ↔
  TightProb (closure S) := by
  constructor; swap
  · simp [TightProb]; intro hε; rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε εpos; specialize hε ε εpos; obtain ⟨K,hkCompact,hbound⟩ := hε
    use K; constructor
    · exact hkCompact
    intro μ hμ
    simp_all
    obtain ⟨μ1, hμ1, _, rfl⟩ := hμ
    specialize hbound μ1 <| subset_closure hμ1
    exact hbound
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
        rw [isOpen_compl_iff]; exact hc.isClosed
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

open TopologicalSpace Filter
open Encodable Function TopologicalSpace Topology
open scoped PiCountable unitInterval

omit [Nonempty X] in
theorem homeothingamajig : ∃ funn : X → ℕ → I, IsEmbedding funn := by sorry
--proven elsewhere and in process of PRing to Mathlib. Blocked by another PR

instance : PseudoEMetricSpace (ℕ → ↑I) := by
  sorry

instance : OpensMeasurableSpace (ℕ → ↑I) := Pi.opensMeasurableSpace

instance : PseudoMetricSpace (LevyProkhorov (ProbabilityMeasure (ℕ → I))) := sorry
  --levyProkhorovDist_pseudoMetricSpace_probabilityMeasure

instance levyProkhorovCompact : CompactSpace (LevyProkhorov (ProbabilityMeasure (ℕ → ↑I))) := by
  -- Almost proven given #28601
  sorry

lemma comp_iff_levprok_comp {S : Set <| ProbabilityMeasure G} : IsCompact S ↔ IsCompact {(( LevyProkhorov.equiv (μ : ProbabilityMeasure G)) : LevyProkhorov <| ProbabilityMeasure G) | μ ∈ S} := by sorry

lemma Compact_if_tight {S : Set (ProbabilityMeasure G)}
(ht : IsTightMeasureSet {((μ : ProbabilityMeasure G) : Measure G) | μ ∈ S}) :
  IsCompact (closure S) := by
  by_cases hempty : IsEmpty (closure S)
  · simp_all only [isEmpty_coe_sort, isClosed_empty, IsClosed.closure_eq,
    finite_empty, Finite.isCompact]
  rw [not_isEmpty_iff] at hempty
  rw [Tight_closure_iff_tight, TightProb] at ht
  obtain ⟨μ , hμ⟩ := hempty
  have tightness (ε : ENNReal) (hε : ε > 0):
    ∃ (K : Set G), IsCompact K ∧ μ Kᶜ ≤ ε := by
    specialize ht ε hε
    simp at ht
    obtain ⟨K,l,r⟩ := ht
    specialize r μ hμ
    use K
    constructor
    all_goals simpa
  haveI : MetricSpace (ProbabilityMeasure (ℕ → I)) :=
    metrizableSpaceMetric (ProbabilityMeasure (ℕ → ↑I))
  haveI topeq := levyProkhorov_eq_convergenceInDistribution (Ω := G)
  have h_compact : CompactSpace (ProbabilityMeasure (ℕ → I)) := by sorry
  --rw [PseudoMetrizableSpace.isCompact_iff_isSeqCompact]
  letI psms : PseudoMetricSpace (ProbabilityMeasure G) :=
    pseudoMetrizableSpacePseudoMetric (ProbabilityMeasure G)
  rw [UniformSpace.isCompact_iff_isSeqCompact (s := closure S)]
  intro μnseq hμnseq
  obtain ⟨T, hT⟩ := (homeothingamajig (X := G))
  let Y₀ := Set.range T
  have meas (n : ℕ) : (AEMeasurable T (μnseq n : Measure G)) := (Continuous.aemeasurable <| IsEmbedding.continuous hT)
  let v_n (n : ℕ) : ProbabilityMeasure (ℕ → I) := by
    let μ := μnseq n
    let aem : AEMeasurable T (μ : Measure G) :=
      Continuous.aemeasurable (IsEmbedding.continuous hT) --(μ : Measure G)
    exact μ.map (f := T) aem
  sorry
    --let v_n n: ProbabilityMeasure (ℕ → ↑I) := (μnseq n).map (f := T) (meas n) --(Continuous.aemeasurable <| IsEmbedding.continuous hT)--μnseq n (T⁻¹ (Y₀ ∩ ·))

  --def to_lp (μ : ProbabilityMeasure (ℕ → I)) : LevyProkhorov (ProbabilityMeasure (ℕ → I)) := (μ : LevyProkhorov (ProbabilityMeasure (ℕ → I)))
  -- def from_lp (μ_lp : LevyProkhorov (ProbabilityMeasure (ℕ → I))) : ProbabilityMeasure (ℕ → I) :=
  --   (LevyProkhorov.equiv (ProbabilityMeasure (ℕ → I))) μ_lp





  -- have homeo : ∃ T : G → Y, IsEmbedding T := homeo_to_compact_space
  -- obtain ⟨T, hT⟩ := homeo

  --let ν n : ProbabilityMeasure
  --rcases homeo with ⟨T,hT,l⟩
  --choose T using homeo

end
end MeasureTheory
