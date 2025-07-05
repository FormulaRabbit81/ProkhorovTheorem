import Mathlib

open TopologicalSpace Classical Filter Set Topology

variable {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
--Note we need to handle the empty case sometime too

--def Z n := ℕ → Icc (0:ℝ) 1
--lemma compactness : CompactSpace (ℕ → Icc 0 1) := compactSpace

noncomputable section
def D : ℕ → X := choose (exists_dense_seq X)

variable (X) in
def T_func : ℕ → X → Icc (0:ℝ) 1 := fun n x ↦
  projIcc (0:ℝ) 1 zero_le_one (dist x (D n))

instance what : TopologicalSpace (Icc (0:ℝ) 1)  := instTopologicalSpaceSubtype
instance whatt : TopologicalSpace X := UniformSpace.toTopologicalSpace

lemma continuous_T (n : ℕ): Continuous (T_func X n) := by
  sorry

lemma separating_T : Pairwise fun x y ↦ ∃ n, T_func X n x ≠ T_func X n y := by sorry

-- lemma isEmbedding_toPiNaticc :
--     IsEmbedding (toPiNat : X → PiNatEmbed X (fun n => Icc 0 1) T_func) := by
--     sorry
