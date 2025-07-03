import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic

section MetricSpace
open TopologicalSpace Classical Filter Function Topology

variable [MetricSpace X] [SeparableSpace X]

lemma isEmbedding_toPiNat (continuous_f : ∀ n, Continuous (f n))
    (separating_f : Pairwise fun x y ↦ ∃ n, f n x ≠ f n y) :
    IsEmbedding (toPiNat : X → PiNatEmbed X Y f) := by
  letI metspace := metricSpace separating_f
  rw [isEmbedding_iff, isInducing_iff_nhds]
  refine ⟨fun x ↦ ((continuous_toPiNat continuous_f).tendsto x).le_comap.antisymm ?_,
    (toPiNatEquiv X Y f).injective⟩
  simp_rw [Filter.le_def, mem_nhds_iff]
  rintro S ⟨ε, hε, hεs⟩
  refine ⟨ofPiNat ⁻¹' S, ?_, .rfl⟩
  by_cases hempt : IsEmpty X
  · refine preimage_nhds_coinduced ?_
    simp
    rw [← Set.singleton_subset_iff]
    have klj : {x} ⊆ ball x ε := by
      simp only [Set.singleton_subset_iff, mem_ball, dist_self]
      exact hε
    exact klj.trans hεs -- Empty case
  rw [not_isEmpty_iff] at hempt
  --let D : ℕ → X := choose (exists_dense_seq X)
  --let α : ℕ → X → ℝ := fun n x => min (dist x <| D n) 1
  refine ContinuousAt.preimage_mem_nhds ?_ ?_
  · refine Continuous.continuousAt ?_
    refine SeqContinuous.continuous ?_
    intro Tn limTn hconvTn


    --from continuity of f? No
  simp
  rw [mem_nhds_iff]
  use ε

  --simp [ofPiNat];
  --rw [@mem_nhds_iff];
  -- refine eventually_nhds_iff_ball.mp ?_
  -- rw [eventually_iff_seq_eventually]
  -- intro zn htendszn
  -- refine tendsto_principal.mp ?_
  -- have Function.injective f := by


  -- use 2 * ε; constructor
  --· norm_num; exact hε
  --refine Set.image_subset_iff.mp ?_


  by_contra!


  rw [Metric]
  refine ⟨fun x ↦ ?_, (toPiNatEquiv X Y f).injective⟩


  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨continuous_toPiNat continuous_f, (toPiNatEquiv X Y f).bijective⟩

end MetricSpace
end MetricSpace
end Metric.PiNatEmbed
