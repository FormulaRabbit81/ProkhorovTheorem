/- This code is not mine, and comes from https://github.com/janemms/BanachAlaoglu-/
import Mathlib

open Function

section Metrizability_lemma

variable {X : Type*} {E : ℕ → Type*} [TopologicalSpace X] [CompactSpace X] [∀ n, NormedAddCommGroup (E n)]
variable (gs : ∀ n, X → E n)
variable (gs_cont : ∀ n, Continuous (gs n))
variable (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y))

private noncomputable def ourMetric (x y : X) : ℝ :=
  ∑' n, (1/2)^n * min ‖gs n x - gs n y‖ 1

variable {gs}

lemma ourMetric_bdd {x y} : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * min ‖gs n x - gs n y‖ 1) i‖
            ≤ (fun n ↦ (1 / 2) ^ n) i) := by
          intro i
          simp [add_nonneg, abs_of_nonneg]

lemma summable_if_bounded {x y} : Summable fun n ↦ (1 / 2) ^ n * min ‖gs n x - gs n y‖ 1 :=
  Summable.of_norm_bounded (fun n ↦ (1 / 2) ^ n) summable_geometric_two (ourMetric_bdd)

lemma ourMetric_self_iff : ∀ {x y : X}, ourMetric gs x y = 0 ↔ x = y := by
  intro x y
  constructor
  · intro sum
    rw [ourMetric] at sum

    have sum_zero : ∑' n, (1/2)^n * min ‖gs n x - gs n y‖ 1 = 0 → ∀ n, (1/2)^n * min ‖gs n x - gs n y‖ 1 = 0 := by
      have tsum_zero (g : ℕ → ℝ) (h : ∀ (i : ℕ), g i ≥ 0) (h' : Summable g) :
          ∑' (i : ℕ), g i = 0 ↔ ∀ (i : ℕ), g i = 0 := by
        calc
          _ ↔ HasSum g 0 := (Summable.hasSum_iff h').symm
          _ ↔ g = 0 := hasSum_zero_iff_of_nonneg h
          _ ↔ _ := Function.funext_iff

      intro sum
      let f := fun n ↦ (1/2)^n * min ‖gs n x - gs n y‖ 1

      have terms_pos n : f n >= 0 := by positivity
      apply (tsum_zero (fun n ↦ (1/2)^n * min ‖gs n x - gs n y‖ 1) (terms_pos) summable_if_bounded).mp

      exact sum

    apply sum_zero at sum
    simp only [one_div, inv_pow, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      ne_eq, false_and, norm_eq_zero, sub_eq_zero, false_or] at sum
    contrapose! sum

    have blah : ∃ n: ℕ, min ‖gs n x - gs n y‖ 1 ≠ 0 := by
      specialize gs_sep sum
      simp only [Set.mem_range, ne_eq, exists_exists_eq_and] at gs_sep
      obtain ⟨a, gs_neq⟩ := gs_sep
      use a
      by_contra h
      cases' le_or_lt ‖gs a x - gs a y‖ 1 with h1 h2
      · rw [min_eq_left_iff.mpr h1, norm_eq_zero, sub_eq_zero] at h
        simp only [one_div, inv_pow, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff',
          OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at *
        exact gs_neq h
      · rw [min_eq_right_iff.mpr (LT.lt.le h2)] at h
        linarith

    exact blah

  · intro x_eq_y
    simp [ourMetric, one_div, inv_pow, x_eq_y, sub_self, norm_zero, mul_zero, tsum_zero]

lemma ourMetric_comm : ∀ x y : X, ourMetric gs x y = ourMetric gs y x := by
  intro x y
  unfold ourMetric
  rw [tsum_congr]
  intro b
  rw [norm_sub_rev (gs b x) (gs b y)]

lemma ourMetric_triangle : ∀ x y z : X, ourMetric gs x z ≤ ourMetric gs x y + ourMetric gs y z := by
  intro x y z
  unfold ourMetric

  have plusminus_eq_self : ∀ n, ‖gs n x - gs n z‖ = ‖gs n x + (gs n y - gs n y) - gs n z‖ := by
    intro n
    simp only [sub_self, add_zero]

  simp_rw [plusminus_eq_self]

  have min_tri {n} : ∀ a b : (E n), min ‖a + b‖ 1 ≤ min ‖a‖ 1 + min ‖b‖ 1 := by
    intro a b
    simp only [sub_self, add_zero, implies_true, min_le_iff]
    cases' le_or_lt ‖a+b‖ 1 with h1 h2
    · left
      cases' le_or_lt ‖a‖ 1 with g1 g2
      · cases' le_or_lt ‖b‖ 1 with j1 j2
        · rw [min_eq_left_iff.mpr g1, min_eq_left_iff.mpr j1]
          exact norm_add_le a b
        · rw [min_eq_left_iff.mpr g1, min_eq_right_iff.mpr (LT.lt.le j2), add_comm ‖a‖ 1]
          exact le_add_of_le_of_nonneg h1 (by positivity)

      · cases' le_or_lt ‖b‖ 1 with j1 j2
        · rw [min_eq_right_iff.mpr (LT.lt.le g2), min_eq_left_iff.mpr j1]
          exact le_add_of_le_of_nonneg h1 (by positivity)
        · rw [min_eq_right_iff.mpr (LT.lt.le g2), min_eq_right_iff.mpr (LT.lt.le j2)]
          linarith

    · right
      cases' le_or_lt ‖a‖ 1 with g1 g2
      · cases' le_or_lt ‖b‖ 1 with j1 j2
        · rw [min_eq_left_iff.mpr g1, min_eq_left_iff.mpr j1]
          linarith [norm_add_le a b]

        · rw [min_eq_left_iff.mpr g1, min_eq_right_iff.mpr (LT.lt.le j2), add_comm ‖a‖ 1]
          norm_num

      · cases' le_or_lt ‖b‖ 1 with j1 j2
        · rw [min_eq_right_iff.mpr (LT.lt.le g2), min_eq_left_iff.mpr j1]
          norm_num
        · rw [min_eq_right_iff.mpr (LT.lt.le g2), min_eq_right_iff.mpr (LT.lt.le j2)]
          linarith



  have tri_ineq : ∀ n, (1/2)^n * min ‖gs n x - gs n z‖ 1 ≤ (1/2)^n * min ‖gs n x - gs n y‖ 1 + (1/2)^n * min ‖gs n y - gs n z‖ 1 := by
    intro n
    rw [← mul_add]
    apply (mul_le_mul_left _).mpr
    simp only [plusminus_eq_self]
    rw [← add_comm_sub, add_sub_assoc (gs n x - gs n y) (gs n y) (gs n z)]
    apply min_tri
    positivity
  have := @tsum_add ℝ ℕ _ _ (fun n ↦ (1/2)^n * min ‖gs n x - gs n y‖ 1) (fun n ↦ (1/2)^n * min ‖gs n y - gs n z‖ 1) _ _
  --simp only [inv_pow] at this
  rw [← this]
  simp only [← mul_add]
  apply tsum_le_tsum
  · intro i
    rw [← plusminus_eq_self, mul_add]
    exact tri_ineq i
  · simp only [inv_pow, sub_self, add_zero]
    exact summable_if_bounded
  · simp only [mul_add]
    exact Summable.add summable_if_bounded summable_if_bounded

  exact summable_if_bounded
  exact summable_if_bounded

noncomputable def ourMetricSpace : MetricSpace X where
  dist := ourMetric gs
  dist_self := by
    intro x
    exact (ourMetric_self_iff gs_sep ).mpr rfl
  dist_comm := ourMetric_comm
  dist_triangle := ourMetric_triangle
  edist_dist := by simp only [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk, implies_true]
  eq_of_dist_eq_zero := by
    intro x y
    exact (ourMetric_self_iff gs_sep).mp

def kopio (X :Type*) (gs : ∀n, X → E n) (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y))
    := X

def kopio.mk (X :Type*) (gs : ∀n, X → E n) (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)) :
    X → kopio X gs gs_sep := id

def kopio.toOrigin (X :Type*) (gs : ∀n, X → E n) (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)) :
    kopio X gs gs_sep → X := id

noncomputable instance : MetricSpace (kopio X gs gs_sep) := ourMetricSpace gs_sep

--example (f : X → ℝ) (g : X → ℝ) (hf : Continuous f) (hg : Continuous g) : Continuous ((f + g) : X × X → ℝ ) := by sorry

lemma cont_ourMetric (gs_cont : ∀ (n : ℕ), Continuous (gs n)) : Continuous (fun (p : X × X) ↦
    ourMetric gs p.1 p.2) := by

  apply @continuous_tsum ℕ (X × X) ℝ _ _ (fun (n : ℕ) ↦ (1 / 2) ^ n) _
      (fun n ↦ fun (x, y) ↦ (1 / 2) ^ n * min ‖gs n x - gs n y‖ 1) ?_ (summable_geometric_two) ?_
  · intro i
    simp only [one_div, inv_pow]
    have cont_xy : ∀ i : ℕ, Continuous (fun (x,y) ↦ ‖gs i x - gs i y‖) := by
      intro i
      have : Continuous (fun (x,y) ↦ gs i x - gs i y) := by
        exact Continuous.sub (by exact Continuous.fst' (gs_cont i)) (Continuous.snd' ((gs_cont i)))
        --ring_nf at this



      exact Continuous.norm this
    have foo n := @Continuous.min ℝ (X×X) _ _ _ (fun (x,y) ↦ ‖gs n x - gs n y‖) (fun (_,_) ↦ 1) _ (cont_xy n) (continuous_const)
    simp at foo
    have loo n := @Continuous.mul ℝ (X×X) _ _ _ _ (fun x ↦ (1 / 2) ^ n) (fun (x,y) ↦ min ‖gs n x - gs n y‖ 1) (continuous_const) (foo n)
    simp at loo
    simp_all only [implies_true]

  · simp only [inv_pow, norm_mul, norm_inv, norm_pow, RCLike.norm_ofNat, norm_norm,
    Prod.forall]
    intro n a b
    simp only [one_div, norm_inv, RCLike.norm_ofNat, inv_pow, mul_comm]
    rw [mul_le_iff_le_one_left]
    · have min_pos := (@le_min_iff ℝ _ ‖gs n a - gs n b‖ 1 0).mpr (by refine ⟨by positivity, by positivity⟩)
      simp only [Real.norm_eq_abs, abs_of_nonneg min_pos]
      rw [min_le_iff]
      right
      rfl
    · simp only [inv_pos, Nat.ofNat_pos, pow_pos]

lemma cont_ourMetric' (gs_cont : ∀ (n : ℕ), Continuous (gs n)) : Continuous (fun (p : X × X) ↦
    dist (kopio.mk X gs gs_sep p.1) (kopio.mk X gs gs_sep p.2)) := by
  exact cont_ourMetric gs_cont

example (X Y Z : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (ϕ : X × Y → Z) (x : X) (hphi : Continuous ϕ) : Continuous (fun y ↦ ϕ ⟨x, y⟩ ) := by
  exact Continuous.along_snd hphi

lemma cont_kopio_mk (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)) (gs_cont : ∀ n, Continuous (gs n)) :
    Continuous (kopio.mk X gs gs_sep) := by
  apply Metric.continuous_iff'.mpr
  intro x ε hε
  have cont_dist : Continuous (fun y ↦ dist (kopio.mk X gs gs_sep y)
      (kopio.mk X gs gs_sep x)) := by
    apply Continuous.along_fst (cont_ourMetric' gs_sep gs_cont)

  have interval_open : IsOpen (Set.Iio ε) := by exact isOpen_Iio
  have := @IsOpen.mem_nhds X x _ _ (cont_dist.isOpen_preimage _ interval_open) (by simpa using hε)
  filter_upwards [this] with y hy using hy

lemma cont_kopio_toOrigin (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)) (gs_cont : ∀ n, Continuous (gs n)) :
    Continuous (kopio.toOrigin X gs gs_sep) := by
  have symm : ∀ (s : Set X), kopio.toOrigin X gs gs_sep ⁻¹' s = kopio.mk X gs gs_sep '' s := by
    exact fun s ↦ Eq.symm (Set.EqOn.image_eq_self fun ⦃x⦄ ↦ congrFun rfl)
  have : ∀ (s : Set X), IsClosed s → IsClosed (kopio.toOrigin X gs gs_sep ⁻¹' s) := by
    intro M M_closed
    have M_cpt_X := IsClosed.isCompact M_closed
    rw [isCompact_iff_finite_subcover] at M_cpt_X
    have : ∀ s : Set (kopio X gs gs_sep), IsOpen s → IsOpen (kopio.mk X gs gs_sep ⁻¹' s) := by
      intro s
      have := cont_kopio_mk gs_sep gs_cont
      rw [continuous_def] at this
      specialize this s
      exact this
    have : IsClosed (kopio.toOrigin X gs gs_sep ⁻¹' M) := by
      --simp only [symm M]
      have M_image_cpt : IsCompact (kopio.mk X gs gs_sep '' M) := by
        apply isCompact_of_finite_subcover
        intro _ Us Usi_open
        simp only [kopio.mk, id_eq, Set.image_id']
        exact fun a ↦ M_cpt_X Us (fun i ↦ this (Us i) (Usi_open i)) a
      simpa [symm M] using IsCompact.isClosed M_image_cpt
    exact this
  have cont_iff_closed := @continuous_iff_isClosed (kopio X gs gs_sep) X _ _ (kopio.toOrigin X gs gs_sep)
  rw [← cont_iff_closed] at this
  exact this


noncomputable def homeomorph_OurMetric :
  X ≃ₜ kopio X gs gs_sep where
    toFun := kopio.mk X gs gs_sep
    invFun := kopio.toOrigin X gs gs_sep
    left_inv := congrFun rfl
    right_inv := congrFun rfl
    continuous_toFun := cont_kopio_mk gs_sep gs_cont
    continuous_invFun := cont_kopio_toOrigin gs_sep gs_cont


lemma X_metrizable' (gs : ∀ n, X → E n) (gs_cont : ∀ n, Continuous (gs n))
    (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)): --gs_bdd ei pitäisi tarvita
    TopologicalSpace.MetrizableSpace X := by

  exact (homeomorph_OurMetric gs_cont gs_sep).embedding.metrizableSpace


/- If X is compact, and there exists a seq of continuous real-valued functions that
separates points on X, then X is metrizable. -/
lemma X_metrizable (gs : ∀ n, X → E n) (gs_cont : ∀ n, Continuous (gs n))
    (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)): --(gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) : --gs_bdd ei pitäisi tarvita
    TopologicalSpace.MetrizableSpace X := by


  --exact X_metrizable' X (E n) hs hs_cont hs_sep hs_bdd
  exact (homeomorph_OurMetric gs_cont gs_sep).embedding.metrizableSpace

end Metrizability_lemma


section Seq_Banach_Alaoglu
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
variable (V : Type*) [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [TopologicalSpace.SeparableSpace V]
variable (K : Set (WeakDual 𝕜 V)) (K_cpt : IsCompact K)

--have : ∀ x y : V, x≠ y, ∃ n, gs n x ≠ gs n y

/- There exists a sequence of continuous functions that separates points on V*. -/
lemma exists_gs : ∃ (gs : ℕ → (WeakDual 𝕜 V) → 𝕜),
    (∀ n, Continuous (gs n)) ∧ (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y) := by
  set vs := TopologicalSpace.denseSeq V
  set gs : ℕ → K → 𝕜 := fun n ↦ fun ϕ ↦ (ϕ : WeakDual 𝕜 V) (vs n)
  use (fun n ↦ fun ϕ ↦ (ϕ : WeakDual 𝕜 V) (vs n))
  --use gs2
  constructor
  · exact fun n ↦ WeakDual.eval_continuous (vs n)
  · intro w y w_ne_y
    contrapose! w_ne_y
    --simp only [Set.forall_mem_range] at w_ne_y
    have : Set.EqOn (⇑w) (⇑y) (Set.range vs) := by
      simp only [Set.eqOn_range]
      exact (Set.eqOn_univ (⇑w ∘ vs) (⇑y ∘ vs)).mp fun ⦃x⦄ _ ↦ w_ne_y x
    have := Continuous.ext_on (TopologicalSpace.denseRange_denseSeq V) (map_continuous w) (map_continuous y) this
    exact DFunLike.coe_fn_eq.mp this

/- A compact subset of the dual V* of a separable space V is metrizable. -/
lemma subset_metrizable : TopologicalSpace.MetrizableSpace K := by
  have k_cpt' : CompactSpace K := by exact isCompact_iff_compactSpace.mp K_cpt
  obtain ⟨gs, gs_cont, gs_sep⟩ := exists_gs 𝕜 V K
  let hs : ℕ → K → 𝕜 := fun n ↦ fun ϕ ↦ gs n (ϕ : WeakDual 𝕜 V)
  apply X_metrizable (E := fun _ ↦ 𝕜) hs
  · intro n
    exact Continuous.comp (gs_cont n) continuous_subtype_val
  · intro x y x_ne_y
    apply gs_sep
    exact Subtype.coe_ne_coe.mpr x_ne_y

/- The closed unit ball is sequentially compact in V* if V is separable. -/
theorem WeakDual.isSeqCompact_closedBall [SequentialSpace V] (x' : NormedSpace.Dual 𝕜 V) (r : ℝ) :
    IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
  let b := (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
  have b_isCompact : IsCompact b := by
    apply WeakDual.isCompact_closedBall
  have b_isCompact' : CompactSpace b := by
    exact isCompact_iff_compactSpace.mp b_isCompact

  have b_isMetrizable : TopologicalSpace.MetrizableSpace b := by
    exact subset_metrizable 𝕜 V b b_isCompact

  have seq_cpt_space := @FirstCountableTopology.seq_compact_of_compact b
      _ _ b_isCompact'

  have seq_cont_phi : SeqContinuous (fun φ : b ↦ (φ : WeakDual 𝕜 V)) := by
    refine continuous_iff_seqContinuous.mp ?_
    exact continuous_subtype_val

  have seq_incl := IsSeqCompact.range seq_cont_phi
  convert seq_incl

  simp only [Subtype.range_coe_subtype, Set.mem_preimage, coe_toNormedDual, Metric.mem_closedBall]
  rfl

example : WeakDual 𝕜 V = (V →L[𝕜] 𝕜) := rfl

end Seq_Banach_Alaoglu


--#help tactic
