import Mathlib.Topology.Algebra.InfiniteSum.Basic

variable {α β : Type*} [TopologicalSpace α] [CommMonoid α]

@[to_additive (attr := simp)]
theorem tprod_ite_eq' (b : β) [DecidablePred (· = b)] (f : β → α) :
    ∏' b', (if b' = b then f b' else 1) = f b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']
