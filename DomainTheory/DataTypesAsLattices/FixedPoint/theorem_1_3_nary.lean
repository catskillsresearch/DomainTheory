/-ai
Scott 1976, Theorem 1.3, ternary substitution. If a map of three arguments is Scott continuous in each argument, and three endomaps are Scott continuous, then substituting those endomaps into the three arguments preserves Scott continuity.

The diagonal substitution theorem is applied to the map that feeds the first two substituted maps to one variable and the third to the other. Continuity in the first variable is binary substitution, and continuity in the second is unary substitution. A code in the resulting union of finite approximants is rewritten as a code in the Scott union, and conversely.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Graph
public import DomainTheory.DataTypesAsLattices.FixedPoint.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3_diag
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3_tuple

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.3, ternary substitution.** -/
theorem theorem_1_3_nary {f : Pomega → Pomega → Pomega → Pomega}
    (hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (hf2 : ∀ x y, IsScottContinuous (fun z => f x y z))
    {g h i : Pomega → Pomega}
    (hg : IsScottContinuous g) (hh : IsScottContinuous h) (hi : IsScottContinuous i) :
    IsScottContinuous (fun x => f (g x) (h x) (i x)) := by
  constructor
  intro x
  have H := theorem_1_3_diag (x := x)
    (f := fun u v => f (g u) (h u) (i v))
    (fun v => theorem_1_3_tuple (fun y => hf0 y (i v)) (fun x => hf1 x (i v)) hg hh)
    (fun u => theorem_1_3 (hf2 (g u) (h u)) hi)
  ext k
  constructor
  · intro hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ f (g (e n)) (h (e n)) (i (e n))} := by
      rwa [← H]
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ f (g (e n)) (h (e n)) (i (e n))} :=
      Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
    rwa [← H] at this

end DomainTheory.DataTypesAsLattices
