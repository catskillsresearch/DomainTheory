/-ai
Scott 1976, Theorem 1.3, binary substitution. If a map of two arguments is Scott continuous in each argument, and two endomaps are Scott continuous, then substituting those endomaps preserves Scott continuity.

The diagonal case is applied to the map that feeds one substituted endomap to the first argument and the other to the second, using unary substitution in each variable. A code in the diagonal union of finite approximants is a code in the Scott union, and conversely.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Graph
public import DomainTheory.DataTypesAsLattices.FixedPoint.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3_diag
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.3, binary substitution.** If `f` is continuous
in each argument and `g, h` are continuous, then `x ↦ f(g x, h x)` is
continuous. -/
theorem theorem_1_3_tuple {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y))
    {g h : Pomega → Pomega} (hg : IsScottContinuous g) (hh : IsScottContinuous h) :
    IsScottContinuous (fun x => f (g x) (h x)) := by
  constructor
  intro x
  have H := theorem_1_3_diag (x := x)
    (f := fun u v => f (g u) (h v))
    (fun v => theorem_1_3 (hfx (h v)) hg)
    (fun u => theorem_1_3 (hfy (g u)) hh)
  ext k
  constructor
  · intro hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ f (g (e n)) (h (e n))} := by rwa [← H]
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ f (g (e n)) (h (e n))} :=
      Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
    rwa [← H] at this

end DomainTheory.DataTypesAsLattices
