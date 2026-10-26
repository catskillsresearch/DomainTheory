module

public import DomainTheory.DataTypesAsLattices.Graph
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.3 (The substitution theorem), binary case.**
If `f` is continuous in each argument separately, then `x ↦ f(x,x)` is
continuous. -/
theorem theorem_1_3_diag {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y))
    {x : Pomega} :
    f x x = ⋃ n, {k | e n ⊆ x ∧ k ∈ f (e n) (e n)} := by
  apply subset_antisymm
  · intro k hk
    have : k ∈ scottUnion (fun z => f z x) x := by
      rw [← (hfx x).out x]; exact hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    have : k ∈ scottUnion (fun y => f (e n) y) x := by
      rw [← (hfy (e n)).out x]; exact hkn
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp this
    refine Set.mem_iUnion.mpr ⟨n ||| m, ?_⟩
    refine ⟨e_or_of_subset hn hm, ?_⟩
    have hle : e n ⊆ e (n ||| m) := by rw [e_or]; exact Set.subset_union_left
    have hre : e m ⊆ e (n ||| m) := by rw [e_or]; exact Set.subset_union_right
    exact IsScottContinuous.monotone (hfy (e (n ||| m))) hre
      (IsScottContinuous.monotone (hfx (e m)) hle hkm)
  · intro k hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp hk
    exact IsScottContinuous.monotone (hfy x) hn
      (IsScottContinuous.monotone (hfx (e n)) hn hkn)

end DomainTheory.DataTypesAsLattices
