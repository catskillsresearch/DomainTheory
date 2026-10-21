/-ai
If a Scott-continuous map fixes z and every member of a family A is contained in z, then the least upper bound of the iterates above the union of A is contained in z.

The union of A is contained in z. Every iterate from that union is contained in z: the starting iterate is the union, and a successor iterate rewrites by the fixed-point equation and monotonicity. An element of the least upper bound therefore lies in some iterate and hence in z.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.iterateFrom
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem lfpAbove_le_of_ub {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set Pomega} {z : Pomega} (hz : f z = z) (hub : ∀ x ∈ A, x ⊆ z) :
    lfpAbove f (⋃₀ A) ⊆ z := by
  have h0 : ⋃₀ A ⊆ z := by
    intro k hk
    obtain ⟨x, hxA, hkx⟩ := Set.mem_sUnion.mp hk
    exact hub x hxA hkx
  have hiter : ∀ n, iterateFrom f (⋃₀ A) n ⊆ z := by
    intro n
    induction n with
    | zero => simpa [iterateFrom] using h0
    | succ n ih => simpa [iterateFrom, hz] using isScottContinuous_monotone hf ih
  intro k hk
  obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
  exact hiter n hkn

end DomainTheory.DataTypesAsLattices
