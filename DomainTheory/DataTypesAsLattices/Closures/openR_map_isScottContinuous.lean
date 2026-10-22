/-ai
The map sending u to the set of codes m for which some finite set e n contained in e m has index n in u is Scott continuous.

Membership of m is compared with membership in the Scott union. A witness n contributes the code two to the n, using the power-of-two description of the finite sets and the singleton containment coming from n lying in u. Conversely, a Scott-union witness supplies an index n whose finite set sits in e m and whose code lies in u.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem openR_map_isScottContinuous :
    IsScottContinuous (fun u => {m | ∃ n, e n ⊆ e m ∧ n ∈ u}) := by
  intro u
  ext m
  constructor
  · intro ⟨n, hn, hnu⟩
    exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hnu],
      ⟨n, hn, by simp [e_pow2]⟩⟩
  · intro hm
    obtain ⟨k, hk, n, hn, hnk⟩ := mem_scottUnion.mp hm
    exact ⟨n, hn, hk hnk⟩

end DomainTheory.DataTypesAsLattices
