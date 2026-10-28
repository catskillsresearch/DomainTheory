module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.seqFunLt
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import Mathlib.Data.Set.Lattice.Indexed
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem mem_seqFunLt {u x : Pomega} {n k : ℕ} :
    k ∈ seqFunLt u x n ↔ ∃ i ∈ x, i < n ∧ k ∈ funOf u (ofNat i) := by
  constructor
  · intro hk
    obtain ⟨i, hi, hrest⟩ := Set.mem_iUnion₂.mp hk
    obtain ⟨hlt, hki⟩ := Set.mem_iUnion.mp hrest
    exact ⟨i, hi, hlt, hki⟩
  · intro ⟨i, hi, hlt, hki⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hi, Set.mem_iUnion.mpr ⟨hlt, hki⟩⟩

end DomainTheory.DataTypesAsLattices
