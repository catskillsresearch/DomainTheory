module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem mem_decodeQPairList_appendCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (appendCode c1 c2) ↔ p ∈ decodeQPairList c1 ∨ p ∈ decodeQPairList c2 := by
  simp only [mem_decodeQPairList, mem_decodeList_appendCode]
  constructor
  · rintro ⟨v, (hv | hv), rfl⟩
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact ⟨v, Or.inl hv, rfl⟩
    · exact ⟨v, Or.inr hv, rfl⟩

end DomainTheory.NeighbourhoodSystems
