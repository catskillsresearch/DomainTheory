module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



theorem funOf_top (x : Pomega) : funOf topElem x = topElem := by
  ext m
  constructor
  · intro
    trivial
  · intro
    exact ⟨0, by simp [e_zero], trivial⟩

end DomainTheory.DataTypesAsLattices
