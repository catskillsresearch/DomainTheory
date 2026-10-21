/-ai
An element x lies in the field of the singleton equivalence of a if and only if x equals a.

Membership is the pair of equations saying that both components equal a. The forward direction keeps the first equation, and the reverse direction repeats the equation as both components.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem singletonE_mem (a x : Pomega) : (singletonE a).mem x ↔ x = a :=
  ⟨fun h => h.1, fun hx => ⟨hx, hx⟩⟩

end DomainTheory.DataTypesAsLattices
