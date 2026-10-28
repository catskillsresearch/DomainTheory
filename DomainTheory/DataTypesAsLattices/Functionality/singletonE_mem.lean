
module

public import DomainTheory.DataTypesAsLattices.Embedding.extend
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.mem
public import DomainTheory.DataTypesAsLattices.Functionality.singletonE

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem singletonE_mem (a x : Pomega) : (singletonE a).mem x ↔ x = a :=
  ⟨fun h => h.1, fun hx => ⟨hx, hx⟩⟩

end DomainTheory.DataTypesAsLattices
