module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V_union_exists

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(i)-for-`∪`, for `V`**: trivially recursively decidable (the always-`1` constant). -/
theorem V_union_computable : RecDecidable₂ (fun n m => ∃ k, VX k = VX n ∪ VX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (V_union_exists t.unpair.1 t.unpair.2) rfl⟩

end DomainTheory.NeighbourhoodSystems
