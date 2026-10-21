/-ai
The open subsets of the domain of a neighbourhood system stand in bijection with the approximable maps into O. An open set is sent to its approximable map, and an approximable map is sent to the set of elements mapped to the top element, which is open. The two constructions invert each other by the membership round trip and by the equality of the reconstructed map with the original map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.openToMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mapToOpen
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.isOpen_mapToOpen
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_mapToOpen_openToMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.openToMap_mapToOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 (main).** The open subsets of `|𝒟|` are in one-one correspondence with the
approximable mappings `𝒟 → 𝒪`, via `U ↦ openToMap U` and `f ↦ {x ∣ f(x) = ⊤}`. -/
def openSet_equiv_map : {U : Set V.Element // IsOpen U} ≃ ApproximableMap V O where
  toFun U := openToMap V U.1 U.2
  invFun f := ⟨mapToOpen V f, isOpen_mapToOpen V f⟩
  left_inv := by
    rintro ⟨U, hU⟩
    apply Subtype.ext
    ext x
    exact mem_mapToOpen_openToMap V U hU x
  right_inv f := openToMap_mapToOpen V f

end DomainTheory.NeighbourhoodSystems.Exercise215
