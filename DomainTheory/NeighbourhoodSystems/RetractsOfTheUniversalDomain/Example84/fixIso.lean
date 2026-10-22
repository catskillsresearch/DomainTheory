module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.toElementMap_a_fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_toElementMap_fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO_check_toElementMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO_mono

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

variable (u : D.Element) (hu : u ≠ D.bot)

/-- **Example 8.4(a) (Scott 1981, PRG-19), packaged.** The range (fixed-point set) of `a` is
order-isomorphic to `O`. -/
def fixIso (hu : u ≠ D.bot) : O.Element ≃o {y : D.Element // (a u).toElementMap y = y} where
  toFun t := ⟨fixOfO u t, toElementMap_a_fixOfO u hu t⟩
  invFun y := check.toElementMap y.1
  left_inv t := check_toElementMap_fixOfO u hu t
  right_inv y := by
    apply Subtype.ext
    show fixOfO u (check.toElementMap y.1) = y.1
    rw [fixOfO_check_toElementMap, y.2]
  map_rel_iff' := by
    intro t t'
    show fixOfO u t ≤ fixOfO u t' ↔ t ≤ t'
    constructor
    · intro h
      have := toElementMap_mono check h
      rwa [check_toElementMap_fixOfO u hu, check_toElementMap_fixOfO u hu] at this
    · exact fixOfO_mono u

end DomainTheory.NeighbourhoodSystems
