/-ai
The endofunctor on the category of empty-free domains and strict maps sends a domain to the three-way sum of the unit domain with that domain and itself, and sends a strict map to the three-way sum of the identity on the unit with the map and the map again. Preservation of identities is the identity law for that three-way sum. Preservation of composition is the composition law for the three-way sum, after the composite of the identity on the unit with itself is rewritten as the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumMap3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumMap3_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumMap3_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sinj2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcMapHom

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


open Example62C in
/-- **Exercise 6.17 — the functor `T(X) = 𝟙 + X + X`** on the category of `∅`-free domains and strict
maps. On objects, `T(D) = 𝟙 + D + D` (Example 6.2's three-way sum); on maps, `T(f) = I_𝟙 + f + f`. -/
abbrev Tc : Endofunctor StrictDomainObj.{w} where
  obj := tcObj
  map := tcMapHom
  map_id D := Subtype.ext (by
    show sumMap3 (idMap unitSys) (idMap D.sys) (idMap D.sys) = idMap (tcObj D).sys
    exact sumMap3_id)
  map_comp {D E F} g f := Subtype.ext (by
    show sumMap3 (idMap unitSys) (g.1.comp f.1) (g.1.comp f.1)
      = (sumMap3 (idMap unitSys) g.1 g.1).comp (sumMap3 (idMap unitSys) f.1 f.1)
    have h := sumMap3_comp (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (h₀'' := Example62C.unitSys_nonempty) (h₁'' := F.nonempty) (h₂'' := F.nonempty)
      (idMap unitSys) g.1 g.1 (idMap unitSys) f.1 f.1
    rw [idMap_comp] at h
    exact h)

end DomainTheory.NeighbourhoodSystems
