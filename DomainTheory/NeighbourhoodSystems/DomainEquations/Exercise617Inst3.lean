module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


/-- **The category of `∅`-free domains and strict maps.** Morphisms are strict approximable maps
(`StrictMap`, Exercise 5.10); identities and associative composition come from Theorem 2.5, and
strictness is preserved by `isStrict_idMap` / `isStrict_comp`. -/
instance : Category StrictDomainObj where
  Hom D E := StrictMap D.sys E.sys
  id D := ⟨ApproximableMap.idMap D.sys, isStrict_idMap⟩
  comp f g := ⟨g.1.comp f.1, isStrict_comp g.2 f.2⟩
  id_comp f := Subtype.ext (ApproximableMap.comp_idMap f.1)
  comp_id f := Subtype.ext (ApproximableMap.idMap_comp f.1)
  assoc f g h := Subtype.ext (ApproximableMap.comp_assoc h.1 g.1 f.1).symm

end DomainTheory.NeighbourhoodSystems
