module

public import Mathlib.CategoryTheory.Category.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.idMap

@[expose] public section

universe w

namespace DomainTheory.NeighbourhoodSystems

/-- Bundled neighbourhood system: a carrier type together with its neighbourhood structure. -/
structure DomainObj : Type (w + 1) where
  carrier : Type w
  sys : NeighborhoodSystem carrier

open CategoryTheory ApproximableMap

/-- Neighbourhood systems and approximable maps form a Mathlib category. -/
instance : Category DomainObj where
  Hom D E := ApproximableMap D.sys E.sys
  id D := idMap D.sys
  comp f g := g.comp f
  id_comp f := comp_idMap f
  comp_id f := idMap_comp f
  assoc f g h := (comp_assoc h g f).symm

@[simp] theorem DomainObj.id_val (D : DomainObj) :
    (𝟙 D : ApproximableMap D.sys D.sys) = idMap D.sys := rfl

@[simp] theorem DomainObj.comp_val {D E F : DomainObj} (g : E ⟶ F) (f : D ⟶ E) :
    (f ≫ g : ApproximableMap D.sys F.sys) = g.comp f := rfl

end DomainTheory.NeighbourhoodSystems
