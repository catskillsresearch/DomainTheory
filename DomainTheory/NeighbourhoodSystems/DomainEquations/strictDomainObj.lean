module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.smashProduct
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.DomainObj

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open CategoryTheory
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.SmashProduct

universe w

theorem isStrict_comp {α β γ : Type*}
    {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
    {a : ApproximableMap V₁ V₂} {b : ApproximableMap V₀ V₁}
    (ha : IsStrict a) (hb : IsStrict b) : IsStrict (a.comp b) := by
  rw [isStrict_iff_apply_bot, toElementMap_comp, isStrict_iff_apply_bot.mp hb,
    isStrict_iff_apply_bot.mp ha]

structure StrictDomainObj : Type (w + 1) where
  carrier : Type w
  sys : NeighborhoodSystem carrier
  nonempty : ∀ X, sys.mem X → X.Nonempty

instance : Category StrictDomainObj where
  Hom D E := StrictMap D.sys E.sys
  id D := ⟨ApproximableMap.idMap D.sys, isStrict_idMap⟩
  comp f g := ⟨g.1.comp f.1, isStrict_comp g.2 f.2⟩
  id_comp f := Subtype.ext (ApproximableMap.comp_idMap f.1)
  comp_id f := Subtype.ext (ApproximableMap.idMap_comp f.1)
  assoc f g h := Subtype.ext (ApproximableMap.comp_assoc h.1 g.1 f.1).symm

@[simp] theorem StrictDomainObj.id_val (D : StrictDomainObj) :
    ((CategoryStruct.id D) : StrictMap D.sys D.sys).1 = ApproximableMap.idMap D.sys := rfl

@[simp] theorem StrictDomainObj.comp_val {D E F : StrictDomainObj}
    (g : (E ⟶ F)) (f : (D ⟶ E)) :
    ((f ≫ g : StrictMap D.sys F.sys)).1 = g.1.comp f.1 := rfl

end DomainTheory.NeighbourhoodSystems
