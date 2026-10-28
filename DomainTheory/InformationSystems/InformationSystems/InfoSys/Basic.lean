module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Element

@[expose] public section

namespace DomainTheory.InformationSystems

universe u

namespace InfoSys

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

theorem Element.ext {x y : sys.Element} (h : x.carrier = y.carrier) : x = y := by
  cases x
  cases y
  subst h
  rfl

theorem element_le_refl (x : sys.Element) : x.carrier ⊆ x.carrier :=
  Set.Subset.refl _

theorem element_le_trans (x y z : sys.Element)
    (hxy : x.carrier ⊆ y.carrier) (hyz : y.carrier ⊆ z.carrier) :
    x.carrier ⊆ z.carrier :=
  Set.Subset.trans hxy hyz

theorem element_le_antisymm (x y : sys.Element)
    (hxy : x.carrier ⊆ y.carrier) (hyx : y.carrier ⊆ x.carrier) :
    x = y :=
  Element.ext sys (Set.Subset.antisymm hxy hyx)

instance instPartialOrderElement : PartialOrder sys.Element where
  le x y := x.carrier ⊆ y.carrier
  le_refl := element_le_refl sys
  le_trans := element_le_trans sys
  le_antisymm := element_le_antisymm sys
end InfoSys
end DomainTheory.InformationSystems
