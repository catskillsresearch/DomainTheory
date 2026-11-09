module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.comp
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_fixed
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_unique
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.fix_under_intertwining

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

namespace proposition_7_4

theorem ii (f : ApproximableMap A A) :
    f.toElement (fixElement A f) = fixElement A f :=
  fixElement_fixed A f

theorem unique (f : ApproximableMap A A) (φ : A.Element)
    (hii : f.toElement φ = φ)
    (hleast : ∀ x : A.Element, f.toElement x ≤ x → φ ≤ x) :
    φ = fixElement A f :=
  fixElement_unique A f φ (le_of_eq hii) hleast

theorem iii (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h)
    (hstrict : h.toElement A.botElement = B.botElement) :
    h.toElement (fixElement A f) = fixElement B g := by
  apply le_antisymm
  · exact toElement_fix_le_fixElement A B f g h hcomm hstrict
  · exact fixElement_le_toElement_fix A B f g h hcomm

end proposition_7_4

theorem proposition_7_4 :
    (∀ {α : Type*} [DecidableEq α] (A : InfoSys α) (f : ApproximableMap A A),
      f.toElement (fixElement A f) = fixElement A f) ∧
    (∀ {α β : Type*} [DecidableEq α] [DecidableEq β]
      (A : InfoSys α) (B : InfoSys β)
      (f : ApproximableMap A A) (g : ApproximableMap B B) (h : ApproximableMap A B),
      comp h f = comp g h →
        h.toElement A.botElement = B.botElement →
          h.toElement (fixElement A f) = fixElement B g) ∧
    (∀ {α : Type*} [DecidableEq α] (A : InfoSys α) (f : ApproximableMap A A) (φ : A.Element),
      f.toElement φ = φ →
        (∀ x : A.Element, f.toElement x ≤ x → φ ≤ x) →
          φ = fixElement A f) :=
  ⟨@proposition_7_4.ii, @proposition_7_4.iii, @proposition_7_4.unique⟩

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
