/-ai
If an approximable map h commutes with endomaps f and g and sends the bottom element to the bottom element, then the image under h of the least fixed point of f lies below the least fixed point of g.

A token of the image comes from a finite set in the fixed point of f and a relation witness. The fixed-point map supplies a finite set of tokens of f and a stage of a fixed-point chain that entails that finite set. The chain estimate places the image under h of the closure of that stage below the least fixed point of g. Monotonicity of h relates the stage to the singleton of the token, so the token lies in that image.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.fixChain_toElement_le_fix

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)


theorem toElement_fix_le_fixElement (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h)
    (hstrict : h.toElement A.botElement = B.botElement) :
    h.toElement (fixElement A f) ≤ fixElement B g := by
  intro Z ⟨u, hu, hrel⟩
  obtain ⟨w, hw, ⟨_, _, v0, hv0, hEnt⟩⟩ :=
    exists_rel_of_subset_image (fixMap A) (approxMap_toElement A A f) u hu
  obtain ⟨n, hn⟩ := hv0
  have hcl := fixChain_toElement_le_fix A B f g h hcomm hstrict hw hn
  have hv0C := fixChain_con A hn
  have hrel' : h.rel v0 {Z} :=
    h.mono hrel hEnt (proposition_2_3_iii B (h.rel_cod hrel)) hv0C (h.rel_cod hrel)
  have hZ : Z ∈ (h.toElement (A.closure v0 hv0C)).carrier :=
    ⟨v0, A.subset_closure hv0C, hrel'⟩
  exact hcl hZ

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
