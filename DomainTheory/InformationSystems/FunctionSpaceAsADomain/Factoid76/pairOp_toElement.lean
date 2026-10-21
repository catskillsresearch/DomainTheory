/-ai
The pairing operator sends the pair of approximable maps f and g to the element of the function space corresponding to the pairing of f and g.

The approximable map recovered from that element equals the pairing. At an element x its value equals the uncurried pairing at the pair of that pair with x, by the pairing identity for a curried map and the equality of the operator's uncurrying with the uncurried pairing, and the uncurried pairing evaluates to the pairing at x. Passing back from the recovered map to an element gives the result.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.pairMap_comp_fst_snd_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.pairOp_uncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.pairOpUncurry_toElement

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.applyMap_toElement
@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


theorem pairOp_toElement (f : ApproximableMap C A) (g : ApproximableMap C B) :
    (pairOp A B C).toElement
      (pairElements (functionSystem C A) (functionSystem C B)
        (approxMap_toElement C A f) (approxMap_toElement C B g)) =
      approxMap_toElement C (productSystem A B) (pairMap A B f g) := by
  let P := productSystem (functionSystem C A) (functionSystem C B)
  let fg := pairElements (functionSystem C A) (functionSystem C B)
      (approxMap_toElement C A f) (approxMap_toElement C B g)
  have huniq :
      element_toApproxMap C (productSystem A B) ((pairOp A B C).toElement fg) =
        pairMap A B f g := by
    refine (ext_iff_toElement _ _).2 fun x => ?_
    have hpair :=
      pairMap_comp_fst_snd_toElement (X := productSystem A B) (pairOp A B C) fg x
    calc
      (element_toApproxMap C (productSystem A B) ((pairOp A B C).toElement fg)).toElement x
          = (uncurryMap P C (productSystem A B) (pairOp A B C)).toElement
              (pairElements P C fg x) := by
              simp only [uncurryMap, comp_toElement]
              rw [hpair, applyMap_toElement]
          _ = (pairOpUncurry A B C).toElement (pairElements P C fg x) := by
              rw [pairOp_uncurry]
          _ = (pairMap A B f g).toElement x := pairOpUncurry_toElement A B C f g x
  rw [← huniq, approxMap_toElement_element_toApproxMap]

end InfoSys
end DomainTheory.InformationSystems
