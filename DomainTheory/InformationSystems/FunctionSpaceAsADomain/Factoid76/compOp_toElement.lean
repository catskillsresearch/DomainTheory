/-ai
The composition operator sends the pair of approximable maps g and f to the element of the function space corresponding to their composite.

The approximable map recovered from that element equals the composite. At an element x its value equals the uncurried composition at the pair of that pair with x, by the pairing identity for a curried map and the equality of the operator's uncurrying with the uncurried composition, and the uncurried composition evaluates to the composite at x. Passing back from the recovered map to an element gives the result.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.pairMap_comp_fst_snd_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOp_uncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOpUncurry_toElement

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)










theorem compOp_toElement (g : ApproximableMap B C) (f : ApproximableMap A B) :
    (compOp A B C).toElement
      (pairElements (functionSystem B C) (functionSystem A B)
        (approxMap_toElement B C g) (approxMap_toElement A B f)) =
      approxMap_toElement A C (comp g f) := by
  let Q := productSystem (functionSystem B C) (functionSystem A B)
  let gf := pairElements (functionSystem B C) (functionSystem A B)
      (approxMap_toElement B C g) (approxMap_toElement A B f)
  have huniq :
      element_toApproxMap A C ((compOp A B C).toElement gf) = comp g f := by
    refine (ext_iff_toElement _ _).2 fun x => ?_
    have hpair := pairMap_comp_fst_snd_toElement (X := C) (compOp A B C) gf x
    calc
      (element_toApproxMap A C ((compOp A B C).toElement gf)).toElement x
          = (uncurryMap Q A C (compOp A B C)).toElement (pairElements Q A gf x) := by
              simp only [uncurryMap, comp_toElement]
              rw [hpair, applyMap_toElement]
          _ = (compOpUncurry A B C).toElement (pairElements Q A gf x) := by
              rw [compOp_uncurry]
          _ = (comp g f).toElement x := compOpUncurry_toElement A B C g f x
  rw [← huniq, approxMap_toElement_element_toApproxMap]

end InfoSys
end DomainTheory.InformationSystems
