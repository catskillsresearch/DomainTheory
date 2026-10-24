module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.constOp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOpUncurry

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.applyMap_toElement
@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

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
              simp only [uncurryMap, comp.toElement]
              rw [hpair, applyMap_toElement]
          _ = (compOpUncurry A B C).toElement (pairElements Q A gf x) := by
              rw [compOp.uncurry]
          _ = (comp g f).toElement x := compOpUncurry.toElement A B C g f x
  rw [← huniq, approxMap_toElement_element_toApproxMap]

end InfoSys
end DomainTheory.InformationSystems
