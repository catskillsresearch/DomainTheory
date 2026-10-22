module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.Basic

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.uncurry_curryMap
@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


theorem pairOp_uncurry :
    uncurryMap (productSystem (functionSystem C A) (functionSystem C B)) C (productSystem A B)
      (pairOp A B C) =
      pairOpUncurry A B C := by
  simp only [pairOp, uncurry_curryMap]

end InfoSys
end DomainTheory.InformationSystems
