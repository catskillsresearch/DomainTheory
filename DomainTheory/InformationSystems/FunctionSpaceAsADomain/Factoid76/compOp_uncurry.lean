/-ai
Uncurrying the composition operator recovers the uncurried composition map.

This is the definition of the operator as a currying, together with the identity that uncurrying a currying returns the original map.
ai-/
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

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)










theorem compOp_uncurry :
    uncurryMap (productSystem (functionSystem B C) (functionSystem A B)) A C (compOp A B C) =
      compOpUncurry A B C := by
  simp only [compOp, uncurry_curryMap]

end InfoSys
end DomainTheory.InformationSystems
