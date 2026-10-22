/-ai
If a is at most c and b is at most d, then the maximum of a and b is at most the maximum of c and d.

The first hypothesis and the left bound for a maximum give a at most the maximum of c and d, and the second hypothesis and the right bound give b at most that same maximum, so the maximum of a and b is at most the maximum of c and d.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem max_le_max_nat {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) :
    max a b ≤ max c d :=
  max_le (le_trans h1 (le_max_left _ _)) (le_trans h2 (le_max_right _ _))

end InfoSys

end DomainTheory.InformationSystems
