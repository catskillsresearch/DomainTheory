module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.subChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.trivialChar

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- The `{0,1}` characteristic function of `Xenum a = Xenum b`. Both consistent → inclusion both
ways (`subChar`); one consistent, one junk (`univ`) → the consistent side is the trivial
neighbourhood (`trivialChar`); both junk → equal. -/
def eqEnumChar (gN incl0 incl1 eq1 : ℕ → ℕ) (a b : ℕ) : ℕ :=
  selectFn (isOne (gN a))
    (selectFn (isOne (gN b))
      (selectFn (subChar P₁ incl0 incl1 a b) (subChar P₁ incl0 incl1 b a) 0)
      (trivialChar P₁ eq1 a))
    (selectFn (isOne (gN b)) (trivialChar P₁ eq1 b) 1)

end DomainTheory.NeighbourhoodSystems
