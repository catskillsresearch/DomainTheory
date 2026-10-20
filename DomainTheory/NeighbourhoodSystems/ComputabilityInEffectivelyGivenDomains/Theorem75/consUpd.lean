module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

section ConsFold

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- One fold step (see the section doc). `projFn` extracts the relevant component index from an
entry; `fc` is `P.cons_computable`'s `{0,1}` consistency tester. -/
def consUpd (projFn fc : ℕ → ℕ) (s x : ℕ) : ℕ :=
  selectFn (s.unpair.1 % 2)
    (Nat.pair (s.unpair.1 / 2)
      (Nat.pair (P.inter s.unpair.2.unpair.1 (projFn x))
        (selectFn s.unpair.2.unpair.2 (isOne (fc (Nat.pair s.unpair.2.unpair.1 (projFn x)))) 0)))
    (Nat.pair (s.unpair.1 / 2) (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2))

end ConsFold

end DomainTheory.NeighbourhoodSystems
