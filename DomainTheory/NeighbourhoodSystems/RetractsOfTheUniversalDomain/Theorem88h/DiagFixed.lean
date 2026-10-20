module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **Theorem 8.8(c), Part 1 of 6 — the diagonal fixed-point predicate.** `DiagFixed P a n` holds
iff the presented neighbourhood `Xₙ = P.X n` is already `a`-fixed, i.e. (`diagFixed_iff_fixedNbhd_mem`)
iff `Xₙ` is a neighbourhood of Theorem 8.5's subsystem `fixedNbhd a = {X ∈ V ∣ X a X}`. -/
def DiagFixed (P : ComputablePresentation V) (a : ApproximableMap V V) (n : ℕ) : Prop :=
  a.rel (P.X n) (P.X n)

end DomainTheory.NeighbourhoodSystems
