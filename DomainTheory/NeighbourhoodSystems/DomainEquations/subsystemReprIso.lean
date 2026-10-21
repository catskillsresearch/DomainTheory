/-ai
The subsystems of a neighbourhood system E, ordered by the subsystem relation, form a domain: they are order-isomorphic to the domain of elements of the representation system built from the family of subdomain neighbourhood-sets. The isomorphism composes the correspondence between subsystems and their neighbourhood-sets with the inverse of the representation isomorphism for that family, using that the family is nonempty and closed under nonempty intersections and directed unions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_sInter_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_sUnion_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611Inst16
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subIso

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- **Proposition 6.11 (Scott 1981, PRG-19).** For a neighbourhood system `E`, the set of
subsystems `{D ∣ D ◁ E}`, ordered by the subdomain relation `◁`, *forms a domain in its own
right*: it is order-isomorphic to the domain `|reprSystem (subFam E) …|` produced by the abstract
representation theorem (Exercise 2.22), using that `subFam E` is closed under non-empty
intersections (`subFam_sInter_mem`) and directed unions (Scott's remark, `subFam_sUnion_mem`). -/
def subsystemReprIso (E : NeighborhoodSystem α) :
    {D : NeighborhoodSystem α // D ◁ E} ≃o
      (reprSystem (subFam E) (subFam_sInter_mem E) (subFam_nonempty E)).Element :=
  (subIso E).trans
    (reprIso (subFam E) (subFam_sInter_mem E) (subFam_nonempty E) (subFam_sUnion_mem E)).symm

end DomainTheory.NeighbourhoodSystems.Proposition611
