/-ai
A finite element lying under an element x is a finite approximant of x.

The finite element is the closure of a consistent finite set of tokens. Every token of that set belongs to the closure and hence to x, so the set consists of tokens of x and the closure is a finite approximant.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem mem_finiteApproximants_of_le {x : A.Element} {y : FiniteElement A}
    (hle : (y : A.Element) ≤ x) : y ∈ finiteApproximants A x := by
  rcases y with ⟨yval, ⟨u, hu, rfl⟩⟩
  refine ⟨u, hu, ?_, rfl⟩
  intro a ha
  exact hle (A.subset_closure hu ha)

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
