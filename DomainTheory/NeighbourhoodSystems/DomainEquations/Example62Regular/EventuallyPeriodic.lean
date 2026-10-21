/-ai
A total tree is eventually periodic when the set of its subtrees, the range of the subtree selector, is finite.
ai-/
module

public import Mathlib.Computability.MyhillNerode
import all Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Tree
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.select_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.pos_select
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.mem_treeLang

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}

/-- **Eventual periodicity (Scott).** A tree `a` is *eventually periodic* iff the set of its subtrees
`{aσ ∣ σ ∈ Σ*}` is finite. (Equivalently — by the picture — the tree is built from finitely many
distinct subtrees, so it is "ultimately periodic" along every branch.) -/
def EventuallyPeriodic (a : Tree n) : Prop := (Set.range (select a)).Finite

end Example62Regular

end DomainTheory.NeighbourhoodSystems
