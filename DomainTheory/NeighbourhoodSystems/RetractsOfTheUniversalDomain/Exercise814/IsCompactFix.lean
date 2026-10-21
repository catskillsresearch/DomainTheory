/-ai
A fixed point of a closure operator is compact when, for every nonempty directed family of fixed points, lying under the directed supremum of the family in the ambient system yields lying under some single member of the family.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section ClosureOperator

variable {a : ApproximableMap E E}

/-- **Compactness of a fixed point w.r.t. directed unions of `Fix(a)`.** Phrased via the ambient
`E.Element` order and `iSupDirected` (since `Fix(a)` is not itself a `NeighborhoodSystem.Element`
type), mirroring `Theorem85.lean`'s `IsCompactElt`. -/
def IsCompactFix (_h : IsClosureOperator a) (y : FixSet a) : Prop :=
  ∀ {I : Type u} [Nonempty I] (d : I → FixSet a)
    (hdir : ∀ i j, ∃ k, (d i).1 ≤ (d k).1 ∧ (d j).1 ≤ (d k).1),
    y.1 ≤ iSupDirected (fun i => (d i).1) hdir → ∃ i, y.1 ≤ (d i).1

end ClosureOperator

end DomainTheory.NeighbourhoodSystems
