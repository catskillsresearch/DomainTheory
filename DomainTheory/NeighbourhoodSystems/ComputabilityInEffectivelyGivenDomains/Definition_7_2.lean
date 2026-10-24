module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive
open NeighborhoodSystem Domain.Recursive ApproximableMap
section
variable {α β γ : Type*}

/- concordance: source L4271 DEFINITION 7.2 computable mapping -/
/-- **Definition 7.2 (Scott 1981, PRG-19) — computable element.** Specializing to `f : 𝟙 → W`, the
condition becomes: the index set `{m ∣ Yₘ ∈ y}` of the element `y ∈ |W|` is recursively enumerable.
We take this as the definition of a *computable element*. -/
class ComputableElement {W : NeighborhoodSystem β} (Q : ComputablePresentation W)
    (y : W.Element) : Prop where
  out : REPred (fun m => y.mem (Q.X m))

/-- **Definition 7.2 (Scott 1981, PRG-19) — computable map.** Relative to computable presentations
`P` of `V` and `Q` of `W`, an approximable map `f : V → W` is *computable* iff its neighbourhood
relation `Xₙ f Yₘ`, transported to the integer indices, is recursively enumerable. -/
class ComputableMap {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) (f : ApproximableMap V W) : Prop where
  out : REPred₂ (fun n m => f.rel (P.X n) (Q.X m))

end

end DomainTheory.NeighbourhoodSystems
end
