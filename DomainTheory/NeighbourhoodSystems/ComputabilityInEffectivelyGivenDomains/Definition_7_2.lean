module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive
open NeighborhoodSystem Domain.Recursive ApproximableMap
section
variable {α β γ : Type*}

class ComputableElement {W : NeighborhoodSystem β} (Q : ComputablePresentation W)
    (y : W.Element) : Prop where
  out : REPred (fun m => y.mem (Q.X m))

class ComputableMap {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) (f : ApproximableMap V W) : Prop where
  out : REPred₂ (fun n m => f.rel (P.X n) (Q.X m))

end

end DomainTheory.NeighbourhoodSystems
end
