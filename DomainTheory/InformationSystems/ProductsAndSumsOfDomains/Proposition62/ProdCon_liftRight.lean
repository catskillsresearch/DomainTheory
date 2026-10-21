/-ai
If a finite set w is consistent in the information system B, then the right lift of w is consistent in the product of A and B.

Product consistency splits into the two projections. The first projection of the right lift is contained in the singleton of the bottom token of A, and that singleton is consistent, so the subset axiom gives consistency of the projection. The second projection of the right lift equals w, which is consistent by hypothesis.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.sndFinset_liftRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.fstFinset_liftRight

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)








theorem ProdCon_liftRight {w : Finset β} (hw : w ∈ B.Con) :
    ProdCon A B (liftRight A B w) := by
  refine ⟨?_, ?_⟩
  · exact A.con_subset (A.con_sing A.bot) (fstFinset_liftRight A B w)
  · rw [sndFinset_liftRight]
    exact hw

end InfoSys
end DomainTheory.InformationSystems
