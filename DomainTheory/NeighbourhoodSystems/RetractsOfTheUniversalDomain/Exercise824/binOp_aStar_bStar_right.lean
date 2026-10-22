module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.toElementMap_fixElement_snd

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}


/-- `(aStar s t, bStar s t)` is a *genuine* fixed point of the pair `(s, t)`. -/
theorem binOp_aStar_bStar_right (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    binOp t (aStar s t) (bStar s t) = bStar s t := by
  unfold binOp aStar bStar
  rw [toFilter_toApproxMap, toFilter_toApproxMap, pair_fst_snd, toElementMap_fixElement_snd]

end Exercise824
end DomainTheory.NeighbourhoodSystems
