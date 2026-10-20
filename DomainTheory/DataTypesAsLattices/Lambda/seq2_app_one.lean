module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


























theorem seq2_app_one (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y := by
  rw [seq2_app]
  ext n
  simp [condSet, predSet, ofNat, botElem]

end DomainTheory.DataTypesAsLattices
