
module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.lambR
public import DomainTheory.DataTypesAsLattices.Retracts.envR
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.envR_app
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_env_nth {t : Pomega} (ht : typed t envR) (n : ℕ) :
    typed (funOf t (ofNat n)) lambR := by
  have ht' : t = graph (fun m => funOf lambR (funOf t m)) := by
    simpa [typed, envR_app] using ht
  have : funOf t (ofNat n) = funOf lambR (funOf t (ofNat n)) := by
    nth_rw 1 [ht']
    exact beta (theorem_1_3 (funOf.isScottContinuous lambR)
      (funOf.isScottContinuous t)) (ofNat n)
  exact this

end DomainTheory.DataTypesAsLattices
