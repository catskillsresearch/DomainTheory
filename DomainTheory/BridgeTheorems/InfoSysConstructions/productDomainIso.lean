module

public import DomainTheory.BridgeTheorems.InfoSysConstructions.unpair_pairElements
public import DomainTheory.BridgeTheorems.InfoSysConstructions.pairElements_unpair
public import DomainTheory.BridgeTheorems.InfoSysConstructions.pairElements_mono

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

noncomputable def productDomainIso :
    A.Element × B.Element ≃o (productSystem A B).Element where
  toFun := fun p => pairElements A B p.1 p.2
  invFun := unpair A B
  left_inv := fun p => unpair_pairElements A B p.1 p.2
  right_inv := pairElements_unpair A B
  map_rel_iff' := by
    intro p q
    constructor
    · intro h
      change pairElements A B p.1 p.2 ≤ pairElements A B q.1 q.2 at h
      constructor
      · have hp := (productSystem.fstMap A B).toElement_mono h
        rw [fstMap_pairElements A B p.1 p.2, fstMap_pairElements A B q.1 q.2] at hp
        exact hp
      · have hp := (productSystem.sndMap A B).toElement_mono h
        rw [sndMap_pairElements A B p.1 p.2, sndMap_pairElements A B q.1 q.2] at hp
        exact hp
    · intro h
      exact pairElements_mono A B h.1 h.2

end InfoSysConstructions

end DomainTheory.BridgeTheorems
