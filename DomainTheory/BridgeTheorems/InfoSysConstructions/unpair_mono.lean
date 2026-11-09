module
public import DomainTheory.BridgeTheorems.InfoSysConstructions.unpair

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem unpair_mono {z₁ z₂ : (productSystem A B).Element} (hz : z₁ ≤ z₂) :
    unpair A B z₁ ≤ unpair A B z₂ := by
  constructor
  · exact (productSystem.fstMap A B).toElement_mono hz
  · exact (productSystem.sndMap A B).toElement_mono hz

end InfoSysConstructions
end DomainTheory.BridgeTheorems
