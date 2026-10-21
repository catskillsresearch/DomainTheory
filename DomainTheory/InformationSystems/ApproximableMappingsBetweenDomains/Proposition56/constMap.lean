/-ai
Proposition 5.6 defines the constant approximable mapping of value an element b to relate a consistent finite set to a finite set of the codomain exactly when that codomain set is contained in b. The codomain set is consistent because b is. The empty set is contained in b. A union of sets contained in b is contained in b. Monotonicity uses closure of b under entailment.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

namespace ApproximableMap

variable {α β γ δ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

variable {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ} {D : InfoSys δ}

/-- **Proposition 5.6.** Constant map: `u (const b) v` means `v ⊆ b`. -/
def constMap (b : B.Element) : ApproximableMap A B where
  rel u v := u ∈ A.Con ∧ (v : Set β) ⊆ b.carrier
  rel_dom h := h.1
  rel_cod h := b.consistent _ h.2
  empty_rel := ⟨A.con_empty, fun _ h => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 h))⟩
  union_right := by
    rintro u v v' ⟨hu, hv⟩ ⟨_, hv'⟩
    refine ⟨hu, ?_⟩
    intro y hy
    rcases mem_funion.mp (Finset.mem_coe.1 hy) with h | h
    · exact hv (Finset.mem_coe.2 h)
    · exact hv' (Finset.mem_coe.2 h)
  mono := by
    rintro u u' v v' ⟨_hu, hv⟩ _hEntu hEntv hu' _hv'
    refine ⟨hu', ?_⟩
    intro y hy
    have hEnt : B.Ent v y := hEntv y hy
    exact b.closed v y hv hEnt

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
