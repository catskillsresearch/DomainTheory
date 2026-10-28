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

theorem constMap.toElement (b : B.Element) (x : A.Element) :
    (constMap (A := A) b).toElement x = b := by
  apply le_antisymm
  · intro Y ⟨_u, _hu, ⟨_, hsub⟩⟩
    exact hsub (Finset.mem_coe.2 (Finset.mem_singleton_self Y))
  · intro Y hY
    refine ⟨∅, ?_, ?_⟩
    · intro a ha
      exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))
    · refine ⟨A.con_empty, ?_⟩
      intro Z hZ
      have hZ' : Z ∈ ({Y} : Finset β) := Finset.mem_coe.1 hZ
      rw [Finset.mem_singleton] at hZ'
      subst hZ'
      exact hY

theorem constMap.comp (b : B.Element) (g : ApproximableMap D A) :
    ApproximableMap.comp (constMap (A := A) b) g = constMap (A := D) b :=
  (ext_iff_toElement _ _).2 fun x => by
    rw [ApproximableMap.comp.toElement, constMap.toElement, constMap.toElement]

theorem constMap.unique (b : B.Element) (f : ApproximableMap A B)
    (h : ∀ x : A.Element, f.toElement x = b) :
    f = constMap (A := A) b :=
  (ext_iff_toElement f (constMap (A := A) b)).2 fun x => by
    rw [h x, constMap.toElement]

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
