module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.finJoinApprox
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_4
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_11
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}

def HasTop (E : NeighborhoodSystem γ) : Prop := ∃ t : E.Element, ∀ x : E.Element, x ≤ t

theorem ft_inter : ({false} : Set Bool) ∩ {true} = ∅ := by
  ext b
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl h; exact absurd h (by decide)

def improperTop (E : NeighborhoodSystem γ)
    (hcl : ∀ {X Y : Set γ}, E.mem X → E.mem Y → E.mem (X ∩ Y)) : E.Element where
  mem := E.mem
  sub h := h
  master_mem := E.master_mem
  inter_mem h1 h2 := hcl h1 h2
  up_mem _ hY _ := hY

theorem tf_inter : ({true} : Set Bool) ∩ {false} = ∅ := by
  ext b
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl h; exact absurd h (by decide)

def Vshape : NeighborhoodSystem Bool where
  mem X := X = Set.univ ∨ X = {true} ∨ X = {false}
  master := Set.univ
  master_nonempty := ⟨true, Set.mem_univ _⟩
  master_mem := Or.inl rfl
  sub_master _ := Set.subset_univ _
  inter_mem := by
    rintro X Y Z hX hY hZ hZsub

    have hZne : Z.Nonempty := by
      rcases hZ with rfl | rfl | rfl
      · exact ⟨true, Set.mem_univ true⟩
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    obtain ⟨z, hz⟩ := hZne
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl (by rw [Set.univ_inter]))
    · exact Or.inr (Or.inr (by rw [Set.univ_inter]))
    · exact Or.inr (Or.inl (by rw [Set.inter_univ]))
    · exact Or.inr (Or.inl (by rw [Set.inter_self]))
    · rw [tf_inter] at hZsub; exact absurd (hZsub hz) (Set.notMem_empty z)
    · exact Or.inr (Or.inr (by rw [Set.inter_univ]))
    · rw [ft_inter] at hZsub; exact absurd (hZsub hz) (Set.notMem_empty z)
    · exact Or.inr (Or.inr (by rw [Set.inter_self]))

end Counterexample712C
namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}

theorem Vshape_mem_false : Vshape.mem {false} := Or.inr (Or.inr rfl)

theorem Vshape_mem_true : Vshape.mem {true} := Or.inr (Or.inl rfl)

theorem Vshape_not_mem_empty : ¬ Vshape.mem (∅ : Set Bool) := by
  rintro (h | h | h)
  · exact Set.empty_ne_univ h
  · exact absurd h.symm (Set.singleton_ne_empty true)
  · exact absurd h.symm (Set.singleton_ne_empty false)

theorem Vshape_not_hasTop : ¬ HasTop Vshape := by
  rintro ⟨t, ht⟩
  have htt : t.mem {true} :=
    ht (Vshape.principal Vshape_mem_true) {true} ⟨Vshape_mem_true, subset_rfl⟩
  have htf : t.mem {false} :=
    ht (Vshape.principal Vshape_mem_false) {false} ⟨Vshape_mem_false, subset_rfl⟩
  have hint : t.mem (({true} : Set Bool) ∩ {false}) := t.inter_mem htt htf
  rw [tf_inter] at hint
  exact Vshape_not_mem_empty (t.sub hint)

end Counterexample712C
namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}

theorem hasTop_of_inter_closed (E : NeighborhoodSystem γ)
    (hcl : ∀ {X Y : Set γ}, E.mem X → E.mem Y → E.mem (X ∩ Y)) : HasTop E :=
  ⟨improperTop E hcl, fun x _X hX => x.sub hX⟩

theorem hasTop_of_iso {D : NeighborhoodSystem γ} {D' : NeighborhoodSystem δ}
    (e : D.Element ≃o D'.Element) (h : HasTop D') : HasTop D := by
  obtain ⟨t, ht⟩ := h
  refine ⟨e.symm t, fun x => ?_⟩
  rw [← e.le_iff_le, e.apply_symm_apply]
  exact ht (e x)

theorem powerDomain_hasTop (V : NeighborhoodSystem γ) : HasTop V.PowerDomain :=
  hasTop_of_inter_closed V.PowerDomain (fun hX hY => V.PDmem_inter hX hY)

end Counterexample712C
namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}

theorem subsystem_inter_closed {D E : NeighborhoodSystem γ} (h : D ◁ E)
    (hE : ∀ {X Y : Set γ}, E.mem X → E.mem Y → E.mem (X ∩ Y))
    {X Y : Set γ} (hX : D.mem X) (hY : D.mem Y) : D.mem (X ∩ Y) :=
  h.inter_closed hX hY (hE (h.sub hX) (h.sub hY))

theorem hasTop_of_trianglelefteq_powerDomain {D : NeighborhoodSystem γ} {E : NeighborhoodSystem δ}
    (h : D ⊴ E.PowerDomain) : HasTop D := by
  obtain ⟨D', hsub, ⟨e⟩⟩ := h
  have hPcl : ∀ {X Y : Set (Set δ)}, E.PowerDomain.mem X → E.PowerDomain.mem Y →
      E.PowerDomain.mem (X ∩ Y) := fun hX hY => E.PDmem_inter hX hY
  exact hasTop_of_iso e (hasTop_of_inter_closed D' (subsystem_inter_closed hsub hPcl))

theorem vshape_not_trianglelefteq_powerDomain : ¬ (Vshape ⊴ Vshape.PowerDomain) := fun h =>
  Vshape_not_hasTop (hasTop_of_trianglelefteq_powerDomain h)

end Counterexample712C

end DomainTheory.NeighbourhoodSystems
