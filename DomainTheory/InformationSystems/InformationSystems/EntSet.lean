module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Constructive.funion

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

def EntSet (u v : Finset α) : Prop := ∀ X ∈ v, sys.Ent u X

namespace EntSet

theorem empty (u : Finset α) : sys.EntSet u (∅ : Finset α) := by
  intro X hX
  exact False.elim (Finset.notMem_empty X hX)

theorem singleton {u : Finset α} {X : α} :
    sys.EntSet u {X} ↔ sys.Ent u X := by
  constructor
  · intro h
    exact h X (Finset.mem_singleton_self X)
  · intro h Y hY
    rw [Finset.mem_singleton] at hY
    subst hY
    exact h

theorem bot : sys.EntSet ∅ ({sys.bot} : Finset α) := by
  intro X hX
  rw [Finset.mem_singleton] at hX
  subst hX
  exact sys.ent_bot sys.con_empty

theorem union_mem {u v : Finset α} (hu : u ∈ sys.Con) (h : sys.EntSet u v) :
    u ∪' v ∈ sys.Con := by
  have : ∀ s : Finset α, (∀ x ∈ s, x ∈ v) → u ∪' s ∈ sys.Con := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa [funion.empty_right] using hu
    · intro a t _ha ih hmem
      have hEnt_u_a : sys.Ent u a := h a (hmem a (Finset.mem_insert_self a t))
      have hut : u ∪' t ∈ sys.Con := ih fun x hx => hmem x (Finset.mem_insert_of_mem hx)
      have hEnt : sys.Ent (u ∪' t) a :=
        sys.ent_trans hut hu (fun y hy => sys.ent_refl hut (funion.subset_left u t hy))
          hEnt_u_a
      have hins : insert a (u ∪' t) ∈ sys.Con := sys.ent_con hEnt
      simpa [funion.insert] using hins
  exact this v fun _ hx => hx

theorem refl {u : Finset α} (hu : u ∈ sys.Con) : sys.EntSet u u :=
  fun _X hX => sys.ent_refl hu hX

theorem trans {u v w : Finset α}
    (hu : u ∈ sys.Con) (hv : v ∈ sys.Con)
    (huv : sys.EntSet u v) (hvw : sys.EntSet v w) : sys.EntSet u w :=
  fun X hX => sys.ent_trans hu hv huv (hvw X hX)

theorem mono {u u' v v' : Finset α}
    (hu : u ∈ sys.Con) (hu' : u' ∈ sys.Con)
    (hsubu : u ⊆ u') (huv : sys.EntSet u v) (hsubv : v' ⊆ v) :
    sys.EntSet u' v' := by
  intro X hX
  have hEnt : sys.Ent u X := huv X (hsubv hX)
  refine sys.ent_trans hu' hu ?_ hEnt
  intro y hy
  exact sys.ent_refl hu' (hsubu hy)

theorem union {u v v' : Finset α}
    (huv : sys.EntSet u v) (huv' : sys.EntSet u v') : sys.EntSet u (v ∪' v') := by
  intro X hX
  rcases funion.mem.mp hX with h | h
  · exact huv X h
  · exact huv' X h

end EntSet

end InfoSys

end DomainTheory.InformationSystems
