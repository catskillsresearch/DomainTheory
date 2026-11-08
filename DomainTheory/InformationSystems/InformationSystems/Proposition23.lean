module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Definition22
public import DomainTheory.InformationSystems.InformationSystems.Constructive.funion

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

namespace proposition_2_3

theorem i : sys.EntSet ∅ ({sys.bot} : Finset α) := by
  intro X hX
  rw [Finset.mem_singleton] at hX
  subst hX
  exact sys.ent_bot sys.con_empty

theorem ii {u v : Finset α} (hu : u ∈ sys.Con) (h : sys.EntSet u v) :
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

theorem iii {u : Finset α} (hu : u ∈ sys.Con) : sys.EntSet u u :=
  fun _X hX => sys.ent_refl hu hX

theorem iv {u v w : Finset α}
    (hu : u ∈ sys.Con) (hv : v ∈ sys.Con)
    (huv : sys.EntSet u v) (hvw : sys.EntSet v w) : sys.EntSet u w :=
  fun X hX => sys.ent_trans hu hv huv (hvw X hX)

theorem v {u u' v v' : Finset α}
    (hu : u ∈ sys.Con) (hu' : u' ∈ sys.Con)
    (hsubu : u ⊆ u') (huv : sys.EntSet u v) (hsubv : v' ⊆ v) :
    sys.EntSet u' v' := by
  intro X hX
  have hEnt : sys.Ent u X := huv X (hsubv hX)
  refine sys.ent_trans hu' hu ?_ hEnt
  intro y hy
  exact sys.ent_refl hu' (hsubu hy)

theorem vi {u v v' : Finset α}
    (huv : sys.EntSet u v) (huv' : sys.EntSet u v') : sys.EntSet u (v ∪' v') := by
  intro X hX
  rcases funion.mem.mp hX with h | h
  · exact huv X h
  · exact huv' X h

end proposition_2_3

theorem proposition_2_3 :
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α),
      sys.EntSet ∅ ({sys.bot} : Finset α)) ∧
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u v : Finset α},
      u ∈ sys.Con → sys.EntSet u v → u ∪' v ∈ sys.Con) ∧
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u : Finset α},
      u ∈ sys.Con → sys.EntSet u u) ∧
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u v w : Finset α},
      u ∈ sys.Con → v ∈ sys.Con → sys.EntSet u v → sys.EntSet v w → sys.EntSet u w) ∧
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u u' v v' : Finset α},
      u ∈ sys.Con → u' ∈ sys.Con → u ⊆ u' → sys.EntSet u v → v' ⊆ v → sys.EntSet u' v') ∧
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u v v' : Finset α},
      sys.EntSet u v → sys.EntSet u v' → sys.EntSet u (v ∪' v')) :=
  ⟨@proposition_2_3.i, @proposition_2_3.ii, @proposition_2_3.iii,
    @proposition_2_3.iv, @proposition_2_3.v, @proposition_2_3.vi⟩

end InfoSys

end DomainTheory.InformationSystems
