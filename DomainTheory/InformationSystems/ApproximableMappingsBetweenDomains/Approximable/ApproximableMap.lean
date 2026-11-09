module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.InformationSystems.EntSet

@[expose] public section

universe u v

namespace DomainTheory.InformationSystems
namespace InfoSys

open DomainTheory.InformationSystems.Constructive

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

structure ApproximableMap (A : InfoSys α) (B : InfoSys β) where
  rel : Finset α → Finset β → Prop
  rel_dom : ∀ {u v}, rel u v → u ∈ A.Con
  rel_cod : ∀ {u v}, rel u v → v ∈ B.Con
  empty_rel : rel ∅ ∅
  union_right : ∀ {u v v'}, rel u v → rel u v' → rel u (v ∪' v')
  mono : ∀ {u u' v v'},
    rel u v → A.EntSet u' u → B.EntSet v v' → u' ∈ A.Con → v' ∈ B.Con → rel u' v'

namespace ApproximableMap

open Constructive

variable {A : InfoSys α} {B : InfoSys β}

def Le (f g : ApproximableMap A B) : Prop := ∀ ⦃u v⦄, f.rel u v → g.rel u v

theorem ext {f g : ApproximableMap A B} (h : ∀ u v, f.rel u v ↔ g.rel u v) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by
    funext u v
    exact propext (h u v)
  subst this
  rfl

variable {γ : Type*} [DecidableEq γ] {C : InfoSys γ}

theorem rel_bot_subset {D : InfoSys β} {s : Finset γ} {w : Finset β}
    (g : ApproximableMap C D) (hs : s ∈ C.Con)
    (hg : g.rel s (∅ : Finset β)) (hw : w ⊆ ({D.bot} : Finset β)) :
    g.rel s w := by
  have hwCon : w ∈ D.Con := D.con_subset (D.con_sing D.bot) hw
  have hEnt : D.EntSet (∅ : Finset β) w := by
    intro y hy
    have : y = D.bot := Finset.mem_singleton.mp (hw hy)
    subst this
    exact D.ent_bot D.con_empty
  exact g.mono hg (EntSet.refl C hs) hEnt hs hwCon

theorem rel_bot_subset_left {D : InfoSys α} {s : Finset γ} {v : Finset α}
    (f : ApproximableMap C D) (hs : s ∈ C.Con)
    (hf : f.rel s (∅ : Finset α)) (hv : v ⊆ ({D.bot} : Finset α)) :
    f.rel s v := by
  have hvCon : v ∈ D.Con := D.con_subset (D.con_sing D.bot) hv
  have hEnt : D.EntSet (∅ : Finset α) v := by
    intro x hx
    have : x = D.bot := Finset.mem_singleton.mp (hv hx)
    subst this
    exact D.ent_bot D.con_empty
  exact f.mono hf (EntSet.refl C hs) hEnt hs hvCon

end ApproximableMap

end InfoSys
end DomainTheory.InformationSystems
