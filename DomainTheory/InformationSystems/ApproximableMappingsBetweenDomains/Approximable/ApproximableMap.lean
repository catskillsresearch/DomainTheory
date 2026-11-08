module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.closure

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

end ApproximableMap

end InfoSys
end DomainTheory.InformationSystems
